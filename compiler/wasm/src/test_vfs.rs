//! `nargo test`, over a [virtual filesystem](crate::vfs), with no filesystem.
//!
//! # This is not a second test runner
//!
//! Every semantic decision a test run makes is `nargo`'s own, called here rather
//! than restated:
//!
//! * **Discovery** is [`noirc_frontend::hir::Context::get_all_test_functions_in_crate_matching`],
//!   the function `nargo test`, the LSP and `stdlib-tests` all call. The names it
//!   returns are `fully_qualified_function_name`'s — the exact strings
//!   `nargo test --exact` compares against.
//! * **Running one test** is [`nargo::ops::run_test`], unchanged. Which means the
//!   inversion that matters — `#[test(should_fail)]`, where an assertion failure is
//!   a PASS and a clean execution is a FAILURE — is decided by
//!   `nargo::ops::test_status_program_compile_pass` and
//!   `nargo::ops::check_expected_failure_message`, and cannot drift from the runner
//!   a user runs locally without `nargo` itself changing. Nothing in this file
//!   inspects `TestScope`, compares a failure message, or decides a verdict.
//! * **Foreign calls** are `nargo::foreign_calls::DefaultForeignCallBuilder`'s
//!   layers, which is what gives a test `print` and `std::test::OracleMock`.
//!   Without the `rpc` feature (which does not build for wasm, and which this
//!   crate's `Cargo.toml` already declines) that builder composes exactly the
//!   print layer over the mock layer — the same stack `nargo test` uses when no
//!   `--oracle-resolver` is passed, which is every invocation a browser could make.
//!
//! What this file owns is therefore only the two things that are genuinely absent
//! in a browser: getting a `Context` out of an in-memory tree (which
//! [`crate::vfs::context_for`] already did for compiling), and a JSON envelope.
//!
//! # ONE CONTEXT, MANY TESTS — and why that is safe
//!
//! `nargo_cli`'s `test_cmd` rebuilds the `Context` per test. Its own comment says
//! why, and the reason is threads: *"This is really hacky but we can't share
//! `Context` or `S` across threads."* There are no threads here. The upstream
//! precedent for the single-context shape is `tooling/nargo_cli/tests/stdlib-tests.rs`,
//! which checks the crate once and then drives hundreds of `run_test` calls
//! against that one `Context` behind a `Mutex`. Rebuilding it per test would mean
//! re-elaborating the stdlib for every test in the project, which in a tab is
//! seconds each.
//!
//! # WHAT `ok` MEANS HERE, because it does not mean what it means next door
//!
//! In [`crate::compile_vfs::VfsResponse`], `ok` means *the compile succeeded*. In
//! [`TestVfsResponse`] it means **the suite ran** — the tree resolved, the crate
//! elaborated, and every discovered test reached a verdict. A suite in which every
//! test failed still answers `ok: true`, and a host must read `failed` (or the
//! per-test `status`) to know how it went. The alternative spelling — `ok` meaning
//! "all green" — would make "the project does not compile" and "one assertion
//! fired" the same value, and those are the two outcomes a Test Results pane most
//! needs to tell apart.

use std::collections::BTreeMap;
use std::path::PathBuf;

use bn254_blackbox_solver::Bn254BlackBoxSolver;
// The trait that gives `FileMap` its `location(file_id, byte)`; `vfs::position_diagnostics`
// reaches it through the same import.
use fm::codespan_files::Files;
use nargo::foreign_calls::DefaultForeignCallBuilder;
use nargo::ops::{TestStatus, run_test};
use noirc_driver::{CompileOptions, check_crate, compile_no_check};
use noirc_errors::CustomDiagnostic;
use noirc_frontend::hir::FunctionNameMatch;
use noirc_frontend::hir::def_map::TestFunction;
use serde::{Deserialize, Serialize};

use crate::vfs::{
    PositionedDiagnostic, VfsError, context_for, debugging_compile_options, position_diagnostics,
    resolve_vfs,
};

/// What a host asks for.
///
/// The `files` / `package_dir` half is [`crate::compile_vfs::VfsRequest`]'s, field
/// for field, so a host that can already ask for a compile can ask for a test run
/// by changing the entry point and nothing else.
#[derive(Deserialize)]
pub struct TestVfsRequest {
    /// The whole virtual filesystem: `path -> contents`.
    pub files: BTreeMap<String, String>,
    /// The directory holding the entry package's `Nargo.toml`.
    #[serde(default)]
    pub package_dir: String,
    /// Fully-qualified test names to run, matched EXACTLY — the same strings and
    /// the same comparison as `nargo test --exact`. Empty runs every test, which
    /// is `nargo test` with no arguments.
    #[serde(default)]
    pub tests: Vec<String>,
    /// One fully-qualified test name to compile as a TRACEABLE entry point.
    ///
    /// This is the recording half, and it is a different request from running:
    /// running answers a verdict, this answers an ARTIFACT — a
    /// `ProgramArtifact` with the named test as its `main`, compiled through
    /// the instrumented `force_brillig` path, which is the only shape
    /// `tooling/tracer_wasm`'s `ct_trace` can step.
    ///
    /// WHY IT IS A SEPARATE FIELD AND NOT A MODE ON `tests`. A run and a
    /// recording want opposite compile options — `nargo test` uses
    /// `CompileOptions::default()` and a recording needs `instrument_debug` +
    /// `force_brillig` — so one request that did both would have to pick one,
    /// and either choice makes the other answer wrong. `vfs::context_for`'s own
    /// header records what happens when the instrumented path is skipped: the
    /// trace has one event and no steps, and both wasm modules report `ok` over
    /// it.
    ///
    /// When set, NO TESTS ARE RUN. The caller asks for the verdict and the
    /// artifact as two dispatches, exactly as Build-then-Run asks for a compile
    /// and a trace.
    #[serde(default)]
    pub record: Option<String>,
}

/// What one test did.
#[derive(Debug, Clone, Serialize)]
pub struct TestOutcome {
    /// The runner's own fully-qualified name (`tests::test_main`) — what
    /// `nargo test --exact` takes and what a catalog keys by.
    pub name: String,
    /// `pass`, `fail`, `skipped` or `compile-error`, one per [`TestStatus`]
    /// variant. Spelled as the LSP spells them (`tooling/lsp/src/requests/test_run.rs`
    /// answers `pass` / `fail` / `skipped` / `error`) except that a compile error
    /// keeps its own tag rather than collapsing into `error`: a test that did not
    /// build and a test that failed are different things to fix.
    pub status: String,
    /// Why it failed, verbatim from [`TestStatus`]. `None` for a pass.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub message: Option<String>,
    /// Whatever the test `print`ed, in order. Empty is omitted.
    #[serde(skip_serializing_if = "String::is_empty", default)]
    pub output: String,
    /// `#[test(should_fail)]` or `#[test(should_fail_with = "…")]` —
    /// [`TestFunction::should_fail`]. Reported so a host can SHOW the inversion
    /// rather than silently applying it: "passed (expected to fail)" is a row a
    /// reader can check, and "passed" over a `should_fail` test is not.
    pub should_fail: bool,
    /// The substring `should_fail_with` requires of the failure message, when the
    /// attribute named one. [`TestFunction::failure_reason`].
    #[serde(skip_serializing_if = "Option::is_none")]
    pub expected_failure: Option<String>,
    /// Whether the test takes arguments, and is therefore a FUZZING harness to
    /// `nargo test` rather than a plain test. See [`run_tests`] for what this
    /// module does with those and why.
    pub has_arguments: bool,
    /// Where the test is declared, against the caller's own VFS paths.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub file: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub line: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub column: Option<usize>,
    /// The positioned diagnostic a failure carried, when it carried one — the
    /// assertion's own location, which is usually not the test's first line.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub diagnostic: Option<PositionedDiagnostic>,
}

/// What a whole run said.
#[derive(Serialize)]
pub struct TestVfsResponse {
    /// **The suite RAN.** Not "everything passed" — see the module header.
    pub ok: bool,
    /// `resolve`, `check` or `request` — which half refused. Absent when it ran.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub stage: Option<String>,
    /// A tag to branch on rather than prose: [`VfsError::kind`], or
    /// `check-error` / `bad-request`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub kind: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub message: Option<String>,
    /// The `Nargo.toml` a resolve refusal is about.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub manifest: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub line: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub column: Option<usize>,
    /// Errors from elaborating the crate — the ones that stop a run before any
    /// test exists. Positioned against the caller's VFS paths.
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub diagnostics: Vec<PositionedDiagnostic>,
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub warnings: Vec<PositionedDiagnostic>,
    /// One per discovered test, in discovery order.
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub tests: Vec<TestOutcome>,
    /// Tallies, so a host does not have to fold the list to render a headline —
    /// and so a mutation that flips one verdict is visible in a scalar.
    pub passed: usize,
    pub failed: usize,
    pub skipped: usize,
    /// The traceable artifact for `TestVfsRequest.record`, when one was asked
    /// for. `nargo compile`'s own `ProgramArtifact` shape, so the tracer takes
    /// it unchanged — it is the same value `nv_compile_vfs` answers in
    /// `VfsResponse.artifact`, and a host hands it to `ct_trace` the same way.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub artifact: Option<serde_json::Value>,
}

impl TestVfsResponse {
    fn refused(stage: &str, kind: &str, message: String) -> TestVfsResponse {
        TestVfsResponse {
            ok: false,
            stage: Some(stage.to_string()),
            kind: Some(kind.to_string()),
            message: Some(message),
            manifest: None,
            line: None,
            column: None,
            diagnostics: Vec::new(),
            warnings: Vec::new(),
            tests: Vec::new(),
            passed: 0,
            failed: 0,
            skipped: 0,
            artifact: None,
        }
    }

    fn resolve_refused(err: &VfsError) -> TestVfsResponse {
        let at = err.position();
        TestVfsResponse {
            manifest: err.manifest().map(|m| m.to_string()),
            line: at.map(|a| a.line),
            column: at.map(|a| a.column),
            ..TestVfsResponse::refused("resolve", err.kind(), err.to_string())
        }
    }
}

/// The `status` string for a [`TestStatus`], and the only place the mapping lives.
fn status_tag(status: &TestStatus) -> &'static str {
    match status {
        TestStatus::Pass => "pass",
        TestStatus::Fail { .. } => "fail",
        TestStatus::Skipped => "skipped",
        TestStatus::CompileError(_) => "compile-error",
    }
}

/// The message a [`TestStatus`] carries, if any.
fn status_message(status: &TestStatus) -> Option<String> {
    match status {
        TestStatus::Pass | TestStatus::Skipped => None,
        TestStatus::Fail { message, .. } => Some(message.clone()),
        TestStatus::CompileError(diagnostic) => Some(diagnostic.message.clone()),
    }
}

/// The diagnostic a [`TestStatus`] carries, if any.
fn status_diagnostic(status: &TestStatus) -> Option<CustomDiagnostic> {
    match status {
        TestStatus::Pass | TestStatus::Skipped => None,
        TestStatus::Fail { error_diagnostic, .. } => error_diagnostic.clone(),
        TestStatus::CompileError(diagnostic) => Some(diagnostic.clone()),
    }
}

/// Resolve, elaborate, discover and run. The one code path every host uses.
pub fn run_tests(request: &TestVfsRequest) -> TestVfsResponse {
    if let Some(name) = request.record.as_deref() {
        return record_test(request, name);
    }

    let tree: BTreeMap<PathBuf, String> =
        request.files.iter().map(|(p, s)| (PathBuf::from(p), s.clone())).collect();

    let plan = match resolve_vfs(&tree, &request.package_dir) {
        Ok(plan) => plan,
        Err(err) => return TestVfsResponse::resolve_refused(&err),
    };

    // `for_debugging: false`, and the flag is not cosmetic. The instrumented path
    // rewrites the AST and forces brillig so a TRACER has something to step;
    // `nargo test` compiles with plain `CompileOptions::default()`, and a runner
    // that quietly instrumented would be executing a different program than the
    // one the user tests locally. The two verdicts could then differ, which is the
    // single failure this whole module exists to avoid.
    let (mut context, crate_id) = context_for(&plan, &tree, false);

    let options = CompileOptions::default();

    // `check_crate` before discovery, exactly as `test_cmd::prepare_package_and_check_crate`
    // and the LSP's `test_run` do: `get_all_test_functions_in_crate_matching` reads
    // `def_maps`, which elaboration is what fills in.
    let warnings = match check_crate(&mut context, crate_id, &options) {
        Ok(((), warnings)) => position_diagnostics(&warnings, &context.file_manager),
        Err(errors) => {
            let diagnostics = position_diagnostics(&errors, &context.file_manager);
            return TestVfsResponse {
                diagnostics,
                ..TestVfsResponse::refused(
                    "check",
                    "check-error",
                    format!("the project did not compile: {} diagnostic(s)", errors.len()),
                )
            };
        }
    };

    let pattern = if request.tests.is_empty() {
        FunctionNameMatch::Anything
    } else {
        FunctionNameMatch::Exact(request.tests.clone())
    };
    let discovered: Vec<(String, TestFunction)> =
        context.get_all_test_functions_in_crate_matching(&crate_id, &pattern);

    let mut outcomes: Vec<TestOutcome> = Vec::with_capacity(discovered.len());
    let (mut passed, mut failed, mut skipped) = (0usize, 0usize, 0usize);

    for (name, test_function) in &discovered {
        let (file, line, column) = declaration_site(&context, test_function);
        let should_fail = test_function.should_fail();
        let expected_failure = test_function.failure_reason().map(|r| r.to_string());
        let has_arguments = test_function.has_arguments;

        let (status, output) = if has_arguments {
            // A test WITH arguments is a fuzzing harness to `nargo test`, and
            // `run_or_fuzz_test` sends it to the fuzzer. The fuzzer needs a corpus
            // directory (`tempfile::tempdir()`), a wall clock and a thread pool —
            // three things a wasm module does not have and must not pretend to.
            //
            // `nargo test --no-fuzz` answers exactly `TestStatus::Skipped` for
            // these (`test_cmd::run_test`'s first branch), so this run IS a
            // `nargo test` run, with the one flag a browser cannot avoid. The
            // message says so rather than leaving a bare "skipped".
            skipped += 1;
            (
                TestStatus::Skipped,
                "skipped: this test takes arguments, so `nargo test` fuzzes it. \
                 Fuzzing needs a corpus directory and a thread pool, which a browser \
                 has neither of; this is `nargo test --no-fuzz`.\n"
                    .to_string(),
            )
        } else {
            let mut printed: Vec<u8> = Vec::new();
            let status = run_test(
                &Bn254BlackBoxSolver,
                &mut context,
                test_function,
                &mut printed,
                &options,
                |output, base| {
                    // The non-`rpc` builder: print over mocks, which is what
                    // `nargo test` composes when no `--oracle-resolver` is given.
                    DefaultForeignCallBuilder::default().with_output(output).build_with_base(base)
                },
            );
            match status {
                TestStatus::Pass => passed += 1,
                TestStatus::Skipped => skipped += 1,
                TestStatus::Fail { .. } | TestStatus::CompileError(_) => failed += 1,
            }
            (status, String::from_utf8_lossy(&printed).into_owned())
        };

        let diagnostic = status_diagnostic(&status).map(|d| {
            position_diagnostics(std::slice::from_ref(&d), &context.file_manager)
                .into_iter()
                .next()
                .expect("position_diagnostics is one-for-one")
        });

        outcomes.push(TestOutcome {
            name: name.clone(),
            status: status_tag(&status).to_string(),
            message: status_message(&status),
            output,
            should_fail,
            expected_failure,
            has_arguments,
            file,
            line,
            column,
            diagnostic,
        });
    }

    TestVfsResponse {
        ok: true,
        stage: None,
        kind: None,
        message: None,
        manifest: None,
        line: None,
        column: None,
        diagnostics: Vec::new(),
        warnings,
        tests: outcomes,
        passed,
        failed,
        skipped,
        artifact: None,
    }
}

/// Compile ONE test function as a traceable entry point.
///
/// The recording half of "run this test". `nargo` has no command that does
/// this — `nargo test` runs and reports, `nargo trace` traces `main` — so this
/// is the one place in this module that is not a call into `nargo::ops`. It is
/// still not an invention: it is `vfs::compile_resolved`'s body with
/// `compile_no_check(test_function.id)` where that has `compile_main(root_id)`,
/// which is exactly the substitution `nargo::ops::run_test` itself makes one
/// line before it executes.
///
/// `for_debugging: true` and `debugging_compile_options()`, and neither is
/// optional. `vfs::context_for` records the measurement: an uninstrumented
/// artifact traces to ONE EVENT AND ZERO STEPS while every module reports `ok`,
/// which is a green answer to the wrong question and the exact shape a
/// click-to-replay flow must not produce.
fn record_test(request: &TestVfsRequest, name: &str) -> TestVfsResponse {
    let tree: BTreeMap<PathBuf, String> =
        request.files.iter().map(|(p, s)| (PathBuf::from(p), s.clone())).collect();

    let plan = match resolve_vfs(&tree, &request.package_dir) {
        Ok(plan) => plan,
        Err(err) => return TestVfsResponse::resolve_refused(&err),
    };

    let (mut context, crate_id) = context_for(&plan, &tree, true);
    let options = debugging_compile_options();

    let warnings = match check_crate(&mut context, crate_id, &options) {
        Ok(((), warnings)) => position_diagnostics(&warnings, &context.file_manager),
        Err(errors) => {
            let diagnostics = position_diagnostics(&errors, &context.file_manager);
            return TestVfsResponse {
                diagnostics,
                ..TestVfsResponse::refused(
                    "check",
                    "check-error",
                    format!("the project did not compile: {} diagnostic(s)", errors.len()),
                )
            };
        }
    };

    let pattern = FunctionNameMatch::Exact(vec![name.to_string()]);
    let discovered = context.get_all_test_functions_in_crate_matching(&crate_id, &pattern);
    let Some((_, test_function)) = discovered.first() else {
        // NAMED, not "0 tests". A recording asked for one specific test, and
        // "there is no such test" is a different thing to fix from "the test
        // failed" or "the project is broken".
        return TestVfsResponse::refused(
            "request",
            "no-such-test",
            format!("`{name}` is not a test in this package"),
        );
    };
    if test_function.has_arguments {
        // A fuzzing harness has no single execution to record. `nargo test`
        // would fuzz it; there is nothing here to hand a tracer, and inventing
        // an input map would record a run the user never asked for.
        return TestVfsResponse::refused(
            "request",
            "test-takes-arguments",
            format!(
                "`{name}` takes arguments, so `nargo test` fuzzes it rather than \
                 running it once. There is no single execution to record."
            ),
        );
    }

    match compile_no_check(&mut context, &options, test_function.id, None, false) {
        Ok(program) => {
            let artifact: noirc_artifacts::program::ProgramArtifact = program.into();
            TestVfsResponse {
                ok: true,
                stage: None,
                kind: None,
                message: None,
                manifest: None,
                line: None,
                column: None,
                diagnostics: Vec::new(),
                warnings,
                tests: Vec::new(),
                passed: 0,
                failed: 0,
                skipped: 0,
                artifact: serde_json::to_value(&artifact).ok(),
            }
        }
        Err(err) => {
            let diagnostic: CustomDiagnostic = err.into();
            let diagnostics =
                position_diagnostics(std::slice::from_ref(&diagnostic), &context.file_manager);
            TestVfsResponse {
                diagnostics,
                ..TestVfsResponse::refused(
                    "compile",
                    "compile-error",
                    format!("`{name}` did not compile for recording"),
                )
            }
        }
    }
}

/// Where a test is DECLARED, against the caller's own VFS paths.
///
/// The same two steps `vfs::position_diagnostics` takes — `file_manager.path()`
/// returns exactly what was registered, and `as_file_map().location()` turns a
/// byte offset into a 1-based line and column — so a host can key a row by
/// `file:line` and have it match the one a diagnostic would name.
fn declaration_site(
    context: &noirc_frontend::hir::Context,
    test_function: &TestFunction,
) -> (Option<String>, Option<usize>, Option<usize>) {
    let location = test_function.location;
    let Some(path) = context.file_manager.path(location.file) else {
        return (None, None, None);
    };
    let file = path.display().to_string();
    let at = context.file_manager.as_file_map().location(location.file, location.span.start() as usize).ok();
    (Some(file), at.as_ref().map(|l| l.line_number), at.as_ref().map(|l| l.column_number))
}

/// JSON in, JSON out. Public because it is the whole of what every host does, and
/// because the tests below drive it as a string so they exercise the wire shape a
/// browser actually sees rather than the struct behind it.
pub fn run_tests_json(request_json: &str) -> String {
    let response = match serde_json::from_str::<TestVfsRequest>(request_json) {
        Ok(request) => run_tests(&request),
        Err(err) => TestVfsResponse::refused(
            "request",
            "bad-request",
            format!("the request is not a TestVfsRequest: {err}"),
        ),
    };
    serde_json::to_string(&response)
        .unwrap_or_else(|e| format!("{{\"ok\":false,\"message\":\"{e}\"}}"))
}

// ---------------------------------------------------------------------------------------
// Tests — native, over the same code a wasm build runs
// ---------------------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    const MANIFEST: &str = "[package]\nname = \"app\"\ntype = \"bin\"\n\n[dependencies]\n";

    fn run(sources: &[(&str, &str)]) -> TestVfsResponse {
        let mut files: BTreeMap<String, String> = BTreeMap::new();
        files.insert("app/Nargo.toml".into(), MANIFEST.into());
        for (path, source) in sources {
            files.insert((*path).into(), (*source).into());
        }
        run_tests(&TestVfsRequest {
            files,
            package_dir: "app".into(),
            tests: Vec::new(),
            record: None,
        })
    }

    fn outcome<'a>(response: &'a TestVfsResponse, name: &str) -> &'a TestOutcome {
        response
            .tests
            .iter()
            .find(|t| t.name == name)
            .unwrap_or_else(|| panic!("no test named {name} in {:?}", names(response)))
    }

    fn names(response: &TestVfsResponse) -> Vec<String> {
        response.tests.iter().map(|t| t.name.clone()).collect()
    }

    /// The whole point of the module, in one program: four tests whose verdicts
    /// are four DIFFERENT combinations of "did it fail" and "was it meant to".
    ///
    /// Asserted per-test rather than on a tally, because a tally of 2 pass / 2
    /// fail is also what a runner that inverted BOTH attributes would report.
    const FOUR_WAYS: &str = r#"
fn main() {}

#[test]
fn passes() {
    assert(1 == 1);
}

#[test]
fn fails() {
    assert(1 == 2, "one is not two");
}

#[test(should_fail)]
fn fails_as_asked() {
    assert(1 == 2);
}

#[test(should_fail)]
fn passes_when_it_should_not() {
    assert(1 == 1);
}
"#;

    #[test]
    fn the_four_verdicts_are_not_symmetric() {
        let response = run(&[("app/src/main.nr", FOUR_WAYS)]);
        assert!(response.ok, "the suite did not run: {:?}", response.message);
        assert_eq!(names(&response).len(), 4, "discovered {:?}", names(&response));

        // An ordinary test that holds.
        assert_eq!(outcome(&response, "passes").status, "pass");

        // An ordinary test that does not.
        //
        // THE USER'S ASSERTION TEXT IS IN THE DIAGNOSTIC, NOT IN `message`, and that
        // asymmetry is nargo's rather than this module's: `TestStatus::Fail.message`
        // is `circuit_execution_err.to_string()`, which for an unsatisfied constraint
        // is the bare `"Failed assertion"`, while the string the user wrote is
        // resolved by `try_to_diagnose_runtime_error` into the `error_diagnostic`.
        // Measured, not assumed — this assertion was written the other way round
        // first and failed. A host that rendered only `message` would show every
        // failing test as "Failed assertion", which is a row nobody can act on, so
        // both are carried and both are asserted here.
        let fails = outcome(&response, "fails");
        assert_eq!(fails.status, "fail");
        assert_eq!(fails.message.as_deref(), Some("Failed assertion"));
        let diagnostic = fails.diagnostic.as_ref().expect("a failing assertion is positioned");
        assert!(
            diagnostic.message.contains("one is not two"),
            "the assertion message did not survive: {:?}",
            diagnostic.message
        );
        assert_eq!(diagnostic.file, "app/src/main.nr");
        assert_eq!(diagnostic.line, 11, "the `assert` line, not the `fn` line");

        // THE INVERSION, both directions. Get either of these backwards and the
        // suite reports the opposite of the truth, which is worse than not running.
        let expected_fail = outcome(&response, "fails_as_asked");
        assert_eq!(
            expected_fail.status, "pass",
            "a `should_fail` test that failed must PASS; got {:?}",
            expected_fail.message
        );
        assert!(expected_fail.should_fail);

        let unexpected_pass = outcome(&response, "passes_when_it_should_not");
        assert_eq!(
            unexpected_pass.status, "fail",
            "a `should_fail` test that passed must FAIL; got {:?}",
            unexpected_pass.message
        );
        assert!(
            unexpected_pass
                .message
                .as_deref()
                .unwrap_or("")
                .contains("Test passed when it should have failed"),
            "got {:?}",
            unexpected_pass.message
        );

        assert_eq!((response.passed, response.failed, response.skipped), (2, 2, 0));
    }

    /// `should_fail_with` is a SUBSTRING match on the failure message, and the
    /// wrong message is a failure rather than a pass. This is the case a runner
    /// that only checked "did it fail" would get wrong while looking correct on
    /// every test above.
    #[test]
    fn should_fail_with_checks_the_message() {
        let source = r#"
fn main() {}

#[test(should_fail_with = "not two")]
fn right_message() {
    assert(1 == 2, "one is not two");
}

#[test(should_fail_with = "some other reason")]
fn wrong_message() {
    assert(1 == 2, "one is not two");
}
"#;
        let response = run(&[("app/src/main.nr", source)]);
        assert!(response.ok, "the suite did not run: {:?}", response.message);

        let right = outcome(&response, "right_message");
        assert_eq!(right.status, "pass", "got {:?}", right.message);
        assert_eq!(right.expected_failure.as_deref(), Some("not two"));

        let wrong = outcome(&response, "wrong_message");
        assert_eq!(wrong.status, "fail", "got {:?}", wrong.message);
        assert!(
            wrong.message.as_deref().unwrap_or("").contains("wrong message"),
            "the mismatch must say the message was wrong, not merely that it failed: {:?}",
            wrong.message
        );
    }

    /// Names are `fully_qualified_function_name`'s, module path included — the
    /// strings `nargo test --exact` takes and a catalog keys by.
    #[test]
    fn names_carry_the_module_path() {
        let source = r#"
fn main() {}

mod tests {
    #[test]
    fn inner() {
        assert(1 == 1);
    }
}
"#;
        let response = run(&[("app/src/main.nr", source)]);
        assert_eq!(names(&response), vec!["tests::inner".to_string()]);
        assert_eq!(outcome(&response, "tests::inner").status, "pass");
    }

    /// A selection runs only what was named, and names are matched EXACTLY.
    #[test]
    fn an_exact_selection_runs_only_that_test() {
        let mut files: BTreeMap<String, String> = BTreeMap::new();
        files.insert("app/Nargo.toml".into(), MANIFEST.into());
        files.insert("app/src/main.nr".into(), FOUR_WAYS.into());
        let response = run_tests(&TestVfsRequest {
            files,
            package_dir: "app".into(),
            tests: vec!["passes".to_string()],
            record: None,
        });
        assert_eq!(names(&response), vec!["passes".to_string()]);
        assert_eq!(response.passed, 1);
        assert_eq!(response.failed, 0);
    }

    /// `print` reaches the host. Tests use it for exactly the reason a pane wants
    /// it: it is the only way a passing-but-suspicious test says anything.
    #[test]
    fn printed_output_reaches_the_host() {
        let source = r#"
fn main() {}

#[test]
fn talks() {
    println("hello from a test");
    assert(1 == 1);
}
"#;
        let response = run(&[("app/src/main.nr", source)]);
        let talks = outcome(&response, "talks");
        assert_eq!(talks.status, "pass", "got {:?}", talks.message);
        assert!(
            talks.output.contains("hello from a test"),
            "print did not reach the host: {:?}",
            talks.output
        );
    }

    /// A test declares a POSITION, against the caller's own VFS keys — not an
    /// absolute host path, which a browser has none of.
    #[test]
    fn a_test_names_where_it_lives() {
        let response = run(&[("app/src/main.nr", FOUR_WAYS)]);
        let passes = outcome(&response, "passes");
        assert_eq!(passes.file.as_deref(), Some("app/src/main.nr"));
        assert_eq!(passes.line, Some(5), "the `fn passes` line, 1-based");
    }

    /// A project that does not compile refuses the RUN, and says so as a
    /// positioned diagnostic — not as "0 tests found", which is what a runner
    /// that discovered before elaborating would report.
    #[test]
    fn a_broken_project_refuses_the_run() {
        let source = "fn main() {}\n\n#[test]\nfn broken() {\n    no_such_function();\n}\n";
        let response = run(&[("app/src/main.nr", source)]);
        assert!(!response.ok);
        assert_eq!(response.stage.as_deref(), Some("check"));
        assert_eq!(response.kind.as_deref(), Some("check-error"));
        assert!(!response.diagnostics.is_empty(), "a refusal with no diagnostics names nothing");
        assert_eq!(response.diagnostics[0].file, "app/src/main.nr");
        assert!(response.tests.is_empty());
    }

    /// A missing manifest is refused at `resolve`, with the same `kind` the
    /// compile path reports — so a host branches on one vocabulary.
    #[test]
    fn a_missing_manifest_is_refused_by_name() {
        let mut files: BTreeMap<String, String> = BTreeMap::new();
        files.insert("app/src/main.nr".into(), "fn main() {}\n".into());
        let response =
            run_tests(&TestVfsRequest {
                files,
                package_dir: "app".into(),
                tests: Vec::new(),
                record: None,
            });
        assert!(!response.ok);
        assert_eq!(response.stage.as_deref(), Some("resolve"));
        assert_eq!(response.kind.as_deref(), Some("missing-manifest"));
    }

    /// A test with arguments is a fuzzing harness. It is SKIPPED and says why,
    /// which is what `nargo test --no-fuzz` does — rather than reported as a pass
    /// nobody ran or a failure nobody caused.
    #[test]
    fn a_fuzzing_harness_is_skipped_with_a_reason() {
        let source = r#"
fn main() {}

#[test]
fn takes_an_argument(x: Field) {
    assert(x == x);
}
"#;
        let response = run(&[("app/src/main.nr", source)]);
        let harness = outcome(&response, "takes_an_argument");
        assert_eq!(harness.status, "skipped");
        assert!(harness.has_arguments);
        assert!(harness.output.contains("no-fuzz"), "got {:?}", harness.output);
        assert_eq!(response.skipped, 1);
    }

    /// The wire shape, driven as a string, because that is what a browser sees.
    #[test]
    fn the_json_envelope_round_trips() {
        let request = serde_json::json!({
            "files": {
                "app/Nargo.toml": MANIFEST,
                "app/src/main.nr": FOUR_WAYS,
            },
            "package_dir": "app",
        });
        let raw = run_tests_json(&request.to_string());
        let parsed: serde_json::Value = serde_json::from_str(&raw).expect("valid JSON");
        assert_eq!(parsed["ok"], serde_json::json!(true));
        assert_eq!(parsed["passed"], serde_json::json!(2));
        assert_eq!(parsed["failed"], serde_json::json!(2));
        let tests = parsed["tests"].as_array().expect("tests is an array");
        assert_eq!(tests.len(), 4);
        // Absent-not-empty, matching `VfsResponse`: a passing test has no
        // `message` key at all, so a decoder must probe rather than index.
        let passes = tests.iter().find(|t| t["name"] == "passes").unwrap();
        assert!(passes.get("message").is_none());
        assert_eq!(passes["should_fail"], serde_json::json!(false));
    }

    fn record(sources: &[(&str, &str)], name: &str) -> TestVfsResponse {
        let mut files: BTreeMap<String, String> = BTreeMap::new();
        files.insert("app/Nargo.toml".into(), MANIFEST.into());
        for (path, source) in sources {
            files.insert((*path).into(), (*source).into());
        }
        run_tests(&TestVfsRequest {
            files,
            package_dir: "app".into(),
            tests: Vec::new(),
            record: Some(name.to_string()),
        })
    }

    /// A recording is an ARTIFACT and not a verdict, and the artifact has to be
    /// the INSTRUMENTED one.
    ///
    /// The step count is what this asserts on, not the artifact's existence.
    /// `vfs::context_for`'s header records why: an uninstrumented compile of
    /// the same test produces an artifact that is present, well-formed, carries
    /// `debug_symbols`, and traces to one event and zero steps — with every
    /// module reporting `ok`. A test asserting "we got an artifact" passes on
    /// exactly that, which is the failure this whole path exists to avoid.
    #[test]
    fn a_recorded_test_produces_an_artifact_a_tracer_can_step() {
        let source = r#"
fn main() {}

fn double(x: Field) -> Field {
    x + x
}

#[test]
fn records() {
    let a = double(3);
    assert(a == 6);
}
"#;
        let response = record(&[("app/src/main.nr", source)], "records");
        assert!(response.ok, "recording refused: {:?}", response.message);
        assert!(response.tests.is_empty(), "a recording runs no tests");
        let artifact = response.artifact.expect("an artifact");

        // THROUGH THE REAL TRACER, in this process. `noir_tracer_wasm` is a dev
        // dependency of this crate for exactly this — `compile_vfs.rs`'s own
        // contract test does the same thing for a contract, and its comment
        // gives the reason: the question "can a tracer actually STEP this?"
        // cannot be answered by reading either crate.
        let trace = noir_tracer_wasm::trace_artifact(&artifact.to_string(), "", false)
            .expect("the tracer accepted the recorded artifact");
        let steps = trace
            .events
            .iter()
            .filter(|e| matches!(e, codetracer_trace_types::TraceLowLevelEvent::Step(_)))
            .count();
        let calls = trace
            .events
            .iter()
            .filter(|e| matches!(e, codetracer_trace_types::TraceLowLevelEvent::Call(_)))
            .count();
        assert!(
            trace.events.len() > 1 && steps > 0 && calls > 0,
            "ONE-EVENT-ZERO-STEPS: {} events, {steps} steps, {calls} calls — an \
             uninstrumented compile produces exactly this and reports ok",
            trace.events.len()
        );
    }

    /// A name that is not a test is refused BY NAME, not reported as "no tests".
    #[test]
    fn recording_a_test_that_does_not_exist_says_so() {
        let response = record(&[("app/src/main.nr", FOUR_WAYS)], "no_such_test");
        assert!(!response.ok);
        assert_eq!(response.kind.as_deref(), Some("no-such-test"));
        assert!(response.message.as_deref().unwrap_or("").contains("no_such_test"));
        assert!(response.artifact.is_none());
        // CONTROL: a name that IS a test records, so the refusal above is about
        // the name and not about recording being broken.
        assert!(record(&[("app/src/main.nr", FOUR_WAYS)], "passes").ok);
    }

    /// A fuzzing harness has no single execution to record, and says that
    /// rather than recording an input map nobody asked for.
    #[test]
    fn recording_a_fuzzing_harness_is_refused_with_a_reason() {
        let source = "fn main() {}\n\n#[test]\nfn takes(x: Field) { assert(x == x); }\n";
        let response = record(&[("app/src/main.nr", source)], "takes");
        assert!(!response.ok);
        assert_eq!(response.kind.as_deref(), Some("test-takes-arguments"));
        assert!(response.artifact.is_none());
    }

    /// Recording and running are DIFFERENT requests over the same tree, and
    /// asking for one must not silently do the other.
    #[test]
    fn recording_runs_no_tests_and_running_records_nothing() {
        let recorded = record(&[("app/src/main.nr", FOUR_WAYS)], "passes");
        assert!(recorded.artifact.is_some());
        assert_eq!(recorded.passed, 0);
        assert_eq!(recorded.failed, 0);

        let ran = run(&[("app/src/main.nr", FOUR_WAYS)]);
        assert!(ran.artifact.is_none());
        assert_eq!(ran.tests.len(), 4);
    }

    /// A test THAT FAILS still records. The recording is the point — a red test
    /// is the one a developer most wants to step through — so a compile that
    /// refused to produce an artifact for it would break the flow exactly where
    /// it matters most.
    #[test]
    fn a_failing_test_records_too() {
        let response = record(&[("app/src/main.nr", FOUR_WAYS)], "fails");
        assert!(response.ok, "recording a failing test was refused: {:?}", response.message);
        assert!(response.artifact.is_some());
    }

    #[test]
    fn a_request_that_is_not_json_is_refused_as_a_request() {
        let raw = run_tests_json("not json");
        let parsed: serde_json::Value = serde_json::from_str(&raw).expect("valid JSON");
        assert_eq!(parsed["ok"], serde_json::json!(false));
        assert_eq!(parsed["stage"], serde_json::json!("request"));
        assert_eq!(parsed["kind"], serde_json::json!("bad-request"));
    }
}
