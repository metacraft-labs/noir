//! Strict `_via_ct_print_full` integration tests for the Noir tracer.
//!
//! Round 1 of M-extended fixture parity (see
//! `codetracer-specs/Planned-Features/Smart-Contract-Languages/Noir-Aztec.status.org`).
//!
//! Each test:
//!
//! 1. Locates the workspace-built `nargo` binary at
//!    `<noir>/target/{debug,release}/nargo` (or via the
//!    `CODETRACER_NARGO_BIN` env var).  If it is missing the test
//!    **fails**; see `skipping_allowed` for why, and for the
//!    explicit local opt-out.
//! 2. Runs `nargo --program-dir <fixture> trace --out-dir <tmp>`,
//!    producing a single `<package>.ct` CTFS bundle.
//! 3. Locates the `codetracer-trace-format-nim/ct-print` binary at
//!    `../../../codetracer-trace-format-nim/ct-print` (sibling
//!    workspace layout) or `CODETRACER_CT_PRINT_BIN`.  Fails if
//!    missing, on the same reasoning as (1).
//! 4. Pipes the `.ct` through `ct-print --full --strip-paths` and
//!    parses the JSON.
//! 5. Pins exact counts, function/type tables, call sequences and
//!    per-step decoded values via `assert_eq!`.  No `>=`, no
//!    `contains`, no substring matching.  No `#[ignore]`.
//!
//! Why these fixtures (out of 22 in `test_programs/trace/`)?
//!
//! * `a_1_mul` — basic `u32` arithmetic baseline, and the fixture that
//!   exercises `x *= y` (see `StatementKind::AssignOp` in
//!   `noirc_frontend::debug`).
//! * `a_2_function_calls` — three-deep call chain (main → foo → bar).
//! * `if_then_else_reduced` — branching `for` loop.
//! * `assert` — assertion-failure → `EventLogKind::Error` io_event.
//! * `types_test` — comprehensive type signature with `Field`,
//!   `u32`, `i8`, `bool`, `str<11>`, `[Field; 2]` and a user-defined
//!   `Point` struct.
//! * `multi_stmt_per_line` — column-aware step encoding.
//! * `while_loop` — assignments inside a `while` body. Added because
//!   nothing else here uses `while` or `loop`, and that gap hid a
//!   defect that silently dropped every such assignment from the
//!   trace.
//!
//! Round 2 (MN+1 in the spec) will add struct destructuring,
//! BoundedVec, generics, oracle calls, std::hash, std::ec, recursion
//! and Aztec.nr contract constructs.
//!
//! ==========================================================================
//! READ THIS BEFORE YOU DIAGNOSE A FAILURE HERE. As of 2026-08-30, on the
//! reconciled `blocktracer` (1.0.0-beta.26), **all six tests pass — and that is
//! not the same statement as "the three known defects were fixed".** One was
//! fixed, one was repinned, and one turned out to be a defect in the test
//! rather than in the recorder. The account is at the bottom of this block; do
//! not read the six greens as six answers.
//!
//! HOW TO BUILD AND RUN THEM. `codetracer_trace_writer_nim`'s `build.rs`
//! compiles a Nim static library at build time, so `nim` must be on `PATH`, and
//! the Nim sources it compiles must be provisioned once (they are pinned to the
//! trace-format revision `Cargo.toml` names; `.cargo/config.toml` points the
//! build script at them):
//!
//!     just trace-format-nim
//!     cargo build -p nargo_cli --bin nargo
//!     cargo test -p noir_tracer --features nim-writer --test test_tracer
//!
//! `ct-print` must come from the same `codetracer-trace-format-nim` revision
//! (an older one refuses the container); build it from
//! `.codetracer-deps/codetracer-trace-format-nim` and name it with
//! `CODETRACER_CT_PRINT_BIN`.
//!
//! **Rebuild `nargo` before you trust a result.** These tests SPAWN the
//! workspace `nargo` binary; `cargo test -p noir_tracer` does not rebuild it.
//! A stale `nargo` is how a baseline measurement was got wrong once already —
//! reverting `tracer_glue.rs` and re-running `cargo test` measured the OLD
//! expectations against the NEW recorder and produced an attribution that was
//! exactly backwards. Take baselines in a separate `git worktree`.
//!
//! WHAT WAS REPINNED HERE, AND WHY EACH ONE MOVED. Every count below was
//! measured, and the two causes are separated because they belong to different
//! people:
//!
//!   * `counts["values"]` and `events.len()` in all five fixtures, and the
//!     column list in `test_multi_stmt_per_line_column_aware`: **not this
//!     repository's change.** `noir/Cargo.toml:144` resolves
//!     `codetracer_trace_writer` to `codetracer_trace_writer_nim` in the
//!     sibling `codetracer-trace-format` checkout **by bare path, at no pinned
//!     revision**, and that checkout has moved 45 commits since this file was
//!     last touched. `register_step_with_column`'s own doc comment there now
//!     reads: *"Current split-stream traces therefore carry one absolute step
//!     at the requested `(line, column)` instead of an intermediate column-1
//!     step plus a separate delta step."* That is `[1, 9, 1, 27, 1, 45]`
//!     becoming `[9, 27, 45]`, and it is `values` going from `2·steps - 1` to
//!     `steps` (19 -> 10, 33 -> 17, 21 -> 11, 155 -> 78, 47 -> 24).
//!
//!   * `counts["types"]` and the `types` table in `a_2_function_calls`,
//!     `assert` and `types_test`: **this repository's change, and it was not
//!     declared.** Rendering a `Field` as `ValueRecord::String` instead of
//!     `ValueRecord::Int` removes exactly ONE type-table entry — the nameless
//!     companion that gets registered for a `TypeKind::Int` type the first
//!     time it carries an `Int` VALUE. Measured across three fixtures in a
//!     clean worktree: `assert` `[None, Field, type_1]` -> `[None, Field]`,
//!     `a_2_function_calls` `[None, Field, type_1, ()]` -> `[None, Field, ()]`,
//!     and `types_test` loses the entry after `Field` while the two companions
//!     after `u32` and `i8` survive and renumber (`type_3` -> `type_2`,
//!     `type_6` -> `type_5`). `a_1_mul`, whose only companion follows `u32`,
//!     is untouched. So the rendering change is NOT type-table-neutral, and
//!     `tracer_glue.rs`'s claim that a `Field` stays "under the SAME
//!     `(TypeKind::Int, "Field")` type record" is true of the TYPE and not of
//!     the TABLE.
//!
//! THE THREE THAT WERE RED, RE-MEASURED ACROSS THE RECONCILIATION (2026-08-30),
//! AND THEN **ALL THREE SETTLED ON 2026-08-31**. Both sides were measured, in
//! separate worktrees, with `nargo` REBUILT for each and with
//! `CODETRACER_NARGO_BIN` / `CODETRACER_CT_PRINT_BIN` set — see the skip warning
//! below, which is why "6 passed in 0.00 s" is not a result.
//!
//! Baseline, `blocktracer` @ `4d2381630` (1.0.0-beta.18): **3 pass / 3 fail.**
//! Reconciled (1.0.0-beta.26): **6 pass / 0 fail** — but that green was one fix,
//! one repin and one test defect, and the 2026-08-31 pass turned the repin into
//! a fix and the remaining two into explanations with controls. What each is
//! NOW, because "green" was never the interesting statement:
//!
//!   1. `test_a_1_mul_via_ct_print_full` — **THE DOUBT IS DISCHARGED, BY
//!      MEASUREMENT.** The question was whether the leading run of unbound `x`
//!      values should be two or three; the reconciliation re-pinned it to two
//!      and deleted the record that anything had been in doubt, leaving a
//!      correct number standing on nothing. It is two, and the cause is now
//!      asserted rather than asserted-around: `a_1_mul`'s first four steps are
//!      `(1,1)`, `(3,13)`, `(3,21)`, `(3,29)` — the entry step, then one step
//!      per parameter at that parameter's own column in the signature, with a
//!      parameter bound only after its own step is recorded. See
//!      `test_a_1_mul_parameter_binding_explains_the_leading_unbound_steps`,
//!      which derives every column from the fixture's signature line.
//!
//!   2. `test_a_2_function_calls_via_ct_print_full` — **FIXED, AND THE
//!      DECLARATION IS WHAT MADE FIXING IT VISIBLE.** `("main", 142)` in a
//!      thirteen-line file was pinned as a declared defect with a test asserting
//!      the defect was STILL THERE. Repairing the recorder on 2026-08-31 tripped
//!      that test by name — `left: 13, right: 142` — instead of passing
//!      silently, which is the entire point of declaring a defect rather than
//!      swallowing it. The cause was ONE off-by-one at end of line, not
//!      anything about `main`: a `codespan` line range includes its terminator,
//!      so the final location — the empty span at the newline after the closing
//!      brace — reported `column = line_length + 1`, the writer turned that into
//!      a byte position one past the last addressable byte, and the reader
//!      surfaced the raw cursor as a line. All three affected numbers equal
//!      `file_size - line_count`. Proved to be a byte cursor by padding a
//!      fixture without changing its line count (96 -> 106). The repair and a
//!      second defect found beside it (the column UNIT: `codespan` counts
//!      characters, the writer counts bytes) are in
//!      `debugger_glue::convert_debugger_location`; the regression test is
//!      `test_last_main_step_is_in_range_in_every_fixture`, over seven fixtures.
//!
//!   3. `test_multi_stmt_per_line_column_aware` — **WAS A DEFECT IN THE TEST,
//!      AND ITS REPLACEMENT WAS A MISATTRIBUTION.** The original assertion
//!      looked for a step on line 4 when the `assert(a + b + c == 6);` it is
//!      about is on line 3, and never reached its own assertion. The
//!      reconciliation replaced it with a pin on "line 3 produces no step",
//!      written so that "fixing the gap trips the test" — describing a fix
//!      nobody could make, because there is no gap: all three operands are
//!      compile-time constants, the SSA pipeline folds the constraint away, and
//!      a recorder cannot record a step for code that is not in the program.
//!      Established by control rather than by argument in
//!      `test_multi_stmt_line_3_assert_is_constant_folded_not_dropped`: the same
//!      program with one runtime operand produces TWO steps on line 3.
//!
//! *Two of the three "recorder defects" this suite has carried turned out not to
//! be recorder defects, and the one that was is fixed. The pattern worth keeping
//! is the mechanism, not the score: a defect that is DECLARED by a test which
//! asserts it is still there cannot be fixed quietly, and an absence that is
//! paired with a control cannot be a drop wearing a fold's label.*
//! ==========================================================================

use std::path::PathBuf;
use std::process::Command;

// -- locator helpers --------------------------------------------------------

/// Escape hatch for a developer who has not built the sibling
/// `codetracer-trace-format-nim` checkout yet.
///
/// It is **opt-in and loud**. The default is a hard failure, because the
/// previous behaviour of this file was the exact anti-pattern this suite
/// exists to prevent: every test called `record_and_dump_full`, which
/// returned `None` when either binary was missing, and every test then did
/// `else { return; }` — so a machine without `ct-print` ran six tests that
/// asserted nothing and reported `ok`. In CI, where neither `nargo` nor
/// `ct-print` is built (the workspace cannot even `cargo metadata` without
/// the sibling repositories — see `CARRY-VS-UPSTREAM.md` §5), that is a
/// green suite proving the tracer works while never once running it.
///
/// AND IT WAS MEASURED, not reasoned about. `cargo test` CAPTURES stderr for a
/// test that PASSES, so the `SKIP:` line this file used to print — written
/// precisely to make skipping loud — was the one thing the runner swallowed.
/// Reproduced on 2026-08-30 with `CARGO_TARGET_DIR` pointed away from the
/// worktree: `test result: ok. 6 passed; 0 failed` in **0.00 s**, over a tree
/// whose real result is 3 pass / 3 fail. The elapsed time was the only thing on
/// the screen that said so, which is why a baseline taken in 0.00 s over tests
/// that SPAWN a compiler is not a baseline.
///
/// Set `CODETRACER_TRACER_TESTS_ALLOW_SKIP=1` to downgrade the panic to a skip
/// while iterating locally.
///
/// **WHAT THIS COMMENT USED TO CLAIM WAS ALREADY OUT OF DATE, AND THE CORRECTION
/// IS SMALLER THAN THE CLAIM.** It said "a run under that variable still reports
/// `ok. N passed` with nothing in the summary line marking it vacuous, so it
/// inherits the whole original defect". Measured on 2026-08-31 with the opt-out
/// set and `ct-print` forced absent, the run is **not** green and was not green
/// before this change either: `test_source_views_embed_the_compiled_source`
/// ignores the opt-out and panics, and it has done since `6939457ff`, which is
/// in the merged mainline. So the sentence described the branch's state and
/// survived the merge that falsified it — this campaign's stale-reason shape,
/// in a comment about vacuity.
///
/// What was genuinely missing is narrower and still worth closing: the failure
/// that marked the run said *"a trace with no embedded source is the defect this
/// test exists to catch"*, which is **a wrong explanation for a run whose real
/// problem is that `ct-print` is not there** — and a wrong explanation is worse
/// than none, because it names a cause the reader will go and check.
/// `test_prerequisites_are_present_or_the_run_is_declared_vacuous` fails in the
/// same runs and names the actual cause and the actual consequence.
///
/// `cargo test` captures stderr for a passing test, so no amount of printing
/// from inside a skipped test can reach the summary line; a test that FAILS is
/// the only mechanism that can. The opt-out keeps its value — the other tests
/// skip instead of each panicking with a wall of text.
fn skipping_allowed() -> bool {
    matches!(std::env::var("CODETRACER_TRACER_TESTS_ALLOW_SKIP").as_deref(), Ok("1") | Ok("true"))
}

/// The vacuity guard for the `CODETRACER_TRACER_TESTS_ALLOW_SKIP` opt-out.
///
/// It is deliberately not conditional on the opt-out: with the variable unset
/// and the binaries present it asserts they are present (a real, if cheap,
/// measurement), and with the variable unset and a binary missing it takes the
/// same panic every other test takes. The case it exists for is the third one —
/// opt-out set, binary missing — where every other test in this file returns
/// early and reports `ok`.
///
/// Calibrated both ways on 2026-08-31:
///
///   * `CODETRACER_TRACER_TESTS_ALLOW_SKIP=1
///     CODETRACER_TRACER_TESTS_PRETEND_CT_PRINT_MISSING=1`: **`11 passed; 1
///     failed`** in 0.00 s — this test naming `ct-print` and the vacuity, and
///     `test_source_views_embed_the_compiled_source` naming its own subject.
///     Without this test the same run is `11 passed; 1 failed`: still red, but
///     the only thing red is a test about embedded source views, over a run
///     whose actual problem is a binary that is not there.
///   * With both binaries present: passes, and the run is **12 passed** in
///     ~1.4 s, which is the elapsed time of a suite that really spawned a
///     compiler twelve times.
///
/// The first calibration needed a mechanism of its own, and finding out why is
/// the reason `locator_override` exists: the obvious way to fake an absent
/// binary — point `CODETRACER_CT_PRINT_BIN` at a path that is not there — did
/// nothing, because the locator silently fell back to the workspace default.
/// So the first attempt at this calibration reported twelve passes and would
/// have been written down as "the guard fires".
#[test]
fn test_prerequisites_are_present_or_the_run_is_declared_vacuous() {
    // `locate_*` panic by default, so reaching the checks below at all means
    // either both are present or the opt-out is set.
    let nargo = locate_nargo("test_prerequisites_are_present_or_the_run_is_declared_vacuous");
    let ct_print = locate_ct_print("test_prerequisites_are_present_or_the_run_is_declared_vacuous");

    let mut missing: Vec<&str> = Vec::new();
    if nargo.is_none() {
        missing.push("nargo (build it with `cargo build -p nargo_cli --bin nargo`)");
    }
    if ct_print.is_none() {
        missing.push("ct-print (build the sibling codetracer-trace-format-nim checkout)");
    }

    assert!(
        missing.is_empty(),
        "THIS RUN IS VACUOUS. CODETRACER_TRACER_TESTS_ALLOW_SKIP is set and these \
         prerequisites are missing, so every other test in this file returned before \
         asserting anything: {}.\n\n\
         This failure is the only thing that puts the vacuity in the summary line — \
         `cargo test` captures a passing test's stderr, so the `SKIP:` diagnostics above \
         are invisible in CI. Build the missing binaries, or accept that this run \
         measured nothing.",
        missing.join("; "),
    );
}

/// Report a missing prerequisite: panic by default, skip only when the
/// developer has explicitly opted in via `CODETRACER_TRACER_TESTS_ALLOW_SKIP`.
fn missing_prerequisite(test_name: &str, what: &str) -> Option<PathBuf> {
    if skipping_allowed() {
        eprintln!("SKIP: {test_name} requires {what}");
        return None;
    }
    panic!(
        "{test_name} cannot run: it requires {what}\n\n\
         This is a hard failure on purpose. These tests assert on a real \
         recording made by a real `nargo trace` and decoded by a real \
         `ct-print`; with either binary missing there is nothing to assert \
         and a pass would be meaningless.\n\
         If you are iterating locally and have not built the sibling \
         `codetracer-trace-format-nim` checkout, set \
         `CODETRACER_TRACER_TESTS_ALLOW_SKIP=1` to downgrade this to a skip. \
         Do not set it in CI."
    );
}

/// Resolve an explicitly-set locator override, refusing a path that is not there.
///
/// **A SET-BUT-MISSING OVERRIDE IS A MISTAKE, NOT A MISSING PREREQUISITE, AND IT
/// USED TO BE SILENT.** `CODETRACER_NARGO_BIN` and `CODETRACER_CT_PRINT_BIN`
/// were read with `if p.exists() { return Some(p) }` and no `else`, so a typo,
/// a stale path or a relative path resolved against the wrong cwd fell straight
/// through to the workspace default — and the run then measured a DIFFERENT
/// binary from the one the developer named, reporting success. That is the exact
/// hazard this file's own header warns about ("a stale `nargo` is how a baseline
/// measurement was got wrong once already"), reached through the escape hatch
/// provided to avoid it. Found on 2026-08-31 while trying to mutation-test the
/// vacuity guard below: pointing `CODETRACER_CT_PRINT_BIN` at a path that does
/// not exist changed nothing at all, and the suite reported twelve passes.
///
/// It is a `panic!` and not a skip on purpose: the opt-out exists for a binary
/// you have not BUILT, and this is a binary you have NAMED.
fn locator_override(var: &str) -> Option<PathBuf> {
    let raw = std::env::var(var).ok()?;
    if raw.trim().is_empty() {
        return None;
    }
    let p = PathBuf::from(&raw);
    assert!(
        p.exists(),
        "{var} is set to {raw:?}, which does not exist.\n\n\
         This is a hard failure rather than a fall-back to the workspace default, \
         because falling back would silently run a DIFFERENT binary from the one \
         you named and report success. Fix the path or unset {var}.",
    );
    Some(p)
}

/// Workspace root (=`noir/`).  `CARGO_MANIFEST_DIR` is `noir/tooling/tracer`,
/// so we walk up two parents.
fn noir_workspace_root() -> PathBuf {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest
        .parent()
        .and_then(|p| p.parent())
        .map(|p| p.to_path_buf())
        .expect("noir workspace root above tooling/tracer")
}

/// Locate the `nargo` binary.
///
/// Order:
///   1. `CODETRACER_NARGO_BIN` env var (absolute path).
///   2. The most recently rebuilt of `<workspace>/target/{debug,release}/nargo`
///      (so `cargo build -p nargo_cli --bin nargo` always wins over a stale
///      release binary; matches what a developer iterating on the tracer
///      expects).
///
/// Panics if none is found; returns `None` only under the explicit
/// `CODETRACER_TRACER_TESTS_ALLOW_SKIP` opt-out.
fn locate_nargo(test_name: &str) -> Option<PathBuf> {
    if let Some(p) = locator_override("CODETRACER_NARGO_BIN") {
        return Some(p);
    }

    let root = noir_workspace_root();
    let candidates: Vec<PathBuf> = ["target/debug/nargo", "target/release/nargo"]
        .iter()
        .map(|sub| root.join(sub))
        .filter(|p| p.exists())
        .collect();
    if let Some(newest) = candidates.into_iter().max_by_key(|p| {
        std::fs::metadata(p).and_then(|m| m.modified()).unwrap_or(std::time::SystemTime::UNIX_EPOCH)
    }) {
        return Some(newest);
    }

    missing_prerequisite(
        test_name,
        "the workspace `nargo` binary at <noir>/target/{debug,release}/nargo. \
         Build it with `cargo build -p nargo_cli --bin nargo` or set \
         CODETRACER_NARGO_BIN.",
    )
}

/// Locate the `ct-print` binary from `codetracer-trace-format-nim`.
///
/// Order:
///   1. `CODETRACER_CT_PRINT_BIN` env var (absolute path).
///   2. `<workspace>/../codetracer-trace-format-nim/ct-print` (sibling
///      layout in the metacraft monorepo).
///
/// Panics if neither is found; returns `None` only under the explicit
/// `CODETRACER_TRACER_TESTS_ALLOW_SKIP` opt-out.
fn locate_ct_print(test_name: &str) -> Option<PathBuf> {
    if let Some(p) = locator_override("CODETRACER_CT_PRINT_BIN") {
        return Some(p);
    }

    // The one deliberate way to make this binary ABSENT rather than misnamed,
    // which is what the vacuity guard has to be calibrated against:
    // `CODETRACER_TRACER_TESTS_PRETEND_CT_PRINT_MISSING=1`. Without it the
    // sibling checkout is always there on a developer box and the guard cannot
    // be shown to fire; with it, the run takes exactly the path a machine
    // without the sibling repository takes.
    if std::env::var("CODETRACER_TRACER_TESTS_PRETEND_CT_PRINT_MISSING").as_deref() == Ok("1") {
        return missing_prerequisite(
            test_name,
            "`ct-print` (forced absent by CODETRACER_TRACER_TESTS_PRETEND_CT_PRINT_MISSING=1)",
        );
    }

    let root = noir_workspace_root();
    let sibling = root
        .parent()
        .map(|p| p.join("codetracer-trace-format-nim").join("ct-print"))
        .filter(|p| p.exists());
    if let Some(p) = sibling {
        return Some(p);
    }

    missing_prerequisite(
        test_name,
        "`ct-print` from codetracer-trace-format-nim. Build it with \
         `just build-ct-print` in the sibling checkout (it lands at the repo \
         root, which is where this looks), or set CODETRACER_CT_PRINT_BIN.",
    )
}

/// Path to one of the existing `test_programs/trace/<name>` fixtures.
fn trace_fixture(name: &str) -> PathBuf {
    noir_workspace_root().join("test_programs").join("trace").join(name)
}

// -- record-and-decode helper -----------------------------------------------

/// Record `fixture` with `nargo trace` and return the
/// `ct-print --full --strip-paths` JSON.  Returns `None` (with the
/// matching `SKIP:` diagnostic already printed) when either binary
/// is unavailable.
fn record_and_dump_full(test_name: &str, fixture: &str) -> Option<serde_json::Value> {
    let nargo = locate_nargo(test_name)?;
    let ct_print = locate_ct_print(test_name)?;

    let tmp = tempfile::tempdir().expect("tempdir");
    let out_dir = tmp.path().join("traces");
    std::fs::create_dir_all(&out_dir).expect("create out_dir");

    let fixture_dir = trace_fixture(fixture);
    assert!(fixture_dir.exists(), "fixture not found: {}", fixture_dir.display());

    let nargo_status = Command::new(&nargo)
        .arg("--program-dir")
        .arg(&fixture_dir)
        .arg("trace")
        .arg("--out-dir")
        .arg(&out_dir)
        .output()
        .expect("nargo trace invocation");
    assert!(
        nargo_status.status.success(),
        "nargo trace failed for {}: stdout={} stderr={}",
        fixture,
        String::from_utf8_lossy(&nargo_status.stdout),
        String::from_utf8_lossy(&nargo_status.stderr)
    );

    let ct_files: Vec<PathBuf> = std::fs::read_dir(&out_dir)
        .expect("read_dir")
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.extension().map(|e| e == "ct").unwrap_or(false))
        .collect();
    assert_eq!(
        ct_files.len(),
        1,
        "expected exactly one .ct file in {} (fixture {}), got {:?}",
        out_dir.display(),
        fixture,
        ct_files
    );

    let dump = Command::new(&ct_print)
        .args(["--full", "--strip-paths"])
        .arg(&ct_files[0])
        .output()
        .expect("ct-print invocation");
    assert!(
        dump.status.success(),
        "ct-print --full failed for {}: stderr={}",
        fixture,
        String::from_utf8_lossy(&dump.stderr)
    );

    let doc: serde_json::Value =
        serde_json::from_slice(&dump.stdout).expect("ct-print --full should emit valid JSON");

    drop(tmp);
    Some(doc)
}

/// Record an ad-hoc Noir program written into a temporary package, and return
/// the `ct-print --full --strip-paths` JSON.
///
/// This exists for CONTROLS — a variant of a fixture that differs in one thing,
/// where committing a second fixture would put the pair two directories apart
/// and let them drift. `test_multi_stmt_line_3_assert_is_constant_folded_not_
/// dropped` uses it to show that the statement the fixture's `assert` compiles
/// to is absent because the compiler folded it and not because the recorder
/// dropped it; that claim is only worth anything if the near-identical program
/// which is NOT folded does produce the steps, in the same run, through the same
/// `nargo` and the same `ct-print`.
///
/// The package is created under a `tempfile::tempdir`, so it is removed with the
/// trace and nothing is left in the worktree.
fn record_and_dump_full_source(
    test_name: &str,
    package: &str,
    main_nr: &str,
    prover_toml: &str,
) -> Option<serde_json::Value> {
    let nargo = locate_nargo(test_name)?;
    let ct_print = locate_ct_print(test_name)?;

    let tmp = tempfile::tempdir().expect("tempdir");
    let program_dir = tmp.path().join(package);
    std::fs::create_dir_all(program_dir.join("src")).expect("create program src dir");
    std::fs::write(
        program_dir.join("Nargo.toml"),
        format!(
            "[package]\nname = \"{package}\"\nversion = \"0.1.0\"\ntype = \"bin\"\n\
             authors = [\"\"]\n\n[dependencies]\n"
        ),
    )
    .expect("write Nargo.toml");
    std::fs::write(program_dir.join("src").join("main.nr"), main_nr).expect("write main.nr");
    std::fs::write(program_dir.join("Prover.toml"), prover_toml).expect("write Prover.toml");

    let out_dir = tmp.path().join("traces");
    std::fs::create_dir_all(&out_dir).expect("create out_dir");

    let nargo_status = Command::new(&nargo)
        .arg("--program-dir")
        .arg(&program_dir)
        .arg("trace")
        .arg("--out-dir")
        .arg(&out_dir)
        .output()
        .expect("nargo trace invocation");
    assert!(
        nargo_status.status.success(),
        "nargo trace failed for the ad-hoc package {}: stdout={} stderr={}",
        package,
        String::from_utf8_lossy(&nargo_status.stdout),
        String::from_utf8_lossy(&nargo_status.stderr)
    );

    let ct_files: Vec<PathBuf> = std::fs::read_dir(&out_dir)
        .expect("read_dir")
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.extension().map(|e| e == "ct").unwrap_or(false))
        .collect();
    assert_eq!(
        ct_files.len(),
        1,
        "expected exactly one .ct file for the ad-hoc package {}, got {:?}",
        package,
        ct_files
    );

    let dump = Command::new(&ct_print)
        .args(["--full", "--strip-paths"])
        .arg(&ct_files[0])
        .output()
        .expect("ct-print invocation");
    assert!(
        dump.status.success(),
        "ct-print --full failed for the ad-hoc package {}: stderr={}",
        package,
        String::from_utf8_lossy(&dump.stderr)
    );

    let doc: serde_json::Value =
        serde_json::from_slice(&dump.stdout).expect("ct-print --full should emit valid JSON");

    drop(tmp);
    Some(doc)
}

// -- helpers for slicing the decoded doc into pin-friendly chunks -----------

fn string_array<'a>(doc: &'a serde_json::Value, key: &str) -> Vec<&'a str> {
    doc[key]
        .as_array()
        .unwrap_or_else(|| panic!("`{}` should be a JSON array; got {}", key, doc[key]))
        .iter()
        .map(|v| {
            v.as_str().unwrap_or_else(|| panic!("entry of `{}` should be a string; got {}", key, v))
        })
        .collect()
}

fn observed_call_sequence(doc: &serde_json::Value) -> Vec<String> {
    doc["events"]
        .as_array()
        .expect("events array")
        .iter()
        .filter(|e| e["kind"] == "call_entry")
        .map(|e| e["function"].as_str().expect("call_entry.function str").to_string())
        .collect()
}

/// The one `call_entry` / `call_exit` event of `function` in `events`.
///
/// Every trace opens with the writer's `<toplevel>` frame (function id 0),
/// which carries the entry step `TraceSink::start` registers before `main`
/// is called, and closes with its exit after `main`'s. So the program's
/// own frame is neither the first nor the last event; it is looked up by
/// name, and a second frame of the same name fails here.
fn the_event<'a>(
    events: &'a [serde_json::Value],
    kind: &str,
    function: &str,
) -> &'a serde_json::Value {
    let found: Vec<&serde_json::Value> =
        events.iter().filter(|e| e["kind"] == kind && e["function"] == function).collect();
    assert_eq!(found.len(), 1, "expected exactly one {kind} of {function}; got {found:?}");
    found[0]
}

/// The arguments one `call_entry` carries, as `(varname, value)` in the order the call record
/// stores them — which is the callee's parameter order.
///
/// Every argument must name its variable: an argument whose `varname` the reader could not
/// resolve fails here instead of being skipped, so a test comparing the names cannot be satisfied
/// by a record that lost one.
fn call_args(entry: &serde_json::Value) -> Vec<(&str, &serde_json::Value)> {
    entry["args"]
        .as_array()
        .unwrap_or_else(|| panic!("call_entry.args should be a JSON array; got {entry}"))
        .iter()
        .map(|arg| {
            let name = arg["varname"]
                .as_str()
                .unwrap_or_else(|| panic!("every call argument names its variable; got {arg}"));
            (name, &arg["value"])
        })
        .collect()
}

/// Just the names of [`call_args`], for an exact-equality assertion on the parameter list.
fn call_arg_names(entry: &serde_json::Value) -> Vec<&str> {
    call_args(entry).into_iter().map(|(name, _)| name).collect()
}

/// A `ValueRecord::Int` argument's integer, asserting the variant first so an `Int` that turned
/// into anything else fails by name rather than reading as `None`.
fn int_value(v: &serde_json::Value) -> i64 {
    assert_eq!(v["kind"].as_str(), Some("Int"), "expected a ValueRecord::Int; got {v}");
    v["i"].as_i64().unwrap_or_else(|| panic!("an Int carries `i`; got {v}"))
}

fn observed_event_kinds(doc: &serde_json::Value) -> Vec<String> {
    // Filter out `sekDeltaColumn` aux cursor-nudges (FU-Column-Aware-
    // Nav-Noir) so fixture assertions that pre-date column-aware mode
    // see one event per user-visible step.
    doc["events"]
        .as_array()
        .expect("events array")
        .iter()
        .filter(|e| !is_aux_column_step(e))
        .map(|e| e["kind"].as_str().expect("event.kind str").to_string())
        .collect()
}

/// True for column-aware auxiliary `sekDeltaColumn` step events.
fn is_aux_column_step(e: &serde_json::Value) -> bool {
    e["kind"] == "step" && e["step_kind"] == "sekDeltaColumn"
}

fn assert_path_strip_normalised(doc: &serde_json::Value, fixture: &str) {
    // The initial entry step must point at the real Noir source file, not the
    // generated trace output path. `--strip-paths` keeps it relative to the
    // package or workspace root.
    let paths = string_array(doc, "paths");
    assert_eq!(paths.len(), 1, "paths count for {}: {:?}", fixture, paths);
    assert!(
        paths[0].ends_with("src/main.nr"),
        "path must be the fixture src/main.nr; got {} (fixture {})",
        paths[0],
        fixture
    );
}

/// A `Field`-typed value's small integer, decoded from the rendering `tracer_glue.rs` now uses.
///
/// **THE SHAPE IS ASSERTED, NOT TOLERATED.** A `Field` is 254 bits and no longer arrives as
/// `ValueRecord::Int`: `aztec-avm-runtime/SOURCE-MAPPING.md` §4 settled the rendering by measuring
/// five candidates against both pinned readers, and the verdict is `0x` + 64 lowercase big-endian
/// hex in `ValueRecord::String`, under the same `(TypeKind::Int, "Field")` type record, so that one
/// field element has one spelling on both sides of a joined Aztec recording. This helper therefore
/// asserts the variant, the `0x` prefix, the FIXED 66-character width (no leading-zero stripping)
/// and lowercase hex before it decodes anything — a helper that merely parsed the number would let
/// the rendering drift back without a test noticing.
///
/// It also asserts the top 48 hex digits are zero, which is what makes returning an `i64` honest:
/// these fixtures' fields are small, and a value that had grown past 64 bits would fail here rather
/// than be silently truncated the way `to_i128() as i64` used to truncate it.
fn field_small_int(v: &serde_json::Value) -> i64 {
    assert_eq!(
        v["kind"].as_str(),
        Some("String"),
        "a Field renders as ValueRecord::String; see tracer_glue.rs's Field arm: {v}"
    );
    let text = v["text"].as_str().expect("a Field's String carries text");
    assert_eq!(text.len(), 66, "0x + 64 hex, fixed width: {text}");
    assert!(text.starts_with("0x"), "a Field is 0x-prefixed: {text}");
    let body = &text[2..];
    assert!(
        body.chars().all(|c| c.is_ascii_digit() || ('a'..='f').contains(&c)),
        "lowercase hex only: {text}"
    );
    assert!(body[..48].chars().all(|c| c == '0'), "this fixture's Field fits in 64 bits: {text}");
    i64::from_str_radix(&body[48..], 16).expect("the low 64 bits parse")
}

// ===========================================================================
// Round 1 fixtures
// ===========================================================================

/// `a_1_mul.nr` — basic `u32` multiplication chain (12^8 = 429981696).
///
/// Pins: 2 calls (`<toplevel>`, then main), 14 step events, 0 io_events,
/// the function table is `[<toplevel>, main]`, the type table is exactly
/// `[None, u32]` (each type once, under its own name), the varname table
/// is `[x, y, z]`, and the per-step value of `x` mutates through the
/// expected sequence 3 → 12 → 144 → 20736 → 429981696.
///
/// THE FRAME SHAPE every fixture below shares: the writer's `<toplevel>`
/// frame opens first and holds exactly one step — the line-1 entry step
/// `TraceSink::start` registers before `main` is called — and `main`'s own
/// `call_entry` follows it, so `main` begins at its first real step. On
/// the way out `main` exits and then `<toplevel>` does.
#[test]
fn test_a_1_mul_via_ct_print_full() {
    let Some(doc) = record_and_dump_full("test_a_1_mul_via_ct_print_full", "a_1_mul") else {
        return;
    };

    // ---- metadata ----------------------------------------------------------
    assert_eq!(doc["metadata"]["program"].as_str(), Some("a_1_mul"));
    assert_eq!(doc["metadata"]["args"].as_array().unwrap().len(), 0);

    // ---- counts ------------------------------------------------------------
    let counts = &doc["counts"];
    assert_eq!(counts["paths"].as_u64(), Some(1), "paths; counts={counts}");
    assert_eq!(counts["functions"].as_u64(), Some(2), "functions; counts={counts}");
    assert_eq!(counts["varnames"].as_u64(), Some(3), "varnames; counts={counts}");
    assert_eq!(counts["types"].as_u64(), Some(2), "types; counts={counts}");
    // Re-pinned after the 2026-08 upstream reconciliation (upstream/master
    // 3d3a1ce78). Two independent shifts:
    //   * the trace writer no longer emits an auxiliary `sekDeltaColumn`
    //     cursor-nudge step between every pair of real steps, so
    //     `values == steps` and `events.len() == steps + calls * 2 + io`;
    //   * upstream's rewritten SSA pipeline changes step granularity.
    // Structural facts (function/varname/type tables, call sequence, return
    // values, io events, per-step variable values) were diffed against the
    // pre-merge trace for all 21 `test_programs/trace` fixtures and are
    // unchanged; only step granularity and some columns moved.
    assert_eq!(counts["steps"].as_u64(), Some(14), "steps; counts={counts}");
    assert_eq!(counts["calls"].as_u64(), Some(2), "calls; counts={counts}");
    assert_eq!(counts["values"].as_u64(), Some(14), "values; counts={counts}");
    assert_eq!(counts["io_events"].as_u64(), Some(0), "io_events; counts={counts}");

    // ---- tables ------------------------------------------------------------
    assert_eq!(string_array(&doc, "functions"), vec!["<toplevel>", "main"]);
    assert_eq!(string_array(&doc, "varnames"), vec!["x", "y", "z"]);
    assert_eq!(string_array(&doc, "types"), vec!["None", "u32"]);
    assert_path_strip_normalised(&doc, "a_1_mul");

    // ---- event shape -------------------------------------------------------
    let events = doc["events"].as_array().unwrap();
    // 2 call_entry + 14 step events + 2 call_exit = 18 wire-level events.
    assert_eq!(events.len(), 18, "2 call_entry + 14 steps + 2 call_exit");
    assert_eq!(observed_call_sequence(&doc), vec!["<toplevel>".to_string(), "main".to_string()]);
    assert_eq!(
        observed_event_kinds(&doc),
        vec![
            "call_entry",
            "step",
            "call_entry",
            "step",
            "step",
            "step",
            "step",
            "step",
            "step",
            "step",
            "step",
            "step",
            "step",
            "step",
            "step",
            "step",
            "call_exit",
            "call_exit",
        ]
    );

    // ---- call_entry args ----------------------------------------------------
    // `main(mut x: u32, y: u32, z: u32)` called with `Prover.toml`'s 3, 4 and
    // 429981696. The parameters are bound one step per parameter AFTER the frame
    // appears (see the binding test below), so the recorder holds `main`'s call
    // record until all three are bound and only then writes it — see
    // `TracingContext::update_record`'s pending call. The `mut` the signature
    // carries is not part of the name.
    let entry = the_event(events, "call_entry", "main");
    assert_eq!(call_arg_names(entry), vec!["x", "y", "z"], "main's args; entry={entry}");
    let args = call_args(entry);
    assert_eq!(int_value(args[0].1), 3, "main's x; entry={entry}");
    assert_eq!(int_value(args[1].1), 4, "main's y; entry={entry}");
    assert_eq!(int_value(args[2].1), 429981696, "main's z; entry={entry}");

    // ---- per-step `x` value sequence (column-aware) -----------------------
    let xs: Vec<Option<i64>> = events
        .iter()
        .filter(|e| e["kind"] == "step" && !is_aux_column_step(e))
        .map(|e| {
            e["vars"]
                .as_array()
                .unwrap()
                .iter()
                .find(|v| v["varname"] == "x")
                .and_then(|v| v["value"]["i"].as_i64())
        })
        .collect();
    // Each `x *= y;` line surfaces two steps: the right-hand-side read
    // (column 10) and the instrumented assignment (column 5), so every value
    // of `x` is observed twice before the next multiplication.
    //
    // THE ONE LEADING `None`, AND WHY STEP 2 ALREADY READS 3. The recorder's
    // full (line, column) sequence for `a_1_mul` explains the head of this
    // vector exactly, and `test_a_1_mul_parameter_binding_explains_the_
    // leading_unbound_steps` below turns the explanation into assertions:
    //
    //   step 1  line 1 col 1   — the historical entry step `ensure_trace_started`
    //                            emits via `TraceSink::start(path, Line(1))`,
    //                            in `<toplevel>`. Nothing is bound.
    //   step 2  line 3 col 13  — `main`'s first step, at the column of `x` in
    //                            `fn main(mut x: u32, …)`: `x`'s OWN binding
    //                            step. The FRAME has no `x` yet — a parameter is
    //                            bound after its step is recorded — but the step
    //                            carries `main`'s three arguments, because the
    //                            call record that precedes it does: the trace
    //                            format registers every call argument as a
    //                            variable of the callee's next step as well
    //                            (`TraceWriter::arg`;
    //                            `codetracer-trace-format-spec/trace-events.md`,
    //                            "Recorder Integration — Staging Values").
    //   step 3  line 3 col 21  — the column of `y`. The frame's `x` reads 3.
    //
    // So the run of `None`s is one: the entry step, which belongs to the
    // writer's frame and not to `main`. It would be two if `main`'s call record
    // were written without its arguments, which is what a record written when
    // the frame appears — before any parameter is bound — produces.
    assert_eq!(
        xs,
        vec![
            None,
            Some(3),
            Some(3),
            Some(3),
            Some(3),
            Some(3),
            Some(12),
            Some(12),
            Some(144),
            Some(144),
            Some(20736),
            Some(20736),
            Some(429981696),
            Some(429981696),
        ]
    );

    // ---- call_exit ---------------------------------------------------------
    let exit = the_event(events, "call_exit", "main");
    assert_eq!(exit["return_value"]["kind"].as_str(), Some("Void"));
    assert_eq!(events[events.len() - 2], *exit, "main exits just before <toplevel>");
    assert_eq!(events.last().unwrap()["function"].as_str(), Some("<toplevel>"));
}

/// THE LEADING UNBOUND STEP IN `a_1_mul`'s VALUE SEQUENCE, ESTABLISHED.
///
/// `test_a_1_mul_via_ct_print_full` pins `xs` as `[None, Some(3), …]`. This test
/// asserts the structure that produces that head instead of restating it.
///
/// `a_1_mul`'s first four steps are `(1,1)`, `(3,13)`, `(3,21)`, `(3,29)` — the
/// entry step, then one step per parameter AT THAT PARAMETER'S OWN COLUMN in
/// `fn main(mut x: u32, y: u32, z: u32) {`. A parameter's value is bound in the
/// frame after its own step is recorded, so the frame has no `x` at step 2, `x`
/// but no `y` at step 3, `x` and `y` but no `z` at step 4, and all three from
/// step 5.
///
/// Step 2 nonetheless carries all three values. It is `main`'s first step, and
/// the call record in front of it carries `main`'s arguments; the trace format
/// registers each call argument as a variable of the callee's next step as well
/// (`TraceWriter::arg`; `codetracer-trace-format-spec/trace-events.md`,
/// "Recorder Integration — Staging Values"). The recorder can only give the call
/// record those arguments because it holds the record until the frame's
/// parameters are bound, and writes it, ahead of the steps it held, at step 5's
/// update (see `PendingCall` in `src/lib.rs`).
///
/// Every column used here is DERIVED from the fixture's own signature line
/// rather than typed, so a recorder that started binding parameters eagerly,
/// emitted a second entry step, or wrote `main`'s call record without its
/// arguments fails here by name rather than moving a number in a list nobody
/// can explain.
/// One step of `a_1_mul` as
/// `test_a_1_mul_parameter_binding_explains_the_leading_unbound_steps` reads it:
/// `(line, column, x, y, z)`, with each parameter `None` until it is bound.
type ParamBindingStep = (i64, i64, Option<i64>, Option<i64>, Option<i64>);

#[test]
fn test_a_1_mul_parameter_binding_explains_the_leading_unbound_steps() {
    let Some(doc) = record_and_dump_full(
        "test_a_1_mul_parameter_binding_explains_the_leading_unbound_steps",
        "a_1_mul",
    ) else {
        return;
    };

    // The signature line, read off disk, and each parameter's column in it.
    let fixture = trace_fixture("a_1_mul").join("src").join("main.nr");
    let source = std::fs::read_to_string(&fixture)
        .unwrap_or_else(|e| panic!("reading {}: {e}", fixture.display()));
    let (sig_index, sig_line) = source
        .lines()
        .enumerate()
        .find(|(_, l)| l.starts_with("fn main("))
        .expect("a_1_mul declares `fn main(`");
    let sig_line_number = sig_index as i64 + 1;
    // 1-indexed byte column of each parameter name in the signature.
    let column_of = |needle: &str| -> i64 {
        sig_line.find(needle).unwrap_or_else(|| panic!("{needle} in {sig_line:?}")) as i64 + 1
    };
    // `mut x` — find the binding, not the later `u32`s.
    let col_x = column_of("x: u32");
    let col_y = column_of("y: u32");
    let col_z = column_of("z: u32");
    assert!(
        col_x < col_y && col_y < col_z,
        "the three parameters must be distinct and in order; got {col_x}/{col_y}/{col_z}",
    );

    let steps: Vec<ParamBindingStep> = doc["events"]
        .as_array()
        .expect("events array")
        .iter()
        .filter(|e| e["kind"] == "step")
        .map(|e| {
            let var = |name: &str| {
                e["vars"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .find(|v| v["varname"] == name)
                    .and_then(|v| v["value"]["i"].as_i64())
            };
            (
                e["line"].as_i64().expect("step.line"),
                e["column"].as_i64().unwrap_or(-1),
                var("x"),
                var("y"),
                var("z"),
            )
        })
        .collect();
    assert!(steps.len() >= 5, "expected at least five steps; got {}", steps.len());

    // 1. The entry step: line 1, column 1, nothing bound.
    assert_eq!((steps[0].0, steps[0].1), (1, 1), "step 1 is the line-1 entry step");
    assert_eq!(
        (steps[0].2, steps[0].3, steps[0].4),
        (None, None, None),
        "entry step binds nothing"
    );

    // 2. `x`'s own binding step, at `x`'s column. It is `main`'s first step,
    //    so it carries the three arguments the call record carries.
    assert_eq!(
        (steps[1].0, steps[1].1),
        (sig_line_number, col_x),
        "step 2 is `x`'s binding step, at `x`'s own column in the signature",
    );
    assert_eq!(
        (steps[1].2, steps[1].3, steps[1].4),
        (Some(3), Some(4), Some(429981696)),
        "`main`'s first step carries the call's arguments",
    );

    // 3. `y`'s step: the frame has `x` now, and not `y`.
    assert_eq!((steps[2].0, steps[2].1), (sig_line_number, col_y), "step 3 is `y`'s binding step",);
    assert_eq!(steps[2].2, Some(3), "`x` reads its argument from `y`'s step onward");
    assert_eq!(steps[2].3, None, "`y` is not yet bound at its own binding step");

    // 4. `z`'s step: `x` and `y` bound, `z` not.
    assert_eq!((steps[3].0, steps[3].1), (sig_line_number, col_z), "step 4 is `z`'s binding step",);
    assert_eq!(steps[3].3, Some(4), "`y` reads its argument from `z`'s step onward");
    assert_eq!(steps[3].4, None, "`z` is not yet bound at its own binding step");

    // 5. The first body step has all three.
    assert!(
        steps[4].2.is_some() && steps[4].3.is_some() && steps[4].4.is_some(),
        "all three parameters are bound by the first body step; got {:?}",
        steps[4],
    );

    // THE CONCLUSION THE PIN NEEDED: the run of leading steps at which `x` is
    // unbound is exactly one — the entry step, which belongs to `<toplevel>`.
    // Every step of `main` reads `x`: the first from the call's arguments, the
    // rest from the frame.
    let leading_unbound = steps.iter().take_while(|s| s.2.is_none()).count();
    assert_eq!(leading_unbound, 1, "`x` should be unbound at exactly the entry step");
}

/// THE `assert` ON LINE 3 OF `multi_stmt_per_line` PRODUCES NO STEP — **AND THAT
/// IS THE COMPILER, NOT THE RECORDER.** Established on 2026-08-31; it had been
/// carried as a recorder gap ("pinned so that fixing the gap trips this test").
///
/// `multi_stmt_per_line/src/main.nr` binds `a`, `b` and `c` to the literals 1, 2
/// and 3 and then asserts `a + b + c == 6`. Every operand is a compile-time
/// constant, so the SSA pipeline proves the constraint and removes it: there is
/// no opcode left for the debugger to stop on, and a recorder cannot record a
/// step for code that is not in the program.
///
/// Measured by CONTROL rather than by argument. The same three statements with
/// `a` bound to a runtime parameter instead of a literal — the only change —
/// produce **two** steps on line 3. So the absence is a fact about constant
/// folding, and this test asserts both halves: the folded program has no line-3
/// step, and the unfolded one does. Without the second half "no step on line 3"
/// is satisfied by a recorder that dropped it, which is exactly the reading this
/// test carried before.
#[test]
fn test_multi_stmt_line_3_assert_is_constant_folded_not_dropped() {
    // --- half 1: the fixture, whose `assert` is over three literals ---------
    let Some(doc) = record_and_dump_full(
        "test_multi_stmt_line_3_assert_is_constant_folded_not_dropped",
        "multi_stmt_per_line",
    ) else {
        return;
    };
    // The fixture must still be the all-constant program this is about; if
    // somebody parameterises it, the assertion below stops meaning anything.
    let fixture_src =
        std::fs::read_to_string(trace_fixture("multi_stmt_per_line").join("src").join("main.nr"))
            .expect("reading the multi_stmt_per_line fixture");
    assert!(
        fixture_src.contains("fn main() {"),
        "this test is about a main with NO parameters, so that every operand of the \
         line-3 assert is a compile-time constant; the fixture now reads:\n{fixture_src}",
    );
    assert!(
        fixture_src.contains("assert(a + b + c == 6);"),
        "the line-3 assert this test is about is gone from the fixture",
    );
    let folded_line3 = doc["events"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|e| e["kind"] == "step" && e["line"].as_i64() == Some(3))
        .count();
    assert_eq!(folded_line3, 0, "the all-constant assert on line 3 should be folded away");

    // --- half 2: the control, same statements, one runtime operand ----------
    // Without this the assertion above is satisfied by a recorder that simply
    // drops the statement, which is what it was previously read as saying.
    let Some(control) = record_and_dump_full_source(
        "test_multi_stmt_line_3_assert_is_constant_folded_not_dropped",
        "multi_stmt_dynamic",
        "fn main(x: Field) {\n    let a: Field = x; let b: Field = 2; let c: Field = 3;\n    assert(a + b + c == 6);\n}\n",
        "x = \"1\"\n",
    ) else {
        return;
    };
    let dynamic_line3: Vec<i64> = control["events"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|e| e["kind"] == "step" && e["line"].as_i64() == Some(3))
        .filter_map(|e| e["column"].as_i64())
        .collect();
    assert!(
        !dynamic_line3.is_empty(),
        "with one runtime operand the line-3 assert must produce steps, or the \
         first half of this test is measuring a recorder that drops asserts",
    );
    // Two: the comparison's read and the instrumented constrain.
    assert_eq!(
        dynamic_line3.len(),
        2,
        "expected the dynamic assert to surface two steps on line 3; got columns {dynamic_line3:?}",
    );
}

/// `a_2_function_calls.nr` — main → foo → bar twice.
///
/// Pins: 6 calls (`<toplevel>` + 1 main + 2 foo + 2 bar), 20 step
/// events, 0 io_events, function table = [<toplevel>, main, foo, bar]
/// in ensure order, type table = [None, Field, "()", "()"], call-entry
/// sequence = [<toplevel>, main, foo, bar, foo, bar], and Field-typed
/// argument values.
///
/// The two `"()"` entries are two types: types are interned by
/// `(kind, name)`, and the recorder registers the unit type under two
/// kinds — `TypeKind::None` for a return with no value (`bar`'s), and
/// `TypeKind::Raw` for a unit VALUE (`foo`'s tail expression `bar(x)`).
#[test]
fn test_a_2_function_calls_via_ct_print_full() {
    let Some(doc) =
        record_and_dump_full("test_a_2_function_calls_via_ct_print_full", "a_2_function_calls")
    else {
        return;
    };

    assert_eq!(doc["metadata"]["program"].as_str(), Some("a_2_function_calls"));

    let counts = &doc["counts"];
    assert_eq!(counts["paths"].as_u64(), Some(1), "paths; counts={counts}");
    assert_eq!(counts["functions"].as_u64(), Some(4), "functions; counts={counts}");
    assert_eq!(counts["varnames"].as_u64(), Some(2), "varnames; counts={counts}");
    assert_eq!(counts["types"].as_u64(), Some(4), "types; counts={counts}");
    // See `test_a_1_mul_via_ct_print_full` for the re-pinning rationale.
    assert_eq!(counts["steps"].as_u64(), Some(20), "steps; counts={counts}");
    assert_eq!(counts["calls"].as_u64(), Some(6), "calls; counts={counts}");
    assert_eq!(counts["values"].as_u64(), Some(20), "values; counts={counts}");
    assert_eq!(counts["io_events"].as_u64(), Some(0), "io_events; counts={counts}");

    assert_eq!(string_array(&doc, "functions"), vec!["<toplevel>", "main", "foo", "bar"]);
    assert_eq!(string_array(&doc, "varnames"), vec!["x", "y"]);
    assert_eq!(string_array(&doc, "types"), vec!["None", "Field", "()", "()"]);
    assert_path_strip_normalised(&doc, "a_2_function_calls");

    // 6 call_entry + 20 step events + 6 call_exit = 32 wire-level events.
    let events = doc["events"].as_array().unwrap();
    assert_eq!(events.len(), 32);
    assert_eq!(
        observed_call_sequence(&doc),
        vec![
            "<toplevel>".to_string(),
            "main".to_string(),
            "foo".to_string(),
            "bar".to_string(),
            "foo".to_string(),
            "bar".to_string(),
        ]
    );
    let observed_steps: Vec<(&str, i64)> = events
        .iter()
        .filter(|e| e["kind"] == "step" && !is_aux_column_step(e))
        .map(|e| {
            (
                e["function"].as_str().expect("step.function str"),
                e["line"].as_i64().expect("step.line i64"),
            )
        })
        .collect();
    // Column-aware mode no longer collapses param-binding events on
    // the function-declaration line, so each call surfaces extra
    // steps on its `fn ...` line.  The trace now visits main, foo
    // and bar at their function-declaration lines too (line 9 for
    // main, 5 for foo, 1 for bar) before the body lines.
    assert_eq!(
        observed_steps,
        vec![
            ("<toplevel>", 1),
            ("main", 9),
            ("main", 9),
            ("main", 10),
            ("foo", 5),
            ("foo", 6),
            ("bar", 1),
            ("bar", 2),
            ("bar", 2),
            ("foo", 6),
            ("main", 10),
            ("foo", 5),
            ("foo", 6),
            ("bar", 1),
            ("bar", 2),
            ("bar", 2),
            ("foo", 6),
            ("main", 11),
            ("main", 12),
            // Line 13 is `main`'s closing brace, and it used to read **142** —
            // the byte cursor at end-of-source, in a thirteen-line file. Fixed
            // on 2026-08-31 in `debugger_glue::convert_debugger_location`,
            // whose comment carries the mechanism; pinned in range by
            // `test_last_main_step_is_in_range_in_every_fixture`.
            ("main", 13),
        ]
    );

    // ---- call_entry args ----------------------------------------------------
    // Every call carries its arguments, in call order: `main(x: Field, y: pub
    // Field)` with `Prover.toml`'s 4 and 5, then `foo(x)` -> `bar(x)` with 4,
    // then `foo(y)` -> `bar(y)` with 5. `<toplevel>` is the writer's frame and
    // has none. The callee's parameter NAME is recorded, not the caller's
    // expression, so the second `foo` is called with `x = 5`. Each parameter is
    // bound after the frame appears, so this holds only because the recorder
    // defers each call record until its frame's parameters are bound (see a_1_mul).
    let call_args_seen: Vec<(String, Vec<(String, i64)>)> = events
        .iter()
        .filter(|e| e["kind"] == "call_entry")
        .map(|e| {
            (
                e["function"].as_str().expect("call_entry.function str").to_string(),
                call_args(e)
                    .into_iter()
                    .map(|(name, value)| (name.to_string(), field_small_int(value)))
                    .collect(),
            )
        })
        .collect();
    let expected_call_args: Vec<(String, Vec<(String, i64)>)> = [
        ("<toplevel>", vec![]),
        ("main", vec![("x", 4), ("y", 5)]),
        ("foo", vec![("x", 4)]),
        ("bar", vec![("y", 4)]),
        ("foo", vec![("x", 5)]),
        ("bar", vec![("y", 5)]),
    ]
    .into_iter()
    .map(|(f, args)| (f.to_string(), args.into_iter().map(|(n, v)| (n.to_string(), v)).collect()))
    .collect();
    assert_eq!(call_args_seen, expected_call_args);

    // foo's return_value is `()` (Raw with text "()", type_id 4)
    let foo_exits: Vec<&str> = events
        .iter()
        .filter(|e| e["kind"] == "call_exit" && e["function"] == "foo")
        .map(|e| e["return_value"]["r"].as_str().unwrap_or("<missing>"))
        .collect();
    assert_eq!(foo_exits, vec!["()", "()"]);
}

/// THE `("main", 142)` DEFECT — **FIXED ON 2026-08-31, AND THIS IS ITS REGRESSION
/// TEST.** It was declared here as a defect first; the declaration is what made
/// fixing it trip a test by name instead of passing silently, and it did.
///
/// WHAT IT WAS. `a_2_function_calls/src/main.nr` is thirteen lines long and the
/// recorder recorded `main`'s last step at line **142**. `a_1_mul` recorded 264
/// in a nine-line file and `multi_stmt_per_line` 96 in a four-line one, so it
/// was the tree's defect and not one fixture's. Measured on both sides of the
/// 2026-08 upstream reconciliation — `blocktracer` @ `4d2381630` (beta.18) and
/// this tree (beta.26), `nargo` rebuilt for each — the numbers were identical,
/// so it was never a regression.
///
/// WHAT IT WAS, MECHANICALLY, AND HOW THAT WAS ESTABLISHED RATHER THAN GUESSED.
/// All three numbers equal `file_size - line_count`, which is the sum of the
/// per-line byte lengths — i.e. the global byte cursor at end of source, not a
/// line at all. Proved by padding line 2 of `multi_stmt_per_line` with ten
/// spaces WITHOUT changing its line count: the number moved **96 -> 106**. The
/// cause is one off-by-one, in `debugger_glue::convert_debugger_location`: a
/// `codespan` line range includes its terminator, so the debugger's final
/// location — the empty span at the newline after `main`'s closing brace —
/// reported `column = line_length + 1`. The writer encodes a step as
/// `sum(len(1..line-1)) + (column - 1)`, so that column produced a position one
/// past the last addressable byte, the reader could not invert it, and it
/// surfaced the raw cursor as the line. Every traced program hit it exactly
/// once. The fix clamps the column to the line's byte length; that comment
/// carries the full account and the second defect found beside it (the column
/// unit: `codespan` counts characters, the writer counts bytes).
///
/// WHAT THIS TEST NOW ASSERTS, and why each part can fail:
///
///   * the last step of `main` is IN RANGE for the file — the property that was
///     false;
///   * it is exactly the fixture's LAST line, which is `main`'s closing brace in
///     all three — a stronger statement than "in range", and the one that says
///     the clamp landed on a meaningful position rather than merely a legal one;
///   * and it is NOT the old byte cursor, which is **derived** here as
///     `file_size - line_count` rather than typed, so the regression is named by
///     its mechanism and the needle cannot rot when a fixture is edited.
///
/// The length and the cursor are both read off disk. The earlier version of this
/// test pinned the length (`assert_eq!(fixture_lines, 13)`) beside the range
/// comparison, which made `142 > 13` true by construction — an assertion that
/// could not fail, in the test written to declare a defect.
#[test]
fn test_last_main_step_is_in_range_in_every_fixture() {
    // The three that carried the defect, plus the four that did not — because
    // "the fix holds where the defect was" and "the fix broke nothing where it
    // was not" are different statements and both are cheap here.
    const FIXTURES: [&str; 7] = [
        "a_2_function_calls",
        "a_1_mul",
        "multi_stmt_per_line",
        "assert",
        "if_then_else_reduced",
        "while_loop",
        "types_test",
    ];

    // Both arms of the partition below must actually be taken, or a branch that
    // stopped being reachable would read as agreement.
    let mut aborted_seen = 0usize;
    let mut completed_seen = 0usize;

    for name in FIXTURES {
        let Some(doc) =
            record_and_dump_full("test_last_main_step_is_in_range_in_every_fixture", name)
        else {
            return;
        };

        let fixture = trace_fixture(name).join("src").join("main.nr");
        let source = std::fs::read_to_string(&fixture)
            .unwrap_or_else(|e| panic!("reading {}: {e}", fixture.display()));
        let fixture_lines = source.lines().count() as i64;
        assert!(
            fixture_lines > 0,
            "{name}: the fixture read as empty, so nothing below measures anything",
        );
        // The value the recorder used to emit, derived from the fixture rather
        // than typed: the sum of the per-line byte lengths, which is
        // `file_size - line_count` for a file whose every line ends in `\n`.
        let old_byte_cursor = source.lines().map(|l| l.len() as i64).sum::<i64>();

        let steps: Vec<i64> = doc["events"]
            .as_array()
            .expect("events array")
            .iter()
            .filter(|e| e["kind"] == "step" && e["function"] == "main")
            .filter_map(|e| e["line"].as_i64())
            .collect();
        assert!(
            !steps.is_empty(),
            "{name}: main recorded no steps at all, so nothing below measures anything",
        );

        let last = *steps.last().unwrap();
        assert!(
            last >= 1 && last <= fixture_lines,
            "{name}: main's last step is at line {last}, outside a {fixture_lines}-line file. \
             This is the byte-cursor defect returning; see \
             `debugger_glue::convert_debugger_location`.",
        );
        // WHERE THE LAST STEP SHOULD BE, PARTITIONED BY WHETHER THE PROGRAM
        // FINISHED — derived from the recording, not from a list typed here.
        // A run that recorded an error event aborted at the failing statement
        // and never reached the closing brace; `assert`'s `assert(a != b)` on
        // line 4 of a five-line file is exactly that, and pinning "the last
        // line" for every fixture would have been a claim that is false for it.
        // (It was: this assertion read `last == fixture_lines` unconditionally
        // on its first run and went red on `assert` for precisely this reason.)
        let aborted = doc["counts"]["io_events"].as_u64().unwrap_or(0) > 0;
        if aborted {
            aborted_seen += 1;
            assert!(
                last < fixture_lines,
                "{name}: the run recorded an error event, so it aborted before the \
                 closing brace; its last step is at line {last} of {fixture_lines}",
            );
        } else {
            completed_seen += 1;
            assert_eq!(
                last, fixture_lines,
                "{name}: this run recorded no error event, so main ran to its closing \
                 brace on line {fixture_lines}; its last step is at line {last}",
            );
        }
        assert_ne!(
            last, old_byte_cursor,
            "{name}: main's last step is the end-of-source BYTE CURSOR ({old_byte_cursor}), \
             which is the defect this test exists for",
        );
        // …and the derivation is only meaningful if the two could differ. Every
        // fixture here is longer than one line, so they do.
        assert_ne!(
            old_byte_cursor, fixture_lines,
            "{name}: the derived byte cursor equals the line count, so the assertion above \
             could not have failed — pick a fixture where they differ",
        );
    }

    assert!(
        aborted_seen >= 1,
        "no fixture in this set aborted, so the aborted arm of the partition above was \
         never taken and is not being measured",
    );
    assert!(
        completed_seen >= 1,
        "no fixture in this set completed, so the closing-brace arm of the partition \
         above was never taken and is not being measured",
    );
}

/// `if_then_else_reduced.nr` — `for i in 1..11 { if i % 2 == 0 { ... } }`.
///
/// Pins: 2 calls (`<toplevel>`, main), 68 step events (10-iteration
/// loop with branching body), 0 io_events.  The varname table reflects the
/// `let mut result = x; for i in 1..11 { ... }` declaration order
/// (`result` introduced in line 2, `i` introduced as the loop
/// induction variable).  The final `result` value is 600 (the
/// asserted `z`).
#[test]
fn test_if_then_else_reduced_via_ct_print_full() {
    let Some(doc) =
        record_and_dump_full("test_if_then_else_reduced_via_ct_print_full", "if_then_else_reduced")
    else {
        return;
    };

    assert_eq!(doc["metadata"]["program"].as_str(), Some("if_then_else_reduced"));

    let counts = &doc["counts"];
    assert_eq!(counts["paths"].as_u64(), Some(1), "paths; counts={counts}");
    assert_eq!(counts["functions"].as_u64(), Some(2), "functions; counts={counts}");
    assert_eq!(counts["varnames"].as_u64(), Some(5), "varnames; counts={counts}");
    assert_eq!(counts["types"].as_u64(), Some(2), "types; counts={counts}");
    // See `test_a_1_mul_via_ct_print_full` for the re-pinning rationale.
    assert_eq!(counts["steps"].as_u64(), Some(68), "steps; counts={counts}");
    assert_eq!(counts["calls"].as_u64(), Some(2), "calls; counts={counts}");
    assert_eq!(counts["values"].as_u64(), Some(68), "values; counts={counts}");
    assert_eq!(counts["io_events"].as_u64(), Some(0), "io_events; counts={counts}");

    assert_eq!(string_array(&doc, "functions"), vec!["<toplevel>", "main"]);
    assert_eq!(string_array(&doc, "varnames"), vec!["x", "y", "z", "result", "i"]);
    assert_eq!(string_array(&doc, "types"), vec!["None", "u32"]);
    assert_path_strip_normalised(&doc, "if_then_else_reduced");

    // 2 call_entry + 68 step events + 2 call_exit = 72 wire-level events.
    let events = doc["events"].as_array().unwrap();
    assert_eq!(events.len(), 72);
    assert_eq!(observed_call_sequence(&doc), vec!["<toplevel>".to_string(), "main".to_string()]);

    // `main(x: u32, y: pub u32, z: u32)` with `Prover.toml`'s 600, 5, 600; the
    // call record is deferred until all three are bound (see a_1_mul).
    let entry = the_event(events, "call_entry", "main");
    assert_eq!(call_arg_names(entry), vec!["x", "y", "z"], "main's args; entry={entry}");
    let args = call_args(entry);
    assert_eq!(int_value(args[0].1), 600, "main's x; entry={entry}");
    assert_eq!(int_value(args[1].1), 5, "main's y; entry={entry}");
    assert_eq!(int_value(args[2].1), 600, "main's z; entry={entry}");

    // The penultimate step (line 11, the `assert(result == z)` line)
    // should surface `result == 600` so the assertion can succeed.
    let final_result = events
        .iter()
        .rev()
        .filter(|e| e["kind"] == "step" && !is_aux_column_step(e))
        .find_map(|e| {
            e["vars"]
                .as_array()?
                .iter()
                .find(|v| v["varname"] == "result")
                .map(|v| v["value"]["i"].as_i64().unwrap())
        })
        .expect("result must appear in some step");
    assert_eq!(final_result, 600);

    // call_exit returns Void (main has no `-> T` annotation).
    let exit = the_event(events, "call_exit", "main");
    assert_eq!(exit["return_value"]["kind"].as_str(), Some("Void"));
}

/// `assert.nr` — `assert(a != b)` where a == b == 12 (assertion fails).
///
/// Pins: 2 calls (`<toplevel>`, main), 12 step events, EXACTLY 1 io_event tagged
/// `Error` (the exact `EventLogKind` `register_error` records) carrying
/// the Brillig failure string.  The variables
/// `a` (=12), `b` (=15 → 12 after the `b = y + 2` reassignment), `x`,
/// `y` all surface as Field-typed Int values.
#[test]
fn test_assert_via_ct_print_full() {
    let Some(doc) = record_and_dump_full("test_assert_via_ct_print_full", "assert") else {
        return;
    };

    assert_eq!(doc["metadata"]["program"].as_str(), Some("assert"));

    let counts = &doc["counts"];
    assert_eq!(counts["paths"].as_u64(), Some(1), "paths; counts={counts}");
    assert_eq!(counts["functions"].as_u64(), Some(2), "functions; counts={counts}");
    assert_eq!(counts["varnames"].as_u64(), Some(4), "varnames; counts={counts}");
    assert_eq!(counts["types"].as_u64(), Some(2), "types; counts={counts}");
    // See `test_a_1_mul_via_ct_print_full` for the re-pinning rationale.
    assert_eq!(counts["steps"].as_u64(), Some(12), "steps; counts={counts}");
    assert_eq!(counts["calls"].as_u64(), Some(2), "calls; counts={counts}");
    assert_eq!(counts["values"].as_u64(), Some(12), "values; counts={counts}");
    assert_eq!(counts["io_events"].as_u64(), Some(1), "io_events; counts={counts}");

    assert_eq!(string_array(&doc, "functions"), vec!["<toplevel>", "main"]);
    assert_eq!(string_array(&doc, "varnames"), vec!["x", "y", "a", "b"]);
    assert_eq!(string_array(&doc, "types"), vec!["None", "Field"]);
    assert_path_strip_normalised(&doc, "assert");

    // 2 call_entry + 12 step events + 1 io + 2 call_exit = 17 wire-level events.
    let events = doc["events"].as_array().unwrap();
    assert_eq!(events.len(), 17);
    assert_eq!(observed_call_sequence(&doc), vec!["<toplevel>".to_string(), "main".to_string()]);

    // The single io_event must carry `EventLogKind::Error` — events.dat
    // records the exact kind, and ct-print names it — and the text must match
    // the recorder's assertion-failure stringification (no payload in
    // this fixture, so the bare Nargo error string surfaces).
    let io_events: Vec<&serde_json::Value> = events.iter().filter(|e| e["kind"] == "io").collect();
    assert_eq!(io_events.len(), 1);
    let io = io_events[0];
    assert_eq!(io["io_kind"].as_str(), Some("Error"));

    // `main(x: Field, y: pub Field)` with `Prover.toml`'s 10 and 10. The run
    // ends in an error; both parameters are bound long before the failing
    // `assert`, so the deferred call record is complete when it is written.
    let entry = the_event(events, "call_entry", "main");
    assert_eq!(call_arg_names(entry), vec!["x", "y"], "main's args; entry={entry}");
    let args = call_args(entry);
    assert_eq!(field_small_int(args[0].1), 10, "main's x; entry={entry}");
    assert_eq!(field_small_int(args[1].1), 10, "main's y; entry={entry}");
    assert_eq!(
        io["text"].as_str(),
        Some("Failed to solve program: 'Failed to solve brillig function'")
    );

    // Last user-visible step before the io error surfaces (a, b, x, y).
    // With column-aware mode the trace lands `b = y + 2` *before* the
    // io error fires, so the recorded pre-error values are
    // a=12, b=12 (post-reassignment), x=10, y=10.  Older line-only
    // traces saw `b=15` here because the reassignment step was
    // collapsed into the post-error step.
    let pre_io_step = events
        .iter()
        .take_while(|e| e["kind"] != "io")
        .filter(|e| e["kind"] == "step" && !is_aux_column_step(e))
        .last()
        .expect("must have at least one user-visible step before io");
    let vars: std::collections::BTreeMap<&str, i64> = pre_io_step["vars"]
        .as_array()
        .unwrap()
        .iter()
        // `main(x: Field, y: pub Field)`, and `a`/`b` are Field-typed too, so every one of these
        // four goes through the OQ-4 rendering rather than through `["i"]`.
        .map(|v| (v["varname"].as_str().unwrap(), field_small_int(&v["value"])))
        .collect();
    assert_eq!(vars[&"a"], 12);
    assert_eq!(vars[&"b"], 12);
    assert_eq!(vars[&"x"], 10);
    assert_eq!(vars[&"y"], 10);
}

/// `types_test/main.nr` — comprehensive type signature with `Field`,
/// `u32`, `i8`, `bool`, `str<11>`, `[Field; 2]`, and a user-defined
/// `Point` struct.  (The Nargo package name in this fixture is
/// `zk_dungeon`, hence the trace file basename.)
///
/// Pins: 2 calls (`<toplevel>`, main), 24 step events, 0 io_events, the
/// function table is exactly `[<toplevel>, main]`, the type table contains
/// every distinct type the recorder ensures, once each (in ensure order:
/// None, Field, u32, Point, i8, Bool, String, Array<2, ..>), the varname
/// table is the parameter list
/// plus `result`, and the `Point` argument decodes as
/// `ValueRecord::Struct` with two `Field`-typed children.
#[test]
fn test_types_test_via_ct_print_full() {
    let Some(doc) = record_and_dump_full("test_types_test_via_ct_print_full", "types_test") else {
        return;
    };

    // The Nargo package is named `zk_dungeon` (per the fixture's
    // `Nargo.toml`), so `metadata.program` reflects that, not the
    // directory name.
    assert_eq!(doc["metadata"]["program"].as_str(), Some("zk_dungeon"));

    let counts = &doc["counts"];
    assert_eq!(counts["paths"].as_u64(), Some(1), "paths; counts={counts}");
    assert_eq!(counts["functions"].as_u64(), Some(2), "functions; counts={counts}");
    assert_eq!(counts["varnames"].as_u64(), Some(9), "varnames; counts={counts}");
    assert_eq!(counts["types"].as_u64(), Some(8), "types; counts={counts}");
    // See `test_a_1_mul_via_ct_print_full` for the re-pinning rationale.
    assert_eq!(counts["steps"].as_u64(), Some(24), "steps; counts={counts}");
    assert_eq!(counts["calls"].as_u64(), Some(2), "calls; counts={counts}");
    assert_eq!(counts["values"].as_u64(), Some(24), "values; counts={counts}");
    assert_eq!(counts["io_events"].as_u64(), Some(0), "io_events; counts={counts}");

    assert_eq!(string_array(&doc, "functions"), vec!["<toplevel>", "main"]);
    assert_eq!(
        string_array(&doc, "varnames"),
        vec!["a", "b", "c", "d", "e", "f", "g", "h", "result"]
    );
    assert_eq!(
        string_array(&doc, "types"),
        vec!["None", "Field", "u32", "Point", "i8", "Bool", "String", "Array<2, ..>"]
    );
    assert_path_strip_normalised(&doc, "types_test");

    // 2 call_entry + 24 step events + 2 call_exit = 28 wire-level events.
    let events = doc["events"].as_array().unwrap();
    assert_eq!(events.len(), 28);
    assert_eq!(observed_call_sequence(&doc), vec!["<toplevel>".to_string(), "main".to_string()]);

    // ---- call_entry args ------------------------------------------------
    // `main(a: Field, b: u32, c: Point, d: Field, e: i8, f: bool, g: str<11>,
    // h: [Field; 2])`. The parameters bind one per step on the declaration
    // line after the frame appears, and the recorder defers the call record
    // until all eight are bound (see a_1_mul), so the record carries all eight
    // with `Prover.toml`'s values, in declaration order. The FIELD-typed ones —
    // a, c.x, c.y, d, h[0], h[1] — carry the OQ-4 rendering; b (u32) and e (i8)
    // are ordinary integers.
    let entry = the_event(events, "call_entry", "main");
    let expected_names: &[&str] = &["a", "b", "c", "d", "e", "f", "g", "h"];
    assert_eq!(call_arg_names(entry), expected_names.to_vec(), "main's args; entry={entry}");
    let args: std::collections::BTreeMap<&str, &serde_json::Value> =
        call_args(entry).into_iter().collect();
    assert_eq!(field_small_int(args[&"a"]), 1);
    assert_eq!(int_value(args[&"b"]), 2);
    assert_eq!(args[&"c"]["kind"].as_str(), Some("Struct"));
    let c_arg_fields = args[&"c"]["field_values"].as_array().unwrap();
    assert_eq!(c_arg_fields.len(), 2);
    assert_eq!(field_small_int(&c_arg_fields[0]), 9);
    assert_eq!(field_small_int(&c_arg_fields[1]), 10);
    assert_eq!(field_small_int(args[&"d"]), 3);
    assert_eq!(int_value(args[&"e"]), 4);
    assert_eq!(args[&"f"]["kind"].as_str(), Some("Bool"));
    assert_eq!(args[&"f"]["b"].as_bool(), Some(true));
    assert_eq!(args[&"g"]["kind"].as_str(), Some("String"));
    assert_eq!(args[&"g"]["text"].as_str(), Some("hello world"));
    assert_eq!(args[&"h"]["kind"].as_str(), Some("Sequence"));
    assert_eq!(args[&"h"]["is_slice"].as_bool(), Some(false));
    let h_arg_elems = args[&"h"]["elements"].as_array().unwrap();
    assert_eq!(h_arg_elems.len(), 2);
    assert_eq!(field_small_int(&h_arg_elems[0]), 7);
    assert_eq!(field_small_int(&h_arg_elems[1]), 8);

    // The same values as STEP variables. The first step that surfaces all
    // eight is `main`'s first step, which carries the call's arguments (see
    // a_1_mul); the frame itself binds them one by one on the declaration line
    // after it.
    let first_body_vars: std::collections::BTreeMap<&str, &serde_json::Value> = events
        .iter()
        .filter(|e| e["kind"] == "step" && !is_aux_column_step(e))
        .find_map(|e| {
            let vars = e["vars"].as_array()?;
            let map: std::collections::BTreeMap<&str, &serde_json::Value> =
                vars.iter().map(|v| (v["varname"].as_str().unwrap(), &v["value"])).collect();
            if expected_names.iter().all(|n| map.contains_key(n)) { Some(map) } else { None }
        })
        .expect("a step must surface all params a..h");
    // `main(a: Field, b: u32, c: Point, d: Field, e: i8, f: bool, g: str<11>, h: [Field; 2])`.
    // The FIELD-typed ones — a, c.x, c.y, d, h[0], h[1] — carry the OQ-4 rendering; b (u32) and
    // e (i8) are ordinary integers and still `ValueRecord::Int`. Both kinds are asserted here,
    // which is what stops "everything is a String now" from passing.
    assert_eq!(field_small_int(&first_body_vars[&"a"]), 1);
    assert_eq!(first_body_vars[&"b"]["kind"].as_str(), Some("Int"));
    assert_eq!(first_body_vars[&"b"]["i"].as_i64(), Some(2));
    assert_eq!(first_body_vars[&"c"]["kind"].as_str(), Some("Struct"));
    let c_fields = first_body_vars[&"c"]["field_values"].as_array().unwrap();
    assert_eq!(c_fields.len(), 2);
    assert_eq!(field_small_int(&c_fields[0]), 9);
    assert_eq!(field_small_int(&c_fields[1]), 10);
    assert_eq!(field_small_int(&first_body_vars[&"d"]), 3);
    assert_eq!(first_body_vars[&"e"]["kind"].as_str(), Some("Int"));
    assert_eq!(first_body_vars[&"e"]["i"].as_i64(), Some(4));
    assert_eq!(first_body_vars[&"f"]["kind"].as_str(), Some("Bool"));
    assert_eq!(first_body_vars[&"f"]["b"].as_bool(), Some(true));
    assert_eq!(first_body_vars[&"g"]["kind"].as_str(), Some("String"));
    assert_eq!(first_body_vars[&"g"]["text"].as_str(), Some("hello world"));
    assert_eq!(first_body_vars[&"h"]["kind"].as_str(), Some("Sequence"));
    // h: [Field; 2] elements 7 and 8 (Sequence array, not slice).
    assert_eq!(first_body_vars[&"h"]["is_slice"].as_bool(), Some(false));
    let h_elems = first_body_vars[&"h"]["elements"].as_array().unwrap();
    assert_eq!(h_elems.len(), 2);
    assert_eq!(field_small_int(&h_elems[0]), 7);
    assert_eq!(field_small_int(&h_elems[1]), 8);

    // call_exit returns Void
    let exit = the_event(events, "call_exit", "main");
    assert_eq!(exit["return_value"]["kind"].as_str(), Some("Void"));
}

/// The `noir_space_ship` shape: calls whose parameters are a STRUCT and an
/// ARRAY, a nested call that passes them on with a scalar, and a call with no
/// parameters.
///
/// CodeTracer's own `test-programs/noir_space_ship` renders every call-trace
/// entry as `()` when its call records carry no arguments, and that program's
/// `main` takes two `Field`s and two `[Field; 8]`s while `iterate_asteroids` /
/// `calculate_damage` pass them on. This program is the same shape in a dozen
/// lines, so the struct and array arms of the call-argument path are pinned
/// here rather than only through the scalar fixtures.
///
/// Pins, by exact equality:
///
/// * the call sequence and each call's argument names and values;
/// * that `base_damage`, which declares no parameter, carries none — its
///   record is written when its frame appears, because there is nothing to
///   wait for;
/// * that every `call_entry` is followed directly by a step of the callee:
///   holding a record back until its parameters are bound must not let the
///   steps it waited behind leak out in front of it;
/// * that a call's first step carries the call's arguments as its variables.
///   That is the trace format's contract for a call argument:
///   `TraceWriter::arg` registers each argument as a variable of the callee's
///   next step as well as on the call record
///   (`codetracer-trace-format-spec/trace-events.md`, "Recorder Integration —
///   Staging Values").
#[test]
fn test_struct_and_array_call_arguments_are_recorded() {
    let main_nr = "\
struct Ship {
    shield: u32,
    regen: u32,
}

fn calculate_damage(ship: Ship, masses: [u32; 3], index: u32) -> u32 {
    let damage = masses[index] / 10;
    ship.shield + ship.regen - damage
}

fn base_damage() -> u32 {
    1
}

fn main(ship: Ship, masses: [u32; 3]) -> pub u32 {
    let first = calculate_damage(ship, masses, 1);
    first - base_damage()
}
";
    let prover_toml = "\
masses = [\"10\", \"20\", \"30\"]

[ship]
shield = \"100\"
regen = \"5\"
";
    let Some(doc) = record_and_dump_full_source(
        "test_struct_and_array_call_arguments_are_recorded",
        "space_ship_shape",
        main_nr,
        prover_toml,
    ) else {
        return;
    };
    let events = doc["events"].as_array().expect("events array");

    assert_eq!(
        observed_call_sequence(&doc),
        vec!["<toplevel>", "main", "calculate_damage", "base_damage"]
            .into_iter()
            .map(String::from)
            .collect::<Vec<_>>()
    );

    // `Ship { shield: 100, regen: 5 }` as a `Struct` of two `Int` fields.
    let assert_ship = |v: &serde_json::Value, what: &str| {
        assert_eq!(v["kind"].as_str(), Some("Struct"), "{what}: {v}");
        let fields: Vec<i64> =
            v["field_values"].as_array().unwrap().iter().map(int_value).collect();
        assert_eq!(fields, vec![100, 5], "{what}: Ship {{ shield, regen }}; {v}");
    };
    // `[10, 20, 30]` as a non-slice `Sequence` of `Int`s.
    let assert_masses = |v: &serde_json::Value, what: &str| {
        assert_eq!(v["kind"].as_str(), Some("Sequence"), "{what}: {v}");
        assert_eq!(v["is_slice"].as_bool(), Some(false), "{what}: {v}");
        let elements: Vec<i64> = v["elements"].as_array().unwrap().iter().map(int_value).collect();
        assert_eq!(elements, vec![10, 20, 30], "{what}: {v}");
    };

    let main_entry = the_event(events, "call_entry", "main");
    assert_eq!(call_arg_names(main_entry), vec!["ship", "masses"], "entry={main_entry}");
    let main_args = call_args(main_entry);
    assert_ship(main_args[0].1, "main's ship");
    assert_masses(main_args[1].1, "main's masses");

    let damage_entry = the_event(events, "call_entry", "calculate_damage");
    assert_eq!(
        call_arg_names(damage_entry),
        vec!["ship", "masses", "index"],
        "entry={damage_entry}"
    );
    let damage_args = call_args(damage_entry);
    assert_ship(damage_args[0].1, "calculate_damage's ship");
    assert_masses(damage_args[1].1, "calculate_damage's masses");
    assert_eq!(int_value(damage_args[2].1), 1, "calculate_damage's index");

    let base_entry = the_event(events, "call_entry", "base_damage");
    assert_eq!(call_arg_names(base_entry), Vec::<&str>::new(), "entry={base_entry}");

    // Each call record is followed directly by a step of its callee.
    for function in ["main", "calculate_damage", "base_damage"] {
        let at = events
            .iter()
            .position(|e| e["kind"] == "call_entry" && e["function"] == function)
            .unwrap();
        let next = &events[at + 1];
        assert_eq!(next["kind"].as_str(), Some("step"), "after {function}'s call_entry: {next}");
        assert_eq!(next["function"].as_str(), Some(function), "after {function}'s call_entry");
    }

    // Each entry step carries that callee's arguments, including the empty
    // frame of a zero-parameter function with a constant body.
    for function in ["main", "calculate_damage", "base_damage"] {
        let at = events
            .iter()
            .position(|e| e["kind"] == "call_entry" && e["function"] == function)
            .unwrap();
        let next = &events[at + 1];
        let step_var_names: Vec<&str> = next["vars"]
            .as_array()
            .unwrap()
            .iter()
            .map(|v| v["varname"].as_str().unwrap())
            .collect();
        assert_eq!(
            step_var_names,
            call_arg_names(&events[at]),
            "{function}'s first step carries its arguments; step={next}"
        );
    }

    let base_definition = main_nr
        .lines()
        .position(|line| line.starts_with("fn base_damage"))
        .expect("fixture declares base_damage") as u64
        + 1;
    let base_steps: Vec<_> = events
        .iter()
        .filter(|event| event["kind"] == "step" && event["function"] == "base_damage")
        .collect();
    assert_eq!(base_steps.len(), 1, "constant callee owns one entry anchor");
    assert_eq!(
        base_steps[0]["line"].as_u64(),
        Some(base_definition),
        "constant callee's step is at its definition, not the caller's call site"
    );
    assert_eq!(base_steps[0]["vars"], serde_json::json!([]));

    // Each call, including main, returns the value computed from its arguments.
    let damage_exit = the_event(events, "call_exit", "calculate_damage");
    assert_eq!(int_value(&damage_exit["return_value"]), 103, "100 + 5 - 20 / 10");
    let base_exit = the_event(events, "call_exit", "base_damage");
    assert_eq!(int_value(&base_exit["return_value"]), 1);
    let main_exit = the_event(events, "call_exit", "main");
    assert_eq!(int_value(&main_exit["return_value"]), 102, "103 - 1");
}

#[test]
fn test_main_public_return_value_via_ct_print_full() {
    let Some(doc) = record_and_dump_full_source(
        "test_main_public_return_value_via_ct_print_full",
        "pub_return",
        "fn main(x: u32, y: u32) -> pub u32 {\n    let z = x + y;\n    z\n}\n",
        "x = 100\ny = 2\n",
    ) else {
        return;
    };
    let events = doc["events"].as_array().expect("events array");
    let main_exit = the_event(events, "call_exit", "main");
    assert_eq!(
        main_exit["return_value"],
        serde_json::json!({"kind": "Int", "i": 102, "type_id": 1}),
        "main must close with its typed public result"
    );
    assert_eq!(events[events.len() - 2], *main_exit, "main exits before toplevel");
    let toplevel_exit = the_event(events, "call_exit", "<toplevel>");
    assert_eq!(toplevel_exit["return_value"]["kind"], "Void");
}

/// Calls whose parameter list the instrumenter can only PARTLY bind, and a
/// recursive call.
///
/// The instrumenter binds a parameter only under a plain name: `_` binds
/// nothing, and a destructuring pattern such as `(a, b)` binds `a` and `b`
/// under their own names, never under the pattern's text, which is the name
/// the frame declares (`noirc_frontend::debug`, `insert_var` and
/// `pattern_vars`). A recorder that waited for EVERY declared parameter would
/// wait for `shift`'s forever: it would hold the call record, and every step
/// behind it, until `shift` returned, and then write it with the values the
/// frame had at the end — `v = 18` after the body's two assignments, instead
/// of the `4` it was called with.
///
/// Pins, by exact equality:
///
/// * `shift`'s record carries `v = 4`, its value at the call. `_` and `(a, b)`
///   are not recorded as arguments: no variable has either name;
/// * each of the three nested `countdown` calls carries its own `n`: the frame
///   stack is compared by function name, and a recursive entry is a new,
///   deeper frame of the same name;
/// * every `call_entry` is followed directly by a step of the callee.
#[test]
fn test_partly_bindable_parameters_and_recursion_record_the_call_time_arguments() {
    let main_nr = "\
fn shift(mut v: u32, _: u32, (a, b): (u32, u32)) -> u32 {
    v = v + a;
    v = v * b;
    v
}

unconstrained fn countdown(n: u32) -> u32 {
    if n == 0 { 0 } else { n + countdown(n - 1) }
}

fn main(x: u32) -> pub u32 {
    let s = shift(x, 7, (2, 3));
    // Safety: a pure function of its argument, called only to be traced.
    let c = unsafe { countdown(2) };
    s + c
}
";
    let Some(doc) = record_and_dump_full_source(
        "test_partly_bindable_parameters_and_recursion_record_the_call_time_arguments",
        "partly_bindable",
        main_nr,
        "x = \"4\"\n",
    ) else {
        return;
    };
    let events = doc["events"].as_array().expect("events array");

    let calls: Vec<(String, Vec<(String, i64)>)> = events
        .iter()
        .filter(|e| e["kind"] == "call_entry")
        .map(|e| {
            (
                e["function"].as_str().expect("call_entry.function str").to_string(),
                call_args(e).into_iter().map(|(n, v)| (n.to_string(), int_value(v))).collect(),
            )
        })
        .collect();
    let expected: Vec<(String, Vec<(String, i64)>)> = [
        ("<toplevel>", vec![]),
        ("main", vec![("x", 4)]),
        ("shift", vec![("v", 4)]),
        ("countdown", vec![("n", 2)]),
        ("countdown", vec![("n", 1)]),
        ("countdown", vec![("n", 0)]),
    ]
    .into_iter()
    .map(|(f, args)| (f.to_string(), args.into_iter().map(|(n, v)| (n.to_string(), v)).collect()))
    .collect();
    assert_eq!(calls, expected);

    let shift_exit = the_event(events, "call_exit", "shift");
    assert_eq!(int_value(&shift_exit["return_value"]), 18, "(4 + 2) * 3");

    for (at, entry) in events.iter().enumerate().filter(|(_, e)| e["kind"] == "call_entry") {
        let function = entry["function"].as_str().unwrap();
        if function == "<toplevel>" {
            continue;
        }
        let next = &events[at + 1];
        assert_eq!(next["kind"].as_str(), Some("step"), "after {function}'s call_entry: {next}");
        assert_eq!(next["function"].as_str(), Some(function), "after {function}'s call_entry");
    }
}

/// FU-Column-Aware-Nav-Noir acceptance: three statements on a single
/// source line must surface three distinct 1-indexed columns on that
/// line in the column-aware step stream.  The fixture
/// `multi_stmt_per_line` lays them out at columns 9 / 27 / 45 of
/// `src/main.nr` line 2:
///
///     fn main() {
///         let a: Field = 1; let b: Field = 2; let c: Field = 3;
///         ...
///
/// Steps the tracer must produce on `src/main.nr`:
/// `(line=1, column=1)`, then three line-2 statements at
/// `(line=2, column=9)`, `(line=2, column=27)`, `(line=2, column=45)`,
/// and then NO step for the `assert` at all — which is on line 3, not line 4.
/// (This sentence said "then the `assert` on `(line=4, column=1)`". The fixture is
/// four lines and the `assert(a + b + c == 6);` is on the THIRD; the body was
/// corrected to pin the real gap — line 3 produces no step — and this comment was
/// left stating the off-by-one it was corrected for.)  This pins both that
/// column-aware mode is latched (`metadata.flags.has_column_aware_steps`
/// is true) and that the recorder distinguishes same-line statements at
/// the byte level via the `DeltaColumn` event.
#[test]
fn test_multi_stmt_per_line_column_aware() {
    let Some(doc) =
        record_and_dump_full("test_multi_stmt_per_line_column_aware", "multi_stmt_per_line")
    else {
        return;
    };

    // ---- column-aware flag latched on ------------------------------------
    assert_eq!(
        doc["metadata"]["flags"]["has_column_aware_steps"].as_bool(),
        Some(true),
        "tracer must opt into column-aware step encoding; metadata={}",
        doc["metadata"]
    );

    // ---- three distinct columns on the multi-statement line --------------
    // Filter to the user's source file (path ends in `src/main.nr`) so the
    // synthetic `__debug/lib.nr` brace step does not pollute the set.
    // This is the only test that asserts on column-aware wire-level
    // structure, so it bypasses the `is_aux_column_step` helper used by the
    // line-only fixtures. The writer used to interleave a `sekDeltaColumn`
    // cursor-nudge at column 1 before each real step; it no longer does, so
    // the three statements' columns are now adjacent.
    let line2_columns: Vec<i64> = doc["events"]
        .as_array()
        .expect("events array")
        .iter()
        .filter(|e| e["kind"] == "step")
        .filter(|e| e["path"].as_str().map(|p| p.ends_with("src/main.nr")).unwrap_or(false))
        .filter(|e| e["line"].as_i64() == Some(2))
        .filter_map(|e| e["column"].as_i64())
        .collect();
    assert_eq!(
        line2_columns,
        vec![9_i64, 27, 45],
        "expected the three statements on line 2 to surface columns \
         9 / 27 / 45, one absolute step each; \
         got {line2_columns:?}",
    );

    // Sanity: column 1 on line 1 (the `fn main()` entry step), so the test
    // still catches a regression that drops the column field entirely.
    let line1_col = doc["events"]
        .as_array()
        .unwrap()
        .iter()
        .find(|e| e["kind"] == "step" && e["line"].as_i64() == Some(1))
        .and_then(|e| e["column"].as_i64());
    assert_eq!(line1_col, Some(1), "line 1 entry step column");

    // The `assert(a + b + c == 6);` on line 3 produces no step of its own, and
    // as of 2026-08-31 that is ESTABLISHED AS THE COMPILER'S DOING rather than
    // carried as a recorder gap: every operand is a compile-time constant, the
    // SSA pipeline folds the constraint away, and there is no opcode to stop on.
    // `test_multi_stmt_line_3_assert_is_constant_folded_not_dropped` owns that
    // claim and carries the control that makes it a measurement — the same
    // program with one runtime operand produces two steps on line 3. The
    // assertion is kept here as well because this test is the one that reads
    // line-by-line structure, but the reason lives with the control.
    //
    // (Two earlier revisions of this comment were wrong in different ways: one
    // looked for the step on line 4, an off-by-one that never reached its own
    // assertion; the next pinned the absence as a defect "so that fixing the gap
    // trips this test", which described a fix nobody could make.)
    let assert_line_step = doc["events"]
        .as_array()
        .unwrap()
        .iter()
        .any(|e| e["kind"] == "step" && e["line"].as_i64() == Some(3));
    assert!(
        !assert_line_step,
        "line 3's assert is over three literals and is expected to be constant-folded away; \
         see test_multi_stmt_line_3_assert_is_constant_folded_not_dropped",
    );
}

/// Assignments inside a `while` body must be recorded.
///
/// This is the end-to-end half of the `debug::tests` unit tests added
/// alongside it. `DebugInstrumenter::walk_statement` used to end in a
/// `_ => {}` catch-all, and `StatementKind::{Loop, While}` fell into it, so
/// the instrumenter never descended into a `while` or `loop` body. The
/// defect predates the `beta.18` -> `beta.26` sync: `Loop` and `While` were
/// already `StatementKind` variants at `beta.18` and already hit that same
/// catch-all. It was never a regression, just never noticed — no fixture in
/// `test_programs/trace` used `while` or `loop`, so nothing recorded it and
/// nothing failed.
///
/// Recorded on a `beta.18` build, `while_loop` yields exactly four value
/// observations — `n`, `out`, `acc = 0`, `i = 0` — and then nothing for the
/// remaining five iterations: the debugger shows `acc` frozen at `0` while
/// the circuit computes `10`.
///
/// Counting steps would not catch this. Only the recorded *values* do.
#[test]
fn test_while_loop_body_assignments_are_recorded() {
    let Some(doc) =
        record_and_dump_full("test_while_loop_body_assignments_are_recorded", "while_loop")
    else {
        return;
    };

    assert_eq!(doc["metadata"]["program"].as_str(), Some("while_loop"));

    // Every point at which a variable's recorded value differs from the value
    // it last held, in order: the observation sequence a debugger user sees.
    let mut last: std::collections::HashMap<String, i64> = std::collections::HashMap::new();
    let mut observed: Vec<(String, i64)> = Vec::new();
    for event in doc["events"].as_array().expect("events") {
        if event["kind"] != "step" {
            continue;
        }
        for var in event["vars"].as_array().into_iter().flatten() {
            let name = var["varname"].as_str().expect("varname").to_string();
            let value = var["value"]["i"].as_i64().expect("integer value");
            if last.get(&name) != Some(&value) {
                observed.push((name.clone(), value));
                last.insert(name, value);
            }
        }
    }

    let observed: Vec<(&str, i64)> = observed.iter().map(|(n, v)| (n.as_str(), *v)).collect();
    assert_eq!(
        observed,
        vec![
            // entry bindings
            ("n", 5),
            ("out", 10),
            ("acc", 0),
            ("i", 0),
            // five iterations of the `while` body
            ("i", 1),
            ("acc", 1),
            ("i", 2),
            ("acc", 3),
            ("i", 3),
            ("acc", 6),
            ("i", 4),
            ("acc", 10),
            ("i", 5),
        ],
        "the `while` body must contribute an observation per assignment per \
         iteration; before the `StatementKind::While` arm existed this \
         stopped after the four entry bindings"
    );
}

// ===========================================================================
// Self-containment: the container must carry the source it recorded
// ===========================================================================

/// Every source path the recording mentions must have its **text** embedded
/// in the container.
///
/// The trace format's central portability promise is that a trace "is
/// self-contained in that it includes all source code and debug symbols
/// needed for executing the replay on a different machine from where the
/// program was built and recorded"
/// (`codetracer-specs/Trace-Files/Trace-Files-Overview.md`), and the
/// seek-based reader is specified against "the trace's embedded source files"
/// (`Trace-Files/Seek-Based-CTFS-Reader.md`).
///
/// Until `trace_circuit` called `register_source_view`, `nargo trace`
/// containers reported `source_views: []`: the recorder read
/// `DebugFile::source` only to compute the per-line length table and then
/// dropped it. Every other gate in this repository still passed — the
/// manifest validated, the steps replayed, `ct-print` succeeded — because
/// none of them ever asked whether the code being stepped through could be
/// *displayed*. This test is the gate that asks.
///
/// `a_3_two_files` is the fixture of choice: three separate `.nr` files, so
/// the test pins not just "some source is present" but that each file's text
/// is filed under its own path id. A single-file fixture would pass even if
/// every view were attached to path 0.
///
/// ## What is and is not checked here
///
/// `ct-print --full` deliberately does not inline the view bytes (they would
/// swamp the JSON), so it surfaces `path_id`, `view_kind`, `view_name`,
/// `content_len` and `map_len`. This test therefore pins the exact byte
/// length of each view against the file on disk, plus the view→path
/// attribution and the view kind. Byte-for-byte content round-tripping
/// through `source_views.dat` is covered on the writer side by
/// `codetracer-trace-format-nim/tests/test_source_views.nim`.
///
/// Comparing against the on-disk file is sound *here* because the fixture is
/// compiled from that file moments earlier in this same test. The recorder
/// itself must never re-read from disk — it embeds `DebugFile::source`, the
/// text the compiler actually consumed, because a working tree can drift from
/// what was compiled and because there is no filesystem under wasm.
#[test]
fn test_source_views_embed_the_compiled_source() {
    const NAME: &str = "test_source_views_embed_the_compiled_source";
    const FIXTURE: &str = "a_3_two_files";

    // Note the `panic!` rather than the `return` the other tests use. Those
    // honour the `CODETRACER_TRACER_TESTS_ALLOW_SKIP` opt-out; this one does
    // not, on purpose. A silently-skipped assertion is exactly the failure
    // mode that let empty `source_views` ship, and the whole point of this
    // test is to be un-skippable.
    let Some(doc) = record_and_dump_full(NAME, FIXTURE) else {
        panic!(
            "{NAME} must not be skipped. Unlike the other tests here it \
             ignores CODETRACER_TRACER_TESTS_ALLOW_SKIP: a trace with no \
             embedded source is the defect this test exists to catch, and a \
             skipped run reports exactly what a broken run would."
        )
    };

    let paths = string_array(&doc, "paths");
    let views = doc["source_views"].as_array().expect("`source_views` should be a JSON array");

    // ---- the container is self-contained ------------------------------------
    assert!(
        !views.is_empty(),
        "{FIXTURE}: `source_views` is empty — the container steps through code \
         it cannot display. paths={paths:?}"
    );
    // `meta.dat` is written by the trace's first record, before any view
    // exists, so its bit 5 (`FlagHasAlternateSourceViews`) is never set: a
    // reader finds `source_views.dat` by its presence in the container's root
    // directory (`internal-files.md`, "Stream-presence flags are a hint, not a
    // gate"). The non-empty `views` above is that presence.
    assert_eq!(
        doc["counts"]["source_views"].as_u64(),
        Some(paths.len() as u64),
        "{FIXTURE}: expected one embedded source per registered path \
         (paths={paths:?}), got {} view(s): {views:?}",
        views.len()
    );

    // ---- each view is a raw, sourcemap-less view of a distinct path ---------
    let mut seen_path_ids: Vec<u64> = Vec::new();
    for view in views {
        let path_id = view["path_id"].as_u64().expect("source_view.path_id");
        assert!(
            path_id < paths.len() as u64,
            "source view names path_id {path_id} but the trace has only {} \
             path(s): {paths:?}",
            paths.len()
        );
        assert!(
            !seen_path_ids.contains(&path_id),
            "path_id {path_id} has more than one embedded source view: {views:?}"
        );
        seen_path_ids.push(path_id);

        // 0 = raw: Noir embeds the compiled text verbatim, so there is nothing
        // to map generated positions back through.
        assert_eq!(view["view_kind"].as_u64(), Some(0), "view_kind should be raw; {view}");
        assert_eq!(view["map_len"].as_u64(), Some(0), "a raw view carries no sourcemap; {view}");
        assert!(
            view["content_len"].as_u64().expect("source_view.content_len") > 0,
            "embedded source must not be empty; {view}"
        );
    }

    // ---- the text is the fixture's, and lands on the right path -------------
    // Matching on the trailing `src/<file>` rather than on the whole string
    // keeps this independent of how `--strip-paths` rewrites prefixes.
    let src_dir = trace_fixture(FIXTURE).join("src");
    let mut compared = 0usize;
    for file in ["main.nr", "foo.nr", "bar.nr"] {
        let suffix = format!("src/{file}");
        let on_disk = std::fs::read(src_dir.join(file))
            .unwrap_or_else(|err| panic!("reading {}/{file}: {err}", src_dir.display()));

        let view = views
            .iter()
            .find(|v| v["view_name"].as_str().is_some_and(|n| n.ends_with(&suffix)))
            .unwrap_or_else(|| panic!("no embedded source view for {suffix}; views={views:?}"));

        assert_eq!(
            view["content_len"].as_u64(),
            Some(on_disk.len() as u64),
            "embedded source for {suffix} must be the compiled text \
             ({} bytes on disk); view={view}",
            on_disk.len()
        );

        // The view has to hang off the same path id `register_step` interns,
        // or a reader looking up the source of one file finds another's.
        let path_id = view["path_id"].as_u64().expect("source_view.path_id") as usize;
        assert!(
            paths[path_id].ends_with(&suffix),
            "source view for {suffix} is filed under path_id {path_id}, which \
             is {:?}",
            paths[path_id]
        );
        compared += 1;
    }
    assert_eq!(
        compared, 3,
        "{FIXTURE} has three source files; all three must have been compared \
         against their on-disk bytes"
    );
}

// -- `nargo trace --test-name` ------------------------------------------------
//
// `nargo trace --test-name <name>` traces ONE `#[test]` function of the package
// instead of `main`, with the same instrumentation and the same `.ct` output.
// The name is matched the way `nargo debug --test-name` matches it: a
// substring of the test's fully-qualified name, narrowed to the exact last
// `::` segment when several tests contain it. So both `tests::test_nested`
// and the bare `test_nested` select the nested test, which is what lets a
// caller holding either form (a test catalog's selector, or a function name
// scanned out of the source) trace the test without rewriting it.
//
// The fixture is `test_programs/trace/test_functions`: a passing test, a test
// whose `assert` fails, a `#[test(should_fail)]` test, and a test nested in
// `mod tests`. Its `main` is traced by the generated `trace_test_functions`
// case in `nargo_cli`, like every other fixture here.
//
// A FAILING TEST STILL PRODUCES A TRACE. Tracing records an execution; it does
// not adjudicate one. A test whose `assert` fails is traced up to the failure,
// which is recorded as an `Error` io event — exactly how a failing `main` is
// recorded (`test_assert_via_ct_print_full`) — and `nargo trace` exits 0
// because the trace was written. A `#[test(should_fail)]` test is the same
// execution: it fails, so its trace ends in the same `Error` event. The
// expectation inversion that makes it a PASSING test is `nargo test`'s verdict,
// and is deliberately not re-applied here: the trace says what ran.

/// Run `nargo trace --test-name <test>` on `fixture`; return the process
/// output and, when exactly one `.ct` was written, its `ct-print --full`
/// JSON. `None` only under the explicit skip opt-out.
fn trace_test_and_dump(
    test_name: &str,
    fixture: &str,
    test: &str,
) -> Option<(std::process::Output, Option<serde_json::Value>)> {
    let nargo = locate_nargo(test_name)?;
    let ct_print = locate_ct_print(test_name)?;

    let tmp = tempfile::tempdir().expect("tempdir");
    let out_dir = tmp.path().join("traces");

    let fixture_dir = trace_fixture(fixture);
    assert!(fixture_dir.exists(), "fixture not found: {}", fixture_dir.display());

    let output = Command::new(&nargo)
        .arg("--program-dir")
        .arg(&fixture_dir)
        .arg("trace")
        .arg("--test-name")
        .arg(test)
        .arg("--out-dir")
        .arg(&out_dir)
        .output()
        .expect("nargo trace --test-name invocation");

    let ct_files: Vec<PathBuf> = std::fs::read_dir(&out_dir)
        .map(|entries| {
            entries
                .filter_map(|e| e.ok())
                .map(|e| e.path())
                .filter(|p| p.extension().map(|e| e == "ct").unwrap_or(false))
                .collect()
        })
        .unwrap_or_default();
    if ct_files.len() != 1 {
        return Some((output, None));
    }

    let dump = Command::new(&ct_print)
        .args(["--full", "--strip-paths"])
        .arg(&ct_files[0])
        .output()
        .expect("ct-print invocation");
    assert!(
        dump.status.success(),
        "ct-print --full failed for {fixture} --test-name {test}: stderr={}",
        String::from_utf8_lossy(&dump.stderr)
    );
    let doc: serde_json::Value =
        serde_json::from_slice(&dump.stdout).expect("ct-print --full should emit valid JSON");
    drop(tmp);
    Some((output, Some(doc)))
}

fn io_event_kinds(doc: &serde_json::Value) -> Vec<String> {
    doc["events"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|e| e["kind"] == "io")
        .map(|e| e["io_kind"].as_str().unwrap_or("").to_string())
        .collect()
}

/// Asserts the run succeeded and produced a trace, and returns it.
fn expect_test_trace(
    result: (std::process::Output, Option<serde_json::Value>),
    test: &str,
) -> serde_json::Value {
    let (output, doc) = result;
    assert!(
        output.status.success(),
        "nargo trace --test-name {test} failed: stdout={} stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    doc.unwrap_or_else(|| panic!("nargo trace --test-name {test} wrote no single .ct"))
}

#[test]
fn test_trace_test_name_traces_the_named_test_instead_of_main() {
    let name = "test_trace_test_name_traces_the_named_test_instead_of_main";
    let Some(result) = trace_test_and_dump(name, "test_functions", "test_passes") else {
        return;
    };
    let doc = expect_test_trace(result, "test_passes");

    // The traced entry point is the test, and `main` never ran.
    let functions = string_array(&doc, "functions");
    assert!(functions.contains(&"test_passes"), "functions={functions:?}");
    assert!(functions.contains(&"add_one"), "functions={functions:?}");
    assert!(!functions.contains(&"main"), "main must not be traced; functions={functions:?}");
    let calls = observed_call_sequence(&doc);
    assert_eq!(
        calls,
        vec!["<toplevel>".to_string(), "test_passes".to_string(), "add_one".to_string()]
    );
    // A zero-parameter entry point has nothing to bind, so its call record is
    // written as soon as its frame appears and carries no argument. `add_one`
    // binds `v` one step after its frame appears, and its record carries it.
    let events = doc["events"].as_array().unwrap();
    let test_entry = the_event(events, "call_entry", "test_passes");
    assert_eq!(call_arg_names(test_entry), Vec::<&str>::new(), "entry={test_entry}");
    let add_one_entry = the_event(events, "call_entry", "add_one");
    assert_eq!(call_arg_names(add_one_entry), vec!["v"], "entry={add_one_entry}");
    assert_eq!(field_small_int(call_args(add_one_entry)[0].1), 2, "entry={add_one_entry}");
    // Instrumented like `main` is: the test's locals are recorded.
    let varnames = string_array(&doc, "varnames");
    assert!(varnames.contains(&"r"), "varnames={varnames:?}");
    // A passing test reports no error.
    assert_eq!(io_event_kinds(&doc), Vec::<String>::new());
}

#[test]
fn test_trace_test_name_records_a_failing_test_up_to_its_failure() {
    let name = "test_trace_test_name_records_a_failing_test_up_to_its_failure";
    let Some(result) = trace_test_and_dump(name, "test_functions", "test_fails") else {
        return;
    };
    let doc = expect_test_trace(result, "test_fails");
    let calls = observed_call_sequence(&doc);
    assert_eq!(calls[1], "test_fails", "calls={calls:?}");
    // The failed `assert` is recorded as the run's one Error event, exactly as
    // a failing `main` is.
    assert_eq!(io_event_kinds(&doc), vec!["Error".to_string()]);
}

#[test]
fn test_trace_test_name_records_a_should_fail_test_as_the_failure_it_is() {
    let name = "test_trace_test_name_records_a_should_fail_test_as_the_failure_it_is";
    let Some(result) = trace_test_and_dump(name, "test_functions", "test_should_fail") else {
        return;
    };
    let doc = expect_test_trace(result, "test_should_fail");
    assert_eq!(observed_call_sequence(&doc)[1], "test_should_fail");
    // The execution failed — which is what makes it a passing should_fail test
    // under `nargo test`, and what the trace records.
    assert_eq!(io_event_kinds(&doc), vec!["Error".to_string()]);
}

#[test]
fn test_trace_test_name_accepts_the_qualified_and_the_bare_name() {
    let name = "test_trace_test_name_accepts_the_qualified_and_the_bare_name";
    for test in ["tests::test_nested", "test_nested"] {
        let Some(result) = trace_test_and_dump(name, "test_functions", test) else {
            return;
        };
        let doc = expect_test_trace(result, test);
        assert_eq!(observed_call_sequence(&doc)[1], "test_nested", "via {test}");
        assert_eq!(io_event_kinds(&doc), Vec::<String>::new(), "via {test}");
    }
}

#[test]
fn test_trace_test_name_refuses_a_name_that_matches_no_test() {
    let name = "test_trace_test_name_refuses_a_name_that_matches_no_test";
    let Some((output, doc)) = trace_test_and_dump(name, "test_functions", "no_such_test") else {
        return;
    };
    assert!(!output.status.success(), "an unknown test must not succeed");
    assert!(doc.is_none(), "an unknown test must not write a trace");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("`no_such_test` does not match with any test function"),
        "stderr={stderr}"
    );
}
