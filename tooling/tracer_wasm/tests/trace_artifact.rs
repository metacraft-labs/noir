//! End-to-end test of the platform-agnostic tracing entry point, cross-checked
//! against the native `.ct` container.
//!
//! `noir_tracer_wasm::trace_artifact` is exactly the code the wasm module runs:
//! a serialized `ProgramArtifact` plus a `Prover.toml` string go in, an
//! in-memory event stream comes out, and nothing inside it touches the
//! filesystem, the environment or a process. Running it natively is how we
//! assert on the result without standing up a JS host; that the same source
//! builds for `wasm32-unknown-unknown` is verified by
//! `cd tooling/tracer_wasm && cargo build --release`.
//!
//! **No mocks.** The artifact comes from the real `nargo` binary compiling a
//! real `test_programs/trace` fixture through the real debugging compile path,
//! the trace comes from the real debugger driving the real ACVM, and the
//! expected numbers come from running the real Nim CTFS writer over the same
//! fixture and decoding the container with the real `ct-print`. The point of
//! the test is precisely that the in-memory path and the container path agree,
//! so substituting a double on either side would destroy its meaning.
//!
//! Tests SKIP loudly (never silently) when `nargo` has not been built, matching
//! the convention in `tooling/tracer/tests/test_tracer.rs`.

use std::path::PathBuf;
use std::process::Command;

use codetracer_trace_types::{EventLogKind, TraceLowLevelEvent};
use noir_tracer_wasm::{MemoryTrace, trace_artifact};

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .expect("noir workspace root above tooling/tracer_wasm")
        .to_path_buf()
}

fn locate_nargo(test_name: &str) -> Option<PathBuf> {
    if let Ok(p) = std::env::var("CODETRACER_NARGO_BIN") {
        let p = PathBuf::from(p);
        if p.exists() {
            return Some(p);
        }
    }
    let root = workspace_root();
    let found = ["target/debug/nargo", "target/release/nargo"]
        .iter()
        .map(|s| root.join(s))
        .find(|p| p.exists());
    if found.is_none() {
        eprintln!(
            "SKIP: {test_name} requires the workspace `nargo` binary; build it with \
             `cargo build -p nargo_cli --bin nargo` or set CODETRACER_NARGO_BIN."
        );
    }
    found
}

/// Produce the debug-instrumented artifact for `fixture`, plus its inputs.
///
/// `nargo compile` is deliberately NOT used: the source-level debug
/// instrumenter -- which injects the `__debug_var_assign` / `__debug_fn_enter`
/// oracle calls the tracer reads frames and variables from -- only runs on the
/// debugging compile path. `nargo trace --emit-debug-artifact` runs that path
/// and hands out exactly the artifact a wasm host would be given.
fn debug_artifact_for(test_name: &str, fixture: &str) -> Option<(String, String)> {
    let nargo = locate_nargo(test_name)?;
    let root = workspace_root();
    let dir = root.join("test_programs/trace").join(fixture);

    let inputs_path = dir.join("Prover.toml");
    if !inputs_path.exists() {
        eprintln!("SKIP: {test_name}: fixture {fixture} has no Prover.toml");
        return None;
    }

    // Per-*test* scratch dir, not per-fixture: three tests here compile
    // `a_1_mul`, cargo runs them in parallel by default, and they were all
    // writing `artifact.json` at the same shared path. The reader then saw one
    // `nargo` process's JSON with another's tail spliced on
    // ("trailing characters at line 1 column ..."), which looks like a tracer
    // defect and is not one.
    let tmp = std::env::temp_dir().join(format!("noir_tracer_wasm_{test_name}_{fixture}"));
    std::fs::create_dir_all(&tmp).expect("temp dir");
    let artifact_path = tmp.join("artifact.json");
    let out = Command::new(&nargo)
        .arg("--program-dir")
        .arg(&dir)
        .arg("trace")
        .arg("--out-dir")
        .arg(&tmp)
        .arg("--emit-debug-artifact")
        .arg(&artifact_path)
        .output()
        .expect("nargo trace");
    assert!(
        out.status.success(),
        "nargo trace failed for {fixture}: {}",
        String::from_utf8_lossy(&out.stderr)
    );

    let artifact = std::fs::read_to_string(&artifact_path).expect("debug artifact");
    let inputs = std::fs::read_to_string(&inputs_path).expect("Prover.toml");
    Some((artifact, inputs))
}

fn count<F: Fn(&TraceLowLevelEvent) -> bool>(t: &MemoryTrace, f: F) -> usize {
    t.events.iter().filter(|e| f(e)).count()
}

fn steps(t: &MemoryTrace) -> usize {
    count(t, |e| matches!(e, TraceLowLevelEvent::Step(_)))
}

/// Non-toplevel calls. `ct-print`'s `counts.calls` reports the call *tree*
/// below the root, so the `<toplevel>` call is excluded on both sides.
fn calls(t: &MemoryTrace) -> usize {
    count(t, |e| matches!(e, TraceLowLevelEvent::Call(_))) - 1
}

fn io_events(t: &MemoryTrace) -> usize {
    count(t, |e| matches!(e, TraceLowLevelEvent::Event(_)))
}

/// The counts `ct-print --full` reports for the `.ct` container the native
/// `nargo trace` produces from the same fixture.
///
/// Regenerate with:
/// ```text
/// nargo --program-dir test_programs/trace/<f> trace --out-dir /tmp/x
/// ct-print --full --strip-paths /tmp/x/<f>.ct | jq .counts
/// ```
const NATIVE_COUNTS: &[(&str, usize, usize, usize, usize)] = &[
    // fixture,            steps, calls, paths, io_events
    ("a_1_mul", 14, 1, 1, 0),
    ("a_2_function_calls", 20, 5, 1, 0),
    ("a_3_two_files", 15, 3, 3, 0),
    ("assert", 12, 1, 1, 1),
    ("a_7_looper", 92, 2, 2, 11),
];

#[test]
fn in_memory_trace_matches_the_native_container() {
    for &(fixture, want_steps, want_calls, want_paths, want_io) in NATIVE_COUNTS {
        let Some((artifact, inputs)) =
            debug_artifact_for("in_memory_trace_matches_the_native_container", fixture)
        else {
            return;
        };
        let t = trace_artifact(&artifact, &inputs, false)
            .unwrap_or_else(|e| panic!("tracing {fixture}: {e}"));

        assert_eq!(steps(&t), want_steps, "{fixture}: steps");
        assert_eq!(calls(&t), want_calls, "{fixture}: calls");
        assert_eq!(t.paths.len(), want_paths, "{fixture}: paths ({:?})", t.paths);
        assert_eq!(io_events(&t), want_io, "{fixture}: io_events");
    }
}

#[test]
fn records_capabilities_paths_and_line_lengths() {
    let Some((artifact, inputs)) =
        debug_artifact_for("records_capabilities_paths_and_line_lengths", "a_1_mul")
    else {
        return;
    };
    let t = trace_artifact(&artifact, &inputs, false).expect("tracing a_1_mul");

    // `trace_circuit` latches all three column capabilities before any step.
    assert!(t.capabilities.column_aware_steps);
    assert!(t.capabilities.column_breakpoints);
    assert!(t.capabilities.column_motions);

    assert!(t.paths[0].ends_with("src/main.nr"), "paths: {:?}", t.paths);
    // The per-line byte-length table the CTFS column decoder needs was captured
    // from `DebugArtifact.file_map`, in memory, with no file read.
    assert!(!t.line_lengths[0].is_empty());

    // No workdir was supplied, so none was recorded -- the recorder no longer
    // invents one from `std::env::current_dir()`.
    assert_eq!(t.workdir, None);
}

#[test]
fn call_tree_names_are_recorded_in_call_order() {
    let Some((artifact, inputs)) =
        debug_artifact_for("call_tree_names_are_recorded_in_call_order", "a_2_function_calls")
    else {
        return;
    };
    let t = trace_artifact(&artifact, &inputs, false).expect("tracing a_2_function_calls");

    let functions: Vec<&str> = t
        .events
        .iter()
        .filter_map(|e| match e {
            TraceLowLevelEvent::Function(f) => Some(f.name.as_str()),
            _ => None,
        })
        .collect();
    assert_eq!(functions, vec!["<toplevel>", "main", "foo", "bar"]);
}

#[test]
fn assertion_failure_becomes_an_error_event() {
    let Some((artifact, inputs)) =
        debug_artifact_for("assertion_failure_becomes_an_error_event", "assert")
    else {
        return;
    };
    let t = trace_artifact(&artifact, &inputs, false).expect("tracing assert");

    let errors: Vec<&str> = t
        .events
        .iter()
        .filter_map(|e| match e {
            TraceLowLevelEvent::Event(ev) if ev.kind == EventLogKind::Error => {
                Some(ev.content.as_str())
            }
            _ => None,
        })
        .collect();
    assert_eq!(errors.len(), 1, "expected exactly one error event, got {errors:?}");
}

#[test]
fn every_fixture_traces_without_panicking() {
    let root = workspace_root();
    if locate_nargo("every_fixture_traces_without_panicking").is_none() {
        return;
    }
    let mut names: Vec<String> = std::fs::read_dir(root.join("test_programs/trace"))
        .expect("test_programs/trace")
        .filter_map(|e| e.ok().map(|e| e.file_name().to_string_lossy().into_owned()))
        .collect();
    names.sort();
    assert!(names.len() >= 20, "expected the full fixture set, found {}", names.len());

    for name in names {
        let Some((artifact, inputs)) =
            debug_artifact_for("every_fixture_traces_without_panicking", &name)
        else {
            continue;
        };
        let t = trace_artifact(&artifact, &inputs, false)
            .unwrap_or_else(|e| panic!("tracing {name}: {e}"));
        assert!(steps(&t) > 0, "{name}: produced no steps");
        assert!(!t.paths.is_empty(), "{name}: registered no paths");
    }
}
