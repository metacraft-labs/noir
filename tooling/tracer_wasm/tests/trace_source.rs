//! End-to-end test of the **source** entry point: Noir text in, trace out, with
//! no compiled artifact and no filesystem in between.
//!
//! `noir_tracer_wasm::trace_source` is exactly the code the wasm module runs
//! when the demo page hands it the contents of a textarea. Running it natively
//! is how we assert on the result without standing up a browser; that the same
//! source builds for `wasm32-unknown-unknown`, and that a real browser gets the
//! same numbers, is checked by `tooling/tracer_wasm/web/check_web.mjs`.
//!
//! **No mocks.** The sources are the real `test_programs/trace` fixtures, the
//! compile is the real `noirc_driver` debugging compile path, the trace comes
//! from the real debugger driving the real ACVM, and the baseline is the real
//! `nargo` binary compiling the same fixture through the same path. The whole
//! point is that the two agree, so substituting a double on either side would
//! destroy the test's meaning.
//!
//! Tests SKIP loudly (never silently) when `nargo` has not been built.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use codetracer_trace_types::TraceLowLevelEvent;
use noir_tracer_wasm::{MemoryTrace, TraceRequest, trace_artifact, trace_source};

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
    let found = ["target/debug/nargo", "target/release/nargo"]
        .iter()
        .map(|s| workspace_root().join(s))
        .find(|p| p.exists());
    if found.is_none() {
        eprintln!(
            "SKIP: {test_name} requires the workspace `nargo` binary; build it with \
             `cargo build -p nargo_cli --bin nargo` or set CODETRACER_NARGO_BIN."
        );
    }
    found
}

/// Every `.nr` under the fixture's `src/`, keyed relative to the fixture root.
///
/// The entry point must sit in a directory: the debug instrumenter decides
/// which files belong to the package by testing the entry point's parent
/// against their ancestors, and every path has the empty path as an ancestor.
fn collect_sources(dir: &Path, base: &Path, out: &mut BTreeMap<String, String>) {
    for entry in std::fs::read_dir(dir).expect("fixture src dir").flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_sources(&path, base, out);
        } else if path.extension().is_some_and(|e| e == "nr") {
            let key = path.strip_prefix(base).expect("under base").to_string_lossy().into_owned();
            out.insert(key, std::fs::read_to_string(&path).expect("fixture source"));
        }
    }
}

fn request_for(fixture: &str) -> Option<TraceRequest> {
    let dir = workspace_root().join("test_programs/trace").join(fixture);
    let inputs_path = dir.join("Prover.toml");
    if !inputs_path.exists() {
        return None;
    }

    let mut files = BTreeMap::new();
    collect_sources(&dir.join("src"), &dir, &mut files);

    Some(TraceRequest {
        files,
        entry_point: "src/main.nr".to_string(),
        inputs: std::fs::read_to_string(&inputs_path).expect("Prover.toml"),
        inputs_are_json: false,
        package: fixture.to_string(),
    })
}

fn count<F: Fn(&TraceLowLevelEvent) -> bool>(t: &MemoryTrace, f: F) -> usize {
    t.events.iter().filter(|e| f(e)).count()
}

fn steps(t: &MemoryTrace) -> usize {
    count(t, |e| matches!(e, TraceLowLevelEvent::Step(_)))
}

/// Non-toplevel calls, matching `ct-print`'s `counts.calls`.
fn calls(t: &MemoryTrace) -> usize {
    count(t, |e| matches!(e, TraceLowLevelEvent::Call(_))) - 1
}

fn io_events(t: &MemoryTrace) -> usize {
    count(t, |e| matches!(e, TraceLowLevelEvent::Event(_)))
}

/// The counts `ct-print --full` reports for the `.ct` container native
/// `nargo trace` produces from the same fixture.
///
/// Regenerate with `just compare-web-traces`, which measures both columns.
const NATIVE_COUNTS: &[(&str, usize, usize, usize, usize)] = &[
    // fixture,             steps, calls, paths, io_events
    ("a_1_mul", 14, 1, 1, 0),
    ("a_2_function_calls", 20, 5, 1, 0),
    ("a_3_two_files", 15, 3, 3, 0),
    ("a_4_signed_ints", 22, 1, 2, 3),
    ("a_7_looper", 92, 2, 2, 11),
    ("assert", 12, 1, 1, 1),
    ("println", 19, 1, 2, 5),
    ("slice", 32, 2, 2, 5),
    ("zk_dungeon", 2511, 25, 2, 0),
];

#[test]
fn tracing_from_source_matches_the_native_container() {
    for &(fixture, want_steps, want_calls, want_paths, want_io) in NATIVE_COUNTS {
        let request = request_for(fixture).unwrap_or_else(|| panic!("{fixture} has no Prover.toml"));
        let t = trace_source(&request).unwrap_or_else(|e| panic!("tracing {fixture} from source: {e}"));

        assert_eq!(steps(&t), want_steps, "{fixture}: steps");
        assert_eq!(calls(&t), want_calls, "{fixture}: calls");
        assert_eq!(t.paths.len(), want_paths, "{fixture}: paths ({:?})", t.paths);
        assert_eq!(io_events(&t), want_io, "{fixture}: io_events");
    }
}

/// Compiling in-process must produce the same trace as compiling with `nargo`
/// and feeding the artifact in.
///
/// This is the invariant that matters and it needs no hard-coded numbers: if
/// the in-wasm compile diverged from the one `nargo trace` performs -- a
/// different instrumenter setting, a missed `force_brillig`, a stdlib that
/// resolved differently -- the two traces would differ here.
#[test]
fn source_and_artifact_paths_agree_on_every_fixture() {
    let test_name = "source_and_artifact_paths_agree_on_every_fixture";
    let Some(nargo) = locate_nargo(test_name) else { return };
    let root = workspace_root();

    let mut fixtures: Vec<String> = std::fs::read_dir(root.join("test_programs/trace"))
        .expect("test_programs/trace")
        .flatten()
        .map(|e| e.file_name().to_string_lossy().into_owned())
        .collect();
    fixtures.sort();
    assert!(fixtures.len() >= 20, "expected the full fixture set, found {}", fixtures.len());

    let mut compared = 0;
    for fixture in fixtures {
        let Some(request) = request_for(&fixture) else { continue };
        let dir = root.join("test_programs/trace").join(&fixture);

        let tmp = std::env::temp_dir().join(format!("noir_trace_source_agree_{fixture}"));
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
        let from_artifact = trace_artifact(&artifact, &request.inputs, false)
            .unwrap_or_else(|e| panic!("tracing {fixture} from an artifact: {e}"));
        let from_source = trace_source(&request)
            .unwrap_or_else(|e| panic!("tracing {fixture} from source: {e}"));

        assert_eq!(steps(&from_source), steps(&from_artifact), "{fixture}: steps");
        assert_eq!(calls(&from_source), calls(&from_artifact), "{fixture}: calls");
        assert_eq!(
            from_source.paths.len(),
            from_artifact.paths.len(),
            "{fixture}: paths ({:?} vs {:?})",
            from_source.paths,
            from_artifact.paths
        );
        assert_eq!(io_events(&from_source), io_events(&from_artifact), "{fixture}: io_events");
        assert_eq!(
            from_source.events.len(),
            from_artifact.events.len(),
            "{fixture}: total low-level events"
        );
        compared += 1;
    }

    assert!(compared >= 19, "expected to compare ~20 fixtures, compared {compared}");
}

#[test]
fn a_compile_error_is_reported_rather_than_panicking() {
    let mut files = BTreeMap::new();
    files.insert("src/main.nr".to_string(), "fn main(x: u32) { let y: Field = x; }".to_string());

    let request = TraceRequest {
        files,
        entry_point: "src/main.nr".to_string(),
        inputs: "x = \"1\"\n".to_string(),
        inputs_are_json: false,
        package: "broken".to_string(),
    };

    let error = trace_source(&request).expect_err("a type error should not compile");
    let message = error.to_string();
    assert!(
        message.contains("failed to compile the program"),
        "expected a rendered compile error, got: {message}"
    );
    // The diagnostic must carry the location, since a browser has no other way
    // to find out where the error is.
    assert!(message.contains("src/main.nr"), "expected the file in the diagnostic: {message}");
}

#[test]
fn an_entry_point_outside_a_directory_is_refused() {
    let mut files = BTreeMap::new();
    files.insert("main.nr".to_string(), "fn main() {}".to_string());

    let request = TraceRequest {
        files,
        entry_point: "main.nr".to_string(),
        inputs: String::new(),
        inputs_are_json: false,
        package: "rootless".to_string(),
    };

    // Silently instrumenting the standard library would be far worse than a
    // refusal: it compiles, and merely produces a wrong and enormous trace.
    let error = trace_source(&request).expect_err("a root-level entry point must be refused");
    assert!(error.to_string().contains("must live in a directory"), "{error}");
}
