//! The `.ct` half of the wasm demo: Noir source in, a CTFS container out.
//!
//! `noir_tracer_wasm::trace_source_to_container` is exactly the code the wasm
//! module runs for `ct_trace_source_container`. Running it natively is how the
//! container is asserted on without standing up a browser; that the same code
//! builds for `wasm32-unknown-unknown` and that a real browser gets a byte-
//! identical container is checked by `tooling/tracer_wasm/web/check_web.mjs`.
//!
//! **No mocks.** Real fixture sources, the real `noirc_driver` debugging
//! compile, the real debugger over the real ACVM, the real
//! `codetracer_trace_writer::CtfsTraceWriter`, and -- where it is available --
//! the real `ct-print` binary decoding the result. Substituting a double
//! anywhere would remove the only thing these tests assert: that two
//! independent implementations agree on the bytes.
//!
//! `ct-print` must come from `codetracer-trace-format-nim` on branch
//! `wasm/nim-to-wasm`. The stock reader cannot decode **any** container this
//! writer produces, native or wasm: it does not skip the writer's 8-byte
//! `HEADERV1` prefix on `events.log`, and it treats a zstd frame with no
//! pledged content size as a size. Both are fixed on that branch. Tests that
//! need it SKIP loudly when it is missing.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use codetracer_trace_types::TraceLowLevelEvent;
use noir_tracer_wasm::{MemoryTrace, TraceRequest, trace_source, trace_source_to_container};

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .expect("noir workspace root above tooling/tracer_wasm")
        .to_path_buf()
}

/// The `ct-print` that can read this writer's output -- see the module docs.
fn locate_ct_print(test_name: &str) -> Option<PathBuf> {
    let candidates = [
        std::env::var("CODETRACER_CT_PRINT").ok().map(PathBuf::from),
        workspace_root().parent().map(|p| p.join("ctfnim-wt-wasm/ct-print")),
    ];
    let found = candidates.into_iter().flatten().find(|p| p.exists());
    if found.is_none() {
        eprintln!(
            "SKIP: {test_name} needs the `ct-print` built from codetracer-trace-format-nim \
             branch `wasm/nim-to-wasm` (`nimble buildCtPrint`). Set CODETRACER_CT_PRINT."
        );
    }
    found
}

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
        // Pinned so the container is reproducible: a wasm sandbox has no clock
        // and no CSPRNG, so the id is always the host's to supply.
        recording_id: Some("01949fcc-7d92-7e9c-8000-00000000ce11".to_string()),
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

const CTFS_MAGIC: [u8; 5] = [0xC0, 0xDE, 0x72, 0xAC, 0xE2];

/// The whole point: source text goes in, a real CTFS container comes out.
#[test]
fn a_container_is_produced_from_source() {
    let request = request_for("a_1_mul").expect("a_1_mul has a Prover.toml");
    let (bytes, summary) = trace_source_to_container(&request).expect("tracing a_1_mul");

    assert_eq!(&bytes[..5], &CTFS_MAGIC, "the container is missing the CTFS magic");
    assert_eq!(summary.container.bytes, bytes.len());
    // Not a claim of parity: this writer has no column encoder, and the Noir
    // recorder always asks for one. See `ctfs_sink`.
    assert!(!summary.container.column_aware);
    assert!(summary.container.dropped_column_awareness);
}

/// The container and the event stream the page renders come from ONE pass, so
/// they must describe the same recording. This is what makes the counts the
/// page shows trustworthy as a description of the file it hands you.
#[test]
fn the_container_describes_the_same_trace_as_the_event_stream() {
    for fixture in ["a_1_mul", "a_2_function_calls", "a_3_two_files", "println", "slice"] {
        let request = request_for(fixture).unwrap_or_else(|| panic!("{fixture} has no Prover.toml"));
        let alone = trace_source(&request).unwrap_or_else(|e| panic!("{fixture}: {e}"));
        let (_, together) =
            trace_source_to_container(&request).unwrap_or_else(|e| panic!("{fixture}: {e}"));

        assert_eq!(steps(&together.trace), steps(&alone), "{fixture}: steps");
        assert_eq!(calls(&together.trace), calls(&alone), "{fixture}: calls");
        assert_eq!(together.trace.paths, alone.paths, "{fixture}: paths");
        assert_eq!(io_events(&together.trace), io_events(&alone), "{fixture}: io_events");
        assert_eq!(
            together.trace.events.len(),
            alone.events.len(),
            "{fixture}: total low-level events"
        );
    }
}

/// Read the container back with a **different implementation** -- the Nim
/// `ct-print` -- and require it to report the counts the Rust side recorded.
///
/// This is the test that turns "the bytes start with the right magic" into
/// "the bytes are a trace someone else can read".
#[test]
fn ct_print_reads_the_container_and_agrees_on_the_counts() {
    let test_name = "ct_print_reads_the_container_and_agrees_on_the_counts";
    let Some(ct_print) = locate_ct_print(test_name) else { return };

    let dir = std::env::temp_dir().join("noir_tracer_wasm_ctfs_container");
    std::fs::create_dir_all(&dir).expect("temp dir");

    for fixture in ["a_1_mul", "a_2_function_calls", "a_3_two_files", "println", "slice", "zk_dungeon"] {
        let request = request_for(fixture).unwrap_or_else(|| panic!("{fixture} has no Prover.toml"));
        let (bytes, summary) =
            trace_source_to_container(&request).unwrap_or_else(|e| panic!("{fixture}: {e}"));

        let path = dir.join(format!("{fixture}.ct"));
        std::fs::write(&path, &bytes).expect("write the container");

        let out = Command::new(&ct_print)
            .arg("--full")
            .arg("--strip-paths")
            .arg(&path)
            .output()
            .expect("run ct-print");
        assert!(
            out.status.success(),
            "ct-print --full failed on {fixture}: {}\n{}",
            String::from_utf8_lossy(&out.stderr),
            String::from_utf8_lossy(&out.stdout),
        );

        let decoded: serde_json::Value =
            serde_json::from_slice(&out.stdout).expect("ct-print --full emits JSON");
        let events = decoded["events"].as_array().expect("ct-print --full lists events");
        let of_type = |t: &str| events.iter().filter(|e| e["type"] == t).count();

        assert_eq!(of_type("Step"), steps(&summary.trace), "{fixture}: ct-print disagrees on steps");
        // ct-print counts the `<toplevel>` call; `calls()` does not.
        assert_eq!(
            of_type("Call") - 1,
            calls(&summary.trace),
            "{fixture}: ct-print disagrees on calls"
        );
        assert_eq!(
            of_type("Event"),
            io_events(&summary.trace),
            "{fixture}: ct-print disagrees on I/O events"
        );
        assert_eq!(
            decoded["paths"].as_array().expect("paths").len(),
            summary.trace.paths.len(),
            "{fixture}: ct-print disagrees on paths"
        );
        assert_eq!(
            events.len(),
            summary.trace.events.len(),
            "{fixture}: ct-print disagrees on the total event count"
        );
    }
}
