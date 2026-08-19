//! Write a `.ct` container for every `test_programs/trace` fixture.
//!
//! The native twin of what the demo page does per click, used to diff the
//! wasm-writable container against the one `nargo trace` produces.
//!
//! ```text
//! cargo run -p noir_tracer_wasm --release --example dump_containers -- /tmp/out
//! ```

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use noir_tracer_wasm::{TraceRequest, trace_source_to_container};

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

fn main() {
    let out_dir = PathBuf::from(std::env::args().nth(1).expect("usage: dump_containers <out-dir>"));
    std::fs::create_dir_all(&out_dir).expect("out dir");

    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .expect("workspace root")
        .to_path_buf();

    let mut fixtures: Vec<String> = std::fs::read_dir(root.join("test_programs/trace"))
        .expect("test_programs/trace")
        .flatten()
        .map(|e| e.file_name().to_string_lossy().into_owned())
        .collect();
    fixtures.sort();

    for fixture in fixtures {
        let dir = root.join("test_programs/trace").join(&fixture);
        let inputs_path = dir.join("Prover.toml");
        if !inputs_path.exists() {
            println!("{fixture}: SKIP (no Prover.toml)");
            continue;
        }
        let mut files = BTreeMap::new();
        collect_sources(&dir.join("src"), &dir, &mut files);
        let request = TraceRequest {
            files,
            entry_point: "src/main.nr".to_string(),
            inputs: std::fs::read_to_string(&inputs_path).expect("Prover.toml"),
            inputs_are_json: false,
            package: fixture.clone(),
            recording_id: Some("01949fcc-7d92-7e9c-8000-00000000ce11".to_string()),
        };
        match trace_source_to_container(&request) {
            Ok((bytes, summary)) => {
                let path = out_dir.join(format!("{fixture}.ct"));
                std::fs::write(&path, &bytes).expect("write container");
                // The same recording as the event stream the page renders,
                // for diffing against what a reader decodes out of the `.ct`.
                std::fs::write(
                    out_dir.join(format!("{fixture}.trace.json")),
                    serde_json::to_vec(&summary).expect("serialize the trace"),
                )
                .expect("write the trace json");
                println!(
                    "{fixture}: {} bytes, {} events, {} paths",
                    bytes.len(),
                    summary.trace.events.len(),
                    summary.trace.paths.len()
                );
            }
            Err(e) => println!("{fixture}: FAILED {e}"),
        }
    }
}
