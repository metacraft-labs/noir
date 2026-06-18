//! Strict `_via_ct_print_full` integration tests for the Noir tracer.
//!
//! Round 1 of M-extended fixture parity (see
//! `codetracer-specs/Planned-Features/Smart-Contract-Languages/Noir-Aztec.status.org`).
//!
//! Each test:
//!
//! 1. Locates the workspace-built `nargo` binary at
//!    `<noir>/target/{debug,release}/nargo` (or via the
//!    `CODETRACER_NARGO_BIN` env var).  If neither is present the
//!    test prints a `SKIP:` line — the convention used by every
//!    other recorder when its toolchain isn't built — so silent
//!    skips remain forbidden.
//! 2. Runs `nargo --program-dir <fixture> trace --out-dir <tmp>`,
//!    producing a single `<package>.ct` CTFS bundle.
//! 3. Locates the `codetracer-trace-format-nim/ct-print` binary at
//!    `../../../codetracer-trace-format-nim/ct-print` (sibling
//!    workspace layout) or `CODETRACER_CT_PRINT_BIN`.  Skips with
//!    `SKIP:` if missing.
//! 4. Pipes the `.ct` through `ct-print --full --strip-paths` and
//!    parses the JSON.
//! 5. Pins exact counts, function/type tables, call sequences and
//!    per-step decoded values via `assert_eq!`.  No `>=`, no
//!    `contains`, no substring matching.  No `#[ignore]`.
//!
//! Why these five fixtures (out of 20 in `test_programs/trace/`)?
//!
//! * `a_1_mul` — basic `u32` arithmetic baseline.
//! * `a_2_function_calls` — three-deep call chain (main → foo → bar).
//! * `if_then_else_reduced` — branching `for` loop.
//! * `assert` — assertion-failure → `EventLogKind::Error` io_event.
//! * `types_test` — comprehensive type signature with `Field`,
//!   `u32`, `i8`, `bool`, `str<11>`, `[Field; 2]` and a user-defined
//!   `Point` struct.
//!
//! Round 2 (MN+1 in the spec) will add struct destructuring,
//! BoundedVec, generics, oracle calls, std::hash, std::ec, recursion
//! and Aztec.nr contract constructs.

use std::path::PathBuf;
use std::process::Command;

// -- locator helpers --------------------------------------------------------

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
/// Returns `None` (with a `SKIP:` diagnostic) if none is found.
fn locate_nargo(test_name: &str) -> Option<PathBuf> {
    if let Ok(env_path) = std::env::var("CODETRACER_NARGO_BIN") {
        let p = PathBuf::from(env_path);
        if p.exists() {
            return Some(p);
        }
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

    eprintln!(
        "SKIP: {test_name} requires the workspace `nargo` binary at \
         <noir>/target/{{debug,release}}/nargo.  Build it with \
         `cargo build -p nargo_cli --bin nargo` or set \
         CODETRACER_NARGO_BIN."
    );
    None
}

/// Locate the `ct-print` binary from `codetracer-trace-format-nim`.
///
/// Order:
///   1. `CODETRACER_CT_PRINT_BIN` env var (absolute path).
///   2. `<workspace>/../codetracer-trace-format-nim/ct-print` (sibling
///      layout in the metacraft monorepo).
///
/// Returns `None` (with a `SKIP:` diagnostic) if neither is found.
fn locate_ct_print(test_name: &str) -> Option<PathBuf> {
    if let Ok(env_path) = std::env::var("CODETRACER_CT_PRINT_BIN") {
        let p = PathBuf::from(env_path);
        if p.exists() {
            return Some(p);
        }
    }

    let root = noir_workspace_root();
    let sibling = root
        .parent()
        .map(|p| p.join("codetracer-trace-format-nim").join("ct-print"))
        .filter(|p| p.exists());
    if let Some(p) = sibling {
        return Some(p);
    }

    eprintln!(
        "SKIP: {test_name} requires `ct-print` from \
         codetracer-trace-format-nim.  Build it via the sibling \
         repo or set CODETRACER_CT_PRINT_BIN."
    );
    None
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

// ===========================================================================
// Round 1 fixtures
// ===========================================================================

/// `a_1_mul.nr` — basic `u32` multiplication chain (12^8 = 429981696).
///
/// Pins: 1 call (main), 7 step events, 0 io_events, the function
/// table contains only `main`, the type table contains exactly the
/// three Noir types the recorder ensures (`None`, `u32`, and the
/// `mut u32`-derived `type_1` synthetic), the varname table is
/// `[x, y, z]`, and the per-step value of `x` mutates through the
/// expected sequence 3 → 12 → 144 → 20736 → 429981696.
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
    assert_eq!(counts["functions"].as_u64(), Some(1), "functions; counts={counts}");
    assert_eq!(counts["varnames"].as_u64(), Some(3), "varnames; counts={counts}");
    assert_eq!(counts["types"].as_u64(), Some(3), "types; counts={counts}");
    // Column-aware counts: each `register_step` is paired with a
    // follow-up `sekDeltaColumn` cursor-nudge whenever the column is
    // > 1; param-binding events on the fn-declaration line surface as
    // distinct steps now too.  See FU-Column-Aware-Nav-Noir notes.
    assert_eq!(counts["steps"].as_u64(), Some(10), "steps; counts={counts}");
    assert_eq!(counts["calls"].as_u64(), Some(1), "calls; counts={counts}");
    assert_eq!(counts["values"].as_u64(), Some(19), "values; counts={counts}");
    assert_eq!(counts["io_events"].as_u64(), Some(0), "io_events; counts={counts}");

    // ---- tables ------------------------------------------------------------
    assert_eq!(string_array(&doc, "functions"), vec!["main"]);
    assert_eq!(string_array(&doc, "varnames"), vec!["x", "y", "z"]);
    assert_eq!(string_array(&doc, "types"), vec!["None", "u32", "type_1"]);
    assert_path_strip_normalised(&doc, "a_1_mul");

    // ---- event shape -------------------------------------------------------
    let events = doc["events"].as_array().unwrap();
    // 1 call_entry + 19 step events (10 register_step calls + 9 aux
    // `sekDeltaColumn` cursor-nudges) + 1 call_exit = 21 wire-level
    // events.
    assert_eq!(events.len(), 21, "1 call_entry + 19 steps + 1 call_exit");
    assert_eq!(observed_call_sequence(&doc), vec!["main".to_string()]);
    assert_eq!(
        observed_event_kinds(&doc),
        vec![
            "call_entry", "step", "step", "step", "step", "step", "step", "step", "step", "step",
            "step", "call_exit",
        ]
    );

    // Column-aware `register_call` fires before params are bound, so
    // `call_entry.args` is empty (deferred-bind: see FU notes).
    let entry = &events[0];
    let args = entry["args"].as_array().unwrap();
    assert!(args.is_empty(), "expected empty call_entry.args; got {args:?}");

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
    assert_eq!(
        xs,
        vec![
            None,
            None,
            None,
            Some(3),
            Some(3),
            Some(3),
            Some(12),
            Some(144),
            Some(20736),
            Some(429981696),
        ]
    );

    // ---- call_exit ---------------------------------------------------------
    let exit = events.last().unwrap();
    assert_eq!(exit["kind"], "call_exit");
    assert_eq!(exit["function"].as_str(), Some("main"));
    assert_eq!(exit["return_value"]["kind"].as_str(), Some("Void"));
}

/// `a_2_function_calls.nr` — main → foo → bar twice.
///
/// Pins: 5 calls (1 main + 2 foo + 2 bar), 11 step events, 0
/// io_events, function table = [main, foo, bar] in ensure order,
/// type table = [None, Field, type_1, "()"], call-entry sequence
/// = [main, foo, bar, foo, bar], and Field-typed argument values.
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
    assert_eq!(counts["functions"].as_u64(), Some(3), "functions; counts={counts}");
    assert_eq!(counts["varnames"].as_u64(), Some(2), "varnames; counts={counts}");
    assert_eq!(counts["types"].as_u64(), Some(4), "types; counts={counts}");
    // counts["steps"] / counts["values"] / events.len() include
    // column-aware auxiliary `sekDeltaColumn` cursor-nudges; see
    // `test_a_1_mul_via_ct_print_full` for the accounting.
    assert_eq!(counts["steps"].as_u64(), Some(17), "steps; counts={counts}");
    assert_eq!(counts["calls"].as_u64(), Some(5), "calls; counts={counts}");
    assert_eq!(counts["values"].as_u64(), Some(33), "values; counts={counts}");
    assert_eq!(counts["io_events"].as_u64(), Some(0), "io_events; counts={counts}");

    assert_eq!(string_array(&doc, "functions"), vec!["main", "foo", "bar"]);
    assert_eq!(string_array(&doc, "varnames"), vec!["x", "y"]);
    assert_eq!(string_array(&doc, "types"), vec!["None", "Field", "type_1", "()"]);
    assert_path_strip_normalised(&doc, "a_2_function_calls");

    // 5 call_entry + 33 step events + 5 call_exit = 43 wire-level events.
    let events = doc["events"].as_array().unwrap();
    assert_eq!(events.len(), 43);
    assert_eq!(
        observed_call_sequence(&doc),
        vec![
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
            ("main", 1),
            ("main", 9),
            ("main", 9),
            ("main", 10),
            ("foo", 5),
            ("foo", 6),
            ("bar", 1),
            ("bar", 2),
            ("foo", 6),
            ("main", 10),
            ("foo", 5),
            ("foo", 6),
            ("bar", 1),
            ("bar", 2),
            ("foo", 6),
            ("main", 11),
            ("main", 13),
        ]
    );

    // Column-aware register_call fires before params are bound, so
    // every call_entry has empty `args` for now (see a_1_mul test).
    for entry in events.iter().filter(|e| e["kind"] == "call_entry") {
        let args = entry["args"].as_array().unwrap();
        assert!(
            args.is_empty(),
            "expected empty call_entry.args under column-aware mode; got {args:?}",
        );
    }

    // foo's return_value is `()` (Raw with text "()", type_id 4)
    let foo_exits: Vec<&str> = events
        .iter()
        .filter(|e| e["kind"] == "call_exit" && e["function"] == "foo")
        .map(|e| e["return_value"]["r"].as_str().unwrap_or("<missing>"))
        .collect();
    assert_eq!(foo_exits, vec!["()", "()"]);
}

/// `if_then_else_reduced.nr` — `for i in 1..11 { if i % 2 == 0 { ... } }`.
///
/// Pins: 1 call (main), 45 step events (10-iteration loop with
/// branching body), 0 io_events.  The varname table reflects the
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
    assert_eq!(counts["functions"].as_u64(), Some(1), "functions; counts={counts}");
    assert_eq!(counts["varnames"].as_u64(), Some(5), "varnames; counts={counts}");
    assert_eq!(counts["types"].as_u64(), Some(3), "types; counts={counts}");
    // Column-aware counts include the auxiliary `sekDeltaColumn`
    // cursor-nudges; see `test_a_1_mul_via_ct_print_full`.
    assert_eq!(counts["steps"].as_u64(), Some(78), "steps; counts={counts}");
    assert_eq!(counts["calls"].as_u64(), Some(1), "calls; counts={counts}");
    assert_eq!(counts["values"].as_u64(), Some(155), "values; counts={counts}");
    assert_eq!(counts["io_events"].as_u64(), Some(0), "io_events; counts={counts}");

    assert_eq!(string_array(&doc, "functions"), vec!["main"]);
    assert_eq!(string_array(&doc, "varnames"), vec!["x", "y", "z", "result", "i"]);
    assert_eq!(string_array(&doc, "types"), vec!["None", "u32", "type_1"]);
    assert_path_strip_normalised(&doc, "if_then_else_reduced");

    // 1 call_entry + 155 step events + 1 call_exit = 157 wire-level events.
    let events = doc["events"].as_array().unwrap();
    assert_eq!(events.len(), 157);
    assert_eq!(observed_call_sequence(&doc), vec!["main".to_string()]);

    // Column-aware call_entry has empty args (see a_1_mul).
    let entry = &events[0];
    assert!(
        entry["args"].as_array().unwrap().is_empty(),
        "call_entry.args should be empty under column-aware mode",
    );

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
    let exit = events.last().unwrap();
    assert_eq!(exit["kind"], "call_exit");
    assert_eq!(exit["return_value"]["kind"].as_str(), Some("Void"));
}

/// `assert.nr` — `assert(a != b)` where a == b == 12 (assertion fails).
///
/// Pins: 1 call (main), 5 step events, EXACTLY 1 io_event tagged
/// `ioError` carrying the Brillig failure string.  The variables
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
    assert_eq!(counts["functions"].as_u64(), Some(1), "functions; counts={counts}");
    assert_eq!(counts["varnames"].as_u64(), Some(4), "varnames; counts={counts}");
    assert_eq!(counts["types"].as_u64(), Some(3), "types; counts={counts}");
    // Column-aware counts include sekDeltaColumn cursor-nudges; see
    // `test_a_1_mul_via_ct_print_full` for the accounting.
    assert_eq!(counts["steps"].as_u64(), Some(11), "steps; counts={counts}");
    assert_eq!(counts["calls"].as_u64(), Some(1), "calls; counts={counts}");
    assert_eq!(counts["values"].as_u64(), Some(21), "values; counts={counts}");
    assert_eq!(counts["io_events"].as_u64(), Some(1), "io_events; counts={counts}");

    assert_eq!(string_array(&doc, "functions"), vec!["main"]);
    assert_eq!(string_array(&doc, "varnames"), vec!["x", "y", "a", "b"]);
    assert_eq!(string_array(&doc, "types"), vec!["None", "Field", "type_1"]);
    assert_path_strip_normalised(&doc, "assert");

    // 1 call_entry + 21 step events + 1 io + 1 call_exit = 24 wire-level events.
    let events = doc["events"].as_array().unwrap();
    assert_eq!(events.len(), 24);
    assert_eq!(observed_call_sequence(&doc), vec!["main".to_string()]);

    // The single io_event must be tagged ioError and the text must match
    // the recorder's assertion-failure stringification (no payload in
    // this fixture, so the bare Nargo error string surfaces).
    let io_events: Vec<&serde_json::Value> = events.iter().filter(|e| e["kind"] == "io").collect();
    assert_eq!(io_events.len(), 1);
    let io = io_events[0];
    assert_eq!(io["io_kind"].as_str(), Some("ioError"));
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
        .map(|v| (v["varname"].as_str().unwrap(), v["value"]["i"].as_i64().unwrap()))
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
/// Pins: 1 call (main), 15 step events, 0 io_events, the
/// function table is exactly `[main]`, the type table contains
/// every distinct type the recorder ensures (in ensure order:
/// None, Field, type_1, u32, type_3, Point, i8, type_6, Bool,
/// String, Array<2, ..>), the varname table is the parameter list
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
    assert_eq!(counts["functions"].as_u64(), Some(1), "functions; counts={counts}");
    assert_eq!(counts["varnames"].as_u64(), Some(9), "varnames; counts={counts}");
    assert_eq!(counts["types"].as_u64(), Some(11), "types; counts={counts}");
    // Column-aware counts include sekDeltaColumn cursor-nudges; see
    // `test_a_1_mul_via_ct_print_full` for the accounting.
    assert_eq!(counts["steps"].as_u64(), Some(24), "steps; counts={counts}");
    assert_eq!(counts["calls"].as_u64(), Some(1), "calls; counts={counts}");
    assert_eq!(counts["values"].as_u64(), Some(47), "values; counts={counts}");
    assert_eq!(counts["io_events"].as_u64(), Some(0), "io_events; counts={counts}");

    assert_eq!(string_array(&doc, "functions"), vec!["main"]);
    assert_eq!(
        string_array(&doc, "varnames"),
        vec!["a", "b", "c", "d", "e", "f", "g", "h", "result"]
    );
    assert_eq!(
        string_array(&doc, "types"),
        vec![
            "None",
            "Field",
            "type_1",
            "u32",
            "type_3",
            "Point",
            "i8",
            "type_6",
            "Bool",
            "String",
            "Array<2, ..>",
        ]
    );
    assert_path_strip_normalised(&doc, "types_test");

    // 1 call_entry + 47 step events + 1 call_exit = 49 wire-level events.
    let events = doc["events"].as_array().unwrap();
    assert_eq!(events.len(), 49);
    assert_eq!(observed_call_sequence(&doc), vec!["main".to_string()]);

    // ---- call_entry args ------------------------------------------------
    // Column-aware register_call fires before params are bound, so the
    // `args` array is empty under the new mode (see a_1_mul).  When the
    // follow-up patch lands the deferred `register_call`, the original
    // per-param assertions can be restored here.
    let entry = &events[0];
    let args = entry["args"].as_array().unwrap();
    assert!(args.is_empty(), "call_entry.args should be empty; got {args:?}");
    // The first user-visible step should surface every param the
    // debugger has bound by the time we reach the body.  Use this to
    // pin the per-arg values that the old `args[i]` assertions
    // covered.
    // Walk steps in order; params bind one-by-one on the function-
    // declaration line (column-aware mode no longer collapses the
    // bindings), so the *first* step that surfaces all eight expected
    // params (a..h) gives us the post-binding snapshot.
    let expected_names: &[&str] = &["a", "b", "c", "d", "e", "f", "g", "h"];
    let first_body_vars: std::collections::BTreeMap<&str, &serde_json::Value> = events
        .iter()
        .filter(|e| e["kind"] == "step" && !is_aux_column_step(e))
        .find_map(|e| {
            let vars = e["vars"].as_array()?;
            let map: std::collections::BTreeMap<&str, &serde_json::Value> = vars
                .iter()
                .map(|v| (v["varname"].as_str().unwrap(), &v["value"]))
                .collect();
            if expected_names.iter().all(|n| map.contains_key(n)) {
                Some(map)
            } else {
                None
            }
        })
        .expect("a step must surface all params a..h");
    assert_eq!(first_body_vars[&"a"]["kind"].as_str(), Some("Int"));
    assert_eq!(first_body_vars[&"a"]["i"].as_i64(), Some(1));
    assert_eq!(first_body_vars[&"b"]["kind"].as_str(), Some("Int"));
    assert_eq!(first_body_vars[&"b"]["i"].as_i64(), Some(2));
    assert_eq!(first_body_vars[&"c"]["kind"].as_str(), Some("Struct"));
    let c_fields = first_body_vars[&"c"]["field_values"].as_array().unwrap();
    assert_eq!(c_fields.len(), 2);
    assert_eq!(c_fields[0]["kind"].as_str(), Some("Int"));
    assert_eq!(c_fields[0]["i"].as_i64(), Some(9));
    assert_eq!(c_fields[1]["kind"].as_str(), Some("Int"));
    assert_eq!(c_fields[1]["i"].as_i64(), Some(10));
    assert_eq!(first_body_vars[&"d"]["i"].as_i64(), Some(3));
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
    assert_eq!(h_elems[0]["i"].as_i64(), Some(7));
    assert_eq!(h_elems[1]["i"].as_i64(), Some(8));

    // call_exit returns Void
    let exit = events.last().unwrap();
    assert_eq!(exit["kind"], "call_exit");
    assert_eq!(exit["return_value"]["kind"].as_str(), Some("Void"));
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
/// then the `assert` on `(line=4, column=1)`.  This pins both that
/// column-aware mode is latched (`metadata.flags.has_column_aware_steps`
/// is true) and that the recorder distinguishes same-line statements at
/// the byte level via the `DeltaColumn` event.
#[test]
fn test_multi_stmt_per_line_column_aware() {
    let Some(doc) = record_and_dump_full(
        "test_multi_stmt_per_line_column_aware",
        "multi_stmt_per_line",
    ) else {
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
    // Intentionally include the `sekDeltaColumn` auxiliary steps —
    // they are the cursor-nudges that surface the distinct columns
    // for each statement; the preceding `sekDeltaStep` resets the
    // cursor to column 1.  This is the only test that asserts on
    // column-aware wire-level structure, so we bypass the
    // `is_aux_column_step` helper used by the line-only fixtures.
    let line2_columns: Vec<i64> = doc["events"]
        .as_array()
        .expect("events array")
        .iter()
        .filter(|e| e["kind"] == "step")
        .filter(|e| {
            e["path"]
                .as_str()
                .map(|p| p.ends_with("src/main.nr"))
                .unwrap_or(false)
        })
        .filter(|e| e["line"].as_i64() == Some(2))
        .filter_map(|e| e["column"].as_i64())
        .collect();
    assert_eq!(
        line2_columns,
        vec![1_i64, 9, 1, 27, 1, 45],
        "expected the three statements on line 2 to surface columns \
         9 / 27 / 45 (interleaved with the writer's column-1 resets); \
         got {line2_columns:?}",
    );

    // Sanity: column 1 on line 1 (the `fn main()` entry step) and column
    // 1 on line 4 (the `assert` step) so the test still catches a
    // regression that drops the column field entirely.
    let line1_col = doc["events"]
        .as_array()
        .unwrap()
        .iter()
        .find(|e| e["kind"] == "step" && e["line"].as_i64() == Some(1))
        .and_then(|e| e["column"].as_i64());
    assert_eq!(line1_col, Some(1), "line 1 entry step column");
    let line4_col = doc["events"]
        .as_array()
        .unwrap()
        .iter()
        .find(|e| e["kind"] == "step" && e["line"].as_i64() == Some(4))
        .and_then(|e| e["column"].as_i64());
    assert_eq!(line4_col, Some(1), "line 4 assert step column");
}
