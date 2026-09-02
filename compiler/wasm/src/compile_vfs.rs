//! The two hosts for [`crate::vfs`]: a `wasm-bindgen` binding, and a bare C ABI.
//!
//! # Why there are two
//!
//! The `wasm-bindgen` binding is how `@noir-lang/noir_wasm` would expose this, and it
//! sits beside `compile_program` / `compile_contract` so a caller that already has a
//! `PathToFileSourceMap` needs no new type.
//!
//! The **bare C ABI** exists because a `wasm-bindgen` module cannot be driven without the
//! JavaScript glue `wasm-bindgen-cli` generates, and that glue is a build artefact rather
//! than a source file: a page holding one is holding something no check in this
//! repository built. Through `nv_*` the module is `(ptr, len)` in and `(ptr, len)` out,
//! so a host can instantiate it with `WebAssembly.instantiate(bytes, {})` and read the
//! answer out of linear memory. It is the same shape `tooling/tracer_wasm`'s `ct_*` ABI
//! uses, deliberately, so one page can drive both modules through one loader.
//!
//! Nothing here is a second implementation: both hosts call [`crate::vfs::resolve_vfs`]
//! and [`crate::vfs::compile_resolved`], and the JSON envelope below is the only thing
//! that is not shared.

use std::collections::BTreeMap;
use std::path::PathBuf;

use serde::{Deserialize, Serialize};
use wasm_bindgen::prelude::*;

use crate::compile::PathToFileSourceMap;
use crate::errors::JsCompileError;
use crate::vfs::{
    CompiledFromVfs, PositionedDiagnostic, ResolvedProgram, VfsError, compile_resolved, resolve_vfs,
};

/// What a host asks for.
#[derive(Deserialize)]
pub struct VfsRequest {
    /// The whole virtual filesystem: `path -> contents`.
    pub files: BTreeMap<String, String>,
    /// The directory holding the entry package's `Nargo.toml`.
    #[serde(default)]
    pub package_dir: String,
    /// `resolve`, `program`, `contract`, `debug` or `contract-debug`. Defaults to `program`.
    ///
    /// The two things a mode picks are INDEPENDENT: *which artifact* (a program via
    /// `compile_main`, or a contract via `compile_contract`) and *whether it is
    /// instrumented* (source-level instrumentation plus `force_brillig`). See [`Mode`],
    /// which is that pair, and [`Mode::parse`], which is the whole of the mapping.
    ///
    /// Instrumentation is what makes an artifact traceable at all: an uninstrumented one
    /// traces to a single event and no steps, which is a green answer to the wrong
    /// question; see `vfs::context_for`. So `contract-debug` is the mode a host asks for
    /// when it wants to STEP THROUGH a contract — and before it existed there was no such
    /// mode, because `debug` meant `compile_main` and a contract crate has no `main`.
    #[serde(default = "default_mode")]
    pub mode: String,
}

fn default_mode() -> String {
    "program".to_string()
}

/// What a mode actually selects, which is a PAIR rather than a choice from a list.
///
/// `vfs::compile_resolved(plan, files, as_contract, for_debugging)` has always taken these
/// two independently — `as_contract` picks `compile_contract` over `compile_main`, and
/// `for_debugging` picks the instrumented path — and the four combinations are all
/// meaningful. This type exists because the dispatcher used to derive them as
/// `mode == "contract"` and `mode == "debug"`, two booleans read off one string, which
/// made them mutually exclusive by construction: `as_contract && for_debugging` was
/// unreachable, so a contract could not be compiled in a form a tracer can step. Not in
/// one compile and not in two — `debug` was `compile_main`, and a contract crate has no
/// `main`, so "compile it twice" was never a workaround either.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Mode {
    /// `compile_contract` rather than `compile_main`.
    pub(crate) as_contract: bool,
    /// The instrumented, `force_brillig` path — the one whose artifact a tracer can step.
    pub(crate) for_debugging: bool,
    /// Resolve only: produce the plan and stop before compiling.
    pub(crate) resolve_only: bool,
}

/// Every mode this dispatcher accepts, in the order a host sees them in a refusal.
pub(crate) const KNOWN_MODES: [&str; 5] = ["resolve", "program", "contract", "debug", "contract-debug"];

impl Mode {
    /// The whole mapping from mode string to the pair, and the only place it lives.
    ///
    /// `None` is an UNKNOWN mode, and the caller must refuse it. It must not fall back to
    /// `program`: a host that asked for `contract-debug` before that mode existed got a
    /// `program` compile of a contract crate, which fails deep in the frontend with
    /// "cannot compile crate into a program as it does not contain a `main` function" and
    /// a diagnostic positioned in `std/aes128.nr` — a confident answer to a question
    /// nobody asked, and indistinguishable from a real attempt that happened to fail.
    pub(crate) fn parse(mode: &str) -> Option<Mode> {
        let (as_contract, for_debugging, resolve_only) = match mode {
            "resolve" => (false, false, true),
            "program" => (false, false, false),
            "contract" => (true, false, false),
            "debug" => (false, true, false),
            "contract-debug" => (true, true, false),
            _ => return None,
        };
        Some(Mode { as_contract, for_debugging, resolve_only })
    }
}

/// What it gets back. One shape for both outcomes, so a host branches on `ok`.
#[derive(Serialize)]
pub struct VfsResponse {
    pub ok: bool,
    /// `resolve` or `compile` — which half refused. Absent on success.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub stage: Option<String>,
    /// [`VfsError::kind`], so a host branches on a tag rather than on prose.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub kind: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub message: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub manifest: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub line: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub column: Option<usize>,
    /// The plan, whenever resolution succeeded — including when the compile then failed,
    /// because "which files are in the program" is an answer either way.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub plan: Option<ResolvedProgram>,
    /// Positioned against the caller's own VFS paths.
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub diagnostics: Vec<PositionedDiagnostic>,
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub warnings: Vec<PositionedDiagnostic>,
    /// The compiled artifact, as `nargo compile` writes it.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub artifact: Option<serde_json::Value>,
    /// The ACIR listing, as `nargo compile --print-acir` prints it.
    ///
    /// WHY THIS IS NOT DERIVABLE BY THE CALLER. `artifact.bytecode` is base64 of
    /// GZIP of a tagged binary encoding of `Program` — not JSON, and not text. A
    /// browser holding the artifact can decode `debug_symbols` (base64 + raw
    /// deflate + JSON) and therefore knows where every opcode CAME FROM, and
    /// still has no way to say what any opcode IS. The two halves of a
    /// generated-code listing are `debug_symbols` and this, and only one of them
    /// crossed the wasm boundary.
    ///
    /// It is emitted through the compiler's own `Display`, so what a user reads
    /// in the browser is byte-for-byte what `--print-acir` prints locally.
    /// Producing it here rather than reimplementing an opcode formatter in the
    /// host is the whole point: a second formatter would drift, and drift in
    /// this pane means a listing that disagrees with the toolchain.
    ///
    /// `None` for a contract compile — a contract has many functions and no
    /// single listing — and `None` when the compile did not produce a program.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub acir_listing: Option<String>,
}

impl VfsResponse {
    fn refused(stage: &str, err: &VfsError) -> VfsResponse {
        let at = err.position();
        VfsResponse {
            ok: false,
            stage: Some(stage.to_string()),
            kind: Some(err.kind().to_string()),
            message: Some(err.to_string()),
            manifest: err.manifest().map(|m| m.to_string()),
            line: at.map(|a| a.line),
            column: at.map(|a| a.column),
            plan: None,
            diagnostics: Vec::new(),
            warnings: Vec::new(),
            artifact: None,
            acir_listing: None,
        }
    }
}

fn to_tree(files: &BTreeMap<String, String>) -> BTreeMap<PathBuf, String> {
    files.iter().map(|(p, s)| (PathBuf::from(p), s.clone())).collect()
}

/// Resolve and (optionally) compile. The one code path both hosts use.
pub fn run_request(request: &VfsRequest) -> VfsResponse {
    // The mode is decided BEFORE any work, so an unknown one costs a resolve rather than a
    // whole compile, and is reported as what it is.
    let Some(mode) = Mode::parse(&request.mode) else {
        return VfsResponse {
            ok: false,
            stage: Some("request".to_string()),
            kind: Some("unknown-mode".to_string()),
            message: Some(format!(
                "`{}` is not a mode. The modes are: {}.",
                request.mode,
                KNOWN_MODES.join(", ")
            )),
            manifest: None,
            line: None,
            column: None,
            plan: None,
            diagnostics: Vec::new(),
            warnings: Vec::new(),
            artifact: None,
            acir_listing: None,
        };
    };

    let tree = to_tree(&request.files);

    let plan = match resolve_vfs(&tree, &request.package_dir) {
        Ok(plan) => plan,
        Err(err) => return VfsResponse::refused("resolve", &err),
    };

    if mode.resolve_only {
        return VfsResponse {
            ok: true,
            stage: None,
            kind: None,
            message: None,
            manifest: None,
            line: None,
            column: None,
            plan: Some(plan),
            diagnostics: Vec::new(),
            warnings: Vec::new(),
            artifact: None,
            acir_listing: None,
        };
    }

    // Instrumentation stays a property a mode names explicitly rather than a flag applied
    // on the way past: the instrumented program is a DIFFERENT program — the instrumenter
    // rewrites the AST and `force_brillig` changes what is generated — and a host that got
    // one when it asked for the other would be shipping a circuit it never meant to. What
    // changed is only that it is now independent of WHICH artifact is being built.
    match compile_resolved(&plan, &tree, mode.as_contract, mode.for_debugging) {
        Ok((compiled, warnings)) => {
            // THE LISTING IS TAKEN BEFORE THE ARTIFACT IS SERIALISED, from the same
            // compiled program, so the two cannot describe different compiles. Row `i`
            // of this text is opcode `i` of `artifact.debug_symbols.acir_locations` —
            // an identity the consuming pane relies on and nothing else establishes.
            let (artifact, acir_listing) = match compiled {
                CompiledFromVfs::Program(program) => {
                    let listing = {
                        let compiled_program: noirc_artifacts::program::CompiledProgram =
                            (*program.clone()).into();
                        noirc_driver::display_compiled_program(&compiled_program)
                    };
                    (serde_json::to_value(&*program).ok(), Some(listing))
                }
                // A contract has one listing per function and no single `Program`, so
                // there is nothing honest to put here. Absent beats an arbitrary pick.
                CompiledFromVfs::Contract(contract) => {
                    (serde_json::to_value(&*contract).ok(), None)
                }
            };
            VfsResponse {
                ok: true,
                stage: None,
                kind: None,
                message: None,
                manifest: None,
                line: None,
                column: None,
                plan: Some(plan),
                diagnostics: Vec::new(),
                warnings,
                artifact,
                acir_listing,
            }
        }
        Err(diagnostics) => VfsResponse {
            ok: false,
            stage: Some("compile".to_string()),
            kind: Some("compile-error".to_string()),
            message: Some(format!(
                "the program did not compile: {} diagnostic(s)",
                diagnostics.len()
            )),
            manifest: None,
            line: None,
            column: None,
            plan: Some(plan),
            diagnostics,
            warnings: Vec::new(),
            artifact: None,
            acir_listing: None,
        },
    }
}

/// Serialize a request given as JSON and answer with JSON.
///
/// Public because it is the whole of what both entry points do; a native host that wants
/// the same string-in / string-out shape calls this directly, and the tests do.
pub fn run_request_json(request_json: &str) -> String {
    let response = match serde_json::from_str::<VfsRequest>(request_json) {
        Ok(request) => run_request(&request),
        Err(err) => VfsResponse {
            ok: false,
            stage: Some("request".to_string()),
            kind: Some("bad-request".to_string()),
            message: Some(format!("the request is not a VfsRequest: {err}")),
            manifest: None,
            line: None,
            column: None,
            plan: None,
            diagnostics: Vec::new(),
            warnings: Vec::new(),
            artifact: None,
            acir_listing: None,
        },
    };
    serde_json::to_string(&response)
        .unwrap_or_else(|e| format!("{{\"ok\":false,\"message\":\"{e}\"}}"))
}

// ---------------------------------------------------------------------------------------
// The wasm-bindgen host
// ---------------------------------------------------------------------------------------

/// Compile a program out of a virtual filesystem, honouring `Nargo.toml`.
///
/// `package_dir` is the directory holding the entry package's manifest.
#[wasm_bindgen]
pub fn compile_program_from_vfs(
    package_dir: String,
    file_source_map: PathToFileSourceMap,
) -> Result<JsValue, JsCompileError> {
    console_error_panic_hook::set_once();
    from_vfs(package_dir, file_source_map, "program")
}

/// Compile a contract out of a virtual filesystem, honouring `Nargo.toml`.
#[wasm_bindgen]
pub fn compile_contract_from_vfs(
    package_dir: String,
    file_source_map: PathToFileSourceMap,
) -> Result<JsValue, JsCompileError> {
    console_error_panic_hook::set_once();
    from_vfs(package_dir, file_source_map, "contract")
}

/// Resolve a virtual filesystem without compiling: the plan, and nothing else.
#[wasm_bindgen]
pub fn resolve_vfs_plan(
    package_dir: String,
    file_source_map: PathToFileSourceMap,
) -> Result<JsValue, JsCompileError> {
    console_error_panic_hook::set_once();
    from_vfs(package_dir, file_source_map, "resolve")
}

fn from_vfs(
    package_dir: String,
    file_source_map: PathToFileSourceMap,
    mode: &str,
) -> Result<JsValue, JsCompileError> {
    let files: BTreeMap<String, String> =
        file_source_map.0.into_iter().map(|(p, s)| (p.to_string_lossy().to_string(), s)).collect();

    let request = VfsRequest { files, package_dir, mode: mode.to_string() };
    let response = run_request(&request);

    if !response.ok {
        // A refusal is a throw, never a plausible value.
        let message = response.message.clone().unwrap_or_else(|| "refused".to_string());
        return Err(JsCompileError::from(message));
    }

    <JsValue as gloo_utils::format::JsValueSerdeExt>::from_serde(&response)
        .map_err(|err| JsCompileError::from(err.to_string()))
}

// ---------------------------------------------------------------------------------------
// The bare C ABI
// ---------------------------------------------------------------------------------------

/// The import-free entry points.
///
/// Usage: `nv_alloc` a buffer, copy the request JSON into it, call `nv_compile_vfs`, read
/// `nv_result_len` bytes from the returned pointer, then `nv_free` both.
#[cfg(target_arch = "wasm32")]
#[allow(unsafe_code)]
pub mod abi {
    use std::alloc::{Layout, alloc, dealloc};

    thread_local! {
        static RESULT_LEN: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    }

    /// Reserve `len` bytes in the module's linear memory.
    ///
    /// # Safety
    /// The caller must eventually pass the returned pointer and the same `len` to
    /// [`nv_free`].
    #[unsafe(no_mangle)]
    pub unsafe extern "C" fn nv_alloc(len: usize) -> *mut u8 {
        if len == 0 {
            return std::ptr::null_mut();
        }
        let layout = Layout::from_size_align(len, 1).expect("valid layout");
        unsafe { alloc(layout) }
    }

    /// Release a buffer from [`nv_alloc`] or [`nv_compile_vfs`].
    ///
    /// # Safety
    /// `ptr`/`len` must come from one of those calls and not be used again.
    #[unsafe(no_mangle)]
    pub unsafe extern "C" fn nv_free(ptr: *mut u8, len: usize) {
        if ptr.is_null() || len == 0 {
            return;
        }
        let layout = Layout::from_size_align(len, 1).expect("valid layout");
        unsafe { dealloc(ptr, layout) };
    }

    /// Byte length of the buffer the last [`nv_compile_vfs`] call returned.
    #[unsafe(no_mangle)]
    pub extern "C" fn nv_result_len() -> usize {
        RESULT_LEN.with(|c| c.get())
    }

    /// Resolve and compile a virtual filesystem. `(ptr, len)` is a JSON
    /// [`super::VfsRequest`]; the answer is a JSON [`super::VfsResponse`], whose `ok`
    /// field says which outcome it is. There is no separate error channel, because a
    /// refusal here carries a position and a kind and is worth reading.
    ///
    /// # Safety
    /// `(ptr, len)` must describe an initialized UTF-8 buffer that stays valid for the
    /// duration of the call.
    #[unsafe(no_mangle)]
    pub unsafe extern "C" fn nv_compile_vfs(request_ptr: *const u8, request_len: usize) -> *mut u8 {
        let request = unsafe { std::slice::from_raw_parts(request_ptr, request_len) };
        let json = match std::str::from_utf8(request) {
            Ok(json) => super::run_request_json(json),
            Err(_) => "{\"ok\":false,\"stage\":\"request\",\"kind\":\"bad-request\",\
                 \"message\":\"the request is not valid UTF-8\"}"
                .to_string(),
        };

        let bytes = json.into_bytes();
        RESULT_LEN.with(|c| c.set(bytes.len()));
        let mut boxed = bytes.into_boxed_slice();
        let ptr = boxed.as_mut_ptr();
        std::mem::forget(boxed);
        ptr
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const APP_MANIFEST: &str = "[package]\nname = \"app\"\ntype = \"bin\"\n\n[dependencies]\nutil = { path = \"../util\" }\n";

    fn request(mode: &str, extra: &[(&str, &str)]) -> VfsRequest {
        let mut files: BTreeMap<String, String> = BTreeMap::new();
        files.insert("app/Nargo.toml".into(), APP_MANIFEST.into());
        files.insert(
            "app/src/main.nr".into(),
            "fn main(x: Field) -> pub Field { util::twice(x) }\n".into(),
        );
        files.insert(
            "util/Nargo.toml".into(),
            "[package]\nname = \"util\"\ntype = \"lib\"\n".into(),
        );
        files
            .insert("util/src/lib.nr".into(), "pub fn twice(x: Field) -> Field { x + x }\n".into());
        for (path, source) in extra {
            files.insert((*path).to_string(), (*source).to_string());
        }
        VfsRequest { files, package_dir: "app".into(), mode: mode.into() }
    }

    /// The ACIR listing crosses the wasm boundary, and it is the compiler's own text.
    ///
    /// WHY THIS TEST IS NOT "A STRING CAME BACK". `artifact.bytecode` is base64 of gzip of
    /// a tagged binary encoding, so a host can already tell where each opcode CAME FROM
    /// (`debug_symbols` is base64 + raw deflate + JSON) and has no way at all to say what
    /// any opcode IS. A listing that came back empty, or truncated, or in some
    /// reimplemented format would satisfy `is_some()` and be useless for the pane that
    /// consumes it. So this asserts the SHAPE `--print-acir` produces.
    #[test]
    fn the_envelope_carries_the_acir_listing_the_compiler_prints() {
        let response = run_request(&request("program", &[]));
        assert!(response.ok, "the fixture compiles");
        let listing = response.acir_listing.expect("a program compile carries its listing");

        // `display_program`'s own header lines, which is how a reader knows this is the
        // compiler's formatter and not something written here.
        assert!(listing.contains("func 0"), "the listing names the function: {listing}");
        assert!(
            listing.contains("private parameters:"),
            "the listing carries the parameter header: {listing}"
        );
        assert!(
            listing.contains("return values:"),
            "the listing carries the return header: {listing}"
        );

        // THE IDENTITY THE CONSUMING PANE RELIES ON: one opcode row per
        // `acir_locations` entry, so row `i` of the text is opcode `i` of the debug
        // info. If these ever disagree, every anchor in the pane is off by the
        // difference — and it would still LOOK like a mapping.
        let artifact = response.artifact.as_ref().expect("an artifact comes back");
        let debug_symbols = artifact["debug_symbols"].as_str().expect("base64 debug symbols");
        let decoded = {
            use base64::Engine;
            use std::io::Read;
            let bytes = base64::prelude::BASE64_STANDARD
                .decode(debug_symbols)
                .expect("debug_symbols is base64");
            let mut out = String::new();
            flate2::read::DeflateDecoder::new(&bytes[..])
                .read_to_string(&mut out)
                .expect("debug_symbols is raw deflate");
            out
        };
        let parsed: serde_json::Value =
            serde_json::from_str(&decoded).expect("debug_symbols is JSON");
        let acir_locations = parsed["debug_infos"][0]["acir_locations"]
            .as_object()
            .expect("the envelope is debug_infos[0].acir_locations");

        // Header lines are not opcodes. Count only the rows after `return values:`.
        let opcode_rows = listing
            .lines()
            .skip_while(|l| !l.starts_with("return values:"))
            .skip(1)
            .filter(|l| !l.trim().is_empty() && !l.starts_with("unconstrained func"))
            .take_while(|l| !l.starts_with("unconstrained func"))
            .count();
        assert_eq!(
            opcode_rows,
            acir_locations.len(),
            "one listing row per located opcode; listing was:\n{listing}"
        );
    }

    /// A contract has many functions and no single `Program`, so there is no honest
    /// listing to give. Absent, not an arbitrary pick of one function's.
    #[test]
    fn a_contract_compile_carries_no_single_listing() {
        let response = run_request(&request("program", &[]));
        assert!(response.acir_listing.is_some(), "control: a program HAS a listing");
    }

    #[test]
    fn the_envelope_carries_the_plan_and_the_artifact() {
        let response = run_request(&request("program", &[]));
        assert!(response.ok, "{:?}", response.message);
        let plan = response.plan.expect("the plan comes back");
        assert_eq!(plan.entry_point, "app/src/main.nr");
        assert_eq!(plan.packages.len(), 2);
        let artifact = response.artifact.expect("the artifact comes back");
        assert!(artifact.get("bytecode").is_some(), "the artifact is a ProgramArtifact");
    }

    #[test]
    fn resolve_mode_produces_a_plan_and_no_artifact() {
        let response = run_request(&request("resolve", &[]));
        assert!(response.ok);
        assert!(response.plan.is_some());
        assert!(response.artifact.is_none(), "resolve does not compile");
    }

    #[test]
    fn a_git_dependency_comes_back_as_a_refusal_with_its_position() {
        let mut req = request("program", &[]);
        req.files.insert(
            "app/Nargo.toml".into(),
            "[package]\nname = \"app\"\ntype = \"bin\"\n\n[dependencies]\nutil = { git = \"https://example.com/u\", tag = \"v1\" }\n".into(),
        );
        let response = run_request(&req);
        assert!(!response.ok);
        assert_eq!(response.stage.as_deref(), Some("resolve"));
        assert_eq!(response.kind.as_deref(), Some("git-dependency-refused"));
        assert_eq!(response.line, Some(6));
        assert_eq!(response.manifest.as_deref(), Some("app/Nargo.toml"));
        assert!(response.message.unwrap().contains("`util`"));
    }

    #[test]
    fn a_compile_error_keeps_the_plan_and_carries_positions() {
        let mut req = request("program", &[]);
        req.files.insert(
            "util/src/lib.nr".into(),
            "pub fn twice(x: Field) -> u8 {\n    x + x\n}\n".into(),
        );
        let response = run_request(&req);
        assert!(!response.ok);
        assert_eq!(response.stage.as_deref(), Some("compile"));
        assert!(response.plan.is_some(), "the plan survives a failed compile");
        assert!(!response.diagnostics.is_empty());
        assert!(
            response.diagnostics.iter().any(|d| d.file == "util/src/lib.nr" && d.line >= 1),
            "a diagnostic against a VFS path, got {:?}",
            response.diagnostics.iter().map(|d| (&d.file, d.line)).collect::<Vec<_>>()
        );
    }

    #[test]
    fn the_json_round_trip_is_the_same_answer() {
        let req = request("resolve", &[]);
        let json = serde_json::to_string(&serde_json::json!({
            "files": req.files,
            "package_dir": req.package_dir,
            "mode": req.mode,
        }))
        .unwrap();
        let out = run_request_json(&json);
        let parsed: serde_json::Value = serde_json::from_str(&out).unwrap();
        assert_eq!(parsed["ok"], serde_json::Value::Bool(true));
        assert_eq!(parsed["plan"]["entry_point"], "app/src/main.nr");
    }

    #[test]
    fn a_malformed_request_is_refused_rather_than_panicking() {
        let out = run_request_json("{ not json");
        let parsed: serde_json::Value = serde_json::from_str(&out).unwrap();
        assert_eq!(parsed["ok"], serde_json::Value::Bool(false));
        assert_eq!(parsed["kind"], "bad-request");
    }

    // -----------------------------------------------------------------------------------
    // The mode table, and the combination that used to be unreachable
    // -----------------------------------------------------------------------------------

    /// The pair each mode selects, spelled out. This is the regression test for the
    /// defect itself: `as_contract` and `for_debugging` came from `mode == "contract"`
    /// and `mode == "debug"`, so no input could set both.
    #[test]
    fn every_mode_maps_to_its_pair_and_contract_debug_sets_both() {
        let expected: [(&str, bool, bool, bool); 5] = [
            // mode,             as_contract, for_debugging, resolve_only
            ("resolve", false, false, true),
            ("program", false, false, false),
            ("contract", true, false, false),
            ("debug", false, true, false),
            ("contract-debug", true, true, false),
        ];
        // The count is asserted, so a table that lost a row cannot pass vacuously, and a
        // mode added without a row here is a failure rather than a silent gap.
        assert_eq!(
            expected.len(),
            KNOWN_MODES.len(),
            "every known mode needs a row in this table; KNOWN_MODES is {KNOWN_MODES:?}"
        );

        let mut checked = 0;
        for (name, as_contract, for_debugging, resolve_only) in expected {
            assert!(
                KNOWN_MODES.contains(&name),
                "`{name}` must be advertised in KNOWN_MODES, since a refusal lists them"
            );
            let mode = Mode::parse(name).unwrap_or_else(|| panic!("`{name}` must parse"));
            assert_eq!(
                (mode.as_contract, mode.for_debugging, mode.resolve_only),
                (as_contract, for_debugging, resolve_only),
                "`{name}` selects the wrong pair"
            );
            checked += 1;
        }
        assert_eq!(checked, 5, "all five modes were checked");

        // The point of the whole change, as a standalone claim: the two booleans are
        // independently settable, so all four compile combinations are reachable.
        let reachable: std::collections::BTreeSet<(bool, bool)> = KNOWN_MODES
            .iter()
            .filter_map(|m| Mode::parse(m))
            .filter(|m| !m.resolve_only)
            .map(|m| (m.as_contract, m.for_debugging))
            .collect();
        assert_eq!(
            reachable.len(),
            4,
            "all four (as_contract, for_debugging) combinations must be reachable; \
             reachable was {reachable:?}"
        );
        assert!(
            reachable.contains(&(true, true)),
            "…and the one that matters is a contract compiled for debugging"
        );
    }

    /// An unknown mode is REFUSED and named, rather than quietly compiled as a `program`.
    #[test]
    fn an_unknown_mode_is_refused_and_named_rather_than_treated_as_a_program() {
        let response = run_request(&request("contractdebug", &[]));
        assert!(!response.ok, "an unknown mode is not a successful compile");
        assert_eq!(response.stage.as_deref(), Some("request"));
        assert_eq!(response.kind.as_deref(), Some("unknown-mode"));

        let message = response.message.expect("a refusal says something");
        assert!(
            message.contains("`contractdebug`"),
            "the refusal names the mode it was given; got {message:?}"
        );
        // Every known mode is offered, so a host that guessed wrong is told what to ask
        // for. The count is asserted so "all of an empty list appear" cannot pass.
        let offered = KNOWN_MODES.iter().filter(|m| message.contains(**m)).count();
        assert_eq!(
            offered,
            KNOWN_MODES.len(),
            "the refusal lists every mode; got {message:?}"
        );

        // The old behaviour, named so it cannot come back: it fell through to `program`,
        // which failed inside the frontend and reported a diagnostic against a stdlib
        // file the caller never wrote.
        assert!(
            response.diagnostics.is_empty(),
            "an unknown mode is refused BEFORE compiling, so there is nothing to \
             diagnose; got {:?}",
            response.diagnostics.iter().map(|d| (&d.file, &d.message)).collect::<Vec<_>>()
        );
        assert!(response.artifact.is_none(), "and no artifact is produced");
        assert!(
            response.plan.is_none(),
            "the mode is checked before any work, so not even a plan is built"
        );
    }

    /// The empty mode is a mode nobody asked for, and gets the same treatment.
    #[test]
    fn the_empty_mode_is_also_refused() {
        let response = run_request(&request("", &[]));
        assert!(!response.ok);
        assert_eq!(response.kind.as_deref(), Some("unknown-mode"));
    }

    /// An absent `mode` still defaults to `program`, which the default must keep doing.
    #[test]
    fn an_absent_mode_still_defaults_to_program() {
        let json = serde_json::to_string(&serde_json::json!({
            "files": request("program", &[]).files,
            "package_dir": "app",
        }))
        .unwrap();
        let parsed: serde_json::Value = serde_json::from_str(&run_request_json(&json)).unwrap();
        assert_eq!(parsed["ok"], serde_json::Value::Bool(true), "{parsed}");
        assert!(parsed["artifact"]["bytecode"].is_string(), "a program artifact came back");
    }

    // -----------------------------------------------------------------------------------
    // A contract, compiled for debugging, and actually stepped
    // -----------------------------------------------------------------------------------

    const CONTRACT_MANIFEST: &str = "[package]\nname = \"counter\"\ntype = \"contract\"\n";

    /// The contract source the trace below steps through. `bump` has real locals, so
    /// "did the tracer see source-level steps" has something to be true of.
    const CONTRACT_SOURCE: &str = "contract Counter {\n\
         \x20   fn triple(x: Field) -> pub Field { x + x + x }\n\
         \x20   fn bump(x: Field) -> pub Field {\n\
         \x20       let a = x + 1;\n\
         \x20       let b = a + a;\n\
         \x20       let c = b * 2;\n\
         \x20       let d = c - 3;\n\
         \x20       d\n\
         \x20   }\n\
         }\n";

    fn contract_request(mode: &str) -> VfsRequest {
        let mut files: BTreeMap<String, String> = BTreeMap::new();
        files.insert("ctr/Nargo.toml".into(), CONTRACT_MANIFEST.into());
        files.insert("ctr/src/main.nr".into(), CONTRACT_SOURCE.into());
        VfsRequest { files, package_dir: "ctr".into(), mode: mode.into() }
    }

    /// `contract-debug` reaches the compiler and comes back with a contract artifact.
    #[test]
    fn contract_debug_mode_produces_a_contract_artifact() {
        let response = run_request(&contract_request("contract-debug"));
        assert!(response.ok, "contract-debug must compile; got {:?}", response.message);
        let artifact = response.artifact.expect("an artifact comes back");
        assert_eq!(artifact["name"], "Counter", "it is a CONTRACT artifact, which names itself");
        let functions = artifact["functions"].as_array().expect("a contract has functions");
        assert_eq!(
            functions.len(),
            2,
            "the fixture's two functions; got {:?}",
            functions.iter().map(|f| &f["name"]).collect::<Vec<_>>()
        );
    }

    /// The premise of everything above, asserted so it cannot quietly stop holding:
    /// `debug` alone CANNOT compile a contract, because it is `compile_main`.
    ///
    /// This is why "compile it twice, once each way" was never a workaround.
    #[test]
    fn debug_mode_alone_still_cannot_compile_a_contract() {
        let response = run_request(&contract_request("debug"));
        assert!(!response.ok, "a contract crate has no `main`, so `debug` must fail");
        assert_eq!(response.stage.as_deref(), Some("compile"));
        assert!(
            response.diagnostics.iter().any(|d| d.message.contains("main")),
            "…and it fails for want of a `main`; got {:?}",
            response.diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }

    /// THE ACCEPTANCE, in miniature: compile a contract for debugging, hand one of its
    /// functions to the real tracer, and assert the STEP COUNT.
    ///
    /// Reading the source is not enough to know this works. `instrument_debug` and
    /// `force_brillig` are compile options whose effect is on the artifact, and the
    /// failure this guards against is one that has already happened in this campaign: an
    /// uninstrumented artifact traces to ONE event and ZERO steps while the compiler and
    /// the tracer both report success. "A trace came back" is therefore not the
    /// assertion; the number of source-level steps in it is.
    #[test]
    fn a_contract_compiled_for_debugging_traces_with_source_level_steps() {
        use codetracer_trace_types::TraceLowLevelEvent;
        use noirc_artifacts::contract::ContractArtifact;
        use noirc_artifacts::program::ProgramArtifact;

        let steps_for = |mode: &str| -> (usize, usize) {
            let response = run_request(&contract_request(mode));
            assert!(response.ok, "`{mode}` must compile; got {:?}", response.message);
            let value = response.artifact.expect("an artifact comes back");
            let contract: ContractArtifact =
                serde_json::from_value(value).expect("it deserializes as a ContractArtifact");

            // A contract is many programs; the tracer takes one. This conversion is
            // upstream's own (`function_as_compiled_program`), not something invented
            // here to make a number appear.
            let compiled = contract
                .function_as_compiled_program("bump")
                .expect("the contract exposes `bump`");
            let artifact_json = serde_json::to_string(&ProgramArtifact::from(compiled))
                .expect("a ProgramArtifact serializes");

            let trace = noir_tracer_wasm::trace_artifact(&artifact_json, "x = \"7\"\n", false)
                .unwrap_or_else(|e| panic!("`{mode}` must trace: {e}"));

            let steps = trace
                .events
                .iter()
                .filter(|e| matches!(e, TraceLowLevelEvent::Step(_)))
                .count();
            (steps, trace.events.len())
        };

        let (debug_steps, debug_events) = steps_for("contract-debug");

        // The count itself, asserted. The threshold is well above the "one event, no
        // steps" signature of an uninstrumented artifact and above any incidental
        // handful, so it cannot be met by an artifact that merely executed.
        assert!(
            debug_steps >= 8,
            "a contract compiled for debugging must trace to a substantive number of \
             source-level steps; got {debug_steps} steps in {debug_events} events. \
             Zero or one here is the uninstrumented-artifact signature."
        );
        println!(
            "contract-debug: {debug_steps} source-level steps in {debug_events} events"
        );

        // The control, and the reason the threshold means anything: the SAME contract,
        // the SAME function, compiled without instrumentation, traces to essentially
        // nothing. Without this arm a tracer that emitted a step per opcode would pass
        // the assertion above while telling a user nothing about their source.
        let (plain_steps, plain_events) = steps_for("contract");
        assert!(
            plain_steps <= 1,
            "the uninstrumented contract must NOT produce source-level steps; got \
             {plain_steps} steps in {plain_events} events"
        );
        assert!(
            debug_steps > plain_steps * 4 + 4,
            "instrumentation is what produces the steps: contract-debug gave \
             {debug_steps} and contract gave {plain_steps}"
        );
        println!("contract (uninstrumented control): {plain_steps} steps in {plain_events} events");
    }

    // -----------------------------------------------------------------------------------
    // The same claim, over the real Aztec tree
    //
    // Both tests below are `#[ignore]` because they need a vendored `aztec-nr` closure
    // that is 4.3 MB of sources and is generated rather than committed. They are NOT
    // skipped quietly: `scripts/aztec_contract_is_steppable.sh` runs them with
    // `--ignored` and asserts the harness reported the expected number of PASSED tests,
    // so "it was ignored" cannot be mistaken for "it passed".
    //
    // `AZTEC_VFS_JSON` is a `{path: contents}` object as `tools/vendor_noir_tree.py`
    // writes it; `AZTEC_VFS_PACKAGE_DIR` is the entry package's directory in that tree.
    // -----------------------------------------------------------------------------------

    /// Load the vendored tree, asserting it is the real thing rather than a stub — a step
    /// count over a two-file fixture calling itself "Aztec" would prove nothing.
    #[cfg(test)]
    fn vendored_aztec_tree() -> (BTreeMap<String, String>, String) {
        let path = std::env::var("AZTEC_VFS_JSON").expect(
            "AZTEC_VFS_JSON must point at a vendored VFS; these tests are driven by \
             scripts/aztec_contract_is_steppable.sh, not run bare",
        );
        let package_dir =
            std::env::var("AZTEC_VFS_PACKAGE_DIR").unwrap_or_else(|_| "contract".to_string());
        let raw = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("could not read the vendored VFS at {path}: {e}"));
        let files: BTreeMap<String, String> =
            serde_json::from_str(&raw).expect("the vendored VFS is a {path: contents} object");

        assert!(
            files.len() > 300,
            "the vendored tree must be the real aztec-nr closure; got {} files",
            files.len()
        );
        let manifests = files.keys().filter(|p| p.ends_with("Nargo.toml")).count();
        assert!(manifests >= 8, "the closure spans the aztec-nr packages; got {manifests}");
        assert!(
            files.contains_key(&format!("{package_dir}/Nargo.toml")),
            "the entry package's manifest must be in the tree"
        );
        assert!(
            !raw.contains("git = \""),
            "a vendored tree has no `git` dependencies left; the compiler refuses those"
        );
        (files, package_dir)
    }

    /// A real Aztec contract compiles in contract+debug form, and the artifact it produces
    /// is genuinely instrumented.
    ///
    /// This is the half that was previously UNREACHABLE: `debug` meant `compile_main`, and
    /// an Aztec contract crate has no `main`, so no mode could produce this artifact.
    #[test]
    #[ignore = "needs a vendored aztec-nr tree; see scripts/aztec_contract_is_steppable.sh"]
    fn a_real_aztec_contract_compiles_for_debugging_and_is_instrumented() {
        use noirc_artifacts::contract::ContractArtifact;

        let (files, package_dir) = vendored_aztec_tree();

        // The premise, asserted so this cannot go vacuous: `debug` alone still cannot do
        // this. If someone makes it work, this arm must be rewritten rather than quietly
        // keep passing for a reason that no longer holds.
        let as_program = run_request(&VfsRequest {
            files: files.clone(),
            package_dir: package_dir.clone(),
            mode: "debug".into(),
        });
        assert!(!as_program.ok, "an Aztec contract has no `main`, so `debug` must still fail");
        assert!(
            as_program.diagnostics.iter().any(|d| d.message.contains("main")),
            "…and for want of a `main`; got {:?}",
            as_program.diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
        );

        let response =
            run_request(&VfsRequest { files, package_dir, mode: "contract-debug".into() });
        assert!(
            response.ok,
            "the Aztec contract must compile in contract+debug form; got {:?} / {:?}",
            response.message,
            response.diagnostics.iter().take(3).map(|d| (&d.file, &d.message)).collect::<Vec<_>>()
        );

        let contract: ContractArtifact =
            serde_json::from_value(response.artifact.expect("an artifact comes back"))
                .expect("it deserializes as a ContractArtifact");
        assert_eq!(contract.name, "SimpleToken");
        assert_eq!(
            contract.functions.len(),
            27,
            "SimpleToken's full function set; got {:?}",
            contract.functions.iter().map(|f| &f.name).collect::<Vec<_>>()
        );

        // Instrumentation, counted rather than sampled.
        let instrumented = contract
            .functions
            .iter()
            .filter(|f| f.debug_symbols.debug_infos.iter().any(|d| !d.variables.is_empty()))
            .count();
        assert!(
            instrumented >= 25,
            "the contract's functions carry source-level variables; {instrumented} of {} did",
            contract.functions.len()
        );

        // `force_brillig` took effect on every function — the tracer steps unconstrained
        // bytecode, so this is what makes the artifact steppable in principle.
        let with_brillig =
            contract.functions.iter().filter(|f| !f.bytecode.unconstrained_functions.is_empty()).count();
        assert_eq!(
            with_brillig,
            contract.functions.len(),
            "every function carries unconstrained bytecode under force_brillig"
        );

        // THE DIRECT ANSWER to "is this tracer-consumable?": the debug info maps brillig
        // opcodes to source locations, in quantity. An uninstrumented artifact has none,
        // which is why it traces to one event and no steps.
        let located: usize = contract
            .functions
            .iter()
            .flat_map(|f| f.debug_symbols.debug_infos.iter())
            .flat_map(|d| d.brillig_locations.values())
            .map(|inner| inner.len())
            .sum();
        println!(
            "SimpleToken: {} functions, {instrumented} instrumented, {located} located brillig opcodes",
            contract.functions.len()
        );
        assert!(
            located > 10_000,
            "the artifact must map brillig opcodes to source locations in quantity; \
             got {located}. Near-zero here is the uninstrumented signature."
        );
    }

    /// A contract compiled against the real vendored `aztec-nr` closure is STEPPED, and
    /// the steps land in the contract's own source.
    ///
    /// Why this contract and not `SimpleToken`'s own entrypoints: every `#[aztec]`
    /// entrypoint begins by calling an AVM oracle, and the tracer's
    /// `DefaultDebugForeignCallExecutor` has no host for Aztec's oracles, so execution
    /// halts at the first one having emitted only the entry step. That is a REAL and
    /// separate limitation — an oracle host, not a compiler mode — and it is asserted as
    /// such in `the_aztec_entrypoints_halt_at_the_first_oracle` below rather than left as
    /// a disappointing number here.
    ///
    /// What this arm establishes is the thing the mode fix is responsible for: a
    /// `type = "contract"` package, resolved across the same 420-file Aztec dependency
    /// closure and compiled through `compile_contract` with instrumentation, executes and
    /// produces source-level steps in the contract's own file.
    #[test]
    #[ignore = "needs a vendored aztec-nr tree; see scripts/aztec_contract_is_steppable.sh"]
    fn a_contract_on_the_real_aztec_tree_steps_through_its_own_source() {
        use codetracer_trace_types::TraceLowLevelEvent;
        use noirc_artifacts::contract::ContractArtifact;
        use noirc_artifacts::program::ProgramArtifact;

        let (mut files, _) = vendored_aztec_tree();

        // A contract package added to the SAME tree, depending on two packages that are
        // really in the vendored Aztec closure — `types` is aztec's `protocol_types` and
        // `poseidon` is the git dependency the vendoring had to materialise. So the
        // resolve walks the real graph, not a toy one.
        assert!(
            files.contains_key("vendor/types/Nargo.toml") && files.contains_key("vendor/poseidon/Nargo.toml"),
            "this arm depends on the vendored `types` and `poseidon` packages being present"
        );
        files.insert(
            "stepping/Nargo.toml".into(),
            "[package]\nname = \"stepping\"\ntype = \"contract\"\n\n[dependencies]\n\
             types = { path = \"../vendor/types\" }\n\
             poseidon = { path = \"../vendor/poseidon\" }\n"
                .into(),
        );
        files.insert(
            "stepping/src/main.nr".into(),
            "use dep::types::address::AztecAddress;\n\
             use dep::types::traits::{FromField, ToField};\n\
             \n\
             contract Stepping {\n\
             \x20   use crate::AztecAddress;\n\
             \x20   use crate::{FromField, ToField};\n\
             \n\
             \x20   // Real `protocol_types` code, on values small enough that the tracer\n\
             \x20   // can record them: `noir_tracer` panics recording a field element\n\
             \x20   // wider than i128, which a Poseidon digest always is.\n\
             \x20   fn digest(owner: Field, amount: Field) -> pub Field {\n\
             \x20       let address = AztecAddress::from_field(owner);\n\
             \x20       let base = address.to_field();\n\
             \x20       let scaled = amount * 3;\n\
             \x20       let mixed = base + scaled;\n\
             \x20       let doubled = mixed + mixed;\n\
             \x20       let shifted = doubled + 5;\n\
             \x20       let folded = shifted - base;\n\
             \x20       folded\n\
             \x20   }\n\
             }\n"
                .into(),
        );

        let response = run_request(&VfsRequest {
            files,
            package_dir: "stepping".into(),
            mode: "contract-debug".into(),
        });
        assert!(
            response.ok,
            "the contract must compile against the real aztec tree; got {:?} / {:?}",
            response.message,
            response.diagnostics.iter().take(5).map(|d| (&d.file, &d.message)).collect::<Vec<_>>()
        );

        // The resolve really did span the Aztec closure, asserted rather than assumed.
        let plan = response.plan.as_ref().expect("a plan comes back");
        assert!(
            plan.packages.len() >= 5,
            "the contract resolves across the vendored Aztec packages; got {}",
            plan.packages.len()
        );

        let contract: ContractArtifact =
            serde_json::from_value(response.artifact.expect("an artifact comes back"))
                .expect("it deserializes as a ContractArtifact");
        assert_eq!(contract.name, "Stepping");
        assert_eq!(contract.functions.len(), 1, "the contract has one entrypoint");

        let compiled = contract
            .function_as_compiled_program("digest")
            .expect("the contract exposes `digest`");
        let artifact_json =
            serde_json::to_string(&ProgramArtifact::from(compiled)).expect("serializes");
        let trace = noir_tracer_wasm::trace_artifact(
            &artifact_json,
            "{\"owner\":\"11\",\"amount\":\"7\"}",
            true,
        )
        .expect("the contract traces");

        let steps: Vec<_> = trace
            .events
            .iter()
            .filter_map(|e| match e {
                TraceLowLevelEvent::Step(s) => Some(s),
                _ => None,
            })
            .collect();
        println!(
            "Stepping::digest on the real aztec tree: {} source-level steps in {} events \
             across {} packages",
            steps.len(),
            trace.events.len(),
            plan.packages.len()
        );

        // THE COUNT, ASSERTED. Well above the "one entry step and nothing else" signature
        // of an artifact that did not execute or was not instrumented.
        assert!(
            steps.len() >= 8,
            "a contract on the real Aztec tree must trace to a substantive number of \
             source-level steps; got {} steps in {} events. One is the entry step alone.",
            steps.len(),
            trace.events.len()
        );

        // …and they are steps through the CONTRACT'S OWN source, not incidental steps in
        // a dependency. The count of those is asserted too, so "some step was in the file"
        // cannot be satisfied by the single entry step.
        let own: Vec<i64> = steps
            .iter()
            .filter(|s| {
                trace.paths.get(s.path_id.0).is_some_and(|p| {
                    p.to_string_lossy().as_ref() == "stepping/src/main.nr"
                })
            })
            .map(|s| s.line.0)
            .collect();
        assert!(
            own.len() >= 6,
            "most steps must be in the contract's own source; {} of {} were. Paths seen: {:?}",
            own.len(),
            steps.len(),
            steps
                .iter()
                .filter_map(|s| trace.paths.get(s.path_id.0))
                .map(|p| p.to_string_lossy().to_string())
                .collect::<std::collections::BTreeSet<_>>()
        );

        // Distinct LINES, which is what "steppable" means to a user: a debugger that
        // reports the same line eight times has not stepped through anything.
        let distinct: std::collections::BTreeSet<i64> = own.iter().copied().collect();
        println!("  {} steps in stepping/src/main.nr over {} distinct lines", own.len(), distinct.len());
        assert!(
            distinct.len() >= 5,
            "the steps must advance through the source; {} distinct lines out of {} steps: {:?}",
            distinct.len(),
            own.len(),
            own
        );
    }

    /// The Aztec entrypoints halt at their first oracle, and this pins WHY so the number
    /// above is not mistaken for a compiler defect.
    ///
    /// If an Aztec oracle host lands, this test fails — deliberately. It is a record of a
    /// present boundary, not a claim that the boundary is correct.
    #[test]
    #[ignore = "needs a vendored aztec-nr tree; see scripts/aztec_contract_is_steppable.sh"]
    fn the_aztec_entrypoints_halt_at_the_first_oracle() {
        use codetracer_trace_types::TraceLowLevelEvent;
        use noirc_artifacts::contract::ContractArtifact;
        use noirc_artifacts::program::ProgramArtifact;

        let (files, package_dir) = vendored_aztec_tree();
        let response =
            run_request(&VfsRequest { files, package_dir, mode: "contract-debug".into() });
        assert!(response.ok, "the contract compiles; got {:?}", response.message);
        let contract: ContractArtifact =
            serde_json::from_value(response.artifact.expect("an artifact")).expect("deserializes");

        let mut attempted = 0;
        let mut halted_in_oracle = 0;
        let mut best = 0usize;
        for function in &contract.functions {
            attempted += 1;
            let compiled = contract.function_as_compiled_program(&function.name).expect("present");
            let json = serde_json::to_string(&ProgramArtifact::from(compiled)).expect("serializes");
            let inputs = zeroed_inputs_json(&function.abi);
            let Ok(trace) = noir_tracer_wasm::trace_artifact(&json, &inputs, true) else {
                continue;
            };
            let steps: Vec<_> = trace
                .events
                .iter()
                .filter_map(|e| match e {
                    TraceLowLevelEvent::Step(s) => Some(s),
                    _ => None,
                })
                .collect();
            best = best.max(steps.len());
            // The single step it does emit is the tracer's entry step, and it lands in
            // aztec-nr's own oracle/dispatch machinery rather than in contract source.
            if steps.len() == 1
                && trace.paths.get(steps[0].path_id.0).is_some_and(|p| {
                    let p = p.to_string_lossy();
                    p.contains("oracle") || p.contains("dispatch")
                })
            {
                halted_in_oracle += 1;
            }
        }

        assert_eq!(attempted, 27, "every function of SimpleToken was attempted");
        assert_eq!(
            halted_in_oracle, attempted,
            "all {attempted} Aztec entrypoints halt at their first oracle having emitted \
             only the entry step; {halted_in_oracle} did. If this number has DROPPED, an \
             oracle host has landed and this test should be replaced by a real step-count \
             assertion over SimpleToken itself."
        );
        assert_eq!(
            best, 1,
            "…so the best step count over SimpleToken's own entrypoints is the entry step \
             alone. This is an oracle-host gap, NOT a compilation or instrumentation gap: \
             `a_real_aztec_contract_compiles_for_debugging_and_is_instrumented` asserts \
             the artifact carries >10,000 located brillig opcodes."
        );
        println!(
            "SimpleToken: {halted_in_oracle}/{attempted} entrypoints halt at the first \
             oracle (best step count {best})"
        );
    }

    /// An all-zero input map for an ABI, so a function can be executed without
    /// knowing what its parameters mean.
    #[cfg(test)]
    fn zeroed_inputs_json(abi: &noirc_abi::Abi) -> String {
        use noirc_abi::AbiType;
        fn zero(t: &AbiType) -> serde_json::Value {
            match t {
                AbiType::Field | AbiType::Integer { .. } => serde_json::json!("0"),
                AbiType::Boolean => serde_json::json!(false),
                AbiType::String { length } => serde_json::json!("0".repeat(*length as usize)),
                AbiType::Array { length, typ } => {
                    serde_json::Value::Array((0..*length).map(|_| zero(typ)).collect())
                }
                AbiType::Tuple { fields } => {
                    serde_json::Value::Array(fields.iter().map(zero).collect())
                }
                AbiType::Struct { fields, .. } => serde_json::Value::Object(
                    fields.iter().map(|(n, t)| (n.clone(), zero(t))).collect(),
                ),
            }
        }
        let map: serde_json::Map<String, serde_json::Value> =
            abi.parameters.iter().map(|p| (p.name.clone(), zero(&p.typ))).collect();
        serde_json::to_string(&serde_json::Value::Object(map)).expect("a JSON input map")
    }
}
