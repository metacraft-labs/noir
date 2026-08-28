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
    CompiledFromVfs, PositionedDiagnostic, ResolvedProgram, VfsError, compile_resolved,
    resolve_vfs,
};

/// What a host asks for.
#[derive(Deserialize)]
pub struct VfsRequest {
    /// The whole virtual filesystem: `path -> contents`.
    pub files: BTreeMap<String, String>,
    /// The directory holding the entry package's `Nargo.toml`.
    #[serde(default)]
    pub package_dir: String,
    /// `resolve`, `program` or `contract`. Defaults to `program`.
    #[serde(default = "default_mode")]
    pub mode: String,
}

fn default_mode() -> String {
    "program".to_string()
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
        }
    }
}

fn to_tree(files: &BTreeMap<String, String>) -> BTreeMap<PathBuf, String> {
    files.iter().map(|(p, s)| (PathBuf::from(p), s.clone())).collect()
}

/// Resolve and (optionally) compile. The one code path both hosts use.
pub fn run_request(request: &VfsRequest) -> VfsResponse {
    let tree = to_tree(&request.files);

    let plan = match resolve_vfs(&tree, &request.package_dir) {
        Ok(plan) => plan,
        Err(err) => return VfsResponse::refused("resolve", &err),
    };

    if request.mode == "resolve" {
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
        };
    }

    let as_contract = request.mode == "contract";
    match compile_resolved(&plan, &tree, as_contract) {
        Ok((compiled, warnings)) => {
            let artifact = match compiled {
                CompiledFromVfs::Program(program) => serde_json::to_value(&*program).ok(),
                CompiledFromVfs::Contract(contract) => serde_json::to_value(&*contract).ok(),
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
    let files: BTreeMap<String, String> = file_source_map
        .0
        .into_iter()
        .map(|(p, s)| (p.to_string_lossy().to_string(), s))
        .collect();

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
            Err(_) => {
                "{\"ok\":false,\"stage\":\"request\",\"kind\":\"bad-request\",\
                 \"message\":\"the request is not valid UTF-8\"}"
                    .to_string()
            }
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

    const APP_MANIFEST: &str =
        "[package]\nname = \"app\"\ntype = \"bin\"\n\n[dependencies]\nutil = { path = \"../util\" }\n";

    fn request(mode: &str, extra: &[(&str, &str)]) -> VfsRequest {
        let mut files: BTreeMap<String, String> = BTreeMap::new();
        files.insert("app/Nargo.toml".into(), APP_MANIFEST.into());
        files.insert(
            "app/src/main.nr".into(),
            "fn main(x: Field) -> pub Field { util::twice(x) }\n".into(),
        );
        files.insert("util/Nargo.toml".into(), "[package]\nname = \"util\"\ntype = \"lib\"\n".into());
        files.insert(
            "util/src/lib.nr".into(),
            "pub fn twice(x: Field) -> Field { x + x }\n".into(),
        );
        for (path, source) in extra {
            files.insert((*path).to_string(), (*source).to_string());
        }
        VfsRequest { files, package_dir: "app".into(), mode: mode.into() }
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
}
