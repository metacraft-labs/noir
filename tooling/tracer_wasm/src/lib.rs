//! Platform-agnostic shell over [`noir_tracer`], plus a `wasm-bindgen` binding.
//!
//! The whole point of this crate is that [`trace_artifact`] below contains **no
//! reachable `std::fs`, `std::env`, `std::process` or networking**: a compiled
//! Noir program arrives as JSON, its inputs arrive as a string, and the
//! execution trace leaves as an in-memory event stream. It builds for
//! `wasm32-unknown-unknown`, and the identical code path is exercised natively
//! by this crate's tests.
//!
//! Build / check it with (note the `cd` -- the crate's own `.cargo/config.toml`
//! carries `--cfg getrandom_backend="wasm_js"`, which cargo only picks up from
//! the invocation directory):
//!
//! ```text
//! cd tooling/tracer_wasm && cargo build --release
//! ```

pub mod compile;
pub mod ctfs_sink;
pub mod memory_sink;
pub use compile::{DEFAULT_ENTRY_POINT, compile_source};
pub use ctfs_sink::{CtfsSink, TeeSink};
pub use memory_sink::{Capabilities, MemorySink, MemoryTrace};

use std::collections::BTreeMap;

use acvm::FieldElement;
use bn254_blackbox_solver::Bn254BlackBoxSolver;
use noir_tracer::TraceOptions;
use noirc_abi::InputMap;
use noirc_abi::input_parser::Format;
use noirc_artifacts::debug::DebugArtifact;
use noirc_artifacts::program::{CompiledProgram, ProgramArtifact};

// These are dependencies only so that their wasm-enabling features get turned
// on for the whole build graph; nothing here calls them. Same idiom as
// `compiler/wasm` and `acvm-repo/acvm_js`.
#[cfg(all(target_arch = "wasm32", feature = "js"))]
use console_error_panic_hook as _;
#[cfg(target_arch = "wasm32")]
use getrandom as _;
#[cfg(target_arch = "wasm32")]
use getrandom_v2 as _;
#[cfg(target_arch = "wasm32")]
use getrandom_v4 as _;
#[cfg(target_arch = "wasm32")]
use uuid as _;

#[derive(Debug)]
pub enum TraceError {
    Artifact(String),
    Inputs(String),
    Abi(String),
    Execution(String),
    Compilation(String),
    Request(String),
}

impl std::fmt::Display for TraceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TraceError::Artifact(m) => write!(f, "could not read the program artifact: {m}"),
            TraceError::Inputs(m) => write!(f, "could not parse the program inputs: {m}"),
            TraceError::Abi(m) => write!(f, "could not encode the inputs against the ABI: {m}"),
            TraceError::Execution(m) => write!(f, "tracing failed: {m}"),
            TraceError::Compilation(m) => write!(f, "{m}"),
            TraceError::Request(m) => write!(f, "could not read the trace request: {m}"),
        }
    }
}

impl std::error::Error for TraceError {}

/// Trace an already-compiled program against an already-parsed input map.
///
/// This is the platform-agnostic core: `(CompiledProgram, InputMap,
/// &mut dyn TraceSink) -> Result<()>`, with the former ambient
/// `current_dir()` lifted into [`TraceOptions`].
pub fn trace_compiled_program(
    program: &CompiledProgram,
    inputs: &InputMap,
    options: &TraceOptions,
    sink: &mut dyn noir_tracer::TraceSink,
) -> Result<(), TraceError> {
    let initial_witness =
        program.abi.encode(inputs, None).map_err(|e| TraceError::Abi(e.to_string()))?;

    let debug_artifact =
        DebugArtifact { debug_symbols: program.debug.clone(), file_map: program.file_map.clone() };

    noir_tracer::trace_circuit(
        &Bn254BlackBoxSolver,
        &program.program.functions,
        &debug_artifact,
        initial_witness,
        &program.program.unconstrained_functions,
        &program.abi.error_types,
        options,
        sink,
    )
    .map_err(|e: nargo::NargoError<FieldElement>| TraceError::Execution(e.to_string()))
}

/// Trace a program given its serialized artifact and its raw inputs.
///
/// `artifact_json` is a `ProgramArtifact` as `nargo compile` writes it.
/// `inputs` is the text of a `Prover.toml` (or the equivalent JSON).
pub fn trace_artifact(
    artifact_json: &str,
    inputs: &str,
    inputs_are_json: bool,
) -> Result<MemoryTrace, TraceError> {
    let artifact: ProgramArtifact =
        serde_json::from_str(artifact_json).map_err(|e| TraceError::Artifact(e.to_string()))?;
    let program: CompiledProgram = artifact.into();

    let format = if inputs_are_json { Format::Json } else { Format::Toml };
    let input_map =
        format.parse(inputs, &program.abi).map_err(|e| TraceError::Inputs(e.to_string()))?;

    let mut sink = MemorySink::new();
    // No workdir: there is no process working directory to strip against, so
    // paths are registered exactly as the compiler recorded them.
    let options = TraceOptions::default();

    noir_tracer::tracer_glue::begin_trace(&mut sink, "", "trace", None);
    trace_compiled_program(&program, &input_map, &options, &mut sink)?;
    noir_tracer::tracer_glue::finish_trace(&mut sink)
        .map_err(|e| TraceError::Execution(e.to_string()))?;

    Ok(sink.into_trace())
}

/// Everything a host must supply to go from Noir source to a trace.
///
/// This crosses the wasm boundary as a single JSON object rather than as a
/// widening list of `(ptr, len)` pairs, so that adding a knob does not change
/// the C ABI.
#[derive(serde::Deserialize)]
pub struct TraceRequest {
    /// Path-to-source for every file in the program. Relative paths; these are
    /// what the trace reports as the program's source locations.
    pub files: BTreeMap<String, String>,
    /// Which of `files` is the crate root. Defaults to [`DEFAULT_ENTRY_POINT`].
    #[serde(default = "default_entry_point")]
    pub entry_point: String,
    /// The text of a `Prover.toml` (or the equivalent JSON).
    pub inputs: String,
    #[serde(default)]
    pub inputs_are_json: bool,
    /// Program name recorded in the trace.
    #[serde(default = "default_package_name")]
    pub package: String,
    /// The `recording_id` to stamp into the container's metadata.
    ///
    /// `wasm32-unknown-unknown` has neither a wall clock nor a CSPRNG, so the
    /// writer cannot mint a UUIDv7 itself; a browser host should pass one made
    /// from `Date.now()` + `crypto.getRandomValues`. Omitting it leaves the
    /// writer's deterministic placeholder, which is well-formed but identical
    /// for every recording.
    #[serde(default)]
    pub recording_id: Option<String>,
}

fn default_entry_point() -> String {
    DEFAULT_ENTRY_POINT.to_string()
}

fn default_package_name() -> String {
    "trace".to_string()
}

/// Compile Noir **source** and trace it -- the whole pipeline, in memory.
///
/// This is [`trace_artifact`] with the missing front half attached: no
/// previously-compiled artifact is required, so a host needs nothing but the
/// program text and its inputs.
pub fn trace_source(request: &TraceRequest) -> Result<MemoryTrace, TraceError> {
    let program = compile::compile_source(&request.files, &request.entry_point)
        .map_err(TraceError::Compilation)?;

    let format = if request.inputs_are_json { Format::Json } else { Format::Toml };
    let input_map = format
        .parse(&request.inputs, &program.abi)
        .map_err(|e| TraceError::Inputs(e.to_string()))?;

    let mut sink = MemorySink::new();
    let options = TraceOptions::default();

    noir_tracer::tracer_glue::begin_trace(&mut sink, "", &request.package, None);
    trace_compiled_program(&program, &input_map, &options, &mut sink)?;
    noir_tracer::tracer_glue::finish_trace(&mut sink)
        .map_err(|e| TraceError::Execution(e.to_string()))?;

    Ok(sink.into_trace())
}

/// What came back alongside the container, so a host can say plainly what it
/// is holding.
#[derive(Debug, serde::Serialize)]
pub struct ContainerInfo {
    /// Byte length of the `.ct` container.
    pub bytes: usize,
    /// Whether the container carries column-aware steps. Always `false` for
    /// the pure-Rust CTFS writer -- see [`ctfs_sink`].
    pub column_aware: bool,
    /// Whether column-aware steps were **requested** and dropped. The Noir
    /// recorder always requests them, so this is the honest signal that the
    /// container is weaker than the one `nargo trace` writes.
    pub dropped_column_awareness: bool,
    /// The `recording_id` stamped into the container, if the host supplied one.
    pub recording_id: Option<String>,
}

/// A trace plus a description of the container built from it.
///
/// `trace` is flattened, so the JSON is a superset of what
/// [`trace_source_to_json`] returns -- existing hosts keep reading `events` /
/// `paths` / `capabilities` at the top level.
#[derive(Debug, serde::Serialize)]
pub struct TracedContainer {
    #[serde(flatten)]
    pub trace: MemoryTrace,
    pub container: ContainerInfo,
}

/// Compile Noir **source**, trace it, and build a `.ct` CTFS container from
/// the trace -- the whole pipeline, in memory, with no filesystem anywhere.
///
/// Returns the container bytes and the same event stream
/// [`trace_source`] returns, produced in a single pass (see
/// [`ctfs_sink::TeeSink`]).
pub fn trace_source_to_container(
    request: &TraceRequest,
) -> Result<(Vec<u8>, TracedContainer), TraceError> {
    let program = compile::compile_source(&request.files, &request.entry_point)
        .map_err(TraceError::Compilation)?;

    let format = if request.inputs_are_json { Format::Json } else { Format::Toml };
    let input_map = format
        .parse(&request.inputs, &program.abi)
        .map_err(|e| TraceError::Inputs(e.to_string()))?;

    let mut sink = TeeSink::new(&request.package, &[], request.recording_id.as_deref());
    let options = TraceOptions::default();

    noir_tracer::tracer_glue::begin_trace(&mut sink, "", &request.package, None);
    trace_compiled_program(&program, &input_map, &options, &mut sink)?;
    noir_tracer::tracer_glue::finish_trace(&mut sink)
        .map_err(|e| TraceError::Execution(e.to_string()))?;

    let dropped_column_awareness = sink.ctfs.dropped_column_awareness();
    let bytes = sink
        .ctfs
        .take_container_bytes()
        .ok_or_else(|| TraceError::Execution("the in-memory CTFS writer produced no container".to_string()))?;

    let info = ContainerInfo {
        bytes: bytes.len(),
        column_aware: false,
        dropped_column_awareness,
        recording_id: request.recording_id.clone(),
    };
    Ok((bytes, TracedContainer { trace: sink.memory.into_trace(), container: info }))
}

/// Build a `.ct` container from a [`TraceRequest`] given as JSON, and frame it
/// with its summary for a host that reads one byte buffer.
///
/// Layout: `[u32 LE summary_len][summary JSON, UTF-8][.ct container]`. The
/// summary is a [`TracedContainer`]; the container is the rest of the buffer.
pub fn trace_source_to_container_envelope(request_json: &str) -> Result<Vec<u8>, String> {
    let request: TraceRequest = serde_json::from_str(request_json)
        .map_err(|e| TraceError::Request(e.to_string()).to_string())?;
    let (container, summary) = trace_source_to_container(&request).map_err(|e| e.to_string())?;
    let summary_json = serde_json::to_vec(&summary).map_err(|e| e.to_string())?;

    let mut out = Vec::with_capacity(4 + summary_json.len() + container.len());
    out.extend_from_slice(&(summary_json.len() as u32).to_le_bytes());
    out.extend_from_slice(&summary_json);
    out.extend_from_slice(&container);
    Ok(out)
}

/// Serialize a trace of a [`TraceRequest`] (given as JSON) to JSON.
///
/// Public because it is the whole of what the wasm entry points do; a native
/// host that wants the same string-in/string-out shape can call it directly.
pub fn trace_source_to_json(request_json: &str) -> Result<String, String> {
    let request: TraceRequest = serde_json::from_str(request_json)
        .map_err(|e| TraceError::Request(e.to_string()).to_string())?;
    let trace = trace_source(&request).map_err(|e| e.to_string())?;
    serde_json::to_string(&trace).map_err(|e| e.to_string())
}

/// Serialize a trace of `artifact_json` / `inputs` to JSON.
pub fn trace_to_json(
    artifact_json: &str,
    inputs: &str,
    inputs_are_json: bool,
) -> Result<String, String> {
    let trace =
        trace_artifact(artifact_json, inputs, inputs_are_json).map_err(|e| e.to_string())?;
    serde_json::to_string(&trace).map_err(|e| e.to_string())
}

/// JS entry point (the `js` feature). Returns the trace as a JSON string.
#[cfg(all(target_arch = "wasm32", feature = "js"))]
#[wasm_bindgen::prelude::wasm_bindgen]
pub fn trace(artifact_json: &str, inputs: &str, inputs_are_json: bool) -> Result<String, String> {
    console_error_panic_hook::set_once();
    trace_to_json(artifact_json, inputs, inputs_are_json)
}

/// JS entry point taking Noir **source**. `request_json` is a [`TraceRequest`].
#[cfg(all(target_arch = "wasm32", feature = "js"))]
#[wasm_bindgen::prelude::wasm_bindgen]
pub fn trace_source_json(request_json: &str) -> Result<String, String> {
    console_error_panic_hook::set_once();
    trace_source_to_json(request_json)
}

/// The bare-engine entry points.
///
/// Built without the `js` feature the module has **no imports at all**, so it
/// instantiates in any WebAssembly engine -- `wasmtime`, or
/// `WebAssembly.instantiate(bytes)` with no import object. Strings cross the
/// boundary as `(ptr, len)` pairs in linear memory.
///
/// Usage: `ct_alloc` two buffers, copy the artifact JSON and the inputs into
/// them, call `ct_trace`, then read `ct_result_len` bytes from the returned
/// pointer and `ct_free` everything.
#[cfg(target_arch = "wasm32")]
pub mod abi {
    use std::alloc::{Layout, alloc, dealloc};

    /// Reserve `len` bytes in the module's linear memory.
    ///
    /// # Safety
    /// The caller must eventually pass the returned pointer and the same `len`
    /// to [`ct_free`].
    #[unsafe(no_mangle)]
    pub unsafe extern "C" fn ct_alloc(len: usize) -> *mut u8 {
        if len == 0 {
            return std::ptr::null_mut();
        }
        let layout = Layout::from_size_align(len, 1).expect("valid layout");
        unsafe { alloc(layout) }
    }

    /// Release a buffer previously returned by [`ct_alloc`] or [`ct_trace`].
    ///
    /// # Safety
    /// `ptr`/`len` must come from one of those calls and not be used again.
    #[unsafe(no_mangle)]
    pub unsafe extern "C" fn ct_free(ptr: *mut u8, len: usize) {
        if ptr.is_null() || len == 0 {
            return;
        }
        let layout = Layout::from_size_align(len, 1).expect("valid layout");
        unsafe { dealloc(ptr, layout) };
    }

    /// Byte length of the buffer the last [`ct_trace`] call returned.
    #[unsafe(no_mangle)]
    pub extern "C" fn ct_result_len() -> usize {
        RESULT_LEN.with(|c| c.get())
    }

    /// Non-zero if the last [`ct_trace`] call returned an error message rather
    /// than a trace.
    #[unsafe(no_mangle)]
    pub extern "C" fn ct_result_is_error() -> u32 {
        RESULT_IS_ERROR.with(|c| u32::from(c.get()))
    }

    thread_local! {
        static RESULT_LEN: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
        static RESULT_IS_ERROR: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    }

    /// Trace a program. Returns a pointer to UTF-8 bytes; the length is
    /// [`ct_result_len`] and [`ct_result_is_error`] says which of the two shapes
    /// (trace JSON / error message) it holds.
    ///
    /// # Safety
    /// Both `(ptr, len)` pairs must describe initialized UTF-8 buffers that stay
    /// valid for the duration of the call.
    #[unsafe(no_mangle)]
    pub unsafe extern "C" fn ct_trace(
        artifact_ptr: *const u8,
        artifact_len: usize,
        inputs_ptr: *const u8,
        inputs_len: usize,
        inputs_are_json: u32,
    ) -> *mut u8 {
        let artifact = unsafe { std::slice::from_raw_parts(artifact_ptr, artifact_len) };
        let inputs = unsafe { std::slice::from_raw_parts(inputs_ptr, inputs_len) };

        let result = match (std::str::from_utf8(artifact), std::str::from_utf8(inputs)) {
            (Ok(a), Ok(i)) => super::trace_to_json(a, i, inputs_are_json != 0),
            _ => Err("inputs are not valid UTF-8".to_string()),
        };

        publish(result)
    }

    /// Compile Noir **source** and trace it. `(ptr, len)` is a JSON
    /// [`super::TraceRequest`]; the result follows the same convention as
    /// [`ct_trace`].
    ///
    /// # Safety
    /// `(ptr, len)` must describe an initialized UTF-8 buffer that stays valid
    /// for the duration of the call.
    #[unsafe(no_mangle)]
    pub unsafe extern "C" fn ct_trace_source(
        request_ptr: *const u8,
        request_len: usize,
    ) -> *mut u8 {
        let request = unsafe { std::slice::from_raw_parts(request_ptr, request_len) };

        let result = match std::str::from_utf8(request) {
            Ok(json) => super::trace_source_to_json(json),
            Err(_) => Err("the request is not valid UTF-8".to_string()),
        };

        publish(result)
    }

    /// Compile Noir **source**, trace it, and build a `.ct` CTFS container.
    ///
    /// `(ptr, len)` is a JSON [`super::TraceRequest`]. On success the result
    /// buffer is `[u32 LE summary_len][summary JSON][.ct container]`; on
    /// failure it is a UTF-8 message and [`ct_result_is_error`] is non-zero.
    /// Lengths and freeing follow the same convention as [`ct_trace`].
    ///
    /// # Safety
    /// `(ptr, len)` must describe an initialized UTF-8 buffer that stays valid
    /// for the duration of the call.
    #[unsafe(no_mangle)]
    pub unsafe extern "C" fn ct_trace_source_container(
        request_ptr: *const u8,
        request_len: usize,
    ) -> *mut u8 {
        let request = unsafe { std::slice::from_raw_parts(request_ptr, request_len) };

        let result = match std::str::from_utf8(request) {
            Ok(json) => super::trace_source_to_container_envelope(json),
            Err(_) => Err("the request is not valid UTF-8".to_string()),
        };

        publish_bytes(result)
    }

    /// Hand a result to the host: record its length and error flag, then leak
    /// the buffer for the host to read and `ct_free`.
    fn publish(result: Result<String, String>) -> *mut u8 {
        publish_bytes(result.map(String::into_bytes))
    }

    /// [`publish`] for a result that is not necessarily text -- a `.ct`
    /// container is arbitrary bytes.
    fn publish_bytes(result: Result<Vec<u8>, String>) -> *mut u8 {
        let (bytes, is_error) = match result {
            Ok(payload) => (payload, false),
            Err(message) => (message.into_bytes(), true),
        };

        RESULT_LEN.with(|c| c.set(bytes.len()));
        RESULT_IS_ERROR.with(|c| c.set(is_error));

        let mut boxed = bytes.into_boxed_slice();
        let ptr = boxed.as_mut_ptr();
        std::mem::forget(boxed);
        ptr
    }
}
