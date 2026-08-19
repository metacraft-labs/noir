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

pub mod memory_sink;
pub use memory_sink::{Capabilities, MemorySink, MemoryTrace};

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
}

impl std::fmt::Display for TraceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TraceError::Artifact(m) => write!(f, "could not read the program artifact: {m}"),
            TraceError::Inputs(m) => write!(f, "could not parse the program inputs: {m}"),
            TraceError::Abi(m) => write!(f, "could not encode the inputs against the ABI: {m}"),
            TraceError::Execution(m) => write!(f, "tracing failed: {m}"),
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

/// Serialize a trace of `artifact_json` / `inputs` to JSON.
fn trace_to_json(
    artifact_json: &str,
    inputs: &str,
    inputs_are_json: bool,
) -> Result<String, String> {
    let trace = trace_artifact(artifact_json, inputs, inputs_are_json).map_err(|e| e.to_string())?;
    serde_json::to_string(&trace).map_err(|e| e.to_string())
}

/// JS entry point (the `js` feature). Returns the trace as a JSON string.
#[cfg(all(target_arch = "wasm32", feature = "js"))]
#[wasm_bindgen::prelude::wasm_bindgen]
pub fn trace(artifact_json: &str, inputs: &str, inputs_are_json: bool) -> Result<String, String> {
    console_error_panic_hook::set_once();
    trace_to_json(artifact_json, inputs, inputs_are_json)
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

        let (bytes, is_error) = match result {
            Ok(json) => (json.into_bytes(), false),
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
