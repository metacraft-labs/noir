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

/// JS entry point. Returns the trace as a JSON string.
#[cfg(target_arch = "wasm32")]
#[wasm_bindgen::prelude::wasm_bindgen]
pub fn trace(artifact_json: &str, inputs: &str, inputs_are_json: bool) -> Result<String, String> {
    console_error_panic_hook::set_once();
    let trace =
        trace_artifact(artifact_json, inputs, inputs_are_json).map_err(|e| e.to_string())?;
    serde_json::to_string(&trace).map_err(|e| e.to_string())
}
