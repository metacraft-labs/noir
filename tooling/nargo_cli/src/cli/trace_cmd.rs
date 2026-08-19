use bn254_blackbox_solver::Bn254BlackBoxSolver;
use clap::Args;

use nargo::ops::debug::compile_options_for_debugging;
use nargo::package::Package;
use nargo::{constants::PROVER_INPUT_FILE, ops::debug::compile_bin_package_for_debugging};
use nargo_toml::{PackageSelection, get_package_manifest, resolve_workspace_from_toml};
use noir_tracer::TraceOptions;
use noir_tracer::sink::NimWriterSink;
use noir_tracer::tracer_glue::begin_trace;
use noir_tracer::tracer_glue::finish_trace;
use noirc_abi::InputMap;
use noirc_abi::input_parser::Format;
use noirc_artifacts::debug::DebugArtifact;
use noirc_artifacts::program::CompiledProgram;
use noirc_driver::{CompileOptions, NOIR_ARTIFACT_VERSION_STRING};
use noirc_frontend::graph::CrateName;

use super::fs::inputs::read_inputs_from_file;
use crate::errors::CliError;

use codetracer_trace_writer::{create_trace_writer, TraceEventsFileFormat};

use super::NargoConfig;

/// Compile the program and record its execution trace into a CTFS `.ct`
/// container.
///
/// CTFS-only.  The previous `--trace-format binary|binaryv0|json` selector
/// was removed in the 2026-05 convention compliance pass — codetracer's
/// db-backend now accepts only the single-file `.ct` bundle for
/// materialized traces.  See
/// `codetracer-specs/Trace-Files/CTFS-Migration-Guide.md`.
#[derive(Debug, Clone, Args)]
pub(crate) struct TraceCommand {
    /// The name of the toml file which contains the inputs for the prover
    #[clap(long, short, default_value = PROVER_INPUT_FILE)]
    prover_name: String,

    /// The name of the package to execute
    #[clap(long)]
    package: Option<CrateName>,

    #[clap(flatten)]
    compile_options: CompileOptions,

    /// Directory where to store the `<package>.ct` CTFS container.
    #[clap(long, short)]
    out_dir: String,
}

pub(crate) fn run(args: TraceCommand, config: NargoConfig) -> Result<(), CliError> {
    let acir_mode = false;
    let skip_instrumentation = false;

    let toml_path = get_package_manifest(&config.program_dir)?;
    let selection = args.package.map_or(PackageSelection::DefaultOrAll, PackageSelection::Selected);
    let workspace = resolve_workspace_from_toml(
        &toml_path,
        selection,
        Some(NOIR_ARTIFACT_VERSION_STRING.to_string()),
    )?;

    let Some(package) = workspace.into_iter().find(|p| p.is_binary()) else {
        println!(
            "No matching binary packages found in workspace. Only binary packages can be debugged."
        );
        return Ok(());
    };

    let compile_options = compile_options_for_debugging(
        acir_mode,
        skip_instrumentation,
        args.compile_options.clone(),
    );

    let compiled_program =
        compile_bin_package_for_debugging(&workspace, package, &compile_options)?;

    trace_program_and_decode(
        compiled_program,
        package,
        &args.prover_name,
        &args.out_dir,
        args.compile_options.pedantic_solving,
    )
}

fn trace_program_and_decode(
    program: CompiledProgram,
    package: &Package,
    prover_name: &str,
    out_dir: &str,
    pedantic_solving: bool,
) -> Result<(), CliError> {
    // Parse the initial witness values from Prover.toml
    let (inputs_map, _) =
        read_inputs_from_file(&package.root_dir, prover_name, Format::Toml, &program.abi)?;

    trace_program(&program, &package.name, &inputs_map, out_dir, pedantic_solving)
}

pub(crate) fn trace_program(
    compiled_program: &CompiledProgram,
    crate_name: &CrateName,
    inputs_map: &InputMap,
    out_dir: &str,
    pedantic_solving: bool,
) -> Result<(), CliError> {
    let initial_witness = compiled_program.abi.encode(inputs_map, None)?;

    let debug_artifact = DebugArtifact {
        debug_symbols: compiled_program.debug.clone(),
        file_map: compiled_program.file_map.clone(),
    };

    let crate_name_string: String = crate_name.into();
    // CTFS is the only trace format nargo emits; the writer factory is kept
    // for symmetry with other recorders and to centralize the format choice
    // in `codetracer_trace_writer`.
    let mut writer =
        create_trace_writer(crate_name_string.as_str(), &[], TraceEventsFileFormat::Ctfs);
    // `NimWriterSink` is the `noir_tracer` adapter over the Nim writer's
    // `TraceWriter` trait; the recorder itself is typed against the
    // platform-agnostic `TraceSink`.
    let mut tracer = NimWriterSink::new(&mut *writer);

    // The recorder no longer reaches for `std::env::current_dir()` itself --
    // that is ambient state a wasm host does not have. The CLI, which does have
    // a working directory, supplies it, so the emitted container is unchanged.
    let options = TraceOptions::with_workdir(std::env::current_dir().ok());

    begin_trace(&mut tracer, out_dir, &crate_name_string, options.workdir.as_deref());
    if let Err(error) = noir_tracer::trace_circuit(
        &Bn254BlackBoxSolver(pedantic_solving),
        &compiled_program.program.functions,
        &debug_artifact,
        initial_witness,
        &compiled_program.program.unconstrained_functions,
        &compiled_program.abi.error_types,
        &options,
        &mut tracer,
    ) {
        return Err(CliError::from(error));
    };

    match finish_trace(&mut tracer) {
        Ok(()) => println!("Saved trace to {out_dir}"),
        Err(err) => println!("Warning: trace writer failed to finalize CTFS container: {err}"),
    }

    Ok(())
}
