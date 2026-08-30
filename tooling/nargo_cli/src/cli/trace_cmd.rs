use bn254_blackbox_solver::Bn254BlackBoxSolver;
use clap::Args;

use nargo::ops::debug::compile_options_for_debugging;
use nargo::package::Package;
use nargo::{constants::PROVER_INPUT_FILE, ops::debug::compile_bin_package_for_debugging};
use nargo_toml::{PackageSelection, get_package_manifest, resolve_workspace_from_toml};
use noir_tracer::tracer_glue::begin_trace;
use noir_tracer::tracer_glue::finish_trace;
use noirc_abi::InputMap;
use noirc_artifacts::debug::DebugArtifact;
use noirc_artifacts::program::CompiledProgram;
use noirc_driver::{CompileOptions, NOIR_ARTIFACT_VERSION_STRING};
use noirc_frontend::graph::CrateName;

use noir_artifact_cli::fs::inputs::read_inputs_from_file;

use crate::errors::CliError;

use codetracer_trace_writer::{TraceEventsFileFormat, create_trace_writer};

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

    trace_program_and_decode(compiled_program, package, &args.prover_name, &args.out_dir)
}

fn trace_program_and_decode(
    program: CompiledProgram,
    package: &Package,
    prover_name: &str,
    out_dir: &str,
) -> Result<(), CliError> {
    // Parse the initial witness values from Prover.toml
    let (inputs_map, _) = read_inputs_from_file(
        &package.root_dir.join(prover_name).with_extension("toml"),
        &program.abi,
    )?;

    trace_program(&program, &package.name, &inputs_map, out_dir)
}

pub(crate) fn trace_program(
    compiled_program: &CompiledProgram,
    crate_name: &CrateName,
    inputs_map: &InputMap,
    out_dir: &str,
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
    let mut tracer =
        create_trace_writer(crate_name_string.as_str(), &[], TraceEventsFileFormat::Ctfs);
    begin_trace(&mut *tracer, out_dir, &crate_name_string);
    if let Err(error) = noir_tracer::trace_circuit(
        &Bn254BlackBoxSolver,
        &compiled_program.program.functions,
        &debug_artifact,
        initial_witness,
        &compiled_program.program.unconstrained_functions,
        &compiled_program.abi.error_types,
        &mut *tracer,
    ) {
        return Err(CliError::from(error));
    };

    finish_trace(&mut *tracer, out_dir);

    Ok(())
}
