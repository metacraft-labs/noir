use bn254_blackbox_solver::Bn254BlackBoxSolver;
use clap::Args;

use nargo::ops::debug::{
    compile_options_for_debugging, compile_test_fn_for_debugging, get_test_function_for_debug,
    load_workspace_files, prepare_package_for_debug,
};
use nargo::ops::{check_crate_and_report_errors, report_errors};
use nargo::package::Package;
use nargo::workspace::Workspace;
use nargo::{constants::PROVER_INPUT_FILE, ops::debug::compile_bin_package_for_debugging};
use nargo_toml::{PackageSelection, get_package_manifest, resolve_workspace_from_toml};
use noir_tracer::TraceOptions;
use noir_tracer::sink::NimWriterSink;
use noir_tracer::tracer_glue::begin_trace;
use noir_tracer::tracer_glue::finish_trace;
use noirc_abi::InputMap;
use noirc_artifacts::debug::DebugArtifact;
use noirc_artifacts::program::{CompiledProgram, ProgramArtifact};
use noirc_driver::{CompileOptions, NOIR_ARTIFACT_VERSION_STRING};
use noirc_frontend::graph::CrateName;
use std::path::PathBuf;

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

    /// Also write the debug-instrumented `ProgramArtifact` to this path.
    ///
    /// This is the artifact a platform-agnostic tracer host (for instance the
    /// `noir_tracer_wasm` module running in a browser) consumes: it carries the
    /// `__debug_*` instrumentation that `nargo compile` does NOT produce, since
    /// the source-level instrumenter only runs on the debugging compile path.
    #[clap(long)]
    emit_debug_artifact: Option<PathBuf>,

    /// Trace this `#[test]` function instead of `main`.
    ///
    /// Matched the way `nargo debug --test-name` matches: a substring of the
    /// test's fully-qualified name, narrowed to the exact last `::` segment when
    /// several tests contain it, so `tests::test_x` and `test_x` both select
    /// `tests::test_x`. Only a test without parameters can be traced (one with
    /// parameters is a fuzz test, refused as `nargo debug` refuses it), so no
    /// prover inputs are read. A test that fails is traced up to its failure,
    /// recorded as an error event, as a failing `main` is.
    #[clap(long)]
    test_name: Option<String>,
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

    if let Some(test_name) = &args.test_name {
        return trace_test(
            test_name,
            &workspace,
            args.compile_options.clone(),
            args.emit_debug_artifact.as_deref(),
            &args.out_dir,
        );
    }

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

    if let Some(path) = &args.emit_debug_artifact {
        write_debug_artifact(&compiled_program, path)?;
    }

    trace_program_and_decode(compiled_program, package, &args.prover_name, &args.out_dir)
}

fn write_debug_artifact(program: &CompiledProgram, path: &std::path::Path) -> Result<(), CliError> {
    let artifact: ProgramArtifact = program.clone().into();
    let json = serde_json::to_string(&artifact)
        .map_err(|err| CliError::Generic(format!("serializing the debug artifact: {err}")))?;
    std::fs::write(path, json).map_err(|err| {
        CliError::Generic(format!("writing the debug artifact to {}: {err}", path.display()))
    })
}

/// Trace the `#[test]` function `test_name` names, compiled with the same
/// debug instrumentation `main` gets, into the same `<package>.ct`.
///
/// The test is found and compiled the way `nargo debug --test-name` finds and
/// compiles it (`get_test_function_for_debug`, `compile_test_fn_for_debugging`).
/// Tests live in libraries as often as in binaries, so any package kind is
/// accepted. A test with parameters is refused by
/// `get_test_function_for_debug`, so the witness of a traced test is empty.
fn trace_test(
    test_name: &str,
    workspace: &Workspace,
    compile_options: CompileOptions,
    emit_debug_artifact: Option<&std::path::Path>,
    out_dir: &str,
) -> Result<(), CliError> {
    let Some(package) = workspace.into_iter().next() else {
        return Err(CliError::Generic(
            "No packages found in workspace, so there is no test to trace.".to_string(),
        ));
    };

    let compile_options = compile_options_for_debugging(false, false, compile_options);

    let (file_manager, mut parsed_files) = load_workspace_files(workspace);
    let (mut context, crate_id) =
        prepare_package_for_debug(&file_manager, &mut parsed_files, package, workspace);
    check_crate_and_report_errors(&mut context, crate_id, &compile_options)?;

    let test =
        get_test_function_for_debug(crate_id, &context, test_name).map_err(CliError::Generic)?;

    let compiled_program =
        match compile_test_fn_for_debugging(&test, &mut context, compile_options.clone()) {
            Ok(program) => program,
            Err(error) => {
                report_errors::<()>(
                    Err(vec![error.into()]),
                    &file_manager,
                    &parsed_files,
                    compile_options.deny_warnings,
                    compile_options.silence_warnings,
                )?;
                return Err(CliError::Generic(format!("test `{}` failed to compile", test.name)));
            }
        };

    if let Some(path) = emit_debug_artifact {
        write_debug_artifact(&compiled_program, path)?;
    }

    trace_program(&compiled_program, &package.name, &InputMap::new(), out_dir)
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

    // Create `--out-dir` up front.  The Nim writer cannot open its container in
    // a directory that does not exist, and `begin_trace` turns that into a
    // `panic!` (which surfaces as SIGABRT, not a diagnostic).  A missing output
    // directory is an ordinary user mistake, so handle it here and report it as
    // a `CliError` instead.
    std::fs::create_dir_all(out_dir)
        .map_err(|err| CliError::Generic(format!("creating trace output dir {out_dir}: {err}")))?;

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
        &Bn254BlackBoxSolver,
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
