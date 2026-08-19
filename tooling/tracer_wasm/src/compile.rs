//! Compile Noir **source** into a `CompiledProgram`, entirely in memory.
//!
//! This is the half of the pipeline that `tooling/tracer_wasm` was missing:
//! [`crate::trace_artifact`] starts from an already-compiled artifact, so a
//! host still needed a native `nargo` to produce one. Everything the compiler
//! needs is reachable without a filesystem -- the standard library is embedded
//! into `noirc_driver` with `rust-embed`, and [`fm::FileManager`] is a plain
//! in-memory map -- so the same source-to-artifact step `nargo trace` performs
//! runs inside the wasm module.
//!
//! The compile options deliberately mirror
//! `nargo::ops::debug::compile_options_for_debugging(false, false, _)`, which is
//! what `nargo trace` uses. In particular `instrument_debug` and `force_brillig`
//! must both be on: the source-level [`DebugInstrumenter`] is what injects the
//! `__debug_*` calls the tracer reads variable values from, and tracing runs the
//! Brillig VM rather than the ACIR backend.

use std::collections::BTreeMap;
use std::path::Path;

use fm::FileManager;
use fm::codespan_files::Files as _;
use nargo::parse_all;
use noirc_artifacts::program::CompiledProgram;
use noirc_driver::{CompileOptions, file_manager_with_stdlib, link_to_debug_crate, prepare_crate};
use noirc_errors::{CustomDiagnostic, reporter::DiagnosticKind};
use noirc_frontend::debug::DebugInstrumenter;
use noirc_frontend::hir::{Context, ParsedFiles};

/// Where a single-file program is registered when the caller does not say.
///
/// It must live in a directory: the instrumenter decides which files belong to
/// the package being traced by testing whether the entry point's *parent* is one
/// of their ancestors, and every path has the empty path as an ancestor -- an
/// entry point at the root would therefore instrument the standard library too.
pub const DEFAULT_ENTRY_POINT: &str = "src/main.nr";

/// Compile a set of in-memory Noir files, rooted at `entry_point`.
///
/// `files` maps a path to that file's source. Paths are relative and are the
/// ones that end up in the artifact's `file_map`, and hence in the trace.
pub fn compile_source(
    files: &BTreeMap<String, String>,
    entry_point: &str,
) -> Result<CompiledProgram, String> {
    let entry_path = Path::new(entry_point);
    let entry_parent =
        entry_path.parent().filter(|p| !p.as_os_str().is_empty()).ok_or_else(|| {
            format!(
                "the entry point must live in a directory (got `{entry_point}`); \
             a root-level entry point would instrument the standard library"
            )
        })?;

    if !files.contains_key(entry_point) {
        return Err(format!("no source was supplied for the entry point `{entry_point}`"));
    }

    let mut file_manager = file_manager_with_stdlib(Path::new(""));
    for (path, source) in files {
        file_manager.add_file_with_source(Path::new(path), source.clone());
    }

    let mut parsed_files = parse_all(&file_manager);
    let debug_instrumenter =
        instrument_package_files(&mut parsed_files, &file_manager, entry_parent);

    let mut context = Context::new(file_manager, parsed_files);
    let crate_id = prepare_crate(&mut context, entry_path);
    link_to_debug_crate(&mut context, crate_id);
    context.debug_instrumenter = debug_instrumenter;

    let options = CompileOptions {
        // Same three knobs `compile_options_for_debugging` sets. Instrumenting
        // pulls in `__debug` functions that the program may not call, so
        // warnings are silenced rather than denied.
        silence_warnings: true,
        deny_warnings: false,
        instrument_debug: true,
        force_brillig: true,
        ..CompileOptions::default()
    };

    let (program, _warnings) =
        noirc_driver::compile_main(&mut context, crate_id, &options, None)
            .map_err(|diagnostics| render_diagnostics(&diagnostics, &context.file_manager))?;

    Ok(program)
}

/// Instrument every parsed file that sits under `entry_parent`.
///
/// A transcription of the private `nargo::ops::debug::instrument_package_files`,
/// which cannot be reused directly because it identifies the package through a
/// `nargo::package::Package` read from a `Nargo.toml` on disk.
fn instrument_package_files(
    parsed_files: &mut ParsedFiles,
    file_manager: &FileManager,
    entry_parent: &Path,
) -> DebugInstrumenter {
    let mut debug_instrumenter = DebugInstrumenter::default();

    for (file_id, parsed_file) in parsed_files.iter_mut() {
        let file_path =
            file_manager.path(*file_id).expect("parsed file ID not found in file manager");
        if file_path.ancestors().any(|ancestor| ancestor == entry_parent) {
            debug_instrumenter.instrument_module(&mut parsed_file.0);
        }
    }

    debug_instrumenter
}

/// Render compiler diagnostics as plain text.
///
/// `codespan_reporting`'s pretty renderer writes to a terminal; a browser only
/// has a string, so errors are flattened to `path:line:col: message` with their
/// secondary labels and notes appended.
fn render_diagnostics(diagnostics: &[CustomDiagnostic], file_manager: &FileManager) -> String {
    let files = file_manager.as_file_map();
    let mut out = String::from("failed to compile the program:");

    for diagnostic in diagnostics {
        if diagnostic.kind != DiagnosticKind::Error && diagnostic.kind != DiagnosticKind::Bug {
            continue;
        }

        let location = file_manager
            .path(diagnostic.file)
            .map(|path| path.display().to_string())
            .unwrap_or_else(|| "<unknown file>".to_string());

        out.push_str("\n  ");
        out.push_str(&location);

        // Point at the first secondary label, which is where the frontend puts
        // the offending span.
        if let Some(label) = diagnostic.secondaries.first()
            && let Ok(position) =
                files.location(diagnostic.file, label.location.span.start() as usize)
        {
            out.push_str(&format!(":{}:{}", position.line_number, position.column_number));
        }

        out.push_str(": ");
        out.push_str(&diagnostic.message);

        for label in &diagnostic.secondaries {
            if !label.message.is_empty() {
                out.push_str("\n      ");
                out.push_str(&label.message);
            }
        }
        for note in &diagnostic.notes {
            out.push_str("\n      note: ");
            out.push_str(note);
        }
    }

    out
}
