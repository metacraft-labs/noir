use crate::{SourceLocation, StackFrame, stack_frame::Variable};

use acvm::{BlackBoxFunctionSolver, FieldElement};
use fm::codespan_files::Files;
use nargo::errors::Location;
use noir_debugger::context::{DebugContext, DebugLocation};

/// Extracts the current stack of source locations from the debugger, given that the relevant
/// debugging information is present. In the context of this method, a source location is a path
/// to a source file and a line in that file. The most recently called function is last in the
/// returned vector/stack.
///
/// If there is no debugging information, an empty vector will be returned.
///
/// If some of the debugging information is missing (no line or filename for a certain frame of
/// the stack), an "unknown location" will be created for that frame. See
/// `SourceLocation::create_unknown`.
pub(crate) fn get_current_source_locations<B: BlackBoxFunctionSolver<FieldElement>>(
    debug_context: &DebugContext<B>,
) -> Vec<SourceLocation> {
    let call_stack = debug_context.get_call_stack();

    get_source_locations_for_call_stack(debug_context, call_stack)
}

pub(crate) fn get_source_locations_for_call_stack<B: BlackBoxFunctionSolver<FieldElement>>(
    debug_context: &DebugContext<B>,
    call_stack: Vec<DebugLocation>,
) -> Vec<SourceLocation> {
    let mut result: Vec<SourceLocation> = vec![];
    for opcode_location in call_stack {
        let locations = debug_context.get_source_location_for_debug_location(&opcode_location);
        for location in locations {
            let source_location = convert_debugger_location(debug_context, location);
            result.push(source_location);
        }
    }

    result
}

/// Converts the debugger stack frames into a vector of stack frames that own their data.
pub(crate) fn get_stack_frames<B: BlackBoxFunctionSolver<FieldElement>>(
    debug_context: &DebugContext<B>,
) -> Vec<StackFrame> {
    debug_context.get_variables().iter().map(convert_debugger_stack_frame).collect()
}

fn convert_debugger_stack_frame(
    debugger_stack_frame: &noirc_artifacts::debug::StackFrame<FieldElement>,
) -> StackFrame {
    let function_name = String::from(debugger_stack_frame.function_name);
    let mut variables: Vec<Variable> =
        debugger_stack_frame.variables.iter().map(Variable::from_tuple).collect();
    variables.sort();

    let mut function_param_indexes = Vec::new();
    for param_name in &debugger_stack_frame.function_params {
        // Note(stanm): `mut` in params is put in the name; remove it.
        let stripped_param_name = match param_name.strip_prefix("mut ") {
            Some(stripped_param_name) => stripped_param_name,
            None => param_name,
        };
        match variables.binary_search_by(|var| var.name.as_str().cmp(stripped_param_name)) {
            Err(_) => {
                // This panic causes a crash when tracing zk_dungeon:
                // TODO(BSN-2056): investigate why this happens
                //panic!("param_name {param_name} not found in variables {variables:?}");
            }
            Ok(index) => function_param_indexes.push(index),
        };
    }
    StackFrame { function_name, function_param_indexes, variables }
}

/// Converts a debugger `Location` into a tracer `SourceLocation`.
///
/// In case there is a problem getting the filepath or the line number from the debugger, a
/// `SourceLocation::create_unknown` is used to return an unknown location.
fn convert_debugger_location<B: BlackBoxFunctionSolver<FieldElement>>(
    debug_context: &DebugContext<B>,
    location: Location,
) -> SourceLocation {
    // These three all come straight off the `DebugArtifact`; there is no need
    // for the debugger to forward them.
    let debug_artifact = debug_context.debug_artifact();

    let filepath = match debug_artifact.name(location.file) {
        Ok(filepath) => filepath,
        Err(error) => {
            tracing::warn!("could not get filepath for source location: {error}");
            return SourceLocation::create_unknown();
        }
    };

    let line_number = match debug_artifact.location_line_index(location) {
        Ok(line) => line as isize + 1,
        Err(error) => {
            tracing::warn!("could not get line for source location: {error}");
            return SourceLocation::create_unknown();
        }
    };
    // The 1-indexed column, derived from `Location::span.start()`.  Synthetic
    // locations (no source file backing) yield `None` rather than an unknown
    // sentinel, so the rest of the location is still usable for the line-only
    // Step fallback.
    //
    // ======================================================================
    // WHY THIS IS DERIVED HERE INSTEAD OF TAKEN FROM
    // `DebugArtifact::location_column_number`, AND IT IS TWO DEFECTS AND NOT ONE.
    // Both were measured on 2026-08-31 against nargo 1.0.0-beta.26.
    //
    // The writer's column coordinate is defined by
    // `tracer_glue::compute_line_lengths`: **per-line UTF-8 BYTE counts, with
    // the line terminator NOT counted**.  `paths.dat` Layout A encodes a step
    // as the global byte position `sum(len(1..line-1)) + (column - 1)`, and the
    // reader inverts that with the same table.  So a column is in contract iff
    // `1 <= column <= line_length_in_bytes`.
    //
    //   1. **THE OFF-BY-ONE AT END OF LINE — this is the `("main", 142)` defect.**
    //      `codespan`'s `column_index` clamps the byte index to `line_range.end`,
    //      and a codespan line range INCLUDES its terminator, so a span that
    //      starts on the newline reports `column = line_length + 1`.  Every
    //      traced program hits this exactly once: the debugger's final location
    //      is the empty span at the newline after `main`'s closing brace.
    //      Measured on `multi_stmt_per_line`: `span=(99..99)`, line 4, and
    //      codespan says column 2 for a one-character line.  The writer then
    //      encodes `sum(all line lengths) + 0`, which is one past the last
    //      addressable byte, the reader cannot map it back to a line, and it
    //      surfaces the RAW GLOBAL CURSOR as the line number.  That is where
    //      `a_2_function_calls` got line **142** in a 13-line file, `a_1_mul`
    //      line **264** in 9, and `multi_stmt_per_line` line **96** in 4 — and
    //      it is why all three equal `file_size - line_count`, which is the sum
    //      of the line lengths, rather than anything about the program.
    //      Proved to be a byte cursor rather than a line by padding line 2 of
    //      `multi_stmt_per_line` with ten spaces WITHOUT changing its line
    //      count: the number moved 96 -> 106.
    //
    //   2. **THE UNIT.** `codespan`'s column counts CHARACTERS (it counts char
    //      boundaries in the line range); `compute_line_lengths` counts BYTES.
    //      They agree for ASCII, which is every fixture in `test_programs/trace`,
    //      and they disagree for any source with a multi-byte character before
    //      the step — silently, and in the direction that produces a plausible
    //      wrong position rather than an obvious one.  Deriving the column from
    //      the byte offsets here makes the recorder speak the writer's unit.
    //
    // Clamping is the right repair rather than dropping the step: the position
    // it clamps to is `main`'s closing brace, which is a real line a stepper
    // should stop on, and which `is_closing_brace_location` deliberately keeps
    // for the outermost frame.  `test_last_main_step_is_in_range_in_every_fixture`
    // pins the result over seven fixtures and would go red if either defect
    // returned: measured by removing the clamp on 2026-08-31, that test and
    // `test_a_2_function_calls_via_ct_print_full` are the only two of twelve
    // that fail.
    // ======================================================================
    let column_number = debug_artifact
        .line_range(location.file, (line_number - 1) as usize)
        .ok()
        .zip(debug_artifact.source(location.file).ok())
        .map(|(line_range, source)| {
            // The line's length in bytes, terminator excluded — the same
            // quantity `compute_line_lengths` puts in `paths.dat`.
            let line_bytes = source
                .get(line_range.start..line_range.end)
                .map(|line| line.trim_end_matches('\n').trim_end_matches('\r').len())
                .unwrap_or(0);
            let offset_in_line = (location.span.start() as usize).saturating_sub(line_range.start);
            // `max(1)` because a zero-length line still has column 1, and
            // `min(line_bytes)` because a column past the last byte is the
            // out-of-contract cursor described above.
            (offset_in_line + 1).min(line_bytes.max(1)) as isize
        });
    SourceLocation { filepath, line_number, column_number }
}
