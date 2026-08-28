mod source_location;
use acvm::acir::circuit::{ErrorSelector, OpcodeLocation};
use acvm::pwg::{OpcodeResolutionError, RawAssertionPayload, ResolvedAssertionPayload};
use nargo::errors::ExecutionError;
use noirc_abi::AbiErrorType;
use source_location::SourceLocation;

mod stack_frame;
use stack_frame::{StackFrame, Variable};

mod debugger_glue;
use debugger_glue::{
    get_current_source_locations, get_source_locations_for_call_stack, get_stack_frames,
};

pub mod tracer_glue;
use tracer_glue::{
    compute_line_lengths, register_call, register_error, register_print, register_return,
    register_step, register_variables,
};

pub mod tail_diff_vecs;
use tail_diff_vecs::tail_diff_vecs;

pub mod sink;
pub use sink::TraceSink;

use acvm::acir::circuit::brillig::{BrilligBytecode, BrilligFunctionId};
use acvm::{AcirField, BlackBoxFunctionSolver, FieldElement};
use acvm::{acir::circuit::Circuit, acir::native_types::WitnessMap};
use codetracer_trace_types::{Line, TypeKind};
use nargo::NargoError;
use noir_debugger::context::{DebugCommandResult, DebugContext};
use noir_debugger::foreign_calls::DefaultDebugForeignCallExecutor;
use noirc_artifacts::debug::DebugArtifact;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::io::Write;
use std::path::PathBuf;
use std::rc::Rc;
use tracing::{debug, error, warn};

/// The result from step_debugger: the debugger either paused at a new location, reached the end of
/// execution, or hit some kind of an error. Takes the error type as a parameter.
enum DebugStepResult<Error> {
    /// The debugger reached a new location and the execution is paused at it. The wrapped value is
    /// a vector, because if the next source line is a function call, one debugger step includes
    /// it, together with the first line of the called function. This is just how `nargo debug`
    /// works and a fact of life we choose not to change.
    Paused(Vec<SourceLocation>),
    /// The debuger reached the end of the program and finished execution.
    Finished,
    /// The debugger reached an error and cannot continue.
    Error(Error),
}

pub struct StringWriter {
    target: Rc<RefCell<String>>,
}

impl StringWriter {
    pub fn new(target: Rc<RefCell<String>>) -> Self {
        Self { target }
    }

    pub fn get_inner(&self) -> Rc<RefCell<String>> {
        Rc::clone(&self.target)
    }
}

impl Write for StringWriter {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        let s = String::from_utf8_lossy(buf);
        self.target.borrow_mut().push_str(&s);
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

pub struct TracingContext<'a, B: BlackBoxFunctionSolver<FieldElement>> {
    debug_context: DebugContext<'a, B>,
    /// The source location at the current moment of tracing.
    source_locations: Vec<SourceLocation>,
    /// The stack trace at the current moment; last call is last in the vector.
    stack_frames: Vec<StackFrame>,
    saved_return_value: Option<Variable>,
    print_output: Rc<RefCell<String>>,
    trace_started: bool,
}

impl<'a, B: BlackBoxFunctionSolver<FieldElement>> TracingContext<'a, B> {
    pub fn new(
        blackbox_solver: &'a B,
        circuit: &'a [Circuit<FieldElement>],
        debug_artifact: &'a DebugArtifact,
        initial_witness: WitnessMap<FieldElement>,
        unconstrained_functions: &'a [BrilligBytecode<FieldElement>],
    ) -> Self {
        let print_output = Rc::new(RefCell::new(String::new()));
        let writer: StringWriter = StringWriter::new(Rc::clone(&print_output));

        let foreign_call_executor = Box::new(DefaultDebugForeignCallExecutor::from_artifact(
            writer,
            None,
            debug_artifact,
            None,
            String::new(),
        ));
        let debug_context = DebugContext::new(
            blackbox_solver,
            circuit,
            debug_artifact,
            initial_witness.clone(),
            foreign_call_executor,
            unconstrained_functions,
        );

        Self {
            debug_context,
            source_locations: vec![],
            stack_frames: vec![],
            saved_return_value: None,
            print_output,
            trace_started: false,
        }
    }

    fn are_src_locations_equal(
        src_location_1: &[SourceLocation],
        src_location_2: &[SourceLocation],
    ) -> bool {
        if src_location_1.len() != src_location_2.len() {
            false
        } else {
            for i in 0..src_location_1.len() {
                if src_location_1[i] != src_location_2[i] {
                    return false;
                }
            }
            true
        }
    }

    /// Steps debugging execution until the next source location, while simultaneously checking for return values after each opcode
    fn next_into_with_return_values_check(&mut self) -> DebugCommandResult {
        let start_location = self.debug_context.get_current_source_location();
        loop {
            let result = self.debug_context.step_into_opcode();
            if !matches!(result, DebugCommandResult::Ok) {
                return result;
            }

            // check for return values
            let stack_frames = get_stack_frames(&self.debug_context);
            if let Some(frame) = stack_frames.last() {
                Self::maybe_update_saved_return_value(frame, &mut self.saved_return_value);
            }

            let new_location = self.debug_context.get_current_source_location();
            if new_location.is_some() && new_location != start_location {
                return DebugCommandResult::Ok;
            }
        }
    }

    /// Steps the debugger until a new line is reached, or the debugger returns anything other than
    /// Ok.
    ///
    /// Propagates the debugger result.
    fn step_debugger(&mut self) -> DebugStepResult<NargoError<FieldElement>> {
        loop {
            match self.next_into_with_return_values_check() {
                DebugCommandResult::Done => return DebugStepResult::Finished,
                DebugCommandResult::Error(error) => return DebugStepResult::Error(error),
                DebugCommandResult::BreakpointReached(loc) => {
                    // Note: this is panic! instead of an error, because it is more serious and
                    // indicates an internal inconsistency, rather than a recoverable error.
                    panic!("Error: Breakpoint unexpected in tracer; loc={loc}")
                }
                DebugCommandResult::Ok => (),
            }

            let source_locations = get_current_source_locations(&self.debug_context);
            if source_locations.is_empty() {
                warn!("no call stack");
                continue;
            };

            if Self::are_src_locations_equal(&self.source_locations, &source_locations) {
                // Continue stepping until a new line in the same file is reached, or the current file
                // has changed.
                continue;
            }

            return DebugStepResult::Paused(source_locations);
        }
    }

    fn maybe_update_saved_return_value(
        frame: &StackFrame,
        saved_return_value: &mut Option<Variable>,
    ) {
        for variable in &frame.variables {
            if variable.name == "__debug_return_expr" {
                *saved_return_value = Some(variable.clone());
                break;
            }
        }
    }

    fn maybe_report_print_events(&self, tracer: &mut dyn TraceSink) {
        let mut s = self.print_output.borrow_mut();
        if !(*s).is_empty() {
            register_print(tracer, (*s).as_str());
            *s = String::new();
        }
    }

    /// Whether `location` points at a line that is nothing but a closing brace.
    ///
    /// The source text is taken from `DebugArtifact.file_map`, which the compiler
    /// already populated with the exact text it compiled. This used to
    /// `std::fs::read_to_string` the path on every call, which was
    ///
    /// * a wasm blocker (no filesystem), and
    /// * a latent correctness bug: what is on disk now can disagree with what
    ///   was compiled, and the paths handed to the recorder are workdir-stripped,
    ///   so the read silently failed -- returning `false` -- whenever `nargo` was
    ///   invoked from anywhere other than the package directory.
    fn is_closing_brace_location(&self, location: &SourceLocation) -> bool {
        if location.line_number <= 0 {
            return false;
        }

        let artifact = self.debug_context.debug_artifact();
        // `location.filepath` is what `DebugArtifact::name(file_id)` produced,
        // which is the workdir-stripped form; `DebugFile::path` is absolute.
        // `Path::ends_with` matches whole components, so a relative suffix
        // resolves without any string surgery.
        let target = PathBuf::from(location.filepath.to_string());
        let Some(source) = artifact
            .file_map
            .values()
            .find(|file| file.path == target || file.path.ends_with(&target))
            .map(|file| &file.source)
        else {
            return false;
        };

        source
            .lines()
            .nth((location.line_number - 1) as usize)
            .map(|line| line.trim() == "}")
            .unwrap_or(false)
    }

    fn ensure_trace_started(
        &mut self,
        tracer: &mut dyn TraceSink,
        source_locations: &[SourceLocation],
    ) {
        if self.trace_started {
            return;
        }

        let Some(location) = source_locations.last() else {
            return;
        };
        let path = PathBuf::from(location.filepath.to_string());
        // Keep the historical entry step on line 1, but attach it to the
        // first real source file instead of the generated trace output path.
        TraceSink::start(tracer, &path, Line(1));
        self.trace_started = true;
    }

    /// Propagates information about the current execution state to `tracer`.
    fn update_record(&mut self, tracer: &mut dyn TraceSink, source_locations: &[SourceLocation]) {
        self.ensure_trace_started(tracer, source_locations);

        let stack_frames = get_stack_frames(&self.debug_context);
        let (first_nomatch, dropped_frames, new_frames) =
            tail_diff_vecs(&self.stack_frames, &stack_frames);
        let returned_from_frame = !dropped_frames.is_empty();

        for dropped_frame_index in (first_nomatch..first_nomatch + dropped_frames.len()).rev() {
            register_return(tracer, &self.saved_return_value);
            self.saved_return_value = None;
            if dropped_frame_index > 0 {
                // This branch is for returns not from main.
                let caller_index = dropped_frame_index - 1;
                let call_site_location = &self.source_locations[caller_index];
                let frame = stack_frames
                    .get(caller_index)
                    .unwrap_or_else(|| &self.stack_frames[caller_index]);
                register_step(tracer, call_site_location);
                register_variables(tracer, frame);
                Self::maybe_update_saved_return_value(frame, &mut self.saved_return_value);
                self.maybe_report_print_events(tracer);
            }
        }

        assert!(new_frames.len() <= 1, "more than one frame entered at the same step");
        if !new_frames.is_empty() {
            let location = self.source_locations.last().expect("no previous location before call");
            register_call(tracer, location, new_frames[0]);
        }

        let index = stack_frames.len() as isize - 1;
        // Noir can report a nested function's closing brace before the call
        // stack drops that frame. The return event captures that transition;
        // recording the brace as a step would expose a stale location with the
        // callee's locals.
        if index >= 0 && !returned_from_frame {
            let index = index as usize;
            let location = &source_locations[index];
            let nested_closing_brace = index > 0 && self.is_closing_brace_location(location);
            if !nested_closing_brace {
                self.maybe_report_print_events(tracer);
                register_step(tracer, location);
                register_variables(tracer, &stack_frames[index]);
                Self::maybe_update_saved_return_value(
                    &stack_frames[index],
                    &mut self.saved_return_value,
                );
            }
        }

        self.stack_frames = stack_frames;
    }
}

/// Ambient state the recorder used to reach for directly, made explicit.
///
/// `trace_circuit` and [`tracer_glue::begin_trace`] previously called
/// `std::env::current_dir()`, which is meaningless on a target with no process
/// environment. The caller now supplies the value.
#[derive(Clone, Debug, Default)]
pub struct TraceOptions {
    /// Prefix stripped from every source path the recorder registers, so the
    /// trace carries package-relative paths. `None` registers paths verbatim.
    ///
    /// The native CLI passes `std::env::current_dir().ok()`, reproducing the
    /// previous behaviour exactly.
    pub workdir: Option<PathBuf>,
}

impl TraceOptions {
    pub fn with_workdir(workdir: Option<PathBuf>) -> Self {
        Self { workdir }
    }

    /// Apply the workdir stripping this recorder has always applied.
    fn strip(&self, path: &std::path::Path) -> PathBuf {
        match &self.workdir {
            Some(workdir) => path
                .strip_prefix(workdir)
                .map(|p| p.to_path_buf())
                .unwrap_or_else(|_| path.to_path_buf()),
            None => path.to_path_buf(),
        }
    }
}

pub fn trace_circuit<B: BlackBoxFunctionSolver<FieldElement>>(
    blackbox_solver: &B,
    circuit: &[Circuit<FieldElement>],
    debug_artifact: &DebugArtifact,
    initial_witness: WitnessMap<FieldElement>,
    unconstrained_functions: &[BrilligBytecode<FieldElement>],
    error_types: &BTreeMap<ErrorSelector, AbiErrorType>,
    options: &TraceOptions,
    tracer: &mut dyn TraceSink,
) -> Result<(), NargoError<FieldElement>> {
    let mut tracing_context = TracingContext::new(
        blackbox_solver,
        circuit,
        debug_artifact,
        initial_witness,
        unconstrained_functions,
    );

    if tracing_context.debug_context.get_current_debug_location().is_none() {
        warn!("circuit contains no opcodes; generating no trace");
        return Ok(());
    }

    // Column-aware replay navigation: opt the writer into the
    // `DeltaColumn` (tag 0x07) encoding path *before* any Step event
    // is emitted (which includes the line-1 entry Step emitted by
    // `TraceSink::start` inside `ensure_trace_started`).  Sticky for
    // the lifetime of the trace; flips the `meta.dat` bit 4
    // (`FLAG_HAS_COLUMN_AWARE_STEPS`) consumed by ct-print and the
    // db-backend.  Mirrors the M-sol / M-evm / M-cairo / Leo
    // recorders.
    TraceSink::enable_column_aware_steps(tracer);
    // Advertise per-column breakpoint + motion capabilities so the
    // GUI can light up those affordances on Noir recordings.  Sets
    // meta.dat bits 6 and 7 (FLAG_SUPPORTS_COLUMN_BREAKPOINTS,
    // FLAG_SUPPORTS_COLUMN_MOTIONS).  Noir's
    // `DebugContext::get_column_for_location` (codetracer fork)
    // surfaces per-statement byte columns from `Span::start`, so
    // both capabilities hold; see
    // `codetracer-trace-format-spec/internal-files.md` §"Column-
    // Aware Capability Flags".
    TraceSink::enable_column_breakpoints_support(tracer);
    TraceSink::enable_column_motions_support(tracer);

    // Register every Noir source file the debugger knows about
    // together with its per-line byte-length table.  The Nim writer
    // ignores `register_path_with_line_lengths` for paths it has
    // already interned, so this has to happen before any
    // `register_step` / `start` call lands.  Skipping the
    // registration drops the table the reader's
    // `decodeGlobalPositionIndex` needs to surface a column, so even
    // with column-aware mode latched, `ct-print` would print
    // `column: null` for every Step.
    //
    // We use the same `DebugArtifact::name(file_id)` accessor that
    // `DebugContext::get_filepath_for_location` consumes on the step-
    // emission path so the path-table identity matches across
    // registration and per-step emission.  Without this, `register_step`
    // would intern a *separate* path (the workdir-stripped relative
    // form) and the column-decoding global position index would land
    // on a path with no `line_lengths`, surfacing the raw byte cursor
    // as a fake line.
    let debug_artifact = tracing_context.debug_context.debug_artifact();
    for debug_file in debug_artifact.file_map.values() {
        // Noir injects a synthetic `__debug/lib.nr` helper crate to
        // back its `__debug_*` builtins.  The debugger filters those
        // out of `get_source_location_for_debug_location`, so steps
        // never land on them in practice (the recorder's closing-brace
        // suppression catches the few stragglers).  Registering the
        // path here would still bloat the trace's `paths` table and
        // perturb the strict `_via_ct_print_full` golden tests; skip
        // it so the table only carries real user-visible source files.
        if debug_file.path.starts_with("__debug/") {
            continue;
        }
        // Mirror the workdir-stripping that `DebugArtifact::name`
        // applies before the debugger hands a path to `register_step`.
        // Registering the *unstripped* form here would intern a path
        // that `register_step` never re-mentions, leaving every Step
        // event keyed against a path with no `line_lengths` table —
        // which makes the column decoder fall back to the raw byte
        // cursor as a fake line.
        let path: PathBuf = options.strip(&debug_file.path);
        let line_lengths = compute_line_lengths(&debug_file.source);
        if let Err(err) = TraceSink::register_path_with_line_lengths(tracer, &path, &line_lengths) {
            warn!("register_path_with_line_lengths failed for {}: {err}", path.display());
        }
    }

    let _ = TraceSink::ensure_type_id(tracer, TypeKind::None, "None");
    loop {
        let source_locations = match tracing_context.step_debugger() {
            DebugStepResult::Finished => break,
            DebugStepResult::Error(err) => match &err {
                NargoError::ExecutionError(ExecutionError::SolvingError(
                    OpcodeResolutionError::BrilligFunctionFailed {
                        function_id,
                        call_stack,
                        payload,
                    },
                    _,
                )) => {
                    handle_function_error(
                        function_id,
                        call_stack,
                        payload.as_ref(),
                        error_types,
                        &err,
                        &mut tracing_context,
                        tracer,
                    );
                    break;
                }
                NargoError::ExecutionError(ExecutionError::AssertionFailed(
                    payload,
                    call_stack,
                    Some(function_id),
                )) => {
                    let opcode_locations =
                        call_stack.iter().map(|loc| loc.opcode_location).collect::<Vec<_>>();
                    handle_function_error(
                        function_id,
                        &opcode_locations,
                        Some(payload),
                        error_types,
                        &err,
                        &mut tracing_context,
                        tracer,
                    );
                    break;
                }
                _ => {
                    error!("{err}");
                    break;
                }
            },
            DebugStepResult::Paused(source_location) => source_location,
        };

        debug!("debugger stepped until line {:?}", source_locations.last().unwrap());

        tracing_context.update_record(tracer, &source_locations);

        // This update is intentionally explicit here, to show what drives the loop.
        tracing_context.source_locations = source_locations;
    }

    Ok(())
}

fn handle_function_error<F, B: BlackBoxFunctionSolver<FieldElement>>(
    function_id: &BrilligFunctionId,
    call_stack: &[OpcodeLocation],
    payload: Option<&ResolvedAssertionPayload<F>>,
    error_types: &BTreeMap<ErrorSelector, AbiErrorType>,
    err: &NargoError<F>,
    tracing_context: &mut TracingContext<B>,
    tracer: &mut dyn TraceSink,
) where
    F: AcirField,
{
    let err_str =
        if let Some(ResolvedAssertionPayload::Raw(RawAssertionPayload { selector, data: _ })) =
            payload
        {
            if let Some(AbiErrorType::String { string }) = error_types.get(selector) {
                string.clone()
            } else {
                err.to_string()
            }
        } else {
            err.to_string()
        };

    let debug_locations = call_stack
        .iter()
        .map(|opcode_loc| noir_debugger::context::DebugLocation {
            circuit_id: 0,
            opcode_location: *opcode_loc,
            brillig_function_id: Some(*function_id),
        })
        .collect();

    let source_locations =
        get_source_locations_for_call_stack(&tracing_context.debug_context, debug_locations);

    tracing_context.update_record(tracer, &source_locations);
    register_error(tracer, &err_str);
}
