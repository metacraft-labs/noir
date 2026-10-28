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
pub use sink::{SOURCE_VIEW_KIND_RAW, TraceSink};

/// Re-exported so an embedder can supply an executor to [`trace_circuit_with_executor`]
/// without taking a direct dependency on `noir_debugger`.
pub use noir_debugger::foreign_calls::DebugForeignCallExecutor as TraceForeignCallExecutor;

use acvm::acir::circuit::brillig::{BrilligBytecode, BrilligFunctionId};
use acvm::{AcirField, BlackBoxFunctionSolver, FieldElement};
use acvm::{acir::circuit::Circuit, acir::native_types::WitnessMap};
use codetracer_trace_types::{Line, TypeKind};
use nargo::NargoError;
use noir_debugger::context::{DebugCommandResult, DebugContext};
use noir_debugger::foreign_calls::{DebugForeignCallExecutor, DefaultDebugForeignCallExecutor};
use noirc_artifacts::debug::DebugArtifact;
use std::cell::RefCell;
use std::collections::{BTreeMap, HashSet};
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

/// A tracer write held back, in order, while a call record waits for its frame's parameters.
/// See [`PendingCall`].
enum DeferredWrite {
    Step(SourceLocation),
    Variables(StackFrame),
    Print(String),
}

/// A call whose record has not been written yet, because its frame's parameters are not all
/// bound.
///
/// WHY A CALL RECORD IS WRITTEN LATE. The record's arguments are read from the callee's frame
/// (`tracer_glue::convert_params_to_args_vec`), and a frame appears at `__debug_fn_enter`, before
/// any parameter is bound: under column-aware stepping the instrumenter binds the parameters
/// afterwards, one step per parameter, at each parameter's own column in the signature
/// (`a_1_mul`'s first steps are `(1,1)`, `(3,13)`, `(3,21)`, `(3,29)`). A record written when the
/// frame appears therefore carries no argument at all, and a viewer renders every call as `()`.
///
/// WHY THE WRITES AFTER IT ARE HELD AS WELL. A trace is an ordered stream, and the call record
/// opens the callee's frame: every step, variable and print event between the frame appearing and
/// its parameters being bound belongs INSIDE the call. Writing them while the record waits would
/// file them under the caller. So they are kept here, in order, and replayed right after the
/// record, which makes the stream identical to the one an eager record produces except that the
/// record carries its arguments.
///
/// The record is written (see [`TracingContext::settle_pending_call`] and
/// [`TracingContext::write_pending_call`]):
///
/// * when the frame's parameters are all bound, at the start of the update that first sees it;
/// * when the frame stack changes so that the frame is gone or a deeper frame is entered — with
///   whatever is bound by then, before that update's returns and calls, which must follow it;
/// * when tracing ends, normally or on an error, so a run that stops early still closes the
///   stream with every call it entered.
struct PendingCall {
    /// Where the caller was when the frame appeared; `register_call` files the function under it.
    call_site: SourceLocation,
    /// The frame's index in the frame stack. It is always the innermost frame: entering a deeper
    /// one writes this record first.
    depth: usize,
    /// The latest snapshot of the frame, which is what the record's arguments are read from.
    frame: StackFrame,
    writes: Vec<DeferredWrite>,
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
    /// Whether the artifact carries any source-level debug instrumentation at all.
    ///
    /// `true` when no `DebugInfo` in the artifact declares a variable or a function, which is what
    /// a compile without `instrument_debug` produces — and what every Aztec contract artifact is.
    /// See [`TracingContext::update_record`], which is the only reader.
    uninstrumented: bool,
    /// The call whose record waits for its frame's parameters, with the writes that follow it.
    /// `None` whenever every entered call has been written. See [`PendingCall`].
    pending_call: Option<PendingCall>,
}

impl<'a, B: BlackBoxFunctionSolver<FieldElement>> TracingContext<'a, B> {
    pub fn new(
        blackbox_solver: &'a B,
        circuit: &'a [Circuit<FieldElement>],
        debug_artifact: &'a DebugArtifact,
        initial_witness: WitnessMap<FieldElement>,
        unconstrained_functions: &'a [BrilligBytecode<FieldElement>],
    ) -> Self {
        Self::with_executor(
            blackbox_solver,
            circuit,
            debug_artifact,
            initial_witness,
            unconstrained_functions,
            None,
        )
    }

    /// As [`TracingContext::new`], with the foreign-call executor supplied by the caller.
    ///
    /// [`DebugContext::new`] has always taken the executor as a boxed trait object; this
    /// constructor is the same parameter one level up, so an embedder can answer foreign calls the
    /// recorder knows nothing about. `None` builds exactly the executor
    /// [`TracingContext::new`] has always built, so the default path is unchanged.
    ///
    /// A supplied executor REPLACES the default rather than sitting beside it. The default is
    /// `DefaultDebugForeignCallExecutor::from_artifact`, whose stack is (top first) the
    /// `__debug_*` variable handler, `print`, the mock handler, and — as its base —
    /// `layers::Empty`, which answers every remaining call with an empty result. A caller that
    /// wants those behaviours composes them itself; `nargo::foreign_calls::layers` is the
    /// machinery for it. Two consequences are worth stating rather than leaving to be discovered:
    ///
    /// * `print` and `debug_log` output is captured through the writer this constructor installs
    ///   into the default executor. An executor supplied here owns its own output, so
    ///   [`TracingContext`]'s `print_output` stays empty unless the caller's stack writes into it.
    /// * `layers::Empty` is what makes an unrecognised foreign call succeed today. An executor
    ///   that refuses instead — returning `ForeignCallError::NoHandler` — turns the same call into
    ///   a named execution error, which is usually what an embedder wants.
    pub fn with_executor(
        blackbox_solver: &'a B,
        circuit: &'a [Circuit<FieldElement>],
        debug_artifact: &'a DebugArtifact,
        initial_witness: WitnessMap<FieldElement>,
        unconstrained_functions: &'a [BrilligBytecode<FieldElement>],
        foreign_call_executor: Option<Box<dyn DebugForeignCallExecutor + 'a>>,
    ) -> Self {
        let print_output = Rc::new(RefCell::new(String::new()));

        let foreign_call_executor: Box<dyn DebugForeignCallExecutor + 'a> =
            match foreign_call_executor {
                Some(executor) => executor,
                None => {
                    let writer: StringWriter = StringWriter::new(Rc::clone(&print_output));
                    Box::new(DefaultDebugForeignCallExecutor::from_artifact(
                        writer,
                        None,
                        debug_artifact,
                        None,
                        String::new(),
                    ))
                }
            };
        let debug_context = DebugContext::new(
            blackbox_solver,
            circuit,
            debug_artifact,
            initial_witness.clone(),
            foreign_call_executor,
            unconstrained_functions,
        );

        let uninstrumented = debug_artifact
            .debug_symbols
            .iter()
            .all(|info| info.variables.is_empty() && info.functions.is_empty());

        Self {
            debug_context,
            source_locations: vec![],
            stack_frames: vec![],
            saved_return_value: None,
            print_output,
            trace_started: false,
            uninstrumented,
            pending_call: None,
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

    // THE THREE WRITES A CALL RECORD CAN BE WAITING IN FRONT OF. Each one goes to `tracer` at once
    // when no call is pending, and into the pending call's queue otherwise, so the order the
    // recorder decides on is the order on the wire. They take the fields they need rather than
    // `&mut self`, because their callers hold a frame borrowed from `self.stack_frames`.

    fn maybe_report_print_events(
        print_output: &RefCell<String>,
        pending_call: &mut Option<PendingCall>,
        tracer: &mut dyn TraceSink,
    ) {
        let s = std::mem::take(&mut *print_output.borrow_mut());
        if s.is_empty() {
            return;
        }
        match pending_call {
            Some(pending) => pending.writes.push(DeferredWrite::Print(s)),
            None => register_print(tracer, &s),
        }
    }

    fn write_step(
        pending_call: &mut Option<PendingCall>,
        tracer: &mut dyn TraceSink,
        location: &SourceLocation,
    ) {
        match pending_call {
            Some(pending) => pending.writes.push(DeferredWrite::Step(location.clone())),
            None => register_step(tracer, location),
        }
    }

    fn write_variables(
        pending_call: &mut Option<PendingCall>,
        tracer: &mut dyn TraceSink,
        frame: &StackFrame,
    ) {
        match pending_call {
            Some(pending) => pending.writes.push(DeferredWrite::Variables(frame.clone())),
            None => register_variables(tracer, frame),
        }
    }

    /// Writes the pending call's record, with the arguments bound in `frame`, and then every write
    /// that was held behind it, in the order they were made. A no-op when no call is pending.
    fn write_pending_call(&mut self, tracer: &mut dyn TraceSink, frame: Option<&StackFrame>) {
        let Some(pending) = self.pending_call.take() else {
            return;
        };
        register_call(tracer, &pending.call_site, frame.unwrap_or(&pending.frame));
        for write in pending.writes {
            match write {
                DeferredWrite::Step(location) => register_step(tracer, &location),
                DeferredWrite::Variables(frame) => register_variables(tracer, &frame),
                DeferredWrite::Print(s) => register_print(tracer, &s),
            }
        }
    }

    /// Decides, at the start of an update, whether the pending call's record can be written now.
    ///
    /// `stack_frames` is the frame stack at this pause; `self.stack_frames` still holds the one the
    /// pending call was last seen in. The comparison is `tail_diff_vecs`'s, the same one
    /// [`TracingContext::update_record`] uses to find returns and calls, so "the frame is still
    /// there" means exactly what it means for the return it would otherwise be reported as.
    fn settle_pending_call(&mut self, tracer: &mut dyn TraceSink, stack_frames: &[StackFrame]) {
        let Some(pending) = &mut self.pending_call else {
            return;
        };
        let depth = pending.depth;
        let (first_nomatch, _, _) = tail_diff_vecs(&self.stack_frames, stack_frames);
        let still_open = first_nomatch > depth;
        if !still_open {
            // Returned from (or replaced) before every parameter was bound: write it with what
            // was bound in the last snapshot it appeared in, ahead of the return this update
            // reports for it.
            self.write_pending_call(tracer, None);
        } else if stack_frames.len() > depth + 1 || stack_frames[depth].all_params_bound() {
            // Either every parameter is bound now, or a deeper call is being entered, whose record
            // must come after this one. The frame as it is at this pause is the most complete.
            self.write_pending_call(tracer, Some(&stack_frames[depth]));
        } else {
            pending.frame = stack_frames[depth].clone();
        }
    }

    /// Writes the pending call's record, if any, because tracing is ending. Every path out of
    /// [`trace_circuit_with_executor`]'s loop, and [`handle_function_error`] before it records the
    /// error, goes through here, so no entered call is left out of the trace.
    fn finish_pending_call(&mut self, tracer: &mut dyn TraceSink) {
        self.write_pending_call(tracer, None);
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
        // Before anything this update writes: a pending call's record either becomes complete
        // here, or has to precede the returns and calls below. See `PendingCall`.
        self.settle_pending_call(tracer, &stack_frames);

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
                Self::write_step(&mut self.pending_call, tracer, call_site_location);
                Self::write_variables(&mut self.pending_call, tracer, frame);
                Self::maybe_update_saved_return_value(frame, &mut self.saved_return_value);
                Self::maybe_report_print_events(&self.print_output, &mut self.pending_call, tracer);
            }
        }

        assert!(new_frames.len() <= 1, "more than one frame entered at the same step");
        if let Some(&frame) = new_frames.first() {
            let location = self.source_locations.last().expect("no previous location before call");
            if frame.all_params_bound() {
                register_call(tracer, location, frame);
            } else {
                // The frame appeared before its parameters were bound, which under column-aware
                // stepping is every function that declares a named one. Hold the record until
                // they are, and everything written meanwhile behind it. See `PendingCall`.
                self.pending_call = Some(PendingCall {
                    call_site: location.clone(),
                    depth: stack_frames.len() - 1,
                    frame: frame.clone(),
                    writes: Vec::new(),
                });
            }
        }

        // AN UNINSTRUMENTED PROGRAM HAS NO VARIABLE FRAMES AND STILL HAS SOURCE POSITIONS, AND IT
        // USED TO RECORD NOTHING AT ALL.
        //
        // `stack_frames` comes from `DebugVars`, which is filled by the `__debug_fn_enter` /
        // `__debug_var_assign` calls the source-level instrumenter injects. A program compiled
        // WITHOUT `instrument_debug` carries none of those, so `stack_frames` is empty at every
        // step, `index` is -1, and the branch below never runs: the whole recording comes out with
        // zero `Step` records over an execution the debugger positions perfectly well.
        //
        // Measured on `@aztec/noir-test-contracts.js`'s `OracleVersionCheck.private_function`:
        // 1,004 opcodes stepped, 44 of them carrying a source location at 13 distinct positions,
        // and **0 steps recorded**.
        //
        // A step is a SOURCE POSITION; variables are what a step may additionally carry. So the
        // position is recorded either way, and the variables only when there is a frame to read
        // them from.
        //
        // THE GATE IS A PROPERTY OF THE ARTIFACT, NOT OF THE MOMENT, and the difference was
        // measured rather than reasoned about. A first version fired whenever `stack_frames` was
        // empty, on the argument that an empty frame stack recorded nothing before and so nothing
        // could change. **That is false**: an instrumented program's frame stack is also empty
        // before its first `__debug_fn_enter`, and six of this crate's twelve fixture tests went
        // red with one extra step each (`a_1_mul` 14 -> 15). Keying on
        // `debug_symbols[*].variables`/`functions` being empty — which the instrumenter always
        // fills and an uninstrumented compile never does — separates the two cases by their cause
        // instead of by a symptom they share.
        if self.uninstrumented && !returned_from_frame {
            if let Some(location) = source_locations.last() {
                Self::maybe_report_print_events(&self.print_output, &mut self.pending_call, tracer);
                Self::write_step(&mut self.pending_call, tracer, location);
            }
            self.stack_frames = stack_frames;
            return;
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
            // A constant body can reach its closing brace at the first pause after
            // __debug_fn_enter. Its definition was the preceding source location;
            // anchor the new frame there so its call owns a step of its own.
            let entry_anchor = nested_closing_brace && !new_frames.is_empty();
            if !nested_closing_brace || entry_anchor {
                let location = if entry_anchor {
                    self.source_locations.last().expect("no previous location before call")
                } else {
                    location
                };
                Self::maybe_report_print_events(&self.print_output, &mut self.pending_call, tracer);
                Self::write_step(&mut self.pending_call, tracer, location);
                Self::write_variables(&mut self.pending_call, tracer, &stack_frames[index]);
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
    trace_circuit_with_executor(
        blackbox_solver,
        circuit,
        debug_artifact,
        initial_witness,
        unconstrained_functions,
        error_types,
        options,
        tracer,
        None,
    )
}

/// As [`trace_circuit`], with the foreign-call executor supplied by the caller.
///
/// The trace destination has been injectable since this function took `&mut dyn TraceSink`; this
/// is the same treatment for the other end. `None` reproduces [`trace_circuit`] exactly — see
/// [`TracingContext::with_executor`] for what the default is and what replacing it costs.
#[allow(clippy::too_many_arguments)]
pub fn trace_circuit_with_executor<'a, B: BlackBoxFunctionSolver<FieldElement>>(
    blackbox_solver: &'a B,
    circuit: &'a [Circuit<FieldElement>],
    debug_artifact: &'a DebugArtifact,
    initial_witness: WitnessMap<FieldElement>,
    unconstrained_functions: &'a [BrilligBytecode<FieldElement>],
    error_types: &BTreeMap<ErrorSelector, AbiErrorType>,
    options: &TraceOptions,
    tracer: &mut dyn TraceSink,
    foreign_call_executor: Option<Box<dyn DebugForeignCallExecutor + 'a>>,
) -> Result<(), NargoError<FieldElement>> {
    let mut tracing_context = TracingContext::with_executor(
        blackbox_solver,
        circuit,
        debug_artifact,
        initial_witness,
        unconstrained_functions,
        foreign_call_executor,
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
    // together with its per-line byte-length table *and its source
    // text*.  The Nim writer
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
    let mut registered_paths: HashSet<PathBuf> = HashSet::new();
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
        if !registered_paths.insert(path.clone()) {
            // Two `FileId`s resolving to the same stripped path: the writer
            // would ignore the re-registration, and embedding the source a
            // second time would put a duplicate view in `source_views.dat`.
            continue;
        }
        let line_lengths = compute_line_lengths(&debug_file.source);
        if let Err(err) = TraceSink::register_path_with_line_lengths(tracer, &path, &line_lengths) {
            warn!("register_path_with_line_lengths failed for {}: {err}", path.display());
            continue;
        }

        // Embed the source text itself, so the container satisfies the
        // format's self-containment guarantee: a trace "includes all source
        // code and debug symbols needed for executing the replay on a
        // different machine from where the program was built and recorded"
        // (`codetracer-specs/Trace-Files/Trace-Files-Overview.md`), and the
        // seek-based reader resolves a source line from "the trace's embedded
        // source files" (`Trace-Files/Seek-Based-CTFS-Reader.md`).  Until this
        // call existed the loop computed `line_lengths` *from* the source and
        // then dropped the source on the floor, so `ct-print --full` reported
        // `source_views: []` and a viewer handed only the `.ct` stepped
        // correctly through code it could not display.
        //
        // This is unconditional on purpose.  A self-contained container is the
        // format's contract, not a mode; making it a flag would only create a
        // way to record the broken thing again.  (Web delivery separately
        // de-duplicates source across traces sharing a code hash via the
        // content-addressed bundles at `/src/{chain}/{codeHash}/{bundleHash}
        // .json` — Trace-Artifacts §2.5 / Source-Resolution §5.  That is a
        // transport optimisation layered on top, not a substitute: a
        // downloaded `.ct` has no bundle server to ask.)
        //
        // `debug_file.source` is the exact text the compiler compiled, held in
        // the `DebugArtifact`'s file map.  We deliberately do NOT re-read the
        // file from disk: what is on disk now can differ from what was
        // compiled, and there is no filesystem under wasm.
        //
        // The same workdir-stripped `path` is used as for the line-length
        // registration above, for the same identity reason: the view has to
        // hang off the very path id that `register_step` later interns, or the
        // reader would look for the source of one path and find it filed under
        // another.
        if let Err(err) = TraceSink::register_source_view(
            tracer,
            &path,
            SOURCE_VIEW_KIND_RAW,
            &path.to_string_lossy(),
            debug_file.source.as_bytes(),
            // No sourcemap: this is the original text, not a reformatting of
            // it, so generated and original positions coincide.
            &[],
        ) {
            warn!("register_source_view failed for {}: {err}", path.display());
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

    // Every `break` above lands here — the end of the program, and each error arm — so a call
    // still waiting for its parameters is written before the trace is closed.
    tracing_context.finish_pending_call(tracer);

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
    // The error belongs to the innermost call, so that call's record has to precede it even
    // when the failure came before its parameters were all bound.
    tracing_context.finish_pending_call(tracer);
    register_error(tracer, &err_str);
}
