//! The tracer's foreign-call executor is injectable, and the default is unchanged.
//!
//! [`noir_tracer::trace_circuit`] has always let the caller choose where the trace GOES — its last
//! parameter is `&mut dyn TraceSink`. What it did not let the caller choose is where foreign calls
//! are ANSWERED: `TracingContext::new` built a `DefaultDebugForeignCallExecutor` itself, even
//! though [`noir_debugger::context::DebugContext::new`] one level below takes the executor as a
//! `Box<dyn DebugForeignCallExecutor>`. [`noir_tracer::trace_circuit_with_executor`] and
//! [`noir_tracer::TracingContext::with_executor`] pass that parameter through.
//!
//! What the four tests here establish, in the order they build on each other:
//!
//! 1. **The default path is unchanged.** `trace_circuit` and
//!    `trace_circuit_with_executor(.., None)` produce the same event stream over a program that
//!    exercises `print` and the `__debug_*` calls the variable recorder rests on — compared as a
//!    whole recorded stream, not as a count, so a reordering fails too.
//! 2. **An injected executor is the one that runs.** It observes a call the default never sees.
//! 3. **An injected executor can REFUSE, and the refusal names the oracle.** Returning
//!    `ForeignCallError::NoHandler` stops the step loop with the oracle's own name in the error.
//! 4. **The control that makes 3 a measurement rather than a tautology: the DEFAULT executor lets
//!    the same call through.** `DefaultForeignCallBuilder::build` composes its layers over
//!    `layers::Empty`, which answers *every* unrecognised foreign call with an empty result — so a
//!    void oracle nobody implements succeeds silently today. That is worth a test of its own
//!    whatever happens to this seam: it is the difference between "no handler ran" and "no handler
//!    was needed", and nothing in the tree said which one `nargo trace` does.
//!
//! The programs are compiled IN PROCESS with `noirc_driver` rather than by spawning `nargo`. That
//! is not a convenience: `cargo test -p noir_tracer` does not rebuild `nargo`, so a test that
//! spawns one measures whatever binary happens to be on disk. Nothing here reads a path.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use acvm::FieldElement;
use acvm::acir::native_types::{WitnessMap, WitnessStack};
use bn254_blackbox_solver::Bn254BlackBoxSolver;
use codetracer_trace_types::{
    EventLogKind, FullValueRecord, FunctionId, Line, PathId, TypeId, TypeKind, ValueRecord,
};
use fm::FileManager;
use nargo::foreign_calls::{ForeignCallError, ForeignCallExecutor};
use nargo::parse_all;
use noir_tracer::{
    TraceForeignCallExecutor, TraceOptions, TraceSink, trace_circuit, trace_circuit_with_executor,
};
use noirc_artifacts::debug::DebugArtifact;
use noirc_artifacts::program::CompiledProgram;
use noirc_driver::{CompileOptions, file_manager_with_stdlib, link_to_debug_crate, prepare_crate};
use noirc_frontend::debug::DebugInstrumenter;
use noirc_frontend::hir::{Context, ParsedFiles};

use acvm::acir::brillig::ForeignCallResult;
use acvm::pwg::ForeignCallWaitInfo;
use noir_debugger::foreign_calls::DefaultDebugForeignCallExecutor;
use noirc_artifacts::debug::StackFrame;

// ---------------------------------------------------------------------------
// A sink that records what it was told, so two runs can be compared as streams.
// ---------------------------------------------------------------------------

/// Every `TraceSink` call, rendered as one line.
///
/// A count would pass over a stream whose events were reordered or whose values changed; the
/// whole rendered stream is compared instead.
#[derive(Default)]
struct RecordingSink {
    lines: Vec<String>,
    next_path_id: usize,
    next_function_id: usize,
    types: Vec<(TypeKind, String)>,
    values: Vec<(String, ValueRecord)>,
}

impl RecordingSink {
    fn push(&mut self, line: String) {
        self.lines.push(line);
    }
}

impl TraceSink for RecordingSink {
    fn begin_writing_trace_events(
        &mut self,
        path: &Path,
    ) -> Result<(), Box<dyn std::error::Error>> {
        self.push(format!("begin {}", path.display()));
        Ok(())
    }

    fn finish_writing_trace_events(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        self.push("finish".to_string());
        Ok(())
    }

    fn close(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        self.push("close".to_string());
        Ok(())
    }

    fn set_workdir(&mut self, workdir: &Path) {
        self.push(format!("workdir {}", workdir.display()));
    }

    fn start(&mut self, path: &Path, line: Line) {
        self.push(format!("start {} {}", path.display(), line.0));
    }

    fn enable_column_aware_steps(&mut self) {
        self.push("cap column-aware".to_string());
    }

    fn enable_column_breakpoints_support(&mut self) {
        self.push("cap column-breakpoints".to_string());
    }

    fn enable_column_motions_support(&mut self) {
        self.push("cap column-motions".to_string());
    }

    fn register_path_with_line_lengths(
        &mut self,
        path: &Path,
        line_lengths: &[u32],
    ) -> Result<PathId, Box<dyn std::error::Error>> {
        let id = self.next_path_id;
        self.next_path_id += 1;
        self.push(format!("path {} lines={} -> {}", path.display(), line_lengths.len(), id));
        Ok(PathId(id))
    }

    fn ensure_function_id(&mut self, function_name: &str, path: &Path, line: Line) -> FunctionId {
        let id = self.next_function_id;
        self.next_function_id += 1;
        self.push(format!("function {} at {}:{} -> {}", function_name, path.display(), line.0, id));
        FunctionId(id)
    }

    fn ensure_type_id(&mut self, kind: TypeKind, lang_type: &str) -> TypeId {
        if let Some(index) = self.types.iter().position(|(k, t)| *k == kind && t == lang_type) {
            return TypeId(index);
        }
        let id = self.types.len();
        self.types.push((kind, lang_type.to_string()));
        self.push(format!("type {:?} {} -> {}", kind, lang_type, id));
        TypeId(id)
    }

    fn register_source_view(
        &mut self,
        path: &Path,
        view_kind: u8,
        view_name: &str,
        content: &[u8],
        sourcemap: &[u8],
    ) -> Result<u64, Box<dyn std::error::Error>> {
        self.push(format!(
            "source-view {} kind={} name={} content={} map={}",
            path.display(),
            view_kind,
            view_name,
            content.len(),
            sourcemap.len()
        ));
        Ok(0)
    }

    fn register_step_with_column(&mut self, path: &Path, line: Line, column: Option<Line>) {
        self.push(format!(
            "step {}:{}:{}",
            path.display(),
            line.0,
            column.map(|c| c.0.to_string()).unwrap_or_else(|| "-".to_string())
        ));
    }

    fn register_variable_with_full_value(&mut self, name: &str, value: ValueRecord) {
        self.values.push((name.to_owned(), value.clone()));
        self.push(format!("var {} = {:?}", name, value));
    }

    fn arg(&mut self, name: &str, value: ValueRecord) -> FullValueRecord {
        self.push(format!("arg {} = {:?}", name, value));
        FullValueRecord { variable_id: codetracer_trace_types::VariableId(0), value }
    }

    fn register_call(&mut self, function_id: FunctionId, args: Vec<FullValueRecord>) {
        self.push(format!("call fn={} args={}", function_id.0, args.len()));
    }

    fn register_return(&mut self, return_value: ValueRecord) {
        self.push(format!("return {:?}", return_value));
    }

    fn register_special_event(&mut self, kind: EventLogKind, metadata: &str, content: &str) {
        self.push(format!("event {:?} {} {}", kind, metadata, content));
    }
}

// ---------------------------------------------------------------------------
// Executors under test.
// ---------------------------------------------------------------------------

/// Wraps the executor the tracer would have built and watches every call go past.
///
/// Delegating rather than replacing is the point: `print` and the `__debug_*` calls the variable
/// recorder rests on keep working, so an observed extra call is the injected layer's doing and not
/// the absence of the default's.
struct Observing<D> {
    inner: D,
    seen: std::rc::Rc<std::cell::RefCell<Vec<String>>>,
}

impl<D: TraceForeignCallExecutor> ForeignCallExecutor<FieldElement> for Observing<D> {
    fn execute(
        &mut self,
        foreign_call: &ForeignCallWaitInfo<FieldElement>,
    ) -> Result<ForeignCallResult<FieldElement>, ForeignCallError> {
        self.seen.borrow_mut().push(foreign_call.function.clone());
        self.inner.execute(foreign_call)
    }
}

impl<D: TraceForeignCallExecutor> TraceForeignCallExecutor for Observing<D> {
    fn get_variables(&self) -> Vec<StackFrame<'_, FieldElement>> {
        self.inner.get_variables()
    }

    fn current_stack_frame(&self) -> Option<StackFrame<'_, FieldElement>> {
        self.inner.current_stack_frame()
    }

    fn restart(&mut self, artifact: &DebugArtifact) {
        self.inner.restart(artifact);
    }
}

/// Answers the calls it knows and REFUSES the rest, naming the one it refused.
///
/// The refusal is `ForeignCallError::NoHandler(name)`, which is the ACVM's own "nobody answered
/// this" and carries the oracle's name into the execution error. A handler that returned an empty
/// result instead would let the program continue over a value nobody produced.
struct RefusingUnknown<D> {
    inner: D,
    /// Names this executor answers itself. Everything else that is not the recorder's own
    /// `__debug_*`/`print` traffic is refused.
    served: Vec<String>,
    refused: std::rc::Rc<std::cell::RefCell<Vec<String>>>,
}

impl<D: TraceForeignCallExecutor> ForeignCallExecutor<FieldElement> for RefusingUnknown<D> {
    fn execute(
        &mut self,
        foreign_call: &ForeignCallWaitInfo<FieldElement>,
    ) -> Result<ForeignCallResult<FieldElement>, ForeignCallError> {
        let name = foreign_call.function.as_str();
        if name.starts_with("__debug") || name == "print" {
            return self.inner.execute(foreign_call);
        }
        if self.served.iter().any(|s| s == name) {
            return Ok(ForeignCallResult::default());
        }
        self.refused.borrow_mut().push(name.to_string());
        Err(ForeignCallError::NoHandler(name.to_string()))
    }
}

impl<D: TraceForeignCallExecutor> TraceForeignCallExecutor for RefusingUnknown<D> {
    fn get_variables(&self) -> Vec<StackFrame<'_, FieldElement>> {
        self.inner.get_variables()
    }

    fn current_stack_frame(&self) -> Option<StackFrame<'_, FieldElement>> {
        self.inner.current_stack_frame()
    }

    fn restart(&mut self, artifact: &DebugArtifact) {
        self.inner.restart(artifact);
    }
}

// ---------------------------------------------------------------------------
// Compiling a program in memory, the way `nargo trace` compiles one.
// ---------------------------------------------------------------------------

/// The three `CompileOptions` knobs are `nargo::ops::debug::compile_options_for_debugging`'s:
/// `instrument_debug` injects the `__debug_*` calls the variable recorder reads, and
/// `force_brillig` is what the tracer executes.
fn compile(source: &str) -> CompiledProgram {
    compile_with_files(source, &[])
}

fn compile_with_files(source: &str, files: &[(&str, &str)]) -> CompiledProgram {
    let entry_point = Path::new("src/main.nr");
    let mut file_manager = file_manager_with_stdlib(Path::new(""));
    file_manager.add_file_with_source(entry_point, source.to_string());
    for (path, content) in files {
        file_manager.add_file_with_source(Path::new(path), content.to_string());
    }

    let mut parsed_files = parse_all(&file_manager);
    let debug_instrumenter =
        instrument_package_files(&mut parsed_files, &file_manager, Path::new("src"));

    let mut context = Context::new(file_manager, parsed_files);
    let crate_id = prepare_crate(&mut context, entry_point);
    link_to_debug_crate(&mut context, crate_id);
    context.debug_instrumenter = debug_instrumenter;

    let options = CompileOptions {
        silence_warnings: true,
        deny_warnings: false,
        instrument_debug: true,
        force_brillig: true,
        ..CompileOptions::default()
    };

    let (program, _warnings) = noirc_driver::compile_main(&mut context, crate_id, &options, None)
        .unwrap_or_else(|diagnostics| {
            panic!("the fixture did not compile: {} diagnostic(s)", diagnostics.len())
        });
    program
}

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

fn debug_artifact_of(program: &CompiledProgram) -> DebugArtifact {
    DebugArtifact { debug_symbols: program.debug.clone(), file_map: program.file_map.clone() }
}

/// The initial witness for a program taking one `Field` argument called `x`.
fn witness_for(program: &CompiledProgram, x: u128) -> WitnessMap<FieldElement> {
    let mut inputs = BTreeMap::new();
    inputs
        .insert("x".to_string(), noirc_abi::input_parser::InputValue::Field(FieldElement::from(x)));
    program.abi.encode(&inputs, None).expect("the fixture's ABI accepts one Field named x")
}

fn options() -> TraceOptions {
    // `None` registers paths verbatim, which is what makes the two runs comparable without
    // depending on the process's working directory.
    TraceOptions::with_workdir(None::<PathBuf>)
}

// ---------------------------------------------------------------------------
// The fixtures.
// ---------------------------------------------------------------------------

/// Exercises `print` (a foreign call the DEFAULT executor answers) and the `__debug_*` calls the
/// instrumenter injects. No custom oracle: this is the program tests 1 and 2 compare on.
const PRINTING: &str = r#"
fn main(x: Field) -> pub Field {
    let y = x + 1;
    println(y);
    y
}
"#;

/// Calls an oracle nobody implements, returning NOTHING. The return shape matters: an oracle with
/// no destination slots is the one `layers::Empty`'s empty result satisfies, which is why test 4
/// can be green over it.
const VOID_ORACLE: &str = r#"
#[oracle(m38_void_probe)]
unconstrained fn m38_void_probe_oracle() {}

unconstrained fn call_probe() {
    m38_void_probe_oracle()
}

fn main(x: Field) -> pub Field {
    // Safety: test program
    unsafe {
        call_probe();
    }
    x + 1
}
"#;

// ---------------------------------------------------------------------------
// 1. The default path is unchanged.
// ---------------------------------------------------------------------------

#[test]
fn the_default_executor_path_is_byte_identical_through_the_new_seam() {
    let program = compile(PRINTING);
    let artifact = debug_artifact_of(&program);
    let solver = Bn254BlackBoxSolver::default();

    let mut old = RecordingSink::default();
    trace_circuit(
        &solver,
        &program.program.functions,
        &artifact,
        witness_for(&program, 7),
        &program.program.unconstrained_functions,
        &program.abi.error_types,
        &options(),
        &mut old,
    )
    .expect("the printing fixture traces through the old entry point");

    let mut new = RecordingSink::default();
    trace_circuit_with_executor(
        &solver,
        &program.program.functions,
        &artifact,
        witness_for(&program, 7),
        &program.program.unconstrained_functions,
        &program.abi.error_types,
        &options(),
        &mut new,
        None,
    )
    .expect("the printing fixture traces through the new entry point with no executor");

    // NON-DEGENERACY FIRST. Two empty streams are equal, and the comparison below would pass over
    // a tracer that had stopped recording anything at all.
    assert!(
        old.lines.len() > 20,
        "the printing fixture must produce a real event stream; got {} lines",
        old.lines.len()
    );
    assert!(
        old.lines.iter().any(|l| l.starts_with("step ")),
        "the stream must contain steps: {:?}",
        &old.lines[..old.lines.len().min(8)]
    );
    assert!(
        old.lines.iter().any(|l| l.contains("Hello") || l.starts_with("event ")),
        "the printing fixture must produce a print event: {:?}",
        old.lines.iter().filter(|l| l.starts_with("event ")).collect::<Vec<_>>()
    );

    assert_eq!(
        old.lines, new.lines,
        "passing None must reproduce the default executor's stream exactly"
    );
}

// ---------------------------------------------------------------------------
// 2. An injected executor is the one that runs.
// ---------------------------------------------------------------------------

#[test]
fn an_injected_executor_sees_the_calls_the_recorder_makes() {
    let program = compile(PRINTING);
    let artifact = debug_artifact_of(&program);
    let solver = Bn254BlackBoxSolver::default();

    let seen = std::rc::Rc::new(std::cell::RefCell::new(Vec::new()));
    let inner = DefaultDebugForeignCallExecutor::from_artifact(
        std::io::sink(),
        None,
        &artifact,
        None,
        String::new(),
    );
    let observing = Observing { inner, seen: std::rc::Rc::clone(&seen) };

    let mut sink = RecordingSink::default();
    trace_circuit_with_executor(
        &solver,
        &program.program.functions,
        &artifact,
        witness_for(&program, 7),
        &program.program.unconstrained_functions,
        &program.abi.error_types,
        &options(),
        &mut sink,
        Some(Box::new(observing)),
    )
    .expect("the printing fixture traces with an observing executor");

    let seen = seen.borrow();
    assert!(!seen.is_empty(), "the injected executor must have been consulted at all");
    assert!(
        seen.iter().any(|n| n.starts_with("__debug")),
        "the instrumented program's __debug_* calls must reach the injected executor; saw {:?}",
        seen.iter().take(8).collect::<Vec<_>>()
    );
    assert!(
        seen.iter().any(|n| n == "print"),
        "println's foreign call must reach the injected executor; saw {:?}",
        seen.iter().take(8).collect::<Vec<_>>()
    );
    // The steps still arrive, which is what says the delegation kept the recorder working rather
    // than merely kept it from crashing.
    assert!(
        sink.lines.iter().filter(|l| l.starts_with("step ")).count() > 0,
        "the trace must still carry steps"
    );
}

// ---------------------------------------------------------------------------
// 3 and 4. A refusal names the oracle; the default lets the same call through.
// ---------------------------------------------------------------------------

#[test]
fn an_injected_executor_refuses_an_unserved_oracle_by_name() {
    let program = compile(VOID_ORACLE);
    let artifact = debug_artifact_of(&program);
    let solver = Bn254BlackBoxSolver::default();

    let refused = std::rc::Rc::new(std::cell::RefCell::new(Vec::new()));
    let inner = DefaultDebugForeignCallExecutor::from_artifact(
        std::io::sink(),
        None,
        &artifact,
        None,
        String::new(),
    );
    let refusing = RefusingUnknown { inner, served: vec![], refused: std::rc::Rc::clone(&refused) };

    let mut sink = RecordingSink::default();
    let result = trace_circuit_with_executor(
        &solver,
        &program.program.functions,
        &artifact,
        witness_for(&program, 7),
        &program.program.unconstrained_functions,
        &program.abi.error_types,
        &options(),
        &mut sink,
        Some(Box::new(refusing)),
    );

    let refused = refused.borrow();
    assert_eq!(
        refused.as_slice(),
        ["m38_void_probe"],
        "exactly the one unserved oracle must have been refused, by name"
    );

    // WHAT `trace_circuit` DOES WITH AN EXECUTION ERROR, MEASURED RATHER THAN ASSUMED, because a
    // reader of this file will otherwise expect the opposite.
    //
    // The step loop's error arms all `break` and the function returns `Ok(())`: a recorder records
    // what happened, including that the program stopped, and the caller's `Result` is about
    // whether RECORDING succeeded. The generic arm logs through `tracing::error!` and nothing
    // else. So the refusal is observable in two places and the return value is not one of them —
    // the executor's own ledger, and the length of the trace.
    assert!(
        result.is_ok(),
        "trace_circuit's Result is about recording, not about the program: {:?}",
        result.err().map(|e| e.to_string())
    );

    let refused_steps = sink.lines.iter().filter(|l| l.starts_with("step ")).count();

    // THE DISCRIMINATOR. The same program, the same executor, with that one oracle SERVED: the
    // trace runs to the end. Without this the assertion above is satisfied by a tracer that
    // records nothing at all, and "the loop stopped" would be indistinguishable from "the loop
    // never started".
    let served_refusals = std::rc::Rc::new(std::cell::RefCell::new(Vec::new()));
    let inner = DefaultDebugForeignCallExecutor::from_artifact(
        std::io::sink(),
        None,
        &artifact,
        None,
        String::new(),
    );
    let serving = RefusingUnknown {
        inner,
        served: vec!["m38_void_probe".to_string()],
        refused: std::rc::Rc::clone(&served_refusals),
    };
    let mut served_sink = RecordingSink::default();
    trace_circuit_with_executor(
        &solver,
        &program.program.functions,
        &artifact,
        witness_for(&program, 7),
        &program.program.unconstrained_functions,
        &program.abi.error_types,
        &options(),
        &mut served_sink,
        Some(Box::new(serving)),
    )
    .expect("the served arm records");

    assert!(
        served_refusals.borrow().is_empty(),
        "the served arm must refuse nothing: {:?}",
        served_refusals.borrow()
    );
    let served_steps = served_sink.lines.iter().filter(|l| l.starts_with("step ")).count();
    assert!(
        served_steps > 0,
        "the served arm must produce steps, or the comparison below is between two zeroes"
    );
    assert!(
        refused_steps < served_steps,
        "the refused run must stop short of the served one; refused {refused_steps} steps, served {served_steps}"
    );
    // And it stopped rather than never started: the refusal happens inside `main`, so the steps
    // before the oracle call are recorded.
    assert!(
        refused_steps > 0,
        "the refused run must have recorded the steps it took BEFORE the refusal"
    );
}

#[test]
fn the_default_executor_answers_an_unimplemented_void_oracle_with_an_empty_result() {
    // THE CONTROL FOR THE TEST ABOVE, and a statement about the tracer worth making on its own.
    //
    // `DefaultForeignCallBuilder::build` composes over `layers::Empty`, whose `execute` is
    // `Ok(ForeignCallResult::default())` for every call. So the refusal in the previous test is
    // the INJECTED executor's doing and not something the tracer does anyway — and, separately,
    // `nargo trace` over a program calling an oracle nobody implements does not fail: it
    // continues over an empty answer.
    let program = compile(VOID_ORACLE);
    let artifact = debug_artifact_of(&program);
    let solver = Bn254BlackBoxSolver::default();

    let mut sink = RecordingSink::default();
    let result = trace_circuit(
        &solver,
        &program.program.functions,
        &artifact,
        witness_for(&program, 7),
        &program.program.unconstrained_functions,
        &program.abi.error_types,
        &options(),
        &mut sink,
    );

    assert!(
        result.is_ok(),
        "the default executor answers an unimplemented void oracle rather than refusing it; got {:?}",
        result.err().map(|e| e.to_string())
    );
    assert!(
        sink.lines.iter().any(|l| l.starts_with("step ")),
        "and the program really did run to completion"
    );
}

/// Guards the fixture rather than the tracer: if `WitnessStack` ever stops being reachable the
/// imports above are wrong and the reader should see that here rather than in a type error two
/// hundred lines up.
#[allow(dead_code)]
fn _witness_stack_is_in_scope(_: WitnessStack<FieldElement>) {}

// This sink observes the real compiler and debugger at the trace-event boundary;
// no compiler, execution, or frame state is mocked.
fn trace_call_steps(source: &str) -> Vec<String> {
    trace_call_steps_with_files(source, &[])
}

fn trace_call_steps_with_files(source: &str, files: &[(&str, &str)]) -> Vec<String> {
    let program = compile_with_files(source, files);
    let artifact = debug_artifact_of(&program);
    let solver = Bn254BlackBoxSolver::default();
    let mut sink = RecordingSink::default();
    trace_circuit(
        &solver,
        &program.program.functions,
        &artifact,
        witness_for(&program, 2),
        &program.program.unconstrained_functions,
        &program.abi.error_types,
        &options(),
        &mut sink,
    )
    .expect("call-step program traces");
    sink.lines
}

#[test]
fn main_public_return_value_is_recorded_when_execution_finishes() {
    let lines = trace_call_steps("fn main(x: u32) -> pub u32 {\n    let z = x + 100;\n    z\n}\n");
    assert_eq!(
        lines.iter().filter(|line| line.starts_with("return ")).collect::<Vec<_>>(),
        ["return Int { i: 102, type_id: TypeId(1) }"],
        "main's computed public result must close its call: {lines:#?}"
    );
}

#[test]
fn main_constant_and_array_public_results_are_recorded() {
    for (source, expected) in [
        ("fn main(x: u32) -> pub u32 { 100 }", "return Int { i: 100, type_id: TypeId(1) }"),
        (
            "fn main(x: u32) -> pub [u32; 2] { [x, x + 100] }",
            "return Sequence { elements: [Int { i: 2, type_id: TypeId(1) }, Int { i: 102, type_id: TypeId(1) }], is_slice: false, type_id: TypeId(2) }",
        ),
    ] {
        let lines = trace_call_steps(source);
        assert_eq!(
            lines.iter().filter(|line| line.starts_with("return ")).collect::<Vec<_>>(),
            [expected],
            "the complete typed main result must be recorded: {lines:#?}"
        );
    }
}

#[test]
fn main_return_is_distinct_from_its_callees_return() {
    let lines = trace_call_steps(
        "fn base_damage() -> u32 { 100 }\nfn main(x: u32) -> pub u32 {\n    let damage = base_damage();\n    damage + x\n}\n",
    );
    assert_eq!(
        lines.iter().filter(|line| line.starts_with("return ")).collect::<Vec<_>>(),
        ["return Int { i: 100, type_id: TypeId(1) }", "return Int { i: 102, type_id: TypeId(1) }",],
        "the callee and main must each return their own value: {lines:#?}"
    );
}

#[test]
fn void_and_failed_main_do_not_reuse_a_callees_return_value() {
    for body in ["assert(damage + x == 102);", "assert(damage + x == 102)", "assert(false);"] {
        let lines = trace_call_steps(&format!(
            "fn base_damage() -> u32 {{ 100 }}\nfn main(x: u32) {{\n    let damage = base_damage();\n    {body}\n}}\n",
        ));
        assert_eq!(
            lines.iter().filter(|line| line.starts_with("return ")).collect::<Vec<_>>(),
            ["return Int { i: 100, type_id: TypeId(1) }"],
            "void and failing main must keep their implicit void return: {lines:#?}"
        );
        assert_eq!(
            lines.iter().any(|line| line.starts_with("event Error ")),
            body == "assert(false);",
            "the failing control must actually fail: {lines:#?}"
        );
    }
}

#[test]
fn constant_body_call_has_its_own_step_and_preserves_the_callers_call_site() {
    let lines = trace_call_steps(
        "fn base_damage() -> u32 {\n    100\n}\n\nfn main(x: Field) {\n    let d = base_damage();\n    assert(d as Field + x == 102);\n}\n",
    );
    let call = lines
        .iter()
        .position(|line| line == "call fn=1 args=0")
        .expect("base_damage call must be recorded");
    let returned = call
        + 1
        + lines[call + 1..]
            .iter()
            .position(|line| line.starts_with("return "))
            .expect("callee returns");
    let first_step = lines[call + 1..returned]
        .iter()
        .find(|line| line.starts_with("step "))
        .expect("base_damage must own a step");
    assert!(
        first_step.starts_with("step src/main.nr:1:")
            || first_step.starts_with("step src/main.nr:2:"),
        "constant-body callee must step in its own source; stream: {lines:#?}"
    );
    assert!(
        lines[call + 1..returned]
            .iter()
            .filter(|line| line.starts_with("step "))
            .all(|line| line.starts_with("step src/main.nr:1:")
                || line.starts_with("step src/main.nr:2:")),
        "every callee step stays in its own source: {lines:#?}"
    );
    let before = lines[..call]
        .iter()
        .rposition(|line| line.starts_with("step "))
        .expect("caller must step before entering the callee");
    assert_eq!(lines[before], "step src/main.nr:6:13", "caller keeps its pre-call step");
    assert!(
        lines[before + 1..call].iter().any(|line| line.starts_with("var x = ")),
        "pre-call step carries the caller's x"
    );
    assert!(
        !lines[call + 1..returned].iter().any(|line| line.starts_with("var ")),
        "zero-parameter constant callee has no variables: {lines:#?}"
    );
    assert_eq!(lines[returned], "return Int { i: 100, type_id: TypeId(2) }");
    let resumed = lines[returned + 1..]
        .iter()
        .find(|line| line.starts_with("step "))
        .expect("caller resumes after return");
    assert_eq!(resumed, "step src/main.nr:6:13", "caller resumes at its call site");
}

#[test]
fn local_body_control_and_single_line_constant_keep_their_own_steps() {
    for body in ["100", "let a = 100; a"] {
        let lines = trace_call_steps(&format!(
            "fn base_damage() -> u32 {{ {body} }}\nfn main(x: Field) {{\n    let d = base_damage();\n    assert(d as Field + x == 102);\n}}\n"
        ));
        let call = lines.iter().position(|line| line == "call fn=1 args=0").unwrap();
        let returned = call
            + 1
            + lines[call + 1..].iter().position(|line| line.starts_with("return ")).unwrap();
        let steps: Vec<_> =
            lines[call + 1..returned].iter().filter(|line| line.starts_with("step ")).collect();
        assert!(!steps.is_empty(), "callee must own a step: {lines:#?}");
        assert!(
            steps.iter().all(|line| line.starts_with("step src/main.nr:1:")),
            "callee steps stay in its single-line body: {lines:#?}"
        );
        assert!(
            !lines[call + 1..returned].iter().any(|line| line.starts_with("var x = ")),
            "caller variables stay outside callee: {lines:#?}"
        );
    }
}

#[test]
fn nested_constant_body_call_anchors_in_the_innermost_function() {
    let lines = trace_call_steps(
        "fn base_damage() -> u32 {\n    100\n}\nfn relay() -> u32 {\n    base_damage()\n}\nfn main(x: Field) {\n    let d = relay();\n    assert(d as Field + x == 102);\n}\n",
    );
    let call =
        lines.iter().position(|line| line == "call fn=2 args=0").expect("nested base_damage call");
    let returned =
        call + 1 + lines[call + 1..].iter().position(|line| line.starts_with("return ")).unwrap();
    assert_eq!(
        &lines[call + 1..returned],
        &["step src/main.nr:1:25", "type Int u32 -> 2"],
        "innermost constant call owns only its own empty-frame anchor"
    );
}

#[test]
fn multiline_materialized_body_control_keeps_its_located_step() {
    let lines = trace_call_steps(
        "fn base_damage() -> u32 {\n    let a = 100;\n    a\n}\nfn main(x: Field) {\n    let d = base_damage();\n    assert(d as Field + x == 102);\n}\n",
    );
    let call = lines.iter().position(|line| line == "call fn=1 args=0").unwrap();
    let returned =
        call + 1 + lines[call + 1..].iter().position(|line| line.starts_with("return ")).unwrap();
    let steps: Vec<_> =
        lines[call + 1..returned].iter().filter(|line| line.starts_with("step ")).collect();
    assert_eq!(steps, ["step src/main.nr:2:9"], "materialized-body control");
    assert!(!lines[call + 1..returned].iter().any(|line| line.starts_with("var x = ")));
    assert_eq!(lines[returned], "return Int { i: 100, type_id: TypeId(2) }");
}

#[test]
fn constant_body_in_another_file_does_not_borrow_the_callers_source() {
    let lines = trace_call_steps_with_files(
        "mod damage;\nfn main(x: Field) {\n    let d = damage::base_damage();\n    assert(d as Field + x == 102);\n}\n",
        &[("src/damage.nr", "pub fn base_damage() -> u32 {\n    100\n}\n")],
    );
    let call = lines.iter().position(|line| line == "call fn=1 args=0").unwrap();
    let returned =
        call + 1 + lines[call + 1..].iter().position(|line| line.starts_with("return ")).unwrap();
    let steps: Vec<_> =
        lines[call + 1..returned].iter().filter(|line| line.starts_with("step ")).collect();
    assert!(!steps.is_empty(), "cross-file callee must own a step: {lines:#?}");
    assert!(
        steps.iter().all(|line| line.starts_with("step src/damage.nr:1:")
            || line.starts_with("step src/damage.nr:2:")),
        "every callee step uses the callee's file: {lines:#?}"
    );
    assert!(
        !lines[call + 1..returned].iter().any(|line| line.starts_with("var ")),
        "cross-file constant callee has an empty frame: {lines:#?}"
    );
    assert_eq!(lines[returned], "return Int { i: 100, type_id: TypeId(2) }");
}

#[test]
fn mutable_reference_snapshots_preserve_referents_and_type_identity() {
    let program = compile(
        r#"
struct TestStruct { a: Field, b: u32 }
fn inspect(parameter_s: &mut TestStruct) { let c = parameter_s.b; assert(c == 10); }
fn main(x: Field) {
    let mut q = TestStruct { a: x, b: 10 };
    let s = &mut q;
    inspect(s);
    let mut n: u32 = 5;
    let w = &mut n;
    assert(*w == 5);
}
"#,
    );
    let artifact = debug_artifact_of(&program);
    let mut sink = RecordingSink::default();
    trace_circuit(
        &Bn254BlackBoxSolver,
        &program.program.functions,
        &artifact,
        witness_for(&program, 5),
        &program.program.unconstrained_functions,
        &program.abi.error_types,
        &options(),
        &mut sink,
    )
    .expect("reference fixture traces successfully");
    let first_reference =
        sink.values.iter().find(|(name, _)| name == "s").expect("s binding is visible");
    assert!(
        matches!(&first_reference.1, ValueRecord::Reference { mutable: true, .. }),
        "a mutable reference must carry its referent instead of None: {first_reference:?}"
    );
    for name in ["&mut TestStruct", "&mut u32"] {
        assert!(
            sink.types.iter().any(|(kind, typ)| *kind == TypeKind::Ref && typ == name),
            "reference type must identify its target and mutability: {:?}",
            sink.types
        );
    }
    let type_id = |name: &str| TypeId(sink.types.iter().position(|(_, typ)| typ == name).unwrap());
    let struct_value = ValueRecord::Struct {
        field_values: vec![
            ValueRecord::String {
                text: "0x0000000000000000000000000000000000000000000000000000000000000005"
                    .to_owned(),
                type_id: type_id("Field"),
            },
            ValueRecord::Int { i: 10, type_id: type_id("u32") },
        ],
        type_id: type_id("TestStruct"),
    };
    for (binding, referent, reference_type) in [
        ("s", struct_value.clone(), "&mut TestStruct"),
        ("parameter_s", struct_value, "&mut TestStruct"),
        ("w", ValueRecord::Int { i: 5, type_id: type_id("u32") }, "&mut u32"),
    ] {
        let records: Vec<_> = sink
            .values
            .iter()
            .filter(|(name, _)| name == binding)
            .map(|(_, value)| value)
            .collect();
        assert!(!records.is_empty(), "missing reference binding {binding}");
        let expected = ValueRecord::Reference {
            dereferenced: Box::new(referent),
            address: 0,
            mutable: true,
            type_id: type_id(reference_type),
        };
        for record in records {
            assert_eq!(
                record, &expected,
                "reference binding {binding} must preserve its complete referent"
            );
        }
    }
}

#[test]
fn reference_snapshots_walk_composites_and_nested_references() {
    let program = compile(
        r#"
fn main(x: Field) {
    let mut numbers: [u32; 2] = [3, 7];
    let array_ref = &mut numbers;
    assert(array_ref[1] == 7);
    let nested_ref = &array_ref;
    assert(nested_ref[0] == 3);
    let mut pair = (x, 9u32);
    let tuple_ref = &mut pair;
    assert(tuple_ref.1 == 9);
    let mut empty = ();
    let unit_ref = &mut empty;
}
"#,
    );
    let artifact = debug_artifact_of(&program);
    let mut sink = RecordingSink::default();
    trace_circuit(
        &Bn254BlackBoxSolver,
        &program.program.functions,
        &artifact,
        witness_for(&program, 5),
        &program.program.unconstrained_functions,
        &program.abi.error_types,
        &options(),
        &mut sink,
    )
    .expect("composite reference fixture traces successfully");
    for (reference, target, mutable) in [
        ("array_ref", "numbers", true),
        ("nested_ref", "array_ref", false),
        ("tuple_ref", "pair", true),
        ("unit_ref", "empty", true),
    ] {
        let expected_target =
            &sink.values.iter().find(|(name, _)| name == target).expect("referent is recorded").1;
        let records: Vec<_> = sink.values.iter().filter(|(name, _)| name == reference).collect();
        assert!(!records.is_empty(), "missing reference {reference}");
        for (_, value) in records {
            match value {
                ValueRecord::Reference { dereferenced, mutable: actual_mutable, .. } => {
                    assert_eq!(
                        dereferenced.as_ref(),
                        expected_target,
                        "{reference} must walk the complete referent"
                    );
                    assert_eq!(*actual_mutable, mutable, "{reference} mutability");
                }
                other => panic!("{reference} must be a reference, got {other:?}"),
            }
        }
    }
}
