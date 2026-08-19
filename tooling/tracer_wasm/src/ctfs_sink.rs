//! A [`TraceSink`] that builds a real `.ct` CTFS container **in linear
//! memory**, so a wasm module can hand one back to its host.
//!
//! This is the pure-Rust `CtfsTraceWriter` from `codetracer-trace-format`
//! (branch `wasm/ctfs-writer`) wearing noir's writer-agnostic [`TraceSink`]
//! trait. Nothing here touches the filesystem: the container is assembled in a
//! `Vec<u8>` and taken out with [`CtfsSink::take_container_bytes`].
//!
//! # What this container does NOT carry: columns
//!
//! The pure-Rust writer has no column-bearing step encoder. Concretely:
//! `paths.dat` records are bare path bytes rather than the spec's Layout A
//! (`path_len, path, line_count, line_lengths[]`), its step position packs
//! `(path_id << 32) | line` rather than the spec's `global_position_index`,
//! and there is no `sekDeltaColumn` (tag 0x07) encoder. So it deliberately
//! does not set `meta.dat` capability bits 4 / 6 / 7 -- advertising a
//! capability the bytes do not carry would make a reader ask for columns and
//! decode garbage rather than fail.
//!
//! `trace_circuit` *does* ask for column-aware steps, so the request is
//! dropped here on every trace. That loss is reported, not hidden:
//! [`CtfsSink::dropped_column_awareness`] is true whenever it happened, and
//! the wasm entry points put it in the summary the page renders. The
//! column-aware container is the Nim writer's (`nargo trace`), which cannot
//! target wasm today.
//!
//! # Why the three overridden methods
//!
//! Most of [`TraceSink`] forwards straight to the identically-named
//! `TraceWriter` method. Three do not, because the pure-Rust writer's
//! defaults emit a *different event sequence* than the Nim writer that
//! produces the native `.ct` -- and the counts in
//! `tooling/tracer_wasm/web/compare_fixtures.mjs` are checked against that
//! native container. Each override reproduces exactly what
//! [`crate::MemorySink`] does, which is the sequence already validated against
//! `nargo trace` on all 20 trace fixtures:
//!
//! * `start` -- `AbstractTraceWriter::start` emits `Function`, `Call` and no
//!   entry `Step` at all. The recording must open with a `Step` at the entry
//!   location, so the container is one step short otherwise.
//! * `register_call` -- `AbstractTraceWriter::register_call` synthesizes a
//!   `Step` at the callee's declaration site before every non-toplevel `Call`.
//!   The Noir recorder has already emitted the caller's step itself, so that
//!   would overshoot by exactly one step per non-toplevel call.
//! * `register_path_with_line_lengths` -- the writer's default calls
//!   `register_path` *and then* `ensure_path_id`, and `ensure_path_id`
//!   registers an unseen path again, so a fresh path yields **two** `Path`
//!   events and a shifted path table.
//!
//! `tests/ctfs_container.rs` pins all three by comparing the container's
//! decoded counts against `MemorySink`'s, fixture by fixture.

use std::error::Error;
use std::path::Path;

use codetracer_trace_types::{
    CallRecord, EventLogKind, FullValueRecord, FunctionId, Line, NONE_TYPE_ID, PathId, StepRecord,
    TOP_LEVEL_FUNCTION_ID, TraceLowLevelEvent, TypeId, TypeKind, ValueRecord,
};
use codetracer_trace_writer_rs::ctfs_writer::CtfsTraceWriter;
use codetracer_trace_writer_rs::trace_writer::TraceWriter;
use noir_tracer::TraceSink;

/// Builds a `.ct` CTFS container in memory as the trace is produced.
pub struct CtfsSink {
    writer: CtfsTraceWriter,
}

impl CtfsSink {
    /// A sink that will build a container for `program`, invoked with `args`.
    ///
    /// `recording_id` must be supplied by the host: `wasm32-unknown-unknown`
    /// has neither a wall clock nor a CSPRNG, so the writer cannot mint a
    /// UUIDv7 itself. Passing `None` leaves the writer's deterministic
    /// placeholder in place -- well-formed and monotonic, but identical across
    /// module instances, which makes two recordings collide in a trace store.
    pub fn new(program: &str, args: &[String], recording_id: Option<&str>) -> Self {
        let mut writer = CtfsTraceWriter::new_in_memory(program, args);
        if let Some(id) = recording_id {
            writer.set_recording_id(id.to_string());
        }
        CtfsSink { writer }
    }

    /// The finished container. `Some` only after `finish_writing_trace_events`.
    pub fn take_container_bytes(&mut self) -> Option<Vec<u8>> {
        self.writer.take_container_bytes()
    }

    /// True if a caller asked for column-aware steps and this writer could not
    /// provide them -- see the module docs. Always true for a Noir trace,
    /// since `trace_circuit` latches the capability unconditionally; it is
    /// surfaced anyway so the page states the loss rather than implying
    /// parity.
    pub fn dropped_column_awareness(&self) -> bool {
        self.writer.dropped_column_awareness()
    }
}

impl TraceSink for CtfsSink {
    fn begin_writing_trace_events(&mut self, path: &Path) -> Result<(), Box<dyn Error>> {
        TraceWriter::begin_writing_trace_events(&mut self.writer, path)
    }

    fn finish_writing_trace_events(&mut self) -> Result<(), Box<dyn Error>> {
        TraceWriter::finish_writing_trace_events(&mut self.writer)
    }

    fn close(&mut self) -> Result<(), Box<dyn Error>> {
        TraceWriter::close(&mut self.writer)
    }

    fn set_workdir(&mut self, workdir: &Path) {
        TraceWriter::set_workdir(&mut self.writer, workdir);
    }

    /// Open the recording at `path:line`, mirroring [`crate::MemorySink`].
    ///
    /// Emits, in order, the `<toplevel>` function (id 0), the entry `Step`,
    /// the `<toplevel>` `Call`, and the `None` type (id 0).
    fn start(&mut self, path: &Path, line: Line) {
        let function_id =
            TraceWriter::ensure_function_id(&mut self.writer, "<toplevel>", path, line);
        debug_assert_eq!(function_id, TOP_LEVEL_FUNCTION_ID);
        let path_id = TraceWriter::ensure_path_id(&mut self.writer, path);
        TraceWriter::add_event(
            &mut self.writer,
            TraceLowLevelEvent::Step(StepRecord { path_id, line }),
        );
        TraceWriter::add_event(
            &mut self.writer,
            TraceLowLevelEvent::Call(CallRecord { function_id, args: vec![] }),
        );
        let none_type = TraceWriter::ensure_type_id(&mut self.writer, TypeKind::None, "None");
        debug_assert_eq!(none_type, NONE_TYPE_ID);
    }

    fn enable_column_aware_steps(&mut self) {
        TraceWriter::enable_column_aware_steps(&mut self.writer);
    }

    fn enable_column_breakpoints_support(&mut self) {
        TraceWriter::enable_column_breakpoints_support(&mut self.writer);
    }

    fn enable_column_motions_support(&mut self) {
        TraceWriter::enable_column_motions_support(&mut self.writer);
    }

    /// Intern `path`. The per-line lengths are **dropped** -- this writer has
    /// no `paths.dat` Layout A producer; see the module docs.
    ///
    /// Deliberately `ensure_path_id` only, not the trait default, which would
    /// emit the `Path` event twice for an unseen path.
    fn register_path_with_line_lengths(
        &mut self,
        path: &Path,
        _line_lengths: &[u32],
    ) -> Result<PathId, Box<dyn Error>> {
        Ok(TraceWriter::ensure_path_id(&mut self.writer, path))
    }

    fn ensure_function_id(&mut self, function_name: &str, path: &Path, line: Line) -> FunctionId {
        TraceWriter::ensure_function_id(&mut self.writer, function_name, path, line)
    }

    fn ensure_type_id(&mut self, kind: TypeKind, lang_type: &str) -> TypeId {
        TraceWriter::ensure_type_id(&mut self.writer, kind, lang_type)
    }

    /// Record a step. The column is dropped -- see the module docs.
    fn register_step_with_column(&mut self, path: &Path, line: Line, _column: Option<Line>) {
        TraceWriter::register_step(&mut self.writer, path, line);
    }

    fn register_variable_with_full_value(&mut self, name: &str, value: ValueRecord) {
        TraceWriter::register_variable_with_full_value(&mut self.writer, name, value);
    }

    fn arg(&mut self, name: &str, value: ValueRecord) -> FullValueRecord {
        TraceWriter::arg(&mut self.writer, name, value)
    }

    /// Record a call **without** the writer's synthesized callee step -- see
    /// the module docs.
    fn register_call(&mut self, function_id: FunctionId, args: Vec<FullValueRecord>) {
        if function_id != TOP_LEVEL_FUNCTION_ID {
            for arg in &args {
                TraceWriter::add_event(&mut self.writer, TraceLowLevelEvent::Value(arg.clone()));
            }
        }
        TraceWriter::add_event(
            &mut self.writer,
            TraceLowLevelEvent::Call(CallRecord { function_id, args }),
        );
    }

    fn register_return(&mut self, return_value: ValueRecord) {
        TraceWriter::register_return(&mut self.writer, return_value);
    }

    fn register_special_event(&mut self, kind: EventLogKind, metadata: &str, content: &str) {
        TraceWriter::register_special_event(&mut self.writer, kind, metadata, content);
    }
}

/// Drives a [`CtfsSink`] and a [`MemorySink`](crate::MemorySink) from the same
/// pass, so the container and the event stream the page renders cannot drift.
///
/// The alternative -- tracing twice -- would compile and execute the program
/// twice, and would leave open the possibility of the two runs differing. Here
/// there is exactly one execution and one sequence of `TraceSink` calls; the
/// container is a second consumer of it.
///
/// `MemorySink` is the authority for every interned id. The two sinks intern
/// identically by construction (both assign ids in first-use order, keyed the
/// same way), and each id-returning method **checks** that rather than
/// assuming it: a drift would silently produce a container whose values point
/// at the wrong types.
pub struct TeeSink {
    pub memory: crate::MemorySink,
    pub ctfs: CtfsSink,
}

impl TeeSink {
    pub fn new(program: &str, args: &[String], recording_id: Option<&str>) -> Self {
        TeeSink {
            memory: crate::MemorySink::new(),
            ctfs: CtfsSink::new(program, args, recording_id),
        }
    }
}

impl TraceSink for TeeSink {
    fn begin_writing_trace_events(&mut self, path: &Path) -> Result<(), Box<dyn Error>> {
        self.memory.begin_writing_trace_events(path)?;
        self.ctfs.begin_writing_trace_events(path)
    }

    fn finish_writing_trace_events(&mut self) -> Result<(), Box<dyn Error>> {
        self.memory.finish_writing_trace_events()?;
        self.ctfs.finish_writing_trace_events()
    }

    fn close(&mut self) -> Result<(), Box<dyn Error>> {
        self.memory.close()?;
        self.ctfs.close()
    }

    fn set_workdir(&mut self, workdir: &Path) {
        self.memory.set_workdir(workdir);
        self.ctfs.set_workdir(workdir);
    }

    fn start(&mut self, path: &Path, line: Line) {
        self.memory.start(path, line);
        self.ctfs.start(path, line);
    }

    fn enable_column_aware_steps(&mut self) {
        self.memory.enable_column_aware_steps();
        self.ctfs.enable_column_aware_steps();
    }

    fn enable_column_breakpoints_support(&mut self) {
        self.memory.enable_column_breakpoints_support();
        self.ctfs.enable_column_breakpoints_support();
    }

    fn enable_column_motions_support(&mut self) {
        self.memory.enable_column_motions_support();
        self.ctfs.enable_column_motions_support();
    }

    fn register_path_with_line_lengths(
        &mut self,
        path: &Path,
        line_lengths: &[u32],
    ) -> Result<PathId, Box<dyn Error>> {
        let id = self.memory.register_path_with_line_lengths(path, line_lengths)?;
        let other = self.ctfs.register_path_with_line_lengths(path, line_lengths)?;
        assert_eq!(id, other, "the two sinks disagree on the id of path {}", path.display());
        Ok(id)
    }

    fn ensure_function_id(&mut self, function_name: &str, path: &Path, line: Line) -> FunctionId {
        let id = self.memory.ensure_function_id(function_name, path, line);
        let other = self.ctfs.ensure_function_id(function_name, path, line);
        assert_eq!(id, other, "the two sinks disagree on the id of function {function_name}");
        id
    }

    fn ensure_type_id(&mut self, kind: TypeKind, lang_type: &str) -> TypeId {
        let id = self.memory.ensure_type_id(kind, lang_type);
        let other = self.ctfs.ensure_type_id(kind, lang_type);
        assert_eq!(id, other, "the two sinks disagree on the id of type {lang_type}");
        id
    }

    fn register_step_with_column(&mut self, path: &Path, line: Line, column: Option<Line>) {
        self.memory.register_step_with_column(path, line, column);
        self.ctfs.register_step_with_column(path, line, column);
    }

    fn register_variable_with_full_value(&mut self, name: &str, value: ValueRecord) {
        self.memory.register_variable_with_full_value(name, value.clone());
        self.ctfs.register_variable_with_full_value(name, value);
    }

    fn arg(&mut self, name: &str, value: ValueRecord) -> FullValueRecord {
        let record = self.memory.arg(name, value.clone());
        let other = self.ctfs.arg(name, value);
        assert_eq!(
            record.variable_id, other.variable_id,
            "the two sinks disagree on the id of variable {name}"
        );
        record
    }

    fn register_call(&mut self, function_id: FunctionId, args: Vec<FullValueRecord>) {
        self.memory.register_call(function_id, args.clone());
        self.ctfs.register_call(function_id, args);
    }

    fn register_return(&mut self, return_value: ValueRecord) {
        self.memory.register_return(return_value.clone());
        self.ctfs.register_return(return_value);
    }

    fn register_special_event(&mut self, kind: EventLogKind, metadata: &str, content: &str) {
        self.memory.register_special_event(kind, metadata, content);
        self.ctfs.register_special_event(kind, metadata, content);
    }
}
