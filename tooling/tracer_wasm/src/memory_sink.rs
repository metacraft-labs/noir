//! An in-memory [`TraceSink`] that accumulates the CodeTracer low-level event
//! stream instead of writing a container.
//!
//! ## Why this exists rather than a dependency on `codetracer_trace_writer`
//!
//! There is, as of `codetracer-trace-format` v0.19.0, **no writer that can
//! produce a `.ct` CTFS container from a wasm target**:
//!
//! * `codetracer_trace_writer_nim` links a Nim static library and `zstd-sys`.
//! * the pure-Rust `codetracer_trace_writer` gates `ctfs_writer` behind
//!   `#[cfg(not(target_arch = "wasm32"))]`, and `create_trace_writer(.., Ctfs)`
//!   is a `panic!("CTFS format is not supported on wasm32")` there. It also
//!   pulls `codetracer_ctfs` -> `zstd` (C, unconditional) and
//!   `codetracer_trace_format_capnp`, whose build script requires the `capnp`
//!   compiler on the host, and its wasm `ruzstd` dependency has a higher MSRV
//!   than noir's pinned toolchain.
//!
//! So the wasm side stops at the event stream and hands it to the host, which
//! can serialize it or feed it to a native container writer. The event
//! semantics -- interning order, the implicit `Step` before a non-toplevel
//! `Call`, `<toplevel>` being function 0 and `None` being type 0 -- mirror
//! `codetracer_trace_writer::abstract_trace_writer::AbstractTraceWriter`
//! exactly, so the produced stream is the same one that writer would have
//! buffered.
//!
//! Columns: `register_step_with_column` drops the column, because the
//! `StepRecord` in `codetracer_trace_types` carries only `(path_id, line)`.
//! The pure-Rust writer drops it at the same place and for the same reason;
//! only the Nim writer's `DeltaColumn` follow-up event preserves it. The
//! capability latches are recorded on the sink so a host that later encodes a
//! container can set the corresponding `meta.dat` flags.

use std::collections::HashMap;
use std::error::Error;
use std::path::{Path, PathBuf};

use codetracer_trace_types::{
    CallRecord, EventLogKind, FullValueRecord, FunctionId, FunctionRecord, Line, NONE_TYPE_ID,
    PathId, RecordEvent, ReturnRecord, StepRecord, TOP_LEVEL_FUNCTION_ID, TraceLowLevelEvent,
    TypeId, TypeKind, TypeRecord, TypeSpecificInfo, ValueRecord, VariableId,
};
use noir_tracer::TraceSink;

/// The capability latches `trace_circuit` sets before emitting any step.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, serde::Serialize)]
pub struct Capabilities {
    pub column_aware_steps: bool,
    pub column_breakpoints: bool,
    pub column_motions: bool,
}

/// The whole recording, in memory.
#[derive(Debug, Default, serde::Serialize)]
pub struct MemoryTrace {
    pub events: Vec<TraceLowLevelEvent>,
    pub paths: Vec<PathBuf>,
    /// Per-path UTF-8 byte lengths, indexed in step with `paths`. The CTFS
    /// `paths.dat` Layout A needs these to recover columns; nothing in the
    /// low-level event stream carries them, so they are kept alongside.
    pub line_lengths: Vec<Vec<u32>>,
    /// The source text of each registered path, in registration order — the
    /// in-memory stand-in for the container's `source_views.dat`. Kept so a
    /// wasm-side recording can still be turned into a *self-contained*
    /// container by the host; see [`MemorySink::register_source_view`].
    pub source_views: Vec<SourceView>,
    pub capabilities: Capabilities,
    pub workdir: Option<PathBuf>,
}

/// One embedded view of a source path (spec §"Alternate Source Views").
///
/// For Noir this is always the verbatim compiled text
/// (`view_kind == noir_tracer::SOURCE_VIEW_KIND_RAW`, empty `sourcemap`), but
/// the record mirrors the writer's full shape so a host encoder can forward it
/// unchanged.
#[derive(Clone, Debug, serde::Serialize)]
pub struct SourceView {
    pub path_id: PathId,
    pub view_kind: u8,
    pub view_name: String,
    pub content: Vec<u8>,
    pub sourcemap: Vec<u8>,
}

pub struct MemorySink {
    trace: MemoryTrace,
    path_ids: HashMap<PathBuf, PathId>,
    function_ids: HashMap<String, FunctionId>,
    function_list: Vec<(String, PathId, Line)>,
    type_ids: HashMap<String, TypeId>,
    variable_ids: HashMap<String, VariableId>,
}

impl Default for MemorySink {
    fn default() -> Self {
        Self::new()
    }
}

impl MemorySink {
    pub fn new() -> Self {
        MemorySink {
            trace: MemoryTrace::default(),
            path_ids: HashMap::new(),
            function_ids: HashMap::new(),
            function_list: Vec::new(),
            type_ids: HashMap::new(),
            variable_ids: HashMap::new(),
        }
    }

    pub fn into_trace(self) -> MemoryTrace {
        self.trace
    }

    pub fn trace(&self) -> &MemoryTrace {
        &self.trace
    }

    fn push(&mut self, event: TraceLowLevelEvent) {
        self.trace.events.push(event);
    }

    fn ensure_path_id(&mut self, path: &Path) -> PathId {
        if let Some(id) = self.path_ids.get(path) {
            return *id;
        }
        let id = PathId(self.path_ids.len());
        self.path_ids.insert(path.to_path_buf(), id);
        self.trace.paths.push(path.to_path_buf());
        self.trace.line_lengths.push(Vec::new());
        self.push(TraceLowLevelEvent::Path(path.to_path_buf()));
        id
    }

    fn ensure_variable_id(&mut self, name: &str) -> VariableId {
        if let Some(id) = self.variable_ids.get(name) {
            return *id;
        }
        let id = VariableId(self.variable_ids.len());
        self.variable_ids.insert(name.to_string(), id);
        self.push(TraceLowLevelEvent::VariableName(name.to_string()));
        id
    }
}

impl TraceSink for MemorySink {
    fn begin_writing_trace_events(&mut self, _path: &Path) -> Result<(), Box<dyn Error>> {
        Ok(())
    }

    fn finish_writing_trace_events(&mut self) -> Result<(), Box<dyn Error>> {
        Ok(())
    }

    fn close(&mut self) -> Result<(), Box<dyn Error>> {
        Ok(())
    }

    fn set_workdir(&mut self, workdir: &Path) {
        self.trace.workdir = Some(workdir.to_path_buf());
    }

    /// Open the recording at `path:line`.
    ///
    /// Emits, in order, the `<toplevel>` function (id 0), the `<toplevel>`
    /// Call, the entry Step, and the `None` type (id 0). The entry Step is the
    /// reason the native container reports exactly one more step than the
    /// recorder's own `register_step` calls.
    ///
    /// ## Why the Call is pushed BEFORE the Step
    ///
    /// CodeTracer's `TraceProcessor` opens a frame when it reads a `Call` and
    /// attributes every subsequent `Step` to the frame that is open. A `Step`
    /// that arrives with no open call makes it synthesize a `<top-level>`
    /// frame of its own — and that synthetic frame then shadows both this
    /// recording's `<toplevel>` and the program's `main`. Measured against the
    /// `.ct` container the native writer produces for the same fixture: one
    /// frame named `main` becomes a three-frame stack with `main` nowhere in
    /// it. The order below is the order the native writer emits, and
    /// `tests/trace_artifact.rs::the_entry_call_precedes_the_entry_step`
    /// holds it there.
    fn start(&mut self, path: &Path, line: Line) {
        let function_id = self.ensure_function_id("<toplevel>", path, line);
        debug_assert_eq!(function_id, TOP_LEVEL_FUNCTION_ID);
        let path_id = self.ensure_path_id(path);
        self.push(TraceLowLevelEvent::Call(CallRecord { function_id, args: vec![] }));
        self.push(TraceLowLevelEvent::Step(StepRecord { path_id, line }));
        let none_type = self.ensure_type_id(TypeKind::None, "None");
        debug_assert_eq!(none_type, NONE_TYPE_ID);
    }

    fn enable_column_aware_steps(&mut self) {
        self.trace.capabilities.column_aware_steps = true;
    }

    fn enable_column_breakpoints_support(&mut self) {
        self.trace.capabilities.column_breakpoints = true;
    }

    fn enable_column_motions_support(&mut self) {
        self.trace.capabilities.column_motions = true;
    }

    fn register_path_with_line_lengths(
        &mut self,
        path: &Path,
        line_lengths: &[u32],
    ) -> Result<PathId, Box<dyn Error>> {
        let id = self.ensure_path_id(path);
        // Match the Nim writer, which ignores a re-registration of an
        // already-interned path rather than overwriting its table.
        if self.trace.line_lengths[id.0].is_empty() {
            self.trace.line_lengths[id.0] = line_lengths.to_vec();
        }
        Ok(id)
    }

    fn ensure_function_id(&mut self, function_name: &str, path: &Path, line: Line) -> FunctionId {
        if let Some(id) = self.function_ids.get(function_name) {
            return *id;
        }
        let id = FunctionId(self.function_ids.len());
        self.function_ids.insert(function_name.to_string(), id);
        let path_id = self.ensure_path_id(path);
        self.function_list.push((function_name.to_string(), path_id, line));
        self.push(TraceLowLevelEvent::Function(FunctionRecord {
            name: function_name.to_string(),
            path_id,
            line,
        }));
        id
    }

    /// Keep the embedded source text alongside the event stream.
    ///
    /// Nothing in `TraceLowLevelEvent` can carry it (the CTFS
    /// `source_views.dat` stream has no low-level-event equivalent), so it
    /// lands in `MemoryTrace::source_views` next to `line_lengths`, which is
    /// there for the same reason. A host that later encodes a container feeds
    /// these to the writer's `register_source_view` so the wasm-recorded
    /// container is as self-contained as the native one.
    fn register_source_view(
        &mut self,
        path: &Path,
        view_kind: u8,
        view_name: &str,
        content: &[u8],
        sourcemap: &[u8],
    ) -> Result<u64, Box<dyn Error>> {
        let path_id = self.ensure_path_id(path);
        let index = self.trace.source_views.len() as u64;
        self.trace.source_views.push(SourceView {
            path_id,
            view_kind,
            view_name: view_name.to_string(),
            content: content.to_vec(),
            sourcemap: sourcemap.to_vec(),
        });
        Ok(index)
    }

    fn ensure_type_id(&mut self, kind: TypeKind, lang_type: &str) -> TypeId {
        if let Some(id) = self.type_ids.get(lang_type) {
            return *id;
        }
        let id = TypeId(self.type_ids.len());
        self.type_ids.insert(lang_type.to_string(), id);
        self.push(TraceLowLevelEvent::Type(TypeRecord {
            kind,
            lang_type: lang_type.to_string(),
            specific_info: TypeSpecificInfo::None,
        }));
        id
    }

    fn register_step_with_column(&mut self, path: &Path, line: Line, _column: Option<Line>) {
        let path_id = self.ensure_path_id(path);
        self.push(TraceLowLevelEvent::Step(StepRecord { path_id, line }));
    }

    fn register_variable_with_full_value(&mut self, name: &str, value: ValueRecord) {
        let variable_id = self.ensure_variable_id(name);
        self.push(TraceLowLevelEvent::Value(FullValueRecord { variable_id, value }));
    }

    fn arg(&mut self, name: &str, value: ValueRecord) -> FullValueRecord {
        let variable_id = self.ensure_variable_id(name);
        FullValueRecord { variable_id, value }
    }

    /// Record a call.
    ///
    /// Note: unlike
    /// `codetracer_trace_writer::abstract_trace_writer::AbstractTraceWriter`,
    /// this does **not** synthesize a `Step` at the callee's declaration site
    /// before the `Call`. The Nim writer that produces the native `.ct` does not
    /// either -- verified by comparing step counts against `ct-print --full`
    /// across the `test_programs/trace` fixtures, where the auto-step made the
    /// in-memory stream overshoot by exactly one step per non-toplevel call.
    /// The recorder has already emitted the caller's step itself.
    fn register_call(&mut self, function_id: FunctionId, args: Vec<FullValueRecord>) {
        if function_id != TOP_LEVEL_FUNCTION_ID {
            for arg in &args {
                self.push(TraceLowLevelEvent::Value(arg.clone()));
            }
        }
        self.push(TraceLowLevelEvent::Call(CallRecord { function_id, args }));
    }

    fn register_return(&mut self, return_value: ValueRecord) {
        self.push(TraceLowLevelEvent::Return(ReturnRecord { return_value }));
    }

    fn register_special_event(&mut self, kind: EventLogKind, metadata: &str, content: &str) {
        self.push(TraceLowLevelEvent::Event(RecordEvent {
            kind,
            metadata: metadata.to_string(),
            content: content.to_string(),
        }));
    }
}
