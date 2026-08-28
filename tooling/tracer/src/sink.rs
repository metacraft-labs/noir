//! The platform boundary of the tracer.
//!
//! `trace_circuit` used to be typed against
//! `codetracer_trace_writer::trace_writer::TraceWriter` -- which, because of the
//! `package = "codetracer_trace_writer_nim"` rename in the workspace manifest,
//! is the trait of the **Nim-FFI-backed** writer. That writer links a Nim static
//! library and `zstd-sys`, so simply naming its trait made every crate in the
//! tracer's dependency closure unbuildable for `wasm32-unknown-unknown`.
//!
//! [`TraceSink`] is the narrow subset of that trait the recorder actually calls
//! -- 18 methods. It carries no dependency beyond `codetracer_trace_types`,
//! which is pure Rust. Backends are attached from outside:
//!
//! * native: the `nim-writer` feature adds [`NimWriterSink`], so `nargo trace`
//!   drives the exact same Nim writer as before and produces a byte-identical
//!   `.ct`.
//! * wasm: `noir_tracer_wasm` supplies a sink over the pure-Rust writer.
//!
//! Signatures deliberately mirror the Nim writer's trait one-for-one so the
//! native adapter is a pure forward with no adaptation logic that could drift.
//! [`TraceSink::register_source_view`] is the one deliberate deviation; its own
//! doc comment says why.

use std::error::Error;
use std::path::Path;

use codetracer_trace_types::{
    EventLogKind, FullValueRecord, FunctionId, Line, PathId, TypeId, TypeKind, ValueRecord,
};

/// `view_kind` for "this is the original, unmodified source text of the path",
/// as opposed to a formatted/deminified alternative.
///
/// The spec's enum (`codetracer-trace-format-spec/internal-files.md`
/// §"Alternate Source Views (Deminification Support)") is `0` = raw,
/// `1` = `prettier_format`, `2` = `black_format`, `3..=127` reserved,
/// `128..` vendor-specific.  Noir embeds the text the compiler actually
/// compiled, verbatim, so `raw` is the accurate kind — nothing was
/// reformatted and there is no sourcemap to carry.
pub const SOURCE_VIEW_KIND_RAW: u8 = 0;

/// Everything `trace_circuit` needs from a trace destination.
pub trait TraceSink {
    // --- container lifecycle ---
    fn begin_writing_trace_events(&mut self, path: &Path) -> Result<(), Box<dyn Error>>;
    fn finish_writing_trace_events(&mut self) -> Result<(), Box<dyn Error>>;
    fn close(&mut self) -> Result<(), Box<dyn Error>>;
    fn set_workdir(&mut self, workdir: &Path);
    fn start(&mut self, path: &Path, line: Line);

    // --- capability latches (must precede the first Step) ---
    fn enable_column_aware_steps(&mut self);
    fn enable_column_breakpoints_support(&mut self);
    fn enable_column_motions_support(&mut self);

    // --- interning ---
    fn register_path_with_line_lengths(
        &mut self,
        path: &Path,
        line_lengths: &[u32],
    ) -> Result<PathId, Box<dyn Error>>;
    fn ensure_function_id(&mut self, function_name: &str, path: &Path, line: Line) -> FunctionId;
    fn ensure_type_id(&mut self, kind: TypeKind, lang_type: &str) -> TypeId;

    // --- embedded source text ---

    /// Embed the source text of `path` into the container.
    ///
    /// A CodeTracer trace is specified to be **self-contained**: it "includes
    /// all source code and debug symbols needed for executing the replay on a
    /// different machine from where the program was built and recorded"
    /// (`codetracer-specs/Trace-Files/Trace-Files-Overview.md`), and the
    /// seek-based reader's `source_line(path_id, line)` is defined against
    /// "the trace's embedded source files"
    /// (`Trace-Files/Seek-Based-CTFS-Reader.md`).  Without this call a viewer
    /// can step through the recording but has nothing to display.
    ///
    /// **Deviation from the writer trait, on purpose.** The Nim writer's
    /// `register_source_view` takes a `PathId`, but the Nim FFI gives no way
    /// to *obtain* one: `trace_writer_register_path_with_line_lengths` returns
    /// only a status code, so `NimTraceWriter::register_path_with_line_lengths`
    /// hands back a placeholder `PathId(0)`, and the writer's internal
    /// `registeredPathId` lookup is not exported. Taking a `&Path` here keeps
    /// that gap where it belongs — inside the backend that has it — instead of
    /// making the recorder reconstruct writer-private id bookkeeping. Sinks
    /// with real path ids (the wasm `MemorySink`) resolve it exactly; the Nim
    /// adapter mirrors the writer's append-order interning and says so.
    ///
    /// `view_kind` follows the spec enum ([`SOURCE_VIEW_KIND_RAW`] for
    /// verbatim source). `sourcemap` is Sourcemap V3 JSON bytes, or empty for
    /// "no sourcemap". Returns the view's 0-based index.
    fn register_source_view(
        &mut self,
        path: &Path,
        view_kind: u8,
        view_name: &str,
        content: &[u8],
        sourcemap: &[u8],
    ) -> Result<u64, Box<dyn Error>>;

    // --- the event stream ---
    fn register_step_with_column(&mut self, path: &Path, line: Line, column: Option<Line>);
    fn register_variable_with_full_value(&mut self, name: &str, value: ValueRecord);
    fn arg(&mut self, name: &str, value: ValueRecord) -> FullValueRecord;
    fn register_call(&mut self, function_id: FunctionId, args: Vec<FullValueRecord>);
    fn register_return(&mut self, return_value: ValueRecord);
    fn register_special_event(&mut self, kind: EventLogKind, metadata: &str, content: &str);
}

#[cfg(feature = "nim-writer")]
pub use nim_writer_impl::NimWriterSink;

/// Adapter over the Nim-FFI writer, used by the native `nargo trace`.
///
/// A newtype rather than a blanket `impl<T: TraceWriter> TraceSink for T`
/// because `create_trace_writer` hands back a `Box<dyn TraceWriter + Send>`, and
/// Rust will not coerce one trait object into an unrelated one; wrapping the
/// `&mut dyn TraceWriter` in a `Sized` type restores the coercion.
///
/// Every method is a straight forward, so the produced container is unchanged
/// from before `TraceSink` was introduced.
#[cfg(feature = "nim-writer")]
mod nim_writer_impl {
    use super::*;
    use codetracer_trace_writer::trace_writer::TraceWriter;
    use std::collections::HashMap;
    use std::path::PathBuf;

    pub struct NimWriterSink<'a> {
        writer: &'a mut (dyn TraceWriter + 'a),
        /// Mirror of the writer's path interning table, needed only by
        /// [`TraceSink::register_source_view`] — see its doc comment for why
        /// the id cannot simply be asked for.
        ///
        /// The Nim writer appends to `msWriter.paths` and never reorders or
        /// removes, so the Nth *distinct* path it interns has id `N`. This map
        /// reproduces that counter from the calls that pass through the
        /// adapter.
        path_ids: HashMap<PathBuf, PathId>,
        /// Set once the recording has emitted its first step, after which
        /// `path_ids` can no longer be trusted: `start` and
        /// `register_step_with_column` let the writer intern paths implicitly,
        /// and the adapter cannot see the ids those produce. Resolving a path
        /// after that point would risk attaching source text to the *wrong*
        /// file, so it is refused loudly instead. The recorder registers every
        /// source view up front, before any step, so this never fires in
        /// practice — it exists so that a future caller which does not gets an
        /// error rather than a silently mislabelled container.
        stepping: bool,
    }

    impl<'a> NimWriterSink<'a> {
        pub fn new(writer: &'a mut (dyn TraceWriter + 'a)) -> Self {
            Self { writer, path_ids: HashMap::new(), stepping: false }
        }
    }

    impl TraceSink for NimWriterSink<'_> {
        fn begin_writing_trace_events(&mut self, path: &Path) -> Result<(), Box<dyn Error>> {
            TraceWriter::begin_writing_trace_events(self.writer, path)
        }
        fn finish_writing_trace_events(&mut self) -> Result<(), Box<dyn Error>> {
            TraceWriter::finish_writing_trace_events(self.writer)
        }
        fn close(&mut self) -> Result<(), Box<dyn Error>> {
            TraceWriter::close(self.writer)
        }
        fn set_workdir(&mut self, workdir: &Path) {
            TraceWriter::set_workdir(self.writer, workdir);
        }
        fn start(&mut self, path: &Path, line: Line) {
            // `start` emits the entry Step, which lets the writer intern a
            // path the adapter never saw registered; from here on the
            // `path_ids` mirror is no longer authoritative.
            self.stepping = true;
            TraceWriter::start(self.writer, path, line);
        }
        fn enable_column_aware_steps(&mut self) {
            TraceWriter::enable_column_aware_steps(self.writer);
        }
        fn enable_column_breakpoints_support(&mut self) {
            TraceWriter::enable_column_breakpoints_support(self.writer);
        }
        fn enable_column_motions_support(&mut self) {
            TraceWriter::enable_column_motions_support(self.writer);
        }
        fn register_path_with_line_lengths(
            &mut self,
            path: &Path,
            line_lengths: &[u32],
        ) -> Result<PathId, Box<dyn Error>> {
            let result =
                TraceWriter::register_path_with_line_lengths(self.writer, path, line_lengths);
            // The returned `PathId` is the Nim backend's placeholder `PathId(0)`
            // (the FFI reports only success/failure), so track the real id
            // ourselves: the writer appends each newly interned path, and a
            // re-registration of a path it already knows is a no-op that does
            // NOT advance the counter.
            if result.is_ok() && !self.stepping {
                let next = PathId(self.path_ids.len());
                self.path_ids.entry(path.to_path_buf()).or_insert(next);
            }
            result
        }
        fn ensure_function_id(
            &mut self,
            function_name: &str,
            path: &Path,
            line: Line,
        ) -> FunctionId {
            TraceWriter::ensure_function_id(self.writer, function_name, path, line)
        }
        fn ensure_type_id(&mut self, kind: TypeKind, lang_type: &str) -> TypeId {
            TraceWriter::ensure_type_id(self.writer, kind, lang_type)
        }
        fn register_source_view(
            &mut self,
            path: &Path,
            view_kind: u8,
            view_name: &str,
            content: &[u8],
            sourcemap: &[u8],
        ) -> Result<u64, Box<dyn Error>> {
            if self.stepping {
                return Err(format!(
                    "register_source_view({}) after the first step: the Nim writer \
                     interns paths implicitly while stepping and exports no \
                     path-id lookup, so the id mirror is no longer trustworthy. \
                     Register source views before recording starts.",
                    path.display()
                )
                .into());
            }
            let Some(path_id) = self.path_ids.get(path).copied() else {
                return Err(format!(
                    "register_source_view({}): path was never registered on this \
                     writer; call register_path_with_line_lengths first",
                    path.display()
                )
                .into());
            };
            TraceWriter::register_source_view(
                self.writer,
                path_id,
                view_kind,
                view_name,
                content,
                sourcemap,
            )
        }
        fn register_step_with_column(&mut self, path: &Path, line: Line, column: Option<Line>) {
            self.stepping = true;
            TraceWriter::register_step_with_column(self.writer, path, line, column);
        }
        fn register_variable_with_full_value(&mut self, name: &str, value: ValueRecord) {
            TraceWriter::register_variable_with_full_value(self.writer, name, value);
        }
        fn arg(&mut self, name: &str, value: ValueRecord) -> FullValueRecord {
            TraceWriter::arg(self.writer, name, value)
        }
        fn register_call(&mut self, function_id: FunctionId, args: Vec<FullValueRecord>) {
            TraceWriter::register_call(self.writer, function_id, args);
        }
        fn register_return(&mut self, return_value: ValueRecord) {
            TraceWriter::register_return(self.writer, return_value);
        }
        fn register_special_event(&mut self, kind: EventLogKind, metadata: &str, content: &str) {
            TraceWriter::register_special_event(self.writer, kind, metadata, content);
        }
    }
}
