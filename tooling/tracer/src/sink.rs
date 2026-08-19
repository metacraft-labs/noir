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
//! -- 17 methods. It carries no dependency beyond `codetracer_trace_types`,
//! which is pure Rust. Backends are attached from outside:
//!
//! * native: the `nim-writer` feature adds [`NimWriterSink`], so `nargo trace`
//!   drives the exact same Nim writer as before and produces a byte-identical
//!   `.ct`.
//! * wasm: `noir_tracer_wasm` supplies a sink over the pure-Rust writer.
//!
//! Signatures deliberately mirror the Nim writer's trait one-for-one so the
//! native adapter is a pure forward with no adaptation logic that could drift.

use std::error::Error;
use std::path::Path;

use codetracer_trace_types::{
    EventLogKind, FullValueRecord, FunctionId, Line, PathId, TypeId, TypeKind, ValueRecord,
};

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

    pub struct NimWriterSink<'a>(&'a mut (dyn TraceWriter + 'a));

    impl<'a> NimWriterSink<'a> {
        pub fn new(writer: &'a mut (dyn TraceWriter + 'a)) -> Self {
            Self(writer)
        }
    }

    impl TraceSink for NimWriterSink<'_> {
        fn begin_writing_trace_events(&mut self, path: &Path) -> Result<(), Box<dyn Error>> {
            TraceWriter::begin_writing_trace_events(self.0, path)
        }
        fn finish_writing_trace_events(&mut self) -> Result<(), Box<dyn Error>> {
            TraceWriter::finish_writing_trace_events(self.0)
        }
        fn close(&mut self) -> Result<(), Box<dyn Error>> {
            TraceWriter::close(self.0)
        }
        fn set_workdir(&mut self, workdir: &Path) {
            TraceWriter::set_workdir(self.0, workdir);
        }
        fn start(&mut self, path: &Path, line: Line) {
            TraceWriter::start(self.0, path, line);
        }
        fn enable_column_aware_steps(&mut self) {
            TraceWriter::enable_column_aware_steps(self.0);
        }
        fn enable_column_breakpoints_support(&mut self) {
            TraceWriter::enable_column_breakpoints_support(self.0);
        }
        fn enable_column_motions_support(&mut self) {
            TraceWriter::enable_column_motions_support(self.0);
        }
        fn register_path_with_line_lengths(
            &mut self,
            path: &Path,
            line_lengths: &[u32],
        ) -> Result<PathId, Box<dyn Error>> {
            TraceWriter::register_path_with_line_lengths(self.0, path, line_lengths)
        }
        fn ensure_function_id(
            &mut self,
            function_name: &str,
            path: &Path,
            line: Line,
        ) -> FunctionId {
            TraceWriter::ensure_function_id(self.0, function_name, path, line)
        }
        fn ensure_type_id(&mut self, kind: TypeKind, lang_type: &str) -> TypeId {
            TraceWriter::ensure_type_id(self.0, kind, lang_type)
        }
        fn register_step_with_column(&mut self, path: &Path, line: Line, column: Option<Line>) {
            TraceWriter::register_step_with_column(self.0, path, line, column);
        }
        fn register_variable_with_full_value(&mut self, name: &str, value: ValueRecord) {
            TraceWriter::register_variable_with_full_value(self.0, name, value);
        }
        fn arg(&mut self, name: &str, value: ValueRecord) -> FullValueRecord {
            TraceWriter::arg(self.0, name, value)
        }
        fn register_call(&mut self, function_id: FunctionId, args: Vec<FullValueRecord>) {
            TraceWriter::register_call(self.0, function_id, args);
        }
        fn register_return(&mut self, return_value: ValueRecord) {
            TraceWriter::register_return(self.0, return_value);
        }
        fn register_special_event(&mut self, kind: EventLogKind, metadata: &str, content: &str) {
            TraceWriter::register_special_event(self.0, kind, metadata, content);
        }
    }
}
