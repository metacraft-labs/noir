//! Turn an in-memory recording into a `.ct` CTFS container.
//!
//! The browser records with [`crate::MemorySink`], which keeps the CodeTracer
//! low-level event stream plus what the stream cannot carry (per-path line
//! lengths, per-step columns, the capability latches). This module replays
//! that recording, in order, into the pure-Rust `CtfsTraceWriter` writing to
//! memory, and hands back the finished container: a browser recording is then
//! the same artefact a native `nargo trace` writes, opened by the same reader.
//!
//! Interning is positional on both sides — a path, function, type or variable
//! id is its registration order — and the replay registers each one at the
//! event that introduced it, so every id in the stream means the same entry
//! in the container.
//!
//! Source text is NOT put into the container: the pure-Rust writer has no
//! source-view stream. It travels beside the container, in the trace result
//! (`TraceResult::source_views`), and the host writes it where the replay
//! engine reads source from.

use std::error::Error;
use std::path::Path;

use codetracer_trace_types::{Line, TraceLowLevelEvent};
use codetracer_trace_writer_rs::ctfs_writer::CtfsTraceWriter;
use codetracer_trace_writer_rs::trace_writer::TraceWriter;

use crate::MemoryTrace;

/// Encode `trace` as a CTFS container and return its bytes.
///
/// `recording_id` is the container's UUIDv7 recording id. A wasm sandbox has
/// neither a wall clock nor an entropy source to mint one, so the host
/// supplies it; `None` lets the writer mint one where it can.
pub fn encode_container(
    trace: &MemoryTrace,
    program: &str,
    recording_id: Option<&str>,
) -> Result<Vec<u8>, Box<dyn Error>> {
    let step_count =
        trace.events.iter().filter(|e| matches!(e, TraceLowLevelEvent::Step(_))).count();
    if trace.step_columns.len() != step_count {
        return Err(format!(
            "the recording has {step_count} step(s) but {} step column(s); \
             the two must run in step",
            trace.step_columns.len()
        )
        .into());
    }

    let mut writer = CtfsTraceWriter::new_in_memory(program, &[]);
    if let Some(id) = recording_id {
        writer.set_recording_id(id);
    }
    if let Some(workdir) = &trace.workdir {
        TraceWriter::set_workdir(&mut writer, workdir);
    }
    if trace.capabilities.column_aware_steps {
        TraceWriter::enable_column_aware_steps(&mut writer);
    }
    if trace.capabilities.column_breakpoints {
        TraceWriter::enable_column_breakpoints_support(&mut writer);
    }
    if trace.capabilities.column_motions {
        TraceWriter::enable_column_motions_support(&mut writer);
    }
    TraceWriter::begin_writing_trace_events(&mut writer, Path::new("trace"))?;

    let mut columns = trace.step_columns.iter();
    for event in &trace.events {
        match event {
            TraceLowLevelEvent::Path(path) => {
                let id = trace.paths.iter().position(|p| p == path).ok_or_else(|| {
                    format!("Path record {} is not in the path table", path.display())
                })?;
                TraceWriter::register_path_with_line_lengths(
                    &mut writer,
                    path,
                    &trace.line_lengths[id],
                )?;
            }
            TraceLowLevelEvent::Function(f) => {
                let path = path_of(trace, f.path_id.0)?;
                TraceWriter::ensure_function_id(&mut writer, &f.name, path, f.line);
            }
            TraceLowLevelEvent::Type(t) => {
                TraceWriter::ensure_raw_type_id(&mut writer, t.clone());
            }
            TraceLowLevelEvent::VariableName(name) => {
                TraceWriter::ensure_variable_id(&mut writer, name);
            }
            TraceLowLevelEvent::Step(step) => {
                let path = path_of(trace, step.path_id.0)?;
                let column: Option<Line> = *columns.next().expect("counted above");
                TraceWriter::register_step_with_column(&mut writer, path, step.line, column);
            }
            // `Call` is added as recorded: the writer's own `register_call`
            // would synthesize a step at the callee's declaration, which the
            // recorder has not taken and the native writer does not add.
            other => TraceWriter::add_event(&mut writer, other.clone()),
        }
    }

    TraceWriter::finish_writing_trace_events(&mut writer)?;
    writer.take_container_bytes().ok_or_else(|| "the in-memory writer produced no container".into())
}

fn path_of(trace: &MemoryTrace, id: usize) -> Result<&Path, Box<dyn Error>> {
    trace
        .paths
        .get(id)
        .map(|p| p.as_path())
        .ok_or_else(|| format!("path id {id} is not in the path table").into())
}
