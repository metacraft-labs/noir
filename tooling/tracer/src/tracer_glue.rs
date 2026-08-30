use crate::{SourceLocation, StackFrame, stack_frame::Variable};

use crate::sink::TraceSink;
use acvm::FieldElement;
use acvm::acir::AcirField; // necessary, for `to_i128` and `to_hex` to work
use codetracer_trace_types::{EventLogKind, FullValueRecord, Line, TypeKind, ValueRecord};
use noirc_printable_type::{PrintableType, PrintableValue};
use std::path::{Path, PathBuf};

/// Initialize the trace writer for emitting a CTFS `.ct` container.
///
/// `tracer` is any [`TraceSink`]. The native `nargo trace` passes a
/// `NimTraceWriter` from `codetracer_trace_writer_nim` (reachable through this
/// crate's default-off `nim-writer` feature), whose Nim-FFI backend writes the
/// v4 multi-stream layout that `codetracer-trace-format-nim/ct-print`
/// understands.
///
/// `workdir` is baked into the container metadata so `ct-print --strip-paths`
/// can normalise recorded paths; pass `None` on targets with no working
/// directory. It used to be read from `std::env::current_dir()`.
///
/// The writer packages events, metadata and source paths into a single
/// `<program>.ct` file in `out_dir`. The `program` argument is used both
/// as the file basename and embedded in the container's `meta.dat`.
///
/// No legacy `trace.json` / `trace_metadata.json` / `trace_paths.json`
/// sidecars are emitted — the codetracer db-backend has rejected those
/// bundles since the 2026-05 convention compliance pass (see
/// `codetracer-specs/Trace-Files/CTFS-Migration-Guide.md`).  The
/// multi-stream writer mints a UUIDv7 `recording_id` (M-REC-1) and
/// embeds it into `meta.dat` automatically at `close()` time, so we no
/// longer need to call `begin_writing_trace_metadata` /
/// `begin_writing_trace_paths` to register sidecar paths.
pub fn begin_trace(
    tracer: &mut dyn TraceSink,
    out_dir: &str,
    program: &str,
    workdir: Option<&Path>,
) {
    // The Nim writer derives the actual `.ct` path by replacing the
    // supplied path's extension with `.ct`. Passing
    // `<out_dir>/<program>` therefore yields `<out_dir>/<program>.ct`.
    let trace_path = Path::new(out_dir).join(program);
    if let Err(err) = TraceSink::begin_writing_trace_events(tracer, &trace_path) {
        panic!("Error: trace writer failed to begin writing CTFS container: {err}")
    }

    // Bake the workdir into the metadata so `ct-print --strip-paths` can
    // normalise it.  Cairo / Leo do the same.
    if let Some(workdir) = workdir {
        TraceSink::set_workdir(tracer, workdir);
    }

    // The initial pending step is registered once the debugger reports the
    // first real source path.  Starting here would use the generated trace
    // output path, which is not a source file and leaves GUI replay without
    // an editor tab.
}

/// Finalize the CTFS container produced by `tracer`.
///
/// Flushes the events stream and closes the multi-stream writer, which
/// emits `events.log`, `meta.dat`, `paths.dat` and the rest of the
/// internal streams into the single `.ct` file.  Errors are returned rather
/// than printed: reporting is the shell's job, not the recorder's, and a wasm
/// host has no stdout to print to.  The partial container is still useful for
/// post-mortem inspection.
///
/// The legacy sidecar `finish_writing_trace_metadata` /
/// `finish_writing_trace_paths` calls were removed after the
/// Recording-Identifier-Migration: the multi-stream writer now handles
/// metadata + paths inside `close()` and emits `meta.dat` with the
/// canonical UUIDv7 `recording_id` (M-REC-1).
pub fn finish_trace(tracer: &mut dyn TraceSink) -> Result<(), Box<dyn std::error::Error>> {
    TraceSink::finish_writing_trace_events(tracer)?;
    TraceSink::close(tracer)?;
    Ok(())
}

/// Registers a tracing step to the given `location` in the given `tracer`.
///
/// When the location carries a 1-indexed column (the common case for
/// real Noir source spans), the step is registered through the
/// column-aware FFI entry point so the writer emits the `DeltaColumn`
/// (tag 0x07) follow-up event after the canonical Step.  Locations
/// without a column (synthetic / unknown) fall through to the
/// line-only path, which the default `register_step_with_column`
/// override in the writer also handles via `register_step` directly.
pub(crate) fn register_step(tracer: &mut dyn TraceSink, location: &SourceLocation) {
    let SourceLocation { filepath, line_number, column_number } = location;
    let path = &PathBuf::from(filepath.to_string());
    let line = Line(*line_number as i64);
    let column = column_number.map(|c| Line(c as i64));
    TraceSink::register_step_with_column(tracer, path, line, column);
}

/// Compute per-line UTF-8 byte counts for `source` (no trailing
/// newline counted in the per-line value).  The CTFS `paths.dat`
/// Layout A consumes this to encode each step's global byte position
/// so the reader can recover the 1-indexed column.
///
/// Mirrors `codetracer-leo-recorder/src/source_map.rs::compute_line_lengths`.
pub(crate) fn compute_line_lengths(source: &str) -> Vec<u32> {
    let mut lengths: Vec<u32> = Vec::new();
    let mut line_start: usize = 0;
    for (i, b) in source.bytes().enumerate() {
        if b == b'\n' {
            lengths.push((i - line_start) as u32);
            line_start = i + 1;
        }
    }
    if line_start < source.len() {
        lengths.push((source.len() - line_start) as u32);
    }
    lengths
}

/// Registers all variables in the given frame for the last registered step. Each time a new step is
/// registered, all of its variables need to be registered too. If no variables are registered for a
/// step, the frontend will not carry over the variables registered for the previous step.
pub(crate) fn register_variables(tracer: &mut dyn TraceSink, frame: &StackFrame) {
    for variable in &frame.variables {
        if variable.name != "__debug_return_expr" {
            register_variable(tracer, variable);
        }
    }
}

/// Registers a variable for the last registered step.
///
/// See `register_variables`.
fn register_variable(tracer: &mut dyn TraceSink, variable: &Variable) {
    let value_record = register_value(tracer, &variable.value, &variable.typ);
    TraceSink::register_variable_with_full_value(tracer, &variable.name, value_record);
}

/// A field element as `0x` + 64 lowercase big-endian hex — the whole 254 bits, always 66
/// characters.
///
/// `AcirField::to_hex` is `hex::encode(self.to_be_bytes())` and `to_be_bytes` is
/// `serialize_uncompressed` reversed, so for BN254 it is exactly 32 bytes and 64 hex digits with
/// leading zeros intact. The `0x` prefix is added here rather than left to a reader, because the
/// public half of a joined Aztec recording writes it and the two strings have to be equal as
/// strings.
fn field_to_hex(field_value: &FieldElement) -> String {
    format!("0x{}", field_value.to_hex())
}

/// Registers a value of a given type. Registers the type, if it's the first time it occurs.
fn register_value(
    tracer: &mut dyn TraceSink,
    value: &PrintableValue<FieldElement>,
    typ: &PrintableType,
) -> ValueRecord {
    if matches!(value, PrintableValue::Other) {
        let (type_kind, type_name) = printable_type_to_kind_and_name(typ);
        let type_id = TraceSink::ensure_type_id(tracer, type_kind, &type_name);
        return ValueRecord::None { type_id };
    }

    match typ {
        PrintableType::Field => {
            if let PrintableValue::Field(field_value) = value {
                let (type_kind, type_name) = printable_type_to_kind_and_name(typ);
                let type_id = TraceSink::ensure_type_id(tracer, type_kind, &type_name);
                // A `Field` is 254 bits and an `i64` is 64, so the old
                // `ValueRecord::Int { i: field_value.to_i128() as i64 }` here could not represent
                // one: `to_i128` PANICS above 127 bits (`acir_field/src/field_element.rs`, gated on
                // `num_bits() <= 127`) and `as i64` silently folds the sign on everything between
                // 64 and 127. An Aztec contract address is full width, so the recorder aborted on
                // the values that matter most. Fixing that is the smaller half of this change.
                //
                // The larger half is CROSS-HALF AGREEMENT. `aztec-avm-runtime` records the public
                // side of one Aztec transaction and this recorder records the private side, and
                // M26 puts both in one recording. A field element that renders as `Int 4` in one
                // frame and as `0x000…04` in the next is a defect a reader cannot see and cannot
                // work around. `aztec-avm-runtime/SOURCE-MAPPING.md` §4 settled the rendering by
                // MEASUREMENT rather than preference — five renderings written by the pinned
                // writer and read by both pinned readers, of which `ValueRecord::BigInt`, the
                // obvious full-precision choice, is REFUSED by `ct-print` with `cbor: expected
                // byte string (major 2), got major 3` — and the verdict is this one:
                //
                //     `0x` + 64 lowercase big-endian hex, in `ValueRecord::String`,
                //     under the SAME `(TypeKind::Int, "Field")` type record.
                //
                // `String` and not `Raw`, because `Raw` is this recorder's escape hatch for values
                // it CANNOT represent (`"()"`, `"fn"` below) and a field element is not one of
                // those. The width is FIXED at 64 characters with no leading-zero stripping, so
                // two renderings of one value are one string and a reader never has to normalise.
                //
                // ONE CONSEQUENCE THAT IS NOT NEUTRAL, and it is stated here because the sentence
                // above is easy to over-read. The TYPE RECORD is unchanged — still
                // `(TypeKind::Int, "Field")`, ensured on the line above. The TYPE TABLE is not:
                // the writer registers a nameless companion type for a `TypeKind::Int` type the
                // first time that type carries an `Int` VALUE, and a `Field` no longer carries
                // one, so the companion is never created. Measured in a clean worktree across
                // three fixtures: `assert`'s table goes `[None, Field, type_1]` -> `[None, Field]`,
                // `a_2_function_calls`' `[None, Field, type_1, ()]` -> `[None, Field, ()]`, and
                // `types_test` loses the entry after `Field` while the companions after `u32` and
                // `i8` survive and renumber. `a_1_mul`, whose only companion follows `u32`, is
                // untouched. `tests/test_tracer.rs`' header carries the full measurement.
                ValueRecord::String { text: field_to_hex(field_value), type_id }
            } else {
                // Note(stanm): panic here, because this means the compiler frontend is broken, which
                // is not the responsibility of this module. Should not be reachable in integration
                // tests (but reachable in unit tests).
                //
                // The same applies for the other `panic!`s in this function.
                panic!("type-value mismatch: value: {:?} does not match type Field", value)
            }
        }
        PrintableType::UnsignedInteger { .. } => {
            if let PrintableValue::Field(field_value) = value {
                let (type_kind, type_name) = printable_type_to_kind_and_name(typ);
                let type_id = TraceSink::ensure_type_id(tracer, type_kind, &type_name);
                ValueRecord::Int { i: field_value.to_i128() as i64, type_id }
            } else {
                panic!(
                    "type-value mismatch: value: {:?} does not match type UnsignedInteger",
                    value
                )
            }
        }
        PrintableType::SignedInteger { .. } => {
            if let PrintableValue::Field(field_value) = value {
                let (type_kind, type_name) = printable_type_to_kind_and_name(typ);
                let type_id = TraceSink::ensure_type_id(tracer, type_kind, &type_name);
                ValueRecord::Int { i: field_value.to_i128() as i64, type_id }
            } else {
                panic!("type-value mismatch: value: {:?} does not match type SignedInteger", value)
            }
        }
        PrintableType::Boolean => {
            if let PrintableValue::Field(field_value) = value {
                let (type_kind, type_name) = printable_type_to_kind_and_name(typ);
                let type_id = TraceSink::ensure_type_id(tracer, type_kind, &type_name);
                ValueRecord::Bool { b: field_value.to_i128() as i64 == 1, type_id }
            } else {
                panic!("type-value mismatch: value: {:?} does not match type Bool", value)
            }
        }
        PrintableType::Vector { typ: element_type } => {
            if let PrintableValue::Vec { array_elements, is_vector } = value {
                if !is_vector {
                    panic!("value of is_slice: {:?} does not match type Slice", value)
                }
                let element_values: Vec<ValueRecord> = array_elements
                    .iter()
                    .map(|e| register_value(tracer, e, element_type))
                    .collect();
                let (type_kind, type_name) = printable_type_to_kind_and_name(typ);
                let type_id = TraceSink::ensure_type_id(tracer, type_kind, &type_name);
                ValueRecord::Sequence { elements: element_values, type_id, is_slice: true }
            } else {
                panic!("type-value mismatch: value: {:?} does not match type Slice", value)
            }
        }
        PrintableType::Array { typ: element_type, .. } => {
            if let PrintableValue::Vec { array_elements, is_vector } = value {
                if *is_vector {
                    panic!("value of is_slice: {:?} does not match type Array", value)
                }
                let element_values: Vec<ValueRecord> = array_elements
                    .iter()
                    .map(|e| register_value(tracer, e, element_type))
                    .collect();
                let (type_kind, type_name) = printable_type_to_kind_and_name(typ);
                let type_id = TraceSink::ensure_type_id(tracer, type_kind, &type_name);
                ValueRecord::Sequence { elements: element_values, type_id, is_slice: false }
            } else {
                panic!("type-value mismatch: value: {:?} does not match type Array", value)
            }
        }
        PrintableType::String { .. } => {
            if let PrintableValue::String(s) = value {
                let (type_kind, type_name) = printable_type_to_kind_and_name(typ);
                let type_id = TraceSink::ensure_type_id(tracer, type_kind, &type_name);
                ValueRecord::String { text: s.clone(), type_id }
            } else {
                panic!("type-value mismatch: value: {:?} does not match type String", value);
            }
        }
        PrintableType::Struct { fields, .. } => {
            if let PrintableValue::Struct(struc) = value {
                let (type_kind, type_name) = printable_type_to_kind_and_name(typ);
                let type_id = TraceSink::ensure_type_id(tracer, type_kind, &type_name);
                let mut field_values = vec![];
                for (field_name, field_type) in fields {
                    let field_value = struc
                        .get(field_name)
                        .unwrap_or_else(|| panic!("field value missing: {field_name}"));
                    field_values.push(register_value(tracer, field_value, field_type));
                }
                ValueRecord::Struct { field_values, type_id }
            } else {
                panic!("type-value mismatch: value: {:?} does not match type Struct", value);
            }
        }
        PrintableType::Unit => {
            let (type_kind, type_name) = printable_type_to_kind_and_name(typ);
            let type_id = TraceSink::ensure_type_id(tracer, type_kind, &type_name);
            ValueRecord::Raw { r: "()".to_string(), type_id }
        }
        PrintableType::Tuple { types } => {
            if let PrintableValue::Vec { array_elements, is_vector } = value {
                if *is_vector {
                    panic!("value of is_slice: {:?} does not match type Tuple", value)
                }
                let element_values: Vec<ValueRecord> = array_elements
                    .iter()
                    .zip(types.iter())
                    .map(|(v, t)| register_value(tracer, v, t))
                    .collect();
                let (type_kind, type_name) = printable_type_to_kind_and_name(typ);
                let type_id = TraceSink::ensure_type_id(tracer, type_kind, &type_name);
                ValueRecord::Tuple { elements: element_values, type_id }
            } else {
                panic!("type-value mismatch: value: {:?} does not match type Tuple", value)
            }
        }
        PrintableType::Reference { typ: dereferenced_type, mutable } => {
            let (type_kind, type_name) = printable_type_to_kind_and_name(typ);
            let type_id = TraceSink::ensure_type_id(tracer, type_kind, &type_name);
            let v = register_value(tracer, value, dereferenced_type);
            ValueRecord::Reference {
                dereferenced: Box::new(v),
                address: 0,
                mutable: *mutable,
                type_id,
            }
        }
        PrintableType::Function { .. } => {
            let (type_kind, type_name) = printable_type_to_kind_and_name(typ);
            let type_id = TraceSink::ensure_type_id(tracer, type_kind, &type_name);
            ValueRecord::Raw { r: "fn".to_string(), type_id }
        }
        PrintableType::Enum { .. } => {
            // Enums are an unstable, experimental Noir feature.
            // Even when enabled with -Z enums, they don't seem to become visible in the debugger, so we can't
            // implement them, yet. Therefore, this code is unreachable in practice. Once debugger support for enums is
            // added, we need to implement this as well.
            todo!("Tracing support for enums is not yet implemented")
        }
        PrintableType::FmtString { typ: element_type, .. } => {
            // TODO: Proper handling for FmtString type
            if let PrintableValue::FmtString(msg, printable_values) = value {
                printable_values.iter().for_each(|printable_value| {
                    register_value(tracer, printable_value, element_type);
                });
                let (type_kind, type_name) = printable_type_to_kind_and_name(typ);
                let type_id = TraceSink::ensure_type_id(tracer, type_kind, &type_name);
                ValueRecord::String { text: msg.clone(), type_id }
            } else {
                panic!("type-value mismatch: value: {:?} does not match type FmtString", value)
            }
        }
    }
}

/// Registers a call to the given `frame` at the given `location` in the given `tracer`.
///
/// A helper method, that makes it easier to interface with `Tracer`.
pub(crate) fn register_call(
    tracer: &mut dyn TraceSink,
    location: &SourceLocation,
    frame: &StackFrame,
) {
    let SourceLocation { filepath, line_number, column_number: _ } = &location;
    let path = &PathBuf::from(filepath.to_string());
    let line = Line(*line_number as i64);
    let file_id = TraceSink::ensure_function_id(tracer, &frame.function_name, path, line);
    let args = convert_params_to_args_vec(tracer, frame);
    TraceSink::register_call(tracer, file_id, args);
}

/// Extracts the relevant information from the given `frame` to construct a vector of `ArgRecord`
/// that the `Tracer` interface expects when registering function calls.
fn convert_params_to_args_vec(
    tracer: &mut dyn TraceSink,
    frame: &StackFrame,
) -> Vec<FullValueRecord> {
    let mut result = Vec::new();
    for param_index in &frame.function_param_indexes {
        let variable = &frame.variables[*param_index];
        let value_record = register_value(tracer, &variable.value, &variable.typ);
        result.push(TraceSink::arg(tracer, &variable.name, value_record));
    }
    result
}

/// Register a return statement in the given `tracer`.
///
/// The tracer seems to be keeping context of which function is returning and is not expecting that
/// to be specified.
pub(crate) fn register_return(tracer: &mut dyn TraceSink, return_value: &Option<Variable>) {
    if let Some(return_value) = return_value {
        let value_record = register_value(tracer, &return_value.value, &return_value.typ);
        TraceSink::register_return(tracer, value_record);
    } else {
        let type_id = TraceSink::ensure_type_id(tracer, TypeKind::None, "()");

        TraceSink::register_return(tracer, ValueRecord::None { type_id });
    }
}

pub(crate) fn register_print(tracer: &mut dyn TraceSink, s: &str) {
    // The newer `register_special_event` API takes a `metadata` parameter
    // (used by other recorders to tag the originating command/syscall).  Noir
    // print events have no such tag, so we pass an empty string — matching
    // the convention used by the shell recorders (see
    // `ct-shell-trace-writer/src/trace_bridge.rs`).
    TraceSink::register_special_event(tracer, EventLogKind::Write, "", s);
}

pub(crate) fn register_error(tracer: &mut dyn TraceSink, s: &str) {
    TraceSink::register_special_event(tracer, EventLogKind::Error, "", s);
}

fn printable_type_to_kind_and_name(printable_type: &PrintableType) -> (TypeKind, String) {
    match printable_type {
        PrintableType::Field => (TypeKind::Int, "Field".to_string()),
        PrintableType::UnsignedInteger { width } => (TypeKind::Int, format!("u{width}")),
        PrintableType::SignedInteger { width } => (TypeKind::Int, format!("i{width}")),
        PrintableType::Boolean => (TypeKind::Bool, "Bool".to_string()),
        PrintableType::Vector { .. } => (TypeKind::Slice, "&[..]".to_string()),
        PrintableType::Array { length, .. } => (TypeKind::Seq, format!("Array<{length}, ..>")),
        PrintableType::String { .. } => (TypeKind::String, "String".to_string()),
        PrintableType::Struct { name, .. } => (TypeKind::Struct, name.clone()),
        PrintableType::Unit => (TypeKind::Raw, "()".to_string()),
        PrintableType::Tuple { .. } => (TypeKind::Tuple, "(..)".to_string()),
        PrintableType::Reference { .. } => (TypeKind::Ref, "&".to_string()),
        PrintableType::Function { unconstrained, .. } => {
            let type_name = if *unconstrained { "unconstrained fn" } else { "fn" };
            (TypeKind::FunctionKind, type_name.to_string())
        }
        PrintableType::FmtString { .. } => {
            // FmtString is ultimately traced as a regular String
            (TypeKind::String, "String".to_string())
        }
        PrintableType::Enum { .. } => {
            // As in the original code, tracing for enums is not yet implemented.
            todo!("Tracing support for enums is not yet implemented")
        }
    }
}
