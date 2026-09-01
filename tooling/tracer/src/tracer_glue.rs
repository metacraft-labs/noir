use crate::{SourceLocation, StackFrame, stack_frame::Variable};

use crate::sink::TraceSink;
use acvm::FieldElement;
use acvm::acir::AcirField; // necessary, for `to_i128` to work
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

/// Record an integer-like field element without losing it.
///
/// `ValueRecord::Int` carries an `i64`, and this used to be reached as
/// `field.to_i128() as i64` — two silent failures stacked on one line:
///
/// * `AcirField::to_i128` **panics** (`field element too large for i128`) on anything
///   wider than 128 bits. A Poseidon digest always is, so this was not an edge case on
///   Aztec code — it was every contract that hashes anything, which is every contract.
/// * `as i64` then truncates whatever survived, so a value between `i64::MAX` and
///   `i128::MAX` was recorded as a *different number* with no error at all. That is the
///   worse of the two: a debugger showing a confidently wrong value.
///
/// `ValueRecord::BigInt` exists for exactly this and carries the big-endian magnitude, so
/// wide values are now recorded EXACTLY rather than approximated or fatal.
fn field_to_int_record(
    field: &FieldElement,
    typ: &PrintableType,
    type_id: codetracer_trace_types::TypeId,
) -> ValueRecord {
    // Only a signed Noir type may use the field's negative half; for `Field` and unsigned
    // integers the whole range is a magnitude, and reading the top half as negative would
    // turn a large hash into a small negative number.
    let signed = matches!(typ, PrintableType::SignedInteger { .. });

    if field.fits_in_i128() {
        let wide = field.to_i128();
        // `as i64` is what truncated; `try_from` is what refuses to.
        if let Ok(i) = i64::try_from(wide)
            && (signed || wide >= 0)
        {
            return ValueRecord::Int { i, type_id };
        }
    }

    let negated = -*field;
    let negative = signed && negated.num_bits() < field.num_bits();
    let magnitude = if negative { negated } else { *field };
    let mut bytes = magnitude.to_be_bytes();
    // Trim leading zeros — the encoding is a magnitude, not a fixed-width word — but keep
    // one byte so zero stays representable.
    let first_significant = bytes.iter().position(|b| *b != 0).unwrap_or(bytes.len() - 1);
    bytes.drain(..first_significant);
    ValueRecord::BigInt { b: bytes, negative, type_id }
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
                field_to_int_record(field_value, typ, type_id)
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
                field_to_int_record(field_value, typ, type_id)
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
                field_to_int_record(field_value, typ, type_id)
            } else {
                panic!("type-value mismatch: value: {:?} does not match type SignedInteger", value)
            }
        }
        PrintableType::Boolean => {
            if let PrintableValue::Field(field_value) = value {
                let (type_kind, type_name) = printable_type_to_kind_and_name(typ);
                let type_id = TraceSink::ensure_type_id(tracer, type_kind, &type_name);
                // `is_one` rather than `to_i128() == 1`: a bool is 0 or 1, but the old form
                // would still panic if a malformed witness put a wide value here.
                ValueRecord::Bool { b: field_value.is_one(), type_id }
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

#[cfg(test)]
mod field_recording_tests {
    use super::*;
    use codetracer_trace_types::TypeId;

    const TID: TypeId = TypeId(0);

    /// A Poseidon digest is wider than `i128`, and recording one used to abort the whole
    /// trace with `field element too large for i128`. Since every Aztec contract hashes
    /// something, that made this unavoidable on real contract code rather than an edge
    /// case. It must now be recorded exactly, as a `BigInt`.
    #[test]
    fn a_field_wider_than_i128_records_as_a_bigint_rather_than_panicking() {
        // 2^200: comfortably past i128 and a valid bn254 field element.
        let wide = FieldElement::from(2u128).pow(&FieldElement::from(200u128));

        // The non-panicking half is asserted EXPLICITLY rather than by the test simply
        // completing. If the `to_i128` path is ever restored, this reddens on its own
        // assertion below instead of dying inside the call and being killed by a panic
        // this test never names.
        let previous_hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            field_to_int_record(&wide, &PrintableType::Field, TID)
        }));
        std::panic::set_hook(previous_hook);

        let record = match outcome {
            Ok(record) => record,
            Err(_) => panic!(
                "recording a field wider than i128 must not panic — a Poseidon digest \
                 always is one, so this aborts the trace of any contract that hashes"
            ),
        };

        let ValueRecord::BigInt { b, negative, .. } = record else {
            panic!("a field wider than i128 must record as BigInt, got {record:?}");
        };
        assert!(!negative, "a `Field` is a magnitude; it is never negative");
        // 2^200 is a 1 followed by 200 zero bits = 26 bytes: 0x01 then 25 zero bytes.
        assert_eq!(b.len(), 26, "the magnitude keeps every significant byte: {b:?}");
        assert_eq!(b[0], 1, "big-endian, leading zeros trimmed");
        assert!(b[1..].iter().all(|byte| *byte == 0), "2^200 has one set bit");
    }

    /// The quieter half of the same defect. `to_i128() as i64` did not panic here — it
    /// TRUNCATED, so a value above `i64::MAX` was recorded as a different, smaller number
    /// with no error anywhere. A debugger showing a confidently wrong value is worse than
    /// one that stops.
    #[test]
    fn a_field_above_i64_max_is_not_silently_truncated() {
        let above = FieldElement::from(i64::MAX as u128 + 1);
        let record = field_to_int_record(&above, &PrintableType::Field, TID);

        let ValueRecord::BigInt { b, negative, .. } = record else {
            panic!("a value above i64::MAX must not be squeezed into Int, got {record:?}");
        };
        assert!(!negative);
        // 2^63 = 0x80 followed by seven zero bytes.
        assert_eq!(b, vec![0x80, 0, 0, 0, 0, 0, 0, 0], "the exact magnitude survives");
    }

    /// The common case must not regress into `BigInt`: an ordinary small value is still an
    /// `Int`, or every integer in every trace would become a base64 blob.
    #[test]
    fn an_ordinary_small_field_still_records_as_an_int() {
        let record = field_to_int_record(&FieldElement::from(42u128), &PrintableType::Field, TID);
        assert!(
            matches!(record, ValueRecord::Int { i: 42, .. }),
            "a small field stays an Int, got {record:?}"
        );
    }

    /// A signed Noir integer may legitimately use the field's negative half, and must keep
    /// its sign rather than being read as an enormous magnitude.
    #[test]
    fn a_negative_signed_integer_keeps_its_sign() {
        let typ = PrintableType::SignedInteger { width: 64 };
        let minus_one = -FieldElement::from(1u128);
        let record = field_to_int_record(&minus_one, &typ, TID);
        assert!(
            matches!(record, ValueRecord::Int { i: -1, .. }),
            "-1 as an i64 stays -1, got {record:?}"
        );
    }

    /// …and an UNSIGNED type must not have the field's top half read as negative, which is
    /// how a large hash would turn into a small negative number.
    #[test]
    fn a_large_unsigned_value_is_never_reported_negative() {
        let typ = PrintableType::UnsignedInteger { width: 128 };
        let big = -FieldElement::from(1u128); // p-1: the field's largest element
        let record = field_to_int_record(&big, &typ, TID);
        let ValueRecord::BigInt { negative, b, .. } = record else {
            panic!("p-1 does not fit an i64, so it must be a BigInt, got {record:?}");
        };
        assert!(!negative, "an unsigned type never yields a negative record");
        assert!(b.len() >= 31, "p-1 is a full-width field element, got {} bytes", b.len());
    }
}
