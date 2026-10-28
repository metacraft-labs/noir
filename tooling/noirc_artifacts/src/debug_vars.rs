use acvm::AcirField;
use noirc_printable_type::{PrintableType, PrintableValue, decode_printable_value};
use std::collections::HashMap;

use crate::debug::{DebugFnId, DebugFunction, DebugInfo, DebugTypeId, DebugVarId, DebugVariable};

#[derive(Debug, Default, Clone)]
pub struct DebugVars<F> {
    variables: HashMap<DebugVarId, DebugVariable>,
    functions: HashMap<DebugFnId, DebugFunction>,
    types: HashMap<DebugTypeId, PrintableType>,
    frames: Vec<(DebugFnId, HashMap<DebugVarId, PrintableValue<F>>)>,
}

#[cfg(test)]
mod variable_order_tests {
    use super::*;
    use acvm::FieldElement;

    #[test]
    fn shadowed_variables_follow_debug_binding_identity() {
        let mut debug = DebugVars::<FieldElement>::default();
        let fn_id = DebugFnId(0);
        let type_id = DebugTypeId(0);
        debug.functions.insert(fn_id, DebugFunction { name: "main".into(), arg_names: vec![] });
        debug.types.insert(type_id, PrintableType::Field);
        debug.push_fn(fn_id);
        // The instrumenter allocates increasing IDs at declarations. Retain
        // every binding, with the newer shadowing binding after the old one.
        for id in (0..64).rev() {
            debug.variables.insert(
                DebugVarId(id),
                DebugVariable { name: "bounds".into(), debug_type_id: type_id },
            );
            let value = if id == 63 { 508u32 } else { id };
            debug.assign_var(DebugVarId(id), &[FieldElement::from(value)]);
        }
        let frame = debug.current_stack_frame().unwrap();
        let values: Vec<_> = frame
            .variables
            .iter()
            .map(|(_, value, _)| match value {
                PrintableValue::Field(value) => value.to_u128(),
                other => panic!("expected field binding, got {other:?}"),
            })
            .collect();
        assert_eq!(values, (0..63).chain(std::iter::once(508)).collect::<Vec<_>>());
        debug.drop_var(DebugVarId(63));
        let after_drop = debug.current_stack_frame().unwrap();
        assert_eq!(after_drop.variables.len(), 63);
        assert_eq!(
            after_drop.variables.last().unwrap().1,
            &PrintableValue::Field(FieldElement::from(62u32))
        );
    }
}

pub struct StackFrame<'a, F> {
    pub function_name: &'a str,
    pub function_params: Vec<&'a str>,
    /// Bindings in increasing debug identity (declaration) order. Equal names
    /// remain distinct, with a newer shadowing binding after its outer binding.
    pub variables: Vec<(&'a str, &'a PrintableValue<F>, &'a PrintableType)>,
}

impl<F: AcirField> DebugVars<F> {
    pub fn insert_debug_info(&mut self, info: &DebugInfo) {
        self.variables.extend(info.variables.clone());
        self.types.extend(info.types.clone());
        self.functions.extend(info.functions.clone());
    }

    pub fn get_variables(&self) -> Vec<StackFrame<F>> {
        self.frames.iter().map(|(fn_id, frame)| self.build_stack_frame(fn_id, frame)).collect()
    }

    pub fn current_stack_frame(&self) -> Option<StackFrame<F>> {
        self.frames.last().map(|(fn_id, frame)| self.build_stack_frame(fn_id, frame))
    }

    fn lookup_var(&self, var_id: DebugVarId) -> Option<(&str, &PrintableType)> {
        let debug_var = self.variables.get(&var_id)?;
        let printable_type = self.types.get(&debug_var.debug_type_id)?;
        Some((debug_var.name.as_str(), printable_type))
    }

    fn build_stack_frame<'a>(
        &'a self,
        fn_id: &DebugFnId,
        frame: &'a HashMap<DebugVarId, PrintableValue<F>>,
    ) -> StackFrame<'a, F> {
        let debug_fn = &self.functions.get(fn_id).expect("failed to find function metadata");

        let params: Vec<&str> =
            debug_fn.arg_names.iter().map(|arg_name| arg_name.as_str()).collect();
        // DebugVarIds are allocated in declaration order. Preserve that order
        // before discarding identity: a later stable sort by name must keep
        // outer bindings before their newer shadowing bindings, so replay's
        // last value for a name is the active binding rather than a random one.
        let mut bindings: Vec<_> = frame.iter().collect();
        bindings.sort_unstable_by_key(|(var_id, _)| var_id.0);
        let vars: Vec<(&str, &PrintableValue<F>, &PrintableType)> = bindings
            .into_iter()
            .filter_map(|(var_id, var_value)| {
                self.lookup_var(*var_id).map(|(name, typ)| (name, var_value, typ))
            })
            .collect();

        StackFrame {
            function_name: debug_fn.name.as_str(),
            function_params: params,
            variables: vars,
        }
    }

    pub fn assign_var(&mut self, var_id: DebugVarId, values: &[F]) {
        let type_id = &self.variables.get(&var_id).unwrap().debug_type_id;
        let printable_type = self.types.get(type_id).unwrap();

        // Debug assignment oracles serialize a snapshot of the referent, rather than
        // the addresses ordinary oracles receive. Keep the reference metadata on the
        // binding for consumers, but decode its payload using the terminal target type.
        let mut value_type = printable_type;
        while let PrintableType::Reference { typ, .. } = value_type {
            value_type = typ;
        }
        self.frames
            .last_mut()
            .expect("unexpected empty stack frames")
            .1
            .insert(var_id, decode_printable_value(&mut values.iter().copied(), value_type));
    }

    pub fn assign_field(&mut self, var_id: DebugVarId, indexes: Vec<u32>, values: &[F]) {
        let current_frame = &mut self.frames.last_mut().expect("unexpected empty stack frames").1;
        let mut cursor: &mut PrintableValue<F> = current_frame
            .get_mut(&var_id)
            .unwrap_or_else(|| panic!("value unavailable for var_id {var_id:?}"));
        let cursor_type_id = &self
            .variables
            .get(&var_id)
            .unwrap_or_else(|| panic!("variable {var_id:?} not found"))
            .debug_type_id;
        let mut cursor_type = self
            .types
            .get(cursor_type_id)
            .unwrap_or_else(|| panic!("type unavailable for type id {cursor_type_id:?}"));
        for index in &indexes {
            (cursor, cursor_type) = match (cursor, cursor_type) {
                (
                    PrintableValue::Vec { array_elements, is_vector },
                    PrintableType::Array { length, typ },
                ) => {
                    assert!(!*is_vector, "vector has array type");
                    if *index >= *length {
                        panic!("unexpected field index past array length")
                    }
                    if *length != array_elements.len() as u32 {
                        panic!("type/array length mismatch")
                    }
                    (array_elements.get_mut(*index as usize).unwrap(), &*Box::leak(typ.clone()))
                }
                (
                    PrintableValue::Vec { array_elements, is_vector },
                    PrintableType::Vector { typ },
                ) => {
                    assert!(*is_vector, "vector doesn't have vector type");
                    (array_elements.get_mut(*index as usize).unwrap(), &*Box::leak(typ.clone()))
                }
                (
                    PrintableValue::Struct(field_map),
                    PrintableType::Struct { name: _name, fields },
                ) => {
                    if *index as usize >= fields.len() {
                        panic!("unexpected field index past struct field length")
                    }
                    let (key, typ) = fields.get(*index as usize).unwrap();
                    (field_map.get_mut(key).unwrap(), typ)
                }
                (
                    PrintableValue::Vec { array_elements, is_vector },
                    PrintableType::Tuple { types },
                ) => {
                    assert!(!*is_vector, "vector has tuple type");
                    if *index >= types.len() as u32 {
                        panic!(
                            "unexpected field index ({index}) past tuple length ({})",
                            types.len()
                        );
                    }
                    if types.len() != array_elements.len() {
                        panic!("type/array length mismatch")
                    }
                    let typ = types.get(*index as usize).unwrap();
                    (array_elements.get_mut(*index as usize).unwrap(), typ)
                }
                _ => {
                    panic!("unexpected assign field of {cursor_type:?} type");
                }
            };
        }
        *cursor = decode_printable_value(&mut values.iter().copied(), cursor_type);
    }

    pub fn assign_deref(&mut self, _var_id: DebugVarId, _values: &[F]) {
        unimplemented![]
    }

    pub fn get_type(&self, var_id: DebugVarId) -> Option<&PrintableType> {
        let debug_var = self.variables.get(&var_id)?;
        self.types.get(&debug_var.debug_type_id)
    }

    pub fn drop_var(&mut self, var_id: DebugVarId) {
        self.frames.last_mut().expect("unexpected empty stack frames").1.remove(&var_id);
    }

    pub fn push_fn(&mut self, fn_id: DebugFnId) {
        self.frames.push((fn_id, HashMap::default()));
    }

    pub fn pop_fn(&mut self) {
        self.frames.pop();
    }
}
