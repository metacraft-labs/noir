mod circuit;
mod config;

use acvm::FieldElement;
use noirc_abi::{Abi, AbiVisibility};
pub use circuit::*;

use std::collections::HashMap;

use crate::{
    ssa::ir::{
        instruction::Instruction,
        value::{Value, ValueId},
    },
};
use plonky2::{
    iop::target::Target, plonk::circuit_data::CircuitConfig, field::types::Field,
};

use self::config::{P2Builder, P2Config, P2Field};

use super::{
    ir::{
        dfg::DataFlowGraph,
        instruction::{Binary, InstructionId},
    },
    ssa_gen::Ssa,
};


pub(crate) struct Builder {
    builder: P2Builder,
    translation: HashMap<ValueId, Target>,
    dfg: DataFlowGraph,
}

impl Builder {
    pub(crate) fn new() -> Builder {
        let config = CircuitConfig::standard_recursion_config();
        Builder {
            dfg: DataFlowGraph::default(),
            builder: P2Builder::new(config),
            translation: HashMap::new(),
        }
    }

    fn set(&mut self, value_id: ValueId, target: Target) {
        self.translation.insert(value_id, target);
    }

    fn get(&mut self, value_id: ValueId) -> Target {
        let value = self.dfg[value_id].clone();
        match value {
            Value::Param { .. } | Value::Instruction { .. } => {
                self.translation.get(&value_id).unwrap().clone()
            }
            Value::NumericConstant { constant, typ: _ } => self
                .builder
                .constant(noir_to_plonky2_field(constant)),
            _ => {
                todo!("TODO(plonky2): State::get() not implemented for value {:?}", value)
            }
        }
    }

    fn add_instruction(&mut self, instr_id: InstructionId) {
        let instr = self.dfg[instr_id].clone();
        // println!("{:?} <- {:?}", self.dfg.instruction_results(instr_id), instr);

        match instr {
            Instruction::Binary(Binary { lhs, rhs, operator }) => {
                let lhs = self.get(lhs);
                let rhs = self.get(rhs);

                // TODO(plonky2) - special handling needed here for modular arithmetic on i32/u55/whatever
                let dst_target = match operator {
                    super::ir::instruction::BinaryOp::Add => self.builder.add(lhs, rhs),
                    super::ir::instruction::BinaryOp::Sub => self.builder.sub(lhs, rhs),
                    super::ir::instruction::BinaryOp::Mul => self.builder.mul(lhs, rhs),
                    super::ir::instruction::BinaryOp::Div => self.builder.div(lhs, rhs),
                    _ => todo!("TODO(plonky2)"),
                };

                let destinations: Vec<_> =
                    self.dfg.instruction_results(instr_id).iter().cloned().collect();
                assert!(destinations.len() == 1);
                self.set(destinations[0], dst_target);
            }
            Instruction::Constrain(lhs, rhs, _) => {
                let lhs = self.get(lhs);
                let rhs = self.get(rhs);
                self.builder.connect(lhs, rhs);
            }
            _ => {
                todo!(
                    "TODO(plonky2): ssa -> plonky2 not implemented for instruction: {:?} <- {:?}",
                    self.dfg.instruction_results(instr_id),
                    instr
                );
            }
        }
    }

    pub(crate) fn build(mut self, ssa: Ssa, abi: Abi) -> Plonky2Circuit {
        // everything must be inlined after ssa optimizations
        assert!(ssa.functions.len() == 1);

        let func = ssa.functions.into_values().next().unwrap(); // rust..
        let block_id = func.entry_block();

        self.dfg = func.dfg;
        let block = self.dfg[block_id].clone();

        let mut parameters = Vec::new();

        for (value_id, param) in block.parameters().iter().zip(&abi.parameters) {
            let target = self.builder.add_virtual_target();
            parameters.push(target);

            if param.visibility == AbiVisibility::Public {
                self.builder.register_public_input(target);
            }

            self.set(*value_id, target);
        }

        for instr_id in block.instructions() {
            self.add_instruction(*instr_id)
        }

        let data = self.builder.build::<P2Config>();

        // TODO(plonky2):
        // We need to serialize the circuit, and store the serialized representation in
        // Plonky2Circuit instead of the Builder. Plonky2 provides a "serialize" for the
        // common_data and verifier_data, but not for prover_only_data, and it doesn't
        // provide a "deserialize" for any of them hahaha. we'll likely need to roll our own.
        let _common_data_serialized = serde_json::to_string(&data.common).unwrap();
        let _verifier_only_data_serialized = serde_json::to_string(&data.verifier_only).unwrap();

        Plonky2Circuit { data, parameters, abi }
    }
}

pub(crate) fn noir_to_plonky2_field(field: FieldElement) -> P2Field {
    // TODO(plonky2): Noir doesn't support the Goldilock field, FieldElement is 254 bit
    //                if the user punches inin a large integer, we'll panic
    //
    // TODO(plonky2): this likely not worketh for negative numbers
    P2Field::from_canonical_u64(field.to_u128() as u64)
}