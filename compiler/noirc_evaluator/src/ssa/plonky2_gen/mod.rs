// !!!!!!!!!!!!!!!!!!!!!!!!!
// this assumes everything is a Field. i REFUSE to deal with noir's typesystem ever again
// but you dear reader who has to continue this marvelous work are in luck, because
// noir has multiple type systems (3 in fact) and here we're dealing with the IR's
// type system which is the simplest of them all:
// types include:
//  - Field - the sane type
//  - u32/i60/u44 - truncated signed/unsigned fields
//  - [T, 100] - arrays
//  - (T1, T2, T3) - tuples

use std::collections::HashMap;

use crate::{
    errors::RuntimeError,
    ssa::ir::{
        instruction::Instruction,
        value::{Value, ValueId},
    },
};
use acvm::acir::native_types::WitnessMap;
use noirc_abi::InputMap;
use plonky2::{
    field::{goldilocks_field::GoldilocksField, types::Field},
    iop::target::Target,
    plonk::{
        circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
        config::PoseidonGoldilocksConfig,
    },
};
use serde::{Deserialize, Serialize};

use super::{
    ir::{
        dfg::DataFlowGraph,
        instruction::{Binary, InstructionId},
    },
    ssa_gen::Ssa,
};

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct Plonky2Circuit {
    common_data_serialized: String,
    verifier_only_data_serialized: String,
}

const D: usize = 2;
type PlonkyBuilder = CircuitBuilder<GoldilocksField, D>;

impl Plonky2Circuit {
    pub fn prove(&self, inputs: InputMap) -> Option<Vec<u8>> {
        None
    }

    pub fn verify(&self, proof: &Vec<u8>, public_inputs: WitnessMap) -> Option<bool> {
        Some(false)
    }
}

struct State {
    builder: PlonkyBuilder,
    translation: HashMap<ValueId, Target>,
    dfg: DataFlowGraph,
}

impl State {
    fn new() -> State {
        let config = CircuitConfig::standard_recursion_config();
        State {
            dfg: DataFlowGraph::default(),
            builder: PlonkyBuilder::new(config),
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
                .constant(GoldilocksField::from_canonical_u64(constant.to_u128() as u64)),
            _ => {
                todo!("State::get() not implemented for value {:?}", value)
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

                let dst_target = match operator {
                    super::ir::instruction::BinaryOp::Add => self.builder.add(lhs, rhs),
                    super::ir::instruction::BinaryOp::Sub => self.builder.sub(lhs, rhs),
                    super::ir::instruction::BinaryOp::Mul => self.builder.mul(lhs, rhs),
                    super::ir::instruction::BinaryOp::Div => self.builder.div(lhs, rhs),
                    _ => todo!(),
                };

                // RUUSTUSUTUUTUSTU
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
                    "ssa -> plonky2 not implemented for instruction: {:?} <- {:?}",
                    self.dfg.instruction_results(instr_id),
                    instr
                );
            }
        }
    }

    fn ssa_to_plonky2(mut self, ssa: Ssa) -> Plonky2Circuit {
        // everything must be inlined after ssa optimizations
        assert!(ssa.functions.len() == 1);

        let func = ssa.functions.into_values().next().unwrap(); // rust..
        let block_id = func.entry_block();

        self.dfg = func.dfg;
        let block = self.dfg[block_id].clone();

        for value_id in block.parameters() {
            let target = self.builder.add_virtual_target();
            self.builder.register_public_input(target); // TODO we're assuming all inputs are public :P

            self.set(*value_id, target);
        }

        for instr_id in block.instructions() {
            self.add_instruction(*instr_id)
        }

        let data = self.builder.build::<PoseidonGoldilocksConfig>();

        let common_data_serialized = serde_json::to_string(&data.common).unwrap();
        let verifier_only_data_serialized = serde_json::to_string(&data.verifier_only).unwrap();

        Plonky2Circuit { common_data_serialized, verifier_only_data_serialized }
    }
}

pub(crate) fn ssa_to_plonky2(ssa: Ssa) -> Result<Plonky2Circuit, RuntimeError> {
    Ok(State::new().ssa_to_plonky2(ssa))
}
