use acvm::acir::native_types::WitnessMap;
use noirc_abi::{Abi, InputMap};
use plonky2::iop::{witness::{PartialWitness, WitnessWrite}, target::Target};
use serde::{Deserialize, Serialize};

use crate::ssa::plonky2_gen::noir_to_plonky2_field;

use super::config::P2CircuitData;

#[derive(Debug)]
pub struct Plonky2Circuit {
    pub data: P2CircuitData,
    pub parameters: Vec<Target>,
    pub abi: Abi,
}

// TODO(plonky2): Plonky2Circuit needs to impl Clone/Serialize/Deserialize.
// this can be easily done if we store a serialized representation of the `data`, which we currently dont
// so all these traits have stubs
impl Clone for Plonky2Circuit {
    fn clone(&self) -> Self {
        todo!()
    }
}

impl Serialize for Plonky2Circuit {
    // see the todo at Clone
    fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        todo!()
    }
}

impl<'de> Deserialize<'de> for Plonky2Circuit {
    // see the todo at Clone
    fn deserialize<D>(_deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        todo!()
    }
}

impl Plonky2Circuit {
    pub fn prove(&self, inputs: &InputMap) -> Option<Vec<u8>> {
        let mut pw = PartialWitness::new();

        for (target, param) in self.parameters.iter().zip(&self.abi.parameters) {
            let value = inputs[&param.name].clone();

            match value {
                noirc_abi::input_parser::InputValue::Field(field) => {
                    let field = noir_to_plonky2_field(field);
                    pw.set_target(*target, field)
                }
                _ => todo!(),
            }
        }

        let proof = self.data.prove(pw).ok()?;
        let proof_seiralized = serde_json::to_vec(&proof).ok()?;
        Some(proof_seiralized)
    }

    pub fn verify(&self, _proof: &Vec<u8>, _public_inputs: WitnessMap) -> Option<bool> {
        Some(false)
    }
}
