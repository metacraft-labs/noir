//! wasm32 shell over [`noir_tracer`].
//!
//! Probe stage: the only job of this crate right now is to force
//! `cargo check --target wasm32-unknown-unknown -p noir_tracer_wasm` to pull the
//! whole tracer dependency closure into a wasm build so the real blocker set can
//! be enumerated empirically.

pub fn probe() {}
