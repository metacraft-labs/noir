#![warn(unused_crate_dependencies, unused_extern_crates)]

// See Cargo.toml for explanation.
use getrandom as _;
use getrandom_v2 as _; // cSpell:disable-line
use getrandom_v4 as _; // cSpell:disable-line
use rust_embed as _;

use gloo_utils::format::JsValueSerdeExt;

use noirc_driver::{GIT_COMMIT, GIT_DIRTY, NOIRC_VERSION};
use serde::{Deserialize, Serialize};
use tracing_subscriber::EnvFilter;
use tracing_subscriber::prelude::*;
use tracing_web::MakeWebConsoleWriter;

mod compile;
mod compile_new;
mod compile_vfs;
mod errors;
pub mod vfs;

pub use compile::{compile_contract, compile_program};

// Expose the new Context-Centric API
pub use compile_new::{CompilerContext, CrateIDWrapper, compile_contract_, compile_program_};

// Compiling a package TREE that lives in memory: `Nargo.toml` honoured, local `path`
// dependencies resolved inside the virtual filesystem, `git` dependencies refused by name.
// See `src/vfs.rs`.
pub use compile_vfs::{
    VfsRequest, VfsResponse, compile_contract_from_vfs, compile_program_from_vfs, resolve_vfs_plan,
    run_request, run_request_json,
};

// The bare `nv_*` C ABI. Re-exported rather than left inside a private module so that
// `unreachable_pub` is satisfied by the entry points being genuinely reachable, which is
// what they are: they are the module's exports.
#[cfg(target_arch = "wasm32")]
pub use compile_vfs::abi;
use wasm_bindgen::{JsValue, prelude::wasm_bindgen};

#[derive(Serialize, Deserialize)]
pub struct BuildInfo {
    git_hash: &'static str,
    version: &'static str,
    dirty: &'static str,
}

#[wasm_bindgen]
pub fn init_log_level(level: String) {
    // Set the static variable from Rust
    use std::sync::Once;

    let level_filter: EnvFilter =
        level.parse().expect("Could not parse log filter while initializing logger");

    static SET_HOOK: Once = Once::new();
    SET_HOOK.call_once(|| {
        let fmt_layer = tracing_subscriber::fmt::layer()
            .with_ansi(false)
            .without_time()
            .with_writer(MakeWebConsoleWriter::new());

        tracing_subscriber::registry().with(fmt_layer.with_filter(level_filter)).init();
    });
}

const BUILD_INFO: BuildInfo =
    BuildInfo { git_hash: GIT_COMMIT, version: NOIRC_VERSION, dirty: GIT_DIRTY };

#[wasm_bindgen]
pub fn build_info() -> JsValue {
    console_error_panic_hook::set_once();
    <JsValue as JsValueSerdeExt>::from_serde(&BUILD_INFO).unwrap()
}
