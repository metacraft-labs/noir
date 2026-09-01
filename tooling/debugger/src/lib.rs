#![forbid(unsafe_code)]
#![cfg_attr(not(test), warn(unused_crate_dependencies, unused_extern_crates))]

//! Stepping execution of Noir programs.
//!
//! The crate is split into a portable core and a set of optional front-ends:
//!
//! * [`context`] and [`foreign_calls`] hold the stepping core. They only depend
//!   on the compiler and the ACVM, so they build for any target the ACVM builds
//!   for, including `wasm32-unknown-unknown`.
//! * The `repl` feature adds the interactive terminal front-end behind
//!   [`run_repl_session`], and the `dap` feature adds the Debug Adapter Protocol
//!   server behind [`run_dap_loop`]. Both are enabled by default and both
//!   require the `rpc` feature, which resolves oracle calls over HTTP.
//!
//! An embedder that drives stepping itself — an editor extension, a tracing
//! tool, or a browser-hosted debugger — can depend on this crate with
//! `default-features = false` and use [`context::DebugContext`] directly.

pub mod aztec_oracles;
pub mod context;
pub mod errors;
pub mod foreign_calls;

#[cfg(feature = "dap")]
mod dap;
#[cfg(feature = "repl")]
mod repl;
#[cfg(feature = "repl")]
mod source_code_printer;

// TODO: extract these pub structs to its own module
pub use context::DebugExecutionResult;
pub use context::DebugProject;
pub use context::RunParams;

#[cfg(feature = "repl")]
pub fn run_repl_session(project: DebugProject, run_params: RunParams) -> DebugExecutionResult {
    repl::run(project, run_params)
}

#[cfg(feature = "dap")]
pub fn run_dap_loop<R: std::io::Read, W: std::io::Write>(
    server: &mut ::dap::server::Server<R, W>,
    project: DebugProject,
    run_params: RunParams,
) -> Result<DebugExecutionResult, ::dap::errors::ServerError> {
    dap::run_session(server, project, run_params)
}
