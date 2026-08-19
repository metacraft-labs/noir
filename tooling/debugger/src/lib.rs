#![forbid(unsafe_code)]
#![cfg_attr(not(test), warn(unused_crate_dependencies, unused_extern_crates))]
#![expect(unreachable_pub)] // This crate is full of issues related to this lint

pub mod context;
pub mod errors;
pub mod foreign_calls;

// The interactive front-ends. They need a terminal (`easy-repl`, `owo-colors`)
// and a DAP transport (`dap`), neither of which exists on e.g.
// `wasm32-unknown-unknown`, so they are gated behind the default-on `cli`
// feature. `context` and `foreign_calls` above -- everything a programmatic
// consumer such as the tracer needs -- stay unconditional.
#[cfg(feature = "cli")]
mod dap;
#[cfg(feature = "cli")]
mod repl;
#[cfg(feature = "cli")]
mod source_code_printer;

// TODO: extract these pub structs to its own module
pub use context::DebugExecutionResult;
pub use context::DebugProject;
pub use context::RunParams;

#[cfg(feature = "cli")]
mod cli_entry {
    use super::{DebugExecutionResult, DebugProject, RunParams};
    use ::dap::errors::ServerError;
    use ::dap::server::Server;
    use std::io::{Read, Write};

    pub fn run_repl_session(
        project: DebugProject,
        run_params: RunParams,
    ) -> DebugExecutionResult {
        crate::repl::run(project, run_params)
    }

    pub fn run_dap_loop<R: Read, W: Write>(
        server: &mut Server<R, W>,
        project: DebugProject,
        run_params: RunParams,
    ) -> Result<DebugExecutionResult, ServerError> {
        crate::dap::run_session(server, project, run_params)
    }
}

#[cfg(feature = "cli")]
pub use cli_entry::{run_dap_loop, run_repl_session};
