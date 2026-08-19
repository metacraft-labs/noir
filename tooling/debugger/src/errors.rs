use thiserror::Error;

/// Errors raised while serving the Debug Adapter Protocol.
///
/// Gated on `cli`: the `ServerError` variant wraps a type from the `dap` crate,
/// which is only a dependency when the interactive front-ends are compiled in.
#[cfg(feature = "cli")]
#[derive(Debug, Error)]
pub enum DapError {
    #[error("{0}")]
    PreFlightGenericError(String),

    #[error(transparent)]
    LoadError(#[from] LoadError),

    #[error(transparent)]
    ServerError(#[from] dap::errors::ServerError),
}

#[derive(Debug, Error)]
pub enum LoadError {
    #[error("{0}")]
    Generic(String),
}
