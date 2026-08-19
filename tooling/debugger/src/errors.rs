use thiserror::Error;

/// Errors raised while serving the Debug Adapter Protocol.
///
/// Gated on the `dap` feature: the `ServerError` variant wraps a type from the
/// `dap` crate, which is only a dependency when that front-end is compiled in.
#[cfg(feature = "dap")]
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
