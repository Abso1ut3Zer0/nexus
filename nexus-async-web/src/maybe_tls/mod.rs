//! MaybeTls — plain TCP or TLS, unified async I/O.
//!
//! The tokio `MaybeTls` now lives in the `nexus-net-tokio` crate and is
//! re-exported here so `crate::maybe_tls::MaybeTls` resolves unchanged.
//! The experimental nexus-async-rt backend keeps its own `MaybeTls`
//! (and `TlsInner`) in the `nexus` submodule.

#[cfg(feature = "nexus")]
mod nexus;

#[cfg(feature = "nexus")]
pub use self::nexus::*;
#[cfg(feature = "tokio-rt")]
pub use nexus_net_tokio::MaybeTls;
