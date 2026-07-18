//! nexus-async-web — async adapters for nexus-web.
//!
//! Renamed from `nexus-async-net` as part of the nexus-net/nexus-web
//! crate restructure. Protocol types now come from nexus-web;
//! networking primitives (buffers, TLS, wire) remain in nexus-net.
//!
//! Thin async wrappers over nexus-web's synchronous protocol primitives.
//! Same zero-copy parsing, same performance — just `.await` on I/O.
//!
//! # Runtime Features
//!
//! Exactly one async runtime must be enabled (mutually exclusive):
//!
//! - **`tokio-rt`** (default) — tokio-based adapters for WebSocket and REST.
//! - **`nexus`** — nexus-async-rt-based adapters (single-threaded, pre-allocated).
//!   *(Renamed from `nexus-rt` in v0.4.2.)*
//!
//! # Modules
//!
//! - [`ws`] — Async WebSocket (wraps FrameReader/FrameWriter).
//!   Both backends provide `recv()`/`send_*()`. The tokio backend also
//!   implements `Stream`/`Sink` for ecosystem integration.
//! - [`rest`] — Async HTTP REST client (wraps RequestWriter/ResponseReader)
//!
//! # Custom transports
//!
//! `WsReader`/`WsWriter` and `HttpConnection<S>` accept any
//! [`WireStream`] — the canonical `MaybeTls`
//! transport implements it directly. To plug a custom
//! `AsyncRead+AsyncWrite` transport into the same API, wrap it at
//! the call site:
//!
//! - tokio (`feature = "tokio-rt"`): [`AsyncReadAdapter`]
//! - nexus-async-rt (`feature = "nexus"`): `NexusAsyncReadAdapter`
//!
//! ```ignore
//! let tcp = tokio::net::TcpStream::connect(addr).await?;
//! let (mut reader, mut writer, mut conn) = WsStreamBuilder::new()
//!     .connect_with(AsyncReadAdapter::new(tcp), url)
//!     .await?;
//! ```

#![warn(missing_docs)]

#[cfg(all(feature = "tokio-rt", feature = "nexus"))]
compile_error!("features `tokio-rt` and `nexus` are mutually exclusive — pick one async runtime");

// `maybe_tls` is implementation surface for the connection builders;
// exposed publicly only so integration tests in this crate's
// `tests/` directory can construct `TlsInner` directly (the test
// binary is a separate compilation unit).
#[doc(hidden)]
pub mod maybe_tls;
pub mod rest;
#[cfg(feature = "nexus")]
mod wire;
pub mod ws;

// The tokio adapter now lives in the `nexus-net-tokio` crate; re-export
// it so the `nexus_async_web::AsyncReadAdapter` path is unchanged.
#[cfg(feature = "tokio-rt")]
pub use nexus_net_tokio::AsyncReadAdapter;
#[cfg(feature = "nexus")]
pub use wire::NexusAsyncReadAdapter;

// Re-export nexus-web protocol types that appear in our public API.
// Users who need deeper access can depend on nexus-web directly.
pub use nexus_net::{WireStream, buf::WriteBuf};
pub use nexus_web::ws::{
    CloseCode, CloseFrame, Error as WsError, FrameReader, FrameReaderBuilder, FrameWriter,
    HandshakeError, Message, OwnedCloseFrame, OwnedMessage, Role,
};

/// REST types used in [`rest::HttpConnection`] and [`rest::ClientSlot`].
pub mod rest_types {
    pub use nexus_web::http::ResponseReader;
    pub use nexus_web::rest::{Request, RequestWriter, RestError, RestResponse};
}

#[cfg(feature = "tls")]
pub use nexus_net::tls::{TlsConfig, TlsError};
