//! Sans-IO FIX session layer.
//!
//! [`SessionState`] is a pure state machine: the caller owns the transport,
//! the clock, and the wire encoding. Each typed handler (e.g.
//! [`SessionState::on_logon`], [`SessionState::on_app`]) receives pre-decoded
//! fields plus an `emit` closure for outbound admin messages, and returns a
//! [`Control`] verdict. The framework layer above supplies the closure (which
//! encodes and journals) and reconstructs the borrowed message from the verdict.
//!
//! # Layering
//!
//! - [`SessionState`] — the pure protocol state machine (above).
//! - [`FixSession`] — the sans-IO core that wraps [`SessionState`] with frame
//!   decode, journaling, encode, and resumable resend, exposing a
//!   [`poll`](FixSession::poll) / [`recv`](FixConnection::recv)-shaped API that
//!   owns everything *except* the socket. This is the reusable core an
//!   integrator drives from their own I/O loop.
//! - [`FixConnection`] — a thin blocking wrapper that adds only the socket I/O
//!   over [`FixSession`]. The async twin, `nexus_async_fix_engine::FixConnection`,
//!   wraps the same [`FixSession`] with `.await`ed I/O.

#![deny(
    rustdoc::broken_intra_doc_links,
    rustdoc::private_intra_doc_links,
    rustdoc::redundant_explicit_links
)]

#[cfg(unix)]
pub mod fix_session;
mod frame;
mod framework;
#[cfg(unix)]
pub mod persist;
mod session;
#[cfg(unix)]
mod timestamp;
#[cfg(unix)]
pub mod transport;

#[cfg(unix)]
pub use fix_session::{FixSession, PollOutcome};
pub use frame::{
    FrameError, FrameReader, FrameReaderBuilder, FrameWriter, FrameWriterBuilder, ReadError,
};
#[cfg(unix)]
pub use framework::Emitter;
pub use framework::{CompId, Message, MessageReader, MessageWriter, SessionConfig, SessionError};
#[cfg(unix)]
pub use nexus_journal::{Conductor, ConductorBuilder, OpenError, OpenMode, WriteError};
#[cfg(unix)]
pub use persist::{FixJournal, ReplayItem};
pub use session::{
    AppIn, Control, DisconnectReason, Emit, HeartbeatIn, LogonIn, LogoutIn, RejectIn,
    RejectInboundIn, ResendRequestIn, SequenceResetIn, SessionState, State, TestRequestIn,
};
#[cfg(unix)]
pub use transport::{
    Error as TransportError, FixConnection, FixConnectionBuilder, REFRAME_HEADROOM,
};
