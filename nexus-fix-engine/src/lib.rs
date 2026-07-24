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
//! - [`FixSession`] — the sans-IO *brain* that wraps [`SessionState`] with frame
//!   decode, journaling, encode, and resumable resend. It owns no buffers and no
//!   socket: the caller holds the [`FixParts`] trio (session + [`MessageReader`] +
//!   [`MessageWriter`]) and passes the reader/writer plus a transport per call.
//!   [`recv`](FixSession::recv) is the thin blocking convenience over the seam;
//!   the async twin, `nexus_async_fix_engine::FixSession::recv`, adds `.await`ed
//!   I/O over the same core.

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
pub use fix_session::{
    Error as TransportError, FixParts, FixSession, FixSessionBuilder, PollOutcome, REFRAME_HEADROOM,
};
pub use frame::{
    FrameError, FrameReader, FrameReaderBuilder, FrameWriter, FrameWriterBuilder, MalformedReason,
    ReadError,
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
