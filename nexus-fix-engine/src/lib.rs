//! Sans-IO FIX session layer.
//!
//! [`SessionState`] is a pure state machine: the caller owns the transport,
//! the clock, and the wire encoding. Each typed handler (e.g.
//! [`SessionState::on_logon`], [`SessionState::on_app`]) receives pre-decoded
//! fields and returns an [`Out`] containing any outbound admin messages and a
//! session event. The framework layer above encodes those messages and drives
//! the transport.
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
pub use framework::{CompId, Message, MessageReader, MessageWriter, SessionConfig, SessionError};
#[cfg(unix)]
pub use nexus_journal::{Conductor, ConductorBuilder, OpenError, OpenMode, WriteError};
#[cfg(unix)]
pub use persist::{FixJournal, ReplayItem};
pub use session::{AdminMsg, DisconnectReason, Event, Out, SessionState, State};
#[cfg(unix)]
pub use transport::{
    Error as TransportError, FixConnection, FixConnectionBuilder, REFRAME_HEADROOM,
};
