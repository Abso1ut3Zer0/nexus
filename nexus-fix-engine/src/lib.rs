//! Sans-IO FIX session layer.
//!
//! [`SessionState`] is a pure state machine: the caller owns the transport,
//! the clock, and the wire encoding. Each typed handler (e.g.
//! [`SessionState::on_logon`], [`SessionState::on_app`]) receives pre-decoded
//! fields and returns an [`Out`] containing any outbound admin messages and a
//! session event. The framework layer above encodes those messages and drives
//! the transport.

mod frame;
mod framework;
#[cfg(unix)]
pub mod persist;
mod session;
#[cfg(unix)]
mod timestamp;
#[cfg(unix)]
pub mod transport;

pub use frame::{
    FrameError, FrameReader, FrameReaderBuilder, FrameWriter, FrameWriterBuilder, ReadError,
};
pub use framework::{CompId, Message, MessageReader, MessageWriter, SessionConfig, SessionError};
#[cfg(unix)]
pub use persist::{FixJournal, ReplayItem};
pub use session::{AdminMsg, DisconnectReason, Event, Out, SessionState, State};
#[cfg(unix)]
pub use transport::{Error as TransportError, FixConnection, FixConnectionBuilder};
