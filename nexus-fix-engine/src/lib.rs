//! A sans-IO FIX session **framework** — mechanism, not policy.
//!
//! We frame, checksum, sequence, journal, and track protocol state. *You* own the
//! loop, the timers, and every decision: comply with a resend or refuse it, accept
//! a Logon or reject it, when to disconnect and why. If you want a
//! batteries-included engine, you wrap this and expose a callback API; this is the
//! layer underneath.
//!
//! # The three-object trio
//!
//! The caller holds a [`FixParts`] trio and passes the buffers plus a transport
//! per call — the session never owns the socket, so reconnect is "same session,
//! new socket" (sequence numbers and the journal survive):
//!
//! - [`FixSession`] — the sans-IO *brain*: state machine (`next_in`/`next_out`/
//!   phase/HBI) + journal + encode. No buffers, no socket. Owns every protocol verb.
//! - [`MessageReader`] — the inbound `ReadBuf` and reassembled frame.
//! - [`MessageWriter`] — the outbound `WriteBuf` and per-venue customizer.
//!
//! [`SessionState`] is the pure protocol state machine underneath [`FixSession`];
//! use it directly only for a fully custom encode/journal layer.
//!
//! # Receive: one variant, one required response
//!
//! [`recv`](FixSession::recv) fills `reader` from the transport, advances the state
//! machine, and returns a [`Message`] borrowing `reader` only — so `&mut session`
//! and `&mut writer` stay free to send the reply while the borrowed payload is
//! still alive. Every variant states its single obligation:
//!
//! | [`Message`] variant | Your required response |
//! |---|---|
//! | [`Application`] | route/decode — your business logic |
//! | [`TestRequest`] `{ id }` | `heartbeat(w, conn, now, Some(id))` |
//! | [`Heartbeat`] / [`Reject`] / [`SequenceReset`] | none (inspect/log) |
//! | [`GapDetected`] `{ begin }` | `resend_request(w, conn, now, begin)` |
//! | [`ResendRequest`] `{ cursor }` | pump the [`ResendCursor`] (drop = refuse) |
//! | [`ResendOutOfRange`] `{ .. }` | `sequence_reset`/`gap_fill`, or log out |
//! | [`LogonRequest`] / [`LogonResetRequest`] `(decision)` | `decision.accept(..)` or `.reject(.., reason)` |
//! | [`LogonAcknowledged`] | none — session is live |
//! | [`LogoutRequest`] | `logout(w, conn, now, reason)` |
//! | [`LoggedOut`] | none — clean terminal |
//!
//! An *abnormal* end never appears as a variant — it surfaces as a
//! [`TransportError`] error (an `UnexpectedDisconnect`), not a message.
//!
//! # Send helpers — two forms each
//!
//! Every protocol action has an **encode-only** form (`encode_heartbeat`,
//! `encode_logout`, …) that fills `writer` for a custom / kernel-bypass transport
//! (drain via `writer.data()`), and a **combined** form (`heartbeat`, `logout`, …)
//! that encodes and flushes through `conn` in one call. `logout` and
//! `LogonDecision::reject` take `reason: Option<&AsciiTextStr>`, encoded as
//! `Text(58)` when `Some`.
//!
//! # Deterministic clock
//!
//! The core reads **no clock of its own**. Every `SendingTime(52)` stamps from a
//! caller-supplied `now: i128` (UTC unix-nanos) passed to `recv` and the send
//! helpers, so the core is a pure function of `(bytes, now)` — fully replayable
//! for testing and historical replay. `now` is the *wall clock*; it has nothing to
//! do with timers.
//!
//! # Timers are yours
//!
//! The session holds **no timers** — it exposes only
//! [`heartbeat_interval`](FixSession::heartbeat_interval). You own three:
//! (1) a heartbeat ticker, (2) a two-phase peer-liveness probe (reset on *any*
//! inbound), and (3) a handshake/logout deadline. Getting timer 2 wrong leaves a
//! dead peer unnoticed, so the worked, runnable recipes are a first-class
//! deliverable: see `examples/timer_recipes.rs` (blocking) and its tokio twin in
//! `nexus-async-fix-engine`.
//!
//! # Async
//!
//! The async twin, `nexus_async_fix_engine::FixSession`, is a newtype that
//! [`Deref`](core::ops::Deref)s to this core: the whole sans-IO seam (encode-only
//! sends, `poll`, the byte methods) is available unchanged, and it adds a `recv`
//! that `.await`s I/O over any `nexus_net::WireStream`.
//!
//! [`Application`]: Message::Application
//! [`TestRequest`]: Message::TestRequest
//! [`Heartbeat`]: Message::Heartbeat
//! [`Reject`]: Message::Reject
//! [`SequenceReset`]: Message::SequenceReset
//! [`GapDetected`]: Message::GapDetected
//! [`ResendRequest`]: Message::ResendRequest
//! [`ResendOutOfRange`]: Message::ResendOutOfRange
//! [`LogonRequest`]: Message::LogonRequest
//! [`LogonResetRequest`]: Message::LogonResetRequest
//! [`LogonAcknowledged`]: Message::LogonAcknowledged
//! [`LogoutRequest`]: Message::LogoutRequest
//! [`LoggedOut`]: Message::LoggedOut

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
pub use framework::{
    CompId, LogonDecision, Message, MessageReader, MessageWriter, ResendCursor, SessionConfig,
    SessionError,
};
#[cfg(unix)]
pub use nexus_journal::{Conductor, ConductorBuilder, OpenError, OpenMode, WriteError};
#[cfg(unix)]
pub use persist::{FixJournal, ReplayItem};
pub use session::{
    AppIn, Control, DisconnectReason, Emit, HeartbeatIn, LogonIn, LogoutIn, RejectIn,
    RejectInboundIn, ResendRequestIn, SequenceResetIn, SessionState, State, TestRequestIn,
};
