//! Tokio adapter for the sans-IO FIX session core.
//!
//! [`FixSession`] is a thin newtype over the sans-IO
//! [`nexus_fix_engine::FixSession`] brain: it [`Deref`]s to the
//! core so the whole seam (encode-only sends, [`poll`], [`message`], the byte
//! methods) is available unchanged, and it adds one thing — an async
//! [`recv`](FixSession::recv) that `.await`s socket I/O over any
//! [`WireStream`]. The caller holds the [`FixParts`] trio (session +
//! [`MessageReader`] + [`MessageWriter`]) and passes the reader/writer plus its
//! transport per call, exactly as in the blocking engine; only the socket I/O in
//! `recv` is `.await`ed.
//!
//! [`poll`]: nexus_fix_engine::FixSession::poll
//! [`message`]: nexus_fix_engine::FixSession::message
//!
//! # Transports
//!
//! Any [`WireStream`] works. Wrap a raw tokio `AsyncRead + AsyncWrite` stream (a
//! `TcpStream`, a mock) in [`AsyncReadAdapter`], or use the plaintext-or-TLS
//! [`MaybeTls`]. The socket is the caller's to open — reconnect is "same trio,
//! new socket."

#![cfg(unix)]
#![deny(
    rustdoc::broken_intra_doc_links,
    rustdoc::private_intra_doc_links,
    rustdoc::redundant_explicit_links
)]

use std::future::poll_fn;
use std::io;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::pin::Pin;

use nexus_fix_codec::{AsciiTextStr, FixDictionary, NoCustomizer, SessionCustomizer};
use nexus_fix_engine::{
    DisconnectReason, FixJournal, FixParts as CoreFixParts, FixSession as CoreFixSession,
    LogonDecision, Message, MessageReader, MessageWriter, PollOutcome, SessionConfig, SessionState,
};

/// Per-message resend reserve; see [`nexus_fix_engine::REFRAME_HEADROOM`].
pub use nexus_fix_engine::REFRAME_HEADROOM;
/// Shared session error type, re-exported from `nexus-fix-engine`.
///
/// This is the same `Error` the core returns; the async layer adds only socket
/// I/O errors via the existing `From<io::Error>` impl.
pub use nexus_fix_engine::TransportError as Error;
/// The transport trait every stream implements — re-exported so callers can name
/// the `S: WireStream` bound without depending on `nexus-net` directly.
pub use nexus_net::WireStream;
/// Tokio wire transports: wrap a raw stream in [`AsyncReadAdapter`], or use the
/// plaintext-or-TLS [`MaybeTls`]. Re-exported so callers need not depend on
/// `nexus-net-tokio` directly.
pub use nexus_net_tokio::{AsyncReadAdapter, MaybeTls};

/// Async FIX session over any [`WireStream`].
///
/// A newtype over the sans-IO [`nexus_fix_engine::FixSession`] core: it
/// [`Deref`]s to the core for the full sans-IO seam (encode-only sends, `poll`,
/// `message`, the byte methods) and adds an async [`recv`](Self::recv) that
/// `.await`s socket I/O. Build the [`FixParts`] trio with [`builder`](Self::builder),
/// or wrap an existing core session with [`new`](Self::new).
///
/// The crate namespace disambiguates this from the core
/// [`nexus_fix_engine::FixSession`] — the core is not re-exported here under the
/// same name.
pub struct FixSession<D: FixDictionary> {
    core: CoreFixSession<D>,
}

impl<D: FixDictionary> FixSession<D> {
    /// Wraps a sans-IO core session for `.await`ed I/O. Prefer
    /// [`builder`](Self::builder) to size the buffers and get a [`FixParts`] trio.
    pub fn new(core: CoreFixSession<D>) -> Self {
        Self { core }
    }

    /// Starts a [`FixSessionBuilder`] to configure and build a [`FixParts`] trio.
    pub fn builder() -> FixSessionBuilder<D, NoCustomizer> {
        FixSessionBuilder {
            reader_cap: 64 * 1024,
            writer_cap: 64 * 1024,
            customizer: NoCustomizer,
            _dict: PhantomData,
        }
    }

    /// Receives the next typed [`Message`] over any [`WireStream`] — the async
    /// twin of [`nexus_fix_engine::FixSession::recv`].
    ///
    /// Fills `reader` from `conn` copy-free (`poll_fill_into`), drives
    /// [`poll`](nexus_fix_engine::FixSession::poll), drains any *mechanism*
    /// outbound (reset handshake, protocol-error Logout, resend) from `writer` to
    /// `conn`, and returns the message. `Ok(None)` means a step produced nothing to
    /// surface (an out-of-sequence app, or a session-level reject). The session
    /// holds no timers, so `recv` simply awaits a full frame; run your own
    /// heartbeat/liveness timers alongside it (e.g. a `tokio::select!` over `recv`
    /// and your tickers).
    ///
    /// `now` (UTC unix-nanos) stamps `SendingTime(52)` on any mechanism emit the
    /// engine drives inside `recv`; the reply to the returned message is still
    /// yours to send with the send helpers.
    ///
    /// The returned `Message<'r>` borrows `reader`, *not* `&mut self`, so `&mut
    /// session` and `&mut writer` stay free for the reply while the payload is
    /// still borrowed.
    pub async fn recv<'r, C, S>(
        &mut self,
        reader: &'r mut MessageReader<D>,
        writer: &mut MessageWriter<D, C>,
        conn: &mut S,
        now: i128,
    ) -> Result<Option<Message<'r, D>>, Error>
    where
        C: SessionCustomizer,
        S: WireStream + Unpin,
    {
        if self.core.is_terminated() {
            return Err(Error::Closed);
        }
        // `recv_step` returns an *owned* outcome so this dispatch can arm the
        // terminated guard — on a clean logout or any fatal error — before
        // borrowing `reader` to reconstruct the message. The flag lives on the
        // core (a fresh `connect` clears it); we mark it via the wrapper-author API.
        match self.recv_step(reader, writer, conn, now).await {
            Ok(RecvStep::Message) => Ok(Some(self.core.message(reader))),
            Ok(RecvStep::LoggedOut) => {
                self.core.mark_terminated();
                Ok(Some(self.core.message(reader)))
            }
            Ok(RecvStep::Nothing) => Ok(None),
            Err(e) => {
                if e.is_fatal() {
                    self.core.mark_terminated();
                }
                Err(e)
            }
        }
    }

    /// Advances one step over a [`WireStream`], returning an *owned* [`RecvStep`].
    /// Fills `reader` from `conn` on `NeedMoreBytes` (copy-free `poll_fill_into`)
    /// and drains `writer` to `conn` after every `poll`.
    async fn recv_step<C, S>(
        &mut self,
        reader: &mut MessageReader<D>,
        writer: &mut MessageWriter<D, C>,
        conn: &mut S,
        now: i128,
    ) -> Result<RecvStep, Error>
    where
        C: SessionCustomizer,
        S: WireStream + Unpin,
    {
        loop {
            let outcome = self.core.poll(reader, writer, now)?;
            // Drain any admin/resend the core enqueued this step. Also flushes a
            // pending opening Logon / `send_app` staged before `recv`.
            drain_outbound(writer, conn).await?;

            match outcome {
                PollOutcome::Message => return Ok(RecvStep::Message),
                PollOutcome::LoggedOut => return Ok(RecvStep::LoggedOut),
                // Abnormal drop: a fault, surfaced as an error, not a message.
                PollOutcome::Disconnected(reason) => {
                    return Err(Error::UnexpectedDisconnect { reason });
                }
                PollOutcome::Suppressed => return Ok(RecvStep::Nothing),
                // Buffer already drained above; loop to continue the resend.
                PollOutcome::ResendPending => {}
                PollOutcome::NeedMoreBytes => {
                    // An empty spare means the reader buffer is full with a single
                    // incomplete frame that cannot grow (compaction reclaimed
                    // nothing). `poll_fill_into` would reject a zero-length spare
                    // with `InvalidInput`; surface the real cause instead — a frame
                    // larger than the reader buffer. Identical to the sync guard.
                    if reader.spare().is_empty() {
                        return Err(Error::MessageTooLarge(reader.capacity().saturating_add(1)));
                    }
                    // Fill the reader copy-free: `poll_fill_into` reads into
                    // `reader.spare()` and commits via `reader.filled` itself,
                    // returning the delivered count (`Ok(0)` = EOF). Cap the pull at
                    // the current spare length.
                    let max = reader.spare().len();
                    match poll_fn(|cx| Pin::new(&mut *conn).poll_fill_into(cx, reader, max)).await {
                        // Peer closed the transport (FIN) without a FIX Logout.
                        Ok(0) => {
                            return Err(Error::UnexpectedDisconnect {
                                reason: DisconnectReason::PeerClosed,
                            });
                        }
                        // Bytes already committed to the reader by `poll_fill_into`;
                        // loop to parse them.
                        Ok(_n) => {}
                        Err(e) => return Err(Error::Io(e)),
                    }
                }
            }
        }
    }

    // ── protocol actions — async combined (encode + flush over a WireStream) ──
    //
    // The async twin of the core's combined sends: encode via the core's
    // `encode_<action>` primitive (reached through `Deref`), then `.await` the
    // flush to `conn`. The encode-only primitives themselves are available
    // unchanged via `Deref` for the custom-transport / byte-seam path.

    /// Encodes a Logon and flushes it to `conn` (initiate the session). `now`
    /// stamps `SendingTime(52)` (UTC unix-nanos).
    pub async fn connect<C, S>(
        &mut self,
        writer: &mut MessageWriter<D, C>,
        conn: &mut S,
        now: i128,
    ) -> Result<(), Error>
    where
        C: SessionCustomizer,
        S: WireStream + Unpin,
    {
        self.core.encode_connect(writer, now)?;
        drain_outbound(writer, conn).await
    }

    /// Encodes a Logon with `ResetSeqNumFlag=Y` and flushes it to `conn`. `now`
    /// stamps `SendingTime(52)` (UTC unix-nanos).
    pub async fn connect_reset<C, S>(
        &mut self,
        writer: &mut MessageWriter<D, C>,
        conn: &mut S,
        now: i128,
    ) -> Result<(), Error>
    where
        C: SessionCustomizer,
        S: WireStream + Unpin,
    {
        self.core.encode_connect_reset(writer, now)?;
        drain_outbound(writer, conn).await
    }

    /// Encodes an in-session sequence reset handshake and flushes it to `conn`.
    /// `now` stamps `SendingTime(52)` (UTC unix-nanos).
    pub async fn reset_sequence<C, S>(
        &mut self,
        writer: &mut MessageWriter<D, C>,
        conn: &mut S,
        now: i128,
    ) -> Result<(), Error>
    where
        C: SessionCustomizer,
        S: WireStream + Unpin,
    {
        self.core.encode_reset_sequence(writer, now)?;
        drain_outbound(writer, conn).await
    }

    /// Encodes a Logout and flushes it to `conn`. Answers a
    /// [`Message::LogoutRequest`] or
    /// initiates a logout. `now` stamps `SendingTime(52)` (UTC unix-nanos).
    pub async fn logout<C, S>(
        &mut self,
        writer: &mut MessageWriter<D, C>,
        conn: &mut S,
        now: i128,
    ) -> Result<(), Error>
    where
        C: SessionCustomizer,
        S: WireStream + Unpin,
    {
        self.core.encode_logout(writer, now)?;
        drain_outbound(writer, conn).await
    }

    /// Encodes a Heartbeat (echoing `echo` if `Some`) and flushes it to `conn`.
    /// Answers a [`Message::TestRequest`] with `Some(id)` (the validated
    /// `TestReqID`). `now` stamps `SendingTime(52)` (UTC unix-nanos).
    pub async fn heartbeat<C, S>(
        &mut self,
        writer: &mut MessageWriter<D, C>,
        conn: &mut S,
        now: i128,
        echo: Option<&AsciiTextStr>,
    ) -> Result<(), Error>
    where
        C: SessionCustomizer,
        S: WireStream + Unpin,
    {
        self.core.encode_heartbeat(writer, now, echo)?;
        drain_outbound(writer, conn).await
    }

    /// Encodes a TestRequest and flushes it to `conn`. `now` stamps
    /// `SendingTime(52)` (UTC unix-nanos).
    pub async fn test_request<C, S>(
        &mut self,
        writer: &mut MessageWriter<D, C>,
        conn: &mut S,
        now: i128,
    ) -> Result<(), Error>
    where
        C: SessionCustomizer,
        S: WireStream + Unpin,
    {
        self.core.encode_test_request(writer, now)?;
        drain_outbound(writer, conn).await
    }

    /// Encodes a ResendRequest covering `[begin, ∞)` and flushes it to `conn`.
    /// Answers a [`Message::GapDetected`].
    /// `now` stamps `SendingTime(52)` (UTC unix-nanos).
    pub async fn resend_request<C, S>(
        &mut self,
        writer: &mut MessageWriter<D, C>,
        conn: &mut S,
        now: i128,
        begin: u32,
    ) -> Result<(), Error>
    where
        C: SessionCustomizer,
        S: WireStream + Unpin,
    {
        self.core.encode_resend_request(writer, now, begin)?;
        drain_outbound(writer, conn).await
    }

    /// Accepts a counterparty-initiated Logon surfaced as
    /// [`Message::LogonRequest`] /
    /// [`Message::LogonResetRequest`]:
    /// encodes the reply, advances the session, and flushes to `conn`. The async
    /// twin of [`LogonDecision::accept`]. `now` stamps `SendingTime(52)`.
    pub async fn accept_logon<C, S>(
        &mut self,
        decision: LogonDecision<'_, D>,
        writer: &mut MessageWriter<D, C>,
        conn: &mut S,
        now: i128,
    ) -> Result<(), Error>
    where
        C: SessionCustomizer,
        S: WireStream + Unpin,
    {
        decision.encode_accept(&mut self.core, writer, now)?;
        drain_outbound(writer, conn).await
    }

    /// Rejects a counterparty-initiated Logon: encodes a Logout, disconnects, and
    /// flushes to `conn`. The async twin of [`LogonDecision::reject`]. `now` stamps
    /// `SendingTime(52)`. **`reason` is captured for logging but NOT yet on the
    /// wire** — `Text(58)` wiring lands in phase 5.
    pub async fn reject_logon<C, S>(
        &mut self,
        decision: LogonDecision<'_, D>,
        writer: &mut MessageWriter<D, C>,
        conn: &mut S,
        now: i128,
        reason: &str,
    ) -> Result<(), Error>
    where
        C: SessionCustomizer,
        S: WireStream + Unpin,
    {
        decision.encode_reject(&mut self.core, writer, now, reason)?;
        drain_outbound(writer, conn).await
    }

    /// Journals, encodes an application frame at sequence `seq`, and flushes it to
    /// `conn`. See [`nexus_fix_engine::FixSession::encode_send_app`] for the
    /// frame-size constraint.
    pub async fn send_app<C, S>(
        &mut self,
        writer: &mut MessageWriter<D, C>,
        conn: &mut S,
        seq: u32,
        frame: &[u8],
    ) -> Result<(), Error>
    where
        C: SessionCustomizer,
        S: WireStream + Unpin,
    {
        self.core.encode_send_app(writer, seq, frame)?;
        drain_outbound(writer, conn).await
    }
}

impl<D: FixDictionary> Deref for FixSession<D> {
    type Target = CoreFixSession<D>;
    fn deref(&self) -> &Self::Target {
        &self.core
    }
}

impl<D: FixDictionary> DerefMut for FixSession<D> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.core
    }
}

/// The persistent async trio a caller holds.
///
/// The async [`FixSession`] plus its [`MessageReader`] and [`MessageWriter`].
/// Produced by [`FixSessionBuilder::build`]; the transport is separate and passed
/// per call.
pub struct FixParts<D: FixDictionary, C = NoCustomizer> {
    pub session: FixSession<D>,
    pub reader: MessageReader<D>,
    pub writer: MessageWriter<D, C>,
}

/// Builds an async [`FixParts`] trio.
///
/// Sizes the reader/writer buffers and attaches an optional per-venue
/// [`SessionCustomizer`]. The socket is the caller's to open. Mirrors
/// [`nexus_fix_engine::FixSessionBuilder`].
pub struct FixSessionBuilder<D: FixDictionary, C = NoCustomizer> {
    reader_cap: usize,
    writer_cap: usize,
    customizer: C,
    _dict: PhantomData<fn() -> D>,
}

impl<D: FixDictionary, C> FixSessionBuilder<D, C> {
    /// Inbound reader buffer capacity in bytes (default 64 KiB).
    pub fn reader_capacity(mut self, n: usize) -> Self {
        self.reader_cap = n;
        self
    }

    /// Outbound writer buffer capacity in bytes (default 64 KiB).
    pub fn writer_capacity(mut self, n: usize) -> Self {
        self.writer_cap = n;
        self
    }

    /// Attach a per-venue [`SessionCustomizer`]; changes the resulting
    /// [`MessageWriter`]'s customizer type to `C2`.
    pub fn customizer<C2: SessionCustomizer>(self, customizer: C2) -> FixSessionBuilder<D, C2> {
        FixSessionBuilder {
            reader_cap: self.reader_cap,
            writer_cap: self.writer_cap,
            customizer,
            _dict: PhantomData,
        }
    }
}

impl<D: FixDictionary, C: SessionCustomizer> FixSessionBuilder<D, C> {
    /// Builds the async [`FixParts`] trio from the configured capacities/customizer
    /// plus the session's `state`, `config`, and `journal`.
    pub fn build(
        self,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
    ) -> FixParts<D, C> {
        let CoreFixParts {
            session,
            reader,
            writer,
        } = CoreFixSession::builder()
            .reader_capacity(self.reader_cap)
            .writer_capacity(self.writer_cap)
            .customizer(self.customizer)
            .build(state, config, journal);
        FixParts {
            session: FixSession::new(session),
            reader,
            writer,
        }
    }
}

/// Owned outcome of one [`FixSession::recv_step`], so [`FixSession::recv`] can arm
/// the terminated guard before borrowing `reader` to reconstruct the message.
enum RecvStep {
    /// A typed message is ready; call `message()`.
    Message,
    /// A clean, negotiated logout ended the session.
    LoggedOut,
    /// Nothing to surface this step (a suppressed frame); `recv` returns `Ok(None)`.
    Nothing,
}

/// Writes all buffered outbound bytes in `writer` to the transport and flushes. A
/// `Pending` `poll_write` is write backpressure — the `.await` yields until the
/// transport is writable again.
async fn drain_outbound<D, C, S>(
    writer: &mut MessageWriter<D, C>,
    conn: &mut S,
) -> Result<(), Error>
where
    D: FixDictionary,
    S: WireStream + Unpin,
{
    while !writer.is_empty() {
        let n = poll_fn(|cx| Pin::new(&mut *conn).poll_write(cx, writer.data())).await?;
        if n == 0 {
            return Err(Error::Io(io::Error::other("write returned 0")));
        }
        writer.advance(n);
    }
    poll_fn(|cx| Pin::new(&mut *conn).poll_flush(cx)).await?;
    Ok(())
}
