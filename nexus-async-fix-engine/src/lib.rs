//! Tokio adapter for the sans-IO FIX session core.
//!
//! [`FixConnection`] is a thin wrapper over the sans-IO [`FixSession`] core: it
//! owns a [`WireStream`] transport and does *only* the
//! I/O — `poll_fill_into` fills the session's inbound buffer copy-free,
//! `poll_write`/`poll_flush` drain its outbound buffer, all `.await`ed. All
//! protocol logic (framing, the state machine, journaling, resend) lives in
//! [`FixSession`]; this crate is the exact async analog of the blocking
//! [`nexus_fix_engine::FixConnection`], differing only in that socket I/O is
//! `.await`ed. `recv`/`try_recv` never service the session clock — heartbeats and
//! the logon/logout/test-request deadlines are the caller's policy: drive
//! [`FixConnection::tick`] from a `select!` timer branch (the receive path no longer
//! uses a `tokio::time` timer, so it is driven only by the executor and the
//! [`WireStream`]).
//!
//! # Transports
//!
//! Any [`WireStream`] works. Two are provided out of the
//! box:
//!
//! - [`MaybeTls`] — plaintext or transparent TLS, built by
//!   [`FixConnectionBuilder::connect`] / [`connect_tls`](FixConnectionBuilder::connect_tls).
//! - [`AsyncReadAdapter`] — wraps a raw tokio `AsyncRead + AsyncWrite` stream
//!   (a `TcpStream`, a mock) as a `WireStream`; pass it to
//!   [`from_parts`](FixConnection::from_parts) / [`accept`](FixConnectionBuilder::accept).

#![cfg(unix)]
#![deny(
    rustdoc::broken_intra_doc_links,
    rustdoc::private_intra_doc_links,
    rustdoc::redundant_explicit_links
)]

use std::future::poll_fn;
use std::io;
use std::marker::PhantomData;
use std::pin::Pin;
use std::task::{Context, Poll, Waker};
use std::time::Instant;

use nexus_fix_codec::{FixDictionary, NoCustomizer, SessionCustomizer};
use nexus_fix_engine::{
    DisconnectReason, FixJournal, FixSession, FrameReader, FrameWriter, Message, MessageReader,
    MessageWriter, PollOutcome, SessionConfig, SessionError, SessionState, State,
};

/// Per-message resend reserve; see [`nexus_fix_engine::REFRAME_HEADROOM`].
pub use nexus_fix_engine::REFRAME_HEADROOM;
/// Shared session-core error type, re-exported from `nexus-fix-engine`.
///
/// This is the same `Error` [`FixSession`] returns; the async wrapper adds only
/// socket I/O errors via the existing `From<io::Error>` impl.
pub use nexus_fix_engine::TransportError as Error;
/// The transport trait every stream implements — re-exported so callers can name
/// the `S: WireStream` bound without depending on `nexus-net` directly. Also
/// used internally as the bound on [`FixConnection`]'s I/O methods.
pub use nexus_net::WireStream;
/// Tokio wire transports: wrap a raw stream in [`AsyncReadAdapter`], or use the
/// plaintext-or-TLS [`MaybeTls`]. Re-exported so callers need not depend on
/// `nexus-net-tokio` directly.
pub use nexus_net_tokio::{AsyncReadAdapter, MaybeTls};

/// Owned outcome of one buffered receive step ([`FixConnection::poll_buffered`]),
/// so the public `recv`/`try_recv` can arm the terminated guard — on any fatal
/// error or a clean logout — before borrowing `self` to reconstruct the message.
#[derive(Clone, Copy)]
enum RecvStep {
    /// A typed message is ready; call `message()`.
    Message,
    /// A clean, negotiated logout ended the session.
    LoggedOut,
}

/// Async FIX session transport over any [`WireStream`].
///
/// Thin wrapper over [`FixSession`]: the socket calls are `.await`ed; everything
/// else — framing, the [`SessionState`] machine, journaling, resend — is in the
/// shared core. This is the async twin of
/// [`nexus_fix_engine::FixConnection`].
///
/// `C` is the per-venue [`SessionCustomizer`] applied to outbound admin
/// messages, defaulting to [`NoCustomizer`] — plain-FIX callers write
/// `FixConnection<MaybeTls, Fix44>` and never name it. Attach one with
/// [`FixConnectionBuilder::customizer`].
pub struct FixConnection<S, D: FixDictionary, C = NoCustomizer> {
    stream: S,
    session: FixSession<D, C>,
    /// Set once a terminal outcome (a `LoggedOut` message or a fatal error) has
    /// been surfaced; a subsequent `recv` returns `Err(Error::Closed)`.
    terminated: bool,
}

/// Builder for [`FixConnection`], mirroring the sync
/// [`FixConnectionBuilder`](nexus_fix_engine::FixConnectionBuilder).
pub struct FixConnectionBuilder<D: FixDictionary, C = NoCustomizer> {
    reader_cap: usize,
    writer_cap: usize,
    nodelay: bool,
    customizer: C,
    _dict: PhantomData<fn() -> D>,
}

impl<D: FixDictionary, C> FixConnectionBuilder<D, C> {
    pub fn reader_capacity(mut self, n: usize) -> Self {
        self.reader_cap = n;
        self
    }

    pub fn writer_capacity(mut self, n: usize) -> Self {
        self.writer_cap = n;
        self
    }

    pub fn nodelay(mut self, v: bool) -> Self {
        self.nodelay = v;
        self
    }

    /// Attach a per-venue [`SessionCustomizer`] — the hook that injects Logon
    /// auth (e.g. `Username(553)`/`Password(554)`/`RawData(96)`).
    ///
    /// Changes the builder's customizer type, so the resulting
    /// [`FixConnection`] carries `C2`.
    pub fn customizer<C2: SessionCustomizer>(self, customizer: C2) -> FixConnectionBuilder<D, C2> {
        FixConnectionBuilder {
            reader_cap: self.reader_cap,
            writer_cap: self.writer_cap,
            nodelay: self.nodelay,
            customizer,
            _dict: PhantomData,
        }
    }
}

impl<D: FixDictionary, C: SessionCustomizer> FixConnectionBuilder<D, C> {
    fn build_session(
        self,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
    ) -> FixSession<D, C> {
        FixSession::from_buffers(
            MessageReader::with_frame_reader(
                FrameReader::builder()
                    .buffer_capacity(self.reader_cap)
                    .build(),
            ),
            MessageWriter::with_frame_writer_and_customizer(
                FrameWriter::builder()
                    .buffer_capacity(self.writer_cap)
                    .build(),
                self.customizer,
            ),
            state,
            config,
            journal,
        )
    }

    /// Connects a plaintext TCP stream, applies `TCP_NODELAY`, and wraps it in a
    /// [`MaybeTls::Plain`] transport.
    pub async fn connect(
        self,
        addr: std::net::SocketAddr,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
    ) -> io::Result<FixConnection<MaybeTls, D, C>> {
        let tcp = tokio::net::TcpStream::connect(addr).await?;
        tcp.set_nodelay(self.nodelay)?;
        let session = self.build_session(state, config, journal);
        Ok(FixConnection {
            stream: MaybeTls::Plain(tcp),
            session,
            terminated: false,
        })
    }

    /// Connects a TCP stream, performs a TLS handshake with `server_name`, and
    /// wraps it in a [`MaybeTls::Tls`] transport — the transparent-TLS path for
    /// crypto venues. `TCP_NODELAY` is applied before the handshake.
    #[cfg(feature = "tls")]
    pub async fn connect_tls(
        self,
        addr: std::net::SocketAddr,
        server_name: &str,
        tls_config: &nexus_net::tls::TlsConfig,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
    ) -> io::Result<FixConnection<MaybeTls, D, C>> {
        let tcp = tokio::net::TcpStream::connect(addr).await?;
        tcp.set_nodelay(self.nodelay)?;
        let connector = tokio_rustls::TlsConnector::from(tls_config.client_config().clone());
        let dns = tokio_rustls::rustls::pki_types::ServerName::try_from(server_name.to_owned())
            .map_err(|_| {
                io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("invalid TLS hostname: {server_name}"),
                )
            })?;
        let tls_stream = connector.connect(dns, tcp).await?;
        let session = self.build_session(state, config, journal);
        Ok(FixConnection {
            stream: MaybeTls::Tls(Box::new(tls_stream)),
            session,
            terminated: false,
        })
    }

    /// Wraps an already-connected [`WireStream`] (acceptor
    /// role or a pre-built stream). Wrap a raw tokio stream in
    /// [`AsyncReadAdapter`] first.
    pub fn accept<S: WireStream + Unpin>(
        self,
        stream: S,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
    ) -> FixConnection<S, D, C> {
        let session = self.build_session(state, config, journal);
        FixConnection {
            stream,
            session,
            terminated: false,
        }
    }
}

impl<D: FixDictionary> FixConnection<MaybeTls, D, NoCustomizer> {
    pub fn builder() -> FixConnectionBuilder<D, NoCustomizer> {
        FixConnectionBuilder {
            reader_cap: 64 * 1024,
            writer_cap: 64 * 1024,
            nodelay: true,
            customizer: NoCustomizer,
            _dict: PhantomData,
        }
    }

    /// Connects a plaintext TCP stream, enables `TCP_NODELAY`, and wraps it in a
    /// [`MaybeTls::Plain`] transport with default buffer sizes.
    pub async fn tcp_connect(
        addr: std::net::SocketAddr,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
    ) -> io::Result<Self> {
        Self::builder().connect(addr, state, config, journal).await
    }
}

impl<S: WireStream + Unpin, D: FixDictionary> FixConnection<S, D, NoCustomizer> {
    pub fn from_parts(
        stream: S,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
    ) -> Self {
        Self::from_parts_with_customizer(stream, state, config, journal, NoCustomizer)
    }
}

impl<S: WireStream + Unpin, D: FixDictionary, C: SessionCustomizer> FixConnection<S, D, C> {
    /// As [`from_parts`](Self::from_parts), with a per-venue
    /// [`SessionCustomizer`] and default (unsized) buffers.
    pub fn from_parts_with_customizer(
        stream: S,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
        customizer: C,
    ) -> Self {
        Self {
            stream,
            session: FixSession::new_with_customizer(state, config, journal, customizer),
            terminated: false,
        }
    }

    pub fn state(&self) -> &SessionState {
        self.session.state()
    }

    pub fn state_mut(&mut self) -> &mut SessionState {
        self.session.state_mut()
    }

    pub fn garbage_frame_count(&self) -> u64 {
        self.session.garbage_frame_count()
    }

    pub fn allocate_seq(&mut self) -> Result<u32, SessionError> {
        self.session.allocate_seq()
    }

    pub fn wants_read(&self) -> bool {
        self.session.state().state() != State::Disconnected
    }

    pub fn wants_write(&self) -> bool {
        self.session.has_outbound()
    }

    pub async fn flush(&mut self) -> Result<(), Error> {
        self.drain_outbound().await
    }

    /// Initiates a session: enqueues and sends the opening Logon.
    pub async fn connect(&mut self, now: Instant) -> Result<(), Error> {
        self.session.connect(now)?;
        self.drain_outbound().await
    }

    /// Initiates a session with `ResetSeqNumFlag(141)=Y`.
    pub async fn connect_reset(&mut self, now: Instant) -> Result<(), Error> {
        self.session.connect_reset(now)?;
        self.drain_outbound().await
    }

    /// Initiates an in-session sequence reset.
    pub async fn reset_sequence(&mut self, now: Instant) -> Result<(), Error> {
        self.session.reset_sequence(now)?;
        self.drain_outbound().await
    }

    /// Journals then sends an application frame at sequence `seq`.
    pub async fn send_app(&mut self, seq: u32, frame: &[u8]) -> Result<(), Error> {
        self.session.send_app(seq, frame)?;
        self.drain_outbound().await
    }

    /// Initiates a clean logout.
    pub async fn logout(&mut self, now: Instant) -> Result<(), Error> {
        self.session.logout(now)?;
        self.drain_outbound().await
    }

    /// Awaits the next inbound message.
    ///
    /// A pure receive: it never touches the session clock. Heartbeats and the
    /// logon/logout/test-request deadlines are the caller's policy — drive
    /// [`tick`](Self::tick) from a `select!` timer branch. A clean logout arrives
    /// as [`Message::LoggedOut`]; an abnormal end as `Err(UnexpectedDisconnect)`.
    /// After any terminal outcome further calls return `Err(Closed)`. A malformed
    /// frame is a recoverable `Err(Malformed)` — the session stays live.
    ///
    /// **Cancellation:** dropping this future (e.g. losing a `select!` race) is safe
    /// at the socket read — the usual cancellation point — and for any message that
    /// carries no reply (application messages, plain heartbeats). A message that
    /// triggers an outbound reply (a TestRequest, a resend, an acceptor Logon, the
    /// Logout ack) flushes that reply before returning, so a future dropped *during
    /// that write* — only reachable under write back-pressure — can drop the
    /// just-processed message. With write headroom on the link the window never arises.
    pub async fn recv(&mut self, now: Instant) -> Result<Message<'_, D>, Error> {
        if self.terminated {
            return Err(Error::Closed);
        }
        let step = loop {
            match self.poll_buffered(now).await {
                Ok(Some(step)) => break step,
                // No complete frame buffered — await more bytes and re-poll.
                Ok(None) => {
                    if let Err(e) = self.await_read().await {
                        return Err(self.note_fatal(e));
                    }
                }
                Err(e) => return Err(self.note_fatal(e)),
            }
        };
        Ok(self.finish(step))
    }

    /// Returns the next ready message without awaiting, or `None` when nothing is
    /// ready (a single `Pending` transport poll). A pure receive — never touches the
    /// clock (see [`tick`](Self::tick)). After any terminal outcome further calls
    /// return `Err(Closed)`.
    pub async fn try_recv(&mut self, now: Instant) -> Result<Option<Message<'_, D>>, Error> {
        if self.terminated {
            return Err(Error::Closed);
        }
        let step = loop {
            match self.poll_buffered(now).await {
                Ok(Some(step)) => break step,
                Ok(None) => match self.poll_read_once() {
                    Ok(true) => {}                // got bytes — re-poll
                    Ok(false) => return Ok(None), // Pending — nothing ready
                    Err(e) => return Err(self.note_fatal(e)),
                },
                Err(e) => return Err(self.note_fatal(e)),
            }
        };
        Ok(Some(self.finish(step)))
    }

    /// Services the session clock: sends any due Heartbeat/TestRequest and enforces
    /// the logon/logout/test-request/reset deadlines. No `recv*` method does this —
    /// drive `tick` from a `select!` timer branch. Returns `Err(UnexpectedDisconnect)`
    /// if a deadline blew.
    pub async fn tick(&mut self, now: Instant) -> Result<(), Error> {
        if self.terminated {
            return Err(Error::Closed);
        }
        let reason = match self.session.on_timeout(now) {
            Ok(r) => r,
            Err(e) => return Err(self.note_fatal(e)),
        };
        if let Err(e) = self.drain_outbound().await {
            return Err(self.note_fatal(e));
        }
        reason.map_or(Ok(()), |reason| {
            Err(self.note_fatal(Error::UnexpectedDisconnect { reason }))
        })
    }

    /// The earliest instant at which [`tick`](Self::tick) next has work — the next
    /// heartbeat, TestRequest, or deadline. `None` when disconnected. Use it to size
    /// a `select!` sleep.
    pub fn next_timeout(&self) -> Option<Instant> {
        self.session.state().next_timeout()
    }

    /// Arms the terminated guard on a fatal error (so the next call is `Closed`) and
    /// hands the error back; a recoverable `Malformed` leaves the session live.
    fn note_fatal(&mut self, e: Error) -> Error {
        if e.is_fatal() {
            self.terminated = true;
        }
        e
    }

    /// Reconstructs the borrowed message for a completed step, arming the guard on a
    /// clean logout (the graceful terminal event).
    fn finish(&mut self, step: RecvStep) -> Message<'_, D> {
        if matches!(step, RecvStep::LoggedOut) {
            self.terminated = true;
        }
        self.session.message()
    }

    /// Poll + drain buffered inbound frames without reading the transport.
    /// `Some(step)` when a message/logout is ready, `None` when a read is needed.
    /// Suppressed frames and in-progress resends are consumed internally.
    async fn poll_buffered(&mut self, now: Instant) -> Result<Option<RecvStep>, Error> {
        loop {
            let outcome = self.session.poll(now)?;
            // Flush admin/resend the core enqueued — for a terminal outcome this is the
            // final message (a Logout ack, a Reject), which MUST reach the wire before
            // the caller's loop ends, so the drain stays after `poll`. See `recv` for
            // the cancellation caveat this implies.
            self.drain_outbound().await?;
            match outcome {
                PollOutcome::Message => return Ok(Some(RecvStep::Message)),
                PollOutcome::LoggedOut => return Ok(Some(RecvStep::LoggedOut)),
                PollOutcome::Disconnected(reason) => {
                    return Err(Error::UnexpectedDisconnect { reason });
                }
                // A buffered frame processed with nothing to surface, or a resend in
                // progress: keep draining buffered data.
                PollOutcome::Suppressed | PollOutcome::ResendPending => {}
                PollOutcome::NeedMoreBytes => {
                    // Empty spare = the buffer is full with one incomplete frame that
                    // cannot grow: a frame larger than the reader buffer. (Also the
                    // zero-length slice `poll_fill_into` would reject.)
                    if self.session.read_spare().is_empty() {
                        return Err(Error::MessageTooLarge(
                            self.session.reader_capacity().saturating_add(1),
                        ));
                    }
                    return Ok(None);
                }
            }
        }
    }

    /// Awaits one copy-free fill from the transport. `poll_fill_into` reads into
    /// `read_spare()` and commits via `read_filled`, returning the delivered count
    /// (`Ok(0)` = EOF).
    async fn await_read(&mut self) -> Result<(), Error> {
        let max = self.session.read_spare().len();
        let n = poll_fn(|cx| Pin::new(&mut self.stream).poll_fill_into(cx, &mut self.session, max))
            .await
            .map_err(Error::Io)?;
        if n == 0 {
            // Peer closed the transport (FIN) without a FIX Logout.
            return Err(Error::UnexpectedDisconnect {
                reason: DisconnectReason::PeerClosed,
            });
        }
        Ok(())
    }

    /// Polls the transport once with a no-op waker (non-blocking). `Ok(true)` = bytes
    /// delivered, `Ok(false)` = `Pending` (nothing ready). A read of `Ok(0)` is EOF.
    fn poll_read_once(&mut self) -> Result<bool, Error> {
        let max = self.session.read_spare().len();
        let mut cx = Context::from_waker(Waker::noop());
        match Pin::new(&mut self.stream).poll_fill_into(&mut cx, &mut self.session, max) {
            // Peer closed the transport (FIN) without a FIX Logout.
            Poll::Ready(Ok(0)) => Err(Error::UnexpectedDisconnect {
                reason: DisconnectReason::PeerClosed,
            }),
            Poll::Ready(Ok(_n)) => Ok(true),
            Poll::Ready(Err(e)) => Err(Error::Io(e)),
            Poll::Pending => Ok(false),
        }
    }

    /// Writes all buffered outbound bytes to the transport and flushes. A
    /// `Pending` `poll_write` is write backpressure — the `.await` yields until
    /// the transport is writable again.
    async fn drain_outbound(&mut self) -> Result<(), Error> {
        while self.session.has_outbound() {
            let n =
                poll_fn(|cx| Pin::new(&mut self.stream).poll_write(cx, self.session.outbound()))
                    .await?;
            if n == 0 {
                return Err(Error::Io(io::Error::other("write returned 0")));
            }
            self.session.advance_outbound(n);
        }
        poll_fn(|cx| Pin::new(&mut self.stream).poll_flush(cx)).await?;
        Ok(())
    }
}
