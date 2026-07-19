//! Tokio adapter for the sans-IO FIX session core.
//!
//! [`FixConnection`] is a thin wrapper over the sans-IO [`FixSession`] core: it
//! owns a [`WireStream`] transport and does *only* the
//! I/O — `poll_fill_into` fills the session's inbound buffer copy-free,
//! `poll_write`/`poll_flush` drain its outbound buffer, all `.await`ed. All
//! protocol logic (framing, the state machine, journaling, resend) lives in
//! [`FixSession`]; this crate is the exact async analog of the blocking
//! [`nexus_fix_engine::FixConnection`], differing only in that socket I/O is
//! `.await`ed and heartbeat/TestRequest deadlines use `tokio::time`.
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
use std::time::{Duration, Instant};

use nexus_fix_codec::{FixDictionary, NoCustomizer, SessionCustomizer};
use nexus_fix_engine::{
    DisconnectReason, FixJournal, FixSession, FrameReader, FrameWriter, Message, MessageReader,
    MessageWriter, PollOutcome, SessionConfig, SessionError, SessionState, State,
};
use tokio::time::timeout_at;

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

    /// Processes buffered inbound frames, reading more bytes when needed and
    /// firing heartbeat/TestRequest timers on read idle. Returns the next typed
    /// [`Message`], or `None` when a step produced nothing to surface (an
    /// out-of-sequence app, a session reject, or a fired timer that did not
    /// disconnect). Mirrors the sync
    /// [`FixConnection::recv`](nexus_fix_engine::FixConnection::recv) loop with
    /// `.await` on the socket read and a `tokio::time` deadline in place of the
    /// blocking socket read-timeout.
    pub async fn recv(&mut self, now: Instant) -> Result<Option<Message<'_, D>>, Error> {
        if self.terminated {
            return Err(Error::Closed);
        }
        loop {
            let outcome = self.session.poll(now)?;
            // Drain any admin/resend the core enqueued for this step (matches the
            // sync wrapper, which flushes after every protocol handler).
            self.drain_outbound().await?;

            match outcome {
                PollOutcome::Message => return Ok(Some(self.session.message())),
                // Clean, negotiated logout: the graceful terminal event.
                PollOutcome::LoggedOut => {
                    self.terminated = true;
                    return Ok(Some(self.session.message()));
                }
                // Abnormal drop: a fault, surfaced as an error, not a message.
                PollOutcome::Disconnected(reason) => {
                    self.terminated = true;
                    return Err(Error::UnexpectedDisconnect { reason });
                }
                PollOutcome::Suppressed => return Ok(None),
                // Buffer already drained above; loop to continue the resend.
                PollOutcome::ResendPending => {}
                PollOutcome::NeedMoreBytes => {
                    // An empty spare means the reader buffer is full with a single
                    // incomplete frame that cannot grow (compaction reclaimed
                    // nothing). `poll_fill_into` would reject a zero-length spare
                    // with `InvalidInput`; surface the real cause instead — a frame
                    // larger than the reader buffer. Identical to the sync wrapper's
                    // guard.
                    if self.session.read_spare().is_empty() {
                        return Err(Error::MessageTooLarge(
                            self.session.reader_capacity().saturating_add(1),
                        ));
                    }
                    // No socket-level read timeout on an async stream, so bound
                    // the read with the session's next heartbeat/TestRequest
                    // deadline (60s fallback when the state machine has no timer).
                    let deadline = self.session.state().next_timeout().map_or_else(
                        || tokio::time::Instant::now() + Duration::from_secs(60),
                        tokio::time::Instant::from_std,
                    );
                    // Fill the session's inbound buffer copy-free: `poll_fill_into`
                    // reads into `read_spare()` and commits via `read_filled` itself,
                    // returning the delivered count (`Ok(0)` = EOF). Cap the pull at
                    // the current spare length.
                    let max = self.session.read_spare().len();
                    match timeout_at(
                        deadline,
                        poll_fn(|cx| {
                            Pin::new(&mut self.stream).poll_fill_into(cx, &mut self.session, max)
                        }),
                    )
                    .await
                    {
                        Ok(Ok(0)) => {
                            // Peer closed the transport (FIN) without a FIX Logout.
                            self.terminated = true;
                            return Err(Error::UnexpectedDisconnect {
                                reason: DisconnectReason::PeerClosed,
                            });
                        }
                        // Bytes already committed to the session by `poll_fill_into`;
                        // loop to parse them.
                        Ok(Ok(_n)) => {}
                        Ok(Err(e)) => return Err(Error::Io(e)),
                        Err(_elapsed) => {
                            if let Some(reason) = self.session.on_timeout(now)? {
                                self.drain_outbound().await?;
                                self.terminated = true;
                                return Err(Error::UnexpectedDisconnect { reason });
                            }
                            self.drain_outbound().await?;
                            return Ok(None);
                        }
                    }
                }
            }
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
