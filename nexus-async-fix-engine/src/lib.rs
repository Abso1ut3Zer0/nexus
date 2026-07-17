//! Tokio adapter for the sans-IO FIX session core.
//!
//! [`FixConnection`] is a thin wrapper over the sans-IO [`FixSession`] core: it
//! owns a tokio `AsyncRead + AsyncWrite` stream and does *only* the I/O —
//! `stream.read` into the session's inbound buffer, `stream.write` from its
//! outbound buffer, both `.await`ed. All protocol logic (framing, the state
//! machine, journaling, resend) lives in [`FixSession`]; this crate is the exact
//! async analog of the blocking
//! [`nexus_fix_engine::FixConnection`], differing
//! only in that socket I/O is `.await`ed and heartbeat/TestRequest deadlines use
//! `tokio::time`.

#![cfg(unix)]
#![deny(
    rustdoc::broken_intra_doc_links,
    rustdoc::private_intra_doc_links,
    rustdoc::redundant_explicit_links
)]

use std::io;
use std::marker::PhantomData;
use std::time::{Duration, Instant};

use nexus_fix_codec::{FixDictionary, NoCustomizer, SessionCustomizer};
use nexus_fix_engine::{
    DisconnectReason, FixJournal, FixSession, FrameReader, FrameWriter, Message, MessageReader,
    MessageWriter, PollOutcome, SessionConfig, SessionError, SessionState, State,
};
use tokio::io::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt};
use tokio::time::timeout_at;

/// Per-message resend reserve; see [`nexus_fix_engine::REFRAME_HEADROOM`].
pub use nexus_fix_engine::REFRAME_HEADROOM;
/// Shared session-core error type, re-exported from `nexus-fix-engine`.
///
/// This is the same `Error` [`FixSession`] returns; the async wrapper adds only
/// socket I/O errors via the existing `From<io::Error>` impl.
pub use nexus_fix_engine::TransportError as Error;

/// Async FIX session transport over any tokio `AsyncRead + AsyncWrite` stream.
///
/// Thin wrapper over [`FixSession`]: the socket calls are `.await`ed; everything
/// else — framing, the [`SessionState`] machine, journaling, resend — is in the
/// shared core. This is the async twin of
/// [`nexus_fix_engine::FixConnection`].
///
/// `C` is the per-venue [`SessionCustomizer`] applied to outbound admin
/// messages, defaulting to [`NoCustomizer`] — plain-FIX callers write
/// `FixConnection<TcpStream, Fix44>` and never name it. Attach one with
/// [`FixConnectionBuilder::customizer`].
pub struct FixConnection<S, D: FixDictionary, C = NoCustomizer> {
    stream: S,
    session: FixSession<D, C>,
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

    /// Connects a TCP stream, applies `TCP_NODELAY`, and wraps it.
    pub async fn connect(
        self,
        addr: std::net::SocketAddr,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
    ) -> io::Result<FixConnection<tokio::net::TcpStream, D, C>> {
        let stream = tokio::net::TcpStream::connect(addr).await?;
        stream.set_nodelay(self.nodelay)?;
        let session = self.build_session(state, config, journal);
        Ok(FixConnection { stream, session })
    }

    /// Wraps an already-connected stream (acceptor role or a pre-built stream).
    pub fn accept<S: AsyncRead + AsyncWrite + Unpin>(
        self,
        stream: S,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
    ) -> FixConnection<S, D, C> {
        let session = self.build_session(state, config, journal);
        FixConnection { stream, session }
    }
}

impl<D: FixDictionary> FixConnection<tokio::net::TcpStream, D, NoCustomizer> {
    pub fn builder() -> FixConnectionBuilder<D, NoCustomizer> {
        FixConnectionBuilder {
            reader_cap: 64 * 1024,
            writer_cap: 64 * 1024,
            nodelay: true,
            customizer: NoCustomizer,
            _dict: PhantomData,
        }
    }

    /// Connects a TCP stream, enables `TCP_NODELAY`, and wraps it with default
    /// buffer sizes.
    pub async fn tcp_connect(
        addr: std::net::SocketAddr,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
    ) -> io::Result<Self> {
        Self::builder().connect(addr, state, config, journal).await
    }
}

impl<S: AsyncRead + AsyncWrite + Unpin, D: FixDictionary> FixConnection<S, D, NoCustomizer> {
    pub fn from_parts(
        stream: S,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
    ) -> Self {
        Self::from_parts_with_customizer(stream, state, config, journal, NoCustomizer)
    }
}

impl<S: AsyncRead + AsyncWrite + Unpin, D: FixDictionary, C: SessionCustomizer>
    FixConnection<S, D, C>
{
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
        loop {
            let outcome = self.session.poll(now)?;
            // Drain any admin/resend the core enqueued for this step (matches the
            // sync wrapper, which flushes after every protocol handler).
            self.drain_outbound().await?;

            match outcome {
                PollOutcome::Message | PollOutcome::Disconnected(_) => {
                    return Ok(Some(self.session.message()));
                }
                PollOutcome::Suppressed => return Ok(None),
                // Buffer already drained above; loop to continue the resend.
                PollOutcome::ResendPending => {}
                PollOutcome::NeedMoreBytes => {
                    // An empty spare means the reader buffer is full with a single
                    // incomplete frame that cannot grow (compaction reclaimed
                    // nothing). Reading into a zero-length slice yields `Ok(0)`,
                    // which the `Ok(Ok(0))` arm below would misread as EOF. Surface
                    // it as the real cause: a frame larger than the reader buffer.
                    // Identical to the sync wrapper's guard.
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
                    let spare = self.session.read_spare();
                    match timeout_at(deadline, self.stream.read(spare)).await {
                        Ok(Ok(0)) => {
                            return Ok(Some(Message::Disconnected {
                                reason: DisconnectReason::Logout,
                            }));
                        }
                        Ok(Ok(n)) => self.session.read_filled(n),
                        Ok(Err(e)) => return Err(Error::Io(e)),
                        Err(_elapsed) => {
                            if let Some(reason) = self.session.on_timeout(now)? {
                                self.drain_outbound().await?;
                                return Ok(Some(Message::Disconnected { reason }));
                            }
                            self.drain_outbound().await?;
                            return Ok(None);
                        }
                    }
                }
            }
        }
    }

    /// Writes all buffered outbound bytes to the socket and flushes.
    async fn drain_outbound(&mut self) -> Result<(), Error> {
        while self.session.has_outbound() {
            let n = self.stream.write(self.session.outbound()).await?;
            if n == 0 {
                return Err(Error::Io(io::Error::other("write returned 0")));
            }
            self.session.advance_outbound(n);
        }
        self.stream.flush().await?;
        Ok(())
    }
}
