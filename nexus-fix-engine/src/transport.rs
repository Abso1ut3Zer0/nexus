//! Blocking, socket-owning FIX connection.
//!
//! [`FixConnection`] is a thin wrapper over the sans-IO [`FixSession`] core
//! ([`crate::fix_session`]): it owns the socket and does *only* the I/O —
//! `stream.read` into the session's inbound buffer, `stream.write` from its
//! outbound buffer. All protocol logic (framing, the state machine, journaling,
//! resend) lives in [`FixSession`].

use std::io::{self, Read, Write};
use std::net::{TcpStream, ToSocketAddrs};
use std::time::Duration;

use nexus_fix_codec::{FixDictionary, NoCustomizer, SessionCustomizer};

use crate::fix_session::{FixSession, PollOutcome};
use crate::frame::FrameWriter;
use crate::framework::{Message, MessageReader, MessageWriter, SessionConfig, SessionError};
use crate::persist::FixJournal;
use crate::session::{DisconnectReason, SessionState, State};

pub use crate::fix_session::{Error, REFRAME_HEADROOM};

/// Owned outcome of one [`FixConnection::recv`] step. Returned by the internal
/// `recv_step` so `recv` can arm the terminated guard — on any fatal error or a
/// clean logout — before borrowing `self` to reconstruct the borrowed message.
enum RecvStep {
    /// A typed message is ready; call `message()`.
    Message,
    /// A clean, negotiated logout ended the session.
    LoggedOut,
    /// Nothing to surface this step (a suppressed frame, or a caller-set socket
    /// read timeout elapsing with no complete frame); the wrapper returns `Ok(None)`.
    Nothing,
}

/// Blocking FIX session transport.
///
/// `C` is the per-venue [`SessionCustomizer`] applied to outbound admin
/// messages, defaulting to [`NoCustomizer`] — plain-FIX callers write
/// `FixConnection<TcpStream, Fix44>` and never name it. Attach one with
/// [`FixConnectionBuilder::customizer`].
pub struct FixConnection<S, D: FixDictionary, C = NoCustomizer> {
    stream: S,
    session: FixSession<D, C>,
    /// Set once a terminal outcome (a `LoggedOut` message or a fatal error) has
    /// been surfaced; a subsequent `recv` returns `Err(Error::Closed)`.
    terminated: bool,
}

pub struct FixConnectionBuilder<D: FixDictionary, C = NoCustomizer> {
    reader_cap: usize,
    writer_cap: usize,
    nodelay: bool,
    connect_timeout: Option<Duration>,
    customizer: C,
    _dict: std::marker::PhantomData<fn() -> D>,
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

    pub fn connect_timeout(mut self, d: Duration) -> Self {
        self.connect_timeout = Some(d);
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
            connect_timeout: self.connect_timeout,
            customizer,
            _dict: std::marker::PhantomData,
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
                crate::frame::FrameReader::builder()
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

    pub fn connect<A: ToSocketAddrs>(
        self,
        addr: A,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
    ) -> io::Result<FixConnection<TcpStream, D, C>> {
        let stream = match self.connect_timeout {
            Some(t) => {
                let addrs: Vec<_> = addr.to_socket_addrs()?.collect();
                let first = addrs
                    .first()
                    .ok_or_else(|| io::Error::other("DNS resolved to zero addresses"))?;
                TcpStream::connect_timeout(first, t)?
            }
            None => TcpStream::connect(addr)?,
        };
        stream.set_nodelay(self.nodelay)?;
        let session = self.build_session(state, config, journal);
        Ok(FixConnection {
            stream,
            session,
            terminated: false,
        })
    }

    pub fn accept<S: Read + Write>(
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

impl<D: FixDictionary> FixConnection<TcpStream, D, NoCustomizer> {
    pub fn builder() -> FixConnectionBuilder<D, NoCustomizer> {
        FixConnectionBuilder {
            reader_cap: 64 * 1024,
            writer_cap: 64 * 1024,
            nodelay: true,
            connect_timeout: None,
            customizer: NoCustomizer,
            _dict: std::marker::PhantomData,
        }
    }
}

impl<S: Read + Write, D: FixDictionary> FixConnection<S, D, NoCustomizer> {
    pub fn from_parts(
        stream: S,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
    ) -> Self {
        Self::from_parts_with_customizer(stream, state, config, journal, NoCustomizer)
    }
}

impl<S: Read + Write, D: FixDictionary, C: SessionCustomizer> FixConnection<S, D, C> {
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

    /// The negotiated heartbeat interval (`HeartBtInt(108)`) — build your own
    /// keepalive/liveness timers from it; the session holds none.
    pub fn heartbeat_interval(&self) -> Duration {
        self.session.heartbeat_interval()
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

    pub fn flush(&mut self) -> Result<(), Error> {
        self.drain_outbound()
    }

    pub fn connect(&mut self) -> Result<(), Error> {
        self.session.connect()?;
        self.drain_outbound()
    }

    pub fn connect_reset(&mut self) -> Result<(), Error> {
        self.session.connect_reset()?;
        self.drain_outbound()
    }

    pub fn reset_sequence(&mut self) -> Result<(), Error> {
        self.session.reset_sequence()?;
        self.drain_outbound()
    }

    pub fn send_app(&mut self, seq: u32, frame: &[u8]) -> Result<(), Error> {
        self.session.send_app(seq, frame)?;
        self.drain_outbound()
    }

    pub fn logout(&mut self) -> Result<(), Error> {
        self.session.logout()?;
        self.drain_outbound()
    }

    pub fn recv(&mut self) -> Result<Option<Message<'_, D>>, Error> {
        if self.terminated {
            return Err(Error::Closed);
        }
        match self.recv_step() {
            Ok(RecvStep::Message) => Ok(Some(self.session.message())),
            // Clean, negotiated logout: the graceful terminal event.
            Ok(RecvStep::LoggedOut) => {
                self.terminated = true;
                Ok(Some(self.session.message()))
            }
            Ok(RecvStep::Nothing) => Ok(None),
            // Any fatal error ends the session, so the next `recv` is `Closed`; a
            // recoverable error (`Malformed`) leaves the session live.
            Err(e) => {
                if e.is_fatal() {
                    self.terminated = true;
                }
                Err(e)
            }
        }
    }

    /// Advances the session one step, returning an *owned* outcome. Splitting this
    /// from [`recv`](Self::recv) lets `recv` arm the terminated guard (on any fatal
    /// error or a clean logout) before borrowing `self` to build the message.
    fn recv_step(&mut self) -> Result<RecvStep, Error> {
        loop {
            let outcome = self.session.poll()?;
            // Drain any admin/resend the core enqueued for this step (matches the
            // original, which flushed after every protocol handler).
            self.drain_outbound()?;

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
                    // nothing). Reading into a zero-length slice yields `Ok(0)`,
                    // which the `Ok(0)` arm below would misread as EOF. Surface it
                    // as the real cause: a frame larger than the reader buffer.
                    if self.session.read_spare().is_empty() {
                        return Err(Error::MessageTooLarge(
                            self.session.reader_capacity().saturating_add(1),
                        ));
                    }
                    let spare = self.session.read_spare();
                    match self.stream.read(spare) {
                        // Peer closed the transport (FIN) without a FIX Logout.
                        Ok(0) => {
                            return Err(Error::UnexpectedDisconnect {
                                reason: DisconnectReason::PeerClosed,
                            });
                        }
                        Ok(n) => self.session.read_filled(n),
                        // A caller-set socket read timeout elapsed with no complete
                        // frame. The session holds no timers, so there is nothing to
                        // service — yield control so the caller can run its own
                        // heartbeat/liveness timers, then call `recv` again.
                        Err(e) if is_timeout(&e) => return Ok(RecvStep::Nothing),
                        Err(e) => return Err(Error::Io(e)),
                    }
                }
            }
        }
    }

    /// Writes all buffered outbound bytes to the socket and flushes.
    fn drain_outbound(&mut self) -> Result<(), Error> {
        while self.session.has_outbound() {
            let n = self
                .stream
                .write(self.session.outbound())
                .map_err(Error::Io)?;
            if n == 0 {
                return Err(Error::Io(io::Error::other("write returned 0")));
            }
            self.session.advance_outbound(n);
        }
        self.stream.flush().map_err(Error::Io)
    }
}

fn is_timeout(e: &io::Error) -> bool {
    matches!(
        e.kind(),
        io::ErrorKind::TimedOut | io::ErrorKind::WouldBlock
    )
}
