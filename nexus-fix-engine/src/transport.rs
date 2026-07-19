//! Blocking, socket-owning FIX connection.
//!
//! [`FixConnection`] is a thin wrapper over the sans-IO [`FixSession`] core
//! ([`crate::fix_session`]): it owns the socket and does *only* the I/O —
//! `stream.read` into the session's inbound buffer, `stream.write` from its
//! outbound buffer. All protocol logic (framing, the state machine, journaling,
//! resend) lives in [`FixSession`].

use std::io::{self, Read, Write};
use std::net::{TcpStream, ToSocketAddrs};
use std::time::{Duration, Instant};

use nexus_fix_codec::{FixDictionary, NoCustomizer, SessionCustomizer};

use crate::fix_session::{FixSession, PollOutcome};
use crate::frame::FrameWriter;
use crate::framework::{Message, MessageReader, MessageWriter, SessionConfig, SessionError};
use crate::persist::FixJournal;
use crate::session::{DisconnectReason, SessionState, State};

pub use crate::fix_session::{Error, REFRAME_HEADROOM};

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

    pub fn connect(&mut self, now: Instant) -> Result<(), Error> {
        self.session.connect(now)?;
        self.drain_outbound()
    }

    pub fn connect_reset(&mut self, now: Instant) -> Result<(), Error> {
        self.session.connect_reset(now)?;
        self.drain_outbound()
    }

    pub fn reset_sequence(&mut self, now: Instant) -> Result<(), Error> {
        self.session.reset_sequence(now)?;
        self.drain_outbound()
    }

    pub fn send_app(&mut self, seq: u32, frame: &[u8]) -> Result<(), Error> {
        self.session.send_app(seq, frame)?;
        self.drain_outbound()
    }

    pub fn logout(&mut self, now: Instant) -> Result<(), Error> {
        self.session.logout(now)?;
        self.drain_outbound()
    }

    /// Blocks until the next inbound message.
    ///
    /// A pure receive: it never touches the session clock. Heartbeats and the
    /// logon/logout/test-request deadlines are the caller's policy — run
    /// [`tick`](Self::tick) on your own schedule (a bounded `try_recv` loop, or a
    /// separate thread).
    ///
    /// `now` is your duty-cycle clock reading. The core never reads the wall clock
    /// itself — that is what keeps the session deterministically replayable — so read
    /// `now` once per iteration, keep it monotonic, and pass the same value to
    /// `recv`/[`try_recv`](Self::try_recv) and [`tick`](Self::tick). It stamps
    /// `last_received` (the liveness clock); a `now` you let go stale backdates that
    /// conservatively — at worst an early, peer-answered TestRequest, never a false
    /// disconnect.
    ///
    /// Requires a **blocking** socket. On one this parks in the read syscall until
    /// bytes arrive; a read timeout (`SO_RCVTIMEO`) is transparent — a no-data wake
    /// is retried, so `recv` returns only with a message or an error and one
    /// read-timeout socket can back both `recv` and [`try_recv`](Self::try_recv). A
    /// **non-blocking** socket is a misuse: the retry has nothing to wait on and
    /// becomes a busy-spin. Use [`try_recv`](Self::try_recv) for non-blocking receipt.
    ///
    /// A clean logout arrives as [`Message::LoggedOut`]; an abnormal end as
    /// `Err(UnexpectedDisconnect)`. After any terminal outcome further calls return
    /// `Err(Closed)`. A malformed frame is a recoverable `Err(Malformed)` — the
    /// session stays live and the caller may call again.
    pub fn recv(&mut self, now: Instant) -> Result<Message<'_, D>, Error> {
        if self.terminated {
            return Err(Error::Closed);
        }
        let step = loop {
            match self.poll_buffered(now) {
                Ok(Some(step)) => break step,
                // No complete frame buffered — block for more bytes and re-poll.
                Ok(None) => {
                    if let Err(e) = self.blocking_read() {
                        return Err(self.note_fatal(e));
                    }
                }
                Err(e) => return Err(self.note_fatal(e)),
            }
        };
        Ok(self.finish(step))
    }

    /// Returns the next ready message without blocking, or `None` when nothing is
    /// ready.
    ///
    /// A pure receive: never touches the clock (see [`tick`](Self::tick)). Requires
    /// a **non-blocking** socket — or one with a read timeout, for a bounded wait,
    /// where `None` means the timeout elapsed. After any terminal outcome further
    /// calls return `Err(Closed)`.
    pub fn try_recv(&mut self, now: Instant) -> Result<Option<Message<'_, D>>, Error> {
        if self.terminated {
            return Err(Error::Closed);
        }
        let step = loop {
            match self.poll_buffered(now) {
                Ok(Some(step)) => break step,
                Ok(None) => match self.read_available() {
                    Ok(true) => {}                // got bytes — re-poll
                    Ok(false) => return Ok(None), // nothing ready
                    Err(e) => return Err(self.note_fatal(e)),
                },
                Err(e) => return Err(self.note_fatal(e)),
            }
        };
        Ok(Some(self.finish(step)))
    }

    /// Services the session clock: sends any due Heartbeat/TestRequest and enforces
    /// the logon/logout/test-request/reset deadlines. No `recv*` method does this —
    /// the caller drives `tick` on its own schedule (`select!` in async, a timeout
    /// loop in sync). Returns `Err(UnexpectedDisconnect)` if a deadline blew.
    ///
    /// Pass the same duty-cycle `now` you give [`recv`](Self::recv) — one monotonic
    /// reading per iteration, shared by both. See `recv` for the clock contract.
    pub fn tick(&mut self, now: Instant) -> Result<(), Error> {
        if self.terminated {
            return Err(Error::Closed);
        }
        let reason = match self.session.on_timeout(now) {
            Ok(r) => r,
            Err(e) => return Err(self.note_fatal(e)),
        };
        if let Err(e) = self.drain_outbound() {
            return Err(self.note_fatal(e));
        }
        reason.map_or(Ok(()), |reason| {
            Err(self.note_fatal(Error::UnexpectedDisconnect { reason }))
        })
    }

    /// The earliest instant at which [`tick`](Self::tick) next has work — the next
    /// heartbeat, TestRequest, or deadline. `None` when disconnected. Use it to size
    /// a bounded `try_recv` wait or a `select!` sleep.
    pub fn next_timeout(&self) -> Option<Instant> {
        self.session.state().next_timeout()
    }

    /// Arms the terminated guard on a fatal error (so the next call is `Closed`) and
    /// hands the error back. A recoverable `Malformed` leaves the session live.
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

    /// Poll + drain buffered inbound frames without reading the socket. `Some(step)`
    /// when a message/logout is ready, `None` when a socket read is needed. Suppressed
    /// frames and in-progress resends are consumed internally.
    fn poll_buffered(&mut self, now: Instant) -> Result<Option<RecvStep>, Error> {
        loop {
            let outcome = self.session.poll(now)?;
            // Flush any admin/resend the core enqueued (matches the original, which
            // flushed after every protocol handler).
            self.drain_outbound()?;
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
                    // cannot grow: a frame larger than the reader buffer.
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

    /// Blocks until at least one byte arrives: a read yielding no data is retried.
    /// Never services the clock.
    fn blocking_read(&mut self) -> Result<(), Error> {
        // Each read blocks; retry a spurious no-data wake until bytes arrive.
        while !self.read_available()? {}
        Ok(())
    }

    /// One socket read. `Ok(true)` = bytes delivered, `Ok(false)` = no data ready
    /// (would-block / read timeout). A read of `Ok(0)` is a peer EOF.
    fn read_available(&mut self) -> Result<bool, Error> {
        let spare = self.session.read_spare();
        match self.stream.read(spare) {
            // Peer closed the transport (FIN) without a FIX Logout.
            Ok(0) => Err(Error::UnexpectedDisconnect {
                reason: DisconnectReason::PeerClosed,
            }),
            Ok(n) => {
                self.session.read_filled(n);
                Ok(true)
            }
            Err(e) if is_timeout(&e) => Ok(false),
            Err(e) => Err(Error::Io(e)),
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
