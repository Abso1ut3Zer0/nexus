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

use nexus_fix_codec::FixDictionary;

use crate::fix_session::{FixSession, PollOutcome};
use crate::frame::FrameWriter;
use crate::framework::{Message, MessageReader, MessageWriter, SessionConfig, SessionError};
use crate::persist::FixJournal;
use crate::session::{DisconnectReason, SessionState, State};

pub use crate::fix_session::{Error, REFRAME_HEADROOM};

pub struct FixConnection<S, D: FixDictionary> {
    stream: S,
    session: FixSession<D>,
}

pub struct FixConnectionBuilder<D: FixDictionary> {
    reader_cap: usize,
    writer_cap: usize,
    nodelay: bool,
    connect_timeout: Option<Duration>,
    _dict: std::marker::PhantomData<fn() -> D>,
}

impl<D: FixDictionary> FixConnectionBuilder<D> {
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

    fn build_session(
        &self,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
    ) -> FixSession<D> {
        FixSession::from_buffers(
            MessageReader::with_frame_reader(
                crate::frame::FrameReader::builder()
                    .buffer_capacity(self.reader_cap)
                    .build(),
            ),
            MessageWriter::with_frame_writer(
                FrameWriter::builder()
                    .buffer_capacity(self.writer_cap)
                    .build(),
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
    ) -> io::Result<FixConnection<TcpStream, D>> {
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
        Ok(FixConnection { stream, session })
    }

    pub fn accept<S: Read + Write>(
        self,
        stream: S,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
    ) -> FixConnection<S, D> {
        let session = self.build_session(state, config, journal);
        FixConnection { stream, session }
    }
}

impl<D: FixDictionary> FixConnection<TcpStream, D> {
    pub fn builder() -> FixConnectionBuilder<D> {
        FixConnectionBuilder {
            reader_cap: 64 * 1024,
            writer_cap: 64 * 1024,
            nodelay: true,
            connect_timeout: None,
            _dict: std::marker::PhantomData,
        }
    }
}

impl<S: Read + Write, D: FixDictionary> FixConnection<S, D> {
    pub fn from_parts(
        stream: S,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
    ) -> Self {
        Self {
            stream,
            session: FixSession::new(state, config, journal),
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

    pub fn recv(&mut self, now: Instant) -> Result<Option<Message<'_, D>>, Error> {
        loop {
            let outcome = self.session.poll(now)?;
            // Drain any admin/resend the core enqueued for this step (matches the
            // original, which flushed after every protocol handler).
            self.drain_outbound()?;

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
                    // which the `Ok(0)` arm below would misread as EOF. Surface it
                    // as the real cause: a frame larger than the reader buffer.
                    if self.session.read_spare().is_empty() {
                        return Err(Error::MessageTooLarge(
                            self.session.reader_capacity().saturating_add(1),
                        ));
                    }
                    let spare = self.session.read_spare();
                    match self.stream.read(spare) {
                        Ok(0) => {
                            return Ok(Some(Message::Disconnected {
                                reason: DisconnectReason::Logout,
                            }));
                        }
                        Ok(n) => self.session.read_filled(n),
                        Err(e) if is_timeout(&e) => {
                            if let Some(reason) = self.session.on_timeout(now)? {
                                self.drain_outbound()?;
                                return Ok(Some(Message::Disconnected { reason }));
                            }
                            self.drain_outbound()?;
                            return Ok(None);
                        }
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
