//! Batteries for the sans-IO FIX session — socket setup, in two layers.
//!
//! The framework proper is the raw three-object trio ([`FixSession`] +
//! [`MessageReader`] + [`MessageWriter`], transport passed per call). This module
//! adds the *socket-setup* conveniences on top, in the same primary/secondary split
//! `nexus-web` uses for WebSocket (`WsStreamBuilder` → raw parts, `WsStream` →
//! owns-everything):
//!
//! ## B — [`FixConnectionBuilder`] → raw parts (the primary batteries)
//!
//! [`FixConnectionBuilder::connect`] / [`accept`](FixConnectionBuilder::accept)
//! open the socket and hand back the [`FixParts`] trio **plus** the socket:
//! `(FixParts<D, C>, S)`. You destructure and run the ordinary three-object loop —
//! `session.recv(&mut reader, &mut writer, &mut conn, now)` and the send helpers —
//! which keeps admin replies **zero-copy** (the `Message` borrows only `reader`, so
//! `&mut session` / `&mut writer` / `&mut conn` stay free to reply). This is why B
//! is primary: no borrow of the whole connection, no copy-out.
//!
//! Reconnect is "keep the [`FixParts`], grab a new socket":
//! [`FixConnectionBuilder::connect_socket`] opens *just* the socket. Sequence
//! numbers and the journal live in the retained `FixParts`, so a reconnect is one
//! call and no re-bundling.
//!
//! ## A — [`FixConnection`] owns everything (the secondary one-object convenience)
//!
//! [`FixConnection`] bundles the trio *and* the socket into one object with `recv`
//! and delegating send helpers, for callers who want to pass a single value around.
//! Build it from B's parts with [`from_parts`](FixConnection::from_parts), or in one
//! step with [`FixConnection::open`]. The trade-off is a borrow one: because the
//! bundle owns everything, [`recv`](FixConnection::recv) returns a `Message<'_>`
//! borrowing the *whole* connection, so answering an admin message copies its small
//! reply field out first (echo a `TestReqID`) — see [`recv`](FixConnection::recv).
//! Reach for A for the ergonomic single object; reach for B (the default) for
//! zero-copy replies, a custom transport, or the acceptor-side
//! [`LogonDecision`](crate::LogonDecision).

use std::io::{self, Read, Write};
use std::marker::PhantomData;
use std::net::{TcpStream, ToSocketAddrs};
use std::time::Duration;

use nexus_fix_codec::{AsciiTextStr, FixDictionary, NoCustomizer, SessionCustomizer};

use crate::fix_session::{Error, FixParts, FixSession};
use crate::framework::{Message, MessageReader, MessageWriter, SessionConfig, SessionError};
use crate::persist::FixJournal;
use crate::session::SessionState;

// =============================================================================
// FixConnectionBuilder — B: setup terminals return raw parts
// =============================================================================

/// Builds the FIX socket-setup batteries — buffer sizes, an optional per-venue
/// [`SessionCustomizer`], and the socket options applied on a
/// [`connect`](Self::connect).
///
/// The setup terminals return the **raw [`FixParts`] trio plus the socket**
/// (`(FixParts<D, C>, S)`) — the primary path, run with the ordinary three-object
/// loop. Wrap the result in a [`FixConnection`] only if you want the one-object
/// convenience.
///
/// `C` is the customizer type, defaulting to [`NoCustomizer`]; attach one with
/// [`customizer`](Self::customizer).
pub struct FixConnectionBuilder<D: FixDictionary, C = NoCustomizer> {
    reader_cap: usize,
    writer_cap: usize,
    customizer: C,
    nodelay: bool,
    read_timeout: Option<Duration>,
    _dict: PhantomData<fn() -> D>,
}

impl<D: FixDictionary> FixConnectionBuilder<D, NoCustomizer> {
    /// A new builder with 64 KiB buffers, no customizer, Nagle enabled, and no
    /// read timeout.
    #[must_use]
    pub fn new() -> Self {
        Self {
            reader_cap: 64 * 1024,
            writer_cap: 64 * 1024,
            customizer: NoCustomizer,
            nodelay: false,
            read_timeout: None,
            _dict: PhantomData,
        }
    }
}

impl<D: FixDictionary> Default for FixConnectionBuilder<D, NoCustomizer> {
    fn default() -> Self {
        Self::new()
    }
}

impl<D: FixDictionary, C> FixConnectionBuilder<D, C> {
    /// Inbound reader buffer capacity in bytes (largest single frame; default 64 KiB).
    #[must_use]
    pub fn reader_capacity(mut self, n: usize) -> Self {
        self.reader_cap = n;
        self
    }

    /// Outbound writer buffer capacity in bytes (default 64 KiB). The largest app
    /// frame you can send is `writer_capacity` minus
    /// [`REFRAME_HEADROOM`](crate::REFRAME_HEADROOM).
    #[must_use]
    pub fn writer_capacity(mut self, n: usize) -> Self {
        self.writer_cap = n;
        self
    }

    /// Set `TCP_NODELAY` (disable Nagle's algorithm) on a [`connect`](Self::connect)
    /// / [`connect_socket`](Self::connect_socket). Ignored by
    /// [`accept`](Self::accept), whose stream the caller already owns.
    #[must_use]
    pub fn disable_nagle(mut self) -> Self {
        self.nodelay = true;
        self
    }

    /// Set the socket read timeout applied on a [`connect`](Self::connect) /
    /// [`connect_socket`](Self::connect_socket). A timeout elapsing with no complete
    /// frame surfaces from `recv` as `Ok(None)`, so the caller can service its own
    /// liveness timers and call `recv` again.
    #[must_use]
    pub fn read_timeout(mut self, d: Duration) -> Self {
        self.read_timeout = Some(d);
        self
    }

    /// Attach a per-venue [`SessionCustomizer`] — the hook that injects Logon auth
    /// (e.g. `Username(553)`/`Password(554)`/`RawData(96)`). Changes the resulting
    /// trio's customizer type to `C2`.
    pub fn customizer<C2: SessionCustomizer>(self, customizer: C2) -> FixConnectionBuilder<D, C2> {
        FixConnectionBuilder {
            reader_cap: self.reader_cap,
            writer_cap: self.writer_cap,
            customizer,
            nodelay: self.nodelay,
            read_timeout: self.read_timeout,
            _dict: PhantomData,
        }
    }

    /// Open **just the socket** — the reconnect primitive. Keep your existing
    /// [`FixParts`] (its sequence numbers and journal are the session's memory) and
    /// pair it with the fresh socket to resume; nothing about the session is rebuilt.
    /// Applies the configured `TCP_NODELAY` / read timeout.
    pub fn connect_socket<A: ToSocketAddrs>(self, addr: A) -> io::Result<TcpStream> {
        self.open_tcp(addr)
    }

    fn open_tcp<A: ToSocketAddrs>(&self, addr: A) -> io::Result<TcpStream> {
        let stream = TcpStream::connect(addr)?;
        if self.nodelay {
            stream.set_nodelay(true)?;
        }
        if let Some(t) = self.read_timeout {
            stream.set_read_timeout(Some(t))?;
        }
        Ok(stream)
    }
}

impl<D: FixDictionary, C: SessionCustomizer> FixConnectionBuilder<D, C> {
    /// Open a TCP connection to `addr` (applying the configured socket options) and
    /// return the raw [`FixParts`] trio paired with the socket. Run the ordinary
    /// three-object loop over them; sending the opening Logon is
    /// `parts.session.connect(&mut parts.writer, &mut sock, now)`.
    pub fn connect<A: ToSocketAddrs>(
        self,
        addr: A,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
    ) -> io::Result<(FixParts<D, C>, TcpStream)> {
        let stream = self.open_tcp(addr)?;
        Ok((self.build_parts(state, config, journal), stream))
    }

    /// Pair an already-accepted stream (server side) with a freshly built raw
    /// [`FixParts`] trio. Socket options are the caller's to set on `stream`
    /// beforehand.
    pub fn accept<S: Read + Write>(
        self,
        stream: S,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
    ) -> (FixParts<D, C>, S) {
        (self.build_parts(state, config, journal), stream)
    }

    fn build_parts(
        self,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
    ) -> FixParts<D, C> {
        FixSession::builder()
            .reader_capacity(self.reader_cap)
            .writer_capacity(self.writer_cap)
            .customizer(self.customizer)
            .build(state, config, journal)
    }
}

// =============================================================================
// FixConnection — A: owns everything (secondary one-object convenience)
// =============================================================================

/// A FIX session, its buffers, and the socket bundled into one object.
///
/// The secondary "I want one value to pass around" convenience over the raw
/// [`FixParts`] trio; mirrors `nexus-web`'s `ws::Client<S>`.
///
/// Prefer the raw trio (`FixConnectionBuilder::connect` → `(FixParts, S)`) for
/// zero-copy admin replies, a custom transport, or the acceptor-side
/// [`LogonDecision`](crate::LogonDecision). Reach for this when the single object is
/// worth the copy-out on [`recv`](Self::recv).
///
/// # Example
///
/// ```ignore
/// use nexus_fix_engine::{FixConnection, SessionState, SessionConfig, FixJournal, Message};
/// use std::time::Duration;
///
/// // One-step: open + build + bundle.
/// let mut conn = FixConnection::<_, Fix44>::open(
///     addr,
///     SessionState::new(Duration::from_secs(30)),
///     SessionConfig { sender, target },
///     FixJournal::open(dir, 0, 256)?,
/// )?;
///
/// conn.connect(now)?; // send the opening Logon
/// loop {
///     match conn.recv(now)? {
///         Some(Message::TestRequest { id }) => {
///             let id = id.as_bytes().to_vec(); // copy out before the reply (see `recv`)
///             let id = nexus_fix_codec::AsciiTextStr::try_from_bytes(&id).unwrap();
///             conn.heartbeat(now, Some(id))?;
///         }
///         Some(Message::LoggedOut { .. }) => break,
///         _ => {}
///     }
/// }
/// ```
pub struct FixConnection<S, D: FixDictionary, C = NoCustomizer> {
    session: FixSession<D>,
    reader: MessageReader<D>,
    writer: MessageWriter<D, C>,
    stream: S,
}

impl<D: FixDictionary> FixConnection<TcpStream, D, NoCustomizer> {
    /// Start a [`FixConnectionBuilder`] to size buffers, set socket options, attach
    /// a customizer, and `connect` / `accept`.
    #[must_use]
    pub fn builder() -> FixConnectionBuilder<D, NoCustomizer> {
        FixConnectionBuilder::new()
    }

    /// One-step construction of the owns-everything bundle: open a TCP connection to
    /// `addr` and wrap the trio + socket. Equivalent to
    /// `FixConnection::from_parts(FixConnection::builder().connect(addr, …)?)`.
    ///
    /// Does **not** send a Logon — that is [`connect`](Self::connect), the FIX-level
    /// handshake. (Named `open`, not `connect`, because `connect(&mut self, now)` is
    /// already the Logon send helper — the same verb name as the raw
    /// `session.connect`.) For buffer/socket-option control, use the builder path.
    pub fn open<A: ToSocketAddrs>(
        addr: A,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
    ) -> io::Result<Self> {
        let (parts, stream) = FixConnectionBuilder::new().connect(addr, state, config, journal)?;
        Ok(Self::from_parts(parts, stream))
    }
}

// -- Unbounded impl: bundle <-> raw parts, accessors --------------------------

impl<S, D: FixDictionary, C> FixConnection<S, D, C> {
    /// Bundle a [`FixParts`] trio and a socket. The other half of
    /// [`into_parts`](Self::into_parts); together they cross between the raw
    /// (primary) and owns-everything (secondary) surfaces, and drive the A-side
    /// reconnect ("same parts, new socket").
    pub fn from_parts(parts: FixParts<D, C>, stream: S) -> Self {
        let FixParts {
            session,
            reader,
            writer,
        } = parts;
        Self {
            session,
            reader,
            writer,
            stream,
        }
    }

    /// Unbundle into the raw [`FixParts`] trio and the socket — drop back to the
    /// primary surface for a zero-copy admin reply, an acceptor-side
    /// [`LogonDecision`](crate::LogonDecision), or a reconnect (keep the parts, open
    /// a new socket with [`FixConnectionBuilder::connect_socket`], rebundle).
    pub fn into_parts(self) -> (FixParts<D, C>, S) {
        (
            FixParts {
                session: self.session,
                reader: self.reader,
                writer: self.writer,
            },
            self.stream,
        )
    }

    /// The session brain.
    pub fn session(&self) -> &FixSession<D> {
        &self.session
    }

    /// Mutable access to the session brain.
    pub fn session_mut(&mut self) -> &mut FixSession<D> {
        &mut self.session
    }

    /// The underlying socket.
    pub fn stream(&self) -> &S {
        &self.stream
    }

    /// Mutable access to the underlying socket.
    pub fn stream_mut(&mut self) -> &mut S {
        &mut self.stream
    }

    /// The pure protocol [`SessionState`] (sequence numbers, phase, `HeartBtInt`).
    pub fn state(&self) -> &SessionState {
        self.session.state()
    }

    /// The negotiated heartbeat interval (`HeartBtInt(108)`) — the one value you
    /// need to build your own keepalive/liveness timers.
    pub fn heartbeat_interval(&self) -> Duration {
        self.session.heartbeat_interval()
    }

    /// Allocate the next outbound sequence number for a [`send_app`](Self::send_app).
    pub fn allocate_seq(&mut self) -> Result<u32, SessionError> {
        self.session.allocate_seq()
    }

    /// Simultaneous `&mut` access to the four owned fields — the escape hatch for a
    /// raw verb the bundle does not wrap, most commonly pumping a
    /// [`ResendCursor`](crate::ResendCursor):
    ///
    /// ```ignore
    /// if let Some(Message::ResendRequest { cursor }) = conn.recv(now)? {
    ///     let mut c = cursor; // owned handle — carries no borrow of `conn`
    ///     let (session, _reader, writer, stream) = conn.parts_mut();
    ///     while let Some(bytes) = c.next(session, writer, now)? {
    ///         stream.write_all(bytes)?;
    ///     }
    /// }
    /// ```
    pub fn parts_mut(
        &mut self,
    ) -> (
        &mut FixSession<D>,
        &mut MessageReader<D>,
        &mut MessageWriter<D, C>,
        &mut S,
    ) {
        (
            &mut self.session,
            &mut self.reader,
            &mut self.writer,
            &mut self.stream,
        )
    }
}

// -- Blocking I/O impl: recv + the delegating send helpers --------------------

impl<S: Read + Write, D: FixDictionary, C: SessionCustomizer> FixConnection<S, D, C> {
    /// Receive the next typed [`Message`], delegating to
    /// [`FixSession::recv`](crate::FixSession::recv) over the owned socket.
    ///
    /// # The copy-out consequence
    ///
    /// The bundle owns everything, so the returned `Message<'_>` borrows the *whole*
    /// `self`. Answering an admin message therefore needs its small reply field
    /// copied out **before** the reply call, because the reply (`&mut self`) cannot
    /// run while the borrowed payload is alive — identical to `ws::Client`'s
    /// ping→pong. For example, a [`Message::TestRequest`]'s `id` (`&AsciiTextStr`)
    /// must be copied (`id.as_bytes().to_vec()`) before [`heartbeat`](Self::heartbeat).
    /// Variants whose reply needs only `Copy` data ([`Message::GapDetected`]'s
    /// `begin`) or no reply ([`Message::Application`], [`Message::Heartbeat`]) are
    /// unaffected.
    ///
    /// This copy-out is exactly why the raw three-object surface (from
    /// [`FixConnectionBuilder::connect`], or [`into_parts`](Self::into_parts)) is the
    /// primary path: there the `Message` borrows only `reader`, so `session`/`writer`
    /// stay free and admin replies are zero-copy. The bundle trades that for owning
    /// the socket and one fewer value to thread.
    ///
    /// `now` (UTC unix-nanos) stamps `SendingTime(52)` on any mechanism emit the
    /// engine drives inside `recv`.
    pub fn recv(&mut self, now: i128) -> Result<Option<Message<'_, D>>, Error> {
        self.session
            .recv(&mut self.reader, &mut self.writer, &mut self.stream, now)
    }

    /// Encode a Logon and flush it (initiate the session). The FIX-level connect —
    /// distinct from the socket-level [`FixConnectionBuilder::connect`] /
    /// [`FixConnection::open`]. `now` stamps `SendingTime(52)` (UTC unix-nanos).
    pub fn connect(&mut self, now: i128) -> Result<(), Error> {
        self.session
            .connect(&mut self.writer, &mut self.stream, now)
    }

    /// Encode a Logon with `ResetSeqNumFlag=Y` and flush it. `now` stamps
    /// `SendingTime(52)`.
    pub fn connect_reset(&mut self, now: i128) -> Result<(), Error> {
        self.session
            .connect_reset(&mut self.writer, &mut self.stream, now)
    }

    /// Encode an in-session sequence reset handshake and flush it. `now` stamps
    /// `SendingTime(52)`.
    pub fn reset_sequence(&mut self, now: i128) -> Result<(), Error> {
        self.session
            .reset_sequence(&mut self.writer, &mut self.stream, now)
    }

    /// Encode a Logout and flush it — answer a [`Message::LogoutRequest`] or
    /// initiate a logout. `reason`, if `Some`, rides the wire as `Text(58)`. `now`
    /// stamps `SendingTime(52)`.
    pub fn logout(&mut self, now: i128, reason: Option<&AsciiTextStr>) -> Result<(), Error> {
        self.session
            .logout(&mut self.writer, &mut self.stream, now, reason)
    }

    /// Encode a Heartbeat (echoing `echo` if `Some`) and flush it — answer a
    /// [`Message::TestRequest`] with `Some(id)`, or send an unsolicited keepalive
    /// with `None`. `now` stamps `SendingTime(52)`.
    pub fn heartbeat(&mut self, now: i128, echo: Option<&AsciiTextStr>) -> Result<(), Error> {
        self.session
            .heartbeat(&mut self.writer, &mut self.stream, now, echo)
    }

    /// Encode a TestRequest and flush it. `now` stamps `SendingTime(52)`.
    pub fn test_request(&mut self, now: i128) -> Result<(), Error> {
        self.session
            .test_request(&mut self.writer, &mut self.stream, now)
    }

    /// Encode a ResendRequest covering `[begin, ∞)` and flush it — answer a
    /// [`Message::GapDetected`]. `now` stamps `SendingTime(52)`.
    pub fn resend_request(&mut self, now: i128, begin: u32) -> Result<(), Error> {
        self.session
            .resend_request(&mut self.writer, &mut self.stream, now, begin)
    }

    /// Encode a SequenceReset-Reset forcing the peer's expected seqnum to `new_seq`
    /// and flush it — answer a [`Message::ResendOutOfRange`] whose `EndSeqNo`
    /// exceeds what we sent. `now` stamps `SendingTime(52)`.
    pub fn sequence_reset(&mut self, now: i128, new_seq: u32) -> Result<(), Error> {
        self.session
            .sequence_reset(&mut self.writer, &mut self.stream, now, new_seq)
    }

    /// Encode a SequenceReset-GapFill standing in for `[from_seq, new_seq)` and
    /// flush it — answer a [`Message::ResendOutOfRange`] whose `BeginSeqNo` rotated
    /// off the replay window. `now` stamps `SendingTime(52)`.
    pub fn gap_fill(&mut self, now: i128, from_seq: u32, new_seq: u32) -> Result<(), Error> {
        self.session
            .gap_fill(&mut self.writer, &mut self.stream, now, from_seq, new_seq)
    }

    /// Journal, encode an application frame at sequence `seq`, and flush it. See
    /// [`FixSession::encode_send_app`](crate::FixSession::encode_send_app) for the
    /// frame-size constraint. Pair with [`allocate_seq`](Self::allocate_seq).
    pub fn send_app(&mut self, seq: u32, frame: &[u8]) -> Result<(), Error> {
        self.session
            .send_app(&mut self.writer, &mut self.stream, seq, frame)
    }
}
