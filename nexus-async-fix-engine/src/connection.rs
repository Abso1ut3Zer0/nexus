//! Batteries for the async FIX session — transport setup, in two layers.
//!
//! The framework proper is the raw three-object trio (the async [`FixSession`]
//! newtype + [`MessageReader`] + [`MessageWriter`], transport passed per call). This
//! module adds the *transport-setup* conveniences on top, in the same
//! primary/secondary split `nexus-web` uses for WebSocket (`WsStreamBuilder` → raw
//! parts, `WsStream` → owns-everything):
//!
//! ## B — [`FixConnectionBuilder`] → raw parts (the primary batteries)
//!
//! [`FixConnectionBuilder::connect`] / `connect_tls` /
//! [`accept`](FixConnectionBuilder::accept) open the transport and hand back the
//! [`FixParts`] trio **plus** the transport: `(FixParts<D, C>, S)`. You destructure
//! and run the ordinary three-object loop — `session.recv(&mut reader, &mut writer,
//! &mut conn, now).await` and the send helpers — which keeps admin replies
//! **zero-copy** (the `Message` borrows only `reader`, so `&mut session` / `&mut
//! writer` / `&mut conn` stay free to reply). This is why B is primary: no borrow of
//! the whole connection, no copy-out.
//!
//! Reconnect is "keep the [`FixParts`], grab a new transport":
//! [`FixConnectionBuilder::connect_socket`] (and `connect_socket_tls`) open *just*
//! the transport. Sequence numbers and the journal live in the retained `FixParts`.
//!
//! ## A — [`FixConnection`] owns everything (the secondary one-object convenience)
//!
//! [`FixConnection`] bundles the trio *and* the transport into one object with an
//! async `recv` and delegating async send helpers. Build it from B's parts with
//! [`from_parts`](FixConnection::from_parts), or in one step with
//! [`FixConnection::open`]. It is deliberately **not** a `Stream`/`Sink` (FIX `recv`
//! surfaces admin you must *answer*). The trade-off is a borrow one: because the
//! bundle owns everything, [`recv`](FixConnection::recv) returns a `Message<'_>`
//! borrowing the *whole* connection, so answering an admin message copies its small
//! reply field out first — see [`recv`](FixConnection::recv). Reach for A for the
//! ergonomic single object; reach for B (the default) for zero-copy replies, a
//! custom transport, or the acceptor-side
//! [`LogonDecision`](nexus_fix_engine::LogonDecision).

use std::io;
use std::marker::PhantomData;
use std::time::Duration;

use nexus_fix_codec::{AsciiTextStr, FixDictionary, NoCustomizer, SessionCustomizer};
use nexus_fix_engine::{FixJournal, SessionConfig, SessionError, SessionState};
use tokio::net::{TcpStream, ToSocketAddrs};

use crate::{
    Error, FixParts, FixSession, MaybeTls, Message, MessageReader, MessageWriter, WireStream,
};

// =============================================================================
// Transport openers (free async helpers, shared by the terminals)
// =============================================================================

async fn open_plain<A: ToSocketAddrs>(addr: A, nodelay: bool) -> io::Result<MaybeTls> {
    let tcp = TcpStream::connect(addr).await?;
    if nodelay {
        tcp.set_nodelay(true)?;
    }
    Ok(MaybeTls::Plain(tcp))
}

#[cfg(feature = "tls")]
async fn open_tls<A: ToSocketAddrs>(
    addr: A,
    domain: &str,
    tls: &nexus_net::tls::TlsConfig,
    nodelay: bool,
) -> io::Result<MaybeTls> {
    let tcp = TcpStream::connect(addr).await?;
    if nodelay {
        tcp.set_nodelay(true)?;
    }
    let connector = tokio_rustls::TlsConnector::from(tls.client_config().clone());
    let server_name = tokio_rustls::rustls::pki_types::ServerName::try_from(domain.to_owned())
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "invalid TLS server name"))?;
    let tls_stream = connector.connect(server_name, tcp).await?;
    Ok(MaybeTls::Tls(Box::new(tls_stream)))
}

// =============================================================================
// FixConnectionBuilder — B: setup terminals return raw parts
// =============================================================================

/// Builds the async FIX transport-setup batteries — buffer sizes, an optional
/// per-venue [`SessionCustomizer`], and `TCP_NODELAY`.
///
/// The setup terminals return the **raw [`FixParts`] trio plus the transport**
/// (`(FixParts<D, C>, S)`) — the primary path, run with the ordinary three-object
/// loop. Wrap the result in a [`FixConnection`] only if you want the one-object
/// convenience.
pub struct FixConnectionBuilder<D: FixDictionary, C = NoCustomizer> {
    reader_cap: usize,
    writer_cap: usize,
    customizer: C,
    nodelay: bool,
    _dict: PhantomData<fn() -> D>,
}

impl<D: FixDictionary> FixConnectionBuilder<D, NoCustomizer> {
    /// A new builder with 64 KiB buffers, no customizer, and Nagle enabled.
    #[must_use]
    pub fn new() -> Self {
        Self {
            reader_cap: 64 * 1024,
            writer_cap: 64 * 1024,
            customizer: NoCustomizer,
            nodelay: false,
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
    /// / `connect_tls` / [`connect_socket`](Self::connect_socket).
    #[must_use]
    pub fn disable_nagle(mut self) -> Self {
        self.nodelay = true;
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
            _dict: PhantomData,
        }
    }

    /// Open **just the plaintext transport** — the reconnect primitive. Keep your
    /// existing [`FixParts`] (its sequence numbers and journal are the session's
    /// memory) and pair it with the fresh transport to resume. See
    /// `connect_socket_tls` for the TLS variant.
    pub async fn connect_socket<A: ToSocketAddrs>(self, addr: A) -> io::Result<MaybeTls> {
        open_plain(addr, self.nodelay).await
    }

    /// Open **just the TLS transport** — the reconnect primitive over TLS. Drives the
    /// rustls client handshake with SNI `domain`.
    #[cfg(feature = "tls")]
    pub async fn connect_socket_tls<A: ToSocketAddrs>(
        self,
        addr: A,
        domain: &str,
        tls: &nexus_net::tls::TlsConfig,
    ) -> io::Result<MaybeTls> {
        open_tls(addr, domain, tls, self.nodelay).await
    }
}

impl<D: FixDictionary, C: SessionCustomizer> FixConnectionBuilder<D, C> {
    /// Open a plaintext TCP connection to `addr` (as [`MaybeTls::Plain`]) and return
    /// the raw [`FixParts`] trio paired with the transport. Run the ordinary
    /// three-object loop over them; sending the opening Logon is
    /// `parts.session.connect(&mut parts.writer, &mut conn, now).await`.
    pub async fn connect<A: ToSocketAddrs>(
        self,
        addr: A,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
    ) -> io::Result<(FixParts<D, C>, MaybeTls)> {
        let stream = open_plain(addr, self.nodelay).await?;
        Ok((self.build_parts(state, config, journal), stream))
    }

    /// Open a TLS connection to `addr` (rustls handshake, SNI `domain`, as
    /// [`MaybeTls::Tls`]) and return the raw [`FixParts`] trio paired with the
    /// transport.
    #[cfg(feature = "tls")]
    pub async fn connect_tls<A: ToSocketAddrs>(
        self,
        addr: A,
        domain: &str,
        tls: &nexus_net::tls::TlsConfig,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
    ) -> io::Result<(FixParts<D, C>, MaybeTls)> {
        let stream = open_tls(addr, domain, tls, self.nodelay).await?;
        Ok((self.build_parts(state, config, journal), stream))
    }

    /// Pair an already-connected transport (server side, or any preexisting
    /// [`WireStream`]) with a freshly built raw [`FixParts`] trio. Wrap a raw tokio
    /// stream in [`AsyncReadAdapter`](crate::AsyncReadAdapter) first.
    pub fn accept<S: WireStream + Unpin>(
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

/// An async FIX session, its buffers, and the transport bundled into one object.
///
/// The secondary "I want one value to pass around" convenience over the raw
/// [`FixParts`] trio — the async twin of `nexus_fix_engine::FixConnection`.
///
/// Prefer the raw trio (`FixConnectionBuilder::connect` → `(FixParts, S)`) for
/// zero-copy admin replies, a custom transport, or the acceptor-side
/// [`LogonDecision`](nexus_fix_engine::LogonDecision). Reach for this when the single
/// object is worth the copy-out on [`recv`](Self::recv). It is deliberately **not** a
/// `Stream`/`Sink` (FIX `recv` surfaces admin you must *answer*).
///
/// # Example
///
/// ```ignore
/// use nexus_async_fix_engine::FixConnection;
/// use nexus_fix_engine::{SessionState, SessionConfig, FixJournal, Message};
/// use std::time::Duration;
///
/// // One-step: open + build + bundle.
/// let mut conn = FixConnection::<_, Fix44>::open(
///     addr,
///     SessionState::new(Duration::from_secs(30)),
///     SessionConfig { sender, target },
///     FixJournal::open(dir, 0, 256)?,
/// )
/// .await?;
///
/// conn.connect(now).await?; // send the opening Logon
/// loop {
///     match conn.recv(now).await? {
///         Some(Message::TestRequest { id }) => {
///             let id = id.as_bytes().to_vec(); // copy out before the reply (see `recv`)
///             let id = nexus_fix_codec::AsciiTextStr::try_from_bytes(&id).unwrap();
///             conn.heartbeat(now, Some(id)).await?;
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

impl<D: FixDictionary> FixConnection<MaybeTls, D, NoCustomizer> {
    /// Start a [`FixConnectionBuilder`] to size buffers, set socket options, attach
    /// a customizer, and `connect` / `connect_tls` / `accept`.
    #[must_use]
    pub fn builder() -> FixConnectionBuilder<D, NoCustomizer> {
        FixConnectionBuilder::new()
    }

    /// One-step construction of the owns-everything bundle: open a plaintext TCP
    /// connection to `addr` and wrap the trio + transport. Equivalent to
    /// `FixConnection::from_parts(FixConnection::builder().connect(addr, …).await?)`.
    ///
    /// Does **not** send a Logon — that is [`connect`](Self::connect), the FIX-level
    /// handshake. (Named `open`, not `connect`, because `connect(&mut self, now)` is
    /// already the Logon send helper — the same verb name as the raw
    /// `session.connect`.) For TLS or buffer/socket-option control, use the builder
    /// path.
    pub async fn open<A: ToSocketAddrs>(
        addr: A,
        state: SessionState,
        config: SessionConfig,
        journal: FixJournal,
    ) -> io::Result<Self> {
        let (parts, stream) = FixConnectionBuilder::new()
            .connect(addr, state, config, journal)
            .await?;
        Ok(Self::from_parts(parts, stream))
    }
}

// -- Unbounded impl: bundle <-> raw parts, accessors --------------------------

impl<S, D: FixDictionary, C> FixConnection<S, D, C> {
    /// Bundle a [`FixParts`] trio and a transport. The other half of
    /// [`into_parts`](Self::into_parts); together they cross between the raw
    /// (primary) and owns-everything (secondary) surfaces, and drive the A-side
    /// reconnect ("same parts, new transport").
    ///
    /// Wrap a raw tokio `AsyncRead + AsyncWrite` stream in
    /// [`AsyncReadAdapter`](crate::AsyncReadAdapter) to satisfy the [`WireStream`]
    /// bound the I/O methods require.
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

    /// Unbundle into the raw [`FixParts`] trio and the transport — drop back to the
    /// primary surface for a zero-copy admin reply, an acceptor-side
    /// [`LogonDecision`](nexus_fix_engine::LogonDecision), or a reconnect (keep the
    /// parts, open a new transport with
    /// [`FixConnectionBuilder::connect_socket`], rebundle).
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

    /// The async session newtype.
    pub fn session(&self) -> &FixSession<D> {
        &self.session
    }

    /// Mutable access to the async session newtype.
    pub fn session_mut(&mut self) -> &mut FixSession<D> {
        &mut self.session
    }

    /// The underlying transport.
    pub fn stream(&self) -> &S {
        &self.stream
    }

    /// Mutable access to the underlying transport.
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
    /// [`ResendCursor`](nexus_fix_engine::ResendCursor):
    ///
    /// ```ignore
    /// if let Some(Message::ResendRequest { cursor }) = conn.recv(now).await? {
    ///     let mut c = cursor; // owned handle — carries no borrow of `conn`
    ///     let (session, _reader, writer, stream) = conn.parts_mut();
    ///     while let Some(bytes) = c.next(session, writer, now)? {
    ///         write_all_ws(stream, bytes).await?;
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

// -- Async I/O impl: recv + the delegating send helpers -----------------------

impl<S: WireStream + Unpin, D: FixDictionary, C: SessionCustomizer> FixConnection<S, D, C> {
    /// Receive the next typed [`Message`], delegating to
    /// [`FixSession::recv`](crate::FixSession::recv) over the owned transport.
    ///
    /// # The copy-out consequence
    ///
    /// The bundle owns everything, so the returned `Message<'_>` borrows the *whole*
    /// `self`. Answering an admin message therefore needs its small reply field
    /// copied out **before** the reply `.await`, because the reply (`&mut self`)
    /// cannot run while the borrowed payload is alive — identical to `ws::Client`'s
    /// ping→pong. For example, a [`Message::TestRequest`]'s `id` (`&AsciiTextStr`)
    /// must be copied before [`heartbeat`](Self::heartbeat). Variants whose reply
    /// needs only `Copy` data ([`Message::GapDetected`]'s `begin`) or no reply
    /// ([`Message::Application`], [`Message::Heartbeat`]) are unaffected.
    ///
    /// This copy-out is exactly why the raw three-object surface (from
    /// [`FixConnectionBuilder::connect`], or [`into_parts`](Self::into_parts)) is the
    /// primary path: there the `Message` borrows only `reader`, so `session`/`writer`
    /// stay free and admin replies are zero-copy. The bundle trades that for owning
    /// the transport and one fewer value to thread.
    ///
    /// `now` (UTC unix-nanos) stamps `SendingTime(52)` on any mechanism emit the
    /// engine drives inside `recv`.
    pub async fn recv(&mut self, now: i128) -> Result<Option<Message<'_, D>>, Error> {
        self.session
            .recv(&mut self.reader, &mut self.writer, &mut self.stream, now)
            .await
    }

    /// Encode a Logon and flush it (initiate the session). The FIX-level connect —
    /// distinct from the transport-level [`FixConnectionBuilder::connect`] /
    /// [`FixConnection::open`]. `now` stamps `SendingTime(52)` (UTC unix-nanos).
    pub async fn connect(&mut self, now: i128) -> Result<(), Error> {
        self.session
            .connect(&mut self.writer, &mut self.stream, now)
            .await
    }

    /// Encode a Logon with `ResetSeqNumFlag=Y` and flush it. `now` stamps
    /// `SendingTime(52)`.
    pub async fn connect_reset(&mut self, now: i128) -> Result<(), Error> {
        self.session
            .connect_reset(&mut self.writer, &mut self.stream, now)
            .await
    }

    /// Encode an in-session sequence reset handshake and flush it. `now` stamps
    /// `SendingTime(52)`.
    pub async fn reset_sequence(&mut self, now: i128) -> Result<(), Error> {
        self.session
            .reset_sequence(&mut self.writer, &mut self.stream, now)
            .await
    }

    /// Encode a Logout and flush it — answer a [`Message::LogoutRequest`] or
    /// initiate a logout. `reason`, if `Some`, rides the wire as `Text(58)`. `now`
    /// stamps `SendingTime(52)`.
    pub async fn logout(&mut self, now: i128, reason: Option<&AsciiTextStr>) -> Result<(), Error> {
        self.session
            .logout(&mut self.writer, &mut self.stream, now, reason)
            .await
    }

    /// Encode a Heartbeat (echoing `echo` if `Some`) and flush it — answer a
    /// [`Message::TestRequest`] with `Some(id)`, or send an unsolicited keepalive
    /// with `None`. `now` stamps `SendingTime(52)`.
    pub async fn heartbeat(&mut self, now: i128, echo: Option<&AsciiTextStr>) -> Result<(), Error> {
        self.session
            .heartbeat(&mut self.writer, &mut self.stream, now, echo)
            .await
    }

    /// Encode a TestRequest and flush it. `now` stamps `SendingTime(52)`.
    pub async fn test_request(&mut self, now: i128) -> Result<(), Error> {
        self.session
            .test_request(&mut self.writer, &mut self.stream, now)
            .await
    }

    /// Encode a ResendRequest covering `[begin, ∞)` and flush it — answer a
    /// [`Message::GapDetected`]. `now` stamps `SendingTime(52)`.
    pub async fn resend_request(&mut self, now: i128, begin: u32) -> Result<(), Error> {
        self.session
            .resend_request(&mut self.writer, &mut self.stream, now, begin)
            .await
    }

    /// Encode a SequenceReset-Reset forcing the peer's expected seqnum to `new_seq`
    /// and flush it — answer a [`Message::ResendOutOfRange`] whose `EndSeqNo`
    /// exceeds what we sent. `now` stamps `SendingTime(52)`.
    pub async fn sequence_reset(&mut self, now: i128, new_seq: u32) -> Result<(), Error> {
        self.session
            .sequence_reset(&mut self.writer, &mut self.stream, now, new_seq)
            .await
    }

    /// Encode a SequenceReset-GapFill standing in for `[from_seq, new_seq)` and
    /// flush it — answer a [`Message::ResendOutOfRange`] whose `BeginSeqNo` rotated
    /// off the replay window. `now` stamps `SendingTime(52)`.
    pub async fn gap_fill(&mut self, now: i128, from_seq: u32, new_seq: u32) -> Result<(), Error> {
        self.session
            .gap_fill(&mut self.writer, &mut self.stream, now, from_seq, new_seq)
            .await
    }

    /// Journal, encode an application frame at sequence `seq`, and flush it. See
    /// [`FixSession::encode_send_app`](nexus_fix_engine::FixSession::encode_send_app)
    /// for the frame-size constraint. Pair with [`allocate_seq`](Self::allocate_seq).
    pub async fn send_app(&mut self, seq: u32, frame: &[u8]) -> Result<(), Error> {
        self.session
            .send_app(&mut self.writer, &mut self.stream, seq, frame)
            .await
    }
}
