#![cfg(unix)]

//! # Timer recipes (tokio) — the three timers the framework leaves to you
//!
//! The async twin of `nexus-fix-engine/examples/timer_recipes.rs`. Read that
//! file first for the full theory of the three timers; this one shows the tokio
//! shape. The session still holds **no timers** — it exposes only
//! `heartbeat_interval()` — so you own all three. (This recipe drives the raw
//! three-object trio — what `FixConnectionBuilder::connect` hands back as
//! `(FixParts, transport)`; the timer logic is identical over the owns-everything
//! `FixConnection` too — `heartbeat_interval()`, the send helpers, and `recv` are
//! all there.)
//!
//! You own all three:
//!
//! | # | Timer | Reset on | Fires when | You do |
//! |---|-------|----------|------------|--------|
//! | 1 | Heartbeat ticker | any **outbound** send | outbound idle ≥ HBI | `heartbeat(.., None)` |
//! | 2 | Peer liveness | any **inbound** message | two phases (below) | probe, then disconnect |
//! | 3 | Handshake deadline | — | a transition stalls | give up (disconnect) |
//!
//! **Timer 2 is two-phase** and the one users get wrong. *Any* inbound message
//! proves life, so one timer — reset on every inbound — covers it:
//! - Phase 0 → 1: inbound silent for `HBI + grace` → `test_request` + a shorter
//!   deadline.
//! - Phase 1 → dead: still silent at that deadline → the peer is gone.
//! - Any inbound → back to phase 0.
//!
//! ## The tokio shape: `select!` + `sleep_until`, replies **after** the select
//!
//! Each loop iteration computes the three deadlines from the timer state, then
//! [`tokio::select!`]s the socket `recv` against a `sleep_until` per timer. The
//! branch that wins yields an **owned** verdict, and the actual protocol sends
//! happen *after* the `select!` returns.
//!
//! Why after, not inside the `recv` arm? A **borrow** reason, not a cancel-safety
//! one: `recv` returns a `Message<'r>` borrowing `reader`, so you must let that
//! borrow end before taking `&mut writer`/`&mut session` for the reply. Extracting
//! an owned verdict in the arm (copy the payload out, or carry the `LogonDecision`
//! by value) drops the borrow, and the send after `select!` then has the buffers
//! free. It also keeps one uniform send path.
//!
//! **On cancel-safety:** when a timer branch wins, `select!` drops the `recv`
//! future mid-`await`, and that is safe on both sides. Inbound bytes are committed
//! to `reader` the instant `poll_read` returns `Ready` (nothing is committed on
//! `Pending`), so a dropped `recv` loses no data and the next `recv` resumes.
//! `recv` *also* flushes the engine's own mechanism frames (the reset-handshake
//! `LogonReset`, protocol-error `Logout`s) via an internal drain — but a mid-flush
//! drop is recoverable, not corrupting: the outbound buffer is append-only (it
//! retains the un-sent tail and resets only once fully drained), so the tail
//! survives in the caller-owned `writer` and the next drain completes the frame in
//! TCP order. A truncated frame is never finalized on the wire. So racing `recv`
//! in `select!` is sound as written.
//!
//! ## Two clocks
//! - Timer **decisions** use tokio's monotonic [`Instant`].
//! - **`now: i128`** is the wall clock (UTC unix-nanos); it stamps only
//!   `SendingTime(52)`. Read fresh per send.
//!
//! Run with: `cargo run --example async_timer_recipes`

use std::io::ErrorKind;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use nexus_async_fix_engine::{AsyncReadAdapter, FixParts, FixSession};
use nexus_fix_codec::{
    AsciiTextStr, FieldView, FixAdminMsg, FixDictionary, FixHeader, FixTimestamp, find_tag,
};
use nexus_fix_engine::{
    CompId, FixJournal, LogonDecision, Message, MessageWriter, SessionConfig, SessionState, State,
    TransportError,
};
use tokio::net::{TcpListener, TcpStream};
use tokio::time::{Duration, Instant, sleep_until};

// ── minimal FIX 4.4 dictionary (same shape as the other examples) ────────────

struct Fix44;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Fix44MsgType {}

struct Decoder<'buf> {
    _buf: &'buf [u8],
}

impl<'buf> FixAdminMsg<'buf> for Decoder<'buf> {
    fn decode(buf: &'buf [u8]) -> Result<Self, nexus_fix_codec::DecodeError> {
        Ok(Self { _buf: buf })
    }
}

impl FixDictionary for Fix44 {
    type MsgType = Fix44MsgType;
    type Header<'buf> = Fix44Header<'buf>;
    type Logon<'buf> = Decoder<'buf>;
    type Logout<'buf> = Decoder<'buf>;
    type Heartbeat<'buf> = Decoder<'buf>;
    type TestRequest<'buf> = Decoder<'buf>;
    type ResendRequest<'buf> = Decoder<'buf>;
    type SequenceReset<'buf> = Decoder<'buf>;
    type Reject<'buf> = Decoder<'buf>;
    const BEGIN_STRING: &'static [u8] = b"FIX.4.4";
    fn is_admin(_: Fix44MsgType) -> bool {
        false
    }
}

struct Fix44Header<'buf> {
    buf: &'buf [u8],
}

impl<'buf> FixHeader<'buf> for Fix44Header<'buf> {
    fn decode(buf: &'buf [u8]) -> Self {
        Self { buf }
    }
    fn raw_msg_type(&self) -> Option<FieldView<'buf, &'buf [u8]>> {
        find_tag(self.buf, 0, 35).and_then(|s| FieldView::new(s, self.buf))
    }
    fn msg_seq_num(&self) -> Option<FieldView<'buf, u64>> {
        find_tag(self.buf, 0, 34).and_then(|s| FieldView::new(s, self.buf))
    }
    fn sender_comp_id(&self) -> Option<FieldView<'buf, &'buf AsciiTextStr>> {
        find_tag(self.buf, 0, 49).and_then(|s| FieldView::new(s, self.buf))
    }
    fn target_comp_id(&self) -> Option<FieldView<'buf, &'buf AsciiTextStr>> {
        find_tag(self.buf, 0, 56).and_then(|s| FieldView::new(s, self.buf))
    }
    fn poss_dup_flag(&self) -> Option<FieldView<'buf, bool>> {
        find_tag(self.buf, 0, 43).and_then(|s| FieldView::new(s, self.buf))
    }
    fn sending_time(&self) -> Option<FieldView<'buf, FixTimestamp>> {
        None
    }
}

/// The wall clock, read fresh per send. Stamps `SendingTime(52)` only.
fn wire_now() -> i128 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock is after the unix epoch")
        .as_nanos() as i128
}

// ─────────────────────────────────────────────────────────────────────────────
// The three timers
// ─────────────────────────────────────────────────────────────────────────────

/// Peer-liveness phase (timer 2). *Any* inbound message returns it to `Healthy`.
#[derive(Clone, Copy)]
enum Liveness {
    /// Phase 0: the peer has spoken recently.
    Healthy,
    /// Phase 1: we sent a `TestRequest` and wait for *any* inbound before
    /// `deadline`. Miss it → the peer is dead.
    Probed { deadline: Instant },
}

/// The three user-owned timers over tokio's monotonic clock. The loop reads the
/// three deadlines each iteration and `sleep_until`s them in the `select!`.
struct Timers {
    hbi: Duration,
    grace: Duration,
    probe_timeout: Duration,
    handshake_timeout: Duration,
    /// Last time *we* sent anything — timer 1's zero.
    last_outbound: Instant,
    /// Last time *any* inbound arrived — timer 2's zero.
    last_inbound: Instant,
    liveness: Liveness,
    /// Timer 3's deadline, armed lazily on entry to a pending transition.
    handshake_armed: Option<Instant>,
}

impl Timers {
    fn new(hbi: Duration, now: Instant) -> Self {
        Self {
            hbi,
            grace: hbi / 2,
            probe_timeout: hbi / 2,
            handshake_timeout: hbi * 3,
            last_outbound: now,
            last_inbound: now,
            liveness: Liveness::Healthy,
            handshake_armed: None,
        }
    }

    /// Timer 1's deadline: a full HBI after our last outbound send. Sending
    /// anything pushes it out — that is "reset on any outbound." (A plain
    /// `tokio::time::interval(hbi)` is the simpler approximation, but it ignores
    /// outbound sends and would emit a redundant heartbeat right after one.)
    fn heartbeat_deadline(&self) -> Instant {
        self.last_outbound + self.hbi
    }

    /// Timer 2's deadline: in phase 0 the inbound-silence threshold; in phase 1
    /// the probe's shorter countdown.
    fn liveness_deadline(&self) -> Instant {
        match self.liveness {
            Liveness::Healthy => self.last_inbound + self.hbi + self.grace,
            Liveness::Probed { deadline } => deadline,
        }
    }

    /// Timer 3's deadline: `Some` only while a handshake/logout transition is
    /// pending, armed on first entry and cleared once the session is up,
    /// recovering, or down.
    fn handshake_deadline(&mut self, state: State, now: Instant) -> Option<Instant> {
        match state {
            State::LogonSent
            | State::LogoutPending
            | State::AwaitingResetDrain
            | State::AwaitingResetAck => Some(
                *self
                    .handshake_armed
                    .get_or_insert(now + self.handshake_timeout),
            ),
            _ => {
                self.handshake_armed = None;
                None
            }
        }
    }

    /// Any send resets timer 1.
    fn record_send(&mut self, now: Instant) {
        self.last_outbound = now;
    }

    /// Any inbound resets timer 2 to phase 0.
    fn record_inbound(&mut self, now: Instant) {
        self.last_inbound = now;
        self.liveness = Liveness::Healthy;
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The select loop
// ─────────────────────────────────────────────────────────────────────────────

/// The reply a received message obliges — carried **by value or borrow** out of
/// the `select!` arm so the actual send runs *after* the `select!`, where it
/// cannot be cancelled by a timer (see the module docs).
enum Reply<'r> {
    /// Inbound that needs no reply (Heartbeat, Application, Reject, …).
    None,
    /// The peer initiated logout; answer with ours, then end.
    Logout,
    /// A counterparty Logon; accept it (authenticate via the decision first).
    Accept(LogonDecision<'r, Fix44>),
    /// A `TestRequest`; echo its `TestReqID` in a Heartbeat.
    Heartbeat(&'r AsciiTextStr),
    /// A detected inbound gap; ask for the missing range.
    Resend(u32),
}

/// The owned outcome of one `select!` iteration.
enum Wake<'r> {
    /// `recv` surfaced an inbound message (with its reply) — reset timer 2.
    Inbound(Reply<'r>),
    /// `recv` processed a frame but surfaced nothing (a suppressed inbound) —
    /// still inbound activity, so reset timer 2.
    Suppressed,
    /// The session ended cleanly.
    Ended,
    /// `recv` failed.
    Failed(TransportError),
    /// Timer 1 fired.
    Heartbeat,
    /// Timer 2 fired (phase depends on `Timers::liveness`).
    Liveness,
    /// Timer 3 fired.
    Handshake,
}

async fn run_session(
    role: &'static str,
    tcp: TcpStream,
    config: SessionConfig,
    dir: &Path,
    initiate: bool,
    active_for: Duration,
) {
    tcp.set_nodelay(true).unwrap();
    let mut conn = AsyncReadAdapter::new(tcp);

    // 1s HeartBtInt — whole seconds, since `HeartBtInt(108)` is encoded in seconds.
    let hbi = Duration::from_secs(1);
    let FixParts {
        mut session,
        mut reader,
        mut writer,
    } = FixSession::builder(Fix44).build(
        SessionState::new(hbi),
        config,
        FixJournal::open(dir, 0, 256).unwrap(),
    );

    if initiate {
        session
            .connect(&mut writer, &mut conn, wire_now())
            .await
            .unwrap();
    }

    let mut timers = Timers::new(hbi, Instant::now());
    let mut active_since: Option<Instant> = None;
    let mut logout_started = false;
    let hard_cap = Instant::now() + Duration::from_secs(15);

    loop {
        // Compute the three deadlines up front (borrows only the timer state), so
        // the `select!` futures own their `Instant`s and borrow nothing that a
        // reply might need.
        let hb_at = timers.heartbeat_deadline();
        let live_at = timers.liveness_deadline();
        let hs_at = timers.handshake_deadline(session.state().state(), Instant::now());
        // A conditional branch cannot be omitted, so point the disarmed handshake
        // sleep at the far-off safety cap and gate it with an `if` guard.
        let hs_sleep_at = hs_at.unwrap_or(hard_cap);

        let wake: Wake = tokio::select! {
            biased;
            // Only `recv` awaits I/O here. Its arm body runs after `recv` resolved,
            // so extracting the borrowed payload is safe; the *send* waits until
            // after the `select!`.
            r = session.recv(&mut reader, &mut writer, &mut conn, wire_now()) => {
                match r {
                    Ok(None) => Wake::Suppressed,
                    Ok(Some(Message::LoggedOut { .. })) => Wake::Ended,
                    Ok(Some(Message::LogoutRequest { .. })) => Wake::Inbound(Reply::Logout),
                    Ok(Some(Message::LogonRequest(d) | Message::LogonResetRequest(d))) => {
                        Wake::Inbound(Reply::Accept(d))
                    }
                    Ok(Some(Message::TestRequest { id })) => Wake::Inbound(Reply::Heartbeat(id)),
                    Ok(Some(Message::GapDetected { begin })) => Wake::Inbound(Reply::Resend(begin)),
                    Ok(Some(_)) => Wake::Inbound(Reply::None),
                    Err(e) => Wake::Failed(e),
                }
            }
            () = sleep_until(hb_at) => Wake::Heartbeat,
            () = sleep_until(live_at) => Wake::Liveness,
            () = sleep_until(hs_sleep_at), if hs_at.is_some() => Wake::Handshake,
        };

        // The `select!` has returned; every branch future is dropped and all
        // borrows are free. Now perform any send — uninterruptibly.
        let now = Instant::now();
        match wake {
            Wake::Ended => {
                println!("{role}: session ended cleanly");
                break;
            }
            Wake::Failed(e) => {
                eprintln!("{role}: {e}");
                break;
            }
            Wake::Suppressed => timers.record_inbound(now),
            Wake::Inbound(reply) => {
                timers.record_inbound(now);
                let ended = drive_reply(
                    role,
                    &mut session,
                    &mut writer,
                    &mut conn,
                    reply,
                    &mut timers,
                )
                .await;
                if ended {
                    println!("{role}: session ended cleanly");
                    break;
                }
            }
            Wake::Heartbeat => {
                // Timer 1: unsolicited keepalive once Active. Record the send even
                // when not yet up so the deadline advances instead of spinning.
                if session.state().state() == State::Active
                    && let Err(e) = session
                        .heartbeat(&mut writer, &mut conn, wire_now(), None)
                        .await
                {
                    eprintln!("{role}: heartbeat failed: {e}");
                    break;
                }
                timers.record_send(Instant::now());
            }
            Wake::Liveness => match timers.liveness {
                // Phase 0 → 1: prod the peer and start the shorter countdown.
                Liveness::Healthy => {
                    if let Err(e) = session
                        .test_request(&mut writer, &mut conn, wire_now())
                        .await
                    {
                        eprintln!("{role}: test_request failed: {e}");
                        break;
                    }
                    let sent = Instant::now();
                    timers.record_send(sent);
                    timers.liveness = Liveness::Probed {
                        deadline: sent + timers.probe_timeout,
                    };
                }
                // Phase 1 → dead: the probe went unanswered.
                Liveness::Probed { .. } => {
                    eprintln!("{role}: peer unresponsive — disconnecting");
                    let why = AsciiTextStr::try_from_str("no heartbeat").ok();
                    let _ = session
                        .logout(&mut writer, &mut conn, wire_now(), why)
                        .await;
                    break;
                }
            },
            Wake::Handshake => {
                eprintln!("{role}: handshake/logout stalled — giving up");
                break;
            }
        }

        // The initiator drives a clean shutdown after a spell of being Active.
        if session.state().state() == State::Active {
            let since = *active_since.get_or_insert_with(Instant::now);
            if initiate && !logout_started && since.elapsed() >= active_for {
                println!("{role}: initiating clean logout");
                let bye = AsciiTextStr::try_from_str("session complete").ok();
                session
                    .logout(&mut writer, &mut conn, wire_now(), bye)
                    .await
                    .unwrap();
                timers.record_send(Instant::now());
                logout_started = true;
            }
        }

        if Instant::now() >= hard_cap {
            eprintln!("{role}: safety cap reached");
            break;
        }
    }
}

/// Send the reply a received message obliged, after the `select!` (uncancellable).
/// Returns `true` when the session has ended (we answered a peer logout).
async fn drive_reply(
    role: &'static str,
    session: &mut FixSession<Fix44>,
    writer: &mut MessageWriter<Fix44>,
    conn: &mut AsyncReadAdapter<TcpStream>,
    reply: Reply<'_>,
    timers: &mut Timers,
) -> bool {
    let result = match reply {
        Reply::None => {
            return false; // inbound, no reply, no outbound to record
        }
        Reply::Logout => {
            let r = session.logout(writer, conn, wire_now(), None).await;
            timers.record_send(Instant::now());
            return match r {
                Ok(()) => true,
                Err(e) => {
                    eprintln!("{role}: logout reply failed: {e}");
                    true
                }
            };
        }
        Reply::Accept(d) => session.accept_logon(d, writer, conn, wire_now()).await,
        Reply::Heartbeat(id) => session.heartbeat(writer, conn, wire_now(), Some(id)).await,
        Reply::Resend(begin) => {
            session
                .resend_request(writer, conn, wire_now(), begin)
                .await
        }
    };
    match result {
        Ok(()) => timers.record_send(Instant::now()),
        Err(e) => eprintln!("{role}: reply failed: {e}"),
    }
    false
}

#[tokio::main(flavor = "current_thread")]
async fn main() {
    let listener = TcpListener::bind(("127.0.0.1", 0)).await.unwrap();
    let addr = listener.local_addr().unwrap();
    println!("listening on {addr}");

    let acceptor_dir = tmp_dir("timer_acceptor");
    let initiator_dir = tmp_dir("timer_initiator");

    // Both sessions run concurrently on the one current-thread runtime — no
    // spawning, so neither future needs to be `Send`. `join!` interleaves them,
    // and they drive each other over TCP loopback.
    let acceptor = async {
        let (conn, _) = listener.accept().await.unwrap();
        run_session(
            "acceptor",
            conn,
            SessionConfig {
                sender: CompId::new(b"ACCEPTOR").unwrap(),
                target: CompId::new(b"INITIATOR").unwrap(),
            },
            &acceptor_dir,
            false,
            Duration::ZERO,
        )
        .await;
    };
    let initiator = async {
        let conn = connect_with_retry(addr).await;
        run_session(
            "initiator",
            conn,
            SessionConfig {
                sender: CompId::new(b"INITIATOR").unwrap(),
                target: CompId::new(b"ACCEPTOR").unwrap(),
            },
            &initiator_dir,
            true,
            // Stay Active long enough to watch at least one heartbeat tick fire.
            Duration::from_millis(1500),
        )
        .await;
    };

    tokio::join!(acceptor, initiator);
}

async fn connect_with_retry(addr: std::net::SocketAddr) -> TcpStream {
    for _ in 0..50 {
        match TcpStream::connect(addr).await {
            Ok(s) => return s,
            Err(e) if e.kind() == ErrorKind::ConnectionRefused => {
                tokio::time::sleep(Duration::from_millis(20)).await;
            }
            Err(e) => panic!("connect failed: {e}"),
        }
    }
    panic!("could not connect to {addr}");
}

fn tmp_dir(name: &str) -> PathBuf {
    let mut p = std::env::temp_dir();
    p.push(format!("nexus_async_timer_recipes_{name}"));
    std::fs::create_dir_all(&p).unwrap();
    p
}
