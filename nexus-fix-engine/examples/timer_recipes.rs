#![cfg(unix)]

//! # Timer recipes (blocking) — the three timers the framework leaves to you
//!
//! A FIX session holds **no timers**. The engine is a pure function of
//! `(bytes, now)`; *when* to act in wall-clock time is policy, and policy is
//! yours. The session exposes exactly one thing to build timers from:
//!
//! ```text
//! session.heartbeat_interval() -> Duration   // the negotiated HeartBtInt(108)
//! ```
//!
//! From it you own **three** timers. Get them right and the session keeps itself
//! alive and notices a dead peer; forget timer 2 and a half-open connection can
//! sit unnoticed forever. This file *is* the reference — read the [`Timers`]
//! type below.
//!
//! | # | Timer | Reset on | Fires when | You do |
//! |---|-------|----------|------------|--------|
//! | 1 | Heartbeat ticker | any **outbound** send | outbound idle ≥ HBI | `heartbeat(.., None)` |
//! | 2 | Peer liveness | any **inbound** message | see below (two phases) | probe, then disconnect |
//! | 3 | Handshake deadline | — | a transition stalls | give up (disconnect) |
//!
//! **Timer 2 is two-phase and the one users get wrong:**
//! *any* inbound message proves the peer is alive, so a single timer — reset on
//! every inbound — covers it, and you never match TestReqIDs.
//! - Phase 0 → 1: inbound silent for `HBI + grace` → send a `TestRequest` and arm
//!   a **shorter** deadline.
//! - Phase 1 → dead: still no inbound before that deadline → the peer is gone →
//!   disconnect (optionally `logout` first).
//! - Any inbound at any point → snap back to phase 0.
//!
//! ## Two clocks — keep them straight
//!
//! - **Timer decisions use a monotonic clock** ([`Instant`]). It never goes
//!   backwards and is immune to wall-clock steps (NTP, leap seconds).
//! - **`now: i128` is the wall clock** (UTC unix-nanos) and stamps only
//!   `SendingTime(52)` on the wire. Read it fresh per send. It has nothing to do
//!   with the timers.
//!
//! ## The wakeup seam (blocking)
//!
//! Set a socket **read timeout** to a fraction of the HBI. Then `recv` returns
//! `Ok(None)` whenever that timeout elapses with no complete frame — a periodic
//! wakeup on which you evaluate the three timers. `Ok(Some(msg))` is inbound
//! activity (reset timer 2); `Ok(None)` is *not* (a bare wakeup — leave timer 2
//! alone).
//!
//! Run with: `cargo run --example timer_recipes`

use std::io::ErrorKind;
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use nexus_fix_codec::{
    AsciiTextStr, FieldView, FixAdminMsg, FixDictionary, FixHeader, FixTimestamp, find_tag,
};
use nexus_fix_engine::{
    CompId, FixJournal, FixParts, FixSession, Message, MessageReader, MessageWriter, SessionConfig,
    SessionState, State, TransportError,
};

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

/// The wall clock, read fresh per send. Stamps `SendingTime(52)` only — the
/// session reads no clock of its own, which is what makes it replayable.
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
enum Liveness {
    /// Phase 0: the peer has spoken recently; nothing to do.
    Healthy,
    /// Phase 1: inbound went quiet, we sent a `TestRequest`, and now wait for
    /// *any* inbound before `deadline`. Miss it → the peer is dead.
    Probed { deadline: Instant },
}

/// What [`Timers::evaluate`] concluded this wakeup.
enum Verdict {
    /// Keep going.
    Live,
    /// Timer 2 phase 2: the peer answered nothing — disconnect.
    PeerDead,
    /// Timer 3: a handshake/logout transition stalled — give up.
    HandshakeStalled,
}

/// The three user-owned session timers, tracked against a monotonic
/// [`Instant`] clock. Re-[`evaluate`](Self::evaluate) them on **every** loop
/// wakeup — whether `recv` returned a message or just a bare timeout.
struct Timers {
    /// Negotiated `HeartBtInt`. Timer 1's period and timer 2's phase-0 threshold.
    hbi: Duration,
    /// Slack added before inbound silence is treated as suspicious (timer 2).
    grace: Duration,
    /// How long we wait for the peer to answer our `TestRequest` (timer 2 phase 1).
    probe_timeout: Duration,
    /// How long a handshake/logout transition may stall before we give up (timer 3).
    handshake_timeout: Duration,
    /// Last time *we* sent anything — resets timer 1.
    last_outbound: Instant,
    /// Last time *any* inbound message arrived — resets timer 2.
    last_inbound: Instant,
    /// Timer 2's phase.
    liveness: Liveness,
    /// Timer 3's deadline, armed only while a transition is pending.
    handshake_deadline: Option<Instant>,
}

impl Timers {
    /// Build the timers from the negotiated HBI. `now` seeds both idle clocks so
    /// nothing fires spuriously on the first wakeup.
    fn new(hbi: Duration, now: Instant) -> Self {
        Self {
            hbi,
            // A well-behaved peer heartbeats every HBI; wait half an interval more
            // before suspecting silence, so ordinary jitter never trips the probe.
            grace: hbi / 2,
            // The probe is urgent: give the peer only a fraction of an HBI to prove
            // it is alive before declaring it dead.
            probe_timeout: hbi / 2,
            // Handshakes are one round-trip; a few intervals is plenty of slack.
            handshake_timeout: hbi * 3,
            last_outbound: now,
            last_inbound: now,
            liveness: Liveness::Healthy,
            handshake_deadline: None,
        }
    }

    /// Record that we just sent something. Every send — a reply, an app message,
    /// a heartbeat tick, a probe — must call this so timer 1 measures *outbound*
    /// idle, not idle-since-the-last-heartbeat.
    fn record_send(&mut self, now: Instant) {
        self.last_outbound = now;
    }

    /// Record that an inbound message arrived. Resets timer 2 to phase 0 — *any*
    /// message proves the peer is alive, so this is the whole of "reset on any
    /// inbound." Never call it for a bare timeout wakeup.
    fn record_inbound(&mut self, now: Instant) {
        self.last_inbound = now;
        self.liveness = Liveness::Healthy;
    }

    /// Evaluate all three timers and act on the ones that fired. Sends flow
    /// through `session`/`writer`/`conn`; `now` is the monotonic reading for the
    /// decisions and `wire` the wall clock for any `SendingTime` stamped here.
    fn evaluate<S: std::io::Read + std::io::Write>(
        &mut self,
        session: &mut FixSession<Fix44>,
        writer: &mut MessageWriter<Fix44>,
        conn: &mut S,
        now: Instant,
        wire: i128,
    ) -> Result<Verdict, TransportError> {
        // ── Timer 3: handshake / logout deadline ─────────────────────────────
        // Armed only while a transition is pending; disarmed once the session is
        // up (`Active`), recovering (`Resending`), or down (`Disconnected`).
        match session.state().state() {
            State::LogonSent
            | State::LogoutPending
            | State::AwaitingResetDrain
            | State::AwaitingResetAck => {
                let deadline = *self
                    .handshake_deadline
                    .get_or_insert(now + self.handshake_timeout);
                if now >= deadline {
                    return Ok(Verdict::HandshakeStalled);
                }
            }
            _ => self.handshake_deadline = None,
        }

        // ── Timer 1: heartbeat ticker ────────────────────────────────────────
        // A full HBI of *outbound* silence → an unsolicited keepalive so the peer
        // sees we are alive. Only meaningful once the session is established.
        if session.state().state() == State::Active
            && now.duration_since(self.last_outbound) >= self.hbi
        {
            session.heartbeat(writer, conn, wire, None)?;
            self.record_send(now);
        }

        // ── Timer 2: peer liveness (two-phase) ───────────────────────────────
        match self.liveness {
            Liveness::Healthy => {
                // Phase 0 → 1: inbound has been silent past HBI + grace. Prod the
                // peer with a TestRequest and start the shorter countdown. (The
                // TestReqID is not tracked — *any* inbound resets us, so there is
                // nothing to match.)
                if now.duration_since(self.last_inbound) >= self.hbi + self.grace {
                    session.test_request(writer, conn, wire)?;
                    self.record_send(now); // a probe is outbound too
                    self.liveness = Liveness::Probed {
                        deadline: now + self.probe_timeout,
                    };
                }
            }
            Liveness::Probed { deadline } => {
                // Phase 1 → dead: the probe went unanswered. `record_inbound`
                // would have snapped us back to `Healthy` had anything arrived, so
                // reaching the deadline here means the peer is gone.
                if now >= deadline {
                    return Ok(Verdict::PeerDead);
                }
            }
        }

        Ok(Verdict::Live)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The recv step and the driver loop
// ─────────────────────────────────────────────────────────────────────────────

/// The owned classification of one `recv` + reply, so the loop can update the
/// timers *after* the borrowed `Message` is gone (contract §3.1: the `Message`
/// borrows `reader` only, freeing `session`/`writer`/`conn` for the reply).
enum Step {
    /// A bare timeout wakeup — no inbound. Do **not** reset timer 2.
    Idle,
    /// An inbound message arrived (and any required reply was sent). Reset timer 2.
    Inbound,
    /// The session ended cleanly (a negotiated logout).
    Ended,
}

/// Receive the next message (or a timeout) and drive its one required reply.
/// Each reply is *outbound*, so it calls `timers.record_send`.
fn step<S: std::io::Read + std::io::Write>(
    session: &mut FixSession<Fix44>,
    reader: &mut MessageReader<Fix44>,
    writer: &mut MessageWriter<Fix44>,
    conn: &mut S,
    timers: &mut Timers,
    now: Instant,
    wire: i128,
) -> Result<Step, TransportError> {
    match session.recv(reader, writer, conn, wire)? {
        // Timeout wakeup: nothing buffered. Not inbound activity.
        None => Ok(Step::Idle),
        // Terminal: the negotiated logout completed.
        Some(Message::LoggedOut { .. }) => Ok(Step::Ended),
        // The peer initiated logout: answer with our Logout, then we are done.
        Some(Message::LogoutRequest { .. }) => {
            session.logout(writer, conn, wire, None)?;
            timers.record_send(now);
            Ok(Step::Ended)
        }
        // A counterparty Logon: authenticate (inspect the decision) then accept.
        Some(Message::LogonRequest(d) | Message::LogonResetRequest(d)) => {
            d.accept(session, writer, conn, wire)?;
            timers.record_send(now);
            Ok(Step::Inbound)
        }
        // Peer liveness probe aimed at us: echo the TestReqID in a Heartbeat.
        Some(Message::TestRequest { id }) => {
            session.heartbeat(writer, conn, wire, Some(id))?;
            timers.record_send(now);
            Ok(Step::Inbound)
        }
        // Inbound gap: ask for the missing range.
        Some(Message::GapDetected { begin }) => {
            session.resend_request(writer, conn, wire, begin)?;
            timers.record_send(now);
            Ok(Step::Inbound)
        }
        // Heartbeat, Application, Reject, SequenceReset, … — no reply required,
        // but every one of them is inbound traffic that proves the peer is alive.
        Some(_) => Ok(Step::Inbound),
    }
}

/// Drive one session end-to-end with the three timers. `initiate` opens the
/// session with a Logon and, once it has been `Active` for `active_for`, starts
/// a clean logout; the passive side simply answers the peer's logout.
fn run_session(
    role: &'static str,
    mut conn: TcpStream,
    config: SessionConfig,
    dir: &Path,
    initiate: bool,
    active_for: Duration,
) {
    // The wakeup seam: a read timeout well under the HBI so `recv` returns
    // `Ok(None)` several times per interval, giving the timers a chance to fire.
    conn.set_read_timeout(Some(Duration::from_millis(200)))
        .unwrap();
    conn.set_nodelay(true).unwrap();

    // The session proposes a 1s HeartBtInt (whole seconds — HBI is encoded in
    // `HeartBtInt(108)`, so sub-second intervals round to zero). Keeps the demo
    // brisk while still measuring real elapsed time.
    let FixParts {
        mut session,
        mut reader,
        mut writer,
    } = FixSession::<Fix44>::builder().build(
        SessionState::new(Duration::from_secs(1)),
        config,
        FixJournal::open(dir, 0, 256).unwrap(),
    );

    if initiate {
        // Combined verb: encode the opening Logon and flush it in one call.
        session.connect(&mut writer, &mut conn, wire_now()).unwrap();
    }

    // Timers cannot be built with the *negotiated* HBI until Logon completes, so
    // seed them from our proposal and refresh once `Active` (both are 1s here).
    let mut timers = Timers::new(Duration::from_secs(1), Instant::now());
    let mut active_since: Option<Instant> = None;
    let mut logout_started = false;

    // A hard safety cap so the example can never hang if the peer misbehaves.
    let hard_cap = Instant::now() + Duration::from_secs(15);

    loop {
        if Instant::now() >= hard_cap {
            eprintln!("{role}: safety cap reached, forcing logout");
            let why = AsciiTextStr::try_from_str("demo time limit").ok();
            let _ = session.logout(&mut writer, &mut conn, wire_now(), why);
            break;
        }

        let now = Instant::now();
        match step(
            &mut session,
            &mut reader,
            &mut writer,
            &mut conn,
            &mut timers,
            now,
            wire_now(),
        ) {
            Ok(Step::Ended) => {
                println!("{role}: session ended cleanly");
                break;
            }
            // Inbound proves the peer is alive → reset timer 2 (to phase 0).
            Ok(Step::Inbound) => timers.record_inbound(Instant::now()),
            // Bare timeout wakeup → leave timer 2 untouched.
            Ok(Step::Idle) => {}
            Err(e) => {
                eprintln!("{role}: {e}");
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
                    .unwrap();
                timers.record_send(Instant::now());
                logout_started = true;
            }
        }

        // Evaluate the three timers on *every* wakeup — message or timeout.
        match timers.evaluate(
            &mut session,
            &mut writer,
            &mut conn,
            Instant::now(),
            wire_now(),
        ) {
            Ok(Verdict::Live) => {}
            Ok(Verdict::PeerDead) => {
                // Timer 2 phase 2: optionally tell the peer why, then drop the
                // socket (the caller owns the disconnect policy).
                eprintln!("{role}: peer unresponsive — disconnecting");
                let why = AsciiTextStr::try_from_str("no heartbeat").ok();
                let _ = session.logout(&mut writer, &mut conn, wire_now(), why);
                break;
            }
            Ok(Verdict::HandshakeStalled) => {
                eprintln!("{role}: handshake/logout stalled — giving up");
                break;
            }
            Err(e) => {
                eprintln!("{role}: emitting a timer message failed: {e}");
                break;
            }
        }
    }
}

fn main() {
    let listener = TcpListener::bind(("127.0.0.1", 0)).unwrap();
    let addr = listener.local_addr().unwrap();
    println!("listening on {addr}");

    let acceptor_dir = tmp_dir("timer_acceptor");
    let acceptor = std::thread::spawn(move || {
        let (conn, _) = listener.accept().unwrap();
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
        );
    });

    let initiator_dir = tmp_dir("timer_initiator");
    let conn = connect_with_retry(addr);
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
    );

    acceptor.join().unwrap();
}

fn connect_with_retry(addr: SocketAddr) -> TcpStream {
    for _ in 0..50 {
        match TcpStream::connect(addr) {
            Ok(s) => return s,
            Err(e) if e.kind() == ErrorKind::ConnectionRefused => {
                std::thread::sleep(Duration::from_millis(20));
            }
            Err(e) => panic!("connect failed: {e}"),
        }
    }
    panic!("could not connect to {addr}");
}

fn tmp_dir(name: &str) -> PathBuf {
    let mut p = std::env::temp_dir();
    p.push(format!("nexus_timer_recipes_{name}"));
    std::fs::create_dir_all(&p).unwrap();
    p
}
