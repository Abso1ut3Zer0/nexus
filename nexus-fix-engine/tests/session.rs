use std::time::{Duration, Instant};

use nexus_fix_codec::{
    AdminEncode, AdminHeader, AdminMsgOut, AsciiTextStr, DecodeError, FieldView, FixAdminMsg,
    FixDictionary, FixHeader, FixTimestamp, FrameFormatter, NoCustomizer, find_tag, parse_fix_uint,
};
use nexus_fix_engine::{Control, DisconnectReason, Emit, SessionState, State};

const HB: Duration = Duration::from_secs(30);

fn new_session() -> SessionState {
    SessionState::new(HB)
}

// ── minimal dictionary so the recording emitter can encode admin frames ─────────

struct MockDict;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum MockMsgType {}

struct AdminDecoder<'buf> {
    _buf: &'buf [u8],
}

impl<'buf> FixAdminMsg<'buf> for AdminDecoder<'buf> {
    fn decode(buf: &'buf [u8]) -> Result<Self, DecodeError> {
        Ok(Self { _buf: buf })
    }
}

struct MockHeader<'buf> {
    buf: &'buf [u8],
}

impl<'buf> FixHeader<'buf> for MockHeader<'buf> {
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

impl FixDictionary for MockDict {
    type MsgType = MockMsgType;
    type Header<'buf> = MockHeader<'buf>;
    type Logon<'buf> = AdminDecoder<'buf>;
    type Logout<'buf> = AdminDecoder<'buf>;
    type Heartbeat<'buf> = AdminDecoder<'buf>;
    type TestRequest<'buf> = AdminDecoder<'buf>;
    type ResendRequest<'buf> = AdminDecoder<'buf>;
    type SequenceReset<'buf> = AdminDecoder<'buf>;
    type Reject<'buf> = AdminDecoder<'buf>;
    const BEGIN_STRING: &'static [u8] = b"FIX.4.4";
    fn is_admin(_: MockMsgType) -> bool {
        false
    }
}

// ── recording emitter: captures each emitted admin as its encoded frame ─────────

/// An [`Emit`] that encodes each emitted message through the real
/// `AdminEncode` path (into a `MockDict` frame) and records the frame bytes.
/// Assertions decode the captured frame — `MsgType(35)` and body tags — so they
/// pin the actual wire output, not a captured enum.
struct RecordingEmitter {
    frames: Vec<Vec<u8>>,
}

impl RecordingEmitter {
    fn new() -> Self {
        Self { frames: Vec::new() }
    }
    fn len(&self) -> usize {
        self.frames.len()
    }
    fn clear(&mut self) {
        self.frames.clear();
    }
    /// `MsgType(35)` of the `i`-th recorded frame.
    fn mt(&self, i: usize) -> &[u8] {
        find_tag(&self.frames[i], 0, 35)
            .map(|s| s.slice(&self.frames[i]))
            .expect("frame carries MsgType(35)")
    }
    /// A body tag parsed as `u32`.
    fn num(&self, i: usize, tag: u32) -> Option<u32> {
        find_tag(&self.frames[i], 0, tag)
            .and_then(|s| parse_fix_uint(s.slice(&self.frames[i])).ok())
    }
    /// A body tag's raw bytes.
    fn val(&self, i: usize, tag: u32) -> Option<&[u8]> {
        find_tag(&self.frames[i], 0, tag).map(|s| s.slice(&self.frames[i]))
    }
    /// Whether a body tag is present on the `i`-th frame.
    fn has(&self, i: usize, tag: u32) -> bool {
        find_tag(&self.frames[i], 0, tag).is_some()
    }
    /// Whether any recorded frame carries the given `MsgType(35)`.
    fn any_mt(&self, mt: &[u8]) -> bool {
        (0..self.frames.len()).any(|i| self.mt(i) == mt)
    }
}

impl Emit for RecordingEmitter {
    type Error = std::convert::Infallible;

    fn emit<M: AdminEncode>(&mut self, msg: M) -> Result<(), std::convert::Infallible> {
        let mut buf = [0u8; 512];
        let hdr = AdminHeader {
            seq: msg.seq(),
            sender: b"SENDER",
            target: b"TARGET",
            ts: b"20260101-00:00:00.000",
        };
        let mut fmt = FrameFormatter::new(&mut buf, MockDict::BEGIN_STRING, M::MSG_TYPE);
        msg.encode::<MockDict>(&mut fmt, &hdr);
        msg.customize(
            &mut NoCustomizer,
            &mut AdminMsgOut::new(&mut fmt, &hdr, M::MSG_TYPE, M::owned::<MockDict>()),
        );
        let (start, len) = fmt.finish().expect("admin frame fits the scratch buffer");
        self.frames.push(buf[start..start + len].to_vec());
        Ok(())
    }
}

fn establish(s: &mut SessionState, now: Instant) {
    let mut recorder = RecordingEmitter::new();
    s.connect(now, &mut recorder).unwrap();
    s.on_logon(1, 30, false, false, now, &mut recorder).unwrap();
    assert_eq!(s.state(), State::Active);
}

#[test]
fn initiator_handshake() {
    let mut s = new_session();
    let now = Instant::now();

    let mut recorder = RecordingEmitter::new();
    s.connect(now, &mut recorder).unwrap();
    assert_eq!(s.state(), State::LogonSent);
    assert_eq!(recorder.len(), 1);
    // Logon (35=A, no 141) at seqnum 1 with HeartBtInt(108)=30.
    assert_eq!(recorder.mt(0), b"A");
    assert!(!recorder.has(0, 141), "plain Logon must not carry 141");
    assert_eq!(recorder.num(0, 34), Some(1));
    assert_eq!(recorder.num(0, 108), Some(30));

    recorder.clear();
    // Initiator receiving the peer's Logon ack: send_reply = false → acknowledged.
    let ctrl = s.on_logon(1, 30, false, false, now, &mut recorder).unwrap();
    assert_eq!(s.state(), State::Active);
    assert_eq!(ctrl, Control::Logon { acknowledged: true });
    assert_eq!(recorder.len(), 0);
    assert_eq!(s.next_inbound_seq(), 2);
    assert_eq!(s.next_outbound_seq(), 2);
}

#[test]
fn acceptor_handshake() {
    let mut s = new_session();
    let now = Instant::now();

    let mut recorder = RecordingEmitter::new();
    // Acceptor: send_reply = true → this Logon is answered, not an ack.
    let ctrl = s.on_logon(1, 15, false, true, now, &mut recorder).unwrap();
    assert_eq!(s.state(), State::Active);
    assert_eq!(
        ctrl,
        Control::Logon {
            acknowledged: false
        }
    );
    assert_eq!(recorder.len(), 1);
    // Reply Logon (35=A, no 141) at seqnum 1, echoing HeartBtInt(108)=15.
    assert_eq!(recorder.mt(0), b"A");
    assert!(!recorder.has(0, 141));
    assert_eq!(recorder.num(0, 34), Some(1));
    assert_eq!(recorder.num(0, 108), Some(15));
}

#[test]
fn logon_reset_seq_num_flag() {
    let mut s = new_session();
    let now = Instant::now();

    let mut recorder = RecordingEmitter::new();
    s.on_logon(1, 30, true, true, now, &mut recorder).unwrap();
    assert_eq!(s.state(), State::Active);
    assert_eq!(recorder.len(), 1);
    // LogonReset (35=A carrying 141=Y) at seqnum 1.
    assert_eq!(recorder.mt(0), b"A");
    assert!(recorder.has(0, 141), "reset Logon must carry 141=Y");
    assert_eq!(recorder.num(0, 34), Some(1));
}

#[test]
fn app_message_emits_control() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let ctrl = s
        .on_app(2, false, now, &mut RecordingEmitter::new())
        .unwrap();
    assert_eq!(ctrl, Control::Application);
    assert_eq!(s.next_inbound_seq(), 3);
}

#[test]
fn test_request_is_echoed() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let mut recorder = RecordingEmitter::new();
    s.on_test_request(2, false, b"PROBE7", now, &mut recorder)
        .unwrap();
    assert_eq!(recorder.len(), 1);
    // Heartbeat (35=0) echoing TestReqID(112)=PROBE7.
    assert_eq!(recorder.mt(0), b"0");
    assert_eq!(recorder.val(0, 112), Some(b"PROBE7".as_ref()));
}

#[test]
fn heartbeat_fires_on_outbound_idle() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let mut recorder = RecordingEmitter::new();
    s.on_timeout(now + Duration::from_secs(29), &mut recorder)
        .unwrap();
    assert_eq!(recorder.len(), 0);

    recorder.clear();
    s.on_timeout(now + Duration::from_secs(30), &mut recorder)
        .unwrap();
    assert_eq!(recorder.len(), 1);
    // Heartbeat (35=0) with no echo (no 112).
    assert_eq!(recorder.mt(0), b"0");
    assert!(
        !recorder.has(0, 112),
        "idle Heartbeat must not echo a TestReqID"
    );
}

#[test]
fn heartbeat_not_queued_twice() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let mut rec1 = RecordingEmitter::new();
    s.on_timeout(now + Duration::from_secs(31), &mut rec1)
        .unwrap();
    let mut rec2 = RecordingEmitter::new();
    s.on_timeout(now + Duration::from_secs(32), &mut rec2)
        .unwrap();

    assert_eq!(rec1.len(), 1);
    assert_eq!(rec2.len(), 0);
}

#[test]
fn inbound_silence_probes_then_disconnects() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let probe_at = now + Duration::from_secs(36);
    let mut recorder = RecordingEmitter::new();
    s.on_timeout(probe_at, &mut recorder).unwrap();
    assert!(recorder.any_mt(b"1"), "must send a TestRequest probe");

    recorder.clear();
    let ctrl = s.on_timeout(probe_at + HB, &mut recorder).unwrap();
    assert_eq!(s.state(), State::Disconnected);
    assert_eq!(
        ctrl,
        Control::Disconnected {
            reason: DisconnectReason::TestRequestTimeout
        }
    );
    assert!(recorder.any_mt(b"5"), "timeout must send a Logout");
}

#[test]
fn probe_answered_keeps_session_alive() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let probe_at = now + Duration::from_secs(36);
    let mut recorder = RecordingEmitter::new();
    s.on_timeout(probe_at, &mut recorder).unwrap();
    s.on_heartbeat(
        2,
        false,
        None,
        probe_at + Duration::from_secs(1),
        &mut recorder,
    )
    .unwrap();

    s.on_timeout(probe_at + HB, &mut recorder).unwrap();
    assert_eq!(s.state(), State::Active);
}

/// A peer that answers a probe with a frame we cannot dispatch (e.g. no MsgType)
/// has still demonstrated liveness, so the probe must be disarmed. Otherwise the
/// next timeout drops a live session with `TestRequestTimeout`.
#[test]
fn probe_answered_by_unprocessable_message_keeps_session_alive() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let probe_at = now + Duration::from_secs(36);
    let mut recorder = RecordingEmitter::new();
    s.on_timeout(probe_at, &mut recorder).unwrap();
    assert!(recorder.any_mt(b"1"), "must send a TestRequest probe");

    recorder.clear();
    s.on_reject_inbound(
        2,
        false,
        Some(35),
        1,
        probe_at + Duration::from_secs(1),
        &mut recorder,
    )
    .unwrap();

    let ctrl = s.on_timeout(probe_at + HB, &mut recorder).unwrap();
    assert_eq!(s.state(), State::Active);
    assert_ne!(
        ctrl,
        Control::Disconnected {
            reason: DisconnectReason::TestRequestTimeout
        }
    );
}

#[test]
fn gap_triggers_resend_request() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let mut recorder = RecordingEmitter::new();
    // A gap suppresses the app message but fires a ResendRequest.
    let ctrl = s.on_app(5, false, now, &mut recorder).unwrap();
    assert_eq!(s.state(), State::Resending);
    assert_eq!(ctrl, Control::None);
    assert_eq!(recorder.len(), 1);
    // ResendRequest (35=2) with BeginSeqNo(7)=2.
    assert_eq!(recorder.mt(0), b"2");
    assert_eq!(recorder.num(0, 7), Some(2));

    for seq in 2u32..=5 {
        s.on_app(seq, true, now, &mut RecordingEmitter::new())
            .unwrap();
    }
    assert_eq!(s.state(), State::Active);
    assert_eq!(s.next_inbound_seq(), 6);
}

#[test]
fn gap_fill_advances_past_admin_messages() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let mut recorder = RecordingEmitter::new();
    s.on_app(6, false, now, &mut recorder).unwrap();
    assert_eq!(s.state(), State::Resending);

    recorder.clear();
    let ctrl = s.on_sequence_reset(2, 7, true, now, &mut recorder).unwrap();
    assert_eq!(s.next_inbound_seq(), 7);
    assert_eq!(s.state(), State::Active);
    assert_eq!(recorder.len(), 0);
    assert_eq!(ctrl, Control::SequenceReset);
}

#[test]
fn sequence_reset_reset_mode_ignores_seq() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let ctrl = s
        .on_sequence_reset(999, 50, false, now, &mut RecordingEmitter::new())
        .unwrap();
    assert_eq!(s.next_inbound_seq(), 50);
    assert_eq!(ctrl, Control::SequenceReset);
}

#[test]
fn resend_request_surfaces_control() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);
    s.allocate_seq(now).unwrap(); // seq 2
    s.allocate_seq(now).unwrap(); // seq 3

    let mut recorder = RecordingEmitter::new();
    let ctrl = s.on_resend_request(2, false, now, &mut recorder).unwrap();
    assert_eq!(ctrl, Control::ResendRequest);
    // The replay walk (gap-fills + PossDup re-frames) is driven by the driver
    // from its locally parsed begin/end — no admin emitted by the handler here.
    assert_eq!(recorder.len(), 0);
}

#[test]
fn seq_too_low_disconnects() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);
    s.on_app(2, false, now, &mut RecordingEmitter::new())
        .unwrap(); // seq 2 consumed

    let ctrl = s
        .on_app(2, false, now, &mut RecordingEmitter::new())
        .unwrap(); // seq 2 again, no poss_dup
    assert_eq!(s.state(), State::Disconnected);
    assert_eq!(
        ctrl,
        Control::Disconnected {
            reason: DisconnectReason::SeqNumTooLow
        }
    );
}

#[test]
fn poss_dup_below_expected_is_ignored() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);
    s.on_app(2, false, now, &mut RecordingEmitter::new())
        .unwrap();

    let mut recorder = RecordingEmitter::new();
    let ctrl = s.on_app(2, true, now, &mut recorder).unwrap(); // poss_dup — silent ignore
    assert_eq!(s.state(), State::Active);
    assert_eq!(ctrl, Control::None);
    assert_eq!(recorder.len(), 0);
}

#[test]
fn comp_id_mismatch_disconnects() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let mut recorder = RecordingEmitter::new();
    let ctrl = s.on_comp_id_mismatch(now, &mut recorder).unwrap();
    assert_eq!(s.state(), State::Disconnected);
    assert_eq!(
        ctrl,
        Control::Disconnected {
            reason: DisconnectReason::CompIdMismatch
        }
    );
    assert!(recorder.any_mt(b"5"), "comp-id mismatch must send a Logout");
}

#[test]
fn initiated_logout_round_trip() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let mut recorder = RecordingEmitter::new();
    s.logout(now, &mut recorder).unwrap();
    assert_eq!(s.state(), State::LogoutPending);
    assert!(recorder.any_mt(b"5"), "logout must send a Logout");

    recorder.clear();
    let ctrl = s.on_logout(2, false, now, &mut recorder).unwrap();
    assert_eq!(s.state(), State::Disconnected);
    assert_eq!(
        ctrl,
        Control::Disconnected {
            reason: DisconnectReason::Logout
        }
    );
}

#[test]
fn counterparty_logout_is_confirmed() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let mut recorder = RecordingEmitter::new();
    let ctrl = s.on_logout(2, false, now, &mut recorder).unwrap();
    assert_eq!(s.state(), State::Disconnected);
    assert_eq!(
        ctrl,
        Control::Disconnected {
            reason: DisconnectReason::Logout
        }
    );
    assert_eq!(recorder.len(), 1);
    assert_eq!(recorder.mt(0), b"5", "must confirm with a Logout");
}

#[test]
fn logout_timeout_disconnects() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);
    let mut recorder = RecordingEmitter::new();
    s.logout(now, &mut recorder).unwrap();

    recorder.clear();
    let ctrl = s.on_timeout(now + HB, &mut recorder).unwrap();
    assert_eq!(s.state(), State::Disconnected);
    assert_eq!(
        ctrl,
        Control::Disconnected {
            reason: DisconnectReason::LogoutTimeout
        }
    );
}

#[test]
fn logon_timeout_disconnects() {
    let mut s = new_session();
    let now = Instant::now();
    let mut recorder = RecordingEmitter::new();
    s.connect(now, &mut recorder).unwrap();

    recorder.clear();
    let ctrl = s.on_timeout(now + HB, &mut recorder).unwrap();
    assert_eq!(s.state(), State::Disconnected);
    assert_eq!(
        ctrl,
        Control::Disconnected {
            reason: DisconnectReason::LogonTimeout
        }
    );
}

#[test]
fn reject_received_surfaces_control() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let ctrl = s
        .on_reject(2, false, now, &mut RecordingEmitter::new())
        .unwrap();
    assert_eq!(ctrl, Control::Reject);
}

#[test]
fn seq_nums_survive_reconnect() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);
    s.allocate_seq(now).unwrap(); // outbound seq 2

    let mut recorder = RecordingEmitter::new();
    s.on_logout(2, false, now, &mut recorder).unwrap(); // counterparty logout at inbound seq 2; session replies (seq 3), disconnects

    assert_eq!(s.state(), State::Disconnected);

    recorder.clear();
    s.connect(now, &mut recorder).unwrap();
    // Reconnect resumes at outbound seq 4 (Logon, no 141).
    assert_eq!(recorder.mt(0), b"A");
    assert!(!recorder.has(0, 141));
    assert_eq!(recorder.num(0, 34), Some(4));

    s.on_logon(3, 30, false, false, now, &mut recorder).unwrap();
    assert_eq!(s.state(), State::Active);
}

#[test]
fn next_timeout_tracks_deadlines() {
    let mut s = new_session();
    assert!(s.next_timeout().is_none());

    let now = Instant::now();
    let mut recorder = RecordingEmitter::new();
    s.connect(now, &mut recorder).unwrap();
    assert_eq!(s.next_timeout(), Some(now + HB));

    s.on_logon(1, 30, false, false, now, &mut recorder).unwrap();
    assert_eq!(s.next_timeout(), Some(now + HB));
}

#[test]
fn messages_ignored_while_disconnected() {
    let mut s = new_session();
    let now = Instant::now();

    let mut recorder = RecordingEmitter::new();
    let ctrl = s.on_app(1, false, now, &mut recorder).unwrap();
    assert_eq!(s.state(), State::Disconnected);
    assert_eq!(ctrl, Control::None);
    assert_eq!(recorder.len(), 0);
}
