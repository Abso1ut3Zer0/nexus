use std::time::Duration;

use nexus_fix_codec::{
    AdminEncode, AdminHeader, AdminMsgOut, AsciiTextStr, DecodeError, FieldView, FixAdminMsg,
    FixDictionary, FixHeader, FixTimestamp, FrameFormatter, NoCustomizer, find_tag, parse_fix_uint,
};
use nexus_fix_engine::{
    AppIn, Control, DisconnectReason, Emit, LogonIn, LogoutIn, RejectIn, ResendRequestIn,
    SequenceResetIn, SessionState, State, TestRequestIn,
};

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

fn establish(s: &mut SessionState) {
    let mut recorder = RecordingEmitter::new();
    s.connect(&mut recorder).unwrap();
    s.on_logon(
        LogonIn {
            seq: 1,
            heart_bt_int_s: 30,
            is_reset_seq_num: false,
        },
        &mut recorder,
    )
    .unwrap();
    assert_eq!(s.state(), State::Active);
}

#[test]
fn initiator_handshake() {
    let mut s = new_session();

    let mut recorder = RecordingEmitter::new();
    s.connect(&mut recorder).unwrap();
    assert_eq!(s.state(), State::LogonSent);
    assert_eq!(recorder.len(), 1);
    // Logon (35=A, no 141) at seqnum 1 with HeartBtInt(108)=30.
    assert_eq!(recorder.mt(0), b"A");
    assert!(!recorder.has(0, 141), "plain Logon must not carry 141");
    assert_eq!(recorder.num(0, 34), Some(1));
    assert_eq!(recorder.num(0, 108), Some(30));

    recorder.clear();
    // Initiator (state LogonSent) receiving the peer's Logon ack → acknowledged.
    let ctrl = s
        .on_logon(
            LogonIn {
                seq: 1,
                heart_bt_int_s: 30,
                is_reset_seq_num: false,
            },
            &mut recorder,
        )
        .unwrap();
    assert_eq!(s.state(), State::Active);
    assert_eq!(ctrl, Control::Logon { acknowledged: true });
    assert_eq!(recorder.len(), 0);
    assert_eq!(s.next_inbound_seq(), 2);
    assert_eq!(s.next_outbound_seq(), 2);
}

#[test]
fn acceptor_handshake() {
    let mut s = new_session();

    let mut recorder = RecordingEmitter::new();
    // Acceptor (fresh session, state Disconnected): the Logon surfaces a decision (no auto-reply);
    // the user then accepts, which emits the reply and brings the session up.
    let ctrl = s
        .on_logon(
            LogonIn {
                seq: 1,
                heart_bt_int_s: 15,
                is_reset_seq_num: false,
            },
            &mut recorder,
        )
        .unwrap();
    assert_eq!(
        ctrl,
        Control::LogonRequest {
            seq: 1,
            heart_bt_int_s: 15
        }
    );
    assert_eq!(recorder.len(), 0, "no reply before the user accepts");
    assert_eq!(
        s.state(),
        State::Disconnected,
        "state unchanged until accept"
    );

    let ctrl = s.accept_logon(1, 15, false, &mut recorder).unwrap();
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

    let mut recorder = RecordingEmitter::new();
    // A reset Logon (141=Y) surfaces a reset decision; accepting emits the
    // LogonReset reply.
    let ctrl = s
        .on_logon(
            LogonIn {
                seq: 1,
                heart_bt_int_s: 30,
                is_reset_seq_num: true,
            },
            &mut recorder,
        )
        .unwrap();
    assert_eq!(
        ctrl,
        Control::LogonResetRequest {
            seq: 1,
            heart_bt_int_s: 30
        }
    );
    assert_eq!(recorder.len(), 0);

    s.accept_logon(1, 30, true, &mut recorder).unwrap();
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
    establish(&mut s);

    let ctrl = s
        .on_app(
            AppIn {
                seq: 2,
                is_poss_dup: false,
            },
            &mut RecordingEmitter::new(),
        )
        .unwrap();
    assert_eq!(ctrl, Control::Application);
    assert_eq!(s.next_inbound_seq(), 3);
}

#[test]
fn test_request_surfaces_not_echoed() {
    let mut s = new_session();
    establish(&mut s);

    let mut recorder = RecordingEmitter::new();
    // The engine no longer auto-echoes: an in-sequence TestRequest surfaces as
    // `Control::TestRequest` (the user answers with `heartbeat`), emitting nothing.
    let ctrl = s
        .on_test_request(
            TestRequestIn {
                seq: 2,
                is_poss_dup: false,
            },
            &mut recorder,
        )
        .unwrap();
    assert_eq!(ctrl, Control::TestRequest);
    assert_eq!(recorder.len(), 0, "no engine-driven Heartbeat echo");
    assert_eq!(s.next_inbound_seq(), 3);
}

#[test]
fn gap_surfaces_gap_detected() {
    let mut s = new_session();
    establish(&mut s);

    let mut recorder = RecordingEmitter::new();
    // A gap suppresses the app message and surfaces GapDetected (the user drives
    // the ResendRequest); the engine emits nothing but enters Resending.
    let ctrl = s
        .on_app(
            AppIn {
                seq: 5,
                is_poss_dup: false,
            },
            &mut recorder,
        )
        .unwrap();
    assert_eq!(s.state(), State::Resending);
    assert_eq!(ctrl, Control::GapDetected { begin: 2 });
    assert_eq!(recorder.len(), 0);

    for seq in 2u32..=5 {
        s.on_app(
            AppIn {
                seq,
                is_poss_dup: true,
            },
            &mut RecordingEmitter::new(),
        )
        .unwrap();
    }
    assert_eq!(s.state(), State::Active);
    assert_eq!(s.next_inbound_seq(), 6);
}

#[test]
fn gap_fill_advances_past_admin_messages() {
    let mut s = new_session();
    establish(&mut s);

    let mut recorder = RecordingEmitter::new();
    s.on_app(
        AppIn {
            seq: 6,
            is_poss_dup: false,
        },
        &mut recorder,
    )
    .unwrap();
    assert_eq!(s.state(), State::Resending);

    recorder.clear();
    let ctrl = s
        .on_sequence_reset(
            SequenceResetIn {
                seq: 2,
                new_seq: 7,
                is_poss_dup: false,
                is_gap_fill: true,
            },
            &mut recorder,
        )
        .unwrap();
    assert_eq!(s.next_inbound_seq(), 7);
    assert_eq!(s.state(), State::Active);
    assert_eq!(recorder.len(), 0);
    assert_eq!(ctrl, Control::SequenceReset);
}

#[test]
fn sequence_reset_reset_mode_ignores_seq() {
    let mut s = new_session();
    establish(&mut s);

    let ctrl = s
        .on_sequence_reset(
            SequenceResetIn {
                seq: 999,
                new_seq: 50,
                is_poss_dup: false,
                is_gap_fill: false,
            },
            &mut RecordingEmitter::new(),
        )
        .unwrap();
    assert_eq!(s.next_inbound_seq(), 50);
    assert_eq!(ctrl, Control::SequenceReset);
}

#[test]
fn resend_request_surfaces_control() {
    let mut s = new_session();
    establish(&mut s);
    s.allocate_seq().unwrap(); // seq 2
    s.allocate_seq().unwrap(); // seq 3

    let mut recorder = RecordingEmitter::new();
    let ctrl = s
        .on_resend_request(
            ResendRequestIn {
                seq: 2,
                is_poss_dup: false,
            },
            &mut recorder,
        )
        .unwrap();
    assert_eq!(ctrl, Control::ResendRequest);
    // The replay walk (gap-fills + PossDup re-frames) is driven by the driver
    // from its locally parsed begin/end — no admin emitted by the handler here.
    assert_eq!(recorder.len(), 0);
}

#[test]
fn seq_too_low_disconnects() {
    let mut s = new_session();
    establish(&mut s);
    s.on_app(
        AppIn {
            seq: 2,
            is_poss_dup: false,
        },
        &mut RecordingEmitter::new(),
    )
    .unwrap(); // seq 2 consumed

    let ctrl = s
        .on_app(
            AppIn {
                seq: 2,
                is_poss_dup: false,
            },
            &mut RecordingEmitter::new(),
        )
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
    establish(&mut s);
    s.on_app(
        AppIn {
            seq: 2,
            is_poss_dup: false,
        },
        &mut RecordingEmitter::new(),
    )
    .unwrap();

    let mut recorder = RecordingEmitter::new();
    let ctrl = s
        .on_app(
            AppIn {
                seq: 2,
                is_poss_dup: true,
            },
            &mut recorder,
        )
        .unwrap(); // poss_dup — silent ignore
    assert_eq!(s.state(), State::Active);
    assert_eq!(ctrl, Control::None);
    assert_eq!(recorder.len(), 0);
}

#[test]
fn comp_id_mismatch_disconnects() {
    let mut s = new_session();
    establish(&mut s);

    let mut recorder = RecordingEmitter::new();
    let ctrl = s.on_comp_id_mismatch(&mut recorder).unwrap();
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
    establish(&mut s);

    let mut recorder = RecordingEmitter::new();
    s.logout(None, &mut recorder).unwrap();
    assert_eq!(s.state(), State::LogoutPending);
    assert!(recorder.any_mt(b"5"), "logout must send a Logout");

    recorder.clear();
    let ctrl = s
        .on_logout(
            LogoutIn {
                seq: 2,
                is_poss_dup: false,
            },
            &mut recorder,
        )
        .unwrap();
    assert_eq!(s.state(), State::Disconnected);
    assert_eq!(ctrl, Control::LoggedOut);
}

#[test]
fn counterparty_logout_surfaces_request() {
    let mut s = new_session();
    establish(&mut s);

    // A peer-initiated Logout while Active no longer auto-replies or disconnects:
    // it surfaces as `Control::Logout` (Message::LogoutRequest) for the user to
    // answer with `logout(..)`. The session stays Active until the user replies.
    let mut recorder = RecordingEmitter::new();
    let ctrl = s
        .on_logout(
            LogoutIn {
                seq: 2,
                is_poss_dup: false,
            },
            &mut recorder,
        )
        .unwrap();
    assert_eq!(ctrl, Control::Logout);
    assert_eq!(recorder.len(), 0, "no engine-driven Logout reply");
    assert_eq!(s.state(), State::Active);
    assert_eq!(
        s.next_inbound_seq(),
        3,
        "the in-sequence Logout advanced inbound"
    );
}

#[test]
fn reject_received_surfaces_control() {
    let mut s = new_session();
    establish(&mut s);

    let ctrl = s
        .on_reject(
            RejectIn {
                seq: 2,
                is_poss_dup: false,
            },
            &mut RecordingEmitter::new(),
        )
        .unwrap();
    assert_eq!(ctrl, Control::Reject);
}

#[test]
fn seq_nums_survive_reconnect() {
    let mut s = new_session();
    establish(&mut s);
    s.allocate_seq().unwrap(); // outbound seq 2

    let mut recorder = RecordingEmitter::new();
    // We initiate the logout (Logout seq 3, → LogoutPending); the counterparty's
    // in-sequence Logout confirms it and disconnects.
    s.logout(None, &mut recorder).unwrap();
    s.on_logout(
        LogoutIn {
            seq: 2,
            is_poss_dup: false,
        },
        &mut recorder,
    )
    .unwrap();

    assert_eq!(s.state(), State::Disconnected);

    recorder.clear();
    s.connect(&mut recorder).unwrap();
    // Reconnect resumes at outbound seq 4 (Logon, no 141).
    assert_eq!(recorder.mt(0), b"A");
    assert!(!recorder.has(0, 141));
    assert_eq!(recorder.num(0, 34), Some(4));

    s.on_logon(
        LogonIn {
            seq: 3,
            heart_bt_int_s: 30,
            is_reset_seq_num: false,
        },
        &mut recorder,
    )
    .unwrap();
    assert_eq!(s.state(), State::Active);
}

#[test]
fn messages_ignored_while_disconnected() {
    let mut s = new_session();

    let mut recorder = RecordingEmitter::new();
    let ctrl = s
        .on_app(
            AppIn {
                seq: 1,
                is_poss_dup: false,
            },
            &mut recorder,
        )
        .unwrap();
    assert_eq!(s.state(), State::Disconnected);
    assert_eq!(ctrl, Control::None);
    assert_eq!(recorder.len(), 0);
}
