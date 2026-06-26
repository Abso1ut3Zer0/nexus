use std::time::{Duration, Instant};

use nexus_fix_engine::{AdminMsg, DisconnectReason, Event, SessionState, State};

const HB: Duration = Duration::from_secs(30);

fn new_session() -> SessionState {
    SessionState::new(HB)
}

fn establish(s: &mut SessionState, now: Instant) {
    s.connect(now);
    s.on_logon(1, 30, false, false, now);
    assert_eq!(s.state(), State::Active);
}

fn admin_msgs(out: nexus_fix_engine::Out) -> Vec<AdminMsg> {
    out.admin_messages().collect()
}

#[test]
fn initiator_handshake() {
    let mut s = new_session();
    let now = Instant::now();

    let out = s.connect(now);
    assert_eq!(s.state(), State::LogonSent);
    let admins = admin_msgs(out);
    assert_eq!(admins.len(), 1);
    assert!(matches!(
        admins[0],
        AdminMsg::Logon {
            seq: 1,
            heart_bt_int_s: 30
        }
    ));

    let out = s.on_logon(1, 30, false, false, now);
    assert_eq!(s.state(), State::Active);
    assert_eq!(out.event(), Some(Event::Established { heart_bt_int_s: 30 }));
    assert_eq!(admin_msgs(out).len(), 0);
    assert_eq!(s.next_inbound_seq(), 2);
    assert_eq!(s.next_outbound_seq(), 2);
}

#[test]
fn acceptor_handshake() {
    let mut s = new_session();
    let now = Instant::now();

    let out = s.on_logon(1, 15, false, true, now);
    assert_eq!(s.state(), State::Active);
    assert_eq!(out.event(), Some(Event::Established { heart_bt_int_s: 15 }));
    let admins = admin_msgs(out);
    assert_eq!(admins.len(), 1);
    assert!(matches!(
        admins[0],
        AdminMsg::Logon {
            seq: 1,
            heart_bt_int_s: 15
        }
    ));
}

#[test]
fn logon_reset_seq_num_flag() {
    let mut s = new_session();
    let now = Instant::now();

    let out = s.on_logon(1, 30, true, true, now);
    assert_eq!(s.state(), State::Active);
    let admins = admin_msgs(out);
    assert_eq!(admins.len(), 1);
    assert!(matches!(admins[0], AdminMsg::Logon { seq: 1, .. }));
}

#[test]
fn app_message_emits_event() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let out = s.on_app(2, false, now);
    assert_eq!(
        out.event(),
        Some(Event::App {
            seq_num: 2,
            poss_dup: false
        })
    );
    assert_eq!(s.next_inbound_seq(), 3);
}

#[test]
fn test_request_is_echoed() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let out = s.on_test_request(2, false, b"PROBE7", now);
    let admins = admin_msgs(out);
    assert_eq!(admins.len(), 1);
    match admins[0] {
        AdminMsg::Heartbeat {
            echo: Some((id, id_len)),
            ..
        } => {
            assert_eq!(&id[..id_len as usize], b"PROBE7");
        }
        _ => panic!("expected Heartbeat with echo"),
    }
}

#[test]
fn heartbeat_fires_on_outbound_idle() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let out = s.on_timeout(now + Duration::from_secs(29));
    assert_eq!(admin_msgs(out).len(), 0);

    let out = s.on_timeout(now + Duration::from_secs(30));
    let admins = admin_msgs(out);
    assert_eq!(admins.len(), 1);
    assert!(matches!(admins[0], AdminMsg::Heartbeat { echo: None, .. }));
}

#[test]
fn heartbeat_not_queued_twice() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let out1 = s.on_timeout(now + Duration::from_secs(31));
    let out2 = s.on_timeout(now + Duration::from_secs(32));

    assert_eq!(admin_msgs(out1).len(), 1);
    assert_eq!(admin_msgs(out2).len(), 0);
}

#[test]
fn inbound_silence_probes_then_disconnects() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let probe_at = now + Duration::from_secs(36);
    let out = s.on_timeout(probe_at);
    assert!(
        out.admin_messages()
            .any(|a| matches!(a, AdminMsg::TestRequest { .. }))
    );

    let out = s.on_timeout(probe_at + HB);
    assert_eq!(s.state(), State::Disconnected);
    assert_eq!(
        out.event(),
        Some(Event::Disconnected {
            reason: DisconnectReason::TestRequestTimeout
        })
    );
    assert!(
        out.admin_messages()
            .any(|a| matches!(a, AdminMsg::Logout { .. }))
    );
}

#[test]
fn probe_answered_keeps_session_alive() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let probe_at = now + Duration::from_secs(36);
    s.on_timeout(probe_at);
    s.on_heartbeat(2, false, probe_at + Duration::from_secs(1));

    s.on_timeout(probe_at + HB);
    assert_eq!(s.state(), State::Active);
}

#[test]
fn gap_triggers_resend_request() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let out = s.on_app(5, false, now);
    assert_eq!(s.state(), State::Resending);
    assert_eq!(out.event(), None);
    let admins = admin_msgs(out);
    assert_eq!(admins.len(), 1);
    assert!(matches!(
        admins[0],
        AdminMsg::ResendRequest { begin: 2, .. }
    ));

    for seq in 2u32..=5 {
        s.on_app(seq, true, now);
    }
    assert_eq!(s.state(), State::Active);
    assert_eq!(s.next_inbound_seq(), 6);
}

#[test]
fn gap_fill_advances_past_admin_messages() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    s.on_app(6, false, now);
    assert_eq!(s.state(), State::Resending);

    let out = s.on_sequence_reset(2, 7, true, now);
    assert_eq!(s.next_inbound_seq(), 7);
    assert_eq!(s.state(), State::Active);
    assert!(out.admin_messages().count() == 0);
    assert_eq!(out.event(), Some(Event::SequenceReset { new_seq: 7 }));
}

#[test]
fn sequence_reset_reset_mode_ignores_seq() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let out = s.on_sequence_reset(999, 50, false, now);
    assert_eq!(s.next_inbound_seq(), 50);
    assert_eq!(out.event(), Some(Event::SequenceReset { new_seq: 50 }));
}

#[test]
fn resend_request_surfaces_event() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);
    s.allocate_seq(now).unwrap(); // seq 2
    s.allocate_seq(now).unwrap(); // seq 3

    let out = s.on_resend_request(2, false, 2, 3, now);
    assert_eq!(out.event(), Some(Event::ResendRange { begin: 2, end: 3 }));
    // The replay walk (gap-fills + PossDup re-frames) is driven by the
    // persistence layer via FixJournal::resend_range — no admin emitted here.
    assert_eq!(admin_msgs(out).len(), 0);
}

#[test]
fn seq_too_low_disconnects() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);
    s.on_app(2, false, now); // seq 2 consumed

    let out = s.on_app(2, false, now); // seq 2 again, no poss_dup
    assert_eq!(s.state(), State::Disconnected);
    assert_eq!(
        out.event(),
        Some(Event::Disconnected {
            reason: DisconnectReason::SeqNumTooLow
        })
    );
}

#[test]
fn poss_dup_below_expected_is_ignored() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);
    s.on_app(2, false, now);

    let out = s.on_app(2, true, now); // poss_dup — silent ignore
    assert_eq!(s.state(), State::Active);
    assert_eq!(out.event(), None);
    assert_eq!(admin_msgs(out).len(), 0);
}

#[test]
fn comp_id_mismatch_disconnects() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let out = s.on_comp_id_mismatch(now);
    assert_eq!(s.state(), State::Disconnected);
    assert_eq!(
        out.event(),
        Some(Event::Disconnected {
            reason: DisconnectReason::CompIdMismatch
        })
    );
    assert!(
        out.admin_messages()
            .any(|a| matches!(a, AdminMsg::Logout { .. }))
    );
}

#[test]
fn initiated_logout_round_trip() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let out = s.logout(now);
    assert_eq!(s.state(), State::LogoutPending);
    assert!(
        admin_msgs(out)
            .iter()
            .any(|a| matches!(a, AdminMsg::Logout { .. }))
    );

    let out = s.on_logout(2, false, now);
    assert_eq!(s.state(), State::Disconnected);
    assert_eq!(
        out.event(),
        Some(Event::Disconnected {
            reason: DisconnectReason::Logout
        })
    );
}

#[test]
fn counterparty_logout_is_confirmed() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let out = s.on_logout(2, false, now);
    assert_eq!(s.state(), State::Disconnected);
    assert_eq!(
        out.event(),
        Some(Event::Disconnected {
            reason: DisconnectReason::Logout
        })
    );
    let admins = admin_msgs(out);
    assert_eq!(admins.len(), 1);
    assert!(matches!(admins[0], AdminMsg::Logout { .. }));
}

#[test]
fn logout_timeout_disconnects() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);
    s.logout(now);

    let out = s.on_timeout(now + HB);
    assert_eq!(s.state(), State::Disconnected);
    assert_eq!(
        out.event(),
        Some(Event::Disconnected {
            reason: DisconnectReason::LogoutTimeout
        })
    );
}

#[test]
fn logon_timeout_disconnects() {
    let mut s = new_session();
    let now = Instant::now();
    s.connect(now);

    let out = s.on_timeout(now + HB);
    assert_eq!(s.state(), State::Disconnected);
    assert_eq!(
        out.event(),
        Some(Event::Disconnected {
            reason: DisconnectReason::LogonTimeout
        })
    );
}

#[test]
fn reject_received_surfaces_event() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let out = s.on_reject(2, false, 7, now);
    assert_eq!(out.event(), Some(Event::RejectReceived { ref_seq_num: 7 }));
}

#[test]
fn seq_nums_survive_reconnect() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);
    s.allocate_seq(now).unwrap(); // outbound seq 2

    s.on_logout(2, false, now); // counterparty logout at inbound seq 2; session replies (seq 3), disconnects

    assert_eq!(s.state(), State::Disconnected);

    let out = s.connect(now);
    let admins = admin_msgs(out);
    assert!(matches!(admins[0], AdminMsg::Logon { seq: 4, .. }));

    s.on_logon(3, 30, false, false, now);
    assert_eq!(s.state(), State::Active);
}

#[test]
fn next_timeout_tracks_deadlines() {
    let mut s = new_session();
    assert!(s.next_timeout().is_none());

    let now = Instant::now();
    s.connect(now);
    assert_eq!(s.next_timeout(), Some(now + HB));

    s.on_logon(1, 30, false, false, now);
    assert_eq!(s.next_timeout(), Some(now + HB));
}

#[test]
fn messages_ignored_while_disconnected() {
    let mut s = new_session();
    let now = Instant::now();

    let out = s.on_app(1, false, now);
    assert_eq!(s.state(), State::Disconnected);
    assert_eq!(out.event(), None);
    assert_eq!(admin_msgs(out).len(), 0);
}
