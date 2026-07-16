use std::convert::Infallible;
use std::time::{Duration, Instant};

use nexus_fix_engine::{AdminMsg, Control, DisconnectReason, SessionState, State};

const HB: Duration = Duration::from_secs(30);

fn new_session() -> SessionState {
    SessionState::new(HB)
}

/// A recording emit closure: pushes each admin message into `sent`, never errors
/// (`E = Infallible`). Tests read `sent` for the admin assertions and the
/// returned [`Control`] for the verdict.
fn recorder(sent: &mut Vec<AdminMsg>) -> impl FnMut(AdminMsg) -> Result<(), Infallible> + '_ {
    move |m| {
        sent.push(m);
        Ok(())
    }
}

fn establish(s: &mut SessionState, now: Instant) {
    let mut sent = Vec::new();
    s.connect(now, &mut recorder(&mut sent)).unwrap();
    s.on_logon(1, 30, false, false, now, &mut recorder(&mut sent))
        .unwrap();
    assert_eq!(s.state(), State::Active);
}

#[test]
fn initiator_handshake() {
    let mut s = new_session();
    let now = Instant::now();

    let mut sent = Vec::new();
    s.connect(now, &mut recorder(&mut sent)).unwrap();
    assert_eq!(s.state(), State::LogonSent);
    assert_eq!(sent.len(), 1);
    assert!(matches!(
        sent[0],
        AdminMsg::Logon {
            seq: 1,
            heart_bt_int_s: 30,
            ..
        }
    ));

    sent.clear();
    // Initiator receiving the peer's Logon ack: send_reply = false → acknowledged.
    let ctrl = s
        .on_logon(1, 30, false, false, now, &mut recorder(&mut sent))
        .unwrap();
    assert_eq!(s.state(), State::Active);
    assert_eq!(ctrl, Control::Logon { acknowledged: true });
    assert_eq!(sent.len(), 0);
    assert_eq!(s.next_inbound_seq(), 2);
    assert_eq!(s.next_outbound_seq(), 2);
}

#[test]
fn acceptor_handshake() {
    let mut s = new_session();
    let now = Instant::now();

    let mut sent = Vec::new();
    // Acceptor: send_reply = true → this Logon is answered, not an ack.
    let ctrl = s
        .on_logon(1, 15, false, true, now, &mut recorder(&mut sent))
        .unwrap();
    assert_eq!(s.state(), State::Active);
    assert_eq!(
        ctrl,
        Control::Logon {
            acknowledged: false
        }
    );
    assert_eq!(sent.len(), 1);
    assert!(matches!(
        sent[0],
        AdminMsg::Logon {
            seq: 1,
            heart_bt_int_s: 15,
            ..
        }
    ));
}

#[test]
fn logon_reset_seq_num_flag() {
    let mut s = new_session();
    let now = Instant::now();

    let mut sent = Vec::new();
    s.on_logon(1, 30, true, true, now, &mut recorder(&mut sent))
        .unwrap();
    assert_eq!(s.state(), State::Active);
    assert_eq!(sent.len(), 1);
    assert!(matches!(sent[0], AdminMsg::LogonReset { seq: 1, .. }));
}

#[test]
fn app_message_emits_control() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let mut sent = Vec::new();
    let ctrl = s.on_app(2, false, now, &mut recorder(&mut sent)).unwrap();
    assert_eq!(ctrl, Control::Application);
    assert_eq!(s.next_inbound_seq(), 3);
}

#[test]
fn test_request_is_echoed() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let mut sent = Vec::new();
    s.on_test_request(2, false, b"PROBE7", now, &mut recorder(&mut sent))
        .unwrap();
    assert_eq!(sent.len(), 1);
    match sent[0] {
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

    let mut sent = Vec::new();
    s.on_timeout(now + Duration::from_secs(29), &mut recorder(&mut sent))
        .unwrap();
    assert_eq!(sent.len(), 0);

    sent.clear();
    s.on_timeout(now + Duration::from_secs(30), &mut recorder(&mut sent))
        .unwrap();
    assert_eq!(sent.len(), 1);
    assert!(matches!(sent[0], AdminMsg::Heartbeat { echo: None, .. }));
}

#[test]
fn heartbeat_not_queued_twice() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let mut sent1 = Vec::new();
    s.on_timeout(now + Duration::from_secs(31), &mut recorder(&mut sent1))
        .unwrap();
    let mut sent2 = Vec::new();
    s.on_timeout(now + Duration::from_secs(32), &mut recorder(&mut sent2))
        .unwrap();

    assert_eq!(sent1.len(), 1);
    assert_eq!(sent2.len(), 0);
}

#[test]
fn inbound_silence_probes_then_disconnects() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let probe_at = now + Duration::from_secs(36);
    let mut sent = Vec::new();
    s.on_timeout(probe_at, &mut recorder(&mut sent)).unwrap();
    assert!(
        sent.iter()
            .any(|a| matches!(a, AdminMsg::TestRequest { .. }))
    );

    sent.clear();
    let ctrl = s
        .on_timeout(probe_at + HB, &mut recorder(&mut sent))
        .unwrap();
    assert_eq!(s.state(), State::Disconnected);
    assert_eq!(
        ctrl,
        Control::Disconnected {
            reason: DisconnectReason::TestRequestTimeout
        }
    );
    assert!(sent.iter().any(|a| matches!(a, AdminMsg::Logout { .. })));
}

#[test]
fn probe_answered_keeps_session_alive() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let probe_at = now + Duration::from_secs(36);
    let mut sent = Vec::new();
    s.on_timeout(probe_at, &mut recorder(&mut sent)).unwrap();
    s.on_heartbeat(
        2,
        false,
        None,
        probe_at + Duration::from_secs(1),
        &mut recorder(&mut sent),
    )
    .unwrap();

    s.on_timeout(probe_at + HB, &mut recorder(&mut sent))
        .unwrap();
    assert_eq!(s.state(), State::Active);
}

#[test]
fn gap_triggers_resend_request() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let mut sent = Vec::new();
    // A gap suppresses the app message but fires a ResendRequest.
    let ctrl = s.on_app(5, false, now, &mut recorder(&mut sent)).unwrap();
    assert_eq!(s.state(), State::Resending);
    assert_eq!(ctrl, Control::None);
    assert_eq!(sent.len(), 1);
    assert!(matches!(sent[0], AdminMsg::ResendRequest { begin: 2, .. }));

    for seq in 2u32..=5 {
        let mut s2 = Vec::new();
        s.on_app(seq, true, now, &mut recorder(&mut s2)).unwrap();
    }
    assert_eq!(s.state(), State::Active);
    assert_eq!(s.next_inbound_seq(), 6);
}

#[test]
fn gap_fill_advances_past_admin_messages() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let mut sent = Vec::new();
    s.on_app(6, false, now, &mut recorder(&mut sent)).unwrap();
    assert_eq!(s.state(), State::Resending);

    sent.clear();
    let ctrl = s
        .on_sequence_reset(2, 7, true, now, &mut recorder(&mut sent))
        .unwrap();
    assert_eq!(s.next_inbound_seq(), 7);
    assert_eq!(s.state(), State::Active);
    assert_eq!(sent.len(), 0);
    assert_eq!(ctrl, Control::SequenceReset);
}

#[test]
fn sequence_reset_reset_mode_ignores_seq() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let mut sent = Vec::new();
    let ctrl = s
        .on_sequence_reset(999, 50, false, now, &mut recorder(&mut sent))
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

    let mut sent = Vec::new();
    let ctrl = s
        .on_resend_request(2, false, now, &mut recorder(&mut sent))
        .unwrap();
    assert_eq!(ctrl, Control::ResendRequest);
    // The replay walk (gap-fills + PossDup re-frames) is driven by the driver
    // from its locally parsed begin/end — no admin emitted by the handler here.
    assert_eq!(sent.len(), 0);
}

#[test]
fn seq_too_low_disconnects() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);
    let mut sent = Vec::new();
    s.on_app(2, false, now, &mut recorder(&mut sent)).unwrap(); // seq 2 consumed

    sent.clear();
    let ctrl = s.on_app(2, false, now, &mut recorder(&mut sent)).unwrap(); // seq 2 again, no poss_dup
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
    let mut sent = Vec::new();
    s.on_app(2, false, now, &mut recorder(&mut sent)).unwrap();

    sent.clear();
    let ctrl = s.on_app(2, true, now, &mut recorder(&mut sent)).unwrap(); // poss_dup — silent ignore
    assert_eq!(s.state(), State::Active);
    assert_eq!(ctrl, Control::None);
    assert_eq!(sent.len(), 0);
}

#[test]
fn comp_id_mismatch_disconnects() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let mut sent = Vec::new();
    let ctrl = s
        .on_comp_id_mismatch(now, &mut recorder(&mut sent))
        .unwrap();
    assert_eq!(s.state(), State::Disconnected);
    assert_eq!(
        ctrl,
        Control::Disconnected {
            reason: DisconnectReason::CompIdMismatch
        }
    );
    assert!(sent.iter().any(|a| matches!(a, AdminMsg::Logout { .. })));
}

#[test]
fn initiated_logout_round_trip() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);

    let mut sent = Vec::new();
    s.logout(now, &mut recorder(&mut sent)).unwrap();
    assert_eq!(s.state(), State::LogoutPending);
    assert!(sent.iter().any(|a| matches!(a, AdminMsg::Logout { .. })));

    sent.clear();
    let ctrl = s
        .on_logout(2, false, now, &mut recorder(&mut sent))
        .unwrap();
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

    let mut sent = Vec::new();
    let ctrl = s
        .on_logout(2, false, now, &mut recorder(&mut sent))
        .unwrap();
    assert_eq!(s.state(), State::Disconnected);
    assert_eq!(
        ctrl,
        Control::Disconnected {
            reason: DisconnectReason::Logout
        }
    );
    assert_eq!(sent.len(), 1);
    assert!(matches!(sent[0], AdminMsg::Logout { .. }));
}

#[test]
fn logout_timeout_disconnects() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);
    let mut sent = Vec::new();
    s.logout(now, &mut recorder(&mut sent)).unwrap();

    sent.clear();
    let ctrl = s.on_timeout(now + HB, &mut recorder(&mut sent)).unwrap();
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
    let mut sent = Vec::new();
    s.connect(now, &mut recorder(&mut sent)).unwrap();

    sent.clear();
    let ctrl = s.on_timeout(now + HB, &mut recorder(&mut sent)).unwrap();
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

    let mut sent = Vec::new();
    let ctrl = s
        .on_reject(2, false, now, &mut recorder(&mut sent))
        .unwrap();
    assert_eq!(ctrl, Control::Reject);
}

#[test]
fn seq_nums_survive_reconnect() {
    let mut s = new_session();
    let now = Instant::now();
    establish(&mut s, now);
    s.allocate_seq(now).unwrap(); // outbound seq 2

    let mut sent = Vec::new();
    s.on_logout(2, false, now, &mut recorder(&mut sent))
        .unwrap(); // counterparty logout at inbound seq 2; session replies (seq 3), disconnects

    assert_eq!(s.state(), State::Disconnected);

    sent.clear();
    s.connect(now, &mut recorder(&mut sent)).unwrap();
    assert!(matches!(sent[0], AdminMsg::Logon { seq: 4, .. }));

    s.on_logon(3, 30, false, false, now, &mut recorder(&mut sent))
        .unwrap();
    assert_eq!(s.state(), State::Active);
}

#[test]
fn next_timeout_tracks_deadlines() {
    let mut s = new_session();
    assert!(s.next_timeout().is_none());

    let now = Instant::now();
    let mut sent = Vec::new();
    s.connect(now, &mut recorder(&mut sent)).unwrap();
    assert_eq!(s.next_timeout(), Some(now + HB));

    s.on_logon(1, 30, false, false, now, &mut recorder(&mut sent))
        .unwrap();
    assert_eq!(s.next_timeout(), Some(now + HB));
}

#[test]
fn messages_ignored_while_disconnected() {
    let mut s = new_session();
    let now = Instant::now();

    let mut sent = Vec::new();
    let ctrl = s.on_app(1, false, now, &mut recorder(&mut sent)).unwrap();
    assert_eq!(s.state(), State::Disconnected);
    assert_eq!(ctrl, Control::None);
    assert_eq!(sent.len(), 0);
}
