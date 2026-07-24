//! Journal stop-and-reopen recovery (battle-test deliverable).
//!
//! Proves persist-before-send survives an application restart: a session that
//! advances seqnums and writes its journal can be dropped ("app stop"), the
//! journal reopened from the same dir via [`FixJournal::open_existing`], the
//! `next_outbound` / `next_inbound` counters recovered, a fresh [`FixSession`]
//! seeded with [`SessionState::reset_seq_nums`], and the session resumes at the
//! recovered seqnums — the post-restart Logon carries `34=3`, not `34=1`, and
//! gap detection still works with the recovered inbound counter.
//!
//! Fully in-process (frames fed through the `read_spare`/`read_filled` byte
//! seam), so it is deterministic and socket-free.
#![cfg(unix)]

use std::path::{Path, PathBuf};
use std::time::Duration;

use nexus_fix_codec::{
    FieldView, FixAdminMsg, FixDictionary, FixHeader, FixTimestamp, FrameFormatter,
    encode_fix_uint, find_tag,
};
use nexus_fix_engine::{
    CompId, FixJournal, FixSession, MessageReader, MessageWriter, PollOutcome, SessionConfig,
    SessionState, State,
};

// ── mock dictionary (mirrors the conformance suites) ─────────────────────────

struct MockDict;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum MockMsgType {}

struct AdminDecoder<'buf> {
    _buf: &'buf [u8],
}

impl<'buf> FixAdminMsg<'buf> for AdminDecoder<'buf> {
    fn decode(buf: &'buf [u8]) -> Result<Self, nexus_fix_codec::DecodeError> {
        Ok(Self { _buf: buf })
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
    fn sender_comp_id(&self) -> Option<FieldView<'buf, &'buf nexus_fix_codec::AsciiTextStr>> {
        find_tag(self.buf, 0, 49).and_then(|s| FieldView::new(s, self.buf))
    }
    fn target_comp_id(&self) -> Option<FieldView<'buf, &'buf nexus_fix_codec::AsciiTextStr>> {
        find_tag(self.buf, 0, 56).and_then(|s| FieldView::new(s, self.buf))
    }
    fn poss_dup_flag(&self) -> Option<FieldView<'buf, bool>> {
        find_tag(self.buf, 0, 43).and_then(|s| FieldView::new(s, self.buf))
    }
    fn sending_time(&self) -> Option<FieldView<'buf, FixTimestamp>> {
        None
    }
}

// ── RAII scratch dir (temp-dir hygiene — must not leak journal dirs) ──────────

struct TempDir(PathBuf);

impl TempDir {
    fn new(suffix: &str) -> Self {
        let mut p = std::env::temp_dir();
        p.push(format!(
            "nexus_fix_recovery_{}_{}",
            std::process::id(),
            suffix
        ));
        let _ = std::fs::remove_dir_all(&p);
        std::fs::create_dir_all(&p).unwrap();
        Self(p)
    }
    fn path(&self) -> &Path {
        &self.0
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

// ── helpers ──────────────────────────────────────────────────────────────────

const WINDOW: usize = 256;
const ENGINE: &[u8] = b"ENGINE";
const PEER: &[u8] = b"PEER";

fn cfg() -> SessionConfig {
    SessionConfig {
        sender: CompId::new(ENGINE).unwrap(),
        target: CompId::new(PEER).unwrap(),
    }
}

/// A frame from the PEER's point of view (49=PEER, 56=ENGINE).
fn peer_frame(msg_type: &[u8], seq: u32, extra: &[(u32, &[u8])]) -> Vec<u8> {
    let mut buf = [0u8; 512];
    let mut seq_buf = [0u8; 10];
    let n = encode_fix_uint(seq, &mut seq_buf);
    let mut fmt = FrameFormatter::new(&mut buf, b"FIX.4.4", msg_type);
    fmt.field(34, &seq_buf[..n]);
    fmt.field(49, PEER);
    fmt.field(56, ENGINE);
    fmt.field(52, b"20260101-00:00:00.000");
    for (tag, val) in extra {
        fmt.field(*tag, val);
    }
    let (start, len) = fmt.finish().unwrap();
    buf[start..start + len].to_vec()
}

/// An ENGINE-side application frame (49=ENGINE, 56=PEER) at `seq`.
fn engine_app(seq: u32) -> Vec<u8> {
    let mut buf = [0u8; 512];
    let mut seq_buf = [0u8; 10];
    let n = encode_fix_uint(seq, &mut seq_buf);
    let mut fmt = FrameFormatter::new(&mut buf, b"FIX.4.4", b"D");
    fmt.field(34, &seq_buf[..n]);
    fmt.field(49, ENGINE);
    fmt.field(56, PEER);
    fmt.field(52, b"20260101-00:00:00.000");
    fmt.field(11, b"ORD-1");
    let (start, len) = fmt.finish().unwrap();
    buf[start..start + len].to_vec()
}

/// Discard whatever the engine queued outbound (a peer that reads and drops).
fn drain_out(writer: &mut MessageWriter<MockDict>) {
    let n = writer.data().len();
    if n > 0 {
        writer.advance(n);
    }
}

/// Feed one frame through the inbound byte seam and drive `poll` to quiescence,
/// draining outbound between steps. Panics on a hard protocol error (the
/// recovery path is expected to be clean).
fn feed(
    session: &mut FixSession<MockDict>,
    reader: &mut MessageReader<MockDict>,
    writer: &mut MessageWriter<MockDict>,
    frame: &[u8],
) {
    let mut off = 0;
    while off < frame.len() {
        let spare = reader.spare();
        assert!(!spare.is_empty(), "reader buffer unexpectedly full");
        let n = spare.len().min(frame.len() - off);
        spare[..n].copy_from_slice(&frame[off..off + n]);
        reader.filled(n);
        off += n;
    }
    loop {
        let outcome = session
            .poll(reader, writer)
            .expect("recovery path must not error");
        drain_out(writer);
        match outcome {
            PollOutcome::NeedMoreBytes | PollOutcome::Disconnected(_) => break,
            _ => {}
        }
    }
}

/// True if `frame` contains the FIX field `tag=val` (delimiter-bounded).
fn has_field(frame: &[u8], tag_eq_val: &[u8]) -> bool {
    // Match "\x01{tag=val}\x01"; also allow the field at buffer start.
    frame
        .windows(tag_eq_val.len() + 1)
        .any(|w| w[0] == 0x01 && &w[1..] == tag_eq_val)
}

// ── the recovery test ────────────────────────────────────────────────────────

#[test]
fn journal_stop_and_reopen_resumes_seqnums() {
    let dir = tmp();

    // ── phase 1: run a session that advances seqnums and writes the journal ──
    {
        let journal = FixJournal::open(dir.path(), 0, WINDOW).unwrap();
        let mut s1 =
            FixSession::<MockDict>::new(SessionState::new(Duration::from_secs(30)), cfg(), journal);
        let mut reader = MessageReader::<MockDict>::new();
        let mut writer = MessageWriter::<MockDict>::new();

        s1.encode_connect(&mut writer).unwrap(); // Logon(seq=1) queued + journaled
        drain_out(&mut writer);
        feed(
            &mut s1,
            &mut reader,
            &mut writer,
            &peer_frame(b"A", 1, &[(108, b"30")]),
        ); // Logon ack → Active
        assert_eq!(s1.state().state(), State::Active);
        assert_eq!(s1.state().next_outbound_seq(), 2);
        assert_eq!(s1.state().next_inbound_seq(), 2);

        let seq = s1.allocate_seq().unwrap(); // 2
        s1.encode_send_app(&mut writer, seq, &engine_app(seq))
            .unwrap(); // app(seq=2) journaled
        drain_out(&mut writer);
        feed(&mut s1, &mut reader, &mut writer, &peer_frame(b"0", 2, &[])); // inbound Heartbeat seq 2

        assert_eq!(s1.state().next_outbound_seq(), 3, "outbound advanced to 3");
        assert_eq!(s1.state().next_inbound_seq(), 3, "inbound advanced to 3");
        // s1 dropped here — simulates an application stop.
    }

    // ── phase 2: reopen the journal and recover the counters ─────────────────
    let (rec_out, rec_in) = {
        let recovered = FixJournal::open_existing(dir.path(), 0, WINDOW)
            .expect("open_existing must recover the stored session");
        (recovered.next_outbound(), recovered.next_inbound())
    };
    assert_eq!(
        rec_out, 3,
        "recovered next_outbound must match where phase 1 left off"
    );
    assert_eq!(
        rec_in, 3,
        "recovered next_inbound must match where phase 1 left off"
    );

    // ── phase 3: fresh session seeded from the recovered counters ────────────
    let journal = FixJournal::open_existing(dir.path(), 0, WINDOW).unwrap();
    let mut s2 =
        FixSession::<MockDict>::new(SessionState::new(Duration::from_secs(30)), cfg(), journal);
    let mut reader = MessageReader::<MockDict>::new();
    let mut writer = MessageWriter::<MockDict>::new();
    s2.state_mut().reset_seq_nums(rec_out, rec_in);
    assert_eq!(
        s2.state().next_outbound_seq(),
        3,
        "continuity: outbound resumes at 3"
    );
    assert_eq!(
        s2.state().next_inbound_seq(),
        3,
        "continuity: inbound resumes at 3"
    );

    // The post-restart Logon must carry the RECOVERED seqnum (34=3), proving
    // persist-before-send survived the restart — not a fresh 34=1.
    s2.encode_connect(&mut writer).unwrap();
    let logon = writer.data().to_vec();
    assert!(has_field(&logon, b"35=A"), "outbound must be a Logon");
    assert!(
        has_field(&logon, b"34=3"),
        "recovered Logon must resume at seq 3, not restart at 1"
    );
    drain_out(&mut writer);

    // ── phase 4: reconnect completes, then gap-detect works on recovered in ──
    feed(
        &mut s2,
        &mut reader,
        &mut writer,
        &peer_frame(b"A", 3, &[(108, b"30")]),
    ); // Logon ack at expected seq 3
    assert_eq!(s2.state().state(), State::Active);
    assert_eq!(
        s2.state().next_inbound_seq(),
        4,
        "inbound continuity after ack"
    );

    // A peer app at seq 6 (expected 4) is a forward gap: the engine must send a
    // ResendRequest and enter Resending — gap detection intact post-recovery.
    feed(
        &mut s2,
        &mut reader,
        &mut writer,
        &peer_frame(b"D", 6, &[(11, b"ORD-GAP")]),
    );
    assert_eq!(
        s2.state().state(),
        State::Resending,
        "gap detection must still work with recovered seqnums"
    );
}

fn tmp() -> TempDir {
    TempDir::new("stop_reopen")
}
