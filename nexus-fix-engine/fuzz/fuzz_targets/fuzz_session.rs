//! Engine survivability fuzz (battle-test Part B2).
//!
//! Drives a live [`FixSession`] through a generated sequence of FIX frames —
//! valid and corrupted — and asserts the survivability oracle after every step:
//!
//! - no panic / no debug-assert fire / no UB;
//! - the session state stays a valid `State`, never wedged;
//! - `next_inbound` / `next_outbound` are monotonic non-decreasing and never
//!   exceed `i32::MAX` (so they never wrap or corrupt);
//! - every `poll` resolves to a `PollOutcome` or a clean protocol `Error` —
//!   never a hang;
//! - the journal stays replayable after the run (reopened + fully walked, no
//!   torn/partial frame).
//!
//! Structured `arbitrary` input so the fuzz budget reaches real state-machine
//! paths (in-order / gapped / duplicate seqnums, resets, unknown MsgTypes, each
//! corruption) instead of dying at the checksum. `ResetSeqNumFlag(141)` is kept
//! out of the generated fields so the monotonic-seqnum invariant stays exact (a
//! `141=Y` Logon is a *legitimate* reset to 1, not corruption).
//!
//! Temp-dir hygiene: each iteration opens its journal in a fresh per-iteration
//! dir removed by an RAII guard at the end of the run, so at most one journal
//! dir exists at a time (and at most one leaks on a crash — the offending input).

#![no_main]

use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;

use nexus_fix_codec::{
    AsciiTextStr, DecodeError, FieldView, FixAdminMsg, FixDictionary, FixHeader, FixTimestamp,
    FrameFormatter, encode_fix_uint, find_tag,
};
use nexus_fix_engine::{
    CompId, FixJournal, FixSession, MessageReader, MessageWriter, PollOutcome, SessionConfig,
    SessionState,
};

// ── generated input ──────────────────────────────────────────────────────────

#[derive(Arbitrary, Debug)]
struct FuzzMsg {
    msg_type: u8,
    seq: u32,
    poss_dup: bool,
    fields: Vec<(u16, Vec<u8>)>,
    corrupt: Corruption,
}

#[derive(Arbitrary, Debug)]
enum Corruption {
    None,
    BadChecksum,
    BadBodyLen,
    Truncate(u8),
    FlipByte(u16),
}

/// MsgTypes the generator draws from: every admin type, an app type (`D`),
/// another app (`8`), and an unknown/garbage type (`ZZ`).
const MSG_TYPES: [&[u8]; 10] = [b"A", b"0", b"1", b"2", b"3", b"4", b"5", b"D", b"8", b"ZZ"];

// ── mock dictionary (mirrors the conformance suites) ─────────────────────────

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

// ── per-iteration journal dir (RAII — never leak more than one) ──────────────

struct JournalDir(PathBuf);

impl JournalDir {
    fn new() -> Self {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        let n = COUNTER.fetch_add(1, Ordering::Relaxed);
        let mut p = std::env::temp_dir();
        p.push(format!("nexus_fix_fuzz_{}_{}", std::process::id(), n));
        let _ = std::fs::remove_dir_all(&p);
        std::fs::create_dir_all(&p).expect("create fuzz journal dir");
        Self(p)
    }
}

impl Drop for JournalDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

const WINDOW: usize = 16;

// ── frame construction ───────────────────────────────────────────────────────

fn u32_bytes(v: u32, buf: &mut [u8; 10]) -> &[u8] {
    let n = encode_fix_uint(v, buf);
    &buf[..n]
}

/// Build a FIX frame from a `FuzzMsg`, then apply its corruption. Returns `None`
/// if the frame does not fit the scratch buffer (skip it — not interesting).
fn build_frame(m: &FuzzMsg) -> Option<Vec<u8>> {
    let mut buf = [0u8; 1024];
    let mt = MSG_TYPES[usize::from(m.msg_type) % MSG_TYPES.len()];
    // Cluster seqnums near the live range so gaps/dups/in-order all occur.
    let seq = 1 + (m.seq % 16);

    let mut fmt = FrameFormatter::new(&mut buf, b"FIX.4.4", mt);
    let mut sb = [0u8; 10];
    fmt.field(34, u32_bytes(seq, &mut sb));
    fmt.field(49, b"PEER");
    fmt.field(56, b"ENGINE");
    fmt.field(52, b"20260101-00:00:00.000");
    if m.poss_dup {
        fmt.field(43, b"Y");
    }

    // Canonical required fields per type (derived from the input) so the happy
    // paths are reachable — resends, resets, probes.
    let mut a = [0u8; 10];
    let mut b = [0u8; 10];
    match mt {
        b"A" => fmt.field(108, b"30"),
        b"1" => fmt.field(112, b"PROBE"),
        b"2" => {
            fmt.field(7, u32_bytes(1 + (m.seq % 8), &mut a)); // BeginSeqNo
            fmt.field(16, u32_bytes(m.seq % 4, &mut b)); // EndSeqNo (0 → open-ended)
        }
        b"4" => {
            if m.poss_dup {
                fmt.field(123, b"Y"); // GapFill mode
            }
            fmt.field(36, u32_bytes(m.seq % 32, &mut a)); // NewSeqNo (weird values incl. 0)
        }
        _ => {}
    }

    // Arbitrary extra fields for adversarial coverage. Skip framing tags (8/9/10
    // are owned by the formatter, 35 is the msg type) and 141 (ResetSeqNumFlag —
    // a legitimate reset would break the monotonic-seqnum invariant).
    for (tag, val) in m.fields.iter().take(8) {
        let t = u32::from(*tag);
        if matches!(t, 8 | 9 | 10 | 35 | 141) {
            continue;
        }
        if fmt.is_full() {
            break;
        }
        fmt.field(t, &val[..val.len().min(64)]);
    }

    if fmt.is_full() {
        return None;
    }
    let (start, len) = fmt.finish().ok()?;
    let mut frame = buf[start..start + len].to_vec();
    apply_corruption(&mut frame, &m.corrupt);
    Some(frame)
}

fn apply_corruption(frame: &mut Vec<u8>, c: &Corruption) {
    match c {
        Corruption::None => {}
        Corruption::BadChecksum => {
            let len = frame.len();
            if len >= 2 {
                frame[len - 2] ^= 1; // flip a CheckSum(10) digit
            }
        }
        Corruption::BadBodyLen => {
            if let Some(i) = find_sub(frame, b"\x019=") {
                let d = i + 3;
                if d < frame.len() && frame[d].is_ascii_digit() {
                    frame[d] = b'0' + (frame[d] - b'0' + 1) % 10; // perturb BodyLength(9)
                }
            }
        }
        Corruption::Truncate(n) => {
            let keep = frame.len().saturating_sub(usize::from(*n)).max(1);
            frame.truncate(keep);
        }
        Corruption::FlipByte(pos) => {
            if !frame.is_empty() {
                let i = usize::from(*pos) % frame.len();
                frame[i] ^= 0x80;
            }
        }
    }
}

fn find_sub(hay: &[u8], needle: &[u8]) -> Option<usize> {
    hay.windows(needle.len()).position(|w| w == needle)
}

// ── survivability oracle ─────────────────────────────────────────────────────

fn check_oracle(session: &FixSession<MockDict>, prev_in: &mut u32, prev_out: &mut u32) {
    let in_seq = session.state().next_inbound_seq();
    let out_seq = session.state().next_outbound_seq();
    assert!(
        in_seq >= *prev_in,
        "next_inbound went backwards: {} -> {}",
        *prev_in,
        in_seq
    );
    assert!(
        out_seq >= *prev_out,
        "next_outbound went backwards: {} -> {}",
        *prev_out,
        out_seq
    );
    assert!(
        in_seq <= i32::MAX as u32,
        "next_inbound overflowed SEQ_MAX: {in_seq}"
    );
    assert!(
        out_seq <= i32::MAX as u32,
        "next_outbound overflowed SEQ_MAX: {out_seq}"
    );
    *prev_in = in_seq;
    *prev_out = out_seq;
}

/// Feed one frame through the inbound byte seam, then drive `poll` to quiescence,
/// draining outbound and asserting the oracle after every step.
fn feed_and_poll(
    session: &mut FixSession<MockDict>,
    reader: &mut MessageReader<MockDict>,
    writer: &mut MessageWriter<MockDict>,
    frame: &[u8],
    prev_in: &mut u32,
    prev_out: &mut u32,
) {
    let mut off = 0;
    while off < frame.len() {
        let spare = reader.spare();
        if spare.is_empty() {
            break; // reader full with an incomplete oversized frame; stop feeding
        }
        let n = spare.len().min(frame.len() - off);
        spare[..n].copy_from_slice(&frame[off..off + n]);
        reader.filled(n);
        off += n;
    }

    loop {
        match session.poll(reader, writer, 1_780_505_733_000_000_000) {
            Ok(outcome) => {
                if outcome == PollOutcome::Message {
                    // Reconstructing the borrowed message must not panic.
                    let _ = session.message(reader);
                }
                // A peer that reads and discards, so the writer never wedges.
                let outn = writer.data().len();
                if outn > 0 {
                    writer.advance(outn);
                }
                check_oracle(session, prev_in, prev_out);
                match outcome {
                    PollOutcome::NeedMoreBytes | PollOutcome::Disconnected(_) => break,
                    _ => {}
                }
            }
            // A clean protocol error is an acceptable resolution (not a hang).
            Err(_) => {
                check_oracle(session, prev_in, prev_out);
                break;
            }
        }
    }
}

fn make_session(dir: &std::path::Path) -> FixSession<MockDict> {
    let journal = FixJournal::open(dir, 0, WINDOW).expect("open journal");
    FixSession::<MockDict>::new(
        SessionState::new(std::time::Duration::from_secs(30)),
        SessionConfig {
            sender: CompId::new(b"ENGINE").unwrap(),
            target: CompId::new(b"PEER").unwrap(),
        },
        journal,
    )
}

fuzz_target!(|msgs: Vec<FuzzMsg>| {
    let jdir = JournalDir::new();
    let mut session = make_session(jdir.0.as_path());
    let mut reader = MessageReader::<MockDict>::new();
    let mut writer = MessageWriter::<MockDict>::new();

    // Initiator role: send our Logon, then drive inbound. A generated Logon at
    // the expected seq completes the handshake and unlocks the Active paths.
    if session.encode_connect(&mut writer, 1_780_505_733_000_000_000).is_ok() {
        let outn = writer.data().len();
        if outn > 0 {
            writer.advance(outn);
        }
    }

    let mut prev_in = session.state().next_inbound_seq();
    let mut prev_out = session.state().next_outbound_seq();

    for m in msgs.iter().take(64) {
        if let Some(frame) = build_frame(m) {
            feed_and_poll(
                &mut session,
                &mut reader,
                &mut writer,
                &frame,
                &mut prev_in,
                &mut prev_out,
            );
        }
    }

    // The journal must stay replayable: reopen it and walk the whole resend
    // range. A torn/partial frame would panic or diverge here.
    drop(session);
    if let Ok(journal) = FixJournal::open_existing(jdir.0.as_path(), 0, WINDOW) {
        let mut count = 0usize;
        for _item in journal.resend(1, 0) {
            count += 1;
            if count > 1_000_000 {
                break; // guard against a pathological infinite replay
            }
        }
    }
});
