//! Both-sides FIX session archive backing resend recovery and audit visibility.
//!
//! [`FixJournal`] wraps **two** [`RotatingJournal`]s — one outbound, one inbound
//! — under a shared [`Conductor`]. Direction is implicit in which journal a
//! message lands in; there is no per-frame direction flag. Each stored frame's
//! payload is `[ts:8][wire msg]`: an 8-byte little-endian UNIX-nanoseconds
//! timestamp prepended by [`FixJournal`] via
//! [`RotatingJournal::append_prefixed`], followed by the untouched FIX wire
//! message. The journal frame format itself is unchanged — the FIX layer owns
//! the timestamp.
//!
//! # Roles
//!
//! - **Resend recovery** reads the *outbound* journal only, via an in-memory
//!   offset table indexed by `MsgSeqNum` (tag 34). The table is repopulated on
//!   recovery by a bounded scan of the outbound hot window.
//! - **Visibility / audit** is served by both journals with `archive(true)`:
//!   evicted segments are preserved rather than zeroed, so the full history is
//!   readable beyond the active window.
//!
//! # Sequence-number recovery
//!
//! `next_outbound` lives in the outbound journal's manifest meta-slot,
//! `next_inbound` in the inbound journal's. Each is written in place on every
//! update ([`store`](FixJournal::store) / [`set_next_inbound`](FixJournal::set_next_inbound))
//! and recovered in O(1) — no scan, robust against window aging (the counter
//! survives even after the messages it counted have rotated out).
//!
//! # Conductor ownership
//!
//! [`open`](FixJournal::open) / [`open_existing`](FixJournal::open_existing)
//! own their conductor (single-session convenience). [`open_in`](FixJournal::open_in)
//! borrows a caller-owned [`Conductor`] so many sessions share one background
//! cleanup thread. The conductor must outlive every [`FixJournal`] opened
//! through it — a drop-order rule the owner controls, since the journals hold
//! owned clones of the conductor's producer and Arcs rather than a borrow.

use std::path::Path;

use nexus_fix_codec::{find_tag, parse_fix_seqnum};
use nexus_journal::{
    Conductor, ConductorBuilder, Frame, LogOffset, OpenError, OpenMode, RotatingJournal, WriteError,
};

/// Width of the per-frame timestamp prefix: an 8-byte LE UNIX-nanos `u64`.
const TS_LEN: usize = 8;

fn unix_nanos_now() -> u64 {
    use std::time::{SystemTime, UNIX_EPOCH};
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_nanos() as u64)
        .unwrap_or(0)
}

enum ResendPlan<'a> {
    Replay(Frame<'a>),
    GapFill,
}

pub enum ReplayItem<'a> {
    GapFill { seq: u32, new_seq: u32 },
    App(&'a [u8]),
}

/// Two-journal (outbound + inbound) FIX session archive.
///
/// See the [module docs](self) for the storage model, timestamp prefix, and
/// recovery guarantees.
pub struct FixJournal {
    outbound: RotatingJournal,
    inbound: RotatingJournal,
    offsets: Box<[Option<LogOffset>]>,
    window: usize,
    next_outbound: u32,
    next_inbound: u32,
    /// `Some` when this journal owns its conductor (via [`open`](Self::open) /
    /// [`open_existing`](Self::open_existing)); `None` when the conductor is
    /// caller-owned (via [`open_in`](Self::open_in)). Held only to drop after
    /// the journals — never touched directly.
    ///
    /// Declared **last** so it drops after `outbound`/`inbound`: a
    /// [`RotatingJournal`]'s `Drop` may spin waiting for the conductor thread to
    /// finish an in-flight segment swap, so the [`Conductor`] (whose own `Drop`
    /// joins that thread) must outlive the journals. Rust drops struct fields in
    /// declaration order, so field order here is load-bearing.
    _conductor: Option<Conductor>,
}

struct ResendIter<'a> {
    journal: &'a FixJournal,
    seq: u32,
    high: u32,
    gap_start: Option<u32>,
    deferred: Option<ReplayItem<'a>>,
    done: bool,
}

impl<'a> Iterator for ResendIter<'a> {
    type Item = ReplayItem<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(item) = self.deferred.take() {
            return Some(item);
        }
        loop {
            if self.done {
                return None;
            }
            if self.seq > self.high {
                self.done = true;
                return self.gap_start.take().map(|gs| ReplayItem::GapFill {
                    seq: gs,
                    new_seq: self.high.wrapping_add(1),
                });
            }
            let seq = self.seq;
            self.seq = self.seq.saturating_add(1);
            let is_gap = match self.journal.resend_one(seq) {
                ResendPlan::GapFill => true,
                ResendPlan::Replay(frame) => {
                    // Payload is `[ts:8][msg]`; replay the wire message only.
                    let msg = &frame.payload()[TS_LEN..];
                    let msg_type = find_tag(msg, 0, 35).map_or(b"" as &[u8], |s| s.slice(msg));
                    if is_admin_type(msg_type) {
                        true
                    } else {
                        let app = ReplayItem::App(msg);
                        if let Some(gs) = self.gap_start.take() {
                            self.deferred = Some(app);
                            return Some(ReplayItem::GapFill {
                                seq: gs,
                                new_seq: seq,
                            });
                        }
                        return Some(app);
                    }
                }
            };
            if is_gap && self.gap_start.is_none() {
                self.gap_start = Some(seq);
            }
        }
    }
}

impl FixJournal {
    /// Open both journals for `session_id` through a caller-owned `conductor`.
    ///
    /// This is the primary constructor: many sessions share one conductor (and
    /// thus one background cleanup thread). The outbound journal uses conductor
    /// session id `session_id * 2`, the inbound `session_id * 2 + 1`, so a FIX
    /// `session_id` maps to a disjoint pair of conductor sessions.
    ///
    /// `window` is the resend horizon in messages (must be a power of two): the
    /// last `window` sequence numbers are replayable, older ones are gap-filled.
    ///
    /// The `conductor` must outlive the returned journal (see the [module
    /// docs](self)). To get archival history for audit, build the conductor with
    /// [`ConductorBuilder::archive(true)`](ConductorBuilder::archive) — the
    /// convenience [`open`](Self::open) does this for you.
    ///
    /// # Panics
    ///
    /// Panics if `window` is not a power of two, or if `session_id >= 2^31`
    /// (the id is doubled to derive the two conductor session ids).
    pub fn open_in(
        conductor: &mut Conductor,
        session_id: u32,
        window: usize,
        mode: OpenMode,
    ) -> Result<Self, OpenError> {
        assert!(window.is_power_of_two(), "window must be a power of two");
        assert!(session_id < 1 << 31, "session_id must be < 2^31");
        let outbound = conductor.session().session_id(session_id * 2).open(mode)?;
        let inbound = conductor
            .session()
            .session_id(session_id * 2 + 1)
            .open(mode)?;
        let mut this = Self {
            _conductor: None,
            outbound,
            inbound,
            offsets: vec![None; window].into_boxed_slice(),
            window,
            next_outbound: 1,
            next_inbound: 1,
        };
        this.recover();
        Ok(this)
    }

    /// Open (or create) the journal for `session_id` under `dir`, owning a
    /// private conductor with archival enabled.
    ///
    /// Convenience for single-session callers. If a manifest for `session_id`
    /// already exists under `dir`, the session is recovered (counters from the
    /// meta-slots, resend ring from the outbound hot window); otherwise a fresh
    /// session is created. Multiple sessions can coexist under the same `dir`
    /// with distinct `session_id` values, each with independent state.
    ///
    /// `window` is the resend horizon in messages (must be a power of two).
    ///
    /// Multi-session applications should instead share one [`Conductor`] via
    /// [`open_in`](Self::open_in).
    pub fn open(dir: impl AsRef<Path>, session_id: u32, window: usize) -> Result<Self, OpenError> {
        let mut conductor = ConductorBuilder::new(dir).archive(true).open()?;
        let mut this = Self::open_in(&mut conductor, session_id, window, OpenMode::OpenOrCreate)?;
        this._conductor = Some(conductor);
        Ok(this)
    }

    /// Open an existing session journal, returning [`OpenError::SessionNotFound`]
    /// when no manifest exists for `session_id`.
    ///
    /// Unlike [`open`](Self::open) this never creates a new session. Use for
    /// reconnect callers that must recover state — a wrong `session_id` is an
    /// error rather than a silent fresh start. Like [`open`](Self::open), the
    /// owned conductor has archival enabled.
    pub fn open_existing(
        dir: impl AsRef<Path>,
        session_id: u32,
        window: usize,
    ) -> Result<Self, OpenError> {
        assert!(window.is_power_of_two(), "window must be a power of two");
        assert!(session_id < 1 << 31, "session_id must be < 2^31");
        // No filesystem side-effects when the journal root does not exist: a
        // typo'd path must not materialize an empty conductor directory.
        if !dir.as_ref().exists() {
            return Err(OpenError::SessionNotFound { session_id });
        }
        let mut conductor = ConductorBuilder::new(dir).archive(true).open()?;
        let mut this = Self::open_in(&mut conductor, session_id, window, OpenMode::OpenExisting)?;
        this._conductor = Some(conductor);
        Ok(this)
    }

    /// Recover counters (O(1) from the manifest meta-slots) and rebuild the
    /// resend ring by scanning the bounded outbound hot window.
    fn recover(&mut self) {
        // Counters: the meta-slot stores `next_*` directly; 0 means fresh → 1.
        self.next_outbound = match self.outbound.meta() as u32 {
            0 => 1,
            n => n,
        };
        self.next_inbound = match self.inbound.meta() as u32 {
            0 => 1,
            n => n,
        };
        // Resend ring: repopulate `offsets` from the outbound hot window. Bounded
        // by the readable segments (O(window) at most), so this survives across a
        // restart — the whole point of persisting the offset table's inputs.
        let mut pos = self.outbound.read_start();
        while let Some(frame) = self.outbound.read_next(&mut pos) {
            let p = frame.payload();
            if p.len() < TS_LEN {
                continue;
            }
            let msg = &p[TS_LEN..];
            if let Some(span) = find_tag(msg, 0, 34)
                && let Ok(seq) = parse_fix_seqnum(span.slice(msg))
            {
                let lo = self.outbound.log_offset_at(frame.offset());
                self.offsets[seq as usize & (self.window - 1)] = Some(lo);
            }
        }
    }

    /// Archive an outbound message after it has been sent.
    ///
    /// `msg` is the already-formatted wire message; `seq` must equal its
    /// `MsgSeqNum` (tag 34). The send path satisfies this by construction — `seq`
    /// is passed in only to index the resend ring without re-parsing on the hot
    /// path; the cold paths ([`resend`](Self::resend), recovery on open)
    /// read the seqnum back out of the message via tag 34.
    ///
    /// The stored payload is `[ts:8][msg]` (an 8-byte LE UNIX-nanos timestamp
    /// prepended in-frame). The outbound manifest's meta-slot is updated to
    /// `seq + 1` so `next_outbound` recovers in O(1).
    pub fn store(&mut self, seq: u32, msg: &[u8]) -> Result<(), WriteError> {
        let ts = unix_nanos_now().to_le_bytes();
        let off = self.outbound.append_prefixed(&ts, msg)?;
        self.offsets[seq as usize & (self.window - 1)] = Some(off);
        self.next_outbound = seq.wrapping_add(1);
        self.outbound.set_meta(self.next_outbound as u64);
        Ok(())
    }

    /// Archive an inbound message for visibility / audit.
    ///
    /// Purely archival: the inbound journal is never read by the resend path.
    /// The inbound *counter* is maintained separately via
    /// [`set_next_inbound`](Self::set_next_inbound). Stored payload is
    /// `[ts:8][msg]`, matching the outbound side.
    pub fn store_inbound(&mut self, msg: &[u8]) -> Result<(), WriteError> {
        let ts = unix_nanos_now().to_le_bytes();
        self.inbound.append_prefixed(&ts, msg)?;
        Ok(())
    }

    fn resend_one(&self, seq: u32) -> ResendPlan<'_> {
        let slot = seq as usize & (self.window - 1);
        if let Some(off) = self.offsets[slot]
            && let Some(frame) = self.outbound.read(off)
            && frame.payload().len() >= TS_LEN
        {
            let msg = &frame.payload()[TS_LEN..];
            if let Some(span) = find_tag(msg, 0, 34)
                && parse_fix_seqnum(span.slice(msg)).ok().map(|s| s as u32) == Some(seq)
            {
                return ResendPlan::Replay(frame);
            }
        }
        ResendPlan::GapFill
    }

    pub fn resend(&'_ self, begin: u32, end: u32) -> impl Iterator<Item = ReplayItem<'_>> + '_ {
        let high = if end == 0 {
            self.next_outbound.saturating_sub(1)
        } else {
            end
        };
        ResendIter {
            journal: self,
            seq: begin,
            high,
            gap_start: None,
            deferred: None,
            done: begin > high,
        }
    }

    pub fn next_outbound(&self) -> u32 {
        self.next_outbound
    }

    pub fn next_inbound(&self) -> u32 {
        self.next_inbound
    }

    pub fn advance_inbound(&mut self) {
        self.set_next_inbound(self.next_inbound.wrapping_add(1));
    }

    /// Set the expected next inbound sequence number, persisting it to the
    /// inbound journal's meta-slot for O(1) recovery.
    ///
    /// A no-op when `seq` is unchanged, so a hot-path caller can invoke it every
    /// receive without a redundant manifest write.
    pub fn set_next_inbound(&mut self, seq: u32) {
        if seq == self.next_inbound {
            return;
        }
        self.next_inbound = seq;
        self.inbound.set_meta(seq as u64);
    }
}

fn is_admin_type(msg_type: &[u8]) -> bool {
    matches!(msg_type, b"A" | b"5" | b"0" | b"1" | b"2" | b"3" | b"4")
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn tmp_dir(name: &str) -> PathBuf {
        std::env::temp_dir().join(format!("nexus-fix-journal-{}-{}", std::process::id(), name))
    }

    fn cleanup(dir: &PathBuf) {
        let _ = std::fs::remove_dir_all(dir);
    }

    fn fix_msg(seq: u32) -> Vec<u8> {
        format!("8=FIX.4.2\x0134={seq}\x0135=D\x0110=000\x01").into_bytes()
    }

    fn fix_admin(seq: u32, msg_type: &str) -> Vec<u8> {
        format!("8=FIX.4.2\x0134={seq}\x0135={msg_type}\x0110=000\x01").into_bytes()
    }

    fn fix_msg_with_time(seq: u32, time: &str) -> Vec<u8> {
        format!("8=FIX.4.2\x0134={seq}\x0135=D\x0152={time}\x0110=000\x01").into_bytes()
    }

    fn collect_range(j: &FixJournal, begin: u32, end: u32) -> Vec<ReplayItem<'_>> {
        j.resend(begin, end).collect()
    }

    #[test]
    fn open_existing_missing_returns_not_found() {
        let dir = tmp_dir("oe-missing");
        cleanup(&dir);
        let result = FixJournal::open_existing(&dir, 0, 64);
        assert!(
            matches!(result, Err(OpenError::SessionNotFound { .. })),
            "expected SessionNotFound"
        );
        cleanup(&dir);
    }

    #[test]
    fn open_existing_wrong_id_returns_not_found() {
        let dir = tmp_dir("oe-wrongid");
        cleanup(&dir);
        {
            let mut j = FixJournal::open(&dir, 0, 64).unwrap();
            j.store(1, &fix_msg(1)).unwrap();
        }
        let result = FixJournal::open_existing(&dir, 1, 64);
        assert!(
            matches!(result, Err(OpenError::SessionNotFound { .. })),
            "expected SessionNotFound for wrong id"
        );
        cleanup(&dir);
    }

    #[test]
    fn open_existing_recovers_correct_session() {
        let dir = tmp_dir("oe-recover");
        cleanup(&dir);
        {
            let mut j = FixJournal::open(&dir, 0, 64).unwrap();
            for seq in 1..=3u32 {
                j.store(seq, &fix_msg(seq)).unwrap();
            }
        }
        let j = FixJournal::open_existing(&dir, 0, 64).unwrap();
        assert_eq!(j.next_outbound(), 4);
        cleanup(&dir);
    }

    #[test]
    fn store_and_resend_roundtrip() {
        let dir = tmp_dir("store-resend");
        cleanup(&dir);

        let mut j = FixJournal::open(&dir, 0, 64).unwrap();
        for seq in 1..=5u32 {
            j.store(seq, &fix_msg(seq)).unwrap();
        }

        // resend strips the 8-byte ts prefix and returns the original wire bytes.
        let items = collect_range(&j, 3, 3);
        assert_eq!(items.len(), 1);
        let ReplayItem::App(bytes) = items[0] else {
            panic!("expected App");
        };
        assert_eq!(bytes, fix_msg(3).as_slice());

        cleanup(&dir);
    }

    #[test]
    fn open_recovers_next_outbound() {
        let dir = tmp_dir("recover");
        cleanup(&dir);

        {
            let mut j = FixJournal::open(&dir, 0, 64).unwrap();
            for seq in 1..=7u32 {
                j.store(seq, &fix_msg(seq)).unwrap();
            }
        }

        let j = FixJournal::open(&dir, 0, 64).unwrap();
        assert_eq!(j.next_outbound(), 8);

        cleanup(&dir);
    }

    #[test]
    fn open_recovers_next_inbound() {
        let dir = tmp_dir("recover-inbound");
        cleanup(&dir);

        {
            let mut j = FixJournal::open(&dir, 0, 64).unwrap();
            j.store(1, &fix_msg(1)).unwrap();
            j.advance_inbound();
            j.advance_inbound();
            j.set_next_inbound(42);
        }

        let j = FixJournal::open(&dir, 0, 64).unwrap();
        assert_eq!(j.next_inbound(), 42);
        assert_eq!(j.next_outbound(), 2);

        cleanup(&dir);
    }

    #[test]
    fn cross_restart_resend_replays() {
        // The point of rebuilding the resend ring on recovery: after a restart,
        // in-window seqnums replay the ACTUAL stored bytes, not a gap-fill.
        let dir = tmp_dir("cross-restart");
        cleanup(&dir);

        let msgs: Vec<Vec<u8>> = (1..=5u32).map(fix_msg).collect();
        {
            let mut j = FixJournal::open(&dir, 0, 64).unwrap();
            for (i, m) in msgs.iter().enumerate() {
                j.store(i as u32 + 1, m).unwrap();
            }
        }

        // Reopen: offsets table is empty until `recover()` rebuilds it from the
        // outbound hot window.
        let j = FixJournal::open_existing(&dir, 0, 64).unwrap();
        assert_eq!(j.next_outbound(), 6);

        let items = collect_range(&j, 1, 5);
        assert_eq!(items.len(), 5, "all five should replay, none gap-filled");
        for (i, item) in items.iter().enumerate() {
            let ReplayItem::App(bytes) = item else {
                panic!("seq {} gap-filled after restart", i + 1);
            };
            assert_eq!(*bytes, msgs[i].as_slice(), "seq {} bytes mismatch", i + 1);
        }

        cleanup(&dir);
    }

    #[test]
    fn store_inbound_is_archival_only() {
        // store_inbound must not touch the outbound resend path or counters.
        let dir = tmp_dir("store-inbound");
        cleanup(&dir);

        let mut j = FixJournal::open(&dir, 0, 64).unwrap();
        j.store(1, &fix_msg(1)).unwrap();
        j.store_inbound(&fix_msg(9)).unwrap();
        j.store_inbound(&fix_msg(10)).unwrap();

        // Outbound state untouched by inbound writes.
        assert_eq!(j.next_outbound(), 2);
        let items = collect_range(&j, 1, 1);
        assert_eq!(items.len(), 1);
        assert!(matches!(items[0], ReplayItem::App(_)));

        cleanup(&dir);
    }

    #[test]
    fn gapfill_for_unstored_seq() {
        let dir = tmp_dir("gapfill");
        cleanup(&dir);

        let mut j = FixJournal::open(&dir, 0, 64).unwrap();
        j.store(1, &fix_msg(1)).unwrap();

        match j.resend_one(2) {
            ResendPlan::GapFill => {}
            ResendPlan::Replay(_) => panic!("expected GapFill"),
        }

        cleanup(&dir);
    }

    #[test]
    fn straddle_mixed_replay_and_gapfill() {
        let dir = tmp_dir("straddle");
        cleanup(&dir);

        let mut j = FixJournal::open(&dir, 0, 64).unwrap();
        for seq in [1u32, 3, 5] {
            j.store(seq, &fix_msg(seq)).unwrap();
        }

        let results: Vec<bool> = (1u32..=5)
            .map(|seq| matches!(j.resend_one(seq), ResendPlan::Replay(_)))
            .collect();
        assert_eq!(results, vec![true, false, true, false, true]);

        cleanup(&dir);
    }

    #[test]
    fn inbound_counter() {
        let dir = tmp_dir("inbound");
        cleanup(&dir);

        let mut j = FixJournal::open(&dir, 0, 64).unwrap();
        assert_eq!(j.next_inbound(), 1);
        j.advance_inbound();
        j.advance_inbound();
        assert_eq!(j.next_inbound(), 3);
        j.set_next_inbound(10);
        assert_eq!(j.next_inbound(), 10);

        cleanup(&dir);
    }

    #[test]
    fn resend_range_admin_skip() {
        let dir = tmp_dir("rr-admin-skip");
        cleanup(&dir);

        let mut j = FixJournal::open(&dir, 0, 64).unwrap();
        j.store(1, &fix_admin(1, "A")).unwrap();
        j.store(2, &fix_admin(2, "0")).unwrap();
        j.store(3, &fix_admin(3, "5")).unwrap();

        let items = collect_range(&j, 1, 3);
        assert_eq!(items.len(), 1);
        assert!(matches!(
            items[0],
            ReplayItem::GapFill { seq: 1, new_seq: 4 }
        ));

        cleanup(&dir);
    }

    #[test]
    fn resend_range_interior_holes() {
        let dir = tmp_dir("rr-holes");
        cleanup(&dir);

        let mut j = FixJournal::open(&dir, 0, 64).unwrap();
        for seq in [1u32, 3, 5] {
            j.store(seq, &fix_msg(seq)).unwrap();
        }

        let items = collect_range(&j, 1, 5);
        assert_eq!(items.len(), 5);
        assert!(matches!(items[0], ReplayItem::App(_)));
        assert!(matches!(
            items[1],
            ReplayItem::GapFill { seq: 2, new_seq: 3 }
        ));
        assert!(matches!(items[2], ReplayItem::App(_)));
        assert!(matches!(
            items[3],
            ReplayItem::GapFill { seq: 4, new_seq: 5 }
        ));
        assert!(matches!(items[4], ReplayItem::App(_)));

        cleanup(&dir);
    }

    #[test]
    fn resend_range_straddle_window() {
        let dir = tmp_dir("rr-straddle");
        cleanup(&dir);

        let mut j = FixJournal::open(&dir, 0, 4).unwrap();
        for seq in 1..=8u32 {
            j.store(seq, &fix_msg(seq)).unwrap();
        }

        let items = collect_range(&j, 1, 8);
        assert_eq!(items.len(), 5);
        assert!(matches!(
            items[0],
            ReplayItem::GapFill { seq: 1, new_seq: 5 }
        ));
        assert!(matches!(items[1], ReplayItem::App(_)));
        assert!(matches!(items[2], ReplayItem::App(_)));
        assert!(matches!(items[3], ReplayItem::App(_)));
        assert!(matches!(items[4], ReplayItem::App(_)));

        cleanup(&dir);
    }

    #[test]
    fn resend_range_yields_original_bytes() {
        let dir = tmp_dir("rr-original");
        cleanup(&dir);

        let mut j = FixJournal::open(&dir, 0, 64).unwrap();
        let msg = fix_msg_with_time(1, "20240101-12:00:00");
        j.store(1, &msg).unwrap();

        let items = collect_range(&j, 1, 1);
        assert_eq!(items.len(), 1);
        let ReplayItem::App(bytes) = items[0] else {
            panic!("expected App");
        };
        assert_eq!(bytes, msg.as_slice());

        cleanup(&dir);
    }

    #[test]
    fn resend_range_coalesced_gapfill() {
        let dir = tmp_dir("rr-coalesced");
        cleanup(&dir);

        let mut j = FixJournal::open(&dir, 0, 64).unwrap();
        j.store(1, &fix_msg(1)).unwrap();
        j.store(5, &fix_msg(5)).unwrap();

        let items = collect_range(&j, 1, 5);
        assert_eq!(items.len(), 3);
        assert!(matches!(items[0], ReplayItem::App(_)));
        assert!(matches!(
            items[1],
            ReplayItem::GapFill { seq: 2, new_seq: 5 }
        ));
        assert!(matches!(items[2], ReplayItem::App(_)));

        cleanup(&dir);
    }

    #[test]
    fn resend_range_all_gapfill() {
        let dir = tmp_dir("rr-allgap");
        cleanup(&dir);

        let mut j = FixJournal::open(&dir, 0, 64).unwrap();
        j.store(1, &fix_admin(1, "A")).unwrap();
        j.store(2, &fix_admin(2, "1")).unwrap();
        j.store(3, &fix_admin(3, "2")).unwrap();

        let items = collect_range(&j, 1, 3);
        assert_eq!(items.len(), 1);
        assert!(matches!(
            items[0],
            ReplayItem::GapFill { seq: 1, new_seq: 4 }
        ));

        cleanup(&dir);
    }

    #[test]
    fn resend_range_end_zero_means_all() {
        let dir = tmp_dir("rr-endzero");
        cleanup(&dir);

        let mut j = FixJournal::open(&dir, 0, 64).unwrap();
        for seq in 1..=3u32 {
            j.store(seq, &fix_msg(seq)).unwrap();
        }

        let items = collect_range(&j, 1, 0);
        assert_eq!(items.len(), 3);
        assert!(items.iter().all(|i| matches!(i, ReplayItem::App(_))));

        cleanup(&dir);
    }

    #[test]
    fn two_sessions_in_one_directory_are_independent() {
        let dir = tmp_dir("two-sessions");
        cleanup(&dir);

        {
            let mut conductor = ConductorBuilder::new(&dir).archive(true).open().unwrap();
            let mut j0 =
                FixJournal::open_in(&mut conductor, 0, 64, OpenMode::OpenOrCreate).unwrap();
            let mut j1 =
                FixJournal::open_in(&mut conductor, 1, 64, OpenMode::OpenOrCreate).unwrap();

            for seq in 1..=3u32 {
                j0.store(seq, &fix_msg(seq)).unwrap();
            }
            for seq in 1..=5u32 {
                j1.store(seq, &fix_msg(seq)).unwrap();
            }

            assert_eq!(j0.next_outbound(), 4);
            assert_eq!(j1.next_outbound(), 6);
        }

        // Reopen both through a fresh shared conductor and verify each recovers
        // its own next_outbound independently.
        let mut conductor = ConductorBuilder::new(&dir).archive(true).open().unwrap();
        let j0 = FixJournal::open_in(&mut conductor, 0, 64, OpenMode::OpenExisting).unwrap();
        let j1 = FixJournal::open_in(&mut conductor, 1, 64, OpenMode::OpenExisting).unwrap();
        assert_eq!(j0.next_outbound(), 4);
        assert_eq!(j1.next_outbound(), 6);

        cleanup(&dir);
    }

    #[test]
    fn open_in_shares_one_conductor() {
        // Two FIX sessions under one conductor use disjoint conductor session
        // ids (2n / 2n+1) and stay independent.
        let dir = tmp_dir("open-in-shared");
        cleanup(&dir);

        let mut conductor = ConductorBuilder::new(&dir).archive(true).open().unwrap();
        let mut a = FixJournal::open_in(&mut conductor, 0, 64, OpenMode::OpenOrCreate).unwrap();
        let mut b = FixJournal::open_in(&mut conductor, 7, 64, OpenMode::OpenOrCreate).unwrap();

        a.store(1, &fix_msg(1)).unwrap();
        a.store(2, &fix_msg(2)).unwrap();
        b.store(1, &fix_msg(1)).unwrap();

        assert_eq!(a.next_outbound(), 3);
        assert_eq!(b.next_outbound(), 2);

        cleanup(&dir);
    }
}
