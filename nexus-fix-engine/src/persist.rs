use std::path::Path;

use nexus_fix_codec::{find_tag, parse_fix_seqnum};
use nexus_journal::{Conductor, Frame, LogOffset, OpenError, RotatingJournal, WriteError};

enum ResendPlan<'a> {
    Replay(Frame<'a>),
    GapFill,
}

pub enum ReplayItem<'a> {
    GapFill { seq: u32, new_seq: u32 },
    App(&'a [u8]),
}

pub struct FixJournal {
    journal: RotatingJournal,
    _conductor: Conductor,
    offsets: Box<[Option<LogOffset>]>,
    window: usize,
    next_outbound: u32,
    next_inbound: u32,
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
                    let p = frame.payload();
                    let msg_type = find_tag(p, 0, 35).map_or(b"" as &[u8], |s| s.slice(p));
                    if is_admin_type(msg_type) {
                        true
                    } else {
                        let app = ReplayItem::App(p);
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
    /// Open (or recover) the journal for a single session under `dir`.
    ///
    /// `window` is the resend horizon in messages (must be a power of two): the
    /// last `window` sequence numbers are replayable, older ones are gap-filled.
    ///
    /// One session per journal: if a session already exists under `dir`, the
    /// first one is reopened; otherwise a new session is created.
    pub fn open(dir: impl AsRef<Path>, window: usize) -> Result<Self, OpenError> {
        assert!(window.is_power_of_two());
        let mut conductor = Conductor::open(dir)?;
        let existing = conductor.sessions_on_disk()?;
        let journal = if let Some(&id) = existing.first() {
            conductor.session().session_id(id).open()?
        } else {
            conductor.session().open()?
        };
        let mut this = Self {
            journal,
            _conductor: conductor,
            offsets: vec![None; window].into_boxed_slice(),
            window,
            next_outbound: 1,
            next_inbound: 1,
        };
        this.recover_from_journal();
        Ok(this)
    }

    fn recover_from_journal(&mut self) {
        let mut pos = self.journal.read_start();
        let mut last_seq: Option<u32> = None;
        while let Some(frame) = self.journal.read_next(&mut pos) {
            let p = frame.payload();
            if let Some(span) = find_tag(p, 0, 34)
                && let Ok(seq) = parse_fix_seqnum(span.slice(p))
            {
                last_seq = Some(seq as u32);
            }
        }
        if let Some(seq) = last_seq {
            self.next_outbound = seq.wrapping_add(1);
        }
    }

    /// Archive an outbound message after it has been sent.
    ///
    /// `msg` is the already-formatted wire message; `seq` must equal its
    /// `MsgSeqNum` (tag 34). The send path satisfies this by construction — `seq`
    /// is passed in only to index the resend ring without re-parsing on the hot
    /// path; the cold paths ([`resend`](Self::resend), [`recover`](Self::recover))
    /// read the seqnum back out of the message via tag 34.
    pub fn store(&mut self, seq: u32, msg: &[u8]) -> Result<(), WriteError> {
        let offset = self.journal.append(msg)?;
        self.offsets[seq as usize & (self.window - 1)] = Some(offset);
        self.next_outbound = seq.wrapping_add(1);
        Ok(())
    }

    fn resend_one(&self, seq: u32) -> ResendPlan<'_> {
        let slot = seq as usize & (self.window - 1);
        if let Some(off) = self.offsets[slot]
            && let Some(frame) = self.journal.read(off)
        {
            let p = frame.payload();
            if let Some(span) = find_tag(p, 0, 34)
                && parse_fix_seqnum(span.slice(p)).ok().map(|s| s as u32) == Some(seq)
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
        self.next_inbound = self.next_inbound.wrapping_add(1);
    }

    pub fn set_next_inbound(&mut self, seq: u32) {
        self.next_inbound = seq;
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
    fn store_and_resend_roundtrip() {
        let dir = tmp_dir("store-resend");
        cleanup(&dir);

        let mut j = FixJournal::open(&dir, 64).unwrap();
        for seq in 1..=5u32 {
            j.store(seq, &fix_msg(seq)).unwrap();
        }

        match j.resend_one(3) {
            ResendPlan::Replay(frame) => {
                assert_eq!(frame.payload(), fix_msg(3).as_slice());
            }
            ResendPlan::GapFill => panic!("expected Replay"),
        }

        cleanup(&dir);
    }

    #[test]
    fn open_recovers_next_outbound() {
        let dir = tmp_dir("recover");
        cleanup(&dir);

        {
            let mut j = FixJournal::open(&dir, 64).unwrap();
            for seq in 1..=7u32 {
                j.store(seq, &fix_msg(seq)).unwrap();
            }
        }

        let j = FixJournal::open(&dir, 64).unwrap();
        assert_eq!(j.next_outbound(), 8);

        cleanup(&dir);
    }

    #[test]
    fn gapfill_for_unstored_seq() {
        let dir = tmp_dir("gapfill");
        cleanup(&dir);

        let mut j = FixJournal::open(&dir, 64).unwrap();
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

        let mut j = FixJournal::open(&dir, 64).unwrap();
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

        let mut j = FixJournal::open(&dir, 64).unwrap();
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

        let mut j = FixJournal::open(&dir, 64).unwrap();
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

        let mut j = FixJournal::open(&dir, 64).unwrap();
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

        let mut j = FixJournal::open(&dir, 4).unwrap();
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

        let mut j = FixJournal::open(&dir, 64).unwrap();
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

        let mut j = FixJournal::open(&dir, 64).unwrap();
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

        let mut j = FixJournal::open(&dir, 64).unwrap();
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

        let mut j = FixJournal::open(&dir, 64).unwrap();
        for seq in 1..=3u32 {
            j.store(seq, &fix_msg(seq)).unwrap();
        }

        let items = collect_range(&j, 1, 0);
        assert_eq!(items.len(), 3);
        assert!(items.iter().all(|i| matches!(i, ReplayItem::App(_))));

        cleanup(&dir);
    }
}
