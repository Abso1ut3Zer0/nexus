use std::path::Path;

use nexus_fix_codec::{find_tag, parse_fix_seqnum};
use nexus_journal::{Conductor, Frame, LogOffset, OpenError, RotatingJournal, WriteError};

pub enum ResendPlan<'a> {
    Replay(Frame<'a>),
    GapFill(u32),
}

pub struct FixJournal {
    journal: RotatingJournal,
    _conductor: Conductor,
    offsets: Box<[Option<LogOffset>]>,
    window: usize,
    next_outbound: u32,
    next_inbound: u32,
}

impl FixJournal {
    pub fn open(dir: impl AsRef<Path>, window: usize) -> Result<Self, OpenError> {
        assert!(window.is_power_of_two());
        let mut conductor = Conductor::open(dir)?;
        let existing = conductor.sessions_on_disk()?;
        let journal = if let Some(&id) = existing.first() {
            conductor.session().session_id(id).open()?
        } else {
            conductor.session().open()?
        };
        Ok(Self {
            journal,
            _conductor: conductor,
            offsets: vec![None; window].into_boxed_slice(),
            window,
            next_outbound: 1,
            next_inbound: 1,
        })
    }

    pub fn recover(&mut self) {
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

    pub fn store(&mut self, seq: u32, msg: &[u8]) -> Result<(), WriteError> {
        let offset = self.journal.append(msg)?;
        self.offsets[seq as usize & (self.window - 1)] = Some(offset);
        self.next_outbound = seq.wrapping_add(1);
        Ok(())
    }

    pub fn resend(&self, seq: u32) -> ResendPlan<'_> {
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
        ResendPlan::GapFill(seq)
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

    /// Caller restores from Logon's `NextExpectedMsgSeqNum` field.
    pub fn set_next_inbound(&mut self, seq: u32) {
        self.next_inbound = seq;
    }
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

    #[test]
    fn store_and_resend_roundtrip() {
        let dir = tmp_dir("store-resend");
        cleanup(&dir);

        let mut j = FixJournal::open(&dir, 64).unwrap();
        for seq in 1..=5u32 {
            j.store(seq, &fix_msg(seq)).unwrap();
        }

        match j.resend(3) {
            ResendPlan::Replay(frame) => {
                assert_eq!(frame.payload(), fix_msg(3).as_slice());
            }
            ResendPlan::GapFill(_) => panic!("expected Replay"),
        }

        cleanup(&dir);
    }

    #[test]
    fn recover_sets_next_outbound() {
        let dir = tmp_dir("recover");
        cleanup(&dir);

        {
            let mut j = FixJournal::open(&dir, 64).unwrap();
            for seq in 1..=7u32 {
                j.store(seq, &fix_msg(seq)).unwrap();
            }
        }

        let mut j = FixJournal::open(&dir, 64).unwrap();
        assert_eq!(j.next_outbound(), 1);
        j.recover();
        assert_eq!(j.next_outbound(), 8);

        cleanup(&dir);
    }

    #[test]
    fn gapfill_for_unstored_seq() {
        let dir = tmp_dir("gapfill");
        cleanup(&dir);

        let mut j = FixJournal::open(&dir, 64).unwrap();
        j.store(1, &fix_msg(1)).unwrap();

        match j.resend(2) {
            ResendPlan::GapFill(2) => {}
            _ => panic!("expected GapFill(2)"),
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
            .map(|seq| matches!(j.resend(seq), ResendPlan::Replay(_)))
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
}
