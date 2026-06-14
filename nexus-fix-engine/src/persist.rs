use std::path::Path;

use nexus_journal::{Conductor, Frame, LogOffset, OpenError, RotatingJournal, WriteError};

pub enum ResendPlan<'a> {
    Replay(Frame<'a>),
    GapFill { from: u32, to: Option<u32> },
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
            if p.len() >= 4 {
                last_seq = Some(u32::from_le_bytes(p[..4].try_into().unwrap()));
            }
        }
        if let Some(seq) = last_seq {
            self.next_outbound = seq.wrapping_add(1);
        }
    }

    pub fn store(&mut self, seq: u32, timestamp: u64, msg: &[u8]) -> Result<(), WriteError> {
        let mut payload = Vec::with_capacity(12 + msg.len());
        payload.extend_from_slice(&seq.to_le_bytes());
        payload.extend_from_slice(&timestamp.to_le_bytes());
        payload.extend_from_slice(msg);
        let offset = self.journal.append(&payload)?;
        self.offsets[seq as usize & (self.window - 1)] = Some(offset);
        self.next_outbound = seq.wrapping_add(1);
        Ok(())
    }

    pub fn resend(&self, begin: u32, end: Option<u32>) -> ResendPlan<'_> {
        let slot = begin as usize & (self.window - 1);
        if let Some(off) = self.offsets[slot] {
            if let Some(frame) = self.journal.read(off) {
                let p = frame.payload();
                if p.len() >= 4 && u32::from_le_bytes(p[..4].try_into().unwrap()) == begin {
                    return ResendPlan::Replay(frame);
                }
            }
        }
        ResendPlan::GapFill { from: begin, to: end }
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

    #[test]
    fn store_and_resend_roundtrip() {
        let dir = tmp_dir("store-resend");
        cleanup(&dir);

        let mut j = FixJournal::open(&dir, 64).unwrap();
        for seq in 1..=5u32 {
            j.store(seq, seq as u64 * 1000, &[seq as u8; 4]).unwrap();
        }

        match j.resend(3, None) {
            ResendPlan::Replay(frame) => {
                let p = frame.payload();
                assert_eq!(u32::from_le_bytes(p[..4].try_into().unwrap()), 3);
                let ts = u64::from_le_bytes(p[4..12].try_into().unwrap());
                assert_eq!(ts, 3000);
                assert_eq!(&p[12..], &[3u8; 4]);
            }
            ResendPlan::GapFill { .. } => panic!("expected Replay"),
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
                j.store(seq, 0, &[0u8; 4]).unwrap();
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
        j.store(1, 0, &[1u8; 4]).unwrap();

        match j.resend(2, Some(5)) {
            ResendPlan::GapFill { from: 2, to: Some(5) } => {}
            _ => panic!("expected GapFill"),
        }

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
