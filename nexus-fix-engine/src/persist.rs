use std::path::Path;

use nexus_journal::{
    AppendOffset, AppendOnlyJournal, AppendOnlyJournalConfig, AppendOnlyJournalError, FixHeader,
    ReadRange, Reader, Writer,
};

const RING_CAPACITY: usize = 8192;
const RING_MASK: u32 = RING_CAPACITY as u32 - 1;

pub struct FixJournal {
    writer: Writer<FixHeader>,
    reader: Reader<FixHeader>,
    offsets: Box<[Option<AppendOffset>; RING_CAPACITY]>,
    next_outbound: u32,
    next_inbound: u32,
}

impl FixJournal {
    pub fn open(
        path: impl AsRef<Path>,
        cfg: AppendOnlyJournalConfig,
    ) -> Result<Self, AppendOnlyJournalError> {
        let (writer, reader) = AppendOnlyJournal::<FixHeader>::open(path, cfg)?;
        Ok(Self {
            writer,
            reader,
            offsets: Box::new([None; RING_CAPACITY]),
            next_outbound: 1,
            next_inbound: 1,
        })
    }

    pub fn recover(&mut self) -> Result<(), AppendOnlyJournalError> {
        if let Some(last) = self.reader.last_seq()? {
            self.next_outbound = (last as u32).wrapping_add(1);
        }
        Ok(())
    }

    pub fn store(
        &mut self,
        seq: u32,
        timestamp: u64,
        msg: &[u8],
    ) -> Result<(), AppendOnlyJournalError> {
        let header = FixHeader {
            seq: seq as u64,
            timestamp,
        };
        let mut claim = self.writer.try_claim(header, msg.len())?;
        claim.as_mut_slice().copy_from_slice(msg);
        let at = claim.commit();
        self.offsets[seq as usize & RING_MASK as usize] = Some(at);
        self.next_outbound = seq.wrapping_add(1);
        Ok(())
    }

    pub fn resend(
        &mut self,
        begin: u32,
        end: Option<u32>,
    ) -> Result<ReadRange<'_, FixHeader>, AppendOnlyJournalError> {
        let hi = end.map_or(u64::MAX, |e| e as u64);
        let lo = begin as u64;
        if let Some(at) = self.offsets[begin as usize & RING_MASK as usize] {
            if let Some(h) = self.reader.peek_header(at)? {
                if h.seq == begin as u64 {
                    return self.reader.read_from(at, lo, hi);
                }
            }
        }
        self.reader.read_range(lo..=hi)
    }

    pub fn resend_is_aged_out(&mut self, begin: u32) -> Result<bool, AppendOnlyJournalError> {
        match self.offsets[begin as usize & RING_MASK as usize] {
            None => Ok(true),
            Some(at) => {
                let aged = match self.reader.peek_header(at)? {
                    Some(h) => h.seq != begin as u64,
                    None => true,
                };
                Ok(aged)
            }
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

#[cfg(test)]
mod tests {
    use super::*;
    use nexus_journal::MapHints;
    use std::path::{Path, PathBuf};

    fn base(name: &str) -> PathBuf {
        std::env::temp_dir().join(format!("nexus-fix-journal-{}-{}", std::process::id(), name))
    }

    fn cleanup(base: &Path) {
        for i in 0..32u64 {
            let mut p = base.as_os_str().to_owned();
            p.push(format!(".{i}"));
            let _ = std::fs::remove_file(PathBuf::from(p));
        }
    }

    fn cfg() -> AppendOnlyJournalConfig {
        AppendOnlyJournalConfig {
            segment_size: 1 << 16,
            hints: MapHints::default(),
        }
    }

    #[test]
    fn store_and_resend_roundtrip() {
        let b = base("store-resend");
        cleanup(&b);

        let mut j = FixJournal::open(&b, cfg()).unwrap();
        for seq in 1..=5u32 {
            j.store(seq, seq as u64 * 1000, &[seq as u8; 4]).unwrap();
        }

        let msgs: Vec<u32> = j
            .resend(2, Some(4))
            .unwrap()
            .map(|r| r.header().seq as u32)
            .collect();
        assert_eq!(msgs, vec![2, 3, 4]);

        cleanup(&b);
    }

    #[test]
    fn resend_open_end() {
        let b = base("resend-open");
        cleanup(&b);

        let mut j = FixJournal::open(&b, cfg()).unwrap();
        for seq in 1..=5u32 {
            j.store(seq, 0, &[seq as u8; 4]).unwrap();
        }

        let msgs: Vec<u32> = j
            .resend(3, None)
            .unwrap()
            .map(|r| r.header().seq as u32)
            .collect();
        assert_eq!(msgs, vec![3, 4, 5]);

        cleanup(&b);
    }

    #[test]
    fn recover_sets_next_outbound() {
        let b = base("recover");
        cleanup(&b);

        {
            let mut j = FixJournal::open(&b, cfg()).unwrap();
            for seq in 1..=7u32 {
                j.store(seq, 0, &[0u8; 4]).unwrap();
            }
        }

        let mut j = FixJournal::open(&b, cfg()).unwrap();
        assert_eq!(j.next_outbound(), 1);
        j.recover().unwrap();
        assert_eq!(j.next_outbound(), 8);

        cleanup(&b);
    }

    #[test]
    fn resend_is_aged_out_fresh_entry() {
        let b = base("aged-out");
        cleanup(&b);

        let mut j = FixJournal::open(&b, cfg()).unwrap();
        j.store(1, 0, &[1u8; 4]).unwrap();

        assert!(!j.resend_is_aged_out(1).unwrap());
        assert!(j.resend_is_aged_out(2).unwrap());

        cleanup(&b);
    }

    #[test]
    fn inbound_counter() {
        let b = base("inbound");
        cleanup(&b);

        let mut j = FixJournal::open(&b, cfg()).unwrap();
        assert_eq!(j.next_inbound(), 1);
        j.advance_inbound();
        j.advance_inbound();
        assert_eq!(j.next_inbound(), 3);
        j.set_next_inbound(10);
        assert_eq!(j.next_inbound(), 10);

        cleanup(&b);
    }
}
