use std::path::{Path, PathBuf};

use nexus_platform::MapHints;

use super::{
    AppendOffset, AppendOnlyJournal, AppendOnlyJournalConfig, AppendOnlyJournalError, FixHeader,
};

fn base_path(name: &str) -> PathBuf {
    std::env::temp_dir().join(format!("nexus-journal-{}-{}", std::process::id(), name))
}

fn cleanup(base: &Path) {
    for i in 0..32u64 {
        let mut p = base.as_os_str().to_owned();
        p.push(format!(".{i}"));
        let _ = std::fs::remove_file(PathBuf::from(p));
    }
}

fn fix(seq: u64) -> FixHeader {
    FixHeader {
        seq,
        timestamp: seq * 1000,
    }
}

fn cfg(segment_size: usize) -> AppendOnlyJournalConfig {
    AppendOnlyJournalConfig {
        segment_size,
        hints: MapHints::default(),
    }
}

#[test]
fn roundtrip_fix() {
    let base = base_path("roundtrip");
    cleanup(&base);

    let (mut w, mut r) = AppendOnlyJournal::<FixHeader>::open(&base, cfg(1 << 16)).unwrap();
    for seq in 1..=3u64 {
        let payload = vec![seq as u8; seq as usize * 4];
        let mut claim = w.try_claim(fix(seq), payload.len()).unwrap();
        claim.as_mut_slice().copy_from_slice(&payload);
        claim.commit();
    }

    for seq in 1..=3u64 {
        let rec = r.next_record().unwrap().unwrap();
        assert_eq!(rec.header(), fix(seq));
        assert_eq!(rec.payload(), &vec![seq as u8; seq as usize * 4][..]);
    }
    assert!(r.next_record().unwrap().is_none());

    drop((w, r));
    cleanup(&base);
}

#[test]
fn unit_header_zero_overhead() {
    let base = base_path("unit");
    cleanup(&base);

    let (mut w, mut r) = AppendOnlyJournal::<()>::open(&base, cfg(1 << 16)).unwrap();
    let mut claim = w.try_claim((), 5).unwrap();
    claim.as_mut_slice().copy_from_slice(b"hello");
    claim.commit();

    let rec = r.next_record().unwrap().unwrap();
    assert_eq!(rec.payload(), b"hello");
    assert!(r.next_record().unwrap().is_none());

    drop((w, r));
    cleanup(&base);
}

#[test]
fn empty_unit_record_rejected() {
    let base = base_path("empty");
    cleanup(&base);

    let (mut w, _r) = AppendOnlyJournal::<()>::open(&base, cfg(1 << 16)).unwrap();
    assert!(matches!(
        w.try_claim((), 0),
        Err(AppendOnlyJournalError::EmptyRecord)
    ));

    drop(w);
    cleanup(&base);
}

#[test]
fn record_too_large_rejected() {
    let base = base_path("toolarge");
    cleanup(&base);

    let (mut w, _r) = AppendOnlyJournal::<FixHeader>::open(&base, cfg(256)).unwrap();
    assert!(matches!(
        w.try_claim(fix(1), 4096),
        Err(AppendOnlyJournalError::RecordTooLarge { .. })
    ));

    drop(w);
    cleanup(&base);
}

#[test]
fn multi_segment_roll() {
    let base = base_path("roll");
    cleanup(&base);

    let (mut w, mut r) = AppendOnlyJournal::<FixHeader>::open(&base, cfg(128)).unwrap();
    for seq in 1..=20u64 {
        let payload = (seq as u32).to_le_bytes();
        let mut claim = w.try_claim(fix(seq), payload.len()).unwrap();
        claim.as_mut_slice().copy_from_slice(&payload);
        claim.commit();
    }

    let mut seen = 0u64;
    for seq in 1..=20u64 {
        let rec = r.next_record().unwrap().unwrap();
        assert_eq!(rec.header().seq, seq);
        assert_eq!(rec.payload(), &(seq as u32).to_le_bytes());
        seen += 1;
    }
    assert_eq!(seen, 20);
    assert!(r.next_record().unwrap().is_none());
    assert!(super::segment_path(&base, 1).exists());

    drop((w, r));
    cleanup(&base);
}

#[test]
fn pad_at_frame_header_boundary() {
    let base = base_path("pad-boundary");
    cleanup(&base);

    let (mut w, mut r) = AppendOnlyJournal::<()>::open(&base, cfg(64)).unwrap();
    let lens = [8usize, 8, 16, 8, 8];
    for (i, &len) in lens.iter().enumerate() {
        let payload = vec![i as u8 + 1; len];
        let mut claim = w.try_claim((), len).unwrap();
        claim.as_mut_slice().copy_from_slice(&payload);
        claim.commit();
    }
    assert!(super::segment_path(&base, 1).exists());

    for (i, &len) in lens.iter().enumerate() {
        let rec = r.next_record().unwrap().unwrap();
        assert_eq!(rec.payload(), &vec![i as u8 + 1; len][..]);
    }
    assert!(r.next_record().unwrap().is_none());

    drop((w, r));
    cleanup(&base);
}

#[test]
fn recovery_stops_at_uncommitted_tail() {
    let base = base_path("recovery");
    cleanup(&base);

    {
        let (mut w, _r) = AppendOnlyJournal::<FixHeader>::open(&base, cfg(1 << 16)).unwrap();
        for seq in 1..=2u64 {
            let payload = (seq as u32).to_le_bytes();
            let mut claim = w.try_claim(fix(seq), payload.len()).unwrap();
            claim.as_mut_slice().copy_from_slice(&payload);
            claim.commit();
        }
        {
            let mut claim = w.try_claim(fix(3), 4).unwrap();
            claim.as_mut_slice().copy_from_slice(&7u32.to_le_bytes());
        }
        drop(w);
    }

    let (mut w, mut r) = AppendOnlyJournal::<FixHeader>::open(&base, cfg(1 << 16)).unwrap();
    let payload = 99u32.to_le_bytes();
    let mut claim = w.try_claim(fix(3), payload.len()).unwrap();
    claim.as_mut_slice().copy_from_slice(&payload);
    claim.commit();

    assert_eq!(r.next_record().unwrap().unwrap().header().seq, 1);
    assert_eq!(r.next_record().unwrap().unwrap().header().seq, 2);
    let third = r.next_record().unwrap().unwrap();
    assert_eq!(third.header().seq, 3);
    assert_eq!(third.payload(), &99u32.to_le_bytes());
    assert!(r.next_record().unwrap().is_none());

    drop((w, r));
    cleanup(&base);
}

#[test]
fn commit_returns_offset_read_from_seeks() {
    let base = base_path("offset-seek");
    cleanup(&base);

    let (mut w, mut r) = AppendOnlyJournal::<FixHeader>::open(&base, cfg(1 << 16)).unwrap();
    let mut offsets: Vec<AppendOffset> = Vec::new();
    for seq in 1..=10u64 {
        let payload = (seq as u32).to_le_bytes();
        let mut claim = w.try_claim(fix(seq), payload.len()).unwrap();
        claim.as_mut_slice().copy_from_slice(&payload);
        offsets.push(claim.commit());
    }

    let at = offsets[4];
    let h = r.peek_header(at).unwrap().unwrap();
    assert_eq!(h.seq, 5);

    let got: Vec<u64> = r
        .read_from(at, 5, 8)
        .unwrap()
        .map(|rec| rec.header().seq)
        .collect();
    assert_eq!(got, vec![5, 6, 7, 8]);

    drop((w, r));
    cleanup(&base);
}

#[test]
fn last_seq_empty_and_nonempty() {
    let base = base_path("last-seq");
    cleanup(&base);

    let (mut w, mut r) = AppendOnlyJournal::<FixHeader>::open(&base, cfg(1 << 16)).unwrap();
    assert_eq!(r.last_seq().unwrap(), None);

    for seq in 1..=5u64 {
        let mut claim = w.try_claim(fix(seq), 4).unwrap();
        claim
            .as_mut_slice()
            .copy_from_slice(&(seq as u32).to_le_bytes());
        claim.commit();
    }

    let (_, mut r2) = AppendOnlyJournal::<FixHeader>::open(&base, cfg(1 << 16)).unwrap();
    assert_eq!(r2.last_seq().unwrap(), Some(5));

    drop((w, r, r2));
    cleanup(&base);
}

#[test]
fn peek_header_returns_none_for_unwritten() {
    let base = base_path("peek-unwritten");
    cleanup(&base);

    let (mut _w, mut r) = AppendOnlyJournal::<FixHeader>::open(&base, cfg(1 << 16)).unwrap();
    let at = AppendOffset {
        segment: 99,
        offset: 0,
    };
    assert!(r.peek_header(at).unwrap().is_none());

    cleanup(&base);
}

#[test]
fn read_range_by_seq() {
    let base = base_path("range");
    cleanup(&base);

    let (mut w, mut r) = AppendOnlyJournal::<FixHeader>::open(&base, cfg(128)).unwrap();
    for seq in 1..=10u64 {
        let payload = (seq as u32).to_le_bytes();
        let mut claim = w.try_claim(fix(seq), payload.len()).unwrap();
        claim.as_mut_slice().copy_from_slice(&payload);
        claim.commit();
    }

    let got: Vec<u64> = r
        .read_range(3..=6)
        .unwrap()
        .map(|rec| rec.header().seq)
        .collect();
    assert_eq!(got, vec![3, 4, 5, 6]);

    let got: Vec<u64> = r
        .read_range(8..)
        .unwrap()
        .map(|rec| rec.header().seq)
        .collect();
    assert_eq!(got, vec![8, 9, 10]);

    drop((w, r));
    cleanup(&base);
}
