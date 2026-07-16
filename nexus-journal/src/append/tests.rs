use std::path::{Path, PathBuf};

use nexus_platform::MapHints;

use super::{AppendOnlyJournal, AppendOnlyJournalConfig, AppendOnlyJournalError, FixHeader};

/// RAII scratch path *prefix*. Unlike the other journals, an
/// [`AppendOnlyJournal`] does not own a directory: it writes sibling segment
/// files `base.0`, `base.1`, ... So this guard removes the numbered segments
/// rather than a tree.
///
/// `Drop` also runs while unwinding, so a *failing* test cleans up too — which
/// the old manual `cleanup(&base)` at the end of the body did not.
///
/// Bind it to a live local (`let base = base_path(..)`), never `let _ = ..`, or
/// the segments are removed before the test can use them.
struct TempBase(PathBuf);

impl TempBase {
    fn new(name: &str) -> Self {
        let p = std::env::temp_dir().join(format!("nexus-journal-{}-{}", std::process::id(), name));
        let this = Self(p);
        // A previous run killed by a signal can leave segments behind, and PIDs
        // get recycled -- start from a clean slate.
        this.remove_segments();
        this
    }

    fn path(&self) -> &Path {
        &self.0
    }

    /// Remove every segment this base could have produced. The tests here never
    /// roll past a handful of segments; 32 covers them all with room to spare.
    fn remove_segments(&self) {
        for i in 0..32u64 {
            let _ = std::fs::remove_file(super::segment_path(&self.0, i));
        }
    }
}

impl Drop for TempBase {
    fn drop(&mut self) {
        self.remove_segments();
    }
}

/// Cleanup must survive a panic. `Drop` running during unwind is the whole
/// reason this is RAII rather than the `cleanup(base)` call this replaced: a
/// panicking test never reaches such a call, which is exactly how the previous
/// convention leaked segments. If a refactor drops the `Drop` impl or reverts to
/// manual cleanup, this fails.
#[test]
fn temp_base_cleans_up_while_unwinding() {
    let captured: std::sync::Mutex<Option<PathBuf>> = std::sync::Mutex::new(None);

    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let base = TempBase::new("panic_cleanup");
        std::fs::write(super::segment_path(base.path(), 0), b"x").unwrap();
        *captured.lock().unwrap() = Some(base.path().to_path_buf());
        assert!(super::segment_path(base.path(), 0).exists());
        // Deliberate: this message is expected in an otherwise-passing run. The
        // global panic hook is left alone on purpose; overriding it would race
        // with other tests panicking in parallel and swallow their output.
        panic!("deliberate panic: exercising TempBase cleanup during unwind");
    }));
    assert!(res.is_err(), "the closure must have panicked");

    let p = captured
        .lock()
        .unwrap()
        .take()
        .expect("path captured before the panic");
    assert!(
        !super::segment_path(&p, 0).exists(),
        "TempBase must remove its segments while unwinding: {}",
        p.display()
    );
}

fn base_path(name: &str) -> TempBase {
    TempBase::new(name)
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

    let (mut w, mut r) = AppendOnlyJournal::<FixHeader>::open(base.path(), cfg(1 << 16)).unwrap();
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
}

#[test]
fn unit_header_zero_overhead() {
    let base = base_path("unit");

    let (mut w, mut r) = AppendOnlyJournal::<()>::open(base.path(), cfg(1 << 16)).unwrap();
    let mut claim = w.try_claim((), 5).unwrap();
    claim.as_mut_slice().copy_from_slice(b"hello");
    claim.commit();

    let rec = r.next_record().unwrap().unwrap();
    assert_eq!(rec.payload(), b"hello");
    assert!(r.next_record().unwrap().is_none());

    drop((w, r));
}

#[test]
fn empty_unit_record_rejected() {
    let base = base_path("empty");

    let (mut w, _r) = AppendOnlyJournal::<()>::open(base.path(), cfg(1 << 16)).unwrap();
    assert!(matches!(
        w.try_claim((), 0),
        Err(AppendOnlyJournalError::EmptyRecord)
    ));

    drop(w);
}

#[test]
fn record_too_large_rejected() {
    let base = base_path("toolarge");

    let (mut w, _r) = AppendOnlyJournal::<FixHeader>::open(base.path(), cfg(256)).unwrap();
    assert!(matches!(
        w.try_claim(fix(1), 4096),
        Err(AppendOnlyJournalError::RecordTooLarge { .. })
    ));

    drop(w);
}

#[test]
fn multi_segment_roll() {
    let base = base_path("roll");

    let (mut w, mut r) = AppendOnlyJournal::<FixHeader>::open(base.path(), cfg(128)).unwrap();
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
    assert!(super::segment_path(base.path(), 1).exists());

    drop((w, r));
}

#[test]
fn pad_at_frame_header_boundary() {
    let base = base_path("pad-boundary");

    let (mut w, mut r) = AppendOnlyJournal::<()>::open(base.path(), cfg(64)).unwrap();
    let lens = [8usize, 8, 16, 8, 8];
    for (i, &len) in lens.iter().enumerate() {
        let payload = vec![i as u8 + 1; len];
        let mut claim = w.try_claim((), len).unwrap();
        claim.as_mut_slice().copy_from_slice(&payload);
        claim.commit();
    }
    assert!(super::segment_path(base.path(), 1).exists());

    for (i, &len) in lens.iter().enumerate() {
        let rec = r.next_record().unwrap().unwrap();
        assert_eq!(rec.payload(), &vec![i as u8 + 1; len][..]);
    }
    assert!(r.next_record().unwrap().is_none());

    drop((w, r));
}

#[test]
fn recovery_stops_at_uncommitted_tail() {
    let base = base_path("recovery");

    {
        let (mut w, _r) = AppendOnlyJournal::<FixHeader>::open(base.path(), cfg(1 << 16)).unwrap();
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

    let (mut w, mut r) = AppendOnlyJournal::<FixHeader>::open(base.path(), cfg(1 << 16)).unwrap();
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
}

#[test]
fn read_range_by_seq() {
    let base = base_path("range");

    let (mut w, mut r) = AppendOnlyJournal::<FixHeader>::open(base.path(), cfg(128)).unwrap();
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
}
