use std::path::{Path, PathBuf};

use super::conductor::SWAP_CLEAN;
use super::frame::footprint;
use super::{Conductor, ConductorBuilder, OpenError, SegmentedLog};

struct TempDir(PathBuf);

impl TempDir {
    fn new(name: &str) -> Self {
        let p = std::env::temp_dir().join(format!("nexus-seglog-{}-{}", std::process::id(), name));
        let _ = std::fs::remove_dir_all(&p);
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

fn open(conductor: &mut Conductor, size: usize) -> SegmentedLog {
    conductor.session().segment_size(size).open().unwrap()
}

fn open_id(conductor: &mut Conductor, size: usize, id: u32) -> SegmentedLog {
    conductor
        .session()
        .segment_size(size)
        .session_id(id)
        .open()
        .unwrap()
}

fn wait_conductor(log: &SegmentedLog) {
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(2);
    while log.swap.state() != SWAP_CLEAN {
        assert!(std::time::Instant::now() < deadline, "conductor timed out");
        std::thread::sleep(std::time::Duration::from_millis(1));
    }
}

// ---- basic operations ----

#[test]
fn roundtrip() {
    let d = TempDir::new("rt");
    let mut c = Conductor::open(d.path()).unwrap();
    let mut log = open(&mut c, 1 << 16);
    let off = log.append(b"hello").unwrap();
    let frame = log.read(off).unwrap();
    assert_eq!(frame.payload(), b"hello");
}

#[test]
fn multiple_records_in_one_segment() {
    let d = TempDir::new("multi");
    let mut c = Conductor::open(d.path()).unwrap();
    let mut log = open(&mut c, 1 << 16);
    let o1 = log.append(b"aaa").unwrap();
    let o2 = log.append(b"bb").unwrap();
    let o3 = log.append(b"cccc").unwrap();
    assert_eq!(log.read(o1).unwrap().payload(), b"aaa");
    assert_eq!(log.read(o2).unwrap().payload(), b"bb");
    assert_eq!(log.read(o3).unwrap().payload(), b"cccc");
}

#[test]
fn empty_payload_roundtrip() {
    let d = TempDir::new("empty");
    let mut c = Conductor::open(d.path()).unwrap();
    let mut log = open(&mut c, 1 << 16);
    let off = log.append(&[]).unwrap();
    assert_eq!(log.read(off).unwrap().payload(), b"");
}

#[test]
fn record_too_large_rejected() {
    let d = TempDir::new("large");
    let mut c = Conductor::open(d.path()).unwrap();
    let mut log = open(&mut c, 64);
    assert!(log.append(&[0u8; 1024]).is_err());
}

// ---- rotation ----

#[test]
fn rotation_makes_prev_slot_readable() {
    let d = TempDir::new("rot");
    let mut c = Conductor::open(d.path()).unwrap();
    let mut log = open_id(&mut c, 64, 1);
    let o0 = log.append(&[0u8; 8]).unwrap();
    let _o1 = log.append(&[1u8; 8]).unwrap();
    let _o2 = log.append(&[2u8; 8]).unwrap();
    let o3 = log.append(&[3u8; 8]).unwrap();
    let o4 = log.append(&[4u8; 8]).unwrap();
    assert_eq!(log.read(o0).unwrap().payload(), &[0u8; 8]);
    assert_eq!(log.read(o3).unwrap().payload(), &[3u8; 8]);
    assert_eq!(log.read(o4).unwrap().payload(), &[4u8; 8]);
}

#[test]
fn evicted_slot_returns_none() {
    let d = TempDir::new("evict");
    let mut c = Conductor::open(d.path()).unwrap();
    let mut log = open_id(&mut c, 64, 1);
    let o0 = log.append(&[0u8; 8]).unwrap();
    for _ in 0..3 {
        log.append(&[0u8; 8]).unwrap();
    }
    for _ in 0..4 {
        log.append(&[0u8; 8]).unwrap();
    }
    wait_conductor(&log);
    log.append(&[0u8; 1]).unwrap();
    assert!(log.read(o0).is_none());
}

#[test]
fn stale_offset_after_full_cycle_returns_none() {
    let d = TempDir::new("gen");
    let mut c = Conductor::open(d.path()).unwrap();
    let mut log = open_id(&mut c, 64, 1);
    let stale = log.append(&[0u8; 8]).unwrap();
    for _ in 0..3 {
        log.append(&[0u8; 8]).unwrap();
    }
    for _ in 0..4 {
        log.append(&[0u8; 8]).unwrap();
    }
    wait_conductor(&log);
    for _ in 0..4 {
        log.append(&[0u8; 8]).unwrap();
    }
    wait_conductor(&log);
    log.append(&[0u8; 8]).unwrap();
    assert!(log.read(stale).is_none());
}

#[test]
fn slot_order_is_sequential() {
    let d = TempDir::new("slotord");
    let mut c = Conductor::open(d.path()).unwrap();
    let mut log = open_id(&mut c, 64, 1);
    assert_eq!(log.current, 0);
    for _ in 0..4 {
        log.append(&[0u8; 8]).unwrap();
    }
    log.append(&[0u8; 8]).unwrap();
    assert_eq!(log.current, 1);
    for _ in 0..3 {
        log.append(&[0u8; 8]).unwrap();
    }
    wait_conductor(&log);
    log.append(&[0u8; 8]).unwrap();
    assert_eq!(log.current, 2);
}

// ---- session ID ----

#[test]
fn session_id_in_frames() {
    let d = TempDir::new("sessrt");
    let mut c = Conductor::open(d.path()).unwrap();
    let mut log = open_id(&mut c, 1 << 16, 42);
    assert_eq!(log.session_id(), 42);
    let o1 = log.append(b"hello").unwrap();
    let o2 = log.append(b"world").unwrap();
    assert_eq!(log.read(o1).unwrap().session_id(), 42);
    assert_eq!(log.read(o2).unwrap().session_id(), 42);
}

#[test]
fn session_id_survives_rotation() {
    let d = TempDir::new("sessrot");
    let mut c = Conductor::open(d.path()).unwrap();
    let mut log = open_id(&mut c, 64, 10);
    let o0 = log.append(&[0u8; 8]).unwrap();
    for _ in 0..3 {
        log.append(&[0u8; 8]).unwrap();
    }
    log.append(&[1u8; 8]).unwrap();
    assert_eq!(log.read(o0).unwrap().session_id(), 10);
}

#[test]
fn scan_returns_session_id() {
    let d = TempDir::new("scansess");
    let mut c = Conductor::open(d.path()).unwrap();
    let mut log = open_id(&mut c, 1 << 16, 7);
    log.append(b"aaa").unwrap();
    log.append(b"bbb").unwrap();

    let mut pos = log.read_start();
    let f1 = log.read_next(&mut pos).unwrap();
    assert_eq!(f1.session_id(), 7);
    let f2 = log.read_next(&mut pos).unwrap();
    assert_eq!(f2.session_id(), 7);
    assert!(log.read_next(&mut pos).is_none());
}

// ---- session name ----

#[test]
fn session_name_roundtrip() {
    let d = TempDir::new("sessname");
    let mut c = Conductor::open(d.path()).unwrap();
    let log = c
        .session()
        .segment_size(1 << 16)
        .session_id(1)
        .name("fix-binance-prod")
        .open()
        .unwrap();
    assert_eq!(log.session_name(), "fix-binance-prod");
}

#[test]
fn session_name_empty_by_default() {
    let d = TempDir::new("sessnoname");
    let mut c = Conductor::open(d.path()).unwrap();
    let log = open_id(&mut c, 1 << 16, 1);
    assert_eq!(log.session_name(), "");
}

#[test]
fn session_name_survives_recovery() {
    let d = TempDir::new("sessname-rec");

    {
        let mut c = Conductor::open(d.path()).unwrap();
        let mut log = c
            .session()
            .segment_size(1 << 16)
            .session_id(1)
            .name("fix-session-alpha")
            .open()
            .unwrap();
        log.append(b"data").unwrap();
    }

    let mut c = Conductor::open(d.path()).unwrap();
    let log = open_id(&mut c, 1 << 16, 1);
    assert_eq!(log.session_name(), "fix-session-alpha");
}

// ---- sequential scan ----

#[test]
fn scan_single_segment() {
    let d = TempDir::new("scan1");
    let mut c = Conductor::open(d.path()).unwrap();
    let mut log = open(&mut c, 1 << 16);
    log.append(b"aaa").unwrap();
    log.append(b"bb").unwrap();
    log.append(b"cccc").unwrap();

    let mut pos = log.read_start();
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), b"aaa");
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), b"bb");
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), b"cccc");
    assert!(log.read_next(&mut pos).is_none());
}

#[test]
fn scan_across_rotation() {
    let d = TempDir::new("scanrot");
    let mut c = Conductor::open(d.path()).unwrap();
    let mut log = open_id(&mut c, 64, 1);
    log.append(&[1u8; 8]).unwrap();
    log.append(&[2u8; 8]).unwrap();
    log.append(&[3u8; 8]).unwrap();
    log.append(&[4u8; 8]).unwrap();
    log.append(&[5u8; 8]).unwrap();
    log.append(&[6u8; 8]).unwrap();

    let mut pos = log.read_start();
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), &[1u8; 8]);
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), &[2u8; 8]);
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), &[3u8; 8]);
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), &[4u8; 8]);
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), &[5u8; 8]);
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), &[6u8; 8]);
    assert!(log.read_next(&mut pos).is_none());
}

#[test]
fn scan_resumes_after_append() {
    let d = TempDir::new("scanresume");
    let mut c = Conductor::open(d.path()).unwrap();
    let mut log = open(&mut c, 1 << 16);
    log.append(b"first").unwrap();

    let mut pos = log.read_start();
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), b"first");
    assert!(log.read_next(&mut pos).is_none());

    log.append(b"second").unwrap();
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), b"second");
    assert!(log.read_next(&mut pos).is_none());
}

#[test]
fn scan_evicted_returns_none() {
    let d = TempDir::new("scanevict");
    let mut c = Conductor::open(d.path()).unwrap();
    let mut log = open_id(&mut c, 64, 1);
    let start = log.read_start();
    for _ in 0..4 {
        log.append(&[0u8; 8]).unwrap();
    }
    for _ in 0..4 {
        log.append(&[0u8; 8]).unwrap();
    }
    wait_conductor(&log);
    log.append(&[0u8; 8]).unwrap();

    let mut pos = start;
    assert!(log.read_next(&mut pos).is_none());
}

#[test]
fn scan_empty_log() {
    let d = TempDir::new("scanempty");
    let mut c = Conductor::open(d.path()).unwrap();
    let log = open(&mut c, 1 << 16);
    let mut pos = log.read_start();
    assert_eq!(pos, 0);
    assert!(log.read_next(&mut pos).is_none());
    assert_eq!(log.write_pos(), 0);
}

#[test]
fn scan_empty_payloads() {
    let d = TempDir::new("scanemptypay");
    let mut c = Conductor::open(d.path()).unwrap();
    let mut log = open(&mut c, 1 << 16);
    log.append(&[]).unwrap();
    log.append(&[]).unwrap();
    log.append(b"x").unwrap();

    let mut pos = log.read_start();
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), b"");
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), b"");
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), b"x");
    assert!(log.read_next(&mut pos).is_none());
}

#[test]
fn scan_variable_size_records() {
    let d = TempDir::new("scanvar");
    let mut c = Conductor::open(d.path()).unwrap();
    let mut log = open(&mut c, 1 << 16);
    log.append(b"a").unwrap();
    log.append(b"bb").unwrap();
    log.append(b"ccccccccc").unwrap();
    log.append(b"dd").unwrap();

    let mut pos = log.read_start();
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), b"a");
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), b"bb");
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), b"ccccccccc");
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), b"dd");
    assert!(log.read_next(&mut pos).is_none());
}

#[test]
fn scan_cursor_matches_write_pos_after_drain() {
    let d = TempDir::new("scandrain");
    let mut c = Conductor::open(d.path()).unwrap();
    let mut log = open_id(&mut c, 64, 1);
    log.append(&[1u8; 8]).unwrap();
    log.append(&[2u8; 8]).unwrap();
    log.append(&[3u8; 8]).unwrap();

    let mut pos = log.read_start();
    while log.read_next(&mut pos).is_some() {}
    assert_eq!(pos, log.write_pos());

    log.append(&[4u8; 8]).unwrap();
    log.append(&[5u8; 8]).unwrap();
    while log.read_next(&mut pos).is_some() {}
    assert_eq!(pos, log.write_pos());
}

// ---- write_pos / read_start ----

#[test]
fn write_pos_increases_monotonically() {
    let d = TempDir::new("wpos");
    let mut c = Conductor::open(d.path()).unwrap();
    let mut log = open(&mut c, 1 << 16);
    let mut prev_pos = log.write_pos();
    assert_eq!(prev_pos, 0);
    for _ in 0..12 {
        log.append(&[0u8; 8]).unwrap();
        let wp = log.write_pos();
        assert!(wp > prev_pos, "write_pos must increase: {wp} <= {prev_pos}");
        prev_pos = wp;
    }
}

#[test]
fn write_pos_increases_across_rotation() {
    let d = TempDir::new("wposrot");
    let mut c = Conductor::open(d.path()).unwrap();
    let mut log = open_id(&mut c, 64, 1);
    let mut prev_pos = 0u64;
    for i in 0..4 {
        log.append(&[i as u8; 8]).unwrap();
        let wp = log.write_pos();
        assert!(wp > prev_pos, "write_pos must increase: {wp} <= {prev_pos}");
        prev_pos = wp;
    }
    log.append(&[4u8; 8]).unwrap();
    let wp = log.write_pos();
    assert!(
        wp > prev_pos,
        "write_pos must increase after rotation: {wp} <= {prev_pos}"
    );
}

#[test]
fn read_start_advances_after_rotation() {
    let d = TempDir::new("readstart");
    let mut c = Conductor::open(d.path()).unwrap();
    let mut log = open_id(&mut c, 64, 1);
    assert_eq!(log.read_start(), 0);

    for _ in 0..4 {
        log.append(&[0u8; 8]).unwrap();
    }
    log.append(&[0u8; 8]).unwrap();
    assert_eq!(log.read_start(), 0);

    for _ in 0..3 {
        log.append(&[0u8; 8]).unwrap();
    }
    wait_conductor(&log);
    log.append(&[0u8; 8]).unwrap();
    assert_eq!(log.read_start(), 64);
}

#[test]
fn frame_offset_matches_global_position() {
    let d = TempDir::new("frmoff");
    let mut c = Conductor::open(d.path()).unwrap();
    let mut log = open(&mut c, 1 << 16);
    log.append(b"aaa").unwrap();
    log.append(b"bbb").unwrap();

    let mut pos = log.read_start();
    let f1 = log.read_next(&mut pos).unwrap();
    assert_eq!(f1.offset(), 0);
    let f2 = log.read_next(&mut pos).unwrap();
    assert_eq!(f2.offset(), footprint(3) as u64);
}

// ---- crash recovery ----

#[test]
fn recover_after_clean_shutdown() {
    let d = TempDir::new("recover-clean");

    {
        let mut c = Conductor::open(d.path()).unwrap();
        let mut log = open_id(&mut c, 1 << 16, 1);
        log.append(b"first").unwrap();
        log.append(b"second").unwrap();
    }

    let mut c = Conductor::open(d.path()).unwrap();
    let log = open_id(&mut c, 1 << 16, 1);
    let mut pos = log.read_start();
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), b"first");
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), b"second");
    assert!(log.read_next(&mut pos).is_none());
}

#[test]
fn recover_after_rotation() {
    let d = TempDir::new("recover-rot");

    {
        let mut c = Conductor::open(d.path()).unwrap();
        let mut log = open_id(&mut c, 64, 1);
        for i in 0..5u8 {
            log.append(&[i; 8]).unwrap();
        }
        assert_eq!(log.epoch, 1);
    }

    let mut c = Conductor::open(d.path()).unwrap();
    let log = open_id(&mut c, 64, 1);
    assert_eq!(log.epoch, 1);
    assert_eq!(log.current, 1);
    let mut pos = log.read_start();
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), &[0u8; 8]);
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), &[1u8; 8]);
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), &[2u8; 8]);
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), &[3u8; 8]);
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), &[4u8; 8]);
    assert!(log.read_next(&mut pos).is_none());
}

#[test]
fn recover_after_multiple_rotations() {
    let d = TempDir::new("recover-multi-rot");

    {
        let mut c = Conductor::open(d.path()).unwrap();
        let mut log = open_id(&mut c, 64, 1);
        // 4 records per segment at 16 bytes each (8 hdr + 8 payload).
        // Fill 3 segments = 12 records → epoch 2 (rotated twice).
        for i in 0..4u8 {
            log.append(&[i; 8]).unwrap();
        }
        assert_eq!(log.epoch, 0);
        for i in 4..8u8 {
            log.append(&[i; 8]).unwrap();
        }
        assert_eq!(log.epoch, 1);
        wait_conductor(&log);
        for i in 8..12u8 {
            log.append(&[i; 8]).unwrap();
        }
        assert_eq!(log.epoch, 2);
    }

    let mut c = Conductor::open(d.path()).unwrap();
    let log = open_id(&mut c, 64, 1);
    assert_eq!(log.epoch, 2);
    assert_eq!(log.current, 2);
    // Only prev (epoch 1, slot 1) and current (epoch 2, slot 2) readable.
    // Slot 0 (epoch 0) was evicted.
    let mut pos = log.read_start();
    // prev segment: records 4..8
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), &[4u8; 8]);
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), &[5u8; 8]);
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), &[6u8; 8]);
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), &[7u8; 8]);
    // current segment: records 8..12
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), &[8u8; 8]);
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), &[9u8; 8]);
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), &[10u8; 8]);
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), &[11u8; 8]);
    assert!(log.read_next(&mut pos).is_none());
}

#[test]
fn recover_continues_appending() {
    let d = TempDir::new("recover-append");

    {
        let mut c = Conductor::open(d.path()).unwrap();
        let mut log = open_id(&mut c, 1 << 16, 1);
        log.append(b"before").unwrap();
    }

    let mut c = Conductor::open(d.path()).unwrap();
    let mut log = open_id(&mut c, 1 << 16, 1);
    log.append(b"after").unwrap();

    let mut pos = log.read_start();
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), b"before");
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), b"after");
    assert!(log.read_next(&mut pos).is_none());
}

#[test]
fn recover_continues_appending_after_rotation() {
    let d = TempDir::new("recover-append-rot");

    {
        let mut c = Conductor::open(d.path()).unwrap();
        let mut log = open_id(&mut c, 64, 1);
        for i in 0..5u8 {
            log.append(&[i; 8]).unwrap();
        }
    }

    let mut c = Conductor::open(d.path()).unwrap();
    let mut log = open_id(&mut c, 64, 1);
    log.append(&[99u8; 8]).unwrap();

    let mut pos = log.read_start();
    // prev slot should have the first 4 records
    for i in 0..4u8 {
        assert_eq!(log.read_next(&mut pos).unwrap().payload(), &[i; 8]);
    }
    // current slot: the 5th record from before + the new one
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), &[4u8; 8]);
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), &[99u8; 8]);
    assert!(log.read_next(&mut pos).is_none());
}

// ---- builder / conductor options ----

#[test]
fn open_strict_rejects_mismatch() {
    let d = TempDir::new("strict");

    {
        let mut c = Conductor::open(d.path()).unwrap();
        let _log = open_id(&mut c, 1 << 16, 1);
    }

    let mut c = Conductor::open(d.path()).unwrap();
    let result = c
        .session()
        .segment_size(1 << 20)
        .session_id(1)
        .open_strict();
    assert!(matches!(result, Err(OpenError::ConfigMismatch { .. })));
}

#[test]
fn open_non_strict_uses_manifest_config() {
    let d = TempDir::new("nonstrict");

    {
        let mut c = Conductor::open(d.path()).unwrap();
        let _log = open_id(&mut c, 64, 1);
    }

    let mut c = Conductor::open(d.path()).unwrap();
    let mut log = c.session().segment_size(1024).session_id(1).open().unwrap();
    assert_eq!(log.segment_size(), 64);
    log.append(&[0u8; 8]).unwrap();
}

#[test]
fn builder_creates_fresh() {
    let d = TempDir::new("builder-fresh");
    let mut c = Conductor::open(d.path()).unwrap();
    let mut log = c.session().segment_size(128).open().unwrap();
    let off = log.append(b"test").unwrap();
    assert_eq!(log.read(off).unwrap().payload(), b"test");
}

#[test]
fn conductor_builder_custom_queue_depth() {
    let d = TempDir::new("cond-builder");
    let mut c = ConductorBuilder::new(d.path())
        .clean_queue_depth(16)
        .open()
        .unwrap();
    let mut log = open_id(&mut c, 64, 1);
    // Rotate several times — deeper queue should handle it without stalling
    for i in 0u32..40 {
        if log.swap.state() != SWAP_CLEAN {
            wait_conductor(&log);
        }
        log.append(&i.to_le_bytes()).unwrap();
    }
    assert!(log.epoch >= 9);
}

// ---- conductor: multi-session ----

#[test]
fn conductor_multiple_sessions() {
    let d = TempDir::new("multi-sess");
    let mut c = Conductor::open(d.path()).unwrap();

    let mut log1 = open_id(&mut c, 1 << 16, 1);
    let mut log2 = open_id(&mut c, 1 << 16, 2);

    let o1 = log1.append(b"session-1-data").unwrap();
    let o2 = log2.append(b"session-2-data").unwrap();

    assert_eq!(log1.read(o1).unwrap().payload(), b"session-1-data");
    assert_eq!(log1.read(o1).unwrap().session_id(), 1);
    assert_eq!(log2.read(o2).unwrap().payload(), b"session-2-data");
    assert_eq!(log2.read(o2).unwrap().session_id(), 2);
}

#[test]
fn conductor_session_in_use_rejected() {
    let d = TempDir::new("sess-inuse");
    let mut c = Conductor::open(d.path()).unwrap();
    let _log = open_id(&mut c, 1 << 16, 5);

    let result = c.session().segment_size(1 << 16).session_id(5).open();
    assert!(matches!(
        result,
        Err(OpenError::SessionInUse { session_id: 5 })
    ));
}

#[test]
fn session_lock_released_on_drop() {
    let d = TempDir::new("sess-lock-drop");
    let mut c = Conductor::open(d.path()).unwrap();

    {
        let _log = open_id(&mut c, 1 << 16, 5);
        // Session 5 is locked while _log is alive
    }
    // _log dropped — OFD lock released

    // Should be able to reopen the same session
    let mut log = open_id(&mut c, 1 << 16, 5);
    log.append(b"reopened").unwrap();
    let mut pos = log.read_start();
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), b"reopened");
}

#[test]
fn session_lock_cross_conductor() {
    let d = TempDir::new("sess-lock-cross");

    // Conductor 1 opens session 5
    let mut c1 = Conductor::open(d.path()).unwrap();
    let _log1 = open_id(&mut c1, 1 << 16, 5);

    // Conductor 2 (simulating another process) tries the same session
    let mut c2 = Conductor::open(d.path()).unwrap();
    let result = c2.session().segment_size(1 << 16).session_id(5).open();
    assert!(matches!(
        result,
        Err(OpenError::SessionInUse { session_id: 5 })
    ));
}

#[test]
fn conductor_auto_assigns_session_id() {
    let d = TempDir::new("auto-id");
    let mut c = Conductor::open(d.path()).unwrap();

    let log1 = c.session().segment_size(1 << 16).open().unwrap();
    let id1 = log1.session_id();
    assert!(id1 > 0);

    let log2 = c.session().segment_size(1 << 16).open().unwrap();
    let id2 = log2.session_id();
    assert_ne!(id1, id2);
}

#[test]
fn conductor_sessions_on_disk() {
    let d = TempDir::new("disk-scan");

    {
        let mut c = Conductor::open(d.path()).unwrap();
        let _log1 = open_id(&mut c, 1 << 16, 3);
        let _log2 = open_id(&mut c, 1 << 16, 7);
    }

    let c = Conductor::open(d.path()).unwrap();
    let ids = c.sessions_on_disk().unwrap();
    assert_eq!(ids, vec![3, 7]);
}

#[test]
fn conductor_auto_id_skips_existing_on_disk() {
    let d = TempDir::new("auto-skip");

    {
        let mut c = Conductor::open(d.path()).unwrap();
        let _log = open_id(&mut c, 1 << 16, 5);
    }

    let mut c = Conductor::open(d.path()).unwrap();
    let log = c.session().segment_size(1 << 16).open().unwrap();
    assert!(log.session_id() > 5);
}

#[test]
fn two_conductors_no_id_collision() {
    let d = TempDir::new("two-cond");

    // Simulate two processes opening conductors on the same directory.
    // Both auto-assign — they must not collide.
    let mut c1 = Conductor::open(d.path()).unwrap();
    let mut c2 = Conductor::open(d.path()).unwrap();

    let log1 = c1.session().segment_size(1 << 16).open().unwrap();
    let log2 = c2.session().segment_size(1 << 16).open().unwrap();

    assert_ne!(log1.session_id(), log2.session_id());
}

#[test]
fn two_conductors_explicit_then_auto() {
    let d = TempDir::new("two-cond-mix");

    // Process 1 claims ID 10 explicitly
    let mut c1 = Conductor::open(d.path()).unwrap();
    let _log1 = open_id(&mut c1, 1 << 16, 10);

    // Process 2 auto-assigns — must be > 10
    let mut c2 = Conductor::open(d.path()).unwrap();
    let log2 = c2.session().segment_size(1 << 16).open().unwrap();
    assert!(log2.session_id() > 10);
}

#[test]
fn conductor_shared_cleanup_thread() {
    let d = TempDir::new("shared-cleanup");
    let mut c = Conductor::open(d.path()).unwrap();

    let mut log1 = open_id(&mut c, 64, 1);
    let mut log2 = open_id(&mut c, 64, 2);

    // Rotate both sessions — both use the same conductor thread
    for _ in 0..5 {
        log1.append(&[0u8; 8]).unwrap();
    }
    assert_eq!(log1.epoch, 1);
    wait_conductor(&log1);

    for _ in 0..5 {
        log2.append(&[0u8; 8]).unwrap();
    }
    assert_eq!(log2.epoch, 1);
    wait_conductor(&log2);

    // Both can continue writing after rotation
    log1.append(&[1u8; 8]).unwrap();
    log2.append(&[2u8; 8]).unwrap();
}

// ---- directory layout ----

#[test]
fn session_files_in_subdirectory() {
    let d = TempDir::new("subdir");

    let mut c = Conductor::open(d.path()).unwrap();
    let _log = open_id(&mut c, 1 << 16, 42);

    assert!(d.path().join("42").join("session.lock").exists());
    assert!(d.path().join("42").join("journal.manifest").exists());
    assert!(d.path().join("42").join("seg0.dat").exists());
    assert!(d.path().join("42").join("seg1.dat").exists());
    assert!(d.path().join("42").join("seg2.dat").exists());
}

#[test]
fn multiple_sessions_separate_directories() {
    let d = TempDir::new("sep-dirs");

    let mut c = Conductor::open(d.path()).unwrap();
    let _log1 = open_id(&mut c, 1 << 16, 1);
    let _log2 = open_id(&mut c, 1 << 16, 2);

    assert!(d.path().join("1").join("journal.manifest").exists());
    assert!(d.path().join("2").join("journal.manifest").exists());
}

// ---- pretouch / huge_pages builder options ----

#[test]
fn builder_pretouch_option() {
    let d = TempDir::new("pretouch");
    let mut c = Conductor::open(d.path()).unwrap();
    let mut log = c
        .session()
        .segment_size(1 << 16)
        .session_id(1)
        .pretouch(true)
        .open()
        .unwrap();
    let off = log.append(b"pretouched").unwrap();
    assert_eq!(log.read(off).unwrap().payload(), b"pretouched");
}

// ---- edge cases ----

#[test]
fn recover_empty_session() {
    let d = TempDir::new("recover-empty");

    {
        let mut c = Conductor::open(d.path()).unwrap();
        let _log = open_id(&mut c, 1 << 16, 1);
        // Create but write nothing
    }

    let mut c = Conductor::open(d.path()).unwrap();
    let mut log = open_id(&mut c, 1 << 16, 1);
    assert_eq!(log.write_pos(), 0);
    assert_eq!(log.epoch, 0);
    log.append(b"post-recovery").unwrap();
    let mut pos = log.read_start();
    assert_eq!(log.read_next(&mut pos).unwrap().payload(), b"post-recovery");
}

#[test]
fn conductor_open_creates_root_directory() {
    let d = TempDir::new("create-root");
    let nested = d.path().join("a").join("b").join("c");
    assert!(!nested.exists());

    let _c = Conductor::open(&nested).unwrap();
    assert!(nested.exists());
}

#[test]
fn recover_high_epoch() {
    let d = TempDir::new("high-epoch");

    {
        let mut c = Conductor::open(d.path()).unwrap();
        let mut log = open_id(&mut c, 64, 1);
        // Rotate through many epochs
        for epoch in 0..6u64 {
            for _ in 0..4 {
                log.append(&[epoch as u8; 8]).unwrap();
            }
            if epoch < 5 {
                wait_conductor(&log);
            }
        }
        // Should be at epoch 5 now
        assert_eq!(log.epoch, 5);
    }

    let mut c = Conductor::open(d.path()).unwrap();
    let log = open_id(&mut c, 64, 1);
    assert_eq!(log.epoch, 5);
    // Current slot should be epoch%3 = 2, prev should be (epoch-1)%3 = 1
    assert_eq!(log.current, 2);
    assert_eq!(log.prev, 1);

    // Should be able to read prev + current segments
    let mut pos = log.read_start();
    // prev: epoch 4 data
    for _ in 0..4 {
        assert_eq!(log.read_next(&mut pos).unwrap().payload(), &[4u8; 8]);
    }
    // current: epoch 5 data
    for _ in 0..4 {
        assert_eq!(log.read_next(&mut pos).unwrap().payload(), &[5u8; 8]);
    }
    assert!(log.read_next(&mut pos).is_none());
}

// ---- stress tests ----

#[test]
fn stress_many_rotations_single_session() {
    let d = TempDir::new("stress-rot");
    let mut c = Conductor::open(d.path()).unwrap();
    let mut log = open_id(&mut c, 64, 1);

    // 100 rotations worth of data. 4 records per segment × 100 epochs.
    let total_records = 400;
    for i in 0u32..total_records {
        if log.swap.state() != SWAP_CLEAN {
            wait_conductor(&log);
        }
        log.append(&i.to_le_bytes()).unwrap();
    }

    assert!(log.epoch >= 99);

    // Verify we can still read the last two segments
    let mut pos = log.read_start();
    let mut count = 0;
    while log.read_next(&mut pos).is_some() {
        count += 1;
    }
    // Should have ~8 records readable (prev + current segments)
    assert!(
        count >= 4 && count <= 8,
        "expected 4-8 readable, got {count}"
    );
    assert_eq!(pos, log.write_pos());
}

#[test]
fn stress_many_sessions_one_conductor() {
    let d = TempDir::new("stress-sessions");
    let mut c = Conductor::open(d.path()).unwrap();

    let mut logs: Vec<SegmentedLog> = Vec::new();
    for i in 1..=20u32 {
        logs.push(open_id(&mut c, 1 << 16, i));
    }

    // Write to all sessions
    for (idx, log) in logs.iter_mut().enumerate() {
        for j in 0..10u32 {
            let payload = format!("session-{}-record-{}", idx + 1, j);
            log.append(payload.as_bytes()).unwrap();
        }
    }

    // Verify all sessions have their data
    for (idx, log) in logs.iter().enumerate() {
        let mut pos = log.read_start();
        let mut count = 0;
        while let Some(frame) = log.read_next(&mut pos) {
            assert_eq!(frame.session_id(), (idx + 1) as u32);
            count += 1;
        }
        assert_eq!(count, 10);
    }
}

#[test]
fn stress_concurrent_id_assignment() {
    let d = TempDir::new("stress-ids");

    // Spawn 8 threads, each opening a conductor and auto-assigning 5 IDs.
    let dir_path = d.path().to_path_buf();
    let handles: Vec<_> = (0..8)
        .map(|_| {
            let p = dir_path.clone();
            std::thread::spawn(move || {
                let mut c = Conductor::open(&p).unwrap();
                let mut ids = Vec::new();
                for _ in 0..5 {
                    let log = c.session().segment_size(1 << 16).open().unwrap();
                    ids.push(log.session_id());
                }
                ids
            })
        })
        .collect();

    let mut all_ids: Vec<u32> = Vec::new();
    for h in handles {
        all_ids.extend(h.join().unwrap());
    }

    // 40 total IDs, all must be unique
    all_ids.sort_unstable();
    let before_dedup = all_ids.len();
    all_ids.dedup();
    assert_eq!(
        all_ids.len(),
        before_dedup,
        "duplicate session IDs assigned: {:?}",
        all_ids
    );
    assert_eq!(all_ids.len(), 40);
}

#[test]
fn stress_rotation_then_recovery() {
    let d = TempDir::new("stress-rec");

    {
        let mut c = Conductor::open(d.path()).unwrap();
        let mut log = open_id(&mut c, 64, 1);

        // Write through many rotations
        for i in 0u32..50 {
            if log.swap.state() != SWAP_CLEAN {
                wait_conductor(&log);
            }
            log.append(&i.to_le_bytes()).unwrap();
        }
    }

    // Recovery
    let mut c = Conductor::open(d.path()).unwrap();
    let mut log = open_id(&mut c, 64, 1);

    // Should be able to append after recovery
    log.append(b"post-recovery").unwrap();

    // Drain current readable content
    let mut pos = log.read_start();
    let mut found_post = false;
    while let Some(frame) = log.read_next(&mut pos) {
        if frame.payload() == b"post-recovery" {
            found_post = true;
        }
    }
    assert!(found_post, "post-recovery record not found after drain");
}

#[test]
fn stress_interleaved_sessions_with_rotation() {
    let d = TempDir::new("stress-interleave");
    let mut c = Conductor::open(d.path()).unwrap();

    let mut log1 = open_id(&mut c, 64, 1);
    let mut log2 = open_id(&mut c, 64, 2);

    // Interleave writes, both rotating at different rates
    for i in 0u32..40 {
        if log1.swap.state() != SWAP_CLEAN {
            wait_conductor(&log1);
        }
        if log2.swap.state() != SWAP_CLEAN {
            wait_conductor(&log2);
        }
        log1.append(&i.to_le_bytes()).unwrap();
        if i % 2 == 0 {
            log2.append(&i.to_le_bytes()).unwrap();
        }
    }

    // Both logs should have advanced epochs
    assert!(log1.epoch >= 9, "log1 epoch: {}", log1.epoch);
    assert!(log2.epoch >= 4, "log2 epoch: {}", log2.epoch);

    // Both should be independently scannable
    let mut pos1 = log1.read_start();
    let mut count1 = 0;
    while log1.read_next(&mut pos1).is_some() {
        count1 += 1;
    }
    assert!(count1 > 0);

    let mut pos2 = log2.read_start();
    let mut count2 = 0;
    while log2.read_next(&mut pos2).is_some() {
        count2 += 1;
    }
    assert!(count2 > 0);
}

#[test]
fn stress_fill_segment_exactly() {
    let d = TempDir::new("stress-exact");
    let mut c = Conductor::open(d.path()).unwrap();
    // segment_size=64, frame footprint for 8-byte payload = 8 (hdr) + 8 (body) = 16
    // So 4 records fill a segment exactly (4 × 16 = 64)
    let mut log = open_id(&mut c, 64, 1);

    // Write exactly 4 records — should fill without rotating
    for i in 0..4u8 {
        log.append(&[i; 8]).unwrap();
    }
    assert_eq!(log.epoch, 0);
    assert_eq!(log.cursor, 64);

    // Next write triggers rotation
    log.append(&[4u8; 8]).unwrap();
    assert_eq!(log.epoch, 1);
    assert_eq!(log.cursor, 16); // one record in new segment
}

#[test]
fn stress_rapid_open_close_cycles() {
    let d = TempDir::new("stress-reopen");

    // Open, write, close, reopen — 20 cycles
    for cycle in 0u32..20 {
        let mut c = Conductor::open(d.path()).unwrap();
        let mut log = open_id(&mut c, 1 << 16, 1);
        log.append(&cycle.to_le_bytes()).unwrap();
    }

    // Final open — should see all 20 records (segment never rotated)
    let mut c = Conductor::open(d.path()).unwrap();
    let log = open_id(&mut c, 1 << 16, 1);
    let mut pos = log.read_start();
    let mut count = 0;
    while let Some(frame) = log.read_next(&mut pos) {
        let val = u32::from_le_bytes(frame.payload().try_into().unwrap());
        assert_eq!(val, count);
        count += 1;
    }
    assert_eq!(count, 20);
}

#[test]
fn stress_large_payloads() {
    let d = TempDir::new("stress-large");
    let mut c = Conductor::open(d.path()).unwrap();
    // 1MB segments, write 100KB payloads
    let mut log = open_id(&mut c, 1 << 20, 1);
    let big = vec![0xABu8; 100_000];

    for _ in 0..20 {
        if log.swap.state() != SWAP_CLEAN {
            wait_conductor(&log);
        }
        log.append(&big).unwrap();
    }

    // Verify readable content is intact
    let mut pos = log.read_start();
    while let Some(frame) = log.read_next(&mut pos) {
        assert_eq!(frame.payload().len(), 100_000);
        assert!(frame.payload().iter().all(|&b| b == 0xAB));
    }
}

// ---- edge cases ----

#[test]
fn session_id_mismatch_on_corrupted_directory() {
    let d = TempDir::new("sid-mismatch");

    // Create session 10 normally
    {
        let mut c = Conductor::open(d.path()).unwrap();
        let _log = open_id(&mut c, 1 << 16, 10);
    }

    // Simulate corruption: rename directory 10/ to 20/
    std::fs::rename(d.path().join("10"), d.path().join("20")).unwrap();

    // Now try to open session 20 — the manifest inside says session_id=10
    let mut c = Conductor::open(d.path()).unwrap();
    let result = c.session().segment_size(1 << 16).session_id(20).open();
    assert!(matches!(
        result,
        Err(OpenError::ConfigMismatch {
            field: "session_id",
            ..
        })
    ));
}
