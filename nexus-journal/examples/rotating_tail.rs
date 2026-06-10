//! Tail-latency harness for the rotating journal — built to EXPOSE tails,
//! not hide them (cf. `rotating_latency`/`rotating_stress`, which pace +
//! pretouch + warm-rotate the tails away).
//!
//!   * fenced rdtsc cycle timing, per-sample (not `Instant::now()`)
//!   * unpaced + small segments → forces frequent rotation
//!   * `PRETOUCH=0` by default → the page-fault sawtooth is visible
//!   * appends classified {normal, page-crossing, rotation}, each its own
//!     histogram; rotation detected by epoch change, not a frame counter
//!   * `StandbyNotReady` is TIMED (retry-to-success), not skipped — no
//!     coordinated omission on the conductor-fell-behind case
//!
//! Cycles, not ns: divide by the pinned core's GHz for nanoseconds.
//!
//! Run pinned, turbo off:
//! ```text
//! echo 1 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo
//! cargo build --release --example rotating_tail -p nexus-journal
//! SEG=262144 PRETOUCH=0 taskset -c 2 ./target/release/examples/rotating_tail
//! echo 0 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo
//! ```
//!
//! Env knobs (default): `SEG`(262144) `PAYLOAD`(64) `WRITES`(5000000)
//! `PRETOUCH`(0) `QDEPTH`(4)

use hdrhistogram::Histogram;
use nexus_journal::{ConductorBuilder, WriteError};

const PAGE: u64 = 4096;
const FRAME_HDR: usize = 8; // mirrors nexus_journal's frame header layout

#[inline(always)]
fn rdtsc_start() -> u64 {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        core::arch::x86_64::_mm_lfence();
        core::arch::x86_64::_rdtsc()
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        0
    }
}

#[inline(always)]
fn rdtsc_end() -> u64 {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        let mut aux = 0u32;
        let t = core::arch::x86_64::__rdtscp(&raw mut aux);
        core::arch::x86_64::_mm_lfence();
        t
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        0
    }
}

fn env_usize(key: &str, default: usize) -> usize {
    std::env::var(key)
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(default)
}

/// Frame footprint: 8-byte header + 8-byte-aligned body (mirrors `frame::footprint`).
const fn footprint(body: usize) -> usize {
    FRAME_HDR + ((body + 7) & !7)
}

fn report(name: &str, h: &Histogram<u64>) {
    if h.is_empty() {
        println!("  {name:<14} (no samples)");
        return;
    }
    println!(
        "  {name:<14} n={:<9} p50={:<6} p90={:<6} p99={:<7} p99.9={:<8} p99.99={:<9} max={}",
        h.len(),
        h.value_at_quantile(0.50),
        h.value_at_quantile(0.90),
        h.value_at_quantile(0.99),
        h.value_at_quantile(0.999),
        h.value_at_quantile(0.9999),
        h.max(),
    );
}

fn main() {
    let seg = env_usize("SEG", 256 * 1024);
    let payload_size = env_usize("PAYLOAD", 64);
    let writes = env_usize("WRITES", 5_000_000);
    let pretouch = env_usize("PRETOUCH", 0) != 0;
    let qdepth = env_usize("QDEPTH", 4);

    let dir = std::env::temp_dir().join(format!("nexus-journal-tail-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);

    let mut conductor = ConductorBuilder::new(&dir)
        .clean_queue_depth(qdepth)
        .open()
        .expect("conductor open");
    let mut journal = conductor
        .session()
        .segment_size(seg)
        .pretouch(pretouch)
        .open()
        .expect("journal open");

    let payload = vec![0xABu8; payload_size];
    let foot = footprint(payload_size) as u64;
    let seg_u = seg as u64;

    let mut h_normal = Histogram::<u64>::new(3).unwrap();
    let mut h_page = Histogram::<u64>::new(3).unwrap();
    let mut h_rot = Histogram::<u64>::new(3).unwrap();
    let mut h_stall = Histogram::<u64>::new(3).unwrap();
    let mut standby = 0u64;

    // Light warmup: prime icache/branch predictors on the normal path. We do
    // NOT pre-fill or pre-rotate the measured segments (that's how the old
    // examples hid the tails).
    for _ in 0..1000 {
        let _ = journal.append(&payload);
    }

    for _ in 0..writes {
        let wp_before = journal.write_pos();
        let local_off = wp_before % seg_u;

        let start = rdtsc_start();
        let res = journal.append(&payload);
        let end = rdtsc_end();
        let cyc = end.wrapping_sub(start);

        match res {
            Ok(_) => {
                let rotated = journal.write_pos() / seg_u != wp_before / seg_u;
                if rotated {
                    h_rot.record(cyc).ok();
                } else if local_off / PAGE != (local_off + foot - 1) / PAGE {
                    h_page.record(cyc).ok();
                } else {
                    h_normal.record(cyc).ok();
                }
            }
            Err(WriteError::StandbyNotReady) => {
                // Conductor fell behind. Time the whole retry-to-success window
                // so the record's true insert latency is captured.
                standby += 1;
                loop {
                    std::hint::spin_loop();
                    match journal.append(&payload) {
                        Ok(_) => {
                            h_stall.record(rdtsc_end().wrapping_sub(start)).ok();
                            break;
                        }
                        Err(WriteError::StandbyNotReady) => {}
                        Err(e) => panic!("unexpected: {e}"),
                    }
                }
            }
            Err(e) => panic!("unexpected: {e}"),
        }
    }

    let clean_rot = h_rot.len();
    let total_rot = clean_rot + standby;
    let not_ready_pct = if total_rot == 0 {
        0
    } else {
        100 * standby / total_rot
    };

    println!("--- rotating journal tail (cycles) ---");
    println!(
        "  seg={seg}B payload={payload_size}B writes={writes} pretouch={pretouch} qdepth={qdepth}"
    );
    println!("  rotations: {clean_rot} clean, {standby} stalled ({not_ready_pct}% not-ready)");
    println!();
    report("normal", &h_normal);
    report("page-cross", &h_page);
    report("rotation", &h_rot);
    report("stall", &h_stall);

    drop(journal);
    drop(conductor);
    let _ = std::fs::remove_dir_all(&dir);
}
