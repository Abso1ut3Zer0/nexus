use std::time::{Duration, Instant};

use hdrhistogram::Histogram;
use nexus_journal::{AppendOnlyJournal, AppendOnlyJournalConfig, FixHeader, MapHints};

const SEGMENT_SIZE: usize = 4 * 1024 * 1024;
const NUM_WRITES: u64 = 100_000;
const PAYLOAD_SIZE: usize = 64;
const INTERVAL: Duration = Duration::from_micros(100);

fn main() {
    let base = std::env::temp_dir().join(format!(
        "nexus-journal-append-latency-{}",
        std::process::id()
    ));
    cleanup(&base);

    let cfg = AppendOnlyJournalConfig {
        segment_size: SEGMENT_SIZE,
        hints: MapHints {
            pretouch: true,
            ..Default::default()
        },
    };
    let (mut w, _r) = AppendOnlyJournal::<FixHeader>::open(&base, cfg).expect("journal open");
    let payload = [0xABu8; PAYLOAD_SIZE];
    let mut hist = Histogram::<u64>::new(3).expect("histogram");
    let mut seq = 0u64;

    // Warmup: fill one segment to prime the roll path.
    let warmup = SEGMENT_SIZE / (PAYLOAD_SIZE + size_of::<FixHeader>() + 8) + 1;
    for _ in 0..warmup {
        seq += 1;
        let mut claim = w
            .try_claim(
                FixHeader {
                    seq,
                    timestamp: seq,
                },
                PAYLOAD_SIZE,
            )
            .expect("warmup");
        claim.as_mut_slice().copy_from_slice(&payload);
        claim.commit();
    }

    let mut next = Instant::now();

    for _ in 0..NUM_WRITES {
        while Instant::now() < next {
            std::hint::spin_loop();
        }

        seq += 1;
        let start = Instant::now();
        let mut claim = w
            .try_claim(
                FixHeader {
                    seq,
                    timestamp: seq,
                },
                PAYLOAD_SIZE,
            )
            .expect("append");
        claim.as_mut_slice().copy_from_slice(&payload);
        claim.commit();
        let elapsed = start.elapsed();

        hist.record(elapsed.as_nanos() as u64).ok();
        next += INTERVAL;
    }

    let foot = PAYLOAD_SIZE + size_of::<FixHeader>() + 8;
    let frames_per_seg = SEGMENT_SIZE / foot;
    let total_writes = warmup as u64 + NUM_WRITES;
    let rolls = total_writes / frames_per_seg as u64;

    println!("--- AppendOnlyJournal paced append latency ---");
    println!(
        "  {NUM_WRITES} writes, {PAYLOAD_SIZE}B payload, {seg_mb}MB segments, {interval_us}μs pacing",
        seg_mb = SEGMENT_SIZE / (1024 * 1024),
        interval_us = INTERVAL.as_micros(),
    );
    println!("  segment rolls (approx): {rolls}");
    println!();
    println!("  p50:    {:>8} ns", hist.value_at_quantile(0.50));
    println!("  p90:    {:>8} ns", hist.value_at_quantile(0.90));
    println!("  p99:    {:>8} ns", hist.value_at_quantile(0.99));
    println!("  p99.9:  {:>8} ns", hist.value_at_quantile(0.999));
    println!("  p99.99: {:>8} ns", hist.value_at_quantile(0.9999));
    println!("  max:    {:>8} ns", hist.max());

    drop((w, _r));
    cleanup(&base);
}

fn cleanup(base: &std::path::Path) {
    for i in 0..128u64 {
        let mut p = base.as_os_str().to_owned();
        p.push(format!(".{i}"));
        let _ = std::fs::remove_file(std::path::PathBuf::from(p));
    }
}
