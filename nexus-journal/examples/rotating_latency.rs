use std::time::{Duration, Instant};

use hdrhistogram::Histogram;
use nexus_journal::Conductor;

const SEGMENT_SIZE: usize = 4 * 1024 * 1024;
const NUM_WRITES: u64 = 100_000;
const PAYLOAD_SIZE: usize = 64;
const INTERVAL: Duration = Duration::from_micros(25);

fn main() {
    let dir = std::env::temp_dir().join(format!(
        "nexus-journal-rotating-latency-{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);

    let mut conductor = Conductor::open(&dir).expect("conductor open");

    let mut journal = conductor
        .session()
        .segment_size(SEGMENT_SIZE)
        .pretouch(true)
        .open()
        .expect("journal open");

    let payload = [0xABu8; PAYLOAD_SIZE];
    let mut hist = Histogram::<u64>::new(3).expect("histogram");

    // Warmup: fill and rotate once to prime the conductor pipeline.
    let warmup = SEGMENT_SIZE / (PAYLOAD_SIZE + 8) + 1;
    for _ in 0..warmup {
        journal.append(&payload).expect("warmup append");
    }

    let mut next = Instant::now();
    let mut rotations = 0u64;
    let epoch_before = journal.write_pos() / SEGMENT_SIZE as u64;

    for _ in 0..NUM_WRITES {
        // Busy-wait pacing.
        while Instant::now() < next {
            std::hint::spin_loop();
        }

        let start = Instant::now();
        journal.append(&payload).expect("append");
        let elapsed = start.elapsed();

        hist.record(elapsed.as_nanos() as u64).ok();
        next += INTERVAL;
    }

    let epoch_after = journal.write_pos() / SEGMENT_SIZE as u64;
    rotations += epoch_after - epoch_before;

    println!("--- RotatingJournal paced append latency ---");
    println!(
        "  {NUM_WRITES} writes, {PAYLOAD_SIZE}B payload, {seg_mb}MB segments, {interval_us}μs pacing",
        seg_mb = SEGMENT_SIZE / (1024 * 1024),
        interval_us = INTERVAL.as_micros(),
    );
    println!("  rotations: {rotations}");
    println!();
    println!("  p50:    {:>8} ns", hist.value_at_quantile(0.50));
    println!("  p90:    {:>8} ns", hist.value_at_quantile(0.90));
    println!("  p99:    {:>8} ns", hist.value_at_quantile(0.99));
    println!("  p99.9:  {:>8} ns", hist.value_at_quantile(0.999));
    println!("  p99.99: {:>8} ns", hist.value_at_quantile(0.9999));
    println!("  max:    {:>8} ns", hist.max());

    drop(journal);
    drop(conductor);
    let _ = std::fs::remove_dir_all(&dir);
}
