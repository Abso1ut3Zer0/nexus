use hdrhistogram::Histogram;
use nexus_journal::Conductor;
use std::time::{Duration, Instant};

fn main() {
    let seg_size: usize = 64 * 1024; // 64KB — forces frequent rotation
    let num_writes: u64 = 100_000;
    let payload_size: usize = 64;
    let dir = std::env::temp_dir().join(format!(
        "nexus-journal-rotating-stress-{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);

    let mut conductor = Conductor::open(&dir).expect("conductor open");
    let mut journal = conductor
        .session()
        .segment_size(seg_size)
        .pretouch(true)
        .open()
        .expect("journal open");

    let payload = [0xABu8; 64];
    let mut hist = Histogram::<u64>::new(3).expect("histogram");
    let mut hist_normal = Histogram::<u64>::new(3).expect("histogram");
    let mut hist_rotation = Histogram::<u64>::new(3).expect("histogram");
    let mut standby_not_ready = 0u64;

    // Warmup
    let warmup = seg_size / (payload_size + 8) + 1;
    for _ in 0..warmup {
        journal.append(&payload).expect("warmup");
    }
    // Let conductor finish processing warmup rotation.
    std::thread::sleep(Duration::from_millis(50));

    let frames_per_seg = seg_size / (payload_size + 8);
    let mut frame_in_seg = (warmup % frames_per_seg) as u64;

    for _ in 0..num_writes {
        let start = Instant::now();
        match journal.append(&payload) {
            Ok(_) => {}
            Err(nexus_journal::WriteError::StandbyNotReady) => {
                standby_not_ready += 1;
                continue;
            }
            Err(e) => panic!("unexpected: {e}"),
        }
        let elapsed_ns = start.elapsed().as_nanos() as u64;

        hist.record(elapsed_ns).ok();
        frame_in_seg += 1;
        if frame_in_seg >= frames_per_seg as u64 {
            hist_rotation.record(elapsed_ns).ok();
            frame_in_seg = 0;
        } else {
            hist_normal.record(elapsed_ns).ok();
        }
    }

    let rotations = hist_rotation.len();
    let normals = hist_normal.len();

    println!("--- RotatingJournal UNPACED (64KB segments) ---");
    println!("  {num_writes} writes, {payload_size}B payload, no pacing");
    println!(
        "  {normals} normal writes, {rotations} rotation writes, {standby_not_ready} StandbyNotReady"
    );
    println!();
    println!("  COMBINED:");
    println!("    p50:    {:>8} ns", hist.value_at_quantile(0.50));
    println!("    p90:    {:>8} ns", hist.value_at_quantile(0.90));
    println!("    p99:    {:>8} ns", hist.value_at_quantile(0.99));
    println!("    p99.9:  {:>8} ns", hist.value_at_quantile(0.999));
    println!("    p99.99: {:>8} ns", hist.value_at_quantile(0.9999));
    println!("    max:    {:>8} ns", hist.max());
    println!();
    println!("  NORMAL (no rotation):");
    println!("    p50:    {:>8} ns", hist_normal.value_at_quantile(0.50));
    println!("    p90:    {:>8} ns", hist_normal.value_at_quantile(0.90));
    println!("    p99:    {:>8} ns", hist_normal.value_at_quantile(0.99));
    println!("    p99.9:  {:>8} ns", hist_normal.value_at_quantile(0.999));
    println!("    max:    {:>8} ns", hist_normal.max());
    println!();
    println!("  ROTATION (segment boundary):");
    println!(
        "    p50:    {:>8} ns",
        hist_rotation.value_at_quantile(0.50)
    );
    println!(
        "    p90:    {:>8} ns",
        hist_rotation.value_at_quantile(0.90)
    );
    println!(
        "    p99:    {:>8} ns",
        hist_rotation.value_at_quantile(0.99)
    );
    println!("    max:    {:>8} ns", hist_rotation.max());

    drop(journal);
    drop(conductor);
    let _ = std::fs::remove_dir_all(&dir);
}
