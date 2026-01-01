// benches/perf_slot_latency.rs
//! Ping-pong latency benchmark for nexus_slot
//!
//! Measures round-trip latency with exactly one value exchange per iteration.
//!
//! Run: cargo build --release --bench perf_slot_latency
//! Profile: sudo taskset -c 0,2 ./target/release/deps/perf_slot_latency-*

use std::thread;

use nexus_slot::{self, Pod};

const WARMUP: u64 = 10_000;
const SAMPLES: u64 = 100_000;

/// 64-byte cache-line sized message
#[derive(Clone)]
#[repr(C, align(64))]
struct Message {
    value: u64,
    _padding: [u8; 56],
}

unsafe impl Pod for Message {}

fn main() {
    let (mut writer_a, mut reader_a) = nexus_slot::slot::<Message>();
    let (mut writer_b, mut reader_b) = nexus_slot::slot::<Message>();

    let total = WARMUP + SAMPLES;

    // Worker thread: read from A, write to B
    let worker = thread::spawn(move || {
        for _ in 0..total {
            // Wait for value
            let msg = loop {
                if let Some(m) = reader_a.read() {
                    break m;
                }
                std::hint::spin_loop();
            };
            // Echo back
            writer_b.write(msg);
        }
    });

    let mut samples = Vec::with_capacity(SAMPLES as usize);

    // Main thread: write to A, wait for B, measure RTT
    for i in 0..total {
        let start = rdtsc();

        writer_a.write(Message {
            value: i,
            _padding: [0; 56],
        });

        loop {
            if reader_b.read().is_some() {
                break;
            }
            std::hint::spin_loop();
        }

        let elapsed = rdtsc() - start;

        if i >= WARMUP {
            samples.push(elapsed / 2); // RTT/2 for one-way estimate
        }
    }

    worker.join().unwrap();

    // Statistics
    samples.sort_unstable();
    let min = samples[0];
    let p50 = samples[samples.len() / 2];
    let p99 = samples[(samples.len() as f64 * 0.99) as usize];
    let p999 = samples[(samples.len() as f64 * 0.999) as usize];
    let max = *samples.last().unwrap();

    println!(
        "nexus_slot latency (cycles): min={} p50={} p99={} p99.9={} max={}",
        min, p50, p99, p999, max
    );
}

#[inline]
fn rdtsc() -> u64 {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        let mut aux: u32 = 0;
        core::arch::x86_64::__rdtscp(&mut aux)
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        use std::time::Instant;
        static START: std::sync::OnceLock<Instant> = std::sync::OnceLock::new();
        START.get_or_init(Instant::now).elapsed().as_nanos() as u64
    }
}
