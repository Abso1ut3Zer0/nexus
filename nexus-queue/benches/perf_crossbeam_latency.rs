//! Ping-pong latency benchmark for crossbeam ArrayQueue (MPMC)
//!
//! NOTE: crossbeam ArrayQueue is MPMC, so it has overhead for handling
//! multiple producers/consumers that SPSC queues avoid.
//!
//! Run: cargo build --release --bench perf_crossbeam_latency
//! Profile: sudo taskset -c 0,2 ./target/release/deps/perf_crossbeam_latency-*

use std::{sync::Arc, thread};

use crossbeam_queue::ArrayQueue;

const WARMUP: u64 = 10_000;
const SAMPLES: u64 = 100_000;
const CAPACITY: usize = 64;

fn main() {
    // Forward channel: main -> worker
    let fwd = Arc::new(ArrayQueue::new(CAPACITY));
    // Return channel: worker -> main
    let ret = Arc::new(ArrayQueue::new(CAPACITY));

    let total = WARMUP + SAMPLES;

    // Worker thread: receive and echo back
    let worker_fwd = fwd.clone();
    let worker_ret = ret.clone();
    let worker = thread::spawn(move || {
        for _ in 0..total {
            let val = loop {
                if let Some(v) = worker_fwd.pop() {
                    break v;
                }
                std::hint::spin_loop();
            };
            while worker_ret.push(val).is_err() {
                std::hint::spin_loop();
            }
        }
    });

    let mut samples = Vec::with_capacity(SAMPLES as usize);

    // Main: send, wait for echo, measure RTT
    for i in 0..total {
        let start = rdtsc();

        while fwd.push(i).is_err() {
            std::hint::spin_loop();
        }

        loop {
            if ret.pop().is_some() {
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
        "crossbeam latency (cycles): min={} p50={} p99={} p99.9={} max={}",
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
