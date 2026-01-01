//! Ping-pong latency benchmark for nexus-channel
//!
//! Measures round-trip latency with exactly one message in flight.
//!
//! Run: cargo build --release --bench perf_channel_latency
//! Profile: sudo taskset -c 0,2 ./target/release/deps/perf_channel_latency-*

use std::thread;

use nexus_channel::channel;

const WARMUP: u64 = 10_000;
const SAMPLES: u64 = 100_000;
const CAPACITY: usize = 64;

fn main() {
    let (mut tx_fwd, mut rx_fwd) = channel::<u64>(CAPACITY);
    let (mut tx_ret, mut rx_ret) = channel::<u64>(CAPACITY);

    let total = WARMUP + SAMPLES;

    // Consumer thread: receive and echo back
    let consumer = thread::spawn(move || {
        for _ in 0..total {
            let val = rx_fwd.recv().unwrap();
            tx_ret.send(val).unwrap();
        }
    });

    let mut samples = Vec::with_capacity(SAMPLES as usize);

    // Producer: send, wait for echo, measure RTT
    for i in 0..total {
        let start = rdtsc();

        tx_fwd.send(i).unwrap();
        rx_ret.recv().unwrap();

        let elapsed = rdtsc() - start;

        if i >= WARMUP {
            samples.push(elapsed / 2); // RTT/2 for one-way estimate
        }
    }

    consumer.join().unwrap();

    // Statistics
    samples.sort_unstable();
    let min = samples[0];
    let p50 = samples[samples.len() / 2];
    let p99 = samples[(samples.len() as f64 * 0.99) as usize];
    let p999 = samples[(samples.len() as f64 * 0.999) as usize];
    let max = *samples.last().unwrap();

    println!(
        "nexus channel latency (cycles): min={} p50={} p99={} p99.9={} max={}",
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
