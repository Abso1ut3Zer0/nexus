//! Ping-pong latency benchmark for rtrb
//!
//! Measures round-trip latency with exactly one message in flight.
//!
//! Run: cargo build --release --bench perf_latency_rtrb
//! Profile: sudo taskset -c 0,2 ./target/release/deps/perf_latency_rtrb-*

use std::thread;

const WARMUP: u64 = 10_000;
const SAMPLES: u64 = 100_000;
const CAPACITY: usize = 64;

fn main() {
    let (mut prod_fwd, mut cons_fwd) = rtrb::RingBuffer::<u64>::new(CAPACITY);
    let (mut prod_ret, mut cons_ret) = rtrb::RingBuffer::<u64>::new(CAPACITY);

    let total = WARMUP + SAMPLES;

    // Consumer thread: receive and echo back
    let consumer = thread::spawn(move || {
        for _ in 0..total {
            // Wait for message
            let val = loop {
                if let Ok(v) = cons_fwd.pop() {
                    break v;
                }
                std::hint::spin_loop();
            };
            // Echo it back
            while prod_ret.push(val).is_err() {
                std::hint::spin_loop();
            }
        }
    });

    let mut samples = Vec::with_capacity(SAMPLES as usize);

    // Producer: send, wait for echo, measure RTT
    for i in 0..total {
        let start = rdtsc();

        while prod_fwd.push(i).is_err() {
            std::hint::spin_loop();
        }

        // Wait for echo
        loop {
            if cons_ret.pop().is_ok() {
                break;
            }
            std::hint::spin_loop();
        }

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
        "rtrb latency (cycles): min={} p50={} p99={} p99.9={} max={}",
        min, p50, p99, p999, max
    );
}

#[inline]
fn rdtsc() -> u64 {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        core::arch::x86_64::_rdtsc()
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        use std::time::Instant;
        static START: std::sync::OnceLock<Instant> = std::sync::OnceLock::new();
        START.get_or_init(Instant::now).elapsed().as_nanos() as u64
    }
}
