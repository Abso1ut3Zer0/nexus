//! Ping-pong latency benchmark for overwriting SPSC ring buffer.
//!
//! Measures round-trip latency with exactly one message in flight.
//!
//! Run: cargo build --release --bench perf_spsc_overwriting_latency
//! Profile: sudo taskset -c 0,2 ./target/release/deps/perf_spsc_overwriting_latency-*

use std::thread;

use nexus_queue::spsc::overwriting;

const WARMUP: u64 = 10_000;
const SAMPLES: u64 = 100_000;
const CAPACITY: usize = 64;

fn main() {
    let (mut prod_fwd, mut cons_fwd) = overwriting::ring_buffer::<u64>(CAPACITY);
    let (mut prod_ret, mut cons_ret) = overwriting::ring_buffer::<u64>(CAPACITY);

    let total = WARMUP + SAMPLES;

    // Consumer thread: receive and echo back
    let consumer = thread::spawn(move || {
        for _ in 0..total {
            let val = loop {
                if let Some(v) = cons_fwd.pop() {
                    break v;
                }
                std::hint::spin_loop();
            };
            prod_ret.push(val);
        }
    });

    let mut samples = Vec::with_capacity(SAMPLES as usize);

    // Producer: send, wait for echo, measure RTT
    for i in 0..total {
        let start = rdtsc();

        prod_fwd.push(i);

        loop {
            if cons_ret.pop().is_some() {
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
        "overwriting latency (cycles): min={} p50={} p99={} p99.9={} max={}",
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
