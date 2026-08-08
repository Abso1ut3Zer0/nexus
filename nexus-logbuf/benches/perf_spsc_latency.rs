//! Cycle-accurate latency benchmark for nexus-logbuf SPSC.
//!
//! Measures producer and consumer latency using rdtscp.
//!
//! Run with:
//!   cargo build --release --example perf_spsc_latency
//!   taskset -c 0 ./target/release/examples/perf_spsc_latency

use std::hint::black_box;

use hdrhistogram::Histogram;
use nexus_logbuf::queue::spsc;

const WARMUP: usize = 10_000;
const SAMPLES: usize = 100_000;
const BUFFER_SIZE: usize = 64 * 1024;

#[inline(always)]
fn rdtscp() -> u64 {
    #[cfg(target_arch = "x86_64")]
    // SAFETY: x86_64 intrinsic; benchmark runs on x86_64 only.
    unsafe {
        let mut aux: u32 = 0;
        std::arch::x86_64::__rdtscp(&raw mut aux)
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        use std::time::Instant;
        static START: std::sync::OnceLock<Instant> = std::sync::OnceLock::new();
        START.get_or_init(Instant::now).elapsed().as_nanos() as u64
    }
}

fn print_stats(name: &str, hist: &Histogram<u64>) {
    println!("{}", name);
    println!("  min:  {:>6} cycles", hist.min());
    println!("  p50:  {:>6} cycles", hist.value_at_quantile(0.50));
    println!("  p99:  {:>6} cycles", hist.value_at_quantile(0.99));
    println!("  p999: {:>6} cycles", hist.value_at_quantile(0.999));
    println!("  max:  {:>6} cycles", hist.max());
    println!("  avg:  {:>6.1} cycles", hist.mean());
}

/// Measure producer latency: try_claim + copy + commit
fn bench_producer_latency(payload_size: usize) -> Histogram<u64> {
    let (mut prod, mut cons) = spsc::new(BUFFER_SIZE);
    let mut hist = Histogram::<u64>::new(3).unwrap();
    let payload = vec![0xABu8; payload_size];

    // Warmup
    for _ in 0..WARMUP {
        let mut claim = prod.try_claim(payload_size).unwrap();
        claim.copy_from_slice(&payload);
        claim.commit();
        let _ = cons.try_claim().unwrap();
    }

    // Measured
    for _ in 0..SAMPLES {
        let start = rdtscp();
        let mut claim = prod.try_claim(payload_size).unwrap();
        claim.copy_from_slice(&payload);
        claim.commit();
        let end = rdtscp();

        let _ = hist.record(end.wrapping_sub(start));

        // Drain to avoid filling buffer
        let _ = black_box(cons.try_claim().unwrap());
    }

    hist
}

/// Measure consumer latency: try_claim + read + drop (zeroing)
fn bench_consumer_latency(payload_size: usize) -> Histogram<u64> {
    let (mut prod, mut cons) = spsc::new(BUFFER_SIZE);
    let mut hist = Histogram::<u64>::new(3).unwrap();
    let payload = vec![0xABu8; payload_size];

    // Warmup
    for _ in 0..WARMUP {
        let mut claim = prod.try_claim(payload_size).unwrap();
        claim.copy_from_slice(&payload);
        claim.commit();
        let _ = cons.try_claim().unwrap();
    }

    // Measured
    for _ in 0..SAMPLES {
        // Produce first
        let mut claim = prod.try_claim(payload_size).unwrap();
        claim.copy_from_slice(&payload);
        claim.commit();

        let start = rdtscp();
        let record = cons.try_claim().unwrap();
        black_box(&*record);
        drop(record); // Zeroing happens here
        let end = rdtscp();

        let _ = hist.record(end.wrapping_sub(start));
    }

    hist
}

/// Measure round-trip latency (ping-pong between threads)
fn bench_roundtrip_latency(payload_size: usize) -> Histogram<u64> {
    use std::thread;

    let (mut prod_fwd, mut cons_fwd) = spsc::new(BUFFER_SIZE);
    let (mut prod_ret, mut cons_ret) = spsc::new(BUFFER_SIZE);

    let total = WARMUP + SAMPLES;
    let payload = vec![0xABu8; payload_size];

    // Echo thread
    let echo = thread::spawn(move || {
        let mut buf = vec![0u8; payload_size];
        for _ in 0..total {
            // Wait for message
            loop {
                if let Some(record) = cons_fwd.try_claim() {
                    buf.copy_from_slice(&record);
                    break;
                }
                std::hint::spin_loop();
            }
            // Echo back
            loop {
                match prod_ret.try_claim(payload_size) {
                    Ok(mut claim) => {
                        claim.copy_from_slice(&buf);
                        claim.commit();
                        break;
                    }
                    Err(_) => std::hint::spin_loop(),
                }
            }
        }
    });

    let mut hist = Histogram::<u64>::new(3).unwrap();

    // Ping-pong
    for i in 0..total {
        let start = rdtscp();

        // Send
        loop {
            match prod_fwd.try_claim(payload_size) {
                Ok(mut claim) => {
                    claim.copy_from_slice(&payload);
                    claim.commit();
                    break;
                }
                Err(_) => std::hint::spin_loop(),
            }
        }

        // Wait for echo
        loop {
            if let Some(record) = cons_ret.try_claim() {
                black_box(&*record);
                break;
            }
            std::hint::spin_loop();
        }

        let elapsed = rdtscp() - start;

        if i >= WARMUP {
            let _ = hist.record(elapsed / 2); // RTT/2 for one-way estimate
        }
    }

    echo.join().unwrap();
    hist
}

fn main() {
    println!("nexus-logbuf SPSC latency benchmark");
    println!("===================================");
    println!("Warmup: {}, Samples: {}", WARMUP, SAMPLES);
    println!();

    for &payload_size in &[8, 64, 256, 1024] {
        println!("Payload size: {} bytes", payload_size);
        println!("-----------------------------------");

        let prod_hist = bench_producer_latency(payload_size);
        print_stats("Producer (claim+copy+commit):", &prod_hist);
        println!();

        let cons_hist = bench_consumer_latency(payload_size);
        print_stats("Consumer (claim+read+drop):", &cons_hist);
        println!();

        let rtt_hist = bench_roundtrip_latency(payload_size);
        print_stats("Round-trip (one-way estimate):", &rtt_hist);
        println!();
        println!();
    }
}
