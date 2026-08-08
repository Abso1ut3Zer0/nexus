//! Cycle-accurate latency benchmark for nexus-logbuf MPSC.
//!
//! Measures producer and consumer latency with multiple producers using rdtscp.
//!
//! Run with:
//!   cargo build --release --example perf_mpsc_latency
//!   taskset -c 0,2,4,6 ./target/release/examples/perf_mpsc_latency

use std::hint::black_box;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;

use hdrhistogram::Histogram;
use nexus_logbuf::queue::mpsc;

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

/// Measure single producer latency (no contention baseline)
fn bench_single_producer_latency(payload_size: usize) -> Histogram<u64> {
    let (mut prod, mut cons) = mpsc::new(BUFFER_SIZE);
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

/// Measure producer latency under contention (multiple producers)
fn bench_contended_producer_latency(payload_size: usize, num_producers: usize) -> Histogram<u64> {
    let (prod, mut cons) = mpsc::new(BUFFER_SIZE);
    let payload = vec![0xABu8; payload_size];

    let running = Arc::new(AtomicBool::new(true));
    let samples_per_producer = SAMPLES / num_producers;

    // Spawn background producers that just hammer the buffer
    let bg_handles: Vec<_> = (1..num_producers)
        .map(|_| {
            let mut prod = prod.clone();
            let payload = payload.clone();
            let running = Arc::clone(&running);
            thread::spawn(move || {
                while running.load(Ordering::Relaxed) {
                    if let Ok(mut claim) = prod.try_claim(payload.len()) {
                        claim.copy_from_slice(&payload);
                        claim.commit();
                    }
                    std::hint::spin_loop();
                }
            })
        })
        .collect();

    // Consumer thread
    let cons_running = Arc::clone(&running);
    let cons_handle = thread::spawn(move || {
        while cons_running.load(Ordering::Relaxed) {
            while cons.try_claim().is_some() {}
            std::hint::spin_loop();
        }
        // Drain remaining
        while cons.try_claim().is_some() {}
    });

    // Measuring producer
    let mut hist = Histogram::<u64>::new(3).unwrap();
    let mut prod = prod;

    // Warmup
    for _ in 0..WARMUP {
        loop {
            if let Ok(mut claim) = prod.try_claim(payload_size) {
                claim.copy_from_slice(&payload);
                claim.commit();
                break;
            }
            std::hint::spin_loop();
        }
    }

    // Measured
    for _ in 0..samples_per_producer {
        let start = rdtscp();
        loop {
            if let Ok(mut claim) = prod.try_claim(payload_size) {
                claim.copy_from_slice(&payload);
                claim.commit();
                break;
            }
            std::hint::spin_loop();
        }
        let end = rdtscp();
        let _ = hist.record(end.wrapping_sub(start));
    }

    // Stop background threads
    running.store(false, Ordering::Relaxed);
    for h in bg_handles {
        h.join().unwrap();
    }
    cons_handle.join().unwrap();

    hist
}

/// Measure consumer latency
fn bench_consumer_latency(payload_size: usize) -> Histogram<u64> {
    let (mut prod, mut cons) = mpsc::new(BUFFER_SIZE);
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
        drop(record);
        let end = rdtscp();

        let _ = hist.record(end.wrapping_sub(start));
    }

    hist
}

/// Measure throughput with multiple producers
fn bench_throughput(payload_size: usize, num_producers: usize) -> f64 {
    const MESSAGES: u64 = 1_000_000;

    let (prod, mut cons) = mpsc::new(BUFFER_SIZE);
    let messages_per_producer = MESSAGES / num_producers as u64;

    let start = std::time::Instant::now();

    // Spawn producers
    let handles: Vec<_> = (0..num_producers)
        .map(|_| {
            let mut prod = prod.clone();
            let payload = vec![0xABu8; payload_size];
            thread::spawn(move || {
                for _ in 0..messages_per_producer {
                    loop {
                        if let Ok(mut claim) = prod.try_claim(payload_size) {
                            claim.copy_from_slice(&payload);
                            claim.commit();
                            break;
                        }
                        std::hint::spin_loop();
                    }
                }
            })
        })
        .collect();

    drop(prod);

    // Consumer
    let mut received = 0u64;
    while received < MESSAGES {
        if cons.try_claim().is_some() {
            received += 1;
        } else {
            std::hint::spin_loop();
        }
    }

    for h in handles {
        h.join().unwrap();
    }

    let elapsed = start.elapsed();
    MESSAGES as f64 / elapsed.as_secs_f64()
}

fn main() {
    println!("nexus-logbuf MPSC latency benchmark");
    println!("====================================");
    println!("Warmup: {}, Samples: {}", WARMUP, SAMPLES);
    println!();

    for &payload_size in &[8, 64, 256] {
        println!("Payload size: {} bytes", payload_size);
        println!("------------------------------------");

        let single_hist = bench_single_producer_latency(payload_size);
        print_stats("Single producer (no contention):", &single_hist);
        println!();

        let cons_hist = bench_consumer_latency(payload_size);
        print_stats("Consumer (claim+read+drop):", &cons_hist);
        println!();

        for &num_producers in &[2, 4] {
            let contended_hist = bench_contended_producer_latency(payload_size, num_producers);
            print_stats(
                &format!("Producer ({} contending):", num_producers),
                &contended_hist,
            );
            println!();
        }

        println!("Throughput:");
        for &num_producers in &[1, 2, 4] {
            let throughput = bench_throughput(payload_size, num_producers);
            println!(
                "  {} producer(s): {:.2}M msgs/sec",
                num_producers,
                throughput / 1_000_000.0
            );
        }
        println!();
        println!();
    }
}
