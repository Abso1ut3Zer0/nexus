//! Latency and throughput benchmark for crossbeam-channel
//!
//! For best results, disable turbo boost and pin to physical cores:
//!   echo 1 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo
//!   sudo taskset -c 0,2 ./target/release/deps/profile_crossbeam_channel-*

use std::thread;
use std::time::{Duration, Instant};

use crossbeam_channel::bounded;
use hdrhistogram::Histogram;

const WARMUP: usize = 1_000_000;
const SAMPLES: usize = 100_000_000;
const CAPACITY: usize = 1024;
const THROUGHPUT_COUNT: u64 = 10_000_000;

#[cfg(target_arch = "x86_64")]
#[inline]
fn rdtscp() -> u64 {
    unsafe {
        let mut aux: u32 = 0;
        core::arch::x86_64::__rdtscp(&mut aux)
    }
}

#[cfg(not(target_arch = "x86_64"))]
#[inline]
fn rdtscp() -> u64 {
    Instant::now().elapsed().as_nanos() as u64
}

fn latency_benchmark() {
    println!("=== Latency Benchmark (ping-pong RTT/2) ===");
    println!("Warmup:   {:>8}", WARMUP);
    println!("Samples:  {:>8}", SAMPLES);
    println!("Capacity: {:>8}", CAPACITY);
    println!();

    let (tx_a, rx_a) = bounded::<u64>(CAPACITY);
    let (tx_b, rx_b) = bounded::<u64>(CAPACITY);

    let total = WARMUP + SAMPLES;

    // Worker: receive on A, send back on B
    let handle = thread::spawn(move || {
        for _ in 0..total {
            let val = rx_a.recv().unwrap();
            tx_b.send(val).unwrap();
        }
    });

    // Warmup
    for _ in 0..WARMUP {
        tx_a.send(0).unwrap();
        rx_b.recv().unwrap();
    }

    // Measured samples
    let mut hist = Histogram::<u64>::new_with_max(1_000_000, 3).unwrap();

    for _ in 0..SAMPLES {
        let start = rdtscp();

        tx_a.send(0).unwrap();
        rx_b.recv().unwrap();

        let end = rdtscp();
        let latency = end.wrapping_sub(start) / 2;
        let _ = hist.record(latency.min(1_000_000));
    }

    handle.join().unwrap();

    let cpu_ghz = estimate_cpu_freq_ghz();

    println!("One-way latency (cycles):");
    println!("  min:   {:>7}", hist.min());
    println!("  mean:  {:>7.0}", hist.mean());
    println!("  p50:   {:>7}", hist.value_at_quantile(0.50));
    println!("  p90:   {:>7}", hist.value_at_quantile(0.90));
    println!("  p99:   {:>7}", hist.value_at_quantile(0.99));
    println!("  p999:  {:>7}", hist.value_at_quantile(0.999));
    println!("  p9999: {:>7}", hist.value_at_quantile(0.9999));
    println!("  max:   {:>7}", hist.max());
    println!();

    println!("Estimated CPU freq: {:.2} GHz", cpu_ghz);
    println!();

    println!("One-way latency (nanoseconds):");
    println!("  min:   {:>7.1} ns", hist.min() as f64 / cpu_ghz);
    println!("  mean:  {:>7.1} ns", hist.mean() / cpu_ghz);
    println!(
        "  p50:   {:>7.1} ns",
        hist.value_at_quantile(0.50) as f64 / cpu_ghz
    );
    println!(
        "  p90:   {:>7.1} ns",
        hist.value_at_quantile(0.90) as f64 / cpu_ghz
    );
    println!(
        "  p99:   {:>7.1} ns",
        hist.value_at_quantile(0.99) as f64 / cpu_ghz
    );
    println!(
        "  p999:  {:>7.1} ns",
        hist.value_at_quantile(0.999) as f64 / cpu_ghz
    );
    println!(
        "  p9999: {:>7.1} ns",
        hist.value_at_quantile(0.9999) as f64 / cpu_ghz
    );
    println!("  max:   {:>7.1} ns", hist.max() as f64 / cpu_ghz);
}

fn throughput_benchmark() {
    println!("=== Throughput Benchmark ===");
    println!("Messages: {:>10}", THROUGHPUT_COUNT);
    println!("Capacity: {:>10}", CAPACITY);
    println!();

    let (tx, rx) = bounded::<u64>(CAPACITY);

    let start = Instant::now();

    let producer = thread::spawn(move || {
        for i in 0..THROUGHPUT_COUNT {
            tx.send(i).unwrap();
        }
    });

    let consumer = thread::spawn(move || {
        let mut sum = 0u64;
        for _ in 0..THROUGHPUT_COUNT {
            sum = sum.wrapping_add(rx.recv().unwrap());
        }
        sum
    });

    producer.join().unwrap();
    let sum = consumer.join().unwrap();

    let elapsed = start.elapsed();

    let expected_sum = THROUGHPUT_COUNT * (THROUGHPUT_COUNT - 1) / 2;
    assert_eq!(sum, expected_sum);

    let msgs_per_sec = THROUGHPUT_COUNT as f64 / elapsed.as_secs_f64();
    let ns_per_msg = elapsed.as_nanos() as f64 / THROUGHPUT_COUNT as f64;

    println!("Results:");
    println!("  Total time:  {:>10.2?}", elapsed);
    println!(
        "  Throughput:  {:>10.2} M msgs/sec",
        msgs_per_sec / 1_000_000.0
    );
    println!("  Per message: {:>10.1} ns", ns_per_msg);
}

fn estimate_cpu_freq_ghz() -> f64 {
    let start_cycles = rdtscp();
    let start_time = Instant::now();

    thread::sleep(Duration::from_millis(10));

    let end_cycles = rdtscp();
    let elapsed = start_time.elapsed();

    end_cycles.wrapping_sub(start_cycles) as f64 / elapsed.as_nanos() as f64
}

fn main() {
    println!("crossbeam-channel Benchmark");
    println!("===========================");
    println!();

    latency_benchmark();
    println!();
    println!();
    throughput_benchmark();
}
