#![allow(unused_mut, dropping_references)]
//! MPSC ping-pong latency benchmark (matches SPSC methodology).
//!
//! Measures true round-trip: producer sends, consumer responds, producer measures.

use crossbeam_queue::ArrayQueue;
use hdrhistogram::Histogram;
use nexus_queue::mpsc;
use std::sync::Arc;
use std::thread;

const WARMUP: u64 = 10_000;
const SAMPLES: u64 = 100_000;

#[cfg(target_arch = "x86_64")]
#[inline]
fn rdtscp() -> u64 {
    let mut aux: u32 = 0;
    // SAFETY: x86_64 intrinsic; function is only compiled for x86_64.
    unsafe { core::arch::x86_64::__rdtscp(&raw mut aux) }
}

#[cfg(not(target_arch = "x86_64"))]
#[inline]
fn rdtscp() -> u64 {
    0
}

fn bench_nexus_mpsc() -> Histogram<u64> {
    let (mut tx_fwd, mut rx_fwd) = mpsc::ring_buffer::<u64>(1024);
    let (mut tx_back, mut rx_back) = mpsc::ring_buffer::<()>(1024);

    let consumer = thread::spawn(move || {
        for _ in 0..(WARMUP + SAMPLES) {
            loop {
                if rx_fwd.pop().is_some() {
                    break;
                }
                std::hint::spin_loop();
            }
            while tx_back.push(()).is_err() {
                std::hint::spin_loop();
            }
        }
    });

    let mut hist = Histogram::<u64>::new(3).unwrap();

    // Warmup
    for _ in 0..WARMUP {
        while tx_fwd.push(0).is_err() {
            std::hint::spin_loop();
        }
        loop {
            if rx_back.pop().is_some() {
                break;
            }
            std::hint::spin_loop();
        }
    }

    // Measure
    for _ in 0..SAMPLES {
        let start = rdtscp();
        while tx_fwd.push(start).is_err() {
            std::hint::spin_loop();
        }
        loop {
            if rx_back.pop().is_some() {
                break;
            }
            std::hint::spin_loop();
        }
        let end = rdtscp();
        let _ = hist.record((end - start) / 2);
    }

    consumer.join().unwrap();
    hist
}

fn bench_crossbeam() -> Histogram<u64> {
    let fwd = Arc::new(ArrayQueue::<u64>::new(1024));
    let back = Arc::new(ArrayQueue::<()>::new(1024));

    let fwd_rx = Arc::clone(&fwd);
    let back_tx = Arc::clone(&back);

    let consumer = thread::spawn(move || {
        for _ in 0..(WARMUP + SAMPLES) {
            loop {
                if fwd_rx.pop().is_some() {
                    break;
                }
                std::hint::spin_loop();
            }
            while back_tx.push(()).is_err() {
                std::hint::spin_loop();
            }
        }
    });

    let mut hist = Histogram::<u64>::new(3).unwrap();

    // Warmup
    for _ in 0..WARMUP {
        while fwd.push(0).is_err() {
            std::hint::spin_loop();
        }
        loop {
            if back.pop().is_some() {
                break;
            }
            std::hint::spin_loop();
        }
    }

    // Measure
    for _ in 0..SAMPLES {
        let start = rdtscp();
        while fwd.push(start).is_err() {
            std::hint::spin_loop();
        }
        loop {
            if back.pop().is_some() {
                break;
            }
            std::hint::spin_loop();
        }
        let end = rdtscp();
        let _ = hist.record((end - start) / 2);
    }

    consumer.join().unwrap();
    hist
}

fn print_hist(name: &str, hist: &Histogram<u64>, freq_ghz: f64) {
    let p50 = hist.value_at_quantile(0.5);
    let p99 = hist.value_at_quantile(0.99);
    let p999 = hist.value_at_quantile(0.999);

    println!("{}:", name);
    println!(
        "  p50: {:4} cy ({:5.1} ns)   p99: {:4} cy ({:5.1} ns)   p999: {:5} cy ({:6.1} ns)",
        p50,
        p50 as f64 / freq_ghz,
        p99,
        p99 as f64 / freq_ghz,
        p999,
        p999 as f64 / freq_ghz
    );
}

fn main() {
    println!("MPSC Ping-Pong Latency Benchmark");
    println!("=================================\n");

    // Estimate CPU frequency
    let start_time = std::time::Instant::now();
    let start_tsc = rdtscp();
    std::thread::sleep(std::time::Duration::from_millis(100));
    let end_tsc = rdtscp();
    let elapsed = start_time.elapsed();
    let freq_ghz = (end_tsc - start_tsc) as f64 / elapsed.as_nanos() as f64;
    println!("CPU freq: {:.2} GHz\n", freq_ghz);

    println!("One-way latency (RTT/2):");
    println!("------------------------");

    let nexus_hist = bench_nexus_mpsc();
    print_hist("nexus-queue MPSC", &nexus_hist, freq_ghz);

    let crossbeam_hist = bench_crossbeam();
    print_hist("crossbeam ArrayQueue", &crossbeam_hist, freq_ghz);
}
