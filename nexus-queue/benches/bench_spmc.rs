#![allow(unused_mut, dropping_references)]
//! SPMC queue latency and throughput benchmark.
//!
//! Two benchmarks:
//! 1. Ping-pong: True one-way latency (RTT/2) with single consumer
//! 2. Fan-out throughput: Total msgs/sec with N consumers
//!
//! Run with:
//! ```bash
//! cargo build --release --example bench_spmc
//! taskset -c 0,2,4,6,8 ./target/release/examples/bench_spmc
//! ```

use crossbeam_queue::ArrayQueue;
use hdrhistogram::Histogram;
use nexus_queue::spmc;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::thread;
use std::time::Instant;

const WARMUP: u64 = 10_000;
const SAMPLES: u64 = 100_000;
const THROUGHPUT_MSGS: u64 = 10_000_000;

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

// ============================================================================
// Ping-Pong Latency (single consumer, RTT/2)
// ============================================================================

fn pingpong_nexus_spmc() -> Histogram<u64> {
    let (mut tx_fwd, mut rx_fwd) = spmc::ring_buffer::<u64>(1024);
    let (mut tx_back, mut rx_back) = spmc::ring_buffer::<()>(1024);

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

fn pingpong_crossbeam() -> Histogram<u64> {
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

// ============================================================================
// Fan-out Throughput (N consumers)
// ============================================================================

fn throughput_nexus_spmc(num_consumers: usize) -> f64 {
    let (mut tx, rx) = spmc::ring_buffer::<u64>(1024);
    let total = Arc::new(AtomicU64::new(0));

    let consumers: Vec<_> = (0..num_consumers)
        .map(|_| {
            let mut rx = rx.clone();
            let total = Arc::clone(&total);
            thread::spawn(move || {
                let mut count = 0u64;
                loop {
                    if rx.pop().is_some() {
                        count += 1;
                    } else if rx.is_disconnected() {
                        while rx.pop().is_some() {
                            count += 1;
                        }
                        break;
                    } else {
                        std::hint::spin_loop();
                    }
                }
                total.fetch_add(count, Ordering::Relaxed);
            })
        })
        .collect();

    drop(rx);

    let start = Instant::now();
    for i in 0..THROUGHPUT_MSGS {
        while tx.push(i).is_err() {
            std::hint::spin_loop();
        }
    }
    drop(tx);

    for c in consumers {
        c.join().unwrap();
    }
    let elapsed = start.elapsed();

    let received = total.load(Ordering::Relaxed);
    assert_eq!(received, THROUGHPUT_MSGS);

    received as f64 / elapsed.as_secs_f64()
}

fn throughput_crossbeam(num_consumers: usize) -> f64 {
    let queue = Arc::new(ArrayQueue::<u64>::new(1024));
    let done = Arc::new(AtomicBool::new(false));
    let total = Arc::new(AtomicU64::new(0));

    let consumers: Vec<_> = (0..num_consumers)
        .map(|_| {
            let queue = Arc::clone(&queue);
            let done = Arc::clone(&done);
            let total = Arc::clone(&total);
            thread::spawn(move || {
                let mut count = 0u64;
                loop {
                    if queue.pop().is_some() {
                        count += 1;
                    } else if done.load(Ordering::Acquire) {
                        while queue.pop().is_some() {
                            count += 1;
                        }
                        break;
                    } else {
                        std::hint::spin_loop();
                    }
                }
                total.fetch_add(count, Ordering::Relaxed);
            })
        })
        .collect();

    let start = Instant::now();
    for i in 0..THROUGHPUT_MSGS {
        while queue.push(i).is_err() {
            std::hint::spin_loop();
        }
    }
    done.store(true, Ordering::Release);

    for c in consumers {
        c.join().unwrap();
    }
    let elapsed = start.elapsed();

    let received = total.load(Ordering::Relaxed);
    assert_eq!(received, THROUGHPUT_MSGS);

    received as f64 / elapsed.as_secs_f64()
}

fn cy_to_ns(cycles: u64, freq_ghz: f64) -> String {
    if freq_ghz > 0.0 {
        format!("{:5.1} ns", cycles as f64 / freq_ghz)
    } else {
        "   n/a".to_string()
    }
}

fn print_hist(name: &str, hist: &Histogram<u64>, freq_ghz: f64) {
    let p50 = hist.value_at_quantile(0.5);
    let p99 = hist.value_at_quantile(0.99);
    let p999 = hist.value_at_quantile(0.999);

    println!(
        "  {}: p50: {:4} cy ({})   p99: {:4} cy ({})   p999: {:5} cy ({})",
        name,
        p50,
        cy_to_ns(p50, freq_ghz),
        p99,
        cy_to_ns(p99, freq_ghz),
        p999,
        cy_to_ns(p999, freq_ghz),
    );
}

fn main() {
    println!("SPMC Queue Benchmark");
    println!("====================\n");

    // Estimate CPU frequency from TSC (x86_64 only)
    let start_time = Instant::now();
    let start_tsc = rdtscp();
    thread::sleep(std::time::Duration::from_millis(100));
    let end_tsc = rdtscp();
    let elapsed = start_time.elapsed();
    let tsc_delta = end_tsc.saturating_sub(start_tsc);
    let freq_ghz = if tsc_delta > 0 {
        tsc_delta as f64 / elapsed.as_nanos() as f64
    } else {
        0.0
    };
    if freq_ghz > 0.0 {
        println!("CPU freq: {:.2} GHz\n", freq_ghz);
    } else {
        println!("CPU freq: unavailable (non-x86_64)\n");
    }

    // --- Ping-pong latency ---
    println!("Ping-Pong Latency (single consumer, RTT/2):");
    println!("---------------------------------------------");

    let hist = pingpong_nexus_spmc();
    print_hist("nexus-queue SPMC", &hist, freq_ghz);

    let hist = pingpong_crossbeam();
    print_hist("crossbeam ArrayQueue", &hist, freq_ghz);

    println!();

    // --- Fan-out throughput ---
    println!("Fan-out Throughput ({} msgs):", THROUGHPUT_MSGS);
    println!("----------------------------------");

    for n in [1, 2, 4] {
        let nexus_mps = throughput_nexus_spmc(n);
        let crossbeam_mps = throughput_crossbeam(n);

        println!(
            "  {} consumer(s):  nexus {:7.2} M/s   crossbeam {:7.2} M/s   ({:+.1}%)",
            n,
            nexus_mps / 1_000_000.0,
            crossbeam_mps / 1_000_000.0,
            ((nexus_mps - crossbeam_mps) / crossbeam_mps) * 100.0,
        );
    }
}
