#![allow(unused_mut, dropping_references)]
//! MPSC queue latency benchmark using rdtscp.
//!
//! Measures round-trip latency: producer pushes, consumer pops, records cycles.
//!
//! Run with:
//! ```bash
//! cargo build --release --example bench_mpsc
//! taskset -c 0,1 ./target/release/examples/bench_mpsc
//! ```

use hdrhistogram::Histogram;
use nexus_queue::mpsc;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;

const CAPACITY: usize = 1024;
const WARMUP: u64 = 100_000;
const SAMPLES: u64 = 1_000_000;

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
    let (mut tx, mut rx) = mpsc::ring_buffer::<u64>(CAPACITY);
    let done = Arc::new(AtomicBool::new(false));
    let done_clone = Arc::clone(&done);

    let consumer = thread::spawn(move || {
        let mut hist = Histogram::<u64>::new(3).unwrap();
        let mut count = 0u64;

        // Warmup
        while count < WARMUP {
            if let Some(start) = rx.pop() {
                let end = rdtscp();
                let _ = end.wrapping_sub(start);
                count += 1;
            } else {
                std::hint::spin_loop();
            }
        }

        // Measure
        count = 0;
        while count < SAMPLES {
            if let Some(start) = rx.pop() {
                let end = rdtscp();
                let elapsed = end.wrapping_sub(start);
                let _ = hist.record(elapsed.min(1_000_000));
                count += 1;
            } else {
                std::hint::spin_loop();
            }
        }

        done_clone.store(true, Ordering::Release);
        hist
    });

    let producer = thread::spawn(move || {
        while !done.load(Ordering::Acquire) {
            let start = rdtscp();
            while tx.push(start).is_err() {
                if done.load(Ordering::Acquire) {
                    return;
                }
                std::hint::spin_loop();
            }
        }
    });

    let hist = consumer.join().unwrap();
    producer.join().unwrap();
    hist
}

fn bench_nexus_mpsc_multi(num_producers: usize) -> Histogram<u64> {
    let (tx, mut rx) = mpsc::ring_buffer::<u64>(CAPACITY);
    let done = Arc::new(AtomicBool::new(false));
    let done_clone = Arc::clone(&done);

    let consumer = thread::spawn(move || {
        let mut hist = Histogram::<u64>::new(3).unwrap();
        let mut count = 0u64;
        let total = WARMUP + SAMPLES;

        // Combined warmup + measure
        while count < total {
            if let Some(start) = rx.pop() {
                let end = rdtscp();
                let elapsed = end.wrapping_sub(start);
                if count >= WARMUP {
                    let _ = hist.record(elapsed.min(1_000_000));
                }
                count += 1;
            } else {
                std::hint::spin_loop();
            }
        }

        done_clone.store(true, Ordering::Release);
        hist
    });

    let producers: Vec<_> = (0..num_producers)
        .map(|_| {
            let mut tx = tx.clone();
            let done = Arc::clone(&done);
            thread::spawn(move || {
                while !done.load(Ordering::Acquire) {
                    let start = rdtscp();
                    while tx.push(start).is_err() {
                        if done.load(Ordering::Acquire) {
                            return;
                        }
                        std::hint::spin_loop();
                    }
                }
            })
        })
        .collect();

    drop(tx); // Drop original

    let hist = consumer.join().unwrap();
    for p in producers {
        p.join().unwrap();
    }
    hist
}

fn bench_crossbeam_arrayqueue() -> Histogram<u64> {
    let queue = Arc::new(crossbeam_queue::ArrayQueue::<u64>::new(CAPACITY));
    let done = Arc::new(AtomicBool::new(false));
    let done_clone = Arc::clone(&done);
    let queue_consumer = Arc::clone(&queue);

    let consumer = thread::spawn(move || {
        let mut hist = Histogram::<u64>::new(3).unwrap();
        let mut count = 0u64;

        // Warmup
        while count < WARMUP {
            if let Some(start) = queue_consumer.pop() {
                let end = rdtscp();
                let _ = end.wrapping_sub(start);
                count += 1;
            } else {
                std::hint::spin_loop();
            }
        }

        // Measure
        count = 0;
        while count < SAMPLES {
            if let Some(start) = queue_consumer.pop() {
                let end = rdtscp();
                let elapsed = end.wrapping_sub(start);
                let _ = hist.record(elapsed.min(1_000_000));
                count += 1;
            } else {
                std::hint::spin_loop();
            }
        }

        done_clone.store(true, Ordering::Release);
        hist
    });

    let producer = thread::spawn(move || {
        while !done.load(Ordering::Acquire) {
            let start = rdtscp();
            while queue.push(start).is_err() {
                if done.load(Ordering::Acquire) {
                    return;
                }
                std::hint::spin_loop();
            }
        }
    });

    let hist = consumer.join().unwrap();
    producer.join().unwrap();
    hist
}

fn bench_crossbeam_arrayqueue_multi(num_producers: usize) -> Histogram<u64> {
    let queue = Arc::new(crossbeam_queue::ArrayQueue::<u64>::new(CAPACITY));
    let done = Arc::new(AtomicBool::new(false));
    let done_clone = Arc::clone(&done);
    let queue_consumer = Arc::clone(&queue);

    let consumer = thread::spawn(move || {
        let mut hist = Histogram::<u64>::new(3).unwrap();
        let mut count = 0u64;
        let total = WARMUP + SAMPLES;

        while count < total {
            if let Some(start) = queue_consumer.pop() {
                let end = rdtscp();
                let elapsed = end.wrapping_sub(start);
                if count >= WARMUP {
                    let _ = hist.record(elapsed.min(1_000_000));
                }
                count += 1;
            } else {
                std::hint::spin_loop();
            }
        }

        done_clone.store(true, Ordering::Release);
        hist
    });

    let producers: Vec<_> = (0..num_producers)
        .map(|_| {
            let queue = Arc::clone(&queue);
            let done = Arc::clone(&done);
            thread::spawn(move || {
                while !done.load(Ordering::Acquire) {
                    let start = rdtscp();
                    while queue.push(start).is_err() {
                        if done.load(Ordering::Acquire) {
                            return;
                        }
                        std::hint::spin_loop();
                    }
                }
            })
        })
        .collect();

    let hist = consumer.join().unwrap();
    for p in producers {
        p.join().unwrap();
    }
    hist
}

fn print_hist(name: &str, hist: &Histogram<u64>) {
    println!(
        "{:30} p50: {:4} cy   p99: {:5} cy   p999: {:5} cy   max: {:6} cy",
        name,
        hist.value_at_quantile(0.5),
        hist.value_at_quantile(0.99),
        hist.value_at_quantile(0.999),
        hist.max()
    );
}

fn main() {
    println!("MPSC Queue Latency Benchmark");
    println!("============================");
    println!(
        "Capacity: {}, Warmup: {}, Samples: {}",
        CAPACITY, WARMUP, SAMPLES
    );
    println!();

    // Single producer benchmarks
    println!("Single Producer:");
    println!("----------------");

    let hist = bench_nexus_mpsc();
    print_hist("nexus-queue mpsc", &hist);

    let hist = bench_crossbeam_arrayqueue();
    print_hist("crossbeam ArrayQueue", &hist);

    println!();

    // Multi-producer benchmarks
    for num_producers in [2, 4] {
        println!("{} Producers:", num_producers);
        println!("------------");

        let hist = bench_nexus_mpsc_multi(num_producers);
        print_hist("nexus-queue mpsc", &hist);

        let hist = bench_crossbeam_arrayqueue_multi(num_producers);
        print_hist("crossbeam ArrayQueue", &hist);

        println!();
    }
}
