//! Sync pool benchmark: acquire/return latency with cross-thread returns
//!
//! Measures cycle-accurate latency for sync pool operations using rdtscp.
//! Tests with varying numbers of returner threads to measure CAS contention.

use hdrhistogram::Histogram;
use nexus_pool::sync::{Pool, Pooled};
use std::hint::black_box;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, mpsc};
use std::thread;

const CAPACITY: usize = 1_000;
const OPERATIONS: usize = 100_000;

#[inline(always)]
fn rdtscp() -> u64 {
    #[cfg(target_arch = "x86_64")]
    // SAFETY: x86_64 intrinsic; benchmark runs on x86_64 only.
    unsafe {
        let mut aux: u32 = 0;
        std::arch::x86_64::__rdtscp(&raw mut aux)
    }
    #[cfg(not(target_arch = "x86_64"))]
    panic!("rdtscp only supported on x86_64");
}

struct Stats {
    acquire: Histogram<u64>,
    release: Histogram<u64>,
}

impl Stats {
    fn new() -> Self {
        Self {
            acquire: Histogram::new(3).unwrap(),
            release: Histogram::new(3).unwrap(),
        }
    }

    fn print(&self, name: &str) {
        println!("{}:", name);
        println!(
            "  ACQUIRE: p50={:>4}  p99={:>4}  p999={:>5}  max={:>8}  (n={})",
            self.acquire.value_at_quantile(0.50),
            self.acquire.value_at_quantile(0.99),
            self.acquire.value_at_quantile(0.999),
            self.acquire.max(),
            self.acquire.len()
        );
        println!(
            "  RELEASE: p50={:>4}  p99={:>4}  p999={:>5}  max={:>8}  (n={})",
            self.release.value_at_quantile(0.50),
            self.release.value_at_quantile(0.99),
            self.release.value_at_quantile(0.999),
            self.release.max(),
            self.release.len()
        );
    }
}

/// Baseline: acquire and release on same thread (no cross-thread)
fn bench_same_thread() -> Stats {
    let pool: Pool<Vec<u8>> = Pool::new(CAPACITY, || Vec::with_capacity(1024), Vec::clear);

    let mut stats = Stats::new();

    for _ in 0..OPERATIONS {
        let start = rdtscp();
        let guard = pool.try_acquire().unwrap();
        let mid = rdtscp();

        black_box(guard.capacity());

        drop(guard);
        let end = rdtscp();

        let _ = stats.acquire.record(mid.wrapping_sub(start));
        let _ = stats.release.record(end.wrapping_sub(mid));
    }

    stats
}

/// Cross-thread: acquire on main, return on N worker threads
fn bench_cross_thread(num_returners: usize) -> Stats {
    let pool: Pool<Vec<u8>> = Pool::new(CAPACITY, || Vec::with_capacity(1024), Vec::clear);

    let mut stats = Stats::new();
    let done = Arc::new(AtomicBool::new(false));
    let items_returned = Arc::new(AtomicUsize::new(0));

    // Channel to send (item, acquire_time) to workers
    let (tx, rx) = mpsc::channel::<(Pooled<Vec<u8>>, u64)>();
    let rx = Arc::new(std::sync::Mutex::new(rx));

    // Histogram for release times (collected by workers)
    let release_times = Arc::new(std::sync::Mutex::new(Vec::with_capacity(OPERATIONS)));

    thread::scope(|s| {
        // Spawn returner threads
        for _ in 0..num_returners {
            let rx = Arc::clone(&rx);
            let done = Arc::clone(&done);
            let items_returned = Arc::clone(&items_returned);
            let release_times = Arc::clone(&release_times);

            s.spawn(move || {
                loop {
                    let item = {
                        let rx = rx.lock().unwrap();
                        rx.recv()
                    };

                    match item {
                        Ok((guard, _acquire_time)) => {
                            black_box(guard.capacity());

                            let start = rdtscp();
                            drop(guard);
                            let end = rdtscp();

                            release_times.lock().unwrap().push(end.wrapping_sub(start));
                            items_returned.fetch_add(1, Ordering::Relaxed);
                        }
                        Err(_) => {
                            if done.load(Ordering::Relaxed) {
                                break;
                            }
                        }
                    }
                }
            });
        }

        // Main thread: acquire and send to workers
        let mut sent = 0;
        while sent < OPERATIONS {
            let start = rdtscp();
            if let Some(guard) = pool.try_acquire() {
                let end = rdtscp();
                let _ = stats.acquire.record(end.wrapping_sub(start));

                tx.send((guard, end)).unwrap();
                sent += 1;
            } else {
                // Pool exhausted, yield to let workers return items
                thread::yield_now();
            }
        }

        // Signal done and wait for workers to finish
        drop(tx);
        done.store(true, Ordering::Relaxed);

        // Wait for all items to be returned
        while items_returned.load(Ordering::Relaxed) < OPERATIONS {
            thread::yield_now();
        }
    });

    // Collect release times into histogram
    let release_times = release_times.lock().unwrap();
    for &time in release_times.iter() {
        let _ = stats.release.record(time);
    }

    stats
}

/// Contention test: all threads return simultaneously
/// Runs multiple rounds to stress the CAS loop
fn bench_concurrent_return(num_returners: usize) -> Stats {
    const ROUNDS: usize = 100;
    let items_per_thread = CAPACITY / num_returners;

    let pool: Pool<Vec<u8>> = Pool::new(CAPACITY, || Vec::with_capacity(1024), Vec::clear);

    let mut stats = Stats::new();

    // Barrier for synchronized start of each round
    let barrier = Arc::new(std::sync::Barrier::new(num_returners + 1)); // +1 for main thread
    let release_times: Arc<std::sync::Mutex<Vec<u64>>> =
        Arc::new(std::sync::Mutex::new(Vec::with_capacity(CAPACITY * ROUNDS)));

    thread::scope(|s| {
        // Channels to distribute items to workers
        let mut senders: Vec<mpsc::SyncSender<Vec<Pooled<Vec<u8>>>>> = Vec::new();

        for _ in 0..num_returners {
            let (tx, rx) = mpsc::sync_channel::<Vec<Pooled<Vec<u8>>>>(1);
            senders.push(tx);

            let barrier = Arc::clone(&barrier);
            let release_times = Arc::clone(&release_times);

            s.spawn(move || {
                while let Ok(items) = rx.recv() {
                    // Wait for all threads to have their items
                    barrier.wait();

                    // Now drop all items as fast as possible
                    let mut local_times = Vec::with_capacity(items.len());
                    for item in items {
                        let start = rdtscp();
                        drop(item);
                        let end = rdtscp();
                        local_times.push(end.wrapping_sub(start));
                    }

                    release_times.lock().unwrap().extend(local_times);

                    // Sync at end of round
                    barrier.wait();
                }
            });
        }

        // Main thread: run multiple rounds
        for _ in 0..ROUNDS {
            // Acquire all items
            let mut all_items: Vec<Pooled<Vec<u8>>> = Vec::with_capacity(CAPACITY);
            for _ in 0..CAPACITY {
                let start = rdtscp();
                let item = pool.try_acquire().unwrap();
                let end = rdtscp();
                let _ = stats.acquire.record(end.wrapping_sub(start));
                all_items.push(item);
            }

            // Distribute to workers
            let mut iter = all_items.into_iter();
            for tx in &senders {
                let chunk: Vec<_> = iter.by_ref().take(items_per_thread).collect();
                tx.send(chunk).unwrap();
            }

            // Signal workers to start (they're waiting at barrier)
            barrier.wait();

            // Wait for workers to finish
            barrier.wait();
        }

        // Close channels to signal workers to exit
        drop(senders);
    });

    // Collect release times
    let release_times = release_times.lock().unwrap();
    for &time in release_times.iter() {
        let _ = stats.release.record(time);
    }

    stats
}

fn main() {
    println!("SYNC POOL BENCHMARK");
    println!("Capacity: {}, Operations: {}", CAPACITY, OPERATIONS);
    println!("================================================================\n");

    println!("PART 1: SEQUENTIAL ACCESS (channel-based)\n");

    let same_thread = bench_same_thread();
    let cross_1 = bench_cross_thread(1);
    let cross_2 = bench_cross_thread(2);
    let cross_4 = bench_cross_thread(4);

    same_thread.print("Same thread (baseline)");
    println!();
    cross_1.print("Cross-thread (1 returner)");
    println!();
    cross_2.print("Cross-thread (2 returners)");
    println!();
    cross_4.print("Cross-thread (4 returners)");
    println!();

    println!("================================================================");
    println!("PART 2: CONCURRENT RETURN (barrier-synchronized, stresses CAS)\n");

    let conc_1 = bench_concurrent_return(1);
    let conc_2 = bench_concurrent_return(2);
    let conc_4 = bench_concurrent_return(4);

    conc_1.print("Concurrent return (1 thread)");
    println!();
    conc_2.print("Concurrent return (2 threads)");
    println!();
    conc_4.print("Concurrent return (4 threads)");
    println!();

    println!("================================================================");
    println!("SUMMARY (cycles):");
    println!("----------------------------------------------------------------");
    println!("Sequential access (channel-based):");
    println!("              Same-Thread   1-Returner   2-Returners  4-Returners");
    println!(
        "  ACQUIRE p50:    {:>4}          {:>4}          {:>4}          {:>4}",
        same_thread.acquire.value_at_quantile(0.50),
        cross_1.acquire.value_at_quantile(0.50),
        cross_2.acquire.value_at_quantile(0.50),
        cross_4.acquire.value_at_quantile(0.50),
    );
    println!(
        "  RELEASE p50:    {:>4}          {:>4}          {:>4}          {:>4}",
        same_thread.release.value_at_quantile(0.50),
        cross_1.release.value_at_quantile(0.50),
        cross_2.release.value_at_quantile(0.50),
        cross_4.release.value_at_quantile(0.50),
    );
    println!();
    println!("Concurrent return (barrier-synchronized, measures CAS contention):");
    println!("              1-Thread     2-Threads    4-Threads");
    println!(
        "  RELEASE p50:    {:>4}          {:>4}          {:>4}",
        conc_1.release.value_at_quantile(0.50),
        conc_2.release.value_at_quantile(0.50),
        conc_4.release.value_at_quantile(0.50),
    );
    println!(
        "  RELEASE p99:    {:>4}          {:>4}          {:>4}",
        conc_1.release.value_at_quantile(0.99),
        conc_2.release.value_at_quantile(0.99),
        conc_4.release.value_at_quantile(0.99),
    );
    println!(
        "  RELEASE p999:   {:>4}          {:>4}          {:>4}",
        conc_1.release.value_at_quantile(0.999),
        conc_2.release.value_at_quantile(0.999),
        conc_4.release.value_at_quantile(0.999),
    );
    println!(
        "  (n=)          {:>6}        {:>6}        {:>6}",
        conc_1.release.len(),
        conc_2.release.len(),
        conc_4.release.len(),
    );

    println!();
    println!("NOTE: Concurrent return is the true CAS contention test.");
    println!("      Sequential access is limited by channel throughput.");
}
