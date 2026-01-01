// benches/profile_slot.rs
//! Latency and throughput benchmark for nexus_slot with comparisons
//!
//! Compares against:
//! - seqlock crate
//! - crossbeam ArrayQueue(1) with pop-before-push
//!
//! For best results, disable turbo boost and pin to physical cores:
//!   echo 1 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo
//!   sudo taskset -c 0,2 ./target/release/deps/profile_slot-*

use std::thread;
use std::time::{Duration, Instant};

use crossbeam_queue::ArrayQueue;
use hdrhistogram::Histogram;
use seqlock::SeqLock;
use std::sync::Arc;

use nexus_slot;

const WARMUP: usize = 100_000;
const SAMPLES: usize = 1_000_000;
const THROUGHPUT_WRITES: u64 = 10_000_000;

/// 64-byte cache-line sized message (Copy for seqlock compatibility)
#[derive(Clone, Copy)]
#[repr(C, align(64))]
struct Quote {
    sequence: u64,
    bid: f64,
    ask: f64,
    _padding: [u8; 40],
}

impl Default for Quote {
    fn default() -> Self {
        Self {
            sequence: Default::default(),
            bid: Default::default(),
            ask: Default::default(),
            _padding: [0; 40],
        }
    }
}

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

fn estimate_cpu_freq_ghz() -> f64 {
    let start_cycles = rdtscp();
    let start_time = Instant::now();
    thread::sleep(Duration::from_millis(10));
    let end_cycles = rdtscp();
    let elapsed = start_time.elapsed();
    end_cycles.wrapping_sub(start_cycles) as f64 / elapsed.as_nanos() as f64
}

// ============================================================================
// nexus_slot benchmark
// ============================================================================

fn bench_nexus_slot_latency() -> Histogram<u64> {
    let (mut writer_a, mut reader_a) = nexus_slot::slot::<Quote>();
    let (mut writer_b, mut reader_b) = nexus_slot::slot::<Quote>();

    let total = WARMUP + SAMPLES;

    let worker = thread::spawn(move || {
        for _ in 0..total {
            let msg = loop {
                if let Some(m) = reader_a.read() {
                    break m;
                }
                std::hint::spin_loop();
            };
            writer_b.write(msg);
        }
    });

    // Warmup
    for i in 0..WARMUP {
        writer_a.write(Quote {
            sequence: i as u64,
            ..Default::default()
        });
        while reader_b.read().is_none() {
            std::hint::spin_loop();
        }
    }

    let mut hist = Histogram::<u64>::new_with_max(1_000_000, 3).unwrap();

    for i in 0..SAMPLES {
        let start = rdtscp();

        writer_a.write(Quote {
            sequence: (WARMUP + i) as u64,
            ..Default::default()
        });

        while reader_b.read().is_none() {
            std::hint::spin_loop();
        }

        let elapsed = rdtscp().wrapping_sub(start) / 2;
        let _ = hist.record(elapsed.min(1_000_000));
    }

    worker.join().unwrap();
    hist
}

fn bench_nexus_slot_throughput() -> (Duration, u64) {
    let (mut writer, mut reader) = nexus_slot::slot::<Quote>();

    let start = Instant::now();

    let writer_handle = thread::spawn(move || {
        for i in 0..THROUGHPUT_WRITES {
            writer.write(Quote {
                sequence: i,
                ..Default::default()
            });
        }
    });

    let reader_handle = thread::spawn(move || {
        let mut reads = 0u64;

        loop {
            if let Some(q) = reader.read() {
                reads += 1;
                if q.sequence >= THROUGHPUT_WRITES - 1 {
                    break;
                }
            } else if reader.is_disconnected() {
                break;
            } else {
                std::hint::spin_loop();
            }
        }
        reads
    });

    writer_handle.join().unwrap();
    let reads = reader_handle.join().unwrap();

    (start.elapsed(), reads)
}

// ============================================================================
// seqlock crate benchmark
// ============================================================================

fn bench_seqlock_latency() -> Histogram<u64> {
    let lock_a = Arc::new(SeqLock::new(Quote::default()));
    let lock_b = Arc::new(SeqLock::new(Quote::default()));
    let flag_a = Arc::new(std::sync::atomic::AtomicU64::new(0));
    let flag_b = Arc::new(std::sync::atomic::AtomicU64::new(0));

    let total = WARMUP + SAMPLES;

    let lock_a_clone = Arc::clone(&lock_a);
    let lock_b_clone = Arc::clone(&lock_b);
    let flag_a_clone = Arc::clone(&flag_a);
    let flag_b_clone = Arc::clone(&flag_b);

    let worker = thread::spawn(move || {
        for i in 0..total {
            // Wait for new value
            while flag_a_clone.load(std::sync::atomic::Ordering::Acquire) != i as u64 + 1 {
                std::hint::spin_loop();
            }
            let msg = lock_a_clone.read();
            // Echo back
            {
                let mut guard = lock_b_clone.lock_write();
                *guard = msg;
            }
            flag_b_clone.store(i as u64 + 1, std::sync::atomic::Ordering::Release);
        }
    });

    // Warmup
    for i in 0..WARMUP {
        {
            let mut guard = lock_a.lock_write();
            *guard = Quote {
                sequence: i as u64,
                ..Default::default()
            };
        }
        flag_a.store(i as u64 + 1, std::sync::atomic::Ordering::Release);

        while flag_b.load(std::sync::atomic::Ordering::Acquire) != i as u64 + 1 {
            std::hint::spin_loop();
        }
        let _ = lock_b.read();
    }

    let mut hist = Histogram::<u64>::new_with_max(1_000_000, 3).unwrap();

    for i in 0..SAMPLES {
        let idx = WARMUP + i;
        let start = rdtscp();

        {
            let mut guard = lock_a.lock_write();
            *guard = Quote {
                sequence: idx as u64,
                ..Default::default()
            };
        }
        flag_a.store(idx as u64 + 1, std::sync::atomic::Ordering::Release);

        while flag_b.load(std::sync::atomic::Ordering::Acquire) != idx as u64 + 1 {
            std::hint::spin_loop();
        }
        let _ = lock_b.read();

        let elapsed = rdtscp().wrapping_sub(start) / 2;
        let _ = hist.record(elapsed.min(1_000_000));
    }

    worker.join().unwrap();
    hist
}

// ============================================================================
// crossbeam ArrayQueue(1) benchmark
// ============================================================================

fn bench_arrayqueue_latency() -> Histogram<u64> {
    let queue_a = Arc::new(ArrayQueue::<Quote>::new(1));
    let queue_b = Arc::new(ArrayQueue::<Quote>::new(1));

    let total = WARMUP + SAMPLES;

    let queue_a_clone = Arc::clone(&queue_a);
    let queue_b_clone = Arc::clone(&queue_b);

    let worker = thread::spawn(move || {
        for _ in 0..total {
            let msg = loop {
                if let Some(m) = queue_a_clone.pop() {
                    break m;
                }
                std::hint::spin_loop();
            };
            // Force push: pop then push if full
            while queue_b_clone.push(msg).is_err() {
                let _ = queue_b_clone.pop();
            }
        }
    });

    // Warmup
    for i in 0..WARMUP {
        let msg = Quote {
            sequence: i as u64,
            ..Default::default()
        };
        while queue_a.push(msg).is_err() {
            let _ = queue_a.pop();
        }
        while queue_b.pop().is_none() {
            std::hint::spin_loop();
        }
    }

    let mut hist = Histogram::<u64>::new_with_max(1_000_000, 3).unwrap();

    for i in 0..SAMPLES {
        let start = rdtscp();

        let msg = Quote {
            sequence: (WARMUP + i) as u64,
            ..Default::default()
        };
        while queue_a.push(msg).is_err() {
            let _ = queue_a.pop();
        }

        while queue_b.pop().is_none() {
            std::hint::spin_loop();
        }

        let elapsed = rdtscp().wrapping_sub(start) / 2;
        let _ = hist.record(elapsed.min(1_000_000));
    }

    worker.join().unwrap();
    hist
}

// ============================================================================
// Main
// ============================================================================

fn print_histogram(name: &str, hist: &Histogram<u64>, cpu_ghz: f64) {
    println!("{}:", name);
    println!("  Cycles:");
    println!("    min:   {:>7}", hist.min());
    println!("    p50:   {:>7}", hist.value_at_quantile(0.50));
    println!("    p99:   {:>7}", hist.value_at_quantile(0.99));
    println!("    p999:  {:>7}", hist.value_at_quantile(0.999));
    println!("    max:   {:>7}", hist.max());
    println!("  Nanoseconds:");
    println!("    min:   {:>7.1} ns", hist.min() as f64 / cpu_ghz);
    println!(
        "    p50:   {:>7.1} ns",
        hist.value_at_quantile(0.50) as f64 / cpu_ghz
    );
    println!(
        "    p99:   {:>7.1} ns",
        hist.value_at_quantile(0.99) as f64 / cpu_ghz
    );
    println!(
        "    p999:  {:>7.1} ns",
        hist.value_at_quantile(0.999) as f64 / cpu_ghz
    );
    println!("    max:   {:>7.1} ns", hist.max() as f64 / cpu_ghz);
    println!();
}

fn main() {
    println!("nexus-slot Benchmark");
    println!("====================");
    println!();
    println!("Warmup:  {}", WARMUP);
    println!("Samples: {}", SAMPLES);
    println!();

    let cpu_ghz = estimate_cpu_freq_ghz();
    println!("Estimated CPU freq: {:.2} GHz", cpu_ghz);
    println!();

    // Latency benchmarks
    println!("=== Ping-Pong Latency (RTT/2) ===");
    println!();

    let nexus_hist = bench_nexus_slot_latency();
    print_histogram("nexus_slot", &nexus_hist, cpu_ghz);

    let seqlock_hist = bench_seqlock_latency();
    print_histogram("seqlock crate", &seqlock_hist, cpu_ghz);

    let arrayqueue_hist = bench_arrayqueue_latency();
    print_histogram("ArrayQueue(1)", &arrayqueue_hist, cpu_ghz);

    // Comparison summary
    println!("=== Latency Summary (p50 cycles) ===");
    println!(
        "  nexus_slot:   {:>5} cycles",
        nexus_hist.value_at_quantile(0.50)
    );
    println!(
        "  seqlock:      {:>5} cycles ({:.1}x)",
        seqlock_hist.value_at_quantile(0.50),
        seqlock_hist.value_at_quantile(0.50) as f64 / nexus_hist.value_at_quantile(0.50) as f64
    );
    println!(
        "  ArrayQueue:   {:>5} cycles ({:.1}x)",
        arrayqueue_hist.value_at_quantile(0.50),
        arrayqueue_hist.value_at_quantile(0.50) as f64 / nexus_hist.value_at_quantile(0.50) as f64
    );
    println!();

    // Throughput benchmark
    println!("=== Throughput (Write-Heavy) ===");
    println!("Writes: {}", THROUGHPUT_WRITES);
    println!();

    let (elapsed, reads) = bench_nexus_slot_throughput();
    let writes_per_sec = THROUGHPUT_WRITES as f64 / elapsed.as_secs_f64();

    println!("nexus_slot:");
    println!("  Time:       {:>10.2?}", elapsed);
    println!("  Writes/sec: {:>10.2} M/sec", writes_per_sec / 1_000_000.0);
    println!(
        "  Reads:      {:>10} ({:.1}x conflation)",
        reads,
        THROUGHPUT_WRITES as f64 / reads as f64
    );
}
