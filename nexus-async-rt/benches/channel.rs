//! Cycle-level latency benchmark for nexus-async-rt's local channel.
//!
//! Measures per-`send+recv` round-trip latency under the executor — i.e.
//! the cost of dispatch + channel ops + waker plumbing for the single-
//! threaded local channel.
//!
//! Pattern matches `nexus-queue/benches/bench_spsc.rs` (rdtscp + HDR
//! histogram, no criterion). The previous criterion-based version
//! collapsed each round-trip into wall-clock per-batch numbers; this
//! version captures the full distribution per operation.
//!
//! Build & run:
//!   cargo build --release -p nexus-async-rt --bench channel
//!   taskset -c 0 ./target/release/deps/channel-*

use std::cell::RefCell;
use std::hint::black_box;
use std::rc::Rc;
use std::thread;
use std::time::{Duration, Instant};

use hdrhistogram::Histogram;

use nexus_async_rt::channel::local;
use nexus_async_rt::{Runtime, spawn_boxed};
use nexus_rt::WorldBuilder;

const WARMUP: usize = 10_000;
const SAMPLES: usize = 100_000;

#[cfg(target_arch = "x86_64")]
#[inline]
fn rdtscp() -> u64 {
    // SAFETY: x86_64 intrinsic; the cfg attribute guarantees target_arch = "x86_64".
    unsafe {
        let mut aux: u32 = 0;
        core::arch::x86_64::__rdtscp(&raw mut aux)
    }
}

#[cfg(not(target_arch = "x86_64"))]
#[inline]
fn rdtscp() -> u64 {
    Instant::now().elapsed().as_nanos() as u64
}

fn run_channel_bench(label: &str, capacity: usize) {
    println!("=== {label} (cap={capacity}) ===");
    println!("Warmup:  {WARMUP:>8}");
    println!("Samples: {SAMPLES:>8}");
    println!();

    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    // Collect raw samples in the async block, then build the histogram
    // from them on the outer thread. Avoids holding any borrow across an
    // await point.
    let samples_cell = Rc::new(RefCell::new(Vec::<u64>::with_capacity(SAMPLES)));
    let samples_clone = samples_cell.clone();

    rt.block_on(async move {
        let (tx, rx) = local::channel::<u64>(capacity);

        let producer = spawn_boxed(async move {
            for i in 0..(WARMUP + SAMPLES) as u64 {
                tx.send(i).await.unwrap();
            }
        });
        // Detach — we drain the receiver below; producer completes
        // before block_on returns.
        std::mem::drop(producer);

        // Warmup
        for _ in 0..WARMUP {
            let v = rx.recv().await.unwrap();
            black_box(v);
        }

        // Measured samples — per-op latency
        for _ in 0..SAMPLES {
            let start = rdtscp();
            let v = rx.recv().await.unwrap();
            let end = rdtscp();
            black_box(v);
            samples_clone.borrow_mut().push(end.wrapping_sub(start));
        }
    });

    let mut h = Histogram::<u64>::new_with_max(1_000_000, 3).unwrap();
    for &s in samples_cell.borrow().iter() {
        let _ = h.record(s.min(1_000_000));
    }
    let h = &h;
    let cpu_ghz = estimate_cpu_freq_ghz();

    println!("Per-recv latency (cycles):");
    println!("  min:   {:>7}", h.min());
    println!("  mean:  {:>7.0}", h.mean());
    println!("  p50:   {:>7}", h.value_at_quantile(0.50));
    println!("  p90:   {:>7}", h.value_at_quantile(0.90));
    println!("  p99:   {:>7}", h.value_at_quantile(0.99));
    println!("  p999:  {:>7}", h.value_at_quantile(0.999));
    println!("  max:   {:>7}", h.max());
    println!();
    println!("Per-recv latency (nanoseconds, est {cpu_ghz:.2} GHz):");
    println!(
        "  p50:   {:>7.1} ns",
        h.value_at_quantile(0.50) as f64 / cpu_ghz
    );
    println!(
        "  p99:   {:>7.1} ns",
        h.value_at_quantile(0.99) as f64 / cpu_ghz
    );
    println!(
        "  p999:  {:>7.1} ns",
        h.value_at_quantile(0.999) as f64 / cpu_ghz
    );
    println!();
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
    println!("nexus-async-rt local channel benchmark");
    println!("======================================");
    println!();
    run_channel_bench("local async send+recv", 64);
    run_channel_bench("local async send+recv (small buffer, backpressure)", 4);
}
