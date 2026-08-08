//! Cycle-level latency benchmark for nexus-async-rt's executor dispatch.
//!
//! Measures per-iteration cost of (spawn → block_on → return) for an
//! immediately-completing future. This is the hottest path most users
//! see when treating an async task as a callback.
//!
//! Pattern matches `nexus-queue/benches/bench_spsc.rs` (rdtscp + HDR).
//! The previous criterion-based version referenced an `Executor::spawn`
//! API that no longer exists — this rewrite targets the current
//! `Runtime` + `spawn_boxed` surface.
//!
//! Build & run:
//!   cargo build --release -p nexus-async-rt --bench executor
//!   taskset -c 0 ./target/release/deps/executor-*

use std::future::Future;
use std::hint::black_box;
use std::pin::Pin;
use std::task::{Context, Poll};
use std::thread;
use std::time::{Duration, Instant};

use hdrhistogram::Histogram;

use nexus_async_rt::{Runtime, spawn_boxed};
use nexus_rt::WorldBuilder;

const WARMUP: usize = 10_000;
const SAMPLES: usize = 100_000;

/// Polls per sample for the amortized per-poll-cycle benchmark.
/// Large enough that block_on entry/exit and the one-time task
/// lifecycle amortize to <0.1 cy per poll.
const POLLS_PER_SAMPLE: usize = 10_000;

/// Tasks spawned per sample for the amortized per-task-lifecycle
/// benchmark. Large enough that block_on overhead and the join-loop
/// machinery amortize to noise.
const TASKS_PER_SAMPLE: usize = 1_000;

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

fn block_on_immediate() {
    println!("=== block_on(async {{ ... }}) — immediate future ===");
    println!("Warmup:  {WARMUP:>8}");
    println!("Samples: {SAMPLES:>8}");
    println!();

    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    // Warmup
    for _ in 0..WARMUP {
        rt.block_on(async {
            black_box(42u64);
        });
    }

    let mut hist = Histogram::<u64>::new_with_max(10_000_000, 3).unwrap();
    for _ in 0..SAMPLES {
        let start = rdtscp();
        rt.block_on(async {
            black_box(42u64);
        });
        let end = rdtscp();
        let _ = hist.record(end.wrapping_sub(start).min(10_000_000));
    }

    print_hist(&hist, "block_on cost");
}

fn spawn_then_join() {
    println!("=== block_on(async {{ spawn_boxed(...).await }}) ===");
    println!("Warmup:  {WARMUP:>8}");
    println!("Samples: {SAMPLES:>8}");
    println!();

    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    // Warmup
    for _ in 0..WARMUP {
        rt.block_on(async {
            spawn_boxed(async {
                black_box(42u64);
            })
            .await;
        });
    }

    let mut hist = Histogram::<u64>::new_with_max(10_000_000, 3).unwrap();
    for _ in 0..SAMPLES {
        let start = rdtscp();
        rt.block_on(async {
            spawn_boxed(async {
                black_box(42u64);
            })
            .await;
        });
        let end = rdtscp();
        let _ = hist.record(end.wrapping_sub(start).min(10_000_000));
    }

    print_hist(&hist, "spawn+join cost");
}

fn print_hist(hist: &Histogram<u64>, label: &str) {
    let cpu_ghz = estimate_cpu_freq_ghz();

    println!("{label} (cycles):");
    println!("  min:   {:>9}", hist.min());
    println!("  mean:  {:>9.0}", hist.mean());
    println!("  p50:   {:>9}", hist.value_at_quantile(0.50));
    println!("  p90:   {:>9}", hist.value_at_quantile(0.90));
    println!("  p99:   {:>9}", hist.value_at_quantile(0.99));
    println!("  p999:  {:>9}", hist.value_at_quantile(0.999));
    println!("  max:   {:>9}", hist.max());
    println!();
    println!("{label} (nanoseconds, est {cpu_ghz:.2} GHz):");
    println!(
        "  p50:   {:>9.1} ns",
        hist.value_at_quantile(0.50) as f64 / cpu_ghz
    );
    println!(
        "  p99:   {:>9.1} ns",
        hist.value_at_quantile(0.99) as f64 / cpu_ghz
    );
    println!(
        "  p999:  {:>9.1} ns",
        hist.value_at_quantile(0.999) as f64 / cpu_ghz
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

// =============================================================================
// Amortized per-poll-cycle benchmarks
// =============================================================================
//
// `block_on(immediate)` and `spawn_then_join` measure full block_on
// round-trips, which include block_on entry/exit and (for spawn_then_join)
// the per-task allocation lifecycle. Neither isolates "what does it cost
// the runtime to poll a future during steady-state operation?"
//
// The Countdown future below re-arms itself via `wake_by_ref` each poll and
// returns Pending until its counter hits zero. With N >> 1, block_on
// entry/exit and the one-shot setup amortize to negligible per-cycle cost.
//
// Two variants — they measure DIFFERENT waker paths:
//
// `root_poll_cycle_amortized`: Countdown is the root future of block_on, so
//   `cx.waker()` inside Countdown::poll is the `RootWake` waker (mio-backed).
//   wake_by_ref sets a flag and pokes mio's eventfd, costing one write()
//   syscall per cycle. This measures the "root future yields back to the
//   runtime" path, which is what `async fn main()` -style code hits.
//
// `task_poll_cycle_amortized`: Countdown is spawned as a task via
//   `spawn_boxed` and awaited from the root. `cx.waker()` inside Countdown::poll
//   is the task waker (data ptr = task pointer, vtable = `waker::VTABLE`).
//   wake_by_ref goes through `waker::wake_impl` → pushes to executor's
//   ready queue. No syscall. This is the path that matters for spawned
//   work, and the path issue #237 was concerned about.

struct Countdown {
    n: usize,
}

impl Future for Countdown {
    type Output = ();
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        if self.n == 0 {
            return Poll::Ready(());
        }
        self.n -= 1;
        // Re-arm: tell the executor to poll us again immediately. This is
        // the wake path that drives the per-poll cycle measurement.
        cx.waker().wake_by_ref();
        Poll::Pending
    }
}

fn root_poll_cycle_amortized() {
    println!("=== per-poll-cycle (root Countdown, RootWake path, amortized) ===");
    println!("Polls per sample: {POLLS_PER_SAMPLE}");
    println!("Samples:          {SAMPLES}");
    println!();

    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    // Warmup
    for _ in 0..WARMUP {
        rt.block_on(Countdown { n: 100 });
    }

    let mut hist = Histogram::<u64>::new_with_max(10_000_000, 3).unwrap();
    for _ in 0..SAMPLES {
        let start = rdtscp();
        rt.block_on(Countdown {
            n: POLLS_PER_SAMPLE,
        });
        let end = rdtscp();
        let total = end.wrapping_sub(start);
        // Per-poll cost = total cycles / (N+1) polls (+1 for the final Ready
        // poll). Truncate; HDR resolution is 3 sig figs so single-cycle
        // precision isn't meaningful anyway.
        let per_poll = total / (POLLS_PER_SAMPLE as u64 + 1);
        let _ = hist.record(per_poll.min(10_000_000));
    }

    print_hist(&hist, "per-poll-cycle (root waker path)");
}

fn task_poll_cycle_amortized() {
    println!("=== per-poll-cycle (spawned Countdown, task waker path, amortized) ===");
    println!("Polls per sample: {POLLS_PER_SAMPLE}");
    println!("Samples:          {SAMPLES}");
    println!();

    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    // Warmup
    for _ in 0..WARMUP {
        rt.block_on(async {
            spawn_boxed(Countdown { n: 100 }).await;
        });
    }

    let mut hist = Histogram::<u64>::new_with_max(10_000_000, 3).unwrap();
    for _ in 0..SAMPLES {
        let start = rdtscp();
        rt.block_on(async {
            spawn_boxed(Countdown {
                n: POLLS_PER_SAMPLE,
            })
            .await;
        });
        let end = rdtscp();
        let total = end.wrapping_sub(start);
        // +1 for the final Ready poll. spawn + JoinHandle resolve amortizes
        // to ~0.1cy across POLLS_PER_SAMPLE polls.
        let per_poll = total / (POLLS_PER_SAMPLE as u64 + 1);
        let _ = hist.record(per_poll.min(10_000_000));
    }

    print_hist(&hist, "per-poll-cycle (task waker path)");
}

fn tokio_localset_task_poll_cycle() {
    println!("=== per-poll-cycle (tokio LocalSet + spawn_local, amortized) ===");
    println!("Polls per sample: {POLLS_PER_SAMPLE}");
    println!("Samples:          {SAMPLES}");
    println!();

    let rt = tokio::runtime::Builder::new_current_thread()
        .build()
        .unwrap();
    let local = tokio::task::LocalSet::new();

    // Warmup
    for _ in 0..WARMUP {
        rt.block_on(local.run_until(async {
            tokio::task::spawn_local(Countdown { n: 100 })
                .await
                .unwrap();
        }));
    }

    let mut hist = Histogram::<u64>::new_with_max(10_000_000, 3).unwrap();
    for _ in 0..SAMPLES {
        let start = rdtscp();
        rt.block_on(local.run_until(async {
            tokio::task::spawn_local(Countdown {
                n: POLLS_PER_SAMPLE,
            })
            .await
            .unwrap();
        }));
        let end = rdtscp();
        let total = end.wrapping_sub(start);
        let per_poll = total / (POLLS_PER_SAMPLE as u64 + 1);
        let _ = hist.record(per_poll.min(10_000_000));
    }

    print_hist(&hist, "per-poll-cycle (tokio LocalSet path)");
}

// =============================================================================
// Amortized per-task-lifecycle benchmark
// =============================================================================
//
// Spawns N immediately-completing tasks inside one block_on, awaits all of
// them, divides total cycles by N. Captures the per-task lifecycle cost
// (allocation + spawn + first poll → Ready + handle resolve) without the
// per-block_on entry/exit overhead that dominates `spawn_then_join`.
//
// Compare to `spawn_then_join`: same operation, but one task per block_on
// instead of N. The delta between the two numbers tells you how much of
// `spawn_then_join`'s 758-cycle floor is block_on overhead vs actual
// task lifecycle.

fn task_lifecycle_amortized() {
    println!("=== per-task-lifecycle (N spawn+join inside one block_on) ===");
    println!("Tasks per sample: {TASKS_PER_SAMPLE}");
    println!("Samples:          {SAMPLES}");
    println!();

    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::new(&mut world);

    // Warmup
    for _ in 0..WARMUP {
        rt.block_on(async {
            let mut handles = Vec::with_capacity(100);
            for _ in 0..100 {
                handles.push(spawn_boxed(async {
                    black_box(42u64);
                }));
            }
            for h in handles {
                h.await;
            }
        });
    }

    let mut hist = Histogram::<u64>::new_with_max(10_000_000, 3).unwrap();
    for _ in 0..SAMPLES {
        let start = rdtscp();
        rt.block_on(async {
            let mut handles = Vec::with_capacity(TASKS_PER_SAMPLE);
            for _ in 0..TASKS_PER_SAMPLE {
                handles.push(spawn_boxed(async {
                    black_box(42u64);
                }));
            }
            for h in handles {
                h.await;
            }
        });
        let end = rdtscp();
        let total = end.wrapping_sub(start);
        let per_task = total / TASKS_PER_SAMPLE as u64;
        let _ = hist.record(per_task.min(10_000_000));
    }

    print_hist(&hist, "per-task-lifecycle (spawn + poll + complete + join)");
}

fn main() {
    println!("nexus-async-rt executor benchmark");
    println!("=================================");
    println!();
    block_on_immediate();
    spawn_then_join();
    root_poll_cycle_amortized();
    task_poll_cycle_amortized();
    tokio_localset_task_poll_cycle();
    task_lifecycle_amortized();
}
