#![allow(
    unused_must_use,
    unused_imports,
    dead_code,
    unknown_lints,
    clippy::float_cmp,
    clippy::ref_option,
    clippy::used_underscore_binding,
    clippy::redundant_locals,
    clippy::semicolon_if_nothing_returned,
    clippy::let_underscore_future,
    clippy::while_let_loop,
    clippy::needless_continue,
    clippy::match_wild_err_arm,
    clippy::collection_is_never_read,
    clippy::async_yields_async,
    clippy::match_same_arms
)]
#![cfg(target_arch = "x86_64")]
//! Pure dispatch overhead comparison: nexus-async-rt vs tokio LocalSet.
//!
//! No IO, no syscalls. A persistent task self-wakes and we measure
//! per-poll cycle cost via batched rdtsc.
//!
//! Run with:
//!   cargo test -p nexus-async-rt --release --test vs_tokio_dispatch -- --ignored --nocapture --test-threads=1

use std::cell::Cell;
use std::future::Future;
use std::pin::Pin;
use std::rc::Rc;
use std::task::{Context, Poll};

const WARMUP: usize = 10_000;
const TOTAL_POLLS: usize = 210_000; // warmup + measurement
const BATCH: usize = 100;

#[inline(always)]
fn rdtsc() -> u64 {
    // SAFETY: x86_64 intrinsic; the file-level cfg(target_arch = "x86_64") guarantees the target.
    unsafe { core::arch::x86_64::_rdtsc() }
}

#[inline(always)]
fn rdtscp() -> u64 {
    // SAFETY: x86_64 intrinsic; the file-level cfg(target_arch = "x86_64") guarantees the target.
    unsafe {
        let mut aux: u32 = 0;
        let tsc = core::arch::x86_64::__rdtscp(&raw mut aux);
        core::arch::x86_64::_mm_lfence();
        tsc
    }
}

fn print_distribution(name: &str, samples: &mut [u64]) {
    samples.sort_unstable();
    let len = samples.len();
    if len == 0 {
        println!("{name}: NO SAMPLES");
        return;
    }
    let p50 = samples[len / 2];
    let p90 = samples[len * 90 / 100];
    let p99 = samples[len * 99 / 100];
    let p999 = samples[len * 999 / 1000];
    let p9999 = samples[len.saturating_sub(1).min(len * 9999 / 10000)];
    let min = samples[0];
    let max = samples[len - 1];
    println!(
        "{name:<45} min:{min:>5}  p50:{p50:>5}  p90:{p90:>5}  p99:{p99:>5}  p999:{p999:>5}  p9999:{p9999:>5}  max:{max:>7}"
    );
}

/// Self-waking future that completes after `target` polls.
/// Records rdtscp timestamp on every poll.
struct BenchTask {
    count: u64,
    target: u64,
    timestamps: Rc<Cell<Vec<u64>>>,
}

impl Future for BenchTask {
    type Output = ();
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        let now = rdtscp();
        let mut ts = self.timestamps.take();
        ts.push(now);
        self.timestamps.set(ts);

        self.count += 1;
        if self.count >= self.target {
            return Poll::Ready(());
        }
        cx.waker().wake_by_ref();
        Poll::Pending
    }
}

fn compute_batched_samples(timestamps: &[u64], warmup: usize, batch: usize) -> Vec<u64> {
    let data = &timestamps[warmup..];
    let mut samples = Vec::with_capacity(data.len() / batch);
    for chunk in data.chunks(batch) {
        if chunk.len() < 2 {
            continue;
        }
        let elapsed = chunk.last().unwrap().wrapping_sub(chunk[0]);
        samples.push(elapsed / chunk.len() as u64);
    }
    samples
}

// =============================================================================
// nexus-async-rt
// =============================================================================

#[test]
#[ignore]
fn dispatch_nexus_vs_tokio() {
    println!("\n=== Pure Dispatch Overhead: nexus-async-rt vs tokio LocalSet ===");
    println!("=== No IO, no syscalls — pure userspace dispatch ===");
    println!("=== Batched rdtsc ({BATCH}/sample), all values in cycles ===\n");

    // --- nexus ---
    {
        use nexus_async_rt::Executor;

        let timestamps = Rc::new(Cell::new(Vec::with_capacity(TOTAL_POLLS)));
        let ts = timestamps.clone();

        let mut executor = Executor::new(4);
        executor.spawn_boxed(BenchTask {
            count: 0,
            target: TOTAL_POLLS as u64,
            timestamps: ts,
        });

        // Drive the executor directly — no Runtime, no mio, no timers.
        while executor.task_count() > 0 {
            executor.poll();
        }

        let ts = timestamps.take();
        let mut samples = compute_batched_samples(&ts, WARMUP, BATCH);
        print_distribution("nexus-async-rt (self-wake)", &mut samples);
    }

    // --- tokio ---
    {
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
        let local = tokio::task::LocalSet::new();

        let timestamps = Rc::new(Cell::new(Vec::with_capacity(TOTAL_POLLS)));
        let ts = timestamps.clone();

        local.block_on(&rt, async move {
            tokio::task::spawn_local(BenchTask {
                count: 0,
                target: TOTAL_POLLS as u64,
                timestamps: ts,
            })
            .await
            .unwrap();
        });

        let ts = timestamps.take();
        let mut samples = compute_batched_samples(&ts, WARMUP, BATCH);
        print_distribution("tokio LocalSet (self-wake)", &mut samples);
    }

    println!();
    println!("  Measures: wake_by_ref (queue push) + dequeue + poll_fn call");
    println!("  Lower = faster dispatch machinery");
}
