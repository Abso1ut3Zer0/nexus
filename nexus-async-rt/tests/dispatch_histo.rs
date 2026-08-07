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
//! Per-poll (not batched) histogram for nexus-async-rt dispatch.
//! Shows exactly which polls are slow and by how much.
//!
//! Run with:
//!   cargo test -p nexus-async-rt --release --test dispatch_histo -- --ignored --nocapture

use std::cell::Cell;
use std::future::Future;
use std::pin::Pin;
use std::rc::Rc;
use std::task::{Context, Poll};

use nexus_async_rt::Executor;

const WARMUP: usize = 10_000;
const SAMPLES: usize = 500_000;

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

/// Self-waking future that records entry+exit timestamps per poll.
struct InstrumentedTask {
    count: u64,
    target: u64,
    /// Pairs of (poll_entry, poll_exit) timestamps.
    /// We record entry at the START of poll, exit at the END.
    /// The gap between consecutive entries = executor overhead.
    entries: Rc<Cell<Vec<u64>>>,
}

impl Future for InstrumentedTask {
    type Output = ();
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        let entry = rdtscp();
        let mut v = self.entries.take();
        v.push(entry);
        self.entries.set(v);

        self.count += 1;
        if self.count >= self.target {
            return Poll::Ready(());
        }
        cx.waker().wake_by_ref();
        Poll::Pending
    }
}

#[test]
#[ignore]
fn dispatch_per_poll_histogram() {
    let total = (WARMUP + SAMPLES) as u64;
    let entries = Rc::new(Cell::new(Vec::with_capacity(total as usize)));
    let e = entries.clone();

    let mut executor = Executor::new(4);
    executor.spawn_boxed(InstrumentedTask {
        count: 0,
        target: total,
        entries: e,
    });

    while executor.task_count() > 0 {
        executor.poll();
    }

    let timestamps = entries.take();
    // Compute inter-poll gaps (consecutive entry timestamps).
    // Gap = time from one poll entry to the next = executor overhead
    // + wake_by_ref + queue management.
    let data = &timestamps[WARMUP..];
    let mut gaps: Vec<u64> = data.windows(2).map(|w| w[1].wrapping_sub(w[0])).collect();

    gaps.sort_unstable();
    let len = gaps.len();

    println!("\n=== Per-Poll Dispatch Latency ({SAMPLES} samples, post-warmup) ===\n");

    let p50 = gaps[len / 2];
    let p90 = gaps[len * 90 / 100];
    let p95 = gaps[len * 95 / 100];
    let p99 = gaps[len * 99 / 100];
    let p995 = gaps[len * 995 / 1000];
    let p999 = gaps[len * 999 / 1000];
    let p9999 = gaps[len * 9999 / 10000];
    let min = gaps[0];
    let max = gaps[len - 1];

    println!("  min:    {min:>6} cy");
    println!("  p50:    {p50:>6} cy");
    println!("  p90:    {p90:>6} cy");
    println!("  p95:    {p95:>6} cy");
    println!("  p99:    {p99:>6} cy");
    println!("  p99.5:  {p995:>6} cy");
    println!("  p999:   {p999:>6} cy");
    println!("  p9999:  {p9999:>6} cy");
    println!("  max:    {max:>6} cy");

    // Histogram: bucket by cycle range.
    println!("\n  Histogram (cycle ranges):\n");
    let buckets = [
        (0, 30, "0-30"),
        (30, 50, "30-50"),
        (50, 70, "50-70"),
        (70, 100, "70-100"),
        (100, 150, "100-150"),
        (150, 200, "150-200"),
        (200, 300, "200-300"),
        (300, 500, "300-500"),
        (500, 1000, "500-1000"),
        (1000, 5000, "1000-5000"),
        (5000, u64::MAX, "5000+"),
    ];

    for (lo, hi, label) in buckets {
        let count = gaps.iter().filter(|&&g| g >= lo && g < hi).count();
        let pct = count as f64 / len as f64 * 100.0;
        let bar_len = (pct * 0.5) as usize; // scale bar
        let bar: String = "#".repeat(bar_len.min(50));
        println!("    {label:>10}: {count:>8} ({pct:>6.2}%) {bar}");
    }

    // Show the top 20 slowest polls.
    println!("\n  Top 20 slowest polls (cycles):");
    for (i, &g) in gaps[len - 20..].iter().enumerate() {
        println!("    #{:>2}: {g} cy", len - 20 + i + 1);
    }

    // Filtered distribution: drop samples > 500 cy (kernel noise).
    // Shows the true userspace dispatch distribution.
    let mut filtered: Vec<u64> = gaps.iter().copied().filter(|&g| g <= 500).collect();
    filtered.sort_unstable();
    let flen = filtered.len();
    let dropped = len - flen;
    let drop_pct = dropped as f64 / len as f64 * 100.0;

    println!("\n  === Filtered (≤500 cy, kernel noise removed) ===");
    println!("  Dropped {dropped} samples ({drop_pct:.3}%)\n");

    let fp50 = filtered[flen / 2];
    let fp90 = filtered[flen * 90 / 100];
    let fp95 = filtered[flen * 95 / 100];
    let fp99 = filtered[flen * 99 / 100];
    let fp995 = filtered[flen * 995 / 1000];
    let fp999 = filtered[flen * 999 / 1000];
    let fmin = filtered[0];
    let fmax = filtered[flen - 1];

    println!("  min:    {fmin:>6} cy");
    println!("  p50:    {fp50:>6} cy");
    println!("  p90:    {fp90:>6} cy");
    println!("  p95:    {fp95:>6} cy");
    println!("  p99:    {fp99:>6} cy");
    println!("  p99.5:  {fp995:>6} cy");
    println!("  p999:   {fp999:>6} cy");
    println!("  max:    {fmax:>6} cy (userspace ceiling)");
}
