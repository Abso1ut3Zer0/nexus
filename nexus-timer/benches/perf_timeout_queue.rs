//! TimeoutQueue cycle-level benchmark.
//!
//! The point of `TimeoutQueue` is that poll is O(fired), not O(population).
//! This bench proves it *and* reports honest per-op costs.
//!
//! ## Why two methods
//!
//! These operations cost tens of cycles. A single-op `rdtsc` bracket
//! (`lfence;rdtsc` … op … `rdtscp;lfence`) has a floor of ~20-30 cycles — the
//! cost of measuring *nothing* — added to every sample and impossible to
//! subtract cleanly from a distribution. At these scales that floor dominates
//! and inflates the absolute numbers.
//!
//! So we report:
//!   1. the **measurement floor** itself, so the percentile rows are interpretable;
//!   2. **amortized cycles/op** — N ops between one `rdtsc` pair, divided by N,
//!      best of several runs — which drives the floor to ~0 and gives the true
//!      steady-state cost;
//!   3. **percentile tails** (single-op) for the distribution shape — inflated by
//!      the floor, but the *shape* (and the flat-across-population property) is
//!      what matters there.
//!
//! Run pinned, turbo disabled, best of a few:
//!   cargo build --release --bench perf_timeout_queue -p nexus-timer
//!   taskset -c 0 ./target/release/deps/perf_timeout_queue-*

use std::hint::black_box;
use std::mem;
use std::time::{Duration, Instant};

use nexus_timer::{TimeoutQueue, TimerHandle};

const SAMPLES: usize = 50_000;
const WARMUP: usize = 5_000;
const POPULATIONS: [usize; 4] = [100, 1_000, 10_000, 50_000];
const K_DUE: usize = 10; // batch fired per k-due poll

// Amortized measurement: many ops per rdtsc pair, best of a few runs.
const AMORT_ITERS: u64 = 200_000;
const AMORT_RUNS: usize = 7;

// =============================================================================
// Timing infrastructure
// =============================================================================

#[inline(always)]
fn rdtsc_start() -> u64 {
    // SAFETY: x86_64 intrinsic; benchmark runs on x86_64 only.
    unsafe {
        std::arch::x86_64::_mm_lfence();
        std::arch::x86_64::_rdtsc()
    }
}

#[inline(always)]
fn rdtsc_end() -> u64 {
    // SAFETY: x86_64 intrinsic; benchmark runs on x86_64 only.
    unsafe {
        let tsc = std::arch::x86_64::__rdtscp(&mut 0u32 as *mut _);
        std::arch::x86_64::_mm_lfence();
        tsc
    }
}

fn percentile(sorted: &[u64], p: f64) -> u64 {
    let idx = ((sorted.len() as f64) * p / 100.0) as usize;
    sorted[idx.min(sorted.len() - 1)]
}

fn print_row(label: &str, samples: &mut [u64]) {
    samples.sort_unstable();
    println!(
        "  {:<34} p50={:>5}  p90={:>5}  p99={:>6}  p999={:>7}  max={:>8}",
        label,
        percentile(samples, 50.0),
        percentile(samples, 90.0),
        percentile(samples, 99.0),
        percentile(samples, 99.9),
        samples[samples.len() - 1],
    );
}

/// True per-op cost: run `f` `iters` times between one rdtsc pair, divide by
/// `iters`, take the best (lowest) of `AMORT_RUNS`. The per-pair rdtsc floor is
/// amortized to ~0, so this is the steady-state work, not the instrument.
fn amortized_per_op(iters: u64, mut f: impl FnMut()) -> f64 {
    let mut best = f64::INFINITY;
    for _ in 0..AMORT_RUNS {
        let s = rdtsc_start();
        for _ in 0..iters {
            f();
        }
        let e = rdtsc_end();
        let per = e.wrapping_sub(s) as f64 / iters as f64;
        if per < best {
            best = per;
        }
    }
    best
}

fn print_amort(label: &str, cycles: f64) {
    println!("  {label:<34} {cycles:>6.1} cycles/op");
}

fn timeout(secs: u64) -> Duration {
    Duration::from_secs(secs)
}

fn main() {
    let now = Instant::now();
    println!("TIMEOUT LIST — cycle-level bench");
    println!("================================================================");

    // ── Measurement floor: an empty single-op rdtsc bracket ─────────────
    // This is the ~20-30 cycles baked into every percentile row below. The
    // amortized rows do NOT include it.
    {
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            let s = rdtsc_start();
            black_box(0u64);
            let e = rdtsc_end();
            black_box(e.wrapping_sub(s));
        }
        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            black_box(0u64);
            let e = rdtsc_end();
            samples.push(e.wrapping_sub(s));
        }
        samples.sort_unstable();
        let floor_amort = amortized_per_op(AMORT_ITERS, || {
            black_box(0u64);
        });
        println!(
            "\nmeasurement floor (empty single-op bracket): p50={} min={} cycles",
            percentile(&samples, 50.0),
            samples[0],
        );
        println!("  loop overhead (amortized empty body):        {floor_amort:>6.1} cycles/op");
        println!(
            "  → the TAIL rows below include the ~{}-cycle floor; the TRUE COST rows do not.",
            percentile(&samples, 50.0),
        );
    }

    // ── TRUE PER-OP COST (amortized, floor-free) ────────────────────────
    println!("\nTRUE PER-OP COST  (amortized over {AMORT_ITERS} ops, best of {AMORT_RUNS}):");

    // schedule + cancel (paired) — self-cleaning, list stays ~empty.
    {
        let mut list: TimeoutQueue<u64> = TimeoutQueue::unbounded(timeout(3600), 4096, now);
        let c = amortized_per_op(AMORT_ITERS, || {
            let h = list.schedule(now, 0);
            black_box(list.cancel(h));
        });
        print_amort("schedule + cancel (paired)", c);
    }

    // schedule_forget — pure insert. Fresh, pre-sized list per run (no slab
    // growth mid-measurement); list drops between runs.
    {
        let mut best = f64::INFINITY;
        for _ in 0..AMORT_RUNS {
            let mut list: TimeoutQueue<u64> =
                TimeoutQueue::unbounded(timeout(3600), AMORT_ITERS as usize + 16, now);
            let s = rdtsc_start();
            for _ in 0..AMORT_ITERS {
                list.schedule_forget(now, 0);
            }
            let e = rdtsc_end();
            best = best.min(e.wrapping_sub(s) as f64 / AMORT_ITERS as f64);
        }
        print_amort("schedule_forget", best);
    }

    // nothing-due poll, per population — MUST be flat (O(1), no scan).
    for &pop in &POPULATIONS {
        let mut list: TimeoutQueue<u64> = TimeoutQueue::unbounded(timeout(3600), pop + 16, now);
        let mut handles: Vec<TimerHandle<u64>> = Vec::with_capacity(pop);
        for i in 0..pop {
            handles.push(list.schedule(now, i as u64));
        }
        let poll_at = now + Duration::from_millis(1); // nothing due
        let mut buf = Vec::new();
        let c = amortized_per_op(AMORT_ITERS, || {
            black_box(list.poll(black_box(poll_at), &mut buf));
        });
        print_amort(&format!("poll nothing-due @{pop} live"), c);
        for h in handles {
            mem::forget(h);
        }
    }

    // ── TAIL DISTRIBUTION (single-op rdtsc; includes the floor) ─────────
    println!("\nTAIL DISTRIBUTION  (single-op rdtsc, {SAMPLES} samples — includes the floor):");

    // schedule + cancel (paired)
    {
        let mut list: TimeoutQueue<u64> = TimeoutQueue::unbounded(timeout(3600), 4096, now);
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            let h = list.schedule(now, 0);
            black_box(list.cancel(h));
        }
        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            let h = list.schedule(now, 0);
            black_box(list.cancel(h));
            let e = rdtsc_end();
            samples.push(e.wrapping_sub(s));
        }
        print_row("schedule + cancel (paired)", &mut samples);
    }

    // nothing-due poll, per population
    for &pop in &POPULATIONS {
        let mut list: TimeoutQueue<u64> = TimeoutQueue::unbounded(timeout(3600), pop + 16, now);
        let mut handles: Vec<TimerHandle<u64>> = Vec::with_capacity(pop);
        for i in 0..pop {
            handles.push(list.schedule(now, i as u64));
        }
        let poll_at = now + Duration::from_millis(1);
        let mut buf = Vec::new();
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            black_box(list.poll(poll_at, &mut buf));
        }
        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            black_box(list.poll(poll_at, &mut buf));
            let e = rdtsc_end();
            samples.push(e.wrapping_sub(s));
        }
        print_row(&format!("poll nothing-due @{pop} live"), &mut samples);
        for h in handles {
            mem::forget(h);
        }
    }

    // k-due poll: fire K_DUE out of `pop` live. Each sample rebuilds the
    // population, so this stays single-op — but the op fires 10 entries, so
    // the floor is a small fraction of the reading.
    for &pop in &POPULATIONS {
        let due_at = now;
        let not_due_at = now + Duration::from_secs(1);
        let poll_at = now + Duration::from_secs(3600) + Duration::from_millis(1);
        let iters = (SAMPLES / 20).max(1);
        let mut samples = Vec::with_capacity(iters);
        for _ in 0..(iters / 10).max(1) {
            let mut list: TimeoutQueue<u64> = TimeoutQueue::unbounded(timeout(3600), pop + 16, now);
            for i in 0..K_DUE {
                list.schedule_forget(due_at, i as u64);
            }
            for i in K_DUE..pop {
                list.schedule_forget(not_due_at, i as u64);
            }
            let mut buf = Vec::with_capacity(K_DUE);
            black_box(list.poll_with_limit(poll_at, K_DUE, &mut buf));
        }
        for _ in 0..iters {
            let mut list: TimeoutQueue<u64> = TimeoutQueue::unbounded(timeout(3600), pop + 16, now);
            for i in 0..K_DUE {
                list.schedule_forget(due_at, i as u64);
            }
            for i in K_DUE..pop {
                list.schedule_forget(not_due_at, i as u64);
            }
            let mut buf = Vec::with_capacity(K_DUE);
            let s = rdtsc_start();
            let fired = black_box(list.poll_with_limit(poll_at, K_DUE, &mut buf));
            let e = rdtsc_end();
            debug_assert_eq!(fired, K_DUE);
            samples.push(e.wrapping_sub(s));
        }
        print_row(&format!("poll {K_DUE}-due @{pop} live"), &mut samples);
    }
}
