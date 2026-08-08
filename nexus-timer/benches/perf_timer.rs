//! Timer wheel cycle-level benchmark.
//!
//! Measures per-operation latency for the core timer wheel hot paths:
//! schedule, cancel, poll, and paired schedule+cancel.
//!
//! Run with:
//!   cargo build --release --example perf_timer -p nexus-timer
//!   taskset -c 0 ./target/release/examples/perf_timer

use std::hint::black_box;
use std::mem;
use std::time::{Duration, Instant};

use nexus_timer::Wheel;

const SAMPLES: usize = 50_000;
const WARMUP: usize = 5_000;
const POLL_BATCH: usize = 100;
const STEADY_SIZE: usize = 100_000;

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
        "  {:<30} p50={:>4}  p90={:>4}  p99={:>5}  p999={:>6}  max={:>8}",
        label,
        percentile(samples, 50.0),
        percentile(samples, 90.0),
        percentile(samples, 99.0),
        percentile(samples, 99.9),
        samples[samples.len() - 1],
    );
}

fn main() {
    let now = Instant::now();
    println!(
        "TIMER WHEEL LATENCY (cycles/op) — {} samples, {} warmup",
        SAMPLES, WARMUP
    );
    println!("================================================================\n");

    // Pre-compute deadlines so Instant arithmetic is not in the timed path.
    // Use offsets into the future that span level 0 (< 64ms).
    let deadline_near = now + Duration::from_millis(50);
    // For steady-state: spread across multiple levels
    let far_future = now + Duration::from_secs(1_000_000);

    // ── schedule + cancel (paired) ──────────────────────────────────
    {
        let mut wheel: Wheel<u64> = Wheel::unbounded(4096, now);
        let mut samples = Vec::with_capacity(SAMPLES);

        // warmup
        for _ in 0..WARMUP {
            let h = wheel.schedule(deadline_near, 0);
            black_box(wheel.cancel(h));
        }

        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            let h = wheel.schedule(deadline_near, 0);
            black_box(wheel.cancel(h));
            let e = rdtsc_end();
            samples.push(e.wrapping_sub(s));
        }
        print_row("schedule + cancel (paired)", &mut samples);
    }

    // ── schedule_forget ─────────────────────────────────────────────
    {
        let mut wheel: Wheel<u64> = Wheel::unbounded(SAMPLES + WARMUP + 16, now);
        let mut samples = Vec::with_capacity(SAMPLES);

        // warmup — schedule then drain
        for _ in 0..WARMUP {
            wheel.schedule_forget(deadline_near, 0);
        }
        let mut buf = Vec::new();
        wheel.poll(far_future, &mut buf);

        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            wheel.schedule_forget(deadline_near, 0);
            let e = rdtsc_end();
            samples.push(e.wrapping_sub(s));
        }
        print_row("schedule_forget", &mut samples);

        // drain
        buf.clear();
        wheel.poll(far_future, &mut buf);
    }

    // ── cancel only (pre-scheduled batch) ───────────────────────────
    {
        let mut wheel: Wheel<u64> = Wheel::unbounded(SAMPLES + WARMUP + 16, now);
        let mut samples = Vec::with_capacity(SAMPLES);

        // warmup
        for _ in 0..WARMUP {
            let h = wheel.schedule(deadline_near, 0);
            black_box(wheel.cancel(h));
        }

        // pre-schedule all, then time individual cancels
        let handles: Vec<_> = (0..SAMPLES)
            .map(|i| wheel.schedule(deadline_near, i as u64))
            .collect();

        for h in handles {
            let s = rdtsc_start();
            black_box(wheel.cancel(h));
            let e = rdtsc_end();
            samples.push(e.wrapping_sub(s));
        }
        print_row("cancel (pre-scheduled)", &mut samples);
    }

    // ── poll (batch of expired timers) ──────────────────────────────
    {
        let expired_deadline = now + Duration::from_millis(1);
        let poll_time = now + Duration::from_millis(100);
        let mut samples = Vec::with_capacity(SAMPLES);

        // warmup
        for _ in 0..WARMUP {
            let mut wheel: Wheel<u64> = Wheel::unbounded(POLL_BATCH + 16, now);
            for i in 0..POLL_BATCH {
                wheel.schedule_forget(expired_deadline, i as u64);
            }
            let mut buf = Vec::with_capacity(POLL_BATCH);
            wheel.poll(poll_time, &mut buf);
        }

        for _ in 0..SAMPLES {
            let mut wheel: Wheel<u64> = Wheel::unbounded(POLL_BATCH + 16, now);
            for i in 0..POLL_BATCH {
                wheel.schedule_forget(expired_deadline, i as u64);
            }
            let mut buf = Vec::with_capacity(POLL_BATCH);
            let s = rdtsc_start();
            black_box(wheel.poll(poll_time, &mut buf));
            let e = rdtsc_end();
            // Per-entry cost
            samples.push(e.wrapping_sub(s) / POLL_BATCH as u64);
        }
        print_row("poll (per entry, 100 batch)", &mut samples);
    }

    // ── poll empty wheel ────────────────────────────────────────────
    {
        let mut wheel: Wheel<u64> = Wheel::unbounded(16, now);
        let poll_time = now + Duration::from_millis(100);
        let mut samples = Vec::with_capacity(SAMPLES);
        let mut buf = Vec::new();

        // warmup
        for _ in 0..WARMUP {
            black_box(wheel.poll(poll_time, &mut buf));
        }

        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            black_box(wheel.poll(poll_time, &mut buf));
            let e = rdtsc_end();
            samples.push(e.wrapping_sub(s));
        }
        print_row("poll (empty wheel)", &mut samples);
    }

    // ── schedule + cancel at steady state (100k active) ─────────────
    {
        let mut wheel: Wheel<u64> = Wheel::unbounded(STEADY_SIZE + WARMUP + 16, now);

        // Fill with timers spread across levels
        let mut steady_handles = Vec::with_capacity(STEADY_SIZE);
        for i in 0..STEADY_SIZE {
            // Spread deadlines: 1ms to 10_000ms
            let offset = Duration::from_millis(1 + (i as u64 % 10_000));
            steady_handles.push(wheel.schedule(now + offset, i as u64));
        }

        let mut samples = Vec::with_capacity(SAMPLES);

        // warmup
        for _ in 0..WARMUP {
            let h = wheel.schedule(deadline_near, 0);
            black_box(wheel.cancel(h));
        }

        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            let h = wheel.schedule(deadline_near, 0);
            black_box(wheel.cancel(h));
            let e = rdtsc_end();
            samples.push(e.wrapping_sub(s));
        }
        print_row("sched+cancel @100k active", &mut samples);

        // Clean up
        for h in steady_handles {
            mem::forget(h);
        }
    }
}
