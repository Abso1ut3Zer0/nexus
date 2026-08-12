//! Realistic server-scenario benchmark for [`TimerWheel`].
//!
//! Server code uses timers two ways: **one-shot timeouts** that are usually
//! cancelled before they fire (a request/connection completes before its
//! deadline), and **periodic events** at fixed intervals (heartbeats, metrics
//! flush, health checks). This bench models three server environments of
//! increasing scale, each a mix of both, and drives the wheel through a
//! simulated 1 ms-tick timeline while measuring **per-poll cost in cycles**.
//!
//! Poll is the hot path and the operation the cascade design affects, so we
//! report its full distribution (p50 / p99 / p99.9 / max), never a mean — a
//! mean hides exactly the two things this bench exists to compare: the
//! cascade re-hash burst and the no-cascade per-poll re-walk of a due slot.
//!
//! Run pinned, turbo off:
//! ```text
//! echo 1 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo
//! cargo build --release --bench perf_server_scenarios
//! taskset -c 0 ./target/release/deps/perf_server_scenarios-*
//! ```

use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::hint::black_box;
use std::time::{Duration, Instant};

use nexus_timer::{TimerHandle, Wheel, WheelBuilder};

// ── deterministic RNG (xorshift64*) — identical workload every run ───────────
struct Rng(u64);
impl Rng {
    #[inline]
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    /// Uniform in `[lo, hi)`.
    #[inline]
    fn range(&mut self, lo: u64, hi: u64) -> u64 {
        lo + self.next() % (hi - lo).max(1)
    }
    #[inline]
    fn pct(&mut self, p: u32) -> bool {
        self.next() % 100 < p as u64
    }
}

// ── rdtsc brackets (match perf_timeout_list.rs) ──────────────────────────────
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
    if sorted.is_empty() {
        return 0;
    }
    let idx = ((p / 100.0) * (sorted.len() - 1) as f64).round() as usize;
    sorted[idx]
}

// ── environment definitions ──────────────────────────────────────────────────
struct Periodic {
    period_ms: u64,
    count: usize,
}
struct Env {
    name: &'static str,
    /// Live one-shot timeouts maintained at steady state.
    population: usize,
    /// One-shot deadline range (request/connection timeouts).
    dur_min_ms: u64,
    dur_max_ms: u64,
    /// Percent of one-shots cancelled before firing.
    cancel_pct: u32,
    /// Periodic events, by interval.
    periodic: &'static [Periodic],
}

// Standard server intervals: 3 s, 5 s, 10 s, 15 s, 30 s.
const EDGE: Env = Env {
    name: "edge     (2k one-shots, 90% cancelled, 8 periodic)",
    population: 2_000,
    dur_min_ms: 50,
    dur_max_ms: 2_000,
    cancel_pct: 90,
    periodic: &[
        Periodic {
            period_ms: 3_000,
            count: 2,
        },
        Periodic {
            period_ms: 5_000,
            count: 2,
        },
        Periodic {
            period_ms: 10_000,
            count: 2,
        },
        Periodic {
            period_ms: 15_000,
            count: 1,
        },
        Periodic {
            period_ms: 30_000,
            count: 1,
        },
    ],
};
const APP: Env = Env {
    name: "app      (15k one-shots, 75% cancelled, 64 periodic)",
    population: 15_000,
    dur_min_ms: 100,
    dur_max_ms: 5_000,
    cancel_pct: 75,
    periodic: &[
        Periodic {
            period_ms: 3_000,
            count: 16,
        },
        Periodic {
            period_ms: 5_000,
            count: 16,
        },
        Periodic {
            period_ms: 10_000,
            count: 12,
        },
        Periodic {
            period_ms: 15_000,
            count: 12,
        },
        Periodic {
            period_ms: 30_000,
            count: 8,
        },
    ],
};
const GATEWAY: Env = Env {
    name: "gateway  (50k one-shots, 95% cancelled, 256 periodic)",
    population: 50_000,
    dur_min_ms: 1_000,
    dur_max_ms: 30_000,
    cancel_pct: 95,
    periodic: &[
        Periodic {
            period_ms: 3_000,
            count: 64,
        },
        Periodic {
            period_ms: 5_000,
            count: 64,
        },
        Periodic {
            period_ms: 10_000,
            count: 48,
        },
        Periodic {
            period_ms: 15_000,
            count: 48,
        },
        Periodic {
            period_ms: 30_000,
            count: 32,
        },
    ],
};

const WARMUP_TICKS: u64 = 5_000; // 5 s to reach steady-state population
const SIM_TICKS: u64 = 30_000; // 30 s measured window (1 sample per 1 ms tick)

/// Which poll strategy the driver measures.
#[derive(Clone, Copy, PartialEq)]
enum Mode {
    /// One `poll_and_rebalance` per tick (collect + maintain together).
    Combined,
    /// Collect-only `poll` per tick (the measured cost) plus a proactive
    /// `rebalance` done separately — its cost tracked apart, as idle-time work.
    Proactive,
    /// Adaptive: collect-only `poll`, and `rebalance` only when the poll came
    /// back empty (nothing fired) — maintain during genuine slack.
    Opportunistic,
}

/// Drive one environment through the simulated timeline. Returns the sorted
/// (poll-cost, rebalance-cost) cycle samples over the measured window;
/// rebalance-cost is empty in Combined mode (folded into the poll).
fn run_env(
    env: &Env,
    cancel_pct: u32,
    rebalance_cap: usize,
    mode: Mode,
    rebalance_every: u64,
) -> (Vec<u64>, Vec<u64>) {
    let epoch = Instant::now();
    let mut wheel: Wheel<u64> = WheelBuilder::default()
        .max_rebalances_per_poll(rebalance_cap)
        .unbounded(4096)
        .build(epoch);
    let mut rng = Rng(0x1234_5678_9abc_def0);
    let periodic_count: usize = env.periodic.iter().map(|p| p.count).sum();

    // Periodic timers carry their period_ms as the value and re-arm on fire.
    // Stagger the first fire within [1, period) so they don't clump.
    for p in env.periodic {
        for _ in 0..p.count {
            let first = rng.range(1, p.period_ms);
            wheel.schedule_forget(epoch + Duration::from_millis(first), p.period_ms);
        }
    }

    // Pending one-shot cancels, keyed by the tick they fire at (a min-heap of
    // (cancel_tick, seq)); handles live in `handles[seq]`.
    let mut cancels: BinaryHeap<Reverse<(u64, u64)>> = BinaryHeap::new();
    let mut handles: Vec<Option<TimerHandle<u64>>> = Vec::new();

    let mut buf: Vec<u64> = Vec::with_capacity(2_048);
    let mut samples: Vec<u64> = Vec::with_capacity(SIM_TICKS as usize);
    let mut rebalance_samples: Vec<u64> = Vec::new();

    for tick in 0..(WARMUP_TICKS + SIM_TICKS) {
        let now = epoch + Duration::from_millis(tick);

        // 1. Cancel one-shots that "completed" this tick (before their deadline).
        while let Some(&Reverse((ct, _))) = cancels.peek() {
            if ct > tick {
                break;
            }
            let Reverse((_, seq)) = cancels.pop().unwrap();
            if let Some(h) = handles[seq as usize].take() {
                wheel.cancel(h);
            }
        }

        // 2. Top up one-shots to maintain the target live population.
        let live_oneshots = wheel.len().saturating_sub(periodic_count);
        for _ in live_oneshots..env.population {
            let dur = rng.range(env.dur_min_ms, env.dur_max_ms + 1);
            let deadline = now + Duration::from_millis(dur);
            if rng.pct(cancel_pct) {
                // Will be cancelled `slack` ms before its deadline.
                let h = wheel.schedule(deadline, 0);
                let slack = rng.range(1, dur.max(2));
                let cancel_tick = tick + dur.saturating_sub(slack);
                let seq = handles.len() as u64;
                handles.push(Some(h));
                cancels.push(Reverse((cancel_tick, seq)));
            } else {
                wheel.schedule_forget(deadline, 0); // fires at its deadline
            }
        }

        // 3. Poll — the measured hot path. In Proactive mode the poll is
        // collect-only and a separate rebalance does the maintenance, whose cost
        // is recorded apart (a real caller runs it off the fire path).
        buf.clear();
        let s = rdtsc_start();
        let fired = black_box(match mode {
            Mode::Combined => wheel.poll_and_rebalance(now, &mut buf),
            Mode::Proactive | Mode::Opportunistic => wheel.poll(now, &mut buf),
        });
        let e = rdtsc_end();
        black_box(fired);
        if tick >= WARMUP_TICKS {
            samples.push(e.wrapping_sub(s));
        }

        let do_rebalance = match mode {
            Mode::Combined => false,
            Mode::Proactive => tick % rebalance_every == 0,
            Mode::Opportunistic => fired == 0,
        };
        if do_rebalance {
            let rs = rdtsc_start();
            let moved = black_box(wheel.rebalance(now, usize::MAX));
            let re = rdtsc_end();
            black_box(moved);
            if tick >= WARMUP_TICKS {
                rebalance_samples.push(re.wrapping_sub(rs));
            }
        }

        // 4. Re-arm periodic timers that fired (non-zero value == period_ms).
        for &v in &buf {
            if v != 0 {
                wheel.schedule_forget(now + Duration::from_millis(v), v);
            }
        }
    }

    samples.sort_unstable();
    rebalance_samples.sort_unstable();
    (samples, rebalance_samples)
}

fn print_poll_row(label: &str, samples: &[u64]) {
    println!(
        "  {label:<52} {:>6} {:>6} {:>7} {:>7}",
        percentile(samples, 50.0),
        percentile(samples, 99.0),
        percentile(samples, 99.9),
        percentile(samples, 100.0),
    );
}

fn main() {
    println!("================================================================");
    println!("TIMER WHEEL — realistic server-scenario poll cost (cycles/poll)");
    println!(
        "  1 ms tick; {SIM_TICKS} samples/env after {WARMUP_TICKS} warmup; best effort — pin with taskset -c 0"
    );
    println!("================================================================");

    println!("\nPer-environment poll cost:");
    println!(
        "  {:<52} {:>6} {:>6} {:>7} {:>7}",
        "environment", "p50", "p99", "p99.9", "max"
    );
    for env in [&EDGE, &APP, &GATEWAY] {
        let (samples, _) = run_env(env, env.cancel_pct, usize::MAX, Mode::Combined, 1);
        print_poll_row(env.name, &samples);
    }

    println!("\nCancel-ratio sweep (app env, 15k one-shots, unbounded rebalance):");
    println!(
        "  {:<52} {:>6} {:>6} {:>7} {:>7}",
        "cancelled %", "p50", "p99", "p99.9", "max"
    );
    for pct in [10u32, 50, 75, 90, 95] {
        let (samples, _) = run_env(&APP, pct, usize::MAX, Mode::Combined, 1);
        print_poll_row(&format!("{pct}% cancelled"), &samples);
    }

    // Option (b): does capping rebalances-per-poll flatten the tail? Same app
    // workload, sweeping max_rebalances_per_poll from unbounded down. Expect the
    // tail (p99.9/max) to fall as the cap tightens, at a modest cost to the body.
    println!("\nRebalance-cap sweep (app env, 75% cancelled):");
    println!(
        "  {:<52} {:>6} {:>6} {:>7} {:>7}",
        "max_rebalances_per_poll", "p50", "p99", "p99.9", "max"
    );
    for cap in [usize::MAX, 256, 64, 16] {
        let (samples, _) = run_env(&APP, APP.cancel_pct, cap, Mode::Combined, 1);
        let label = if cap == usize::MAX {
            "unbounded".to_string()
        } else {
            cap.to_string()
        };
        print_poll_row(&label, &samples);
    }

    // Proactive rebalance: move maintenance off the collect hot path. Combined
    // does collect+rebalance in one poll; Proactive collects with a cheap `poll`
    // and does `rebalance` separately on a cadence (its cost shown apart, as
    // idle-time work). Sweeping the cadence: rebalancing more often keeps the
    // collect cheap but re-walks the look-ahead window; less often lets the
    // collect drift up but amortizes rebalance down. (rebalance rows are
    // per-CALL cost — amortized cost per tick ≈ that / cadence.)
    println!("\nProactive rebalance vs combined (app env, 75% cancelled):");
    println!(
        "  {:<52} {:>6} {:>6} {:>7} {:>7}",
        "operation measured", "p50", "p99", "p99.9", "max"
    );
    let (combined, _) = run_env(&APP, APP.cancel_pct, usize::MAX, Mode::Combined, 1);
    print_poll_row("poll_and_rebalance (combined baseline)", &combined);
    for every in [1u64, 16, 64, 256] {
        let (collect, rebal) = run_env(&APP, APP.cancel_pct, usize::MAX, Mode::Proactive, every);
        print_poll_row(
            &format!("poll (collect-only), rebalance every {every}t"),
            &collect,
        );
        print_poll_row(&format!("  rebalance call cost (every {every}t)"), &rebal);
    }

    // Adaptive: rebalance only when a poll comes back empty (nothing fired) —
    // maintain during genuine slack, never steal from a poll that has work.
    println!("\nOpportunistic rebalance (rebalance only on an empty poll, app env):");
    println!(
        "  {:<52} {:>6} {:>6} {:>7} {:>7}",
        "operation measured", "p50", "p99", "p99.9", "max"
    );
    let (collect, rebal) = run_env(&APP, APP.cancel_pct, usize::MAX, Mode::Opportunistic, 1);
    let ran_pct = rebal.len() as f64 / SIM_TICKS as f64 * 100.0;
    print_poll_row("poll (collect-only)", &collect);
    print_poll_row(
        &format!("rebalance (ran on {ran_pct:.0}% of ticks, the empty ones)"),
        &rebal,
    );
}
