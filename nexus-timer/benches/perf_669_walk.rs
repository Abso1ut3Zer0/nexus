//! #669 isolation micro-bench: the per-entry **cache** cost of walking a slot's
//! entries, no-churn (`a`) vs steady-state-churn (`b`).
//!
//! Uses `perf_event` to count hardware events around **only** the `rebalance`
//! call — the setup (and, in mode `b`, the fragmenting churn) is not counted, so
//! the numbers are exactly the walk of the N live entries. No subtraction.
//!
//! - **mode `a` (no churn):** the N live entries are scheduled into a fresh slab
//!   → contiguous, insertion-ordered slots.
//! - **mode `b` (churn):** the free list is first fragmented by scheduling and
//!   cancelling batches in shuffled order, so the N live entries land in
//!   scattered slots — the pointer-chased DLL walk then jumps around memory.
//!
//! Run pinned to a P-core so the counters read the cpu_core PMU:
//! ```text
//! cargo build --release --bench perf_669_walk
//! BIN=$(find target/release/deps -name 'perf_669_walk-*' -type f -executable | head -1)
//! for mode in a b; do for n in 10000 50000; do taskset -c 0 "$BIN" $mode $n; done; done
//! ```

use std::time::{Duration, Instant};

use nexus_timer::{TimerHandle, Wheel};
use perf_event::events::Hardware;
use perf_event::{Builder, Group};

struct Rng(u64);
impl Rng {
    #[inline]
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mode = args.get(1).map_or("a", String::as_str);
    let n: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(10_000);

    let epoch = Instant::now();
    let mut wheel: Wheel<u64> = Wheel::unbounded(4096, epoch);
    let mut rng = Rng(0xC0FF_EE00_1234_5678);

    // mode b: fragment the slab free list before the live population exists.
    if mode == "b" {
        let batch = n * 2;
        for _round in 0..3 {
            let mut handles: Vec<TimerHandle<u64>> = Vec::with_capacity(batch);
            for _ in 0..batch {
                handles.push(wheel.schedule(epoch + Duration::from_secs(3600), 0));
            }
            for i in (1..handles.len()).rev() {
                let j = (rng.next() as usize) % (i + 1);
                handles.swap(i, j);
            }
            for h in handles {
                wheel.cancel(h);
            }
        }
    }

    // Live population: N entries at level-2 deadlines in [600, 1000) ticks.
    for i in 0..n {
        let d = 600 + (i as u64 % 400);
        wheel.schedule_forget(epoch + Duration::from_millis(d), 0);
    }

    // Count cache-misses / cycles / instructions around ONLY the rebalance walk.
    let mut group = Group::new().expect("perf_event Group::new (need perf_event_paranoid <= 2)");
    let cache_misses = Builder::new()
        .group(&mut group)
        .kind(Hardware::CACHE_MISSES)
        .build()
        .expect("cache-misses counter");
    let cycles = Builder::new()
        .group(&mut group)
        .kind(Hardware::CPU_CYCLES)
        .build()
        .expect("cycles counter");
    let insns = Builder::new()
        .group(&mut group)
        .kind(Hardware::INSTRUCTIONS)
        .build()
        .expect("instructions counter");

    let now = epoch + Duration::from_millis(590);
    group.enable().expect("enable");
    let t0 = Instant::now();
    let moved = wheel.rebalance(now, usize::MAX);
    let elapsed = t0.elapsed();
    group.disable().expect("disable");
    assert_eq!(moved, n, "rebalance should walk+move every live entry");

    let counts = group.read().expect("read counters");
    let cm = counts[&cache_misses];
    let cy = counts[&cycles];
    let ins = counts[&insns];
    let ns_total = elapsed.as_nanos();
    println!(
        "mode={mode} n={n:>7}  walk={:>8.3}ms  {:>6.1}ns/entry  {:>5.1}cy/entry  {:>5.2}miss/entry  IPC={:.2}  ({:.2} GHz eff)",
        ns_total as f64 / 1e6,
        ns_total as f64 / n as f64,
        cy as f64 / n as f64,
        cm as f64 / n as f64,
        ins as f64 / cy.max(1) as f64,
        cy as f64 / ns_total.max(1) as f64, // cycles/ns = GHz
    );
}
