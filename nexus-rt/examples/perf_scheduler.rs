//! Scheduler dispatch latency benchmark.
//!
//! Measures the cost of `SystemScheduler::run()` with various stage
//! configurations and system counts. All systems do trivial work (single
//! wrapping_add) to isolate scheduler overhead from system body cost.
//!
//! Run with:
//! ```bash
//! taskset -c 0 cargo run --release -p nexus-rt --example perf_scheduler
//! ```

use std::hint::black_box;

use nexus_rt::scheduler::SchedulerBuilder;
use nexus_rt::{ResMut, WorldBuilder, new_resource};

new_resource!(ResU64(u64));

// =============================================================================
// Bench infrastructure (inline — no shared utils crate yet)
// =============================================================================

const ITERATIONS: usize = 100_000;
const WARMUP: usize = 10_000;
const BATCH: u64 = 100;

#[inline(always)]
#[cfg(target_arch = "x86_64")]
fn rdtsc_start() -> u64 {
    // SAFETY: x86_64 intrinsic; function is only compiled for x86_64.
    unsafe {
        core::arch::x86_64::_mm_lfence();
        core::arch::x86_64::_rdtsc()
    }
}

#[inline(always)]
#[cfg(target_arch = "x86_64")]
fn rdtsc_end() -> u64 {
    // SAFETY: x86_64 intrinsic; function is only compiled for x86_64.
    unsafe {
        let mut aux = 0u32;
        let tsc = core::arch::x86_64::__rdtscp(&raw mut aux);
        core::arch::x86_64::_mm_lfence();
        tsc
    }
}

fn percentile(sorted: &[u64], p: f64) -> u64 {
    let idx = ((sorted.len() as f64) * p / 100.0) as usize;
    sorted[idx.min(sorted.len() - 1)]
}

fn bench_batched<F: FnMut()>(name: &str, mut f: F) -> (u64, u64, u64) {
    for _ in 0..WARMUP {
        f();
    }
    let mut samples = Vec::with_capacity(ITERATIONS);
    for _ in 0..ITERATIONS {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            f();
        }
        let end = rdtsc_end();
        samples.push(end.wrapping_sub(start) / BATCH);
    }
    samples.sort_unstable();
    let p50 = percentile(&samples, 50.0);
    let p99 = percentile(&samples, 99.0);
    let p999 = percentile(&samples, 99.9);
    println!("{:<44} {:>8} {:>8} {:>8}", name, p50, p99, p999);
    (p50, p99, p999)
}

fn print_header(title: &str) {
    println!("=== {} ===\n", title);
    println!(
        "{:<44} {:>8} {:>8} {:>8}",
        "Operation", "p50", "p99", "p999"
    );
    println!("{}", "-".repeat(72));
}

// =============================================================================
// Trivial systems — isolate scheduler overhead from system body cost
// =============================================================================

fn sys_true(mut val: ResMut<ResU64>) -> bool {
    val.0 = val.0.wrapping_add(1);
    true
}

fn sys_false(mut val: ResMut<ResU64>) -> bool {
    val.0 = val.0.wrapping_add(1);
    false
}

// =============================================================================
// Main
// =============================================================================

fn main() {
    println!("SCHEDULER DISPATCH LATENCY BENCHMARK");
    println!("====================================\n");
    println!("Iterations: {ITERATIONS}, Warmup: {WARMUP}, Batch: {BATCH}");
    println!("All times in CPU cycles\n");

    // -- Single-system stages (linear chains) --

    print_header("Linear Chain (single-system stages, all propagate true)");

    {
        let mut wb = WorldBuilder::new();
        wb.register(ResU64(0));
        let reg = wb.registry();
        let mut scheduler = wb.install_driver(SchedulerBuilder::new().root(sys_true, reg));
        let mut world = wb.build();
        bench_batched("chain 1 system", || {
            black_box(scheduler.run(&mut world));
        });
    }
    {
        let mut wb = WorldBuilder::new();
        wb.register(ResU64(0));
        let reg = wb.registry();
        let mut scheduler = wb.install_driver(
            SchedulerBuilder::new()
                .root(sys_true, reg)
                .then(sys_true, reg)
                .then(sys_true, reg)
                .then(sys_true, reg),
        );
        let mut world = wb.build();
        bench_batched("chain 4 systems", || {
            black_box(scheduler.run(&mut world));
        });
    }
    {
        let mut wb = WorldBuilder::new();
        wb.register(ResU64(0));
        let reg = wb.registry();
        let mut scheduler = wb.install_driver(
            SchedulerBuilder::new()
                .root(sys_true, reg)
                .then(sys_true, reg)
                .then(sys_true, reg)
                .then(sys_true, reg)
                .then(sys_true, reg)
                .then(sys_true, reg)
                .then(sys_true, reg)
                .then(sys_true, reg),
        );
        let mut world = wb.build();
        bench_batched("chain 8 systems", || {
            black_box(scheduler.run(&mut world));
        });
    }

    // -- Multi-system stages (fan-out) --

    println!();
    print_header("Multi-System Stage (all in root, all propagate true)");

    {
        let mut wb = WorldBuilder::new();
        wb.register(ResU64(0));
        let reg = wb.registry();
        let mut scheduler = wb.install_driver(
            SchedulerBuilder::new().root((sys_true, sys_true, sys_true, sys_true), reg),
        );
        let mut world = wb.build();
        bench_batched("stage with 4 systems", || {
            black_box(scheduler.run(&mut world));
        });
    }
    {
        let mut wb = WorldBuilder::new();
        wb.register(ResU64(0));
        let reg = wb.registry();
        let mut scheduler = wb.install_driver(SchedulerBuilder::new().root(
            (
                sys_true, sys_true, sys_true, sys_true, sys_true, sys_true, sys_true, sys_true,
            ),
            reg,
        ));
        let mut world = wb.build();
        bench_batched("stage with 8 systems", || {
            black_box(scheduler.run(&mut world));
        });
    }

    // -- Diamond (fan-out + fan-in) --

    println!();
    print_header("Diamond (root → stage with N → sink)");

    {
        let mut wb = WorldBuilder::new();
        wb.register(ResU64(0));
        let reg = wb.registry();
        let mut scheduler = wb.install_driver(
            SchedulerBuilder::new()
                .root(sys_true, reg)
                .then((sys_true, sys_true), reg)
                .then(sys_true, reg),
        );
        let mut world = wb.build();
        bench_batched("diamond fan=2 (4 systems)", || {
            black_box(scheduler.run(&mut world));
        });
    }
    {
        let mut wb = WorldBuilder::new();
        wb.register(ResU64(0));
        let reg = wb.registry();
        let mut scheduler = wb.install_driver(
            SchedulerBuilder::new()
                .root(sys_true, reg)
                .then((sys_true, sys_true, sys_true, sys_true), reg)
                .then(sys_true, reg),
        );
        let mut world = wb.build();
        bench_batched("diamond fan=4 (6 systems)", || {
            black_box(scheduler.run(&mut world));
        });
    }
    {
        let mut wb = WorldBuilder::new();
        wb.register(ResU64(0));
        let reg = wb.registry();
        let mut scheduler = wb.install_driver(
            SchedulerBuilder::new()
                .root(sys_true, reg)
                .then(
                    (
                        sys_true, sys_true, sys_true, sys_true, sys_true, sys_true, sys_true,
                        sys_true,
                    ),
                    reg,
                )
                .then(sys_true, reg),
        );
        let mut world = wb.build();
        bench_batched("diamond fan=8 (10 systems)", || {
            black_box(scheduler.run(&mut world));
        });
    }

    // -- Skipped chain (root returns false) --

    println!();
    print_header("Skipped Chain (root=false, downstream skipped)");

    {
        let mut wb = WorldBuilder::new();
        wb.register(ResU64(0));
        let reg = wb.registry();
        let mut scheduler = wb.install_driver(
            SchedulerBuilder::new()
                .root(sys_false, reg)
                .then(sys_true, reg)
                .then(sys_true, reg)
                .then(sys_true, reg),
        );
        let mut world = wb.build();
        bench_batched("skipped chain 4 (1 runs, 3 skip)", || {
            black_box(scheduler.run(&mut world));
        });
    }
    {
        let mut wb = WorldBuilder::new();
        wb.register(ResU64(0));
        let reg = wb.registry();
        let mut scheduler = wb.install_driver(
            SchedulerBuilder::new()
                .root(sys_false, reg)
                .then(sys_true, reg)
                .then(sys_true, reg)
                .then(sys_true, reg)
                .then(sys_true, reg)
                .then(sys_true, reg)
                .then(sys_true, reg)
                .then(sys_true, reg),
        );
        let mut world = wb.build();
        bench_batched("skipped chain 8 (1 runs, 7 skip)", || {
            black_box(scheduler.run(&mut world));
        });
    }

    println!();
}
