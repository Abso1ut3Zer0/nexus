#![allow(unused_mut, dropping_references)]
//! Construction-time latency benchmark for `into_handler`, `into_callback`,
//! and `into_step`.
//!
//! Measures the cold-path cost of resolving Param state + access
//! conflict detection at various arities. This is paid once per handler
//! at build time — never on the dispatch hot path.
//!
//! Run with:
//! ```bash
//! taskset -c 0 cargo run --release -p nexus-rt --example perf_construction
//! ```

use std::hint::black_box;

use nexus_rt::{
    IntoCallback, IntoHandler, Local, PipelineBuilder, Res, ResMut, WorldBuilder, new_resource,
};

new_resource!(ResU64(u64));
new_resource!(ResU32(u32));
new_resource!(ResBool(bool));
new_resource!(ResF64(f64));
new_resource!(ResI64(i64));
new_resource!(ResI32(i32));
new_resource!(ResU8(u8));
new_resource!(ResU16(u16));

// =============================================================================
// Bench infrastructure (same as perf_pipeline.rs)
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

fn bench_batched<F: FnMut() -> u64>(name: &str, mut f: F) -> (u64, u64, u64) {
    for _ in 0..WARMUP {
        black_box(f());
    }
    let mut samples = Vec::with_capacity(ITERATIONS);
    for _ in 0..ITERATIONS {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            black_box(f());
        }
        let end = rdtsc_end();
        samples.push(end.wrapping_sub(start) / BATCH);
    }
    samples.sort_unstable();
    let p50 = percentile(&samples, 50.0);
    let p99 = percentile(&samples, 99.0);
    let p999 = percentile(&samples, 99.9);
    println!("{:<50} {:>8} {:>8} {:>8}", name, p50, p99, p999);
    (p50, p99, p999)
}

fn print_header(title: &str) {
    println!("=== {} ===\n", title);
    println!(
        "{:<50} {:>8} {:>8} {:>8}",
        "Operation", "p50", "p99", "p999"
    );
    println!("{}", "-".repeat(78));
}

// =============================================================================
// Handler functions at various arities
// =============================================================================

fn sys_1p(_a: Res<ResU64>, _e: ()) {}
fn sys_2p(_a: Res<ResU64>, _b: ResMut<ResU32>, _e: ()) {}
fn sys_4p(_a: Res<ResU64>, _b: ResMut<ResU32>, _c: Res<ResBool>, _d: Res<ResF64>, _e: ()) {}

#[allow(clippy::too_many_arguments)]
fn sys_8p(
    _a: Res<ResU64>,
    _b: ResMut<ResU32>,
    _c: Res<ResBool>,
    _d: Res<ResF64>,
    _e2: Res<ResI64>,
    _f: Res<ResI32>,
    _g: Res<ResU8>,
    _h: ResMut<ResU16>,
    _e: (),
) {
}

// With Local (no World resource — skipped by check_access)
fn sys_local(_a: Local<u64>, _b: ResMut<ResU32>, _e: ()) {}

// With Option (try_id path in init)
fn sys_option(_a: Option<Res<ResU64>>, _b: ResMut<ResU32>, _e: ()) {}

// =============================================================================
// Callback functions
// =============================================================================

fn cb_2p(_ctx: &mut u64, _a: Res<ResU64>, _b: ResMut<ResU32>, _e: ()) {}
fn cb_4p(
    _ctx: &mut u64,
    _a: Res<ResU64>,
    _b: ResMut<ResU32>,
    _c: Res<ResBool>,
    _d: Res<ResF64>,
    _e: (),
) {
}

// =============================================================================
// Step functions
// =============================================================================

fn stage_2p(_a: Res<ResU64>, _b: ResMut<ResU32>, _x: u32) -> u32 {
    0
}
fn stage_4p(
    _a: Res<ResU64>,
    _b: ResMut<ResU32>,
    _c: Res<ResBool>,
    _d: Res<ResF64>,
    _x: u32,
) -> u32 {
    0
}

// =============================================================================
// Main
// =============================================================================

fn main() {
    // Register enough types to exercise the check_access bitset.
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(0));
    wb.register(ResU32(0));
    wb.register(ResBool(false));
    wb.register(ResF64(0.0));
    wb.register(ResI64(0));
    wb.register(ResI32(0));
    wb.register(ResU8(0));
    wb.register(ResU16(0));
    let mut world = wb.build();
    let r = world.registry();

    print_header("into_handler Construction (cycles)");

    bench_batched("into_handler  1-param (Res<ResU64>)", || {
        let _ = black_box(sys_1p.into_handler(r));
        0
    });

    bench_batched("into_handler  2-param (Res + ResMut)", || {
        let _ = black_box(sys_2p.into_handler(r));
        0
    });

    bench_batched("into_handler  4-param", || {
        let _ = black_box(sys_4p.into_handler(r));
        0
    });

    bench_batched("into_handler  8-param", || {
        let _ = black_box(sys_8p.into_handler(r));
        0
    });

    bench_batched("into_handler  2-param (Local + ResMut)", || {
        let _ = black_box(sys_local.into_handler(r));
        0
    });

    bench_batched("into_handler  2-param (Option<Res> + ResMut)", || {
        let _ = black_box(sys_option.into_handler(r));
        0
    });

    println!();
    print_header("into_callback Construction (cycles)");

    bench_batched("into_callback 2-param (Res + ResMut)", || {
        let _ = black_box(cb_2p.into_callback(0u64, r));
        0
    });

    bench_batched("into_callback 4-param", || {
        let _ = black_box(cb_4p.into_callback(0u64, r));
        0
    });

    println!();
    print_header("into_step Construction (cycles)");

    bench_batched(".then() 2-param (Res + ResMut)", || {
        let _ = black_box(PipelineBuilder::<u32>::new().then(stage_2p, r));
        0
    });

    bench_batched(".then() 4-param", || {
        let _ = black_box(PipelineBuilder::<u32>::new().then(stage_4p, r));
        0
    });

    println!();
}
