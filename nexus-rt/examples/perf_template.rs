//! Template instantiation benchmark: `resolve` + `with_state` vs `into_handler`.
//!
//! Measures the hot-path cost of stamping out handlers from pre-resolved
//! state compared to full `into_handler` construction (HashMap lookups +
//! conflict detection each time).
//!
//! Run with:
//! ```bash
//! taskset -c 0 cargo run --release -p nexus-rt --example perf_template
//! ```

use std::hint::black_box;

use nexus_rt::{
    CallbackTemplate, HandlerTemplate, IntoCallback, IntoHandler, Res, ResMut, WorldBuilder,
    callback_blueprint, handler_blueprint,
};

// =============================================================================
// Bench infrastructure (same as perf_construction.rs)
// =============================================================================

const ITERATIONS: usize = 100_000;
const WARMUP: usize = 10_000;
const BATCH: u64 = 100;

#[inline(always)]
#[cfg(target_arch = "x86_64")]
fn rdtsc_start() -> u64 {
    unsafe {
        core::arch::x86_64::_mm_lfence();
        core::arch::x86_64::_rdtsc()
    }
}

#[inline(always)]
#[cfg(target_arch = "x86_64")]
fn rdtsc_end() -> u64 {
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

fn sys_1p(_a: Res<u64>, _e: ()) {}
fn sys_2p(_a: Res<u64>, _b: ResMut<u32>, _e: ()) {}
fn sys_4p(_a: Res<u64>, _b: ResMut<u32>, _c: Res<bool>, _d: Res<f64>, _e: ()) {}

#[allow(clippy::too_many_arguments)]
fn sys_8p(
    _a: Res<u64>,
    _b: ResMut<u32>,
    _c: Res<bool>,
    _d: Res<f64>,
    _e2: Res<i64>,
    _f: Res<i32>,
    _g: Res<u8>,
    _h: ResMut<u16>,
    _e: (),
) {
}

// =============================================================================
// Callback functions
// =============================================================================

fn cb_2p(_ctx: &mut u64, _a: Res<u64>, _b: ResMut<u32>, _e: ()) {}
fn cb_4p(_ctx: &mut u64, _a: Res<u64>, _b: ResMut<u32>, _c: Res<bool>, _d: Res<f64>, _e: ()) {}

// =============================================================================
// Blueprint keys for HandlerTemplate / CallbackTemplate benchmarks
// =============================================================================

handler_blueprint!(K1P, ());
handler_blueprint!(K2P, ());
handler_blueprint!(K4P, ());
handler_blueprint!(K8P, ());
callback_blueprint!(KCb2P, u64, ());
callback_blueprint!(KCb4P, u64, ());

// =============================================================================
// Main
// =============================================================================

fn main() {
    let mut wb = WorldBuilder::new();
    wb.register::<u64>(0);
    wb.register::<u32>(0);
    wb.register::<bool>(false);
    wb.register::<f64>(0.0);
    wb.register::<i64>(0);
    wb.register::<i32>(0);
    wb.register::<u8>(0);
    wb.register::<u16>(0);
    let mut world = wb.build();
    let r = world.registry_mut();

    // Pre-resolve state once for each arity.
    let state_1p = sys_1p.resolve(r);
    let state_2p = sys_2p.resolve(r);
    let state_4p = sys_4p.resolve(r);
    let state_8p = sys_8p.resolve(r);
    let cb_state_2p = cb_2p.resolve(r);
    let cb_state_4p = cb_4p.resolve(r);

    // ── Baseline: into_handler (HashMap lookups each time) ──────────────

    print_header("into_handler Construction — baseline (cycles)");

    bench_batched("into_handler  1-param", || {
        let _ = black_box(sys_1p.into_handler(r));
        0
    });
    bench_batched("into_handler  2-param", || {
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

    println!();

    // ── Template: with_state (zero HashMap lookups) ─────────────────────

    print_header("with_state Instantiation — template (cycles)");

    bench_batched("with_state    1-param", || {
        let _ = black_box(sys_1p.with_state(state_1p));
        0
    });
    bench_batched("with_state    2-param", || {
        let _ = black_box(sys_2p.with_state(state_2p));
        0
    });
    bench_batched("with_state    4-param", || {
        let _ = black_box(sys_4p.with_state(state_4p));
        0
    });
    bench_batched("with_state    8-param", || {
        let _ = black_box(sys_8p.with_state(state_8p));
        0
    });

    println!();

    // ── Callbacks: into_callback vs with_state ──────────────────────────

    print_header("into_callback Construction — baseline (cycles)");

    bench_batched("into_callback 2-param", || {
        let _ = black_box(cb_2p.into_callback(0u64, r));
        0
    });
    bench_batched("into_callback 4-param", || {
        let _ = black_box(cb_4p.into_callback(0u64, r));
        0
    });

    println!();
    print_header("with_state Callback — template (cycles)");

    bench_batched("with_state    cb 2-param", || {
        let _ = black_box(cb_2p.with_state(0u64, cb_state_2p));
        0
    });
    bench_batched("with_state    cb 4-param", || {
        let _ = black_box(cb_4p.with_state(0u64, cb_state_4p));
        0
    });

    println!();

    // ── HandlerTemplate::instantiate (type-erased, heap alloc) ────────────

    let tpl_1p = HandlerTemplate::<K1P>::new(sys_1p, r);
    let tpl_2p = HandlerTemplate::<K2P>::new(sys_2p, r);
    let tpl_4p = HandlerTemplate::<K4P>::new(sys_4p, r);
    let tpl_8p = HandlerTemplate::<K8P>::new(sys_8p, r);
    let cb_tpl_2p = CallbackTemplate::<KCb2P>::new(cb_2p, r);
    let cb_tpl_4p = CallbackTemplate::<KCb4P>::new(cb_4p, r);

    print_header("HandlerTemplate::instantiate — type-erased (cycles)");

    bench_batched("instantiate   1-param", || {
        let _ = black_box(tpl_1p.instantiate());
        0
    });
    bench_batched("instantiate   2-param", || {
        let _ = black_box(tpl_2p.instantiate());
        0
    });
    bench_batched("instantiate   4-param", || {
        let _ = black_box(tpl_4p.instantiate());
        0
    });
    bench_batched("instantiate   8-param", || {
        let _ = black_box(tpl_8p.instantiate());
        0
    });

    println!();
    print_header("CallbackTemplate::instantiate — type-erased (cycles)");

    bench_batched("instantiate   cb 2-param", || {
        let _ = black_box(cb_tpl_2p.instantiate(0u64));
        0
    });
    bench_batched("instantiate   cb 4-param", || {
        let _ = black_box(cb_tpl_4p.instantiate(0u64));
        0
    });

    println!();
}
