//! Runtime keyed dispatch latency benchmark (issue #723).
//!
//! Compares the two dispatch-table combinators against the two things they sit
//! between: the compile-time `select!` jump table (faster, arms fixed at compile
//! time) and an `FxHashMap` keyed-dispatch table (the usual runtime-composable
//! alternative, which hashes). For an N-variant enum all arms do identical work
//! (accumulate a payload into a `World` resource) so only the dispatch mechanism
//! differs:
//!
//! - `.dispatch_variant` — input IS the enum, arms get the typed payload; the
//!   table is a flat array indexed by the value's own `ordinal()`, one indirect
//!   call into the boxed arm.
//! - `.dispatch_on` — projected key (`Fn(&V) -> K`), whole-value arms; same flat
//!   array, keyed by the projection's ordinal. Also exercises a tuple-product
//!   composite key `(A, B)` (dense, no hashing).
//! - `select!` — compile-time arms; the dispatch inlines to a `match` / jump
//!   table with a direct (inlined) call — the baseline to beat.
//! - `FxHashMap<usize, Box<dyn Handler>>` — runtime table via hashing; the
//!   alternative the flat-array table replaces.
//!
//! Run asm inspection:
//! ```bash
//! cargo asm -p nexus-rt --example perf_dispatch perf_dispatch::probe_dispatch_variant
//! cargo asm -p nexus-rt --example perf_dispatch perf_dispatch::probe_dispatch_on
//! cargo asm -p nexus-rt --example perf_dispatch perf_dispatch::probe_select
//! cargo asm -p nexus-rt --example perf_dispatch perf_dispatch::probe_hashmap
//! ```
//!
//! Run benchmark:
//! ```bash
//! taskset -c 0 cargo run --release -p nexus-rt --example perf_dispatch
//! ```
//!
//! The printed cycle counts are only meaningful under the controlled conditions
//! the maintainer runs them under — pinned to a physical core (`taskset -c 0`),
//! turbo boost disabled, otherwise-quiescent machine. Numbers from a casual run
//! are noise and are deliberately NOT recorded in the docs or CHANGELOG.

use std::hint::black_box;

use nexus_rt::{
    Dispatchable, Handler, IntoHandler, PipelineBuilder, ResMut, WorldBuilder, new_resource, select,
};
use rustc_hash::FxHashMap;

new_resource!(Acc(u64));

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

fn bench_batched<F: FnMut()>(name: &str, mut f: F) {
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
    println!(
        "{:<44} {:>7} {:>7} {:>7} {:>7} {:>7}",
        name,
        percentile(&samples, 50.0),
        percentile(&samples, 90.0),
        percentile(&samples, 99.0),
        percentile(&samples, 99.9),
        percentile(&samples, 99.99),
    );
}

fn print_header(title: &str) {
    println!("=== {} ===\n", title);
    println!(
        "{:<44} {:>7} {:>7} {:>7} {:>7} {:>7}",
        "Operation", "p50", "p90", "p99", "p999", "p9999"
    );
    println!("{}", "-".repeat(84));
}

// =============================================================================
// Dispatch keys — an 8-variant enum, plus a projected key and a composite key
// =============================================================================

/// The dispatched enum.
///
/// Data-carrying so `.dispatch_variant` has a real typed payload to unwrap;
/// `select!` and the `FxHashMap` baseline dispatch on the same discriminant for
/// an apples-to-apples comparison.
#[derive(Dispatchable, Clone, Copy)]
pub enum Cmd {
    V0(u64),
    V1(u64),
    V2(u64),
    V3(u64),
    V4(u64),
    V5(u64),
    V6(u64),
    V7(u64),
}

/// Projected key for `.dispatch_on`: a fieldless discriminant carried as a
/// struct field of `Msg`.
#[derive(Dispatchable, Clone, Copy)]
pub enum Kind {
    K0,
    K1,
    K2,
    K3,
    K4,
    K5,
    K6,
    K7,
}

/// Whole value the `.dispatch_on` arms receive (routed by its `kind` field).
#[derive(Clone, Copy)]
pub struct Msg {
    kind: Kind,
    payload: u64,
}

// Composite (tuple-product) key: 2 * 4 = 8 dense slots, no hashing.
#[derive(Dispatchable, Clone, Copy)]
pub enum Coarse {
    X,
    Y,
}

#[derive(Dispatchable, Clone, Copy)]
pub enum Fine {
    P,
    Q,
    R,
    S,
}

#[derive(Clone, Copy)]
pub struct Grid {
    a: Coarse,
    b: Fine,
    payload: u64,
}

// =============================================================================
// Arms — identical work (accumulate the payload) so only dispatch cost differs
// =============================================================================

/// `.dispatch_variant` arm: receives the unwrapped `u64` payload directly.
#[allow(clippy::needless_pass_by_value)]
fn add_payload(mut acc: ResMut<Acc>, payload: u64) {
    acc.0 = acc.0.wrapping_add(payload);
}

/// `select!` / `FxHashMap` arm: receives the whole `Cmd`, matches out the
/// payload (every variant carries a `u64`).
#[allow(clippy::needless_pass_by_value)]
fn add_cmd(mut acc: ResMut<Acc>, cmd: Cmd) {
    let payload = match cmd {
        Cmd::V0(p)
        | Cmd::V1(p)
        | Cmd::V2(p)
        | Cmd::V3(p)
        | Cmd::V4(p)
        | Cmd::V5(p)
        | Cmd::V6(p)
        | Cmd::V7(p) => p,
    };
    acc.0 = acc.0.wrapping_add(payload);
}

/// `.dispatch_on` arm: receives the whole `Msg` value.
#[allow(clippy::needless_pass_by_value)]
fn add_msg(mut acc: ResMut<Acc>, msg: Msg) {
    acc.0 = acc.0.wrapping_add(msg.payload);
}

/// Tuple-product `.dispatch_on` arm: receives the whole `Grid` value.
#[allow(clippy::needless_pass_by_value)]
fn add_grid(mut acc: ResMut<Acc>, grid: Grid) {
    acc.0 = acc.0.wrapping_add(grid.payload);
}

// =============================================================================
// Codegen probes — one indirect call each (dispatch table), inlined for select!
// =============================================================================

/// `.dispatch_variant` table: `ordinal()` index + one indirect call into the
/// boxed arm, which unwraps the typed payload.
#[inline(never)]
pub fn probe_dispatch_variant(p: &mut impl Handler<Cmd>, world: &mut nexus_rt::World, cmd: Cmd) {
    p.run(world, cmd);
}

/// `.dispatch_on` table: projection + `ordinal()` index + one indirect call
/// into the boxed arm, which gets the whole value.
#[inline(never)]
pub fn probe_dispatch_on(p: &mut impl Handler<Msg>, world: &mut nexus_rt::World, msg: Msg) {
    p.run(world, msg);
}

/// Tuple-product composite key: `(a.ordinal() * Fine::VARIANTS + b.ordinal())`
/// index into the same flat table — no hashing.
#[inline(never)]
pub fn probe_dispatch_on_pair(p: &mut impl Handler<Grid>, world: &mut nexus_rt::World, grid: Grid) {
    p.run(world, grid);
}

/// `select!` baseline: the dispatch inlines to a `match` / jump table with a
/// direct call — no indirection.
#[inline(never)]
pub fn probe_select(p: &mut impl Handler<Cmd>, world: &mut nexus_rt::World, cmd: Cmd) {
    p.run(world, cmd);
}

/// `FxHashMap` baseline: hash the key, probe the bucket, one indirect (vtable)
/// call. The alternative the flat-array table replaces.
#[inline(never)]
#[allow(clippy::implicit_hasher)] // benchmarking FxHashMap specifically
pub fn probe_hashmap(
    map: &mut FxHashMap<usize, Box<dyn Handler<Cmd>>>,
    world: &mut nexus_rt::World,
    cmd: Cmd,
) {
    if let Some(arm) = map.get_mut(&cmd.ordinal()) {
        arm.run(world, cmd);
    }
}

/// `.dispatch_map` table: hash the projected key into an `FxHashMap`.
///
/// One indirect call into the boxed arm (whole value). The runtime-composable
/// catch-all for non-`Dispatchable` keys — the combinator over a raw `FxHashMap`.
#[inline(never)]
pub fn probe_dispatch_map(p: &mut impl Handler<Cmd>, world: &mut nexus_rt::World, cmd: Cmd) {
    p.run(world, cmd);
}

// =============================================================================
// Main — benchmark
// =============================================================================

fn main() {
    let mut wb = WorldBuilder::new();
    wb.register(Acc(0));
    let mut world = wb.build();
    let r = world.registry();

    // --- .dispatch_variant table (input IS the enum, arms get the payload) ---

    let mut dv = PipelineBuilder::<Cmd>::new()
        .dispatch_variant(r, |d| {
            d.arm(cmd_variants::V0, add_payload)
                .arm(cmd_variants::V1, add_payload)
                .arm(cmd_variants::V2, add_payload)
                .arm(cmd_variants::V3, add_payload)
                .arm(cmd_variants::V4, add_payload)
                .arm(cmd_variants::V5, add_payload)
                .arm(cmd_variants::V6, add_payload)
                .arm(cmd_variants::V7, add_payload)
        })
        .build();

    // --- .dispatch_on table (projected key, arms get the whole value) ---

    let mut don = PipelineBuilder::<Msg>::new()
        .dispatch_on(
            |m: &Msg| m.kind,
            r,
            |d| {
                d.arm(Kind::K0, add_msg)
                    .arm(Kind::K1, add_msg)
                    .arm(Kind::K2, add_msg)
                    .arm(Kind::K3, add_msg)
                    .arm(Kind::K4, add_msg)
                    .arm(Kind::K5, add_msg)
                    .arm(Kind::K6, add_msg)
                    .arm(Kind::K7, add_msg)
            },
        )
        .build();

    // --- .dispatch_on with a tuple-product composite key ---

    let mut dpair = PipelineBuilder::<Grid>::new()
        .dispatch_on(
            |g: &Grid| (g.a, g.b),
            r,
            |d| {
                d.arm((Coarse::X, Fine::P), add_grid)
                    .arm((Coarse::X, Fine::Q), add_grid)
                    .arm((Coarse::X, Fine::R), add_grid)
                    .arm((Coarse::X, Fine::S), add_grid)
                    .arm((Coarse::Y, Fine::P), add_grid)
                    .arm((Coarse::Y, Fine::Q), add_grid)
                    .arm((Coarse::Y, Fine::R), add_grid)
                    .arm((Coarse::Y, Fine::S), add_grid)
            },
        )
        .build();

    // --- select! baseline (compile-time arms, one match / jump table) ---

    let mut sel = PipelineBuilder::<Cmd>::new()
        .then(
            select! {
                r,
                Cmd::V0(..) => add_cmd,
                Cmd::V1(..) => add_cmd,
                Cmd::V2(..) => add_cmd,
                Cmd::V3(..) => add_cmd,
                Cmd::V4(..) => add_cmd,
                Cmd::V5(..) => add_cmd,
                Cmd::V6(..) => add_cmd,
                Cmd::V7(..) => add_cmd,
            },
            r,
        )
        .build();

    // --- FxHashMap baseline (runtime table via hashing) ---

    let mut map: FxHashMap<usize, Box<dyn Handler<Cmd>>> = FxHashMap::default();
    for k in 0..Cmd::VARIANTS {
        map.insert(k, Box::new(add_cmd.into_handler(r)));
    }

    // --- .dispatch_map table (Hash+Eq key via FxHashMap; whole-value arms) ---

    let mut dm = PipelineBuilder::<Cmd>::new()
        .dispatch_map(
            |c: &Cmd| c.ordinal(),
            r,
            |d| {
                d.arm(0usize, add_cmd)
                    .arm(1usize, add_cmd)
                    .arm(2usize, add_cmd)
                    .arm(3usize, add_cmd)
                    .arm(4usize, add_cmd)
                    .arm(5usize, add_cmd)
                    .arm(6usize, add_cmd)
                    .arm(7usize, add_cmd)
                    .default_noop()
            },
        )
        .build();

    // --- Inputs (round-robin over all keys each call) ---

    let cmds: [Cmd; 8] = [
        Cmd::V0(10),
        Cmd::V1(11),
        Cmd::V2(12),
        Cmd::V3(13),
        Cmd::V4(14),
        Cmd::V5(15),
        Cmd::V6(16),
        Cmd::V7(17),
    ];
    let msgs: [Msg; 8] = [
        Msg {
            kind: Kind::K0,
            payload: 10,
        },
        Msg {
            kind: Kind::K1,
            payload: 11,
        },
        Msg {
            kind: Kind::K2,
            payload: 12,
        },
        Msg {
            kind: Kind::K3,
            payload: 13,
        },
        Msg {
            kind: Kind::K4,
            payload: 14,
        },
        Msg {
            kind: Kind::K5,
            payload: 15,
        },
        Msg {
            kind: Kind::K6,
            payload: 16,
        },
        Msg {
            kind: Kind::K7,
            payload: 17,
        },
    ];
    let grids: [Grid; 8] = [
        Grid {
            a: Coarse::X,
            b: Fine::P,
            payload: 10,
        },
        Grid {
            a: Coarse::X,
            b: Fine::Q,
            payload: 11,
        },
        Grid {
            a: Coarse::X,
            b: Fine::R,
            payload: 12,
        },
        Grid {
            a: Coarse::X,
            b: Fine::S,
            payload: 13,
        },
        Grid {
            a: Coarse::Y,
            b: Fine::P,
            payload: 14,
        },
        Grid {
            a: Coarse::Y,
            b: Fine::Q,
            payload: 15,
        },
        Grid {
            a: Coarse::Y,
            b: Fine::R,
            payload: 16,
        },
        Grid {
            a: Coarse::Y,
            b: Fine::S,
            payload: 17,
        },
    ];

    // --- Discriminant dispatch: table vs jump table vs hashmap (same key) ---

    print_header("Keyed Dispatch on Discriminant (cycles, 8 variants)");

    let mut i = 0usize;

    bench_batched(".dispatch_variant (array index)", || {
        let c = cmds[i & 7];
        i = i.wrapping_add(1);
        probe_dispatch_variant(&mut dv, &mut world, black_box(c));
    });

    bench_batched("select! (jump table, inlined)", || {
        let c = cmds[i & 7];
        i = i.wrapping_add(1);
        probe_select(&mut sel, &mut world, black_box(c));
    });

    bench_batched("FxHashMap (raw, hash + vtable)", || {
        let c = cmds[i & 7];
        i = i.wrapping_add(1);
        probe_hashmap(&mut map, &mut world, black_box(c));
    });

    bench_batched(".dispatch_map (FxHashMap combinator)", || {
        let c = cmds[i & 7];
        i = i.wrapping_add(1);
        probe_dispatch_map(&mut dm, &mut world, black_box(c));
    });

    // --- Projected-key and composite-key dispatch_on ---

    println!();
    print_header("Projected-Key Dispatch (cycles, 8 keys)");

    bench_batched(".dispatch_on (projected key)", || {
        let m = msgs[i & 7];
        i = i.wrapping_add(1);
        probe_dispatch_on(&mut don, &mut world, black_box(m));
    });

    bench_batched(".dispatch_on (tuple-product key)", || {
        let g = grids[i & 7];
        i = i.wrapping_add(1);
        probe_dispatch_on_pair(&mut dpair, &mut world, black_box(g));
    });

    // Keep every accumulate live so nothing is dead-code eliminated.
    black_box(world.resource::<Acc>().0);

    println!();
}
