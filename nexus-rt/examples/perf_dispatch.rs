//! Runtime keyed dispatch latency benchmark (issue #723).
//!
//! Compares the two dispatch-table combinators against the two things they sit
//! between: the compile-time `select!` jump table (faster, arms fixed at compile
//! time) and an `FxHashMap` keyed-dispatch table (the usual runtime-composable
//! alternative, which hashes). For an N-variant enum every arm does the same
//! *shape* of minimal work (fold the payload into a `World` resource) but each
//! arm is a **distinct function**, and keys arrive in a **precomputed random
//! order** rather than a round robin, so the indirect-call target genuinely
//! varies per dispatch and the branch/indirect predictor cannot learn the
//! sequence. Only the dispatch mechanism differs between rows:
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
/// Length of the precomputed random key sequence (power of two so `& (LEN - 1)`
/// masks). Long enough that the key order does not repeat within a batch.
const RAND_LEN: usize = 4096;

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

/// A fixed, precomputed pseudo-random sequence of key indices in `0..modulo`.
/// Feeding keys in this order (rather than a period-`modulo` round robin) keeps
/// the branch/indirect predictor from learning the sequence, so the measured
/// cost reflects a realistic mispredict rate instead of a perfectly-predicted
/// loop. Deterministic (fixed seed) so runs are comparable.
fn random_indices(len: usize, modulo: usize) -> Vec<usize> {
    let mut x: u64 = 0x9E37_79B9_7F4A_7C15;
    (0..len)
        .map(|_| {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            (x as usize) % modulo
        })
        .collect()
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
// Arms — every arm is a DISTINCT function doing the same *shape* of minimal work
// (fold the payload plus a per-arm constant into the accumulator). Same shape
// keeps the per-arm cost equal across keys; distinct bodies keep the branch /
// indirect predictor honest (identical-code-folding cannot collapse them to one
// call target).
// =============================================================================

/// Extract the `u64` payload carried by every `Cmd` variant.
#[inline(always)]
fn cmd_payload(cmd: &Cmd) -> u64 {
    match cmd {
        Cmd::V0(p)
        | Cmd::V1(p)
        | Cmd::V2(p)
        | Cmd::V3(p)
        | Cmd::V4(p)
        | Cmd::V5(p)
        | Cmd::V6(p)
        | Cmd::V7(p) => *p,
    }
}

/// Generate distinct arm functions, one per entry. Each folds a distinct
/// constant, so no two share an implementation and ICF cannot merge them.
macro_rules! bench_arms {
    ($( $name:ident($v:ident: $ty:ty) = $body:expr ; )*) => {
        $(
            #[allow(clippy::needless_pass_by_value)]
            fn $name(mut acc: ResMut<Acc>, $v: $ty) {
                acc.0 = acc.0.wrapping_add($body);
            }
        )*
    };
}

bench_arms! {
    // .dispatch_variant arms: receive the unwrapped u64 payload.
    pv0(p: u64) = p ^ 0xA1; pv1(p: u64) = p ^ 0xB2; pv2(p: u64) = p ^ 0xC3;
    pv3(p: u64) = p ^ 0xD4; pv4(p: u64) = p ^ 0xE5; pv5(p: u64) = p ^ 0xF6;
    pv6(p: u64) = p ^ 0x17; pv7(p: u64) = p ^ 0x28;
    // .dispatch_on arms: receive the whole Msg.
    mv0(m: Msg) = m.payload ^ 0xA1; mv1(m: Msg) = m.payload ^ 0xB2;
    mv2(m: Msg) = m.payload ^ 0xC3; mv3(m: Msg) = m.payload ^ 0xD4;
    mv4(m: Msg) = m.payload ^ 0xE5; mv5(m: Msg) = m.payload ^ 0xF6;
    mv6(m: Msg) = m.payload ^ 0x17; mv7(m: Msg) = m.payload ^ 0x28;
    // tuple-product .dispatch_on arms: receive the whole Grid.
    gv0(g: Grid) = g.payload ^ 0xA1; gv1(g: Grid) = g.payload ^ 0xB2;
    gv2(g: Grid) = g.payload ^ 0xC3; gv3(g: Grid) = g.payload ^ 0xD4;
    gv4(g: Grid) = g.payload ^ 0xE5; gv5(g: Grid) = g.payload ^ 0xF6;
    gv6(g: Grid) = g.payload ^ 0x17; gv7(g: Grid) = g.payload ^ 0x28;
    // select! / FxHashMap / .dispatch_map arms: receive the whole Cmd.
    cv0(c: Cmd) = cmd_payload(&c) ^ 0xA1; cv1(c: Cmd) = cmd_payload(&c) ^ 0xB2;
    cv2(c: Cmd) = cmd_payload(&c) ^ 0xC3; cv3(c: Cmd) = cmd_payload(&c) ^ 0xD4;
    cv4(c: Cmd) = cmd_payload(&c) ^ 0xE5; cv5(c: Cmd) = cmd_payload(&c) ^ 0xF6;
    cv6(c: Cmd) = cmd_payload(&c) ^ 0x17; cv7(c: Cmd) = cmd_payload(&c) ^ 0x28;
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

/// Baseline: a single `.then` step, **no dispatch at all**. Isolates the shared
/// per-call floor every row pays — the `#[inline(never)]` probe call,
/// `Pipeline::run`, resolving `ResMut<Acc>` from the `World`, and the add — so a
/// dispatch row's cost *over this* is the dispatch mechanism itself.
#[inline(never)]
pub fn probe_baseline(p: &mut impl Handler<Cmd>, world: &mut nexus_rt::World, cmd: Cmd) {
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
            d.arm(cmd_variants::V0, pv0)
                .arm(cmd_variants::V1, pv1)
                .arm(cmd_variants::V2, pv2)
                .arm(cmd_variants::V3, pv3)
                .arm(cmd_variants::V4, pv4)
                .arm(cmd_variants::V5, pv5)
                .arm(cmd_variants::V6, pv6)
                .arm(cmd_variants::V7, pv7)
        })
        .build();

    // --- .dispatch_on table (projected key, arms get the whole value) ---

    let mut don = PipelineBuilder::<Msg>::new()
        .dispatch_on(
            |m: &Msg| m.kind,
            r,
            |d| {
                d.arm(Kind::K0, mv0)
                    .arm(Kind::K1, mv1)
                    .arm(Kind::K2, mv2)
                    .arm(Kind::K3, mv3)
                    .arm(Kind::K4, mv4)
                    .arm(Kind::K5, mv5)
                    .arm(Kind::K6, mv6)
                    .arm(Kind::K7, mv7)
            },
        )
        .build();

    // --- .dispatch_on with a tuple-product composite key ---

    let mut dpair = PipelineBuilder::<Grid>::new()
        .dispatch_on(
            |g: &Grid| (g.a, g.b),
            r,
            |d| {
                d.arm((Coarse::X, Fine::P), gv0)
                    .arm((Coarse::X, Fine::Q), gv1)
                    .arm((Coarse::X, Fine::R), gv2)
                    .arm((Coarse::X, Fine::S), gv3)
                    .arm((Coarse::Y, Fine::P), gv4)
                    .arm((Coarse::Y, Fine::Q), gv5)
                    .arm((Coarse::Y, Fine::R), gv6)
                    .arm((Coarse::Y, Fine::S), gv7)
            },
        )
        .build();

    // --- select! baseline (compile-time arms, one match / jump table) ---

    let mut sel = PipelineBuilder::<Cmd>::new()
        .then(
            select! {
                r,
                Cmd::V0(..) => cv0,
                Cmd::V1(..) => cv1,
                Cmd::V2(..) => cv2,
                Cmd::V3(..) => cv3,
                Cmd::V4(..) => cv4,
                Cmd::V5(..) => cv5,
                Cmd::V6(..) => cv6,
                Cmd::V7(..) => cv7,
            },
            r,
        )
        .build();

    // --- baseline: a single `.then(cv0)`, no dispatch (the shared floor) ---

    let mut base = PipelineBuilder::<Cmd>::new().then(cv0, r).build();

    // --- FxHashMap baseline (runtime table via hashing) ---

    // Distinct boxed handler per key, so the vtable call target varies per key.
    let mut map: FxHashMap<usize, Box<dyn Handler<Cmd>>> = FxHashMap::default();
    map.insert(0, Box::new(cv0.into_handler(r)));
    map.insert(1, Box::new(cv1.into_handler(r)));
    map.insert(2, Box::new(cv2.into_handler(r)));
    map.insert(3, Box::new(cv3.into_handler(r)));
    map.insert(4, Box::new(cv4.into_handler(r)));
    map.insert(5, Box::new(cv5.into_handler(r)));
    map.insert(6, Box::new(cv6.into_handler(r)));
    map.insert(7, Box::new(cv7.into_handler(r)));

    // --- .dispatch_map table (Hash+Eq key via FxHashMap; whole-value arms) ---

    let mut dm = PipelineBuilder::<Cmd>::new()
        .dispatch_map(
            |c: &Cmd| c.ordinal(),
            r,
            |d| {
                d.arm(0usize, cv0)
                    .arm(1usize, cv1)
                    .arm(2usize, cv2)
                    .arm(3usize, cv3)
                    .arm(4usize, cv4)
                    .arm(5usize, cv5)
                    .arm(6usize, cv6)
                    .arm(7usize, cv7)
                    .default_noop()
            },
        )
        .build();

    // --- Inputs, indexed by a precomputed random key order (see `idxs`) ---

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

    // Precomputed random key order: each bench indexes its input array by
    // `idxs[i & (RAND_LEN - 1)]`, so successive dispatches hit unpredictable
    // keys (and thus unpredictable arm targets), not a learnable round robin.
    let idxs = random_indices(RAND_LEN, 8);

    // --- Discriminant dispatch: table vs jump table vs hashmap (same key) ---

    print_header("Keyed Dispatch on Discriminant (cycles, 8 variants)");

    let mut i = 0usize;

    bench_batched("baseline: single .then (no dispatch)", || {
        let c = cmds[idxs[i & (RAND_LEN - 1)]];
        i = i.wrapping_add(1);
        probe_baseline(&mut base, &mut world, black_box(c));
    });

    bench_batched(".dispatch_variant (array index)", || {
        let c = cmds[idxs[i & (RAND_LEN - 1)]];
        i = i.wrapping_add(1);
        probe_dispatch_variant(&mut dv, &mut world, black_box(c));
    });

    bench_batched("select! (jump table, inlined)", || {
        let c = cmds[idxs[i & (RAND_LEN - 1)]];
        i = i.wrapping_add(1);
        probe_select(&mut sel, &mut world, black_box(c));
    });

    bench_batched("FxHashMap (raw, hash + vtable)", || {
        let c = cmds[idxs[i & (RAND_LEN - 1)]];
        i = i.wrapping_add(1);
        probe_hashmap(&mut map, &mut world, black_box(c));
    });

    bench_batched(".dispatch_map (FxHashMap combinator)", || {
        let c = cmds[idxs[i & (RAND_LEN - 1)]];
        i = i.wrapping_add(1);
        probe_dispatch_map(&mut dm, &mut world, black_box(c));
    });

    // --- Projected-key and composite-key dispatch_on ---

    println!();
    print_header("Projected-Key Dispatch (cycles, 8 keys)");

    bench_batched(".dispatch_on (projected key)", || {
        let m = msgs[idxs[i & (RAND_LEN - 1)]];
        i = i.wrapping_add(1);
        probe_dispatch_on(&mut don, &mut world, black_box(m));
    });

    bench_batched(".dispatch_on (tuple-product key)", || {
        let g = grids[idxs[i & (RAND_LEN - 1)]];
        i = i.wrapping_add(1);
        probe_dispatch_on_pair(&mut dpair, &mut world, black_box(g));
    });

    // Keep every accumulate live so nothing is dead-code eliminated.
    black_box(world.resource::<Acc>().0);

    println!();
}
