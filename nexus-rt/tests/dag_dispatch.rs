//! Integration tests for the `.dispatch_on()` DAG combinator (issue #723,
//! Phase 3b) on `DagChain`/`DagBuilder` and `CtxDagChain`/`CtxDagBuilder`.
//!
//! The DAG twist versus the pipeline `.dispatch_on()`: DAG steps take their
//! value **by reference**, so every arm here receives `&Tick`, not an owned
//! `Tick`. The erased arm table stores reference-taking steps
//! (`Box<dyn for<'a> StepCall<&'a V, Out = ()> + Send>`); these tests exercise
//! that the borrowed value actually reaches the chosen arm.
//!
//! `.dispatch_variant()` is intentionally not provided on the DAG surface (see
//! the doc comment on `DagChain::dispatch_on`), so it is not tested here.
//!
//! Coverage: correct arm per key, unset key -> no-op, `.default` override,
//! entry form (dispatch as the DAG root), a borrowing closure arm, a
//! tuple-product composite key, and the ctx (`CtxDagChain`/`CtxDagBuilder`)
//! variant threading `&mut C`.

// DAG steps take their input by reference, so value-return continuations receive
// `&u64` — the trivially-copyable-ref lint is expected here (as in `compile_tests`).
#![allow(clippy::trivially_copy_pass_by_ref)]

use nexus_rt::{
    CtxDagBuilder, DagBuilder, Dispatchable, Handler, Res, ResMut, Resource, World, WorldBuilder,
};

// Projected key: a fieldless discriminant carried as a struct field. `Copy` so
// `key_fn` can read it out of `&Tick` by value.
#[derive(Dispatchable, Clone, Copy)]
enum Source {
    A, // ordinal 0
    B, // ordinal 1
    C, // ordinal 2 — left unset in most wirings below
}

// The whole value each arm *borrows*. No `Copy` needed: DAG arms take `&Tick`.
struct Tick {
    source: Source,
    px: u64,
}

// Records which arm fired and the whole-value `px` it saw through the borrow.
#[derive(Resource, Default)]
struct Log {
    a: Option<u64>,
    b: Option<u64>,
    fallback: Option<u64>,
}

// Named-fn arms: params first, borrowed value last (`&Tick`).
fn on_a(mut log: ResMut<Log>, t: &Tick) {
    log.a = Some(t.px);
}

fn on_b(mut log: ResMut<Log>, t: &Tick) {
    log.b = Some(t.px);
}

fn on_default(mut log: ResMut<Log>, t: &Tick) {
    log.fallback = Some(t.px);
}

// Identity root: hands the owned event straight to `.dispatch_on`, which then
// borrows it for the arms. Exercises the *continuation* form (DagChain).
fn root_identity(t: Tick) -> Tick {
    t
}

#[test]
fn dag_routes_on_projected_key_and_borrows_whole_value() {
    let mut wb = WorldBuilder::new();
    wb.register(Log::default());
    let mut world = wb.build();
    let reg = world.registry();

    let mut dag = DagBuilder::<Tick>::new()
        .root(root_identity, reg)
        .dispatch_on(
            |t: &Tick| t.source,
            reg,
            // `Source::C` intentionally unset — routed to the explicit no-op.
            |d| d.arm(Source::A, on_a).arm(Source::B, on_b).default_noop(),
        )
        .build();

    dag.run(
        &mut world,
        Tick {
            source: Source::A,
            px: 100,
        },
    );
    dag.run(
        &mut world,
        Tick {
            source: Source::B,
            px: 200,
        },
    );
    dag.run(
        &mut world,
        Tick {
            source: Source::C,
            px: 300,
        },
    ); // unset → no-op

    let log = world.resource::<Log>();
    // Right arm fired, and each arm saw the whole borrowed `Tick` (its `px`).
    assert_eq!(log.a, Some(100));
    assert_eq!(log.b, Some(200));
    // Unset key hit the no-op fallback — no default installed, nothing ran.
    assert_eq!(log.fallback, None);
}

#[test]
fn dag_unset_keys_route_to_default_when_set() {
    let mut wb = WorldBuilder::new();
    wb.register(Log::default());
    let mut world = wb.build();
    let reg = world.registry();

    let mut dag = DagBuilder::<Tick>::new()
        .root(root_identity, reg)
        .dispatch_on(
            |t: &Tick| t.source,
            reg,
            |d| d.arm(Source::A, on_a).default(on_default),
        )
        .build();

    dag.run(
        &mut world,
        Tick {
            source: Source::A,
            px: 11,
        },
    ); // matched arm
    dag.run(
        &mut world,
        Tick {
            source: Source::B,
            px: 22,
        },
    ); // unset → default
    dag.run(
        &mut world,
        Tick {
            source: Source::C,
            px: 33,
        },
    ); // unset → default

    let log = world.resource::<Log>();
    assert_eq!(log.a, Some(11));
    // Last unset key to hit the default wins the recorded px.
    assert_eq!(log.fallback, Some(33));
    // The default arm is the only thing that ran for B/C; the B arm never fired.
    assert_eq!(log.b, None);
}

#[test]
fn dag_builder_entry_form_dispatches_at_root() {
    // Entry form: `.dispatch_on` is the DAG's first step (DagBuilder), so the
    // owned event `E` is borrowed straight into the arms.
    let mut wb = WorldBuilder::new();
    wb.register(Log::default());
    let mut world = wb.build();
    let reg = world.registry();

    let mut dag = DagBuilder::<Tick>::new()
        .dispatch_on(
            |t: &Tick| t.source,
            reg,
            |d| d.arm(Source::A, on_a).arm(Source::B, on_b).default_noop(),
        )
        .build();

    dag.run(
        &mut world,
        Tick {
            source: Source::B,
            px: 55,
        },
    );
    dag.run(
        &mut world,
        Tick {
            source: Source::C,
            px: 66,
        },
    ); // unset → no-op

    let log = world.resource::<Log>();
    assert_eq!(log.b, Some(55));
    assert_eq!(log.a, None);
    assert_eq!(log.fallback, None);
}

#[test]
fn dag_closure_arm_borrows_whole_value() {
    // Arity-0 closure arm (no resource params) that borrows `&Tick`. Writes
    // into a world resource via the Opaque `&mut World` closure form to keep
    // the arm self-contained.
    let mut wb = WorldBuilder::new();
    wb.register(Log::default());
    let mut world = wb.build();
    let reg = world.registry();

    let mut dag = DagBuilder::<Tick>::new()
        .root(root_identity, reg)
        .dispatch_on(
            |t: &Tick| t.source,
            reg,
            |d| {
                d.arm(Source::A, |w: &mut World, t: &Tick| {
                    w.resource_mut::<Log>().a = Some(t.px);
                })
                .default_noop()
            },
        )
        .build();

    dag.run(
        &mut world,
        Tick {
            source: Source::A,
            px: 777,
        },
    );
    dag.run(
        &mut world,
        Tick {
            source: Source::B,
            px: 999,
        },
    ); // unset → no-op

    assert_eq!(world.resource::<Log>().a, Some(777));
}

// -- tuple-product composite key --------------------------------------------

#[derive(Dispatchable, Clone, Copy)]
enum Coarse {
    X, // ordinal 0
    Y, // ordinal 1
}

#[derive(Dispatchable, Clone, Copy)]
enum Fine {
    P, // ordinal 0
    Q, // ordinal 1
    R, // ordinal 2
}

struct Grid {
    a: Coarse,
    b: Fine,
    tag: u64,
}

#[derive(Resource, Default)]
struct PairLog {
    fired: Vec<(usize, u64)>,
}

fn on_xp(mut log: ResMut<PairLog>, g: &Grid) {
    log.fired.push((0, g.tag));
}
fn on_yq(mut log: ResMut<PairLog>, g: &Grid) {
    log.fired.push((4, g.tag));
}
fn on_yr(mut log: ResMut<PairLog>, g: &Grid) {
    log.fired.push((5, g.tag));
}

#[test]
fn dag_dispatch_on_tuple_product_key() {
    let mut wb = WorldBuilder::new();
    wb.register(PairLog::default());
    let mut world = wb.build();
    let reg = world.registry();

    let mut dag = DagBuilder::<Grid>::new()
        .root(|g: Grid| g, reg)
        .dispatch_on(
            |g: &Grid| (g.a, g.b),
            reg,
            |d| {
                d.arm((Coarse::X, Fine::P), on_xp)
                    .arm((Coarse::Y, Fine::Q), on_yq)
                    .arm((Coarse::Y, Fine::R), on_yr)
                    .default_noop()
            },
        )
        .build();

    dag.run(
        &mut world,
        Grid {
            a: Coarse::X,
            b: Fine::P,
            tag: 1,
        },
    );
    dag.run(
        &mut world,
        Grid {
            a: Coarse::Y,
            b: Fine::Q,
            tag: 2,
        },
    );
    dag.run(
        &mut world,
        Grid {
            a: Coarse::Y,
            b: Fine::R,
            tag: 3,
        },
    );
    // An unwired pair falls through to the no-op.
    dag.run(
        &mut world,
        Grid {
            a: Coarse::X,
            b: Fine::Q,
            tag: 4,
        },
    );

    let log = world.resource::<PairLog>();
    assert_eq!(log.fired, vec![(0, 1), (4, 2), (5, 3)]);
}

// -- ctx DAG (`CtxDagChain` / `CtxDagBuilder`) --------------------------------

// Per-instance context the arms mutate. Proving `&mut C` is threaded is the
// point: every arm records into this, and the tests assert the writes.
#[derive(Default)]
struct Ctx {
    a: Option<u64>,
    b: Option<u64>,
    fallback: Option<u64>,
    // Bumped by a resource-scaled arm to prove Params resolve alongside ctx.
    scaled: u64,
}

// A world resource, to exercise the named-fn + Param tier: ctx first, then
// resources, then the borrowed value last.
#[derive(Resource)]
struct Scale(u64);

// Ctx arm using only ctx and the borrowed value.
fn ctx_on_a(ctx: &mut Ctx, t: &Tick) {
    ctx.a = Some(t.px);
}

// Ctx arm with a resolved resource Param between ctx and the borrowed value.
fn ctx_on_b(ctx: &mut Ctx, scale: Res<Scale>, t: &Tick) {
    ctx.b = Some(t.px);
    ctx.scaled = t.px * scale.0;
}

fn ctx_on_default(ctx: &mut Ctx, t: &Tick) {
    ctx.fallback = Some(t.px);
}

// Ctx identity root: `fn(&mut C, E) -> Out`.
fn ctx_root_identity(_ctx: &mut Ctx, t: Tick) -> Tick {
    t
}

#[test]
fn ctx_dag_dispatch_on_threads_ctx_and_borrows_value() {
    let mut wb = WorldBuilder::new();
    wb.register(Scale(10));
    let mut world = wb.build();
    let reg = world.registry();

    // Continuation form on CtxDagChain (after `.root`).
    let mut dag = CtxDagBuilder::<Ctx, Tick>::new()
        .root(ctx_root_identity, reg)
        .dispatch_on(
            |t: &Tick| t.source,
            reg,
            |d| {
                d.arm(Source::A, ctx_on_a)
                    .arm(Source::B, ctx_on_b)
                    .default_noop()
            },
        )
        .build();

    let mut ctx = Ctx::default();
    dag.run(
        &mut ctx,
        &mut world,
        Tick {
            source: Source::A,
            px: 100,
        },
    );
    dag.run(
        &mut ctx,
        &mut world,
        Tick {
            source: Source::B,
            px: 20,
        },
    );
    dag.run(
        &mut ctx,
        &mut world,
        Tick {
            source: Source::C,
            px: 300,
        },
    ); // unset → no-op

    // Both arms threaded `&mut C` and saw the borrowed value.
    assert_eq!(ctx.a, Some(100));
    assert_eq!(ctx.b, Some(20));
    // Resource Param resolved alongside ctx: 20 * 10.
    assert_eq!(ctx.scaled, 200);
    // Unset key ran the no-op — ctx untouched for that path.
    assert_eq!(ctx.fallback, None);
}

#[test]
fn ctx_dag_dispatch_on_default_override() {
    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    let mut dag = CtxDagBuilder::<Ctx, Tick>::new()
        .root(ctx_root_identity, reg)
        .dispatch_on(
            |t: &Tick| t.source,
            reg,
            |d| d.arm(Source::A, ctx_on_a).default(ctx_on_default),
        )
        .build();

    let mut ctx = Ctx::default();
    dag.run(
        &mut ctx,
        &mut world,
        Tick {
            source: Source::A,
            px: 11,
        },
    ); // matched arm
    dag.run(
        &mut ctx,
        &mut world,
        Tick {
            source: Source::C,
            px: 33,
        },
    ); // unset → default

    assert_eq!(ctx.a, Some(11));
    assert_eq!(ctx.fallback, Some(33));
    assert_eq!(ctx.b, None);
}

#[test]
fn ctx_dag_builder_entry_form_dispatches_at_root() {
    // Entry form on CtxDagBuilder: dispatch as the ctx DAG's first step.
    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    let mut dag = CtxDagBuilder::<Ctx, Tick>::new()
        .dispatch_on(
            |t: &Tick| t.source,
            reg,
            |d| d.arm(Source::A, ctx_on_a).default_noop(),
        )
        .build();

    let mut ctx = Ctx::default();
    dag.run(
        &mut ctx,
        &mut world,
        Tick {
            source: Source::A,
            px: 42,
        },
    );
    dag.run(
        &mut ctx,
        &mut world,
        Tick {
            source: Source::B,
            px: 99,
        },
    ); // unset → no-op

    assert_eq!(ctx.a, Some(42));
    assert_eq!(ctx.b, None);
}

// -- value-return dispatch (issue #723, Phase 5b) ----------------------------
//
// DAG mirror of `tests/dispatch_value_return.rs`: `dispatch_on` arms borrow
// `&V` and RETURN a `u64` that bubbles up out of the dispatch node into
// `.then(...)`. Because DAG steps take their input by reference, the
// continuation also borrows the bubbled value (`&u64`). Covers value-return
// (exhaustive and with `.default`) and the construction-time exhaustive-or-
// `.default` panic, for both the plain and ctx DAG surfaces.

#[derive(Dispatchable, Clone, Copy)]
enum VrKey {
    X, // ordinal 0
    Y, // ordinal 1
}

// The whole value each arm borrows.
struct VrTick {
    key: VrKey,
    px: u64,
}

// Collects the values bubbled out of the dispatch node into `.then`.
#[derive(Resource, Default)]
struct VrSink(Vec<u64>);

// dispatch_on arms borrow `&VrTick` and RETURN a `u64`.
fn vr_on_x(t: &VrTick) -> u64 {
    t.px + 10
}
fn vr_on_y(t: &VrTick) -> u64 {
    t.px + 20
}
fn vr_default(t: &VrTick) -> u64 {
    t.px + 900
}
// Continuation borrows the bubbled-up value (`&u64`, DAG-by-reference).
fn vr_consume(mut sink: ResMut<VrSink>, v: &u64) {
    sink.0.push(*v);
}

#[test]
fn dag_on_value_bubbles_up_to_then() {
    let mut wb = WorldBuilder::new();
    wb.register(VrSink::default());
    let mut world = wb.build();
    let reg = world.registry();

    // Exhaustive table (both keys armed), arms return `u64`, no `.default`. The
    // value bubbles up into `.then(vr_consume)`, which borrows it.
    let mut dag = DagBuilder::<VrTick>::new()
        .root(|t: VrTick| t, reg)
        .dispatch_on(
            |t: &VrTick| t.key,
            reg,
            |d| d.arm(VrKey::X, vr_on_x).arm(VrKey::Y, vr_on_y),
        )
        .then(vr_consume, reg)
        .build();

    dag.run(
        &mut world,
        VrTick {
            key: VrKey::X,
            px: 1,
        },
    ); // 11
    dag.run(
        &mut world,
        VrTick {
            key: VrKey::Y,
            px: 2,
        },
    ); // 22

    assert_eq!(world.resource::<VrSink>().0, vec![11, 22]);
}

#[test]
fn dag_on_value_return_with_default() {
    let mut wb = WorldBuilder::new();
    wb.register(VrSink::default());
    let mut world = wb.build();
    let reg = world.registry();

    // Non-exhaustive: only `X` armed, `.default` supplies the fallback value for
    // the unset key. Both arm and default return `Out = u64`.
    let mut dag = DagBuilder::<VrTick>::new()
        .root(|t: VrTick| t, reg)
        .dispatch_on(
            |t: &VrTick| t.key,
            reg,
            |d| d.arm(VrKey::X, vr_on_x).default(vr_default),
        )
        .then(vr_consume, reg)
        .build();

    dag.run(
        &mut world,
        VrTick {
            key: VrKey::X,
            px: 1,
        },
    ); // matched → 11
    dag.run(
        &mut world,
        VrTick {
            key: VrKey::Y,
            px: 2,
        },
    ); // unset → default 902

    assert_eq!(world.resource::<VrSink>().0, vec![11, 902]);
}

fn vr_unit_x(_t: &VrTick) {}

#[test]
#[should_panic(expected = "no `.default`")]
fn dag_on_non_exhaustive_no_default_panics_at_construction() {
    let world = WorldBuilder::new().build();
    let reg = world.registry();

    // Only `X` of {X, Y} armed, no `.default`/`.default_noop()` → panic here,
    // inside `.dispatch_on`, before `.build()`.
    let _dag = DagBuilder::<VrTick>::new()
        .root(|t: VrTick| t, reg)
        .dispatch_on(|t: &VrTick| t.key, reg, |d| d.arm(VrKey::X, vr_unit_x))
        .build();
}

// -- ctx DAG value-return ----------------------------------------------------

// Per-instance ctx that collects the bubbled-up values.
#[derive(Default)]
struct VrCtx {
    sink: Vec<u64>,
}

// Ctx arms thread `&mut C`, borrow `&VrTick`, and RETURN a `u64`.
fn ctx_vr_on_x(_c: &mut VrCtx, t: &VrTick) -> u64 {
    t.px + 10
}
fn ctx_vr_on_y(_c: &mut VrCtx, t: &VrTick) -> u64 {
    t.px + 20
}
fn ctx_vr_default(_c: &mut VrCtx, t: &VrTick) -> u64 {
    t.px + 900
}
// Ctx continuation: threads `&mut C` and borrows the bubbled value (`&u64`).
fn ctx_vr_consume(c: &mut VrCtx, v: &u64) {
    c.sink.push(*v);
}

#[test]
fn ctx_dag_on_value_bubbles_up_to_then() {
    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    let mut dag = CtxDagBuilder::<VrCtx, VrTick>::new()
        .root(|_c: &mut VrCtx, t: VrTick| t, reg)
        .dispatch_on(
            |t: &VrTick| t.key,
            reg,
            |d| d.arm(VrKey::X, ctx_vr_on_x).arm(VrKey::Y, ctx_vr_on_y),
        )
        .then(ctx_vr_consume, reg)
        .build();

    let mut ctx = VrCtx::default();
    dag.run(
        &mut ctx,
        &mut world,
        VrTick {
            key: VrKey::X,
            px: 1,
        },
    ); // 11
    dag.run(
        &mut ctx,
        &mut world,
        VrTick {
            key: VrKey::Y,
            px: 2,
        },
    ); // 22

    assert_eq!(ctx.sink, vec![11, 22]);
}

#[test]
fn ctx_dag_on_value_return_with_default() {
    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    let mut dag = CtxDagBuilder::<VrCtx, VrTick>::new()
        .root(|_c: &mut VrCtx, t: VrTick| t, reg)
        .dispatch_on(
            |t: &VrTick| t.key,
            reg,
            |d| d.arm(VrKey::X, ctx_vr_on_x).default(ctx_vr_default),
        )
        .then(ctx_vr_consume, reg)
        .build();

    let mut ctx = VrCtx::default();
    dag.run(
        &mut ctx,
        &mut world,
        VrTick {
            key: VrKey::X,
            px: 1,
        },
    ); // matched → 11
    dag.run(
        &mut ctx,
        &mut world,
        VrTick {
            key: VrKey::Y,
            px: 2,
        },
    ); // unset → default 902

    assert_eq!(ctx.sink, vec![11, 902]);
}

fn ctx_vr_unit_x(_c: &mut VrCtx, _t: &VrTick) {}

#[test]
#[should_panic(expected = "no `.default`")]
fn ctx_dag_on_non_exhaustive_no_default_panics_at_construction() {
    let world = WorldBuilder::new().build();
    let reg = world.registry();

    let _dag = CtxDagBuilder::<VrCtx, VrTick>::new()
        .root(|_c: &mut VrCtx, t: VrTick| t, reg)
        .dispatch_on(|t: &VrTick| t.key, reg, |d| d.arm(VrKey::X, ctx_vr_unit_x))
        .build();
}
