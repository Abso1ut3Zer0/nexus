//! Integration tests for the context-aware dispatch combinators
//! `.dispatch_variant()` and `.dispatch_on()` on `CtxPipeline` (issue #723,
//! Phase 3a).
//!
//! These mirror `tests/dispatch_variant.rs` + `tests/dispatch_on.rs` but thread
//! `&mut C` through every arm. The key thing under test — beyond parity with
//! the non-ctx versions — is that the per-instance context `C` actually reaches
//! the arms: every arm mutates `C`, and each test asserts the mutation. The
//! context-first step convention is `fn(&mut C, Params..., In)`.
//!
//! Runs in the default (debug) profile so the `debug_assert!` inside the
//! generated `unwrap` is active — every arm here is indexed by the value's own
//! ordinal, so the happy path must never trip it.

use nexus_rt::{CtxPipelineBuilder, Dispatchable, Res, Resource, WorldBuilder};

// -- dispatch_variant --------------------------------------------------------

// Mixed variant shapes: single unnamed field (typed payload), multi-field
// tuple, unit, and `Cancel` — intentionally left UNSET in the wiring below.
#[derive(Dispatchable)]
enum Cmd {
    RouteAway(u32),    // ordinal 0 — single-field payload
    Reprice(u32, i64), // ordinal 1 — multi-field tuple payload
    Halt,              // ordinal 2 — unit payload `()`
    // Left unset in the wiring below and routed to the no-op/default, so its
    // payload is deliberately never unwrapped — hence the dead_code allow.
    #[allow(dead_code)]
    Cancel(u64), // ordinal 3 — left unset
}

// Per-instance context the arms mutate. Proving `&mut C` is threaded is the
// whole point: every arm records into this, and the tests assert the writes.
#[derive(Default)]
struct Ctx {
    route_away: Option<u32>,
    reprice: Option<(u32, i64)>,
    halt_count: u32,
    default_hits: u32,
    // Bumped by a resource-scaled arm to prove Params resolve alongside ctx.
    scaled: u64,
}

// A world resource, to exercise the named-fn + Param tier (context first, then
// resources, then the variant payload last).
#[derive(Resource)]
struct Scale(u64);

// Named-fn arm using ONLY ctx (arity-0 closure would also work, but a named fn
// keeps parity with the non-ctx tests).
fn on_route_away(ctx: &mut Ctx, payload: u32) {
    ctx.route_away = Some(payload);
}

// Named-fn arm with a resolved resource Param between ctx and payload.
fn on_reprice(ctx: &mut Ctx, scale: Res<Scale>, payload: (u32, i64)) {
    ctx.reprice = Some(payload);
    ctx.scaled = payload.0 as u64 * scale.0;
}

fn on_halt(ctx: &mut Ctx, _payload: ()) {
    ctx.halt_count += 1;
}

// Default arm receives ctx and the whole enum, not a payload.
fn on_default(ctx: &mut Ctx, _cmd: Cmd) {
    ctx.default_hits += 1;
}

#[test]
fn variant_threads_ctx_and_unwraps_payload() {
    let mut wb = WorldBuilder::new();
    wb.register(Scale(10));
    let mut world = wb.build();
    let reg = world.registry();

    let mut pipeline = CtxPipelineBuilder::<Ctx, Cmd>::new()
        .dispatch_variant(reg, |d| {
            d.arm(cmd_variants::RouteAway, on_route_away)
                .arm(cmd_variants::Reprice, on_reprice)
                .arm(cmd_variants::Halt, on_halt)
                // `Cancel` intentionally unset — routed to the explicit no-op.
                .default_noop()
        })
        .build();

    let mut ctx = Ctx::default();
    pipeline.run(&mut ctx, &mut world, Cmd::RouteAway(42));
    pipeline.run(&mut ctx, &mut world, Cmd::Reprice(7, -3));
    pipeline.run(&mut ctx, &mut world, Cmd::Halt);
    pipeline.run(&mut ctx, &mut world, Cmd::Cancel(999)); // unset → no-op

    // Right arm fired, payload unwrapped (single field + tuple), and every
    // write landed in the threaded `&mut Ctx`.
    assert_eq!(ctx.route_away, Some(42));
    assert_eq!(ctx.reprice, Some((7, -3)));
    assert_eq!(ctx.scaled, 70); // 7 * Scale(10) — Param resolved next to ctx
    assert_eq!(ctx.halt_count, 1);
    // Unset variant hit the no-op fallback — no default installed, nothing ran.
    assert_eq!(ctx.default_hits, 0);
}

#[test]
fn variant_unset_routes_to_default_when_set() {
    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    let mut pipeline = CtxPipelineBuilder::<Ctx, Cmd>::new()
        .dispatch_variant(reg, |d| {
            d.arm(cmd_variants::RouteAway, on_route_away)
                .default(on_default)
        })
        .build();

    let mut ctx = Ctx::default();
    pipeline.run(&mut ctx, &mut world, Cmd::RouteAway(5)); // matched arm
    pipeline.run(&mut ctx, &mut world, Cmd::Reprice(2, 3)); // unset → default
    pipeline.run(&mut ctx, &mut world, Cmd::Halt); // unset → default
    pipeline.run(&mut ctx, &mut world, Cmd::Cancel(1)); // unset → default

    assert_eq!(ctx.route_away, Some(5));
    // The three unset variants all routed to the default arm (via `&mut Ctx`).
    assert_eq!(ctx.default_hits, 3);
    // The default never touches these.
    assert_eq!(ctx.reprice, None);
    assert_eq!(ctx.halt_count, 0);
}

#[test]
fn variant_closure_arm_mutates_ctx() {
    // Arity-0 closure arm (no resource params): `FnMut(&mut C, In)`. The arm
    // mutates ctx directly — no captured sink needed, since threading `&mut C`
    // is exactly what we assert.
    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    let mut pipeline = CtxPipelineBuilder::<Ctx, Cmd>::new()
        .dispatch_variant(reg, |d| {
            d.arm(cmd_variants::RouteAway, |ctx: &mut Ctx, p: u32| {
                ctx.route_away = Some(p);
            })
            .default_noop()
        })
        .build();

    let mut ctx = Ctx::default();
    pipeline.run(&mut ctx, &mut world, Cmd::RouteAway(123));
    pipeline.run(&mut ctx, &mut world, Cmd::Halt); // unset → no-op, closure untouched

    assert_eq!(ctx.route_away, Some(123));
}

#[test]
fn variant_continuation_form_after_then() {
    // Exercises `CtxPipelineChain::dispatch_variant` (not the builder entry):
    // a `.then` maps input to a Cmd, then dispatch on that Cmd's discriminant.
    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    let mut pipeline = CtxPipelineBuilder::<Ctx, u32>::new()
        .then(
            |ctx: &mut Ctx, x: u32| {
                // Mutate ctx pre-dispatch too, to prove threading spans nodes.
                ctx.halt_count += 1;
                Cmd::RouteAway(x)
            },
            reg,
        )
        .dispatch_variant(reg, |d| {
            d.arm(cmd_variants::RouteAway, on_route_away).default_noop()
        })
        .build();

    let mut ctx = Ctx::default();
    pipeline.run(&mut ctx, &mut world, 88);

    assert_eq!(ctx.halt_count, 1); // the `.then` ran with &mut Ctx
    assert_eq!(ctx.route_away, Some(88)); // the arm ran with &mut Ctx + payload
}

// -- dispatch_on -------------------------------------------------------------

// Projected key: a fieldless discriminant carried as a struct field. `Copy` so
// `key_fn` can read it out of `&Tick` by value.
#[derive(Dispatchable, Clone, Copy)]
enum Source {
    A, // ordinal 0
    B, // ordinal 1
    C, // ordinal 2 — left unset in the wiring below
}

// The whole value each arm receives. `Copy` (POD): arms take it by value, as
// the dispatch API hands the whole value to the chosen arm.
#[derive(Clone, Copy)]
struct Tick {
    source: Source,
    px: u64,
}

// Per-instance context the arms mutate.
#[derive(Default)]
struct OnCtx {
    a: Option<u64>,
    b: Option<u64>,
    fallback: Option<u64>,
}

// Named-fn arms: ctx first, whole value last.
fn on_a(ctx: &mut OnCtx, t: Tick) {
    ctx.a = Some(t.px);
}

fn on_b(ctx: &mut OnCtx, t: Tick) {
    ctx.b = Some(t.px);
}

fn on_fallback(ctx: &mut OnCtx, t: Tick) {
    ctx.fallback = Some(t.px);
}

#[test]
fn dispatch_on_projected_key_threads_ctx_and_whole_value() {
    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    let mut pipeline = CtxPipelineBuilder::<OnCtx, Tick>::new()
        .dispatch_on(
            |t: &Tick| t.source,
            reg,
            // `Source::C` intentionally unset — routed to the explicit no-op.
            |d| d.arm(Source::A, on_a).arm(Source::B, on_b).default_noop(),
        )
        .build();

    let mut ctx = OnCtx::default();
    pipeline.run(
        &mut ctx,
        &mut world,
        Tick {
            source: Source::A,
            px: 100,
        },
    );
    pipeline.run(
        &mut ctx,
        &mut world,
        Tick {
            source: Source::B,
            px: 200,
        },
    );
    pipeline.run(
        &mut ctx,
        &mut world,
        Tick {
            source: Source::C,
            px: 300,
        },
    ); // unset → no-op

    // Right arm fired, each arm saw the whole `Tick`, and each write landed in
    // the threaded `&mut OnCtx`.
    assert_eq!(ctx.a, Some(100));
    assert_eq!(ctx.b, Some(200));
    // Unset key hit the no-op fallback — no default installed, nothing ran.
    assert_eq!(ctx.fallback, None);
}

#[test]
fn dispatch_on_unset_keys_route_to_default_when_set() {
    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    let mut pipeline = CtxPipelineBuilder::<OnCtx, Tick>::new()
        .dispatch_on(
            |t: &Tick| t.source,
            reg,
            |d| d.arm(Source::A, on_a).default(on_fallback),
        )
        .build();

    let mut ctx = OnCtx::default();
    pipeline.run(
        &mut ctx,
        &mut world,
        Tick {
            source: Source::A,
            px: 11,
        },
    ); // matched arm
    pipeline.run(
        &mut ctx,
        &mut world,
        Tick {
            source: Source::B,
            px: 22,
        },
    ); // unset → default
    pipeline.run(
        &mut ctx,
        &mut world,
        Tick {
            source: Source::C,
            px: 33,
        },
    ); // unset → default

    assert_eq!(ctx.a, Some(11));
    // Last unset key to hit the default wins the recorded px.
    assert_eq!(ctx.fallback, Some(33));
    // The default arm is the only thing that ran for B/C; the B arm never fired.
    assert_eq!(ctx.b, None);
}

#[test]
fn dispatch_on_closure_arm_mutates_ctx() {
    // Arity-0 closure arm: `FnMut(&mut C, In)`, receiving the whole value.
    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    let mut pipeline = CtxPipelineBuilder::<OnCtx, Tick>::new()
        .dispatch_on(
            |t: &Tick| t.source,
            reg,
            |d| {
                d.arm(Source::A, |ctx: &mut OnCtx, t: Tick| {
                    ctx.a = Some(t.px);
                })
                .default_noop()
            },
        )
        .build();

    let mut ctx = OnCtx::default();
    pipeline.run(
        &mut ctx,
        &mut world,
        Tick {
            source: Source::A,
            px: 777,
        },
    );
    pipeline.run(
        &mut ctx,
        &mut world,
        Tick {
            source: Source::B,
            px: 999,
        },
    ); // unset → no-op

    assert_eq!(ctx.a, Some(777));
}

// -- tuple-product key + continuation form -----------------------------------

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

#[derive(Clone, Copy)]
struct Grid {
    a: Coarse,
    b: Fine,
    tag: u64,
}

#[derive(Default)]
struct GridCtx {
    // Which composite ordinal fired, and the tag it saw.
    fired: Vec<(usize, u64)>,
}

fn on_xp(ctx: &mut GridCtx, g: Grid) {
    ctx.fired.push((0, g.tag));
}
fn on_yq(ctx: &mut GridCtx, g: Grid) {
    ctx.fired.push((4, g.tag));
}
fn on_yr(ctx: &mut GridCtx, g: Grid) {
    ctx.fired.push((5, g.tag));
}

#[test]
fn dispatch_on_tuple_product_key_continuation_form() {
    // 2 * 3 = 6 dense slots. Also exercises `CtxPipelineChain::dispatch_on`
    // (continuation, after a `.then`) rather than the builder entry point.
    assert_eq!(<(Coarse, Fine)>::VARIANTS, 6);

    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    let mut pipeline = CtxPipelineBuilder::<GridCtx, Grid>::new()
        .then(|_ctx: &mut GridCtx, g: Grid| g, reg)
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

    let mut ctx = GridCtx::default();
    // Each wired pair fires its own arm; distinct pairs map to distinct slots.
    pipeline.run(
        &mut ctx,
        &mut world,
        Grid {
            a: Coarse::X,
            b: Fine::P,
            tag: 1,
        },
    );
    pipeline.run(
        &mut ctx,
        &mut world,
        Grid {
            a: Coarse::Y,
            b: Fine::Q,
            tag: 2,
        },
    );
    pipeline.run(
        &mut ctx,
        &mut world,
        Grid {
            a: Coarse::Y,
            b: Fine::R,
            tag: 3,
        },
    );
    // An unwired pair falls through to the no-op.
    pipeline.run(
        &mut ctx,
        &mut world,
        Grid {
            a: Coarse::X,
            b: Fine::Q,
            tag: 4,
        },
    );

    assert_eq!(ctx.fired, vec![(0, 1), (4, 2), (5, 3)]);
}

// -- value-return dispatch (issue #723, Phase 5b) ----------------------------
//
// Context-aware mirror of `tests/dispatch_value_return.rs`: dispatch arms return
// a `u64` that bubbles up out of the dispatch node into `.then(...)`, threading
// `&mut C` the whole way. Covers `dispatch_variant`/`dispatch_on`/`dispatch_map`
// value-return (exhaustive and with `.default`) and the construction-time
// exhaustive-or-`.default` panics.

#[derive(Dispatchable, Clone, Copy)]
enum Sig {
    A(u64), // ordinal 0 — single-field payload
    B(u64), // ordinal 1 — single-field payload
    C,      // ordinal 2 — unit payload `()`
}

// Ctx that collects the values bubbled out of the dispatch node into `.then`.
#[derive(Default)]
struct VrCtx {
    sink: Vec<u64>,
}

// Variant arms: receive `&mut C` + the unwrapped payload, RETURN a `u64`.
fn ctx_a_arm(_c: &mut VrCtx, p: u64) -> u64 {
    p + 1000
}
fn ctx_b_arm(_c: &mut VrCtx, p: u64) -> u64 {
    p + 2000
}
fn ctx_c_arm(_c: &mut VrCtx, _p: ()) -> u64 {
    9999
}
// Default arm: receives `&mut C` + the whole enum, returns a fallback `u64`.
fn ctx_sig_default(_c: &mut VrCtx, _s: Sig) -> u64 {
    42
}
// Continuation step that consumes the bubbled-up value via `&mut C`.
fn ctx_consume(c: &mut VrCtx, v: u64) {
    c.sink.push(v);
}

#[test]
fn ctx_variant_value_bubbles_up_to_then() {
    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    // Exhaustive table (all 3 variants armed), arms return `u64`, no `.default`.
    // The value flows straight into `.then(ctx_consume)`, threading `&mut C`.
    let mut pipeline = CtxPipelineBuilder::<VrCtx, Sig>::new()
        .dispatch_variant(reg, |d| {
            d.arm(sig_variants::A, ctx_a_arm)
                .arm(sig_variants::B, ctx_b_arm)
                .arm(sig_variants::C, ctx_c_arm)
        })
        .then(ctx_consume, reg)
        .build();

    let mut ctx = VrCtx::default();
    pipeline.run(&mut ctx, &mut world, Sig::A(5)); // 1005
    pipeline.run(&mut ctx, &mut world, Sig::B(7)); // 2007
    pipeline.run(&mut ctx, &mut world, Sig::C); // 9999

    assert_eq!(ctx.sink, vec![1005, 2007, 9999]);
}

#[test]
fn ctx_variant_value_return_with_default() {
    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    // Non-exhaustive: only `A` armed, `.default` supplies the fallback value for
    // every unset variant. Both arm and default return `Out = u64`.
    let mut pipeline = CtxPipelineBuilder::<VrCtx, Sig>::new()
        .dispatch_variant(reg, |d| {
            d.arm(sig_variants::A, ctx_a_arm).default(ctx_sig_default)
        })
        .then(ctx_consume, reg)
        .build();

    let mut ctx = VrCtx::default();
    pipeline.run(&mut ctx, &mut world, Sig::A(5)); // matched → 1005
    pipeline.run(&mut ctx, &mut world, Sig::B(7)); // unset → default 42
    pipeline.run(&mut ctx, &mut world, Sig::C); // unset → default 42

    assert_eq!(ctx.sink, vec![1005, 42, 42]);
}

// -- dispatch_on value-return ------------------------------------------------

#[derive(Dispatchable, Clone, Copy)]
enum VrKey {
    X, // ordinal 0
    Y, // ordinal 1
}

#[derive(Clone, Copy)]
struct VrTick {
    key: VrKey,
    px: u64,
}

// `dispatch_on` arms receive `&mut C` + the WHOLE value and return a `u64`.
fn ctx_on_x(_c: &mut VrCtx, t: VrTick) -> u64 {
    t.px + 10
}
fn ctx_on_y(_c: &mut VrCtx, t: VrTick) -> u64 {
    t.px + 20
}

#[test]
fn ctx_on_value_bubbles_up_to_then() {
    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    // Exhaustive projected-key table (both keys armed), arms return `u64`, no
    // `.default`. The value bubbles up into `.then(ctx_consume)`.
    let mut pipeline = CtxPipelineBuilder::<VrCtx, VrTick>::new()
        .dispatch_on(
            |t: &VrTick| t.key,
            reg,
            |d| d.arm(VrKey::X, ctx_on_x).arm(VrKey::Y, ctx_on_y),
        )
        .then(ctx_consume, reg)
        .build();

    let mut ctx = VrCtx::default();
    pipeline.run(
        &mut ctx,
        &mut world,
        VrTick {
            key: VrKey::X,
            px: 1,
        },
    ); // 11
    pipeline.run(
        &mut ctx,
        &mut world,
        VrTick {
            key: VrKey::Y,
            px: 2,
        },
    ); // 22

    assert_eq!(ctx.sink, vec![11, 22]);
}

// -- dispatch_map value-return -----------------------------------------------

#[derive(Clone, Copy)]
struct VrMapMsg {
    kind: u16,
    payload: u64,
}

fn ctx_map_a(_c: &mut VrCtx, m: VrMapMsg) -> u64 {
    m.payload + 100
}
fn ctx_map_default(_c: &mut VrCtx, m: VrMapMsg) -> u64 {
    m.payload + 900
}

#[test]
fn ctx_map_value_return_with_default() {
    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    // Open key space always requires a `.default`; both arm and default return
    // `u64`, which bubbles up into `.then(ctx_consume)`.
    let mut pipeline = CtxPipelineBuilder::<VrCtx, VrMapMsg>::new()
        .dispatch_map(
            |m: &VrMapMsg| m.kind,
            reg,
            |d| d.arm(10u16, ctx_map_a).default(ctx_map_default),
        )
        .then(ctx_consume, reg)
        .build();

    let mut ctx = VrCtx::default();
    pipeline.run(
        &mut ctx,
        &mut world,
        VrMapMsg {
            kind: 10,
            payload: 1,
        },
    ); // matched → 101
    pipeline.run(
        &mut ctx,
        &mut world,
        VrMapMsg {
            kind: 99,
            payload: 2,
        },
    ); // unset → default 902

    assert_eq!(ctx.sink, vec![101, 902]);
}

// -- construction-time exhaustiveness panics ---------------------------------
//
// Terminal (`Out = ()`) arms keep `.build()` reachable, but the panic fires
// inside the `dispatch_*` call at construction — before `.build()` and before
// any dispatch ever runs.

fn ctx_unit_a(_c: &mut VrCtx, _p: u64) {}

#[test]
#[should_panic(expected = "no `.default`")]
fn ctx_variant_non_exhaustive_no_default_panics_at_construction() {
    let world = WorldBuilder::new().build();
    let reg = world.registry();

    // Only `A` of {A, B, C} armed, no `.default`/`.default_noop()` → panic here.
    let _p = CtxPipelineBuilder::<VrCtx, Sig>::new()
        .dispatch_variant(reg, |d| d.arm(sig_variants::A, ctx_unit_a))
        .build();
}

fn ctx_unit_x(_c: &mut VrCtx, _t: VrTick) {}

#[test]
#[should_panic(expected = "no `.default`")]
fn ctx_on_non_exhaustive_no_default_panics_at_construction() {
    let world = WorldBuilder::new().build();
    let reg = world.registry();

    // Only `X` of {X, Y} armed, no default → panic at construction.
    let _p = CtxPipelineBuilder::<VrCtx, VrTick>::new()
        .dispatch_on(|t: &VrTick| t.key, reg, |d| d.arm(VrKey::X, ctx_unit_x))
        .build();
}

fn ctx_unit_map(_c: &mut VrCtx, _m: VrMapMsg) {}

#[test]
#[should_panic(expected = "dispatch_map requires a")]
fn ctx_map_no_default_panics_at_construction() {
    let world = WorldBuilder::new().build();
    let reg = world.registry();

    // Open key space with no default → panic at construction, even with an arm.
    let _p = CtxPipelineBuilder::<VrCtx, VrMapMsg>::new()
        .dispatch_map(|m: &VrMapMsg| m.kind, reg, |d| d.arm(10u16, ctx_unit_map))
        .build();
}
