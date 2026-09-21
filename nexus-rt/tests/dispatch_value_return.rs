//! Value-returning Pipeline dispatch (issue #723, Phase 5a).
//!
//! The Pipeline dispatch combinators (`dispatch_variant`, `dispatch_on`,
//! `dispatch_map`) are `Out`-generic: an arm returns a value that bubbles up so
//! the pipeline continues with `.then(...)` — the real runtime `select!`
//! replacement. Exhaustiveness (or a `.default`/`.default_noop()`) is enforced
//! at construction, so a non-exhaustive table with no fallback panics when the
//! pipeline is wired, before any dispatch.

use nexus_rt::{Dispatchable, Handler, PipelineBuilder, ResMut, Resource, WorldBuilder};

// -- shared fixtures ---------------------------------------------------------

#[derive(Dispatchable, Clone, Copy)]
enum Sig {
    A(u64), // ordinal 0 — single-field payload
    B(u64), // ordinal 1 — single-field payload
    C,      // ordinal 2 — unit payload `()`
}

// Collects the values that bubbled out of the dispatch node into `.then`.
#[derive(Resource, Default)]
struct Sink(Vec<u64>);

// `dispatch_variant` arms: receive the unwrapped payload, RETURN a `u64`.
fn a_arm(p: u64) -> u64 {
    p + 1000
}
fn b_arm(p: u64) -> u64 {
    p + 2000
}
fn c_arm(_p: ()) -> u64 {
    9999
}

// Default arm: receives the whole enum, returns a fallback `u64`.
fn sig_default(_c: Sig) -> u64 {
    42
}

// Continuation step that consumes the bubbled-up value.
fn consume(mut sink: ResMut<Sink>, v: u64) {
    sink.0.push(v);
}

// -- dispatch_variant value-return -------------------------------------------

#[test]
fn variant_value_bubbles_up_to_then() {
    let mut wb = WorldBuilder::new();
    wb.register(Sink::default());
    let mut world = wb.build();
    let reg = world.registry();

    // Exhaustive table (all 3 variants armed), arms return `u64`, no `.default`.
    // The returned value flows straight into `.then(consume)`.
    let mut pipeline = PipelineBuilder::<Sig>::new()
        .dispatch_variant(reg, |d| {
            d.arm(sig_variants::A, a_arm)
                .arm(sig_variants::B, b_arm)
                .arm(sig_variants::C, c_arm)
        })
        .then(consume, reg)
        .build();

    pipeline.run(&mut world, Sig::A(5)); // 1005
    pipeline.run(&mut world, Sig::B(7)); // 2007
    pipeline.run(&mut world, Sig::C); // 9999

    // Every arm's return value bubbled up through the dispatch node into `.then`.
    assert_eq!(world.resource::<Sink>().0, vec![1005, 2007, 9999]);
}

#[test]
fn variant_value_return_with_default() {
    let mut wb = WorldBuilder::new();
    wb.register(Sink::default());
    let mut world = wb.build();
    let reg = world.registry();

    // Non-exhaustive: only `A` armed, `.default` supplies the fallback value for
    // every unset variant. Both arm and default return the same `Out = u64`.
    let mut pipeline = PipelineBuilder::<Sig>::new()
        .dispatch_variant(reg, |d| d.arm(sig_variants::A, a_arm).default(sig_default))
        .then(consume, reg)
        .build();

    pipeline.run(&mut world, Sig::A(5)); // matched → 1005
    pipeline.run(&mut world, Sig::B(7)); // unset → default 42
    pipeline.run(&mut world, Sig::C); // unset → default 42

    assert_eq!(world.resource::<Sink>().0, vec![1005, 42, 42]);
}

// -- dispatch_on value-return ------------------------------------------------

#[derive(Dispatchable, Clone, Copy)]
enum Key {
    X, // ordinal 0
    Y, // ordinal 1
}

#[derive(Clone, Copy)]
struct Tick {
    key: Key,
    px: u64,
}

// `dispatch_on` arms receive the WHOLE value and return a `u64`.
fn on_x(t: Tick) -> u64 {
    t.px + 10
}
fn on_y(t: Tick) -> u64 {
    t.px + 20
}

#[test]
fn on_value_bubbles_up_to_then() {
    let mut wb = WorldBuilder::new();
    wb.register(Sink::default());
    let mut world = wb.build();
    let reg = world.registry();

    // Exhaustive projected-key table (both keys armed), arms return `u64`, no
    // `.default`. The value bubbles up into `.then(consume)`.
    let mut pipeline = PipelineBuilder::<Tick>::new()
        .dispatch_on(
            |t: &Tick| t.key,
            reg,
            |d| d.arm(Key::X, on_x).arm(Key::Y, on_y),
        )
        .then(consume, reg)
        .build();

    pipeline.run(&mut world, Tick { key: Key::X, px: 1 }); // 11
    pipeline.run(&mut world, Tick { key: Key::Y, px: 2 }); // 22

    assert_eq!(world.resource::<Sink>().0, vec![11, 22]);
}

// -- dispatch_map value-return -----------------------------------------------

#[derive(Clone, Copy)]
struct MapMsg {
    kind: u16,
    payload: u64,
}

fn map_a(m: MapMsg) -> u64 {
    m.payload + 100
}
fn map_default(m: MapMsg) -> u64 {
    m.payload + 900
}

#[test]
fn map_value_return_with_default() {
    let mut wb = WorldBuilder::new();
    wb.register(Sink::default());
    let mut world = wb.build();
    let reg = world.registry();

    // Open key space always requires a `.default`; both arm and default return
    // `u64`, which bubbles up into `.then(consume)`.
    let mut pipeline = PipelineBuilder::<MapMsg>::new()
        .dispatch_map(
            |m: &MapMsg| m.kind,
            reg,
            |d| d.arm(10u16, map_a).default(map_default),
        )
        .then(consume, reg)
        .build();

    pipeline.run(
        &mut world,
        MapMsg {
            kind: 10,
            payload: 1,
        },
    ); // matched → 101
    pipeline.run(
        &mut world,
        MapMsg {
            kind: 99,
            payload: 2,
        },
    ); // unset → default 902

    assert_eq!(world.resource::<Sink>().0, vec![101, 902]);
}

// -- construction-time exhaustiveness panics ---------------------------------
//
// Terminal (`Out = ()`) arms keep `.build()` reachable, but the panic fires
// inside the `dispatch_*` call at construction — before `.build()` and before
// any dispatch ever runs.

fn unit_a(_p: u64) {}

#[test]
#[should_panic(expected = "no `.default`")]
fn variant_non_exhaustive_no_default_panics_at_construction() {
    let world = WorldBuilder::new().build();
    let reg = world.registry();

    // Only `A` of {A, B, C} armed, no `.default`/`.default_noop()` → panic here.
    let _p = PipelineBuilder::<Sig>::new()
        .dispatch_variant(reg, |d| d.arm(sig_variants::A, unit_a))
        .build();
}

fn unit_x(_t: Tick) {}

#[test]
#[should_panic(expected = "no `.default`")]
fn on_non_exhaustive_no_default_panics_at_construction() {
    let world = WorldBuilder::new().build();
    let reg = world.registry();

    // Only `X` of {X, Y} armed, no default → panic at construction.
    let _p = PipelineBuilder::<Tick>::new()
        .dispatch_on(|t: &Tick| t.key, reg, |d| d.arm(Key::X, unit_x))
        .build();
}

fn unit_map(_m: MapMsg) {}

#[test]
#[should_panic(expected = "dispatch_map requires a")]
fn map_no_default_panics_at_construction() {
    let world = WorldBuilder::new().build();
    let reg = world.registry();

    // Open key space with no default → panic at construction, even with an arm.
    let _p = PipelineBuilder::<MapMsg>::new()
        .dispatch_map(|m: &MapMsg| m.kind, reg, |d| d.arm(10u16, unit_map))
        .build();
}
