//! Integration tests for the `.dispatch_map()` pipeline combinator (issue #723,
//! Phase 2c) on both [`Pipeline`](nexus_rt::Pipeline) and
//! [`CtxPipeline`](nexus_rt::CtxPipeline).
//!
//! `.dispatch_map()` is the escape hatch from `.dispatch_on()`'s ordinal `Vec`
//! table for keys that aren't [`Dispatchable`](nexus_rt::Dispatchable) enums:
//! arbitrary/non-enum keys (a `u16`, a `String`), or a discriminant produced by
//! a resource lookup upstream. It swaps the ordinal table for an `FxHashMap`
//! keyed on `Hash + Eq`. Like `.dispatch_on()`, every arm receives the **whole**
//! value; unlisted keys run a no-op unless a `.default` is set.

use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use nexus_rt::{CtxPipelineBuilder, Handler, PipelineBuilder, Res, ResMut, Resource, WorldBuilder};

// The whole value each arm receives. `Copy` (POD): arms take it by value, as the
// dispatch API hands the whole value to the chosen arm. `kind` is an arbitrary
// non-enum `Hash + Eq` key read by `key_fn`.
#[derive(Clone, Copy)]
struct Msg {
    kind: u16,
    payload: u64,
}

// Records which arm fired and the whole-value `payload` it saw.
#[derive(Resource, Default)]
struct Log {
    a: Option<u64>,
    b: Option<u64>,
    fallback: Option<u64>,
}

// Named-fn arms: params first, whole value last.
fn on_a(mut log: ResMut<Log>, m: Msg) {
    log.a = Some(m.payload);
}

fn on_b(mut log: ResMut<Log>, m: Msg) {
    log.b = Some(m.payload);
}

fn on_default(mut log: ResMut<Log>, m: Msg) {
    log.fallback = Some(m.payload);
}

#[test]
fn routes_on_u16_key_and_passes_whole_value() {
    let mut wb = WorldBuilder::new();
    wb.register(Log::default());
    let mut world = wb.build();
    let reg = world.registry();

    let mut pipeline = PipelineBuilder::<Msg>::new()
        .dispatch_map(
            |m: &Msg| m.kind,
            reg,
            // key 30 intentionally unset — the open key space always requires a
            // default, so `.default_noop()` no-ops the unset keys.
            |d| d.arm(10u16, on_a).arm(20u16, on_b).default_noop(),
        )
        .build();

    pipeline.run(
        &mut world,
        Msg {
            kind: 10,
            payload: 100,
        },
    );
    pipeline.run(
        &mut world,
        Msg {
            kind: 20,
            payload: 200,
        },
    );
    pipeline.run(
        &mut world,
        Msg {
            kind: 30,
            payload: 300,
        },
    ); // unset → no-op

    let log = world.resource::<Log>();
    // Right arm fired, and each arm saw the whole `Msg` (its `payload`).
    assert_eq!(log.a, Some(100));
    assert_eq!(log.b, Some(200));
    // Unset key hit the no-op fallback — no default installed, nothing ran.
    assert_eq!(log.fallback, None);
}

#[test]
fn unset_key_routes_to_default_when_set() {
    let mut wb = WorldBuilder::new();
    wb.register(Log::default());
    let mut world = wb.build();
    let reg = world.registry();

    let mut pipeline = PipelineBuilder::<Msg>::new()
        .dispatch_map(
            |m: &Msg| m.kind,
            reg,
            |d| d.arm(10u16, on_a).default(on_default),
        )
        .build();

    pipeline.run(
        &mut world,
        Msg {
            kind: 10,
            payload: 11,
        },
    ); // matched arm
    pipeline.run(
        &mut world,
        Msg {
            kind: 20,
            payload: 22,
        },
    ); // unset → default
    pipeline.run(
        &mut world,
        Msg {
            kind: 30,
            payload: 33,
        },
    ); // unset → default

    let log = world.resource::<Log>();
    assert_eq!(log.a, Some(11));
    // Last unset key to hit the default wins the recorded payload.
    assert_eq!(log.fallback, Some(33));
    // The default arm is the only thing that ran for 20/30; the B arm never fired.
    assert_eq!(log.b, None);
}

// A `String` key exercises a non-`Copy`, heap-allocated `Hash + Eq` key — the
// case the ordinal `Vec` of `.dispatch_on()` cannot express at all.
#[derive(Clone)]
struct Named {
    channel: String,
    payload: u64,
}

// Records the owned `String` the arm was handed, proving the whole non-`Copy`
// value moves into the arm (not a borrow).
#[derive(Resource, Default)]
struct StringLog {
    seen_channel: Option<String>,
    payload: Option<u64>,
}

fn on_named_a(mut log: ResMut<StringLog>, m: Named) {
    // Move the owned `String` out of the value — the arm genuinely consumes it.
    log.seen_channel = Some(m.channel);
    log.payload = Some(m.payload);
}

#[test]
fn routes_on_string_key() {
    let mut wb = WorldBuilder::new();
    wb.register(StringLog::default());
    let mut world = wb.build();
    let reg = world.registry();

    let mut pipeline = PipelineBuilder::<Named>::new()
        .dispatch_map(
            |m: &Named| m.channel.clone(),
            reg,
            // Open key space requires a default; `.default_noop()` no-ops unset keys.
            |d| d.arm("orders".to_string(), on_named_a).default_noop(),
        )
        .build();

    pipeline.run(
        &mut world,
        Named {
            channel: "orders".to_string(),
            payload: 42,
        },
    );
    pipeline.run(
        &mut world,
        Named {
            channel: "quotes".to_string(),
            payload: 99,
        },
    ); // unset key → no-op

    let log = world.resource::<StringLog>();
    assert_eq!(log.seen_channel.as_deref(), Some("orders"));
    assert_eq!(log.payload, Some(42));
}

#[test]
fn closure_arm_receives_whole_value() {
    // Arity-0 closure arm (no resource params). Captures a Send + 'static sink so
    // the boxed step satisfies `S::Step: Send + 'static`.
    let captured = Arc::new(AtomicU64::new(0));
    let sink = Arc::clone(&captured);

    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    let mut pipeline = PipelineBuilder::<Msg>::new()
        .dispatch_map(
            |m: &Msg| m.kind,
            reg,
            move |d| {
                d.arm(10u16, move |m: Msg| {
                    sink.store(m.payload, Ordering::Relaxed);
                })
                // Open key space — no-op fallback for unset keys.
                .default_noop()
            },
        )
        .build();

    pipeline.run(
        &mut world,
        Msg {
            kind: 10,
            payload: 777,
        },
    );
    pipeline.run(
        &mut world,
        Msg {
            kind: 20,
            payload: 999,
        },
    ); // unset → no-op

    assert_eq!(captured.load(Ordering::Relaxed), 777);
}

// -- resource-derived key ----------------------------------------------------

// A routing table looked up at runtime: maps a raw symbol id to a venue key. The
// key that drives dispatch is not carried by the input — it is computed by a
// `.then` stage that reads this resource, then stamped onto the value. This is
// the "discriminant from a resource lookup" case `.dispatch_map()` exists for.
#[derive(Resource)]
struct VenueTable {
    // symbol id -> venue key
    binance_symbol: u32,
}

#[derive(Clone, Copy)]
struct Routed {
    symbol: u32,
    venue: u16, // filled in by the resource-reading stage below
    px: u64,
}

fn resolve_venue(table: Res<VenueTable>, mut r: Routed) -> Routed {
    // Resource lookup produces the routing key, stamped onto the value.
    r.venue = u16::from(r.symbol == table.binance_symbol);
    r
}

fn on_binance(mut log: ResMut<Log>, r: Routed) {
    log.a = Some(r.px);
}

fn on_other(mut log: ResMut<Log>, r: Routed) {
    log.b = Some(r.px);
}

#[test]
fn resource_derived_key_via_then() {
    let mut wb = WorldBuilder::new();
    wb.register(Log::default());
    wb.register(VenueTable {
        binance_symbol: 1234,
    });
    let mut world = wb.build();
    let reg = world.registry();

    // Continuation form: `.then` reads a resource to compute the routing key,
    // then `.dispatch_map` keys on the stamped field.
    let mut pipeline = PipelineBuilder::<Routed>::new()
        .then(resolve_venue, reg)
        .dispatch_map(
            |r: &Routed| r.venue,
            reg,
            // Open key space requires a default even though both venues are armed.
            |d| d.arm(1u16, on_binance).arm(0u16, on_other).default_noop(),
        )
        .build();

    pipeline.run(
        &mut world,
        Routed {
            symbol: 1234,
            venue: 0,
            px: 500,
        },
    ); // resolves to venue 1
    pipeline.run(
        &mut world,
        Routed {
            symbol: 9999,
            venue: 0,
            px: 600,
        },
    ); // resolves to venue 0

    let log = world.resource::<Log>();
    assert_eq!(log.a, Some(500)); // binance arm
    assert_eq!(log.b, Some(600)); // other arm
}

// -- CtxPipeline mirror ------------------------------------------------------

// Per-instance context the arms mutate. Proving `&mut C` is threaded is the
// whole point: every arm records into this, and the test asserts the writes.
#[derive(Default)]
struct OnCtx {
    a: Option<u64>,
    b: Option<u64>,
    fallback: Option<u64>,
}

// Named-fn arms: ctx first, whole value last.
fn ctx_on_a(ctx: &mut OnCtx, m: Msg) {
    ctx.a = Some(m.payload);
}

fn ctx_on_b(ctx: &mut OnCtx, m: Msg) {
    ctx.b = Some(m.payload);
}

fn ctx_on_default(ctx: &mut OnCtx, m: Msg) {
    ctx.fallback = Some(m.payload);
}

#[test]
fn ctx_dispatch_map_threads_ctx_and_whole_value() {
    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    let mut pipeline = CtxPipelineBuilder::<OnCtx, Msg>::new()
        .dispatch_map(
            |m: &Msg| m.kind,
            reg,
            |d| {
                d.arm(10u16, ctx_on_a)
                    .arm(20u16, ctx_on_b)
                    .default(ctx_on_default)
            },
        )
        .build();

    let mut ctx = OnCtx::default();
    pipeline.run(
        &mut ctx,
        &mut world,
        Msg {
            kind: 10,
            payload: 100,
        },
    );
    pipeline.run(
        &mut ctx,
        &mut world,
        Msg {
            kind: 20,
            payload: 200,
        },
    );
    pipeline.run(
        &mut ctx,
        &mut world,
        Msg {
            kind: 30,
            payload: 300,
        },
    ); // unset → default

    // Right arm fired, each arm saw the whole `Msg`, and each write landed in the
    // threaded `&mut OnCtx`.
    assert_eq!(ctx.a, Some(100));
    assert_eq!(ctx.b, Some(200));
    // Unset key routed to the default (via `&mut OnCtx`).
    assert_eq!(ctx.fallback, Some(300));
}

#[test]
fn ctx_dispatch_map_closure_arm_mutates_ctx() {
    // Arity-0 closure arm: `FnMut(&mut C, In)`, receiving the whole value.
    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    let mut pipeline = CtxPipelineBuilder::<OnCtx, Msg>::new()
        .dispatch_map(
            |m: &Msg| m.kind,
            reg,
            // Open key space requires a default; `.default_noop()` no-ops unset keys.
            |d| {
                d.arm(10u16, |ctx: &mut OnCtx, m: Msg| {
                    ctx.a = Some(m.payload);
                })
                .default_noop()
            },
        )
        .build();

    let mut ctx = OnCtx::default();
    pipeline.run(
        &mut ctx,
        &mut world,
        Msg {
            kind: 10,
            payload: 555,
        },
    );
    pipeline.run(
        &mut ctx,
        &mut world,
        Msg {
            kind: 20,
            payload: 666,
        },
    ); // unset → no-op

    assert_eq!(ctx.a, Some(555));
    assert_eq!(ctx.b, None);
    assert_eq!(ctx.fallback, None);
}
