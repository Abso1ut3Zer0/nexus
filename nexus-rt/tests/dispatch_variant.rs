//! Integration tests for the `.dispatch_variant()` pipeline combinator
//! (issue #723, Phase 1b).
//!
//! Exercises terminal keyed dispatch on the input enum's own discriminant:
//! each arm receives its variant's *payload* (single-field, multi-field tuple,
//! or unit), unlisted variants run a no-op unless a `.default` is set, and
//! arity-0 closures work as arms.
//!
//! Runs in the default (debug) profile so the `debug_assert!` inside the
//! generated `unwrap` is active — every arm here is indexed by the value's own
//! ordinal, so the happy path must never trip it.

use std::sync::Arc;
use std::sync::atomic::{AtomicU32, Ordering};

use nexus_rt::{Dispatchable, Handler, PipelineBuilder, ResMut, Resource, WorldBuilder};

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

// Records which arm fired and the payload it unwrapped.
#[derive(Resource, Default)]
struct Log {
    route_away: Option<u32>,
    reprice: Option<(u32, i64)>,
    halt_count: u32,
    default_hits: u32,
}

// Named-fn arms: params first, variant payload last.
fn on_route_away(mut log: ResMut<Log>, payload: u32) {
    log.route_away = Some(payload);
}

fn on_reprice(mut log: ResMut<Log>, payload: (u32, i64)) {
    log.reprice = Some(payload);
}

fn on_halt(mut log: ResMut<Log>, _payload: ()) {
    log.halt_count += 1;
}

// Default arm receives the whole enum, not a payload.
fn on_default(mut log: ResMut<Log>, _cmd: Cmd) {
    log.default_hits += 1;
}

#[test]
fn routes_to_matching_arm_and_unwraps_payload() {
    let mut wb = WorldBuilder::new();
    wb.register(Log::default());
    let mut world = wb.build();
    let reg = world.registry();

    let mut pipeline = PipelineBuilder::<Cmd>::new()
        .dispatch_variant(reg, |d| {
            d.arm(cmd_variants::RouteAway, on_route_away)
                .arm(cmd_variants::Reprice, on_reprice)
                .arm(cmd_variants::Halt, on_halt)
            // `Cancel` intentionally unset — must fall through to the no-op.
        })
        .build();

    pipeline.run(&mut world, Cmd::RouteAway(42));
    pipeline.run(&mut world, Cmd::Reprice(7, -3));
    pipeline.run(&mut world, Cmd::Halt);
    pipeline.run(&mut world, Cmd::Cancel(999)); // unset → no-op

    let log = world.resource::<Log>();
    // Right arm fired, payloads unwrapped correctly (single field + tuple).
    assert_eq!(log.route_away, Some(42));
    assert_eq!(log.reprice, Some((7, -3)));
    assert_eq!(log.halt_count, 1);
    // Unset variant hit the no-op fallback — no default installed, nothing ran.
    assert_eq!(log.default_hits, 0);
}

#[test]
fn unset_variants_route_to_default_when_set() {
    let mut wb = WorldBuilder::new();
    wb.register(Log::default());
    let mut world = wb.build();
    let reg = world.registry();

    let mut pipeline = PipelineBuilder::<Cmd>::new()
        .dispatch_variant(reg, |d| {
            d.arm(cmd_variants::RouteAway, on_route_away)
                .default(on_default)
        })
        .build();

    pipeline.run(&mut world, Cmd::RouteAway(5)); // matched arm
    pipeline.run(&mut world, Cmd::Reprice(2, 3)); // unset → default
    pipeline.run(&mut world, Cmd::Halt); // unset → default
    pipeline.run(&mut world, Cmd::Cancel(1)); // unset → default

    let log = world.resource::<Log>();
    assert_eq!(log.route_away, Some(5));
    // The three unset variants all routed to the default arm.
    assert_eq!(log.default_hits, 3);
    // The default never touches these.
    assert_eq!(log.reprice, None);
    assert_eq!(log.halt_count, 0);
}

#[test]
fn closure_arm_receives_payload() {
    // Arity-0 closure arm (no resource params). Captures a Send + 'static sink
    // so the boxed step satisfies the `S::Step: Send + 'static` bound.
    let captured = Arc::new(AtomicU32::new(0));
    let sink = Arc::clone(&captured);

    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    let mut pipeline = PipelineBuilder::<Cmd>::new()
        .dispatch_variant(reg, move |d| {
            d.arm(cmd_variants::RouteAway, move |p: u32| {
                sink.store(p, Ordering::Relaxed);
            })
        })
        .build();

    pipeline.run(&mut world, Cmd::RouteAway(123));
    pipeline.run(&mut world, Cmd::Halt); // unset → no-op, closure untouched

    assert_eq!(captured.load(Ordering::Relaxed), 123);
}
