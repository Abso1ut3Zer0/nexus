#![allow(
    unused_must_use,
    dead_code,
    clippy::float_cmp,
    clippy::used_underscore_binding,
    clippy::items_after_statements,
    // Handler params are by-value by contract (the `Param` trait fetches
    // owned items); clippy's by-ref suggestion doesn't apply here.
    clippy::needless_pass_by_value
)]
//! Integration tests for #[derive(Param)].

use nexus_rt::{Handler, IntoHandler, Local, Param, Res, ResMut, Resource, WorldBuilder, no_event};

// Building a handler runs the always-on static conflict check
// (`Registry::check_access`) at construction time — before any dispatch — so
// these tests never call `run()`. Any panic therefore comes from the static
// check, not the debug-only runtime borrow tracker. See issue #719.

// =========================================================================
// Test types
// =========================================================================

#[derive(Resource, Default)]
struct OrderBook {
    best_bid: f64,
    best_ask: f64,
}

#[derive(Resource, Default)]
struct RiskState {
    exposure: f64,
}

#[derive(Resource, Default)]
struct Config {
    max_exposure: f64,
}

// =========================================================================
// Basic: Res + ResMut
// =========================================================================

#[derive(Param)]
struct BasicParams<'w> {
    book: Res<'w, OrderBook>,
    risk: ResMut<'w, RiskState>,
}

fn handler_basic(mut params: BasicParams<'_>, _event: u32) {
    let spread = params.book.best_ask - params.book.best_bid;
    params.risk.exposure += spread;
}

#[test]
fn basic_res_resmut() {
    let mut wb = WorldBuilder::new();
    wb.register(OrderBook {
        best_bid: 100.0,
        best_ask: 101.0,
    });
    wb.register(RiskState::default());
    let mut world = wb.build();

    let mut h = handler_basic.into_handler(world.registry());
    h.run(&mut world, 0u32);

    assert_eq!(world.resource::<RiskState>().exposure, 1.0);
}

// =========================================================================
// With Local
// =========================================================================

#[derive(Param)]
struct ParamsWithLocal<'w> {
    config: Res<'w, Config>,
    call_count: Local<'w, u64>,
}

fn handler_with_local(mut params: ParamsWithLocal<'_>) {
    *params.call_count += 1;
    let _ = params.config.max_exposure;
}

#[test]
fn with_local() {
    let mut wb = WorldBuilder::new();
    wb.register(Config {
        max_exposure: 1000.0,
    });
    let mut world = wb.build();

    let mut h = no_event(handler_with_local).into_handler(world.registry());
    h.run(&mut world, ());
    h.run(&mut world, ());
    h.run(&mut world, ());
    // Local state persists across calls — 3 invocations
    // (We can't directly inspect Local from outside, but it compiles and runs)
}

// =========================================================================
// With Option<Res<T>>
// =========================================================================

#[derive(Param)]
struct OptionalParams<'w> {
    config: Option<Res<'w, Config>>,
    risk: ResMut<'w, RiskState>,
}

fn handler_optional(mut params: OptionalParams<'_>) {
    if let Some(config) = params.config {
        params.risk.exposure = config.max_exposure;
    }
}

#[test]
fn with_optional_res() {
    // Config NOT registered — should still work
    let mut wb = WorldBuilder::new();
    wb.register(RiskState::default());
    let mut world = wb.build();

    let mut h = no_event(handler_optional).into_handler(world.registry());
    h.run(&mut world, ());
    assert_eq!(world.resource::<RiskState>().exposure, 0.0); // no config

    // Now with Config registered
    let mut wb2 = WorldBuilder::new();
    wb2.register(RiskState::default());
    wb2.register(Config {
        max_exposure: 500.0,
    });
    let mut world2 = wb2.build();

    let mut h2 = no_event(handler_optional).into_handler(world2.registry());
    h2.run(&mut world2, ());
    assert_eq!(world2.resource::<RiskState>().exposure, 500.0);
}

// =========================================================================
// With #[param(ignore)] field
// =========================================================================

#[derive(Param)]
struct ParamsWithIgnored<'w> {
    risk: ResMut<'w, RiskState>,
    #[param(ignore)]
    _marker: std::marker::PhantomData<u32>,
}

fn handler_ignored(mut params: ParamsWithIgnored<'_>) {
    params.risk.exposure += 1.0;
}

#[test]
fn with_ignored_field() {
    let mut wb = WorldBuilder::new();
    wb.register(RiskState::default());
    let mut world = wb.build();

    let mut h = no_event(handler_ignored).into_handler(world.registry());
    h.run(&mut world, ());
    assert_eq!(world.resource::<RiskState>().exposure, 1.0);
}

// =========================================================================
// Nested Param structs
// =========================================================================

#[derive(Param)]
struct InnerParams<'w> {
    risk: ResMut<'w, RiskState>,
}

#[derive(Param)]
struct OuterParams<'w> {
    inner: InnerParams<'w>,
    config: Res<'w, Config>,
}

fn handler_nested(mut params: OuterParams<'_>) {
    params.inner.risk.exposure = params.config.max_exposure;
}

#[test]
fn nested_params() {
    let mut wb = WorldBuilder::new();
    wb.register(RiskState::default());
    wb.register(Config {
        max_exposure: 999.0,
    });
    let mut world = wb.build();

    let mut h = no_event(handler_nested).into_handler(world.registry());
    h.run(&mut world, ());
    assert_eq!(world.resource::<RiskState>().exposure, 999.0);
}

// =========================================================================
// Param + additional resource params (higher arity)
// =========================================================================

#[derive(Param)]
struct TradingParams<'w> {
    book: Res<'w, OrderBook>,
    risk: ResMut<'w, RiskState>,
}

fn handler_mixed(mut params: TradingParams<'_>, config: Res<Config>) {
    params.risk.exposure = params.book.best_bid * config.max_exposure;
}

#[test]
fn param_plus_additional_resources() {
    let mut wb = WorldBuilder::new();
    wb.register(OrderBook {
        best_bid: 50.0,
        best_ask: 51.0,
    });
    wb.register(RiskState::default());
    wb.register(Config { max_exposure: 2.0 });
    let mut world = wb.build();

    let mut h = no_event(handler_mixed).into_handler(world.registry());
    h.run(&mut world, ());
    assert_eq!(world.resource::<RiskState>().exposure, 100.0);
}

// =========================================================================
// Conflict detection reaches inside bundles and nested tuples (#719)
//
// Before the fix, `check_access` only saw top-level params, so a conflicting
// borrow hidden in a `#[derive(Param)]` bundle (or a nested tuple) silently
// bypassed the always-on static aliasing guard — the very escape hatch used
// to exceed the 8-param arity ceiling.
// =========================================================================

// Bundle that mutably borrows RiskState.
#[derive(Param)]
struct RiskWriter<'w> {
    risk: ResMut<'w, RiskState>,
}

// Bundle that shared-borrows the same resource.
#[derive(Param)]
struct RiskReader<'w> {
    risk: Res<'w, RiskState>,
}

// Bundle touching a *different* resource — never conflicts with the above.
#[derive(Param)]
struct ConfigReader<'w> {
    config: Res<'w, Config>,
}

fn world_with_risk() -> nexus_rt::World {
    let mut wb = WorldBuilder::new();
    wb.register(RiskState::default());
    wb.build()
}

// (1) Conflict between a bundle's `ResMut<X>` and a top-level `Res<X>`.
#[test]
#[should_panic(expected = "conflicting access")]
fn bundle_vs_top_level_conflict() {
    let world = world_with_risk();

    fn bad(_bundle: RiskWriter<'_>, _also: Res<RiskState>) {}

    // Construction alone must trip the static check — no dispatch.
    let _h = no_event(bad).into_handler(world.registry());
}

// (2) Two bundles that both touch the same resource.
#[test]
#[should_panic(expected = "conflicting access")]
fn two_bundles_conflict() {
    let world = world_with_risk();

    fn bad(_writer: RiskWriter<'_>, _reader: RiskReader<'_>) {}

    let _h = no_event(bad).into_handler(world.registry());
}

// (3) Bundle-in-bundle: the conflict is one nesting level down, proving the
// derived `collect_access` forwards recursively.
#[derive(Param)]
struct NestedConflict<'w> {
    inner: RiskWriter<'w>,      // ResMut<RiskState>, one level down
    reader: Res<'w, RiskState>, // same resource at this level
}

#[test]
#[should_panic(expected = "conflicting access")]
fn bundle_in_bundle_conflict() {
    let world = world_with_risk();

    fn bad(_p: NestedConflict<'_>) {}

    let _h = no_event(bad).into_handler(world.registry());
}

// (4) Tuple nested inside a bundle: proves the tuple `Param` impl's
// `collect_access` override participates in the recursion too.
#[derive(Param)]
struct TupleBundle<'w> {
    pair: (Res<'w, RiskState>, ResMut<'w, RiskState>),
}

#[test]
#[should_panic(expected = "conflicting access")]
fn tuple_in_bundle_conflict() {
    let world = world_with_risk();

    fn bad(_p: TupleBundle<'_>) {}

    let _h = no_event(bad).into_handler(world.registry());
}

// (5) A bare nested tuple as a single handler param — the tuple impl override
// alone must surface the conflict.
#[test]
#[should_panic(expected = "conflicting access")]
fn nested_tuple_param_conflict() {
    let world = world_with_risk();

    fn bad(_t: (Res<RiskState>, ResMut<RiskState>)) {}

    let _h = no_event(bad).into_handler(world.registry());
}

// (6) No false positives: disjoint bundles build and dispatch fine.
#[test]
fn non_conflicting_bundles_build() {
    let mut wb = WorldBuilder::new();
    wb.register(RiskState::default());
    wb.register(Config { max_exposure: 7.0 });
    let mut world = wb.build();

    // One bundle writes RiskState, another reads Config — disjoint.
    fn ok(mut writer: RiskWriter<'_>, cfg: ConfigReader<'_>) {
        writer.risk.exposure += cfg.config.max_exposure;
    }

    let mut h = no_event(ok).into_handler(world.registry());
    h.run(&mut world, ());
    assert_eq!(world.resource::<RiskState>().exposure, 7.0);
}
