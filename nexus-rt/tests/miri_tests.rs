#![allow(
    unused_must_use,
    dead_code,
    clippy::float_cmp,
    clippy::used_underscore_binding,
    clippy::items_after_statements
)]
//! Miri tests for nexus-rt's unsafe paths.
//!
//! Two unsafe surfaces are covered:
//! - World/ResourceId: type-erased resource storage via NonNull<u8>, Box
//!   reconstitution on drop, and ResourceCell change detection.
//! - dispatch (issue #723): the `VariantOf::unwrap` unchecked unwrap reached
//!   through `.dispatch_variant`'s per-variant thunks (see the dispatch section
//!   at the bottom of this file).
//!
//! Run: `cargo +nightly miri test -p nexus-rt --test miri_tests`

use std::cell::Cell;

use nexus_rt::{
    CtxPipelineBuilder, Dispatchable, Handler, PipelineBuilder, ResMut, Resource, WorldBuilder,
};

// =============================================================================
// Helper types
// =============================================================================

thread_local! {
    static DROP_COUNT: Cell<usize> = const { Cell::new(0) };
}

#[derive(Resource)]
struct Counter(u64);

#[derive(Resource)]
struct Label(String);

#[derive(Resource)]
struct DropTracker(#[allow(dead_code)] u64);

impl Drop for DropTracker {
    fn drop(&mut self) {
        DROP_COUNT.with(|c| c.set(c.get() + 1));
    }
}

fn reset_drop_count() {
    DROP_COUNT.with(|c| c.set(0));
}

fn get_drop_count() -> usize {
    DROP_COUNT.with(Cell::get)
}

// =============================================================================
// Resource insert / get / get_mut cycle
// =============================================================================

#[test]
fn world_resource_insert_get_roundtrip() {
    let mut wb = WorldBuilder::new();
    wb.register(Counter(42));
    wb.register(Label("hello".into()));
    let world = wb.build();

    assert_eq!(world.resource::<Counter>().0, 42);
    assert_eq!(world.resource::<Label>().0, "hello");
}

#[test]
fn world_resource_mut() {
    let mut wb = WorldBuilder::new();
    wb.register(Counter(0));
    let mut world = wb.build();

    world.resource_mut::<Counter>().0 = 99;
    assert_eq!(world.resource::<Counter>().0, 99);
}

#[test]
fn world_multiple_resources_coexist() {
    let mut wb = WorldBuilder::new();
    wb.register(Counter(1));
    wb.register(Label("a".into()));
    let mut world = wb.build();

    // Mutate one, read both — verifies separate ResourceId pointers
    world.resource_mut::<Counter>().0 += 10;
    assert_eq!(world.resource::<Counter>().0, 11);
    assert_eq!(world.resource::<Label>().0, "a");
}

// =============================================================================
// Drop ordering when World is dropped
// =============================================================================

#[derive(Resource)]
struct DT1(#[allow(dead_code)] u64);
impl Drop for DT1 {
    fn drop(&mut self) {
        DROP_COUNT.with(|c| c.set(c.get() + 1));
    }
}
#[derive(Resource)]
struct DT2(#[allow(dead_code)] u64);
impl Drop for DT2 {
    fn drop(&mut self) {
        DROP_COUNT.with(|c| c.set(c.get() + 1));
    }
}
#[derive(Resource)]
struct DT3(#[allow(dead_code)] u64);
impl Drop for DT3 {
    fn drop(&mut self) {
        DROP_COUNT.with(|c| c.set(c.get() + 1));
    }
}

#[test]
fn world_drop_drops_resources() {
    reset_drop_count();

    {
        let mut wb = WorldBuilder::new();
        wb.register(DT1(1));
        wb.register(DT2(2));
        wb.register(DT3(3));
        let _world = wb.build();
        assert_eq!(get_drop_count(), 0);
    }
    // World dropped — all 3 drop-tracked resources should be dropped
    assert_eq!(get_drop_count(), 3);
}

#[test]
fn world_drop_drops_heap_resources() {
    // String has a heap allocation — verify no leak
    let mut wb = WorldBuilder::new();
    wb.register(Label("heap allocated string".into()));
    let world = wb.build();
    assert_eq!(world.resource::<Label>().0, "heap allocated string");
    drop(world);
    // Miri checks for leaks
}

// =============================================================================
// Resource replacement
// =============================================================================

/// Register a resource, build world, drop and rebuild — verifies
/// the full lifecycle through Box reconstitution.
#[test]
fn world_rebuild_after_drop() {
    let mut wb = WorldBuilder::new();
    wb.register(Counter(10));
    let world = wb.build();
    assert_eq!(world.resource::<Counter>().0, 10);
    drop(world);

    // Rebuild fresh — old allocation freed, new one created
    let mut wb2 = WorldBuilder::new();
    wb2.register(Counter(20));
    let world2 = wb2.build();
    assert_eq!(world2.resource::<Counter>().0, 20);
}

// =============================================================================
// Change detection (ResourceCell tick)
// =============================================================================

#[test]
fn world_change_detection() {
    let mut wb = WorldBuilder::new();
    wb.register(Counter(0));
    let mut world = wb.build();

    // Initial state — resource was just registered
    let changed_before = world.resource::<Counter>().0;
    assert_eq!(changed_before, 0);

    // Mutate via resource_mut — stamps the ResourceCell
    world.resource_mut::<Counter>().0 = 42;
    assert_eq!(world.resource::<Counter>().0, 42);
}

// =============================================================================
// Many resources — exercises the HashMap<TypeId, ResourceId> path
// =============================================================================

#[derive(Resource)]
struct R0(u64);
#[derive(Resource)]
struct R1(u64);
#[derive(Resource)]
struct R2(u64);
#[derive(Resource)]
struct R3(u64);
#[derive(Resource)]
struct R4(u64);
#[derive(Resource)]
struct R5(u64);
#[derive(Resource)]
struct R6(u64);
#[derive(Resource)]
struct R7(u64);

#[test]
fn world_many_resources() {
    let mut wb = WorldBuilder::new();
    wb.register(R0(0));
    wb.register(R1(1));
    wb.register(R2(2));
    wb.register(R3(3));
    wb.register(R4(4));
    wb.register(R5(5));
    wb.register(R6(6));
    wb.register(R7(7));
    let world = wb.build();

    assert_eq!(world.resource::<R0>().0, 0);
    assert_eq!(world.resource::<R7>().0, 7);
    assert_eq!(world.resource::<R3>().0, 3);
}

// =============================================================================
// Stress — alloc/read/mutate/drop cycle
// =============================================================================

#[test]
fn world_stress_register_mutate_drop() {
    reset_drop_count();

    for _ in 0..10 {
        let mut wb = WorldBuilder::new();
        wb.register(Counter(0));
        wb.register(Label("stress".into()));
        wb.register(DT1(99));
        let mut world = wb.build();

        for i in 0..5u64 {
            world.resource_mut::<Counter>().0 += i;
        }
        assert_eq!(world.resource::<Counter>().0, 10); // 0+1+2+3+4
    }

    assert_eq!(get_drop_count(), 10); // 10 DT1 instances
}

// =============================================================================
// dispatch — VariantOf::unwrap unchecked-unwrap path (issue #723)
// =============================================================================
//
// The only unsafe in the dispatch feature is `VariantOf::unwrap_unchecked` →
// `core::hint::unreachable_unchecked()` (guarded by a `debug_assert!`), reached
// through the shared `VariantArm` thunk (both plain and ctx) that `.dispatch_variant`
// installs. Miri runs with `debug_assertions` on, so the happy path keeps the
// guard active and never reaches `unreachable_unchecked`. What these tests
// prove is that the unwrap's match / move-out-of-enum and the subsequent typed
// dispatch are UB-free (no aliasing or provenance violation) for a mix of
// variant shapes — including a heap-carrying (`String`) payload, so the
// move-out is a genuine non-`Copy` ownership transfer miri can check for leaks
// and provenance.
//
// The invariant-violation path (which would reach `unreachable_unchecked`) is
// unreachable given the dispatch invariant: each arm is indexed by the value's
// own `ordinal()`, so the value always IS variant `V`. These tests use
// `#[derive(Dispatchable)]`, the safe path, which upholds that invariant by
// construction, so the violation path is not (and cannot soundly be) tested here.

#[derive(Dispatchable)]
enum Shape {
    Unit,              // ordinal 0 — unit payload `()`
    Single(u64),       // ordinal 1 — single-field payload
    Pair(u32, String), // ordinal 2 — multi-field tuple payload (heap-carrying)
}

// -- Pipeline (`.dispatch_variant`) -----------------------------------------

#[derive(Resource, Default)]
struct DispatchLog {
    unit_hits: u32,
    single: Option<u64>,
    pair: Option<(u32, String)>,
}

fn dv_on_unit(mut log: ResMut<DispatchLog>, _payload: ()) {
    log.unit_hits += 1;
}

fn dv_on_single(mut log: ResMut<DispatchLog>, payload: u64) {
    log.single = Some(payload);
}

fn dv_on_pair(mut log: ResMut<DispatchLog>, payload: (u32, String)) {
    log.pair = Some(payload);
}

/// Dispatch a value of EACH variant shape through a built pipeline and assert
/// the correct typed payload came out — the unchecked unwrap runs once per
/// variant with no UB.
#[test]
fn dispatch_variant_unwraps_each_variant_shape() {
    let mut wb = WorldBuilder::new();
    wb.register(DispatchLog::default());
    let mut world = wb.build();
    let reg = world.registry();

    let mut pipeline = PipelineBuilder::<Shape>::new()
        .dispatch_variant(reg, |d| {
            d.arm(shape_variants::Unit, dv_on_unit)
                .arm(shape_variants::Single, dv_on_single)
                .arm(shape_variants::Pair, dv_on_pair)
        })
        .build();

    pipeline.run(&mut world, Shape::Unit);
    pipeline.run(&mut world, Shape::Single(42));
    pipeline.run(&mut world, Shape::Pair(7, "heap".into()));

    let log = world.resource::<DispatchLog>();
    assert_eq!(log.unit_hits, 1);
    assert_eq!(log.single, Some(42));
    assert_eq!(log.pair, Some((7, "heap".to_string())));
}

// -- CtxPipeline (`.dispatch_variant`) --------------------------------------

#[derive(Default)]
struct DispatchCtx {
    unit_hits: u32,
    single: Option<u64>,
    pair: Option<(u32, String)>,
}

fn ctx_dv_on_unit(ctx: &mut DispatchCtx, _payload: ()) {
    ctx.unit_hits += 1;
}

fn ctx_dv_on_single(ctx: &mut DispatchCtx, payload: u64) {
    ctx.single = Some(payload);
}

fn ctx_dv_on_pair(ctx: &mut DispatchCtx, payload: (u32, String)) {
    ctx.pair = Some(payload);
}

/// Same coverage as above but for the context-aware `CtxPipeline` thunk (the
/// shared `VariantArm`'s `CtxStepCall` impl), threading `&mut C` through each arm.
#[test]
fn ctx_dispatch_variant_unwraps_each_variant_shape() {
    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    let mut pipeline = CtxPipelineBuilder::<DispatchCtx, Shape>::new()
        .dispatch_variant(reg, |d| {
            d.arm(shape_variants::Unit, ctx_dv_on_unit)
                .arm(shape_variants::Single, ctx_dv_on_single)
                .arm(shape_variants::Pair, ctx_dv_on_pair)
        })
        .build();

    let mut ctx = DispatchCtx::default();
    pipeline.run(&mut ctx, &mut world, Shape::Unit);
    pipeline.run(&mut ctx, &mut world, Shape::Single(42));
    pipeline.run(&mut ctx, &mut world, Shape::Pair(7, "heap".into()));

    assert_eq!(ctx.unit_hits, 1);
    assert_eq!(ctx.single, Some(42));
    assert_eq!(ctx.pair, Some((7, "heap".to_string())));
}
