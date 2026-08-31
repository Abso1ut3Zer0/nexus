//! Comprehensive compile-time and runtime integration tests for nexus-rt
//! pipeline and DAG APIs.
//!
//! If this file compiles, the public API surface works for real users.
//! Each test exercises a specific pattern and verifies runtime behavior.

//! These are compile-time + runtime integration tests — helper functions
//! intentionally use specific signatures to exercise the nexus-rt API
//! (pass-by-value Params, trivially-copyable refs, items-after-statements
//! for test locality, f64 assert_eq for exact bit patterns, etc.).
#![allow(
    clippy::unnecessary_wraps,
    clippy::needless_pass_by_value,
    clippy::trivially_copy_pass_by_ref,
    clippy::items_after_statements,
    clippy::float_cmp,
    clippy::many_single_char_names,
    clippy::option_if_let_else,
    clippy::redundant_closure,
    clippy::manual_assert
)]

use nexus_rt::dag::{DagArmSeed, DagBuilder};
use nexus_rt::shutdown::Shutdown;
use nexus_rt::{
    Handler, IntoHandler, IntoSystem, Local, PipelineBuilder, Registry, Res, ResMut, Seq, SeqMut,
    System, Virtual, World, WorldBuilder, resolve_arm, resolve_producer, resolve_ref_step,
    resolve_step,
};

// =========================================================================
// Newtype resource wrappers for primitive types
// =========================================================================

nexus_rt::new_resource!(
    #[derive(Debug, PartialEq)]
    ResU32(u32)
);
nexus_rt::new_resource!(
    #[derive(Debug, PartialEq)]
    ResU64(u64)
);
nexus_rt::new_resource!(
    #[derive(Debug, PartialEq)]
    ResI64(i64)
);
nexus_rt::new_resource!(
    #[derive(Debug, PartialEq)]
    ResF64(f64)
);
nexus_rt::new_resource!(
    #[derive(Debug, PartialEq)]
    ResBool(bool)
);
nexus_rt::new_resource!(
    #[derive(Debug, PartialEq)]
    ResString(String)
);

// =========================================================================
// Helper types and named functions used across tests
// =========================================================================

#[derive(Debug, Clone, PartialEq)]
struct Order {
    id: u64,
    price: f64,
    size: u32,
}

impl Order {
    fn new(id: u64, price: f64, size: u32) -> Self {
        Self { id, price, size }
    }
}

#[derive(Debug, Clone, PartialEq)]
struct ValidOrder {
    id: u64,
    price: f64,
}

#[derive(Debug, Clone, PartialEq)]
struct EnrichedOrder {
    id: u64,
    total: f64,
}

#[derive(Debug, Clone)]
struct MyError(String);

// -- Pipeline step functions (named fns, as required for Param resolution) --

fn identity_u32(x: u32) -> u32 {
    x
}

fn double_u32(x: u32) -> u64 {
    x as u64 * 2
}

fn add_ten(x: u32) -> u32 {
    x + 10
}

fn triple(x: u32) -> u32 {
    x * 3
}

fn store_u64(mut out: ResMut<ResU64>, val: u64) {
    *out = ResU64(val);
}

fn read_factor_and_multiply(factor: Res<ResU64>, x: u32) -> u64 {
    **factor * x as u64
}

fn write_and_transform(mut out: ResMut<ResU64>, x: u32) -> u32 {
    *out = ResU64(x as u64);
    x * 2
}

fn read_and_write(config: Res<ResU64>, mut out: ResMut<ResString>, x: u32) {
    *out = ResString(format!("{}:{}", **config, x));
}

fn opt_res_step(opt: Option<Res<ResU64>>, x: u32) -> u32 {
    match opt {
        Some(v) => x + **v as u32,
        None => x,
    }
}

fn opt_res_mut_step(opt: Option<ResMut<ResString>>, x: u32) -> u32 {
    if let Some(mut s) = opt {
        *s = ResString(x.to_string());
    }
    x
}

fn seq_step(seq: Seq, x: u32) -> u32 {
    let _ = seq.get();
    x
}

fn seq_mut_step(mut seq: SeqMut, x: u32) -> u32 {
    let _ = seq.advance();
    x
}

fn shutdown_step(shutdown: Shutdown, x: u32) -> u32 {
    let _ = shutdown.is_shutdown();
    x
}

fn validate_order(order: Order) -> Option<ValidOrder> {
    if order.price > 0.0 {
        Some(ValidOrder {
            id: order.id,
            price: order.price,
        })
    } else {
        None
    }
}

fn enrich_order(vo: ValidOrder) -> EnrichedOrder {
    EnrichedOrder {
        id: vo.id,
        total: vo.price * 2.0,
    }
}

fn store_enriched(mut out: ResMut<ResF64>, eo: EnrichedOrder) {
    *out = ResF64(eo.total);
}

fn guard_positive(x: &u32) -> bool {
    *x > 0
}

fn guard_positive_with_res(threshold: Res<ResU32>, x: &u32) -> bool {
    *x > **threshold
}

fn tap_log(_x: &u32) {}

fn tap_log_with_res(_counter: Res<ResU64>, _x: &u32) {}

fn filter_even(x: &u32) -> bool {
    (*x).is_multiple_of(2)
}

fn inspect_option(x: &u32) {
    let _ = *x;
}

fn produce_true() -> bool {
    true
}

fn produce_false() -> bool {
    false
}

fn fallible_parse(x: u32) -> Result<u64, MyError> {
    if x < 100 {
        Ok(x as u64)
    } else {
        Err(MyError("too large".into()))
    }
}

fn map_ok_double(x: u64) -> u64 {
    x * 2
}

fn and_then_validate(x: u64) -> Result<u64, MyError> {
    if x < 200 {
        Ok(x)
    } else {
        Err(MyError("too large after double".into()))
    }
}

fn catch_error(_err: MyError) {}

fn map_err_to_string(err: MyError) -> String {
    err.0
}

fn inspect_err_log(_err: &MyError) {}

fn inspect_ok_log(_val: &u64) {}

fn or_else_recover(_err: MyError) -> Result<u64, String> {
    Ok(0)
}

fn unwrap_or_else_result(err: MyError) -> u64 {
    let _ = err;
    42
}

fn splat2(a: u32, b: u32) -> u32 {
    a + b
}

fn splat3(a: u32, b: u32, c: u32) -> u32 {
    a + b + c
}

fn splat4(a: u32, b: u32, c: u32, d: u32) -> u32 {
    a + b + c + d
}

fn splat5(a: u32, b: u32, c: u32, d: u32, e: u32) -> u32 {
    a + b + c + d + e
}

fn make_pair(x: u32) -> (u32, u32) {
    (x, x + 1)
}

fn make_triple(x: u32) -> (u32, u32, u32) {
    (x, x + 1, x + 2)
}

fn make_quad(x: u32) -> (u32, u32, u32, u32) {
    (x, x + 1, x + 2, x + 3)
}

fn make_quint(x: u32) -> (u32, u32, u32, u32, u32) {
    (x, x + 1, x + 2, x + 3, x + 4)
}

fn store_u32(mut out: ResMut<ResU32>, val: u32) {
    *out = ResU32(val);
}

// -- DAG step functions (takes &T) --

fn dag_double(x: &u32) -> u64 {
    *x as u64 * 2
}

fn dag_negate(x: &u32) -> i64 {
    -(*x as i64)
}

fn dag_store_u64(mut out: ResMut<ResU64>, val: &u64) {
    *out = ResU64(*val);
}

fn dag_store_i64(mut out: ResMut<ResI64>, val: &i64) {
    *out = ResI64(*val);
}

fn dag_add_one(x: &u64) -> u64 {
    *x + 1
}

fn dag_merge_sum(a: &u64, b: &i64) -> f64 {
    *a as f64 + *b as f64
}

fn dag_merge3(a: &u64, b: &i64, c: &f64) -> f64 {
    *a as f64 + *b as f64 + *c
}

fn dag_merge4(a: &u64, b: &u64, c: &u64, d: &u64) -> u64 {
    *a + *b + *c + *d
}

fn dag_store_f64(mut out: ResMut<ResF64>, val: &f64) {
    *out = ResF64(*val);
}

fn dag_guard_positive(x: &u64) -> bool {
    *x > 0
}

fn dag_tap_noop(_x: &u64) {}

fn dag_id(x: u32) -> u32 {
    x
}

fn dag_store_u32(mut out: ResMut<ResU32>, val: &u32) {
    *out = ResU32(*val);
}

fn dag_splat2(a: &u32, b: &u32) -> u32 {
    *a + *b
}

// Helper to build a simple world with common resources
fn build_world() -> World {
    let mut wb = WorldBuilder::new();
    wb.register(ResU32(0));
    wb.register(ResU64(0));
    wb.register(ResI64(0));
    wb.register(ResF64(0.0));
    wb.register(ResString(String::new()));
    wb.register(ResBool(false));
    wb.build()
}

// =========================================================================
// 1. Pipeline basics
// =========================================================================

#[test]
fn pipeline_single_step() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new().then(store_u32, r).build();
    p.run(&mut world, 42);
    assert_eq!(**world.resource::<ResU32>(), 42);
}

#[test]
fn pipeline_linear_chain_three() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(add_ten, r)
        .then(triple, r)
        .then(store_u32, r)
        .build();
    p.run(&mut world, 1);
    assert_eq!(**world.resource::<ResU32>(), 33); // (1+10)*3
}

#[test]
fn pipeline_linear_chain_five() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(identity_u32, r)
        .then(add_ten, r)
        .then(triple, r)
        .then(add_ten, r)
        .then(store_u32, r)
        .build();
    p.run(&mut world, 0);
    // 0 -> 0 -> 10 -> 30 -> 40
    assert_eq!(**world.resource::<ResU32>(), 40);
}

#[test]
fn pipeline_build_batch() {
    let mut world = build_world();
    let r = world.registry();
    let mut batch = PipelineBuilder::<u32>::new()
        .then(|x: u32| -> u64 { x as u64 }, r)
        .then(store_u64, r)
        .build_batch(16);

    batch.input_mut().extend_from_slice(&[1, 2, 3]);
    batch.run(&mut world);
    // last item wins
    assert_eq!(**world.resource::<ResU64>(), 3);
    assert!(batch.input().is_empty());
}

#[test]
fn pipeline_run_direct() {
    let mut world = build_world();
    let r = world.registry();
    let mut builder = PipelineBuilder::<u32>::new().then(double_u32, r);

    let result = builder.run(&mut world, 5);
    assert_eq!(result, 10);
}

// =========================================================================
// 2. Pipeline with every Param type
// =========================================================================

#[test]
fn pipeline_with_res() {
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(10));
    let mut world = wb.build();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(read_factor_and_multiply, r)
        .then(store_u64, r)
        .build();
    p.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU64>(), 50);
}

#[test]
fn pipeline_with_res_mut() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(write_and_transform, r)
        .then(store_u32, r)
        .build();
    p.run(&mut world, 7);
    assert_eq!(**world.resource::<ResU64>(), 7);
    assert_eq!(**world.resource::<ResU32>(), 14);
}

#[test]
fn pipeline_with_multiple_res_and_res_mut() {
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(42));
    wb.register(ResString(String::new()));
    let mut world = wb.build();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(read_and_write, r)
        .build();
    p.run(&mut world, 5);
    assert_eq!(world.resource::<ResString>().as_str(), "42:5");
}

#[test]
fn pipeline_with_option_res() {
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(100));
    let mut world = wb.build();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new().then(opt_res_step, r);
    let result = p.run(&mut world, 5);
    assert_eq!(result, 105);
}

#[test]
fn pipeline_with_option_res_mut() {
    let mut wb = WorldBuilder::new();
    wb.register(ResString(String::new()));
    let mut world = wb.build();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new().then(opt_res_mut_step, r);
    let result = p.run(&mut world, 7);
    assert_eq!(result, 7);
    assert_eq!(world.resource::<ResString>().as_str(), "7");
}

#[test]
fn pipeline_with_seq() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new().then(seq_step, r);
    let result = p.run(&mut world, 5);
    assert_eq!(result, 5);
}

#[test]
fn pipeline_with_seq_mut() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new().then(seq_mut_step, r);
    let result = p.run(&mut world, 5);
    assert_eq!(result, 5);
}

#[test]
fn pipeline_with_shutdown() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new().then(shutdown_step, r);
    let result = p.run(&mut world, 5);
    assert_eq!(result, 5);
}

// =========================================================================
// 3. Pipeline Option combinators
// =========================================================================

#[test]
fn pipeline_option_map() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(|x: u32| -> Option<u32> { Some(x) }, r)
        .map(double_u32, r)
        .map(
            |x: u64| {
                let _ = x;
            },
            r,
        )
        .build();
    p.run(&mut world, 5);
}

#[test]
fn pipeline_guard_then_map() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(identity_u32, r)
        .guard(guard_positive, r)
        .map(store_u32, r)
        .build();
    p.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU32>(), 5);

    // zero gets guarded out
    p.run(&mut world, 0);
    assert_eq!(**world.resource::<ResU32>(), 5); // unchanged
}

#[test]
fn pipeline_filter() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(identity_u32, r)
        .guard(|_: &u32| true, r) // enter Option land
        .filter(filter_even, r)
        .map(store_u32, r)
        .build();
    p.run(&mut world, 4);
    assert_eq!(**world.resource::<ResU32>(), 4);

    p.run(&mut world, 5); // odd, filtered
    assert_eq!(**world.resource::<ResU32>(), 4); // unchanged
}

#[test]
fn pipeline_inspect_option() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(identity_u32, r)
        .guard(guard_positive, r)
        .inspect(inspect_option, r)
        .map(store_u32, r)
        .build();
    p.run(&mut world, 3);
    assert_eq!(**world.resource::<ResU32>(), 3);
}

#[test]
fn pipeline_and_then_option() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(|x: u32| -> Option<u32> { Some(x) }, r)
        .and_then(|x: u32| -> Option<u64> { Some(x as u64 * 3) }, r)
        .map(store_u64, r)
        .build();
    p.run(&mut world, 4);
    assert_eq!(**world.resource::<ResU64>(), 12);
}

#[test]
fn pipeline_on_none() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(identity_u32, r)
        .guard(guard_positive, r)
        .on_none(|| {}, r)
        .map(store_u32, r)
        .build();
    p.run(&mut world, 0); // guarded, on_none fires
    assert_eq!(**world.resource::<ResU32>(), 0); // unchanged, was default
}

#[test]
fn pipeline_ok_or() {
    let mut world = build_world();
    let r = world.registry();
    // ok_or produces Result<u32, &str>; catch takes the error by value
    let mut p = PipelineBuilder::<u32>::new()
        .then(identity_u32, r)
        .guard(guard_positive, r)
        .ok_or("was zero")
        .map(store_u32, r)
        .catch(|_err: &str| {}, r)
        .build();
    p.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU32>(), 5);
}

#[test]
fn pipeline_unwrap_or_option() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(identity_u32, r)
        .guard(guard_positive, r)
        .unwrap_or(99)
        .then(store_u32, r)
        .build();

    p.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU32>(), 5);

    p.run(&mut world, 0);
    assert_eq!(**world.resource::<ResU32>(), 99);
}

#[test]
fn pipeline_cloned_option() {
    let mut world = build_world();
    let r = world.registry();
    // Option<&T> -> Option<T> via .cloned() — T must be Sized + Clone
    static YES: u64 = 1;
    static NO: u64 = 0;
    let mut p = PipelineBuilder::<u32>::new()
        .then(|x: u32| -> Option<u32> { Some(x) }, r)
        .map(
            |x: u32| -> &'static u64 { if x > 0 { &YES } else { &NO } },
            r,
        )
        .cloned()
        .map(
            |val: u64| {
                let _ = val;
            },
            r,
        )
        .build();
    p.run(&mut world, 1);
}

// =========================================================================
// 4. Pipeline Result combinators
// =========================================================================

#[test]
fn pipeline_result_map() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(fallible_parse, r)
        .map(map_ok_double, r)
        .map(store_u64, r)
        .catch(catch_error, r)
        .build();
    p.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU64>(), 10);
}

#[test]
fn pipeline_result_and_then() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(fallible_parse, r)
        .and_then(and_then_validate, r)
        .map(store_u64, r)
        .catch(catch_error, r)
        .build();
    p.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU64>(), 5);
}

#[test]
fn pipeline_result_catch() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(fallible_parse, r)
        .catch(catch_error, r)
        .map(store_u64, r)
        .build();
    p.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU64>(), 5);

    // Error case: catch consumes the error, None produced
    p.run(&mut world, 200);
    assert_eq!(**world.resource::<ResU64>(), 5); // unchanged
}

#[test]
fn pipeline_result_map_err() {
    let mut world = build_world();
    let r = world.registry();
    // After map_err, error type is String. Pipeline catch takes E by value.
    let mut p = PipelineBuilder::<u32>::new()
        .then(fallible_parse, r)
        .map_err(map_err_to_string, r)
        .catch(|_err: String| {}, r)
        .map(store_u64, r)
        .build();
    p.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU64>(), 5);
}

#[test]
fn pipeline_result_inspect_err() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(fallible_parse, r)
        .inspect_err(inspect_err_log, r)
        .map(store_u64, r)
        .catch(catch_error, r)
        .build();
    p.run(&mut world, 200); // error path
}

#[test]
fn pipeline_result_ok() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(fallible_parse, r)
        .ok()
        .map(store_u64, r)
        .build();
    p.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU64>(), 5);
}

#[test]
fn pipeline_result_unwrap_or() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(fallible_parse, r)
        .unwrap_or(999)
        .then(store_u64, r)
        .build();
    p.run(&mut world, 200);
    assert_eq!(**world.resource::<ResU64>(), 999);
}

#[test]
fn pipeline_result_or_else() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(fallible_parse, r)
        .or_else(or_else_recover, r)
        .map(store_u64, r)
        .catch(|_err: String| {}, r)
        .build();
    p.run(&mut world, 200); // error -> recovered to Ok(0)
    assert_eq!(**world.resource::<ResU64>(), 0);
}

#[test]
fn pipeline_result_unwrap_or_else() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(fallible_parse, r)
        .unwrap_or_else(unwrap_or_else_result, r)
        .then(store_u64, r)
        .build();
    p.run(&mut world, 200);
    assert_eq!(**world.resource::<ResU64>(), 42);
}

#[test]
fn pipeline_result_inspect_ok() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(fallible_parse, r)
        .inspect(inspect_ok_log, r)
        .map(store_u64, r)
        .catch(catch_error, r)
        .build();
    p.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU64>(), 5);
}

// =========================================================================
// 5. Pipeline bool combinators
// =========================================================================

#[test]
fn pipeline_bool_not() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(|x: u32| -> bool { x > 5 }, r)
        .not();
    assert!(p.run(&mut world, 3)); // 3 > 5 is false, !false = true
    assert!(!p.run(&mut world, 10)); // 10 > 5 is true, !true = false
}

#[test]
fn pipeline_bool_and() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(|x: u32| -> bool { x > 5 }, r)
        .and(produce_true, r);
    assert!(p.run(&mut world, 10)); // true && true
    assert!(!p.run(&mut world, 3)); // false && true (short-circuits)
}

#[test]
fn pipeline_bool_or() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(|x: u32| -> bool { x > 5 }, r)
        .or(produce_true, r);
    assert!(p.run(&mut world, 3)); // false || true
    assert!(p.run(&mut world, 10)); // true || true (short-circuits)
}

#[test]
fn pipeline_bool_xor() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(|x: u32| -> bool { x > 5 }, r)
        .xor(produce_false, r);
    assert!(!p.run(&mut world, 3)); // false ^ false = false
    assert!(p.run(&mut world, 10)); // true ^ false = true
}

// =========================================================================
// 6. Pipeline special combinators
// =========================================================================

#[test]
fn pipeline_guard_with_res_param() {
    let mut wb = WorldBuilder::new();
    wb.register(ResU32(5));
    wb.register(ResU64(0));
    let mut world = wb.build();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(identity_u32, r)
        .guard(guard_positive_with_res, r)
        .map(|x: u32| x as u64, r)
        .map(store_u64, r)
        .build();

    p.run(&mut world, 10); // 10 > 5, passes guard
    assert_eq!(**world.resource::<ResU64>(), 10);

    p.run(&mut world, 3); // 3 > 5 is false, guarded out
    assert_eq!(**world.resource::<ResU64>(), 10); // unchanged
}

#[test]
fn pipeline_guard_arity0_closure() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(identity_u32, r)
        .guard(|x: &u32| *x > 10, r)
        .map(store_u32, r)
        .build();

    p.run(&mut world, 20);
    assert_eq!(**world.resource::<ResU32>(), 20);

    p.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU32>(), 20); // unchanged
}

#[test]
fn pipeline_tap_named_fn() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(identity_u32, r)
        .tap(tap_log, r)
        .then(store_u32, r)
        .build();
    p.run(&mut world, 7);
    assert_eq!(**world.resource::<ResU32>(), 7);
}

#[test]
fn pipeline_tap_arity0_closure() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(identity_u32, r)
        .tap(|_x: &u32| {}, r)
        .then(store_u32, r)
        .build();
    p.run(&mut world, 9);
    assert_eq!(**world.resource::<ResU32>(), 9);
}

#[test]
fn pipeline_route() {
    let mut world = build_world();
    let r = world.registry();

    let large = PipelineBuilder::new().then(|x: u32| x * 10, r);
    let small = PipelineBuilder::new().then(|x: u32| x, r);

    let mut p = PipelineBuilder::<u32>::new()
        .then(identity_u32, r)
        .route(|x: &u32| *x > 100, r, large, small)
        .then(store_u32, r)
        .build();

    p.run(&mut world, 200);
    assert_eq!(**world.resource::<ResU32>(), 2000);

    p.run(&mut world, 50);
    assert_eq!(**world.resource::<ResU32>(), 50);
}

#[test]
fn pipeline_tee() {
    let mut world = build_world();
    let r = world.registry();

    let side = DagArmSeed::<u32>::new()
        .then(|x: &u32| *x as u64, r)
        .then(dag_store_u64, r);

    let mut p = PipelineBuilder::<u32>::new()
        .then(identity_u32, r)
        .tee(side)
        .then(store_u32, r)
        .build();

    p.run(&mut world, 7);
    assert_eq!(**world.resource::<ResU32>(), 7);
    assert_eq!(**world.resource::<ResU64>(), 7);
}

#[test]
fn pipeline_dedup() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(identity_u32, r)
        .dedup()
        .map(store_u32, r)
        .build();

    p.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU32>(), 5);

    p.run(&mut world, 5); // duplicate, suppressed
    // store not called again, stays 5

    p.run(&mut world, 10);
    assert_eq!(**world.resource::<ResU32>(), 10);
}

#[test]
fn pipeline_scan() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(identity_u32, r)
        .scan(
            0u64,
            |acc: &mut u64, val: u32| {
                *acc += val as u64;
                *acc
            },
            r,
        )
        .then(store_u64, r)
        .build();

    p.run(&mut world, 1);
    assert_eq!(**world.resource::<ResU64>(), 1);

    p.run(&mut world, 2);
    assert_eq!(**world.resource::<ResU64>(), 3);

    p.run(&mut world, 3);
    assert_eq!(**world.resource::<ResU64>(), 6);
}

#[test]
fn pipeline_dispatch_to_handler() {
    let mut world = build_world();
    let r = world.registry();

    fn sink(mut out: ResMut<ResU64>, val: u64) {
        **out = val;
    }
    let handler = sink.into_handler(r);

    let mut p = PipelineBuilder::<u32>::new()
        .then(double_u32, r)
        .dispatch(handler)
        .build();

    p.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU64>(), 10);
}

// =========================================================================
// 7. Pipeline splat
// =========================================================================

#[test]
fn pipeline_splat2() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(make_pair, r)
        .splat()
        .then(splat2, r)
        .then(store_u32, r)
        .build();
    p.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU32>(), 11); // 5 + 6
}

#[test]
fn pipeline_splat3() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(make_triple, r)
        .splat()
        .then(splat3, r)
        .then(store_u32, r)
        .build();
    p.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU32>(), 18); // 5+6+7
}

#[test]
fn pipeline_splat4() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(make_quad, r)
        .splat()
        .then(splat4, r)
        .then(store_u32, r)
        .build();
    p.run(&mut world, 1);
    assert_eq!(**world.resource::<ResU32>(), 10); // 1+2+3+4
}

#[test]
fn pipeline_splat5() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(make_quint, r)
        .splat()
        .then(splat5, r)
        .then(store_u32, r)
        .build();
    p.run(&mut world, 0);
    assert_eq!(**world.resource::<ResU32>(), 10); // 0+1+2+3+4
}

#[test]
fn pipeline_splat_at_start() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<(u32, u32)>::new()
        .splat()
        .then(splat2, r)
        .then(store_u32, r)
        .build();
    p.run(&mut world, (3, 4));
    assert_eq!(**world.resource::<ResU32>(), 7);
}

// =========================================================================
// 8. Pipeline Opaque closures
// =========================================================================

#[test]
fn pipeline_guard_opaque() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(identity_u32, r)
        .guard(|_w: &mut World, x: &u32| -> bool { *x > 5 }, r)
        .map(store_u32, r)
        .build();
    p.run(&mut world, 10);
    assert_eq!(**world.resource::<ResU32>(), 10);
    p.run(&mut world, 3);
    assert_eq!(**world.resource::<ResU32>(), 10); // unchanged
}

#[test]
fn pipeline_tap_opaque() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(identity_u32, r)
        .tap(|_w: &mut World, _x: &u32| {}, r)
        .then(store_u32, r)
        .build();
    p.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU32>(), 5);
}

#[test]
fn pipeline_on_none_opaque() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(identity_u32, r)
        .guard(guard_positive, r)
        .on_none(|_w: &mut World| {}, r)
        .map(store_u32, r)
        .build();
    p.run(&mut world, 0); // guarded out, on_none fires
}

#[test]
fn pipeline_then_opaque() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(
            |w: &mut World, x: u32| {
                **w.resource_mut::<ResU64>() = x as u64;
            },
            r,
        )
        .build();
    p.run(&mut world, 42);
    assert_eq!(**world.resource::<ResU64>(), 42);
}

// =========================================================================
// 9. Pipeline Output<()> terminal
// =========================================================================

#[test]
fn pipeline_option_unit_terminal() {
    let mut world = build_world();
    let r = world.registry();
    // Chain ends with Option<()> -- build() should work
    let mut p = PipelineBuilder::<u32>::new()
        .then(identity_u32, r)
        .guard(guard_positive, r)
        .map(store_u32, r)
        .build();
    p.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU32>(), 5);
}

#[test]
fn pipeline_filter_then_map_sink() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(identity_u32, r)
        .guard(|_: &u32| true, r)
        .filter(filter_even, r)
        .map(store_u32, r)
        .build();
    p.run(&mut world, 4);
    assert_eq!(**world.resource::<ResU32>(), 4);
}

// =========================================================================
// 10. Pipeline borrowed events
// =========================================================================

#[test]
fn pipeline_borrowed_slice() {
    let mut world = build_world();
    let data = vec![1u8, 2, 3, 4, 5];
    let r = world.registry();

    fn decode(data: &[u8]) -> u32 {
        data.len() as u32
    }

    let mut p = PipelineBuilder::<&[u8]>::new()
        .then(decode, r)
        .then(store_u32, r)
        .build();

    p.run(&mut world, &data);
    assert_eq!(**world.resource::<ResU32>(), 5);
}

#[test]
fn pipeline_borrowed_str() {
    let mut world = build_world();
    let msg = String::from("hello");
    let r = world.registry();

    fn parse_len(s: &str) -> u32 {
        s.len() as u32
    }

    let mut p = PipelineBuilder::<&str>::new()
        .then(parse_len, r)
        .then(store_u32, r)
        .build();

    p.run(&mut world, msg.as_str());
    assert_eq!(**world.resource::<ResU32>(), 5);
}

#[test]
fn pipeline_borrowed_option_unit_terminal() {
    let mut world = build_world();
    let data = vec![1u8, 2, 3];
    let r = world.registry();

    fn decode_len(data: &[u8]) -> u32 {
        data.len() as u32
    }

    let mut p = PipelineBuilder::<&[u8]>::new()
        .then(decode_len, r)
        .guard(guard_positive, r)
        .map(store_u32, r)
        .build();

    p.run(&mut world, &data);
    assert_eq!(**world.resource::<ResU32>(), 3);
}

#[test]
fn pipeline_borrowed_through_guard() {
    let mut world = build_world();
    let r = world.registry();

    fn parse_val(s: &str) -> u32 {
        s.len() as u32
    }

    let mut p = PipelineBuilder::<&str>::new()
        .then(parse_val, r)
        .guard(guard_positive, r)
        .filter(filter_even, r)
        .map(store_u32, r)
        .build();

    // &str literal has 'static lifetime, no drop ordering issue
    p.run(&mut world, "abcd"); // len=4, positive, even
    assert_eq!(**world.resource::<ResU32>(), 4);
}

#[test]
fn pipeline_borrowed_run_direct() {
    let mut world = build_world();
    let data = vec![1u8, 2, 3, 4];
    let r = world.registry();

    fn decode_len(data: &[u8]) -> u32 {
        data.len() as u32
    }

    let mut builder = PipelineBuilder::<&[u8]>::new().then(decode_len, r);

    let result = builder.run(&mut world, &data);
    assert_eq!(result, 4);
}

#[test]
fn pipeline_to_boxed_handler() {
    let mut world = build_world();
    let r = world.registry();

    let p = PipelineBuilder::<u32>::new().then(store_u32, r).build();

    let mut boxed: Virtual<u32> = Box::new(p);
    boxed.run(&mut world, 77);
    assert_eq!(**world.resource::<ResU32>(), 77);
}

// =========================================================================
// 11. DAG basics
// =========================================================================

#[test]
fn dag_root_then_build() {
    let mut world = build_world();
    let r = world.registry();
    let mut d = DagBuilder::<u32>::new()
        .root(dag_id, r)
        .then(dag_store_u32, r)
        .build();
    d.run(&mut world, 42);
    assert_eq!(**world.resource::<ResU32>(), 42);
}

#[test]
fn dag_root_then_then_build() {
    let mut world = build_world();
    let r = world.registry();

    fn root_to_u64(x: u32) -> u64 {
        x as u64
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root_to_u64, r)
        .then(dag_add_one, r)
        .then(dag_store_u64, r)
        .build();
    d.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU64>(), 6);
}

#[test]
fn dag_root_single_step() {
    let mut world = build_world();
    let r = world.registry();
    let mut d = DagBuilder::<u32>::new()
        .root(
            |x: u32| {
                let _ = x;
            },
            r,
        )
        .build();
    d.run(&mut world, 1);
}

#[test]
fn dag_fork_merge_2arm() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> u32 {
        x
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .fork()
        .arm(|a| a.then(dag_double, r))
        .arm(|a| a.then(dag_negate, r))
        .merge(dag_merge_sum, r)
        .then(dag_store_f64, r)
        .build();

    d.run(&mut world, 10);
    // arm0: 10*2=20, arm1: -10, merge: 20+(-10)=10.0
    assert_eq!(**world.resource::<ResF64>(), 10.0);
}

#[test]
fn dag_fork_join_2arm() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> u32 {
        x
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .fork()
        .arm(|a| a.then(|x: &u32| *x as u64, r).then(dag_store_u64, r))
        .arm(|a| a.then(|x: &u32| -(*x as i64), r).then(dag_store_i64, r))
        .join()
        .build();

    d.run(&mut world, 7);
    assert_eq!(**world.resource::<ResU64>(), 7);
    assert_eq!(**world.resource::<ResI64>(), -7);
}

#[test]
fn dag_build_batch() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> u64 {
        x as u64
    }
    fn accumulate(mut sum: ResMut<ResU64>, val: &u64) {
        **sum += *val;
    }

    let mut batch = DagBuilder::<u32>::new()
        .root(root, r)
        .then(accumulate, r)
        .build_batch(8);

    batch.input_mut().extend([1, 2, 3]);
    batch.run(&mut world);
    assert_eq!(**world.resource::<ResU64>(), 6); // 1+2+3
    assert!(batch.input().is_empty());
}

// =========================================================================
// 12. DAG fork patterns
// =========================================================================

#[test]
fn dag_fork_merge_3arm() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> u32 {
        x
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .fork()
        .arm(|a| a.then(dag_double, r))
        .arm(|a| a.then(dag_negate, r))
        .arm(|a| a.then(|x: &u32| *x as f64 * 0.5, r))
        .merge(dag_merge3, r)
        .then(dag_store_f64, r)
        .build();

    d.run(&mut world, 10);
    // arm0: 20, arm1: -10, arm2: 5.0
    // merge: 20 + (-10) + 5.0 = 15.0
    assert_eq!(**world.resource::<ResF64>(), 15.0);
}

#[test]
fn dag_fork_merge_4arm() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> u64 {
        x as u64
    }
    fn arm_fn(x: &u64) -> u64 {
        *x
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .fork()
        .arm(|a| a.then(arm_fn, r))
        .arm(|a| a.then(arm_fn, r))
        .arm(|a| a.then(arm_fn, r))
        .arm(|a| a.then(arm_fn, r))
        .merge(dag_merge4, r)
        .then(dag_store_u64, r)
        .build();

    d.run(&mut world, 3);
    assert_eq!(**world.resource::<ResU64>(), 12); // 3*4
}

#[test]
fn dag_fork_arms_with_multiple_steps() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> u32 {
        x
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .fork()
        .arm(|a| a.then(dag_double, r).then(dag_add_one, r))
        .arm(|a| a.then(dag_negate, r))
        .merge(dag_merge_sum, r)
        .then(dag_store_f64, r)
        .build();

    d.run(&mut world, 5);
    // arm0: double=10, add_one=11
    // arm1: negate=-5
    // merge: 11 + (-5) = 6.0
    assert_eq!(**world.resource::<ResF64>(), 6.0);
}

#[test]
fn dag_fork_arm_with_guard() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> u64 {
        x as u64
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .fork()
        .arm(|a| {
            a.then(|x: &u64| *x, r)
                .guard(dag_guard_positive, r)
                .unwrap_or(0)
        })
        .arm(|a| a.then(|x: &u64| *x + 100, r))
        .merge(|a: &u64, b: &u64| *a + *b, r)
        .then(dag_store_u64, r)
        .build();

    d.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU64>(), 110); // 5 + 105
}

#[test]
fn dag_nested_fork() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> u32 {
        x
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .fork()
        .arm(|a| {
            a.then(|x: &u32| *x as u64, r)
                .fork()
                .arm(|inner| inner.then(|x: &u64| *x * 2, r))
                .arm(|inner| inner.then(|x: &u64| *x * 3, r))
                .merge(|a: &u64, b: &u64| (*a + *b) as f64, r)
        })
        .arm(|a| a.then(|x: &u32| *x as f64 * 10.0, r))
        .merge(|a: &f64, b: &f64| *a + *b, r)
        .then(dag_store_f64, r)
        .build();

    d.run(&mut world, 2);
    // inner arm0: 2*2=4, inner arm1: 2*3=6, inner merge: 10.0
    // outer arm1: 2*10=20.0
    // outer merge: 10.0 + 20.0 = 30.0
    assert_eq!(**world.resource::<ResF64>(), 30.0);
}

// =========================================================================
// 13. DAG splat
// =========================================================================

#[test]
fn dag_splat_chain() {
    let mut world = build_world();
    let r = world.registry();

    fn split(x: u32) -> (u32, u32) {
        (x, x + 1)
    }

    let mut d = DagBuilder::<u32>::new()
        .root(split, r)
        .splat()
        .then(dag_splat2, r)
        .then(dag_store_u32, r)
        .build();

    d.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU32>(), 11); // 5 + 6
}

#[test]
fn dag_splat_inside_arm() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> u32 {
        x
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .fork()
        .arm(|a| {
            a.then(|x: &u32| (*x, *x + 1), r)
                .splat()
                .then(dag_splat2, r)
        })
        .arm(|a| a.then(|x: &u32| *x * 10, r))
        .merge(|a: &u32, b: &u32| (*a + *b) as u64, r)
        .then(dag_store_u64, r)
        .build();

    d.run(&mut world, 3);
    // arm0: splat(3,4) -> 7
    // arm1: 30
    // merge: 37
    assert_eq!(**world.resource::<ResU64>(), 37);
}

// =========================================================================
// 14. DAG borrowed events
// =========================================================================

#[test]
fn dag_borrowed_slice() {
    let mut world = build_world();
    let data = vec![1u8, 2, 3];
    let r = world.registry();

    fn decode(data: &[u8]) -> u32 {
        data.len() as u32
    }

    let mut d = DagBuilder::<&[u8]>::new()
        .root(decode, r)
        .then(dag_store_u32, r)
        .build();

    d.run(&mut world, &data);
    assert_eq!(**world.resource::<ResU32>(), 3);
}

#[test]
fn dag_borrowed_through_fork() {
    let mut world = build_world();
    let data = vec![1u8, 2, 3, 4, 5];
    let r = world.registry();

    fn decode(data: &[u8]) -> u32 {
        data.len() as u32
    }

    let mut d = DagBuilder::<&[u8]>::new()
        .root(decode, r)
        .fork()
        .arm(|a| a.then(dag_double, r).then(dag_store_u64, r))
        .arm(|a| a.then(dag_negate, r).then(dag_store_i64, r))
        .join()
        .build();

    d.run(&mut world, &data);
    assert_eq!(**world.resource::<ResU64>(), 10); // 5 * 2
    assert_eq!(**world.resource::<ResI64>(), -5);
}

#[test]
fn dag_borrowed_with_guard() {
    let mut world = build_world();
    let data = vec![1u8, 2, 3];
    let short = vec![1u8];
    let r = world.registry();

    fn decode(data: &[u8]) -> u32 {
        data.len() as u32
    }

    let mut d = DagBuilder::<&[u8]>::new()
        .root(decode, r)
        .guard(|x: &u32| *x > 2, r)
        .unwrap_or(0)
        .then(dag_store_u32, r)
        .build();

    d.run(&mut world, &data);
    assert_eq!(**world.resource::<ResU32>(), 3);

    d.run(&mut world, &short);
    assert_eq!(**world.resource::<ResU32>(), 0); // guarded, unwrap_or
}

// =========================================================================
// 15. DAG Option<()> terminal
// =========================================================================

#[test]
fn dag_option_unit_terminal() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> u32 {
        x
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .guard(|x: &u32| *x > 0, r)
        .map(dag_store_u32, r)
        .build();

    d.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU32>(), 5);
}

// =========================================================================
// 16. DAG route
// =========================================================================

#[test]
fn dag_route() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> u32 {
        x
    }

    let fast = DagArmSeed::new().then(|x: &u32| *x as u64 * 100, r);
    let slow = DagArmSeed::new().then(|x: &u32| *x as u64, r);

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .route(|x: &u32| *x > 10, r, fast, slow)
        .then(dag_store_u64, r)
        .build();

    d.run(&mut world, 20);
    assert_eq!(**world.resource::<ResU64>(), 2000);

    d.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU64>(), 5);
}

// =========================================================================
// 17. Mixed patterns
// =========================================================================

#[test]
fn pipeline_dispatch_handler_interop() {
    let mut world = build_world();
    let r = world.registry();

    fn handler_fn(mut out: ResMut<ResU64>, event: u64) {
        **out = event * 10;
    }
    let handler = handler_fn.into_handler(r);

    let mut p = PipelineBuilder::<u32>::new()
        .then(double_u32, r)
        .dispatch(handler)
        .build();
    p.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU64>(), 100); // 5*2=10, handler: 10*10=100
}

#[test]
fn pipeline_result_catch_then() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(fallible_parse, r)
        .catch(catch_error, r)
        .map(store_u64, r)
        .build();

    p.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU64>(), 5);
}

#[test]
fn pipeline_guard_unwrap_then() {
    // Common validation pattern: guard -> unwrap_or -> then -> build
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(identity_u32, r)
        .guard(guard_positive, r)
        .unwrap_or(0)
        .then(|x: u32| x as u64, r)
        .then(store_u64, r)
        .build();

    p.run(&mut world, 10);
    assert_eq!(**world.resource::<ResU64>(), 10);

    p.run(&mut world, 0);
    assert_eq!(**world.resource::<ResU64>(), 0);
}

#[test]
fn pipeline_realistic_decode_validate_enrich_store() {
    let mut wb = WorldBuilder::new();
    wb.register(ResF64(0.0));
    let mut world = wb.build();
    let r = world.registry();

    let mut p = PipelineBuilder::<Order>::new()
        .then(validate_order, r)
        .and_then(
            |vo: ValidOrder| -> Option<EnrichedOrder> { Some(enrich_order(vo)) },
            r,
        )
        .map(store_enriched, r)
        .build();

    p.run(&mut world, Order::new(1, 10.0, 100));
    assert_eq!(**world.resource::<ResF64>(), 20.0);

    // Invalid order (price=0) gets None from validate, skipped
    p.run(&mut world, Order::new(2, 0.0, 50));
    assert_eq!(**world.resource::<ResF64>(), 20.0); // unchanged
}

#[test]
fn pipeline_long_realistic() {
    // decode -> validate -> enrich -> route -> sink
    let mut wb = WorldBuilder::new();
    wb.register(ResF64(0.0));
    wb.register(ResU64(0));
    let mut world = wb.build();
    let r = world.registry();

    fn decode(raw: u32) -> Order {
        Order::new(raw as u64, raw as f64, raw)
    }

    fn validate(order: Order) -> Result<Order, MyError> {
        if order.price > 0.0 {
            Ok(order)
        } else {
            Err(MyError("bad price".into()))
        }
    }

    fn log_error(_err: MyError) {}

    fn store_price(mut out: ResMut<ResF64>, order: Order) {
        **out = order.price;
    }

    let mut p = PipelineBuilder::<u32>::new()
        .then(decode, r)
        .then(validate, r)
        .catch(log_error, r)
        .map(store_price, r)
        .build();

    p.run(&mut world, 42);
    assert_eq!(**world.resource::<ResF64>(), 42.0);
}

// =========================================================================
// 18. Handler interop
// =========================================================================

#[test]
fn pipeline_build_into_virtual() {
    let mut world = build_world();
    let r = world.registry();

    let pipeline = PipelineBuilder::<u32>::new().then(store_u32, r).build();

    let mut v: Virtual<u32> = Box::new(pipeline);
    v.run(&mut world, 99);
    assert_eq!(**world.resource::<ResU32>(), 99);
}

#[test]
fn dag_build_into_virtual() {
    let mut world = build_world();
    let r = world.registry();

    let dag = DagBuilder::<u32>::new()
        .root(dag_id, r)
        .then(dag_store_u32, r)
        .build();

    let mut v: Virtual<u32> = Box::new(dag);
    v.run(&mut world, 88);
    assert_eq!(**world.resource::<ResU32>(), 88);
}

// =========================================================================
// 19. resolve_step / resolve_ref_step / resolve_producer helpers
// =========================================================================

#[test]
fn resolve_step_named_fn() {
    let mut world = build_world();
    let r = world.registry();

    let mut step = resolve_step(double_u32, r);
    let result = step(&mut world, 7);
    assert_eq!(result, 14);
}

#[test]
fn resolve_step_arity0_closure() {
    let mut world = build_world();
    let r = world.registry();

    let mut step = resolve_step(|x: u32| x + 100, r);
    let result = step(&mut world, 5);
    assert_eq!(result, 105);
}

#[test]
fn resolve_ref_step_named_fn() {
    let mut world = build_world();
    let r = world.registry();

    let mut step = resolve_ref_step(guard_positive, r);
    assert!(step(&mut world, &5));
    assert!(!step(&mut world, &0));
}

#[test]
fn resolve_producer_helper() {
    let mut world = build_world();
    let r = world.registry();

    let mut prod = resolve_producer(produce_true, r);
    assert!(prod(&mut world));
}

#[test]
fn resolve_arm_helper() {
    let mut world = build_world();
    let r = world.registry();

    fn dag_step(x: &u32) -> u64 {
        *x as u64 * 3
    }

    let mut arm = resolve_arm(dag_step, r);
    let result = arm(&mut world, &10);
    assert_eq!(result, 30);
}

// =========================================================================
// 20. Batch patterns
// =========================================================================

#[test]
fn batch_pipeline_fill_run_check() {
    let mut world = build_world();
    let r = world.registry();

    fn accumulate(mut sum: ResMut<ResU64>, x: u32) {
        **sum += x as u64;
    }

    let mut batch = PipelineBuilder::<u32>::new()
        .then(accumulate, r)
        .build_batch(32);

    assert!(batch.input().is_empty());
    batch.input_mut().extend_from_slice(&[10, 20, 30]);
    assert_eq!(batch.input().len(), 3);
    batch.run(&mut world);
    assert!(batch.input().is_empty());
    assert_eq!(**world.resource::<ResU64>(), 60);
}

#[test]
fn batch_dag_fill_run_check() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> u64 {
        x as u64
    }
    fn accumulate(mut sum: ResMut<ResU64>, val: &u64) {
        **sum += *val;
    }

    let mut batch = DagBuilder::<u32>::new()
        .root(root, r)
        .then(accumulate, r)
        .build_batch(32);

    assert!(batch.input().is_empty());
    batch.input_mut().extend([5, 10, 15]);
    assert_eq!(batch.input().len(), 3);
    batch.run(&mut world);
    assert!(batch.input().is_empty());
    assert_eq!(**world.resource::<ResU64>(), 30);
}

// =========================================================================
// Additional edge case tests
// =========================================================================

#[test]
fn pipeline_scan_at_start() {
    let mut world = build_world();
    let r = world.registry();

    let mut p = PipelineBuilder::<u32>::new()
        .scan(
            0u64,
            |acc: &mut u64, x: u32| {
                *acc += x as u64;
                *acc
            },
            r,
        )
        .then(store_u64, r)
        .build();

    p.run(&mut world, 1);
    assert_eq!(**world.resource::<ResU64>(), 1);
    p.run(&mut world, 2);
    assert_eq!(**world.resource::<ResU64>(), 3);
}

#[test]
fn dag_scan() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> u32 {
        x
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .scan(
            0u64,
            |acc: &mut u64, x: &u32| {
                *acc += *x as u64;
                *acc
            },
            r,
        )
        .then(dag_store_u64, r)
        .build();

    d.run(&mut world, 10);
    assert_eq!(**world.resource::<ResU64>(), 10);
    d.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU64>(), 15);
}

#[test]
fn dag_dedup() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> u32 {
        x
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .dedup()
        .map(dag_store_u32, r)
        .build();

    d.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU32>(), 5);

    d.run(&mut world, 5); // duplicate, suppressed
    d.run(&mut world, 10);
    assert_eq!(**world.resource::<ResU32>(), 10);
}

#[test]
fn dag_bool_not_and() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> bool {
        x > 5
    }
    fn store_bool(mut out: ResMut<ResBool>, val: &bool) {
        **out = *val;
    }

    // Test: !root && produce_true — store the result
    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .not()
        .and(produce_true, r)
        .then(store_bool, r)
        .build();

    d.run(&mut world, 3); // 3>5=false, !false=true, true&&true
    assert!(**world.resource::<ResBool>());

    d.run(&mut world, 10); // 10>5=true, !true=false, false&&true (short-circuits)
    assert!(!**world.resource::<ResBool>());
}

#[test]
fn dag_tap() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> u64 {
        x as u64
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .tap(dag_tap_noop, r)
        .then(dag_store_u64, r)
        .build();

    d.run(&mut world, 7);
    assert_eq!(**world.resource::<ResU64>(), 7);
}

#[test]
fn dag_tee() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> u32 {
        x
    }

    let side = DagArmSeed::<u32>::new()
        .then(|x: &u32| *x as u64, r)
        .then(dag_store_u64, r);

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .tee(side)
        .then(dag_store_u32, r)
        .build();

    d.run(&mut world, 9);
    assert_eq!(**world.resource::<ResU32>(), 9);
    assert_eq!(**world.resource::<ResU64>(), 9);
}

#[test]
fn dag_result_combinators() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> Result<u64, MyError> {
        if x < 100 {
            Ok(x as u64)
        } else {
            Err(MyError("too large".into()))
        }
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .map(|x: &u64| *x * 2, r)
        .catch(|_err: &MyError| {}, r)
        .map(dag_store_u64, r)
        .build();

    d.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU64>(), 10);

    d.run(&mut world, 200); // error path
    assert_eq!(**world.resource::<ResU64>(), 10); // unchanged
}

#[test]
fn dag_option_combinators() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> u32 {
        x
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .guard(|x: &u32| *x > 0, r)
        .filter(|x: &u32| (*x).is_multiple_of(2), r)
        .inspect(|_x: &u32| {}, r)
        .map(dag_store_u32, r)
        .build();

    d.run(&mut world, 4);
    assert_eq!(**world.resource::<ResU32>(), 4);

    d.run(&mut world, 3); // odd, filtered
    assert_eq!(**world.resource::<ResU32>(), 4);

    d.run(&mut world, 0); // guarded
    assert_eq!(**world.resource::<ResU32>(), 4);
}

#[test]
fn dag_option_ok_or() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> u32 {
        x
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .guard(|x: &u32| *x > 0, r)
        .ok_or("zero")
        .map(dag_store_u32, r)
        .catch(|_e: &&str| {}, r)
        .build();

    d.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU32>(), 5);
}

#[test]
fn dag_option_unwrap_or() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> u32 {
        x
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .guard(|x: &u32| *x > 0, r)
        .unwrap_or(99)
        .then(dag_store_u32, r)
        .build();

    d.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU32>(), 5);

    d.run(&mut world, 0);
    assert_eq!(**world.resource::<ResU32>(), 99);
}

#[test]
fn dag_result_ok() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> Result<u64, MyError> {
        if x > 0 {
            Ok(x as u64)
        } else {
            Err(MyError("zero".into()))
        }
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .ok()
        .map(dag_store_u64, r)
        .build();

    d.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU64>(), 5);
}

#[test]
fn dag_result_unwrap_or() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> Result<u64, MyError> {
        if x > 0 {
            Ok(x as u64)
        } else {
            Err(MyError("zero".into()))
        }
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .unwrap_or(999)
        .then(dag_store_u64, r)
        .build();

    d.run(&mut world, 0);
    assert_eq!(**world.resource::<ResU64>(), 999);
}

#[test]
fn dag_result_map_err() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> Result<u64, MyError> {
        if x > 0 {
            Ok(x as u64)
        } else {
            Err(MyError("zero".into()))
        }
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .map_err(|e: MyError| e.0, r)
        .ok()
        .map(dag_store_u64, r)
        .build();

    d.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU64>(), 5);
}

#[test]
fn dag_result_inspect_err() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> Result<u64, MyError> {
        if x > 0 {
            Ok(x as u64)
        } else {
            Err(MyError("zero".into()))
        }
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .inspect_err(|_e: &MyError| {}, r)
        .ok()
        .map(dag_store_u64, r)
        .build();

    d.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU64>(), 5);
}

#[test]
fn dag_result_or_else() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> Result<u64, MyError> {
        if x > 0 {
            Ok(x as u64)
        } else {
            Err(MyError("zero".into()))
        }
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .or_else(|_e: MyError| -> Result<u64, String> { Ok(0) }, r)
        .ok()
        .map(dag_store_u64, r)
        .build();

    d.run(&mut world, 0);
    assert_eq!(**world.resource::<ResU64>(), 0);
}

#[test]
fn dag_dispatch() {
    let mut world = build_world();
    let r = world.registry();

    fn handler_fn(mut out: ResMut<ResU64>, event: u64) {
        **out = event;
    }
    let handler = handler_fn.into_handler(r);

    fn root(x: u32) -> u64 {
        x as u64 * 3
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .dispatch(handler)
        .build();

    d.run(&mut world, 7);
    assert_eq!(**world.resource::<ResU64>(), 21);
}

#[test]
fn pipeline_ok_or_else() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(identity_u32, r)
        .guard(guard_positive, r)
        .ok_or_else(|| "was zero".to_string(), r)
        .catch(|_err: String| {}, r)
        .map(store_u32, r)
        .build();
    p.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU32>(), 5);
}

#[test]
fn pipeline_unwrap_or_else_option() {
    let mut world = build_world();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(identity_u32, r)
        .guard(guard_positive, r)
        .unwrap_or_else(|| 42, r)
        .then(store_u32, r)
        .build();

    p.run(&mut world, 0);
    assert_eq!(**world.resource::<ResU32>(), 42);

    p.run(&mut world, 7);
    assert_eq!(**world.resource::<ResU32>(), 7);
}

#[test]
fn dag_option_on_none() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> u32 {
        x
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .guard(|x: &u32| *x > 0, r)
        .on_none(|| {}, r)
        .map(dag_store_u32, r)
        .build();

    d.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU32>(), 5);
}

#[test]
fn dag_option_ok_or_else() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> u32 {
        x
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .guard(|x: &u32| *x > 0, r)
        .ok_or_else(|| "zero".to_string(), r)
        .ok()
        .map(dag_store_u32, r)
        .build();

    d.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU32>(), 5);
}

#[test]
fn dag_option_unwrap_or_else() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> u32 {
        x
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .guard(|x: &u32| *x > 0, r)
        .unwrap_or_else(|| 42, r)
        .then(dag_store_u32, r)
        .build();

    d.run(&mut world, 0);
    assert_eq!(**world.resource::<ResU32>(), 42);
}

#[test]
fn dag_result_unwrap_or_else() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> Result<u64, MyError> {
        if x > 0 {
            Ok(x as u64)
        } else {
            Err(MyError("zero".into()))
        }
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .unwrap_or_else(|_e: MyError| 999, r)
        .then(dag_store_u64, r)
        .build();

    d.run(&mut world, 0);
    assert_eq!(**world.resource::<ResU64>(), 999);
}

#[test]
fn dag_result_and_then() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> Result<u64, MyError> {
        if x > 0 {
            Ok(x as u64)
        } else {
            Err(MyError("zero".into()))
        }
    }

    fn validate(x: &u64) -> Result<u64, MyError> {
        if *x < 100 {
            Ok(*x * 2)
        } else {
            Err(MyError("too large".into()))
        }
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .and_then(validate, r)
        .ok()
        .map(dag_store_u64, r)
        .build();

    d.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU64>(), 10);
}

#[test]
fn dag_bool_or() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> bool {
        x > 5
    }
    fn store_bool(mut out: ResMut<ResBool>, val: &bool) {
        **out = *val;
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .or(produce_false, r)
        .then(store_bool, r)
        .build();

    d.run(&mut world, 10); // true || false
    assert!(**world.resource::<ResBool>());

    d.run(&mut world, 3); // false || false
    assert!(!**world.resource::<ResBool>());
}

#[test]
fn dag_bool_xor() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> bool {
        x > 5
    }
    fn store_bool(mut out: ResMut<ResBool>, val: &bool) {
        **out = *val;
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .xor(produce_true, r)
        .then(store_bool, r)
        .build();

    d.run(&mut world, 10); // true ^ true = false
    assert!(!**world.resource::<ResBool>());

    d.run(&mut world, 3); // false ^ true = true
    assert!(**world.resource::<ResBool>());
}

#[test]
fn batch_pipeline_option_terminal() {
    let mut world = build_world();
    let r = world.registry();

    fn accumulate(mut sum: ResMut<ResU64>, x: u32) {
        **sum += x as u64;
    }

    let mut batch = PipelineBuilder::<u32>::new()
        .then(identity_u32, r)
        .guard(guard_positive, r)
        .map(accumulate, r)
        .build_batch(16);

    batch.input_mut().extend_from_slice(&[0, 1, 2, 3]);
    batch.run(&mut world);
    // 0 is guarded out, 1+2+3 = 6
    assert_eq!(**world.resource::<ResU64>(), 6);
}

#[test]
fn dag_batch_option_terminal() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> u32 {
        x
    }
    fn accumulate(mut sum: ResMut<ResU64>, x: &u32) {
        **sum += *x as u64;
    }

    let mut batch = DagBuilder::<u32>::new()
        .root(root, r)
        .guard(|x: &u32| *x > 0, r)
        .map(accumulate, r)
        .build_batch(16);

    batch.input_mut().extend([0, 1, 2, 3]);
    batch.run(&mut world);
    assert_eq!(**world.resource::<ResU64>(), 6);
}

#[test]
fn dag_join_3arm() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> u32 {
        x
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .fork()
        .arm(|a| {
            a.then(
                |x: &u32| {
                    let _ = *x;
                },
                r,
            )
        })
        .arm(|a| {
            a.then(
                |x: &u32| {
                    let _ = *x;
                },
                r,
            )
        })
        .arm(|a| a.then(dag_store_u32, r))
        .join()
        .build();

    d.run(&mut world, 11);
    assert_eq!(**world.resource::<ResU32>(), 11);
}

#[test]
fn dag_join_4arm() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> u32 {
        x
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .fork()
        .arm(|a| {
            a.then(
                |x: &u32| {
                    let _ = *x;
                },
                r,
            )
        })
        .arm(|a| {
            a.then(
                |x: &u32| {
                    let _ = *x;
                },
                r,
            )
        })
        .arm(|a| {
            a.then(
                |x: &u32| {
                    let _ = *x;
                },
                r,
            )
        })
        .arm(|a| a.then(dag_store_u32, r))
        .join()
        .build();

    d.run(&mut world, 22);
    assert_eq!(**world.resource::<ResU32>(), 22);
}

#[test]
fn pipeline_tap_with_res() {
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(0));
    wb.register(ResU32(0));
    let mut world = wb.build();
    let r = world.registry();
    let mut p = PipelineBuilder::<u32>::new()
        .then(identity_u32, r)
        .tap(tap_log_with_res, r)
        .then(store_u32, r)
        .build();
    p.run(&mut world, 3);
    assert_eq!(**world.resource::<ResU32>(), 3);
}

#[test]
fn dag_option_and_then() {
    let mut world = build_world();
    let r = world.registry();

    fn root(x: u32) -> u32 {
        x
    }

    fn validate(x: &u32) -> Option<u64> {
        if *x > 5 { Some(*x as u64) } else { None }
    }

    let mut d = DagBuilder::<u32>::new()
        .root(root, r)
        .guard(|x: &u32| *x > 0, r)
        .and_then(validate, r)
        .map(dag_store_u64, r)
        .build();

    d.run(&mut world, 10);
    assert_eq!(**world.resource::<ResU64>(), 10);
}

#[test]
fn pipeline_multiple_batch_runs() {
    let mut world = build_world();
    let r = world.registry();

    fn accumulate(mut sum: ResMut<ResU64>, x: u32) {
        **sum += x as u64;
    }

    let mut batch = PipelineBuilder::<u32>::new()
        .then(accumulate, r)
        .build_batch(16);

    batch.input_mut().extend_from_slice(&[1, 2, 3]);
    batch.run(&mut world);
    assert_eq!(**world.resource::<ResU64>(), 6);

    batch.input_mut().extend_from_slice(&[4, 5]);
    batch.run(&mut world);
    assert_eq!(**world.resource::<ResU64>(), 15);
}

// =========================================================================
// 21. HRTB boxing — borrowed event dispatch
// =========================================================================
//
// These tests prove that Pipeline and Dag can be boxed as
// `Box<dyn for<'a> Handler<&'a T>>` for zero-copy event dispatch with
// borrowed data. Primarily compile-time tests — if they compile, the HRTB
// bounds are satisfied. Runtime assertions verify dispatch correctness.
//
// NOT tested (documented reasons):
// - BatchPipeline/BatchDag with borrowed events: Batch stores items in
//   Vec<In>, requires In: 'static. Can't store &'a T in a Vec.
// - Templates with borrowed events: Blueprint::Event is an associated
//   type, can't express HRTB at the type level.

// -- HRTB helper types and step functions --

#[derive(Debug)]
#[allow(dead_code)]
struct Message<'a> {
    topic: u8,
    payload: &'a [u8],
}

fn slice_len(data: &[u8]) -> usize {
    data.len()
}
fn store_len(mut out: ResMut<ResU64>, len: usize) {
    **out = len as u64;
}

fn msg_payload_len(msg: Message<'_>) -> usize {
    msg.payload.len()
}

fn hrtb_dag_double_len(len: &usize) -> usize {
    *len * 2
}
fn hrtb_dag_store_len(mut out: ResMut<ResU64>, len: &usize) {
    **out = *len as u64;
}
fn hrtb_dag_add_lens(a: &usize, b: &usize) -> usize {
    *a + *b
}

#[test]
fn hrtb_pipeline_basic() {
    let mut world = build_world();
    let r = world.registry();

    let pipeline = PipelineBuilder::<&[u8]>::new()
        .then(slice_len, r)
        .then(store_len, r)
        .build();

    let mut boxed: Box<dyn for<'a> Handler<&'a [u8]>> = Box::new(pipeline);

    let data = vec![1u8, 2, 3, 4, 5];
    boxed.run(&mut world, &data);
    assert_eq!(**world.resource::<ResU64>(), 5);
}

#[test]
fn hrtb_pipeline_with_guard() {
    let mut world = build_world();
    let r = world.registry();

    let pipeline = PipelineBuilder::<&[u8]>::new()
        .then(slice_len, r)
        .guard(|len: &usize| *len > 2, r)
        .map(store_len, r)
        .build();

    let mut boxed: Box<dyn for<'a> Handler<&'a [u8]>> = Box::new(pipeline);

    let data = vec![1u8, 2, 3];
    boxed.run(&mut world, &data);
    assert_eq!(**world.resource::<ResU64>(), 3);

    // Short slice — guard filters, store_len not called, value unchanged
    let short = vec![1u8];
    boxed.run(&mut world, &short);
    assert_eq!(**world.resource::<ResU64>(), 3);
}

#[test]
fn hrtb_pipeline_with_option_chain() {
    let mut world = build_world();
    let r = world.registry();

    fn mark_none(mut flag: ResMut<ResBool>) {
        **flag = true;
    }

    let pipeline = PipelineBuilder::<&[u8]>::new()
        .then(slice_len, r)
        .guard(|len: &usize| *len > 0, r)
        .map(store_len, r)
        .on_none(mark_none, r)
        .build();

    let mut boxed: Box<dyn for<'a> Handler<&'a [u8]>> = Box::new(pipeline);

    let data = vec![10u8, 20, 30];
    boxed.run(&mut world, &data);
    assert_eq!(**world.resource::<ResU64>(), 3);
    assert!(!**world.resource::<ResBool>()); // on_none did NOT fire

    // Empty — guard rejects, on_none fires, store not called
    let empty: Vec<u8> = vec![];
    boxed.run(&mut world, &empty);
    assert_eq!(**world.resource::<ResU64>(), 3); // unchanged
    assert!(**world.resource::<ResBool>()); // on_none DID fire
}

#[test]
fn hrtb_pipeline_with_closure() {
    let mut world = build_world();
    let r = world.registry();

    // Arity-0 closures in .then() and .guard() positions (not just guard)
    let pipeline = PipelineBuilder::<&[u8]>::new()
        .then(|data: &[u8]| data.len() * 2, r)
        .guard(|doubled: &usize| *doubled > 0, r)
        .map(
            |val: usize| {
                let _ = val;
            },
            r,
        )
        .build();

    let mut boxed: Box<dyn for<'a> Handler<&'a [u8]>> = Box::new(pipeline);

    let data = vec![7u8, 8];
    boxed.run(&mut world, &data);
    // Compiles + runs — arity-0 closures compose through HRTB
}

#[test]
fn hrtb_dag_basic() {
    let mut world = build_world();
    let r = world.registry();

    let dag = DagBuilder::<&[u8]>::new()
        .root(slice_len, r)
        .then(hrtb_dag_store_len, r)
        .build();

    let mut boxed: Box<dyn for<'a> Handler<&'a [u8]>> = Box::new(dag);

    let data = vec![1u8, 2, 3];
    boxed.run(&mut world, &data);
    assert_eq!(**world.resource::<ResU64>(), 3);
}

#[test]
fn hrtb_dag_fork_merge() {
    let mut world = build_world();
    let r = world.registry();

    let dag = DagBuilder::<&[u8]>::new()
        .root(slice_len, r)
        .fork()
        .arm(|a| a.then(hrtb_dag_double_len, r))
        .arm(|a| a.then(|len: &usize| *len + 10, r))
        .merge(hrtb_dag_add_lens, r)
        .then(hrtb_dag_store_len, r)
        .build();

    let mut boxed: Box<dyn for<'a> Handler<&'a [u8]>> = Box::new(dag);

    let data = vec![1u8, 2, 3, 4, 5]; // len=5
    boxed.run(&mut world, &data);
    // arm0: 5*2=10, arm1: 5+10=15, merge: 10+15=25
    assert_eq!(**world.resource::<ResU64>(), 25);
}

#[test]
fn hrtb_dag_fork_join() {
    let mut world = build_world();
    let r = world.registry();

    fn store_len_u32(mut out: ResMut<ResU32>, len: &usize) {
        **out = *len as u32;
    }
    fn store_len_i64(mut out: ResMut<ResI64>, len: &usize) {
        **out = *len as i64;
    }

    let dag = DagBuilder::<&[u8]>::new()
        .root(slice_len, r)
        .fork()
        .arm(|a| a.then(store_len_u32, r))
        .arm(|a| a.then(store_len_i64, r))
        .join()
        .build();

    let mut boxed: Box<dyn for<'a> Handler<&'a [u8]>> = Box::new(dag);

    let data = vec![1u8, 2, 3, 4];
    boxed.run(&mut world, &data);
    assert_eq!(**world.resource::<ResU32>(), 4);
    assert_eq!(**world.resource::<ResI64>(), 4);
}

#[test]
fn hrtb_borrowed_struct_event() {
    let mut world = build_world();
    let r = world.registry();

    let pipeline = PipelineBuilder::<Message<'_>>::new()
        .then(msg_payload_len, r)
        .then(store_len, r)
        .build();

    let mut boxed: Box<dyn for<'a> Handler<Message<'a>>> = Box::new(pipeline);

    let payload = vec![10u8, 20, 30, 40];
    let msg = Message {
        topic: 1,
        payload: &payload,
    };
    boxed.run(&mut world, msg);
    assert_eq!(**world.resource::<ResU64>(), 4);
}

#[test]
fn hrtb_dispatch_map() {
    let mut world = build_world();
    let r = world.registry();

    fn store_len_u32(mut out: ResMut<ResU32>, len: usize) {
        **out = len as u32;
    }

    let p1 = PipelineBuilder::<&[u8]>::new()
        .then(slice_len, r)
        .then(store_len, r)
        .build();

    let p2 = PipelineBuilder::<&[u8]>::new()
        .then(slice_len, r)
        .then(store_len_u32, r)
        .build();

    type HrtbSliceHandler = Box<dyn for<'a> Handler<&'a [u8]>>;
    let mut map: std::collections::HashMap<u8, HrtbSliceHandler> = std::collections::HashMap::new();
    map.insert(0, Box::new(p1));
    map.insert(1, Box::new(p2));

    let data = vec![1u8, 2, 3];
    map.get_mut(&0).unwrap().run(&mut world, &data);
    assert_eq!(**world.resource::<ResU64>(), 3);

    let data2 = vec![10u8, 20];
    map.get_mut(&1).unwrap().run(&mut world, &data2);
    assert_eq!(**world.resource::<ResU32>(), 2);
}

#[test]
fn hrtb_direct_run_no_boxing() {
    let mut world = build_world();
    let r = world.registry();

    let mut pipeline = PipelineBuilder::<&[u8]>::new()
        .then(slice_len, r)
        .then(store_len, r)
        .build();

    let data = vec![1u8, 2, 3, 4, 5, 6];
    pipeline.run(&mut world, &data);
    assert_eq!(**world.resource::<ResU64>(), 6);
}

#[test]
fn hrtb_dag_direct_run_no_boxing() {
    let mut world = build_world();
    let r = world.registry();

    let mut dag = DagBuilder::<&[u8]>::new()
        .root(slice_len, r)
        .then(hrtb_dag_double_len, r)
        .then(hrtb_dag_store_len, r)
        .build();

    let data = vec![1u8, 2, 3];
    dag.run(&mut world, &data);
    assert_eq!(**world.resource::<ResU64>(), 6); // 3 * 2
}

#[test]
fn hrtb_pipeline_and_dag_in_same_map() {
    let mut world = build_world();
    let r = world.registry();

    let pipeline = PipelineBuilder::<&[u8]>::new()
        .then(slice_len, r)
        .then(store_len, r)
        .build();

    let dag = DagBuilder::<&[u8]>::new()
        .root(slice_len, r)
        .then(hrtb_dag_double_len, r)
        .then(hrtb_dag_store_len, r)
        .build();

    type HrtbSliceHandler = Box<dyn for<'a> Handler<&'a [u8]>>;
    let mut map: std::collections::HashMap<u8, HrtbSliceHandler> = std::collections::HashMap::new();
    map.insert(0, Box::new(pipeline));
    map.insert(1, Box::new(dag));

    let data = vec![1u8, 2, 3, 4];
    map.get_mut(&0).unwrap().run(&mut world, &data);
    assert_eq!(**world.resource::<ResU64>(), 4);

    let data2 = vec![10u8, 20, 30];
    map.get_mut(&1).unwrap().run(&mut world, &data2);
    assert_eq!(**world.resource::<ResU64>(), 6); // 3 * 2
}

#[test]
fn hrtb_disjoint_lifetimes() {
    let mut world = build_world();
    let r = world.registry();

    let pipeline = PipelineBuilder::<&[u8]>::new()
        .then(slice_len, r)
        .then(store_len, r)
        .build();

    let mut boxed: Box<dyn for<'a> Handler<&'a [u8]>> = Box::new(pipeline);

    // First dispatch — borrow from a scope that ends
    {
        let data = vec![1u8, 2, 3];
        boxed.run(&mut world, &data);
        assert_eq!(**world.resource::<ResU64>(), 3);
    }
    // data is dropped — if the handler held a reference, this would be UB

    // Second dispatch — completely different borrow
    {
        let other = [10u8, 20, 30, 40, 50];
        boxed.run(&mut world, &other);
        assert_eq!(**world.resource::<ResU64>(), 5);
    }
}

#[test]
fn hrtb_pipeline_opaque_closure() {
    let mut world = build_world();
    let r = world.registry();

    let pipeline = PipelineBuilder::<&[u8]>::new()
        .then(slice_len, r)
        .then(
            |w: &mut World, len: usize| {
                **w.resource_mut::<ResU64>() = len as u64;
            },
            r,
        )
        .build();

    let mut boxed: Box<dyn for<'a> Handler<&'a [u8]>> = Box::new(pipeline);

    let data = vec![1u8, 2, 3, 4];
    boxed.run(&mut world, &data);
    assert_eq!(**world.resource::<ResU64>(), 4);
}

#[test]
fn hrtb_pipeline_tee() {
    let mut world = build_world();
    let r = world.registry();

    fn store_len_u32(mut out: ResMut<ResU32>, len: &usize) {
        **out = *len as u32;
    }

    // Side arm observes &usize (nested HRTB: C: for<'a> ChainCall<&'a usize>)
    let side = DagArmSeed::<usize>::new().then(store_len_u32, r);

    let pipeline = PipelineBuilder::<&[u8]>::new()
        .then(slice_len, r)
        .tee(side)
        .then(store_len, r)
        .build();

    let mut boxed: Box<dyn for<'a> Handler<&'a [u8]>> = Box::new(pipeline);

    let data = vec![1u8, 2, 3, 4, 5];
    boxed.run(&mut world, &data);
    assert_eq!(**world.resource::<ResU64>(), 5); // main path stored len
    assert_eq!(**world.resource::<ResU32>(), 5); // side arm also observed len
}

#[test]
fn hrtb_send_bound() {
    fn assert_send<T: Send>() {}
    assert_send::<Box<dyn for<'a> Handler<&'a [u8]>>>();
    assert_send::<Box<dyn for<'a> Handler<Message<'a>>>>();
}

#[test]
fn hrtb_pipeline_local() {
    let mut world = build_world();
    let r = world.registry();

    // Local<u64> persists across dispatches — counts invocations
    fn count_and_store(mut count: Local<u64>, mut out: ResMut<ResU64>, data: &[u8]) {
        *count += 1;
        **out = data.len() as u64 * 100 + *count;
    }

    let pipeline = PipelineBuilder::<&[u8]>::new()
        .then(count_and_store, r)
        .build();

    let mut boxed: Box<dyn for<'a> Handler<&'a [u8]>> = Box::new(pipeline);

    let data = vec![1u8, 2, 3];
    boxed.run(&mut world, &data);
    assert_eq!(**world.resource::<ResU64>(), 301); // len=3, count=1

    let data2 = vec![10u8, 20];
    boxed.run(&mut world, &data2);
    assert_eq!(**world.resource::<ResU64>(), 202); // len=2, count=2

    boxed.run(&mut world, &data);
    assert_eq!(**world.resource::<ResU64>(), 303); // len=3, count=3
}

#[test]
fn hrtb_pipeline_multi_param() {
    let mut wb = WorldBuilder::new();
    wb.register(ResF64(2.5));
    wb.register(ResU64(0));
    let mut world = wb.build();
    let r = world.registry();

    fn scaled_store(factor: Res<ResF64>, mut out: ResMut<ResU64>, data: &[u8]) {
        **out = (data.len() as f64 * **factor) as u64;
    }

    let pipeline = PipelineBuilder::<&[u8]>::new()
        .then(scaled_store, r)
        .build();

    let mut boxed: Box<dyn for<'a> Handler<&'a [u8]>> = Box::new(pipeline);

    let data = vec![1u8, 2, 3, 4]; // len=4, factor=2.5 → 10
    boxed.run(&mut world, &data);
    assert_eq!(**world.resource::<ResU64>(), 10);
}

// =========================================================================
// IntoSystem void return + run_startup
// =========================================================================

// -- Named fns for void system tests --

fn void_noop() {}

fn void_write_u64(mut v: ResMut<ResU64>) {
    **v = 42;
}

fn void_read_and_write(factor: Res<ResU64>, mut out: ResMut<ResString>) {
    **out = format!("value={}", **factor);
}

fn void_three_params(a: Res<ResU64>, mut b: ResMut<ResBool>, mut c: ResMut<ResString>) {
    if **a > 10 {
        **b = true;
        **c = "big".into();
    }
}

fn void_with_local(mut count: Local<u64>, mut out: ResMut<ResU64>) {
    *count += 1;
    **out = *count;
}

fn void_with_optional(opt: Option<Res<ResU64>>, mut out: ResMut<ResString>) {
    match opt {
        Some(v) => **out = format!("found={}", **v),
        None => **out = "missing".into(),
    }
}

fn void_with_seq(seq: Seq, mut out: ResMut<ResU64>) {
    let _ = seq.get();
    **out = 1;
}

fn void_with_seq_mut(mut seq: SeqMut, mut out: ResMut<ResU64>) {
    seq.advance();
    **out = 1;
}

fn void_with_shutdown(shutdown: Shutdown) {
    shutdown.trigger();
}

fn bool_system_still_works(val: Res<ResU64>) -> bool {
    **val > 10
}

// -- Void IntoSystem compile tests --

#[test]
fn void_system_arity0() {
    let mut world = WorldBuilder::new().build();
    let mut sys = void_noop.into_system(world.registry());
    assert!(sys.run(&mut world));
}

#[test]
fn void_system_single_res_mut() {
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(0));
    let mut world = wb.build();
    let mut sys = void_write_u64.into_system(world.registry());
    assert!(sys.run(&mut world));
    assert_eq!(**world.resource::<ResU64>(), 42);
}

#[test]
fn void_system_two_params() {
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(100));
    wb.register(ResString(String::new()));
    let mut world = wb.build();
    let mut sys = void_read_and_write.into_system(world.registry());
    assert!(sys.run(&mut world));
    assert_eq!(world.resource::<ResString>().as_str(), "value=100");
}

#[test]
fn void_system_three_params() {
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(42));
    wb.register(ResBool(false));
    wb.register(ResString(String::new()));
    let mut world = wb.build();
    let mut sys = void_three_params.into_system(world.registry());
    assert!(sys.run(&mut world));
    assert!(**world.resource::<ResBool>());
    assert_eq!(world.resource::<ResString>().as_str(), "big");
}

#[test]
fn void_system_with_local() {
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(0));
    let mut world = wb.build();
    let mut sys = void_with_local.into_system(world.registry());
    sys.run(&mut world);
    assert_eq!(**world.resource::<ResU64>(), 1);
    sys.run(&mut world);
    assert_eq!(**world.resource::<ResU64>(), 2);
}

#[test]
fn void_system_with_optional_present() {
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(99));
    wb.register(ResString(String::new()));
    let mut world = wb.build();
    let mut sys = void_with_optional.into_system(world.registry());
    sys.run(&mut world);
    assert_eq!(world.resource::<ResString>().as_str(), "found=99");
}

#[test]
fn void_system_with_optional_missing() {
    let mut wb = WorldBuilder::new();
    wb.register(ResString(String::new()));
    let mut world = wb.build();
    let mut sys = void_with_optional.into_system(world.registry());
    sys.run(&mut world);
    assert_eq!(world.resource::<ResString>().as_str(), "missing");
}

#[test]
fn void_system_with_seq() {
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(0));
    let mut world = wb.build();
    let mut sys = void_with_seq.into_system(world.registry());
    assert!(sys.run(&mut world));
    assert_eq!(**world.resource::<ResU64>(), 1);
}

#[test]
fn void_system_with_seq_mut() {
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(0));
    let mut world = wb.build();
    let mut sys = void_with_seq_mut.into_system(world.registry());
    assert!(sys.run(&mut world));
    assert_eq!(**world.resource::<ResU64>(), 1);
}

#[test]
fn void_system_boxed() {
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(0));
    let mut world = wb.build();
    let mut boxed: Box<dyn System> = Box::new(void_write_u64.into_system(world.registry()));
    assert!(boxed.run(&mut world));
    assert_eq!(**world.resource::<ResU64>(), 42);
}

#[test]
fn bool_system_regression() {
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(42));
    let mut world = wb.build();
    let mut sys = bool_system_still_works.into_system(world.registry());
    assert!(sys.run(&mut world));
}

// -- run_startup compile tests --

#[test]
fn run_startup_void_no_params() {
    let mut world = WorldBuilder::new().build();
    world.run_startup(void_noop);
}

#[test]
fn run_startup_void_single_param() {
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(0));
    let mut world = wb.build();
    world.run_startup(void_write_u64);
    assert_eq!(**world.resource::<ResU64>(), 42);
}

#[test]
fn run_startup_void_two_params() {
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(100));
    wb.register(ResString(String::new()));
    let mut world = wb.build();
    world.run_startup(void_read_and_write);
    assert_eq!(world.resource::<ResString>().as_str(), "value=100");
}

#[test]
fn run_startup_void_three_params() {
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(42));
    wb.register(ResBool(false));
    wb.register(ResString(String::new()));
    let mut world = wb.build();
    world.run_startup(void_three_params);
    assert!(**world.resource::<ResBool>());
    assert_eq!(world.resource::<ResString>().as_str(), "big");
}

#[test]
fn run_startup_phased() {
    fn phase1(mut v: ResMut<ResU64>) {
        **v += 10;
    }
    fn phase2(mut v: ResMut<ResU64>) {
        **v += 5;
    }
    fn phase3(val: Res<ResU64>, mut out: ResMut<ResString>) {
        **out = format!("total={}", **val);
    }

    let mut wb = WorldBuilder::new();
    wb.register(ResU64(0));
    wb.register(ResString(String::new()));
    let mut world = wb.build();
    world.run_startup(phase1);
    world.run_startup(phase2);
    world.run_startup(phase3);
    assert_eq!(**world.resource::<ResU64>(), 15);
    assert_eq!(world.resource::<ResString>().as_str(), "total=15");
}

#[test]
fn run_startup_with_local() {
    // Local should work but state is discarded after startup runs.
    fn init(mut count: Local<u64>, mut out: ResMut<ResU64>) {
        *count += 1;
        **out = *count;
    }
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(0));
    let mut world = wb.build();
    world.run_startup(init);
    assert_eq!(**world.resource::<ResU64>(), 1);
}

#[test]
fn run_startup_with_optional_present() {
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(99));
    wb.register(ResString(String::new()));
    let mut world = wb.build();
    world.run_startup(void_with_optional);
    assert_eq!(world.resource::<ResString>().as_str(), "found=99");
}

#[test]
fn run_startup_with_optional_missing() {
    let mut wb = WorldBuilder::new();
    wb.register(ResString(String::new()));
    let mut world = wb.build();
    world.run_startup(void_with_optional);
    assert_eq!(world.resource::<ResString>().as_str(), "missing");
}

#[test]
fn run_startup_with_shutdown() {
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let handle = world.shutdown_handle();
    world.run_startup(void_with_shutdown);
    assert!(handle.is_shutdown());
}

#[test]
fn run_startup_bool_returning_also_works() {
    fn init_bool(mut v: ResMut<ResU64>) -> bool {
        **v = 123;
        true
    }
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(0));
    let mut world = wb.build();
    world.run_startup(init_bool);
    assert_eq!(**world.resource::<ResU64>(), 123);
}

// =========================================================================
// Resolved — comprehensive coverage
// =========================================================================

// -- All param types --

#[test]
fn resolved_res_param() {
    fn read_val(val: Res<ResU32>, mut out: ResMut<ResU64>) {
        **out = **val as u64;
    }
    let mut wb = WorldBuilder::new();
    wb.register(ResU32(42));
    wb.register(ResU64(0));
    let mut world = wb.build();
    let mut h = nexus_rt::no_event(read_val)
        .into_handler(world.registry())
        .into_handler(world.registry());
    h.run(&mut world, ());
    assert_eq!(**world.resource::<ResU64>(), 42);
}

#[test]
fn resolved_seq_param() {
    fn use_seq(_s: Seq, mut out: ResMut<ResU64>, e: u64) {
        **out = e;
    }
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(0));
    let mut world = wb.build();
    let mut h = use_seq
        .into_handler(world.registry())
        .into_handler(world.registry());
    h.run(&mut world, 77);
    assert_eq!(**world.resource::<ResU64>(), 77);
}

#[test]
fn resolved_seq_mut_param() {
    fn use_seq(_s: SeqMut<'_>, mut out: ResMut<ResU64>, e: u64) {
        **out = e;
    }
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(0));
    let mut world = wb.build();
    let mut h = use_seq
        .into_handler(world.registry())
        .into_handler(world.registry());
    h.run(&mut world, 99);
    assert_eq!(**world.resource::<ResU64>(), 99);
}

#[test]
fn resolved_optional_res() {
    fn maybe(v: Option<Res<ResU32>>, mut out: ResMut<ResU64>) {
        if let Some(v) = v {
            **out = **v as u64;
        }
    }
    let mut wb = WorldBuilder::new();
    wb.register(ResU32(55));
    wb.register(ResU64(0));
    let mut world = wb.build();
    let mut h = nexus_rt::no_event(maybe)
        .into_handler(world.registry())
        .into_handler(world.registry());
    h.run(&mut world, ());
    assert_eq!(**world.resource::<ResU64>(), 55);
}

#[test]
fn resolved_optional_resmut() {
    fn maybe(mut v: Option<ResMut<ResU64>>, e: u64) {
        if let Some(ref mut v) = v {
            ***v = e;
        }
    }
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(0));
    let mut world = wb.build();
    let mut h = maybe
        .into_handler(world.registry())
        .into_handler(world.registry());
    h.run(&mut world, 88);
    assert_eq!(**world.resource::<ResU64>(), 88);
}

#[test]
fn resolved_local_preserves_state() {
    fn counter(mut l: Local<u64>, mut out: ResMut<ResU64>) {
        *l += 1;
        **out = *l;
    }
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(0));
    let mut world = wb.build();
    let mut h = nexus_rt::no_event(counter)
        .into_handler(world.registry())
        .into_handler(world.registry());
    h.run(&mut world, ());
    h.run(&mut world, ());
    h.run(&mut world, ());
    assert_eq!(**world.resource::<ResU64>(), 3);
}

// -- Borrowed / zero-copy event types --

#[test]
fn resolved_slice_event() {
    fn handle(mut out: ResMut<ResU64>, e: &[u8]) {
        **out = e.len() as u64;
    }
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(0));
    let mut world = wb.build();
    let mut h = handle
        .into_handler(world.registry())
        .into_handler(world.registry());
    h.run(&mut world, &[1u8, 2, 3, 4, 5][..]);
    assert_eq!(**world.resource::<ResU64>(), 5);
}

#[test]
fn resolved_str_event() {
    fn handle(mut out: ResMut<ResU64>, e: &str) {
        **out = e.len() as u64;
    }
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(0));
    let mut world = wb.build();
    let mut h = handle
        .into_handler(world.registry())
        .into_handler(world.registry());
    h.run(&mut world, "hello");
    assert_eq!(**world.resource::<ResU64>(), 5);
}

#[test]
fn resolved_borrowed_struct_event() {
    #[derive(Debug)]
    struct Message<'a> {
        payload: &'a [u8],
        seq: u64,
    }
    fn handle(mut out: ResMut<ResU64>, m: Message<'_>) {
        **out = m.seq + m.payload.len() as u64;
    }
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(0));
    let mut world = wb.build();
    let mut h = handle
        .into_handler(world.registry())
        .into_handler(world.registry());
    let data = [1u8, 2, 3];
    h.run(
        &mut world,
        Message {
            payload: &data,
            seq: 100,
        },
    );
    assert_eq!(**world.resource::<ResU64>(), 103);
}

#[test]
fn resolved_ref_struct_event() {
    fn handle(mut out: ResMut<ResU64>, o: &Order) {
        **out = o.id;
    }
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(0));
    let mut world = wb.build();
    let mut h = handle
        .into_handler(world.registry())
        .into_handler(world.registry());
    h.run(
        &mut world,
        &Order {
            id: 42,
            price: 100.0,
            size: 10,
        },
    );
    assert_eq!(**world.resource::<ResU64>(), 42);
}

// -- All Handler producers --

#[test]
fn resolved_pipeline() {
    fn double(x: u64) -> u64 {
        x * 2
    }
    fn sink(mut out: ResMut<ResU64>, e: u64) {
        **out = e;
    }
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(0));
    let mut world = wb.build();
    let r = world.registry();
    let s = sink.into_handler(r);
    let p = PipelineBuilder::<u64>::new()
        .then(double, r)
        .dispatch(s)
        .build();
    let mut h = p.into_handler(r);
    // r borrow ends here — world can be mutably borrowed below
    h.run(&mut world, 5);
    assert_eq!(**world.resource::<ResU64>(), 10);
}

#[test]
fn resolved_dag() {
    fn root(x: u32) -> u64 {
        x as u64 * 10
    }
    fn sink(mut out: ResMut<ResU64>, e: u64) {
        **out = e;
    }
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(0));
    let mut world = wb.build();
    let r = world.registry();
    let s = sink.into_handler(r);
    let d = DagBuilder::<u32>::new().root(root, r).dispatch(s).build();
    let mut h = d.into_handler(r);
    // r borrow ends here
    h.run(&mut world, 3);
    assert_eq!(**world.resource::<ResU64>(), 30);
}

#[test]
fn resolved_callback() {
    use nexus_rt::IntoCallback;
    struct Acc {
        total: u64,
    }
    fn acc(ctx: &mut Acc, mut out: ResMut<ResU64>, e: u64) {
        ctx.total += e;
        **out = ctx.total;
    }
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(0));
    let mut world = wb.build();
    let r = world.registry();
    let cb = acc.into_callback(Acc { total: 0 }, r);
    let mut h = cb.into_handler(r);
    // r borrow ends here
    h.run(&mut world, 10);
    h.run(&mut world, 20);
    assert_eq!(**world.resource::<ResU64>(), 30);
}

#[test]
fn resolved_opaque() {
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(0));
    let mut world = wb.build();
    let f = |world: &mut World, e: u64| {
        **world.resource_mut::<ResU64>() = e;
    };
    let mut h = f
        .into_handler(world.registry())
        .into_handler(world.registry());
    h.run(&mut world, 42);
    assert_eq!(**world.resource::<ResU64>(), 42);
}

#[test]
fn resolved_resmut_param() {
    fn add_one(mut out: ResMut<ResU64>, x: u64) {
        **out = x + 1;
    }
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(0));
    let mut world = wb.build();
    let mut h = add_one
        .into_handler(world.registry())
        .into_handler(world.registry());
    h.run(&mut world, 10);
    assert_eq!(**world.resource::<ResU64>(), 11);
}

#[test]
fn resolved_arity_zero() {
    fn event_only(e: u64) {
        assert!(e > 0);
    }
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut h = event_only
        .into_handler(world.registry())
        .into_handler(world.registry());
    h.run(&mut world, 42);
}

// -- Kitchen sink --

#[test]
fn resolved_all_params_borrowed_event() {
    fn everything(
        val: Res<ResU32>,
        mut out: ResMut<ResU64>,
        mut ctr: Local<u64>,
        _s: Seq,
        e: &[u8],
    ) {
        *ctr += 1;
        **out = **val as u64 + e.len() as u64 + *ctr;
    }
    let mut wb = WorldBuilder::new();
    wb.register(ResU32(100));
    wb.register(ResU64(0));
    let mut world = wb.build();
    let mut h = everything
        .into_handler(world.registry())
        .into_handler(world.registry());
    h.run(&mut world, &[1u8, 2, 3][..]);
    assert_eq!(**world.resource::<ResU64>(), 104);
}

// -- Driver-style acceptance (the actual use case) --

#[test]
fn resolved_install_handler_pattern() {
    fn install_handler<E: 'static, P>(
        h: impl IntoHandler<E, P>,
        registry: &Registry,
    ) -> Virtual<E> {
        Box::new(h.into_handler(registry))
    }

    // Named function through install_handler
    fn tick(mut out: ResMut<ResU64>, e: u64) {
        **out = e;
    }
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(0));
    let mut world = wb.build();
    let r = world.registry();
    let mut h = install_handler(tick, r);
    // r borrow ends here
    h.run(&mut world, 42);
    assert_eq!(**world.resource::<ResU64>(), 42);
}

#[test]
fn resolved_box_passthrough() {
    fn tick(mut out: ResMut<ResU64>, e: u64) {
        **out = e;
    }
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(0));
    let mut world = wb.build();
    let r = world.registry();
    let handler = tick.into_handler(r);
    let boxed: Virtual<u64> = Box::new(handler);
    // Box<dyn Handler<E>> through Resolved blanket
    let mut h = boxed.into_handler(r);
    // r borrow ends here
    h.run(&mut world, 99);
    assert_eq!(**world.resource::<ResU64>(), 99);
}

// =========================================================================
// HRTB tests — for<'a> Handler<Msg<'a>> through register pattern
// =========================================================================

#[derive(Debug)]
struct Msg<'a> {
    payload: &'a [u8],
    seq: u64,
}

/// Simulates the zero copy driver register pattern:
/// - IntoHandler resolves at 'static for type inference
/// - Output handler must work at ANY lifetime (driver manufactures events)
fn register_handler<F, P>(handler: F, registry: &Registry) -> Box<dyn for<'a> Handler<Msg<'a>>>
where
    F: IntoHandler<Msg<'static>, P>,
    F::Handler: for<'a> Handler<Msg<'a>>,
{
    Box::new(handler.into_handler(registry))
}

#[test]
fn hrtb_named_function() {
    fn on_msg(mut counter: ResMut<ResU64>, msg: Msg<'_>) {
        **counter += msg.seq;
    }
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(0));
    let mut world = wb.build();
    let mut h = register_handler(on_msg, world.registry());
    let data = [1u8, 2, 3];
    h.run(
        &mut world,
        Msg {
            payload: &data,
            seq: 42,
        },
    );
    assert_eq!(**world.resource::<ResU64>(), 42);
}

#[test]
fn hrtb_pipeline() {
    fn double_seq(msg: Msg<'_>) -> Msg<'_> {
        Msg {
            payload: msg.payload,
            seq: msg.seq * 2,
        }
    }
    fn sink(mut out: ResMut<ResU64>, msg: Msg<'_>) {
        **out = msg.seq;
    }
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(0));
    let mut world = wb.build();
    let r = world.registry();
    let pipeline = PipelineBuilder::<Msg<'static>>::new()
        .then(double_seq, r)
        .dispatch(sink.into_handler(r))
        .build();
    let mut h = register_handler(pipeline, r);
    // r borrow ends here
    h.run(
        &mut world,
        Msg {
            payload: &[1, 2, 3],
            seq: 5,
        },
    );
    assert_eq!(**world.resource::<ResU64>(), 10);
}

#[test]
fn hrtb_dag() {
    fn root(msg: Msg<'_>) -> u64 {
        msg.seq * 10
    }
    fn sink(mut out: ResMut<ResU64>, e: u64) {
        **out = e;
    }
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(0));
    let mut world = wb.build();
    let r = world.registry();
    let s = sink.into_handler(r);
    let dag = DagBuilder::<Msg<'static>>::new()
        .root(root, r)
        .dispatch(s)
        .build();
    let mut h = register_handler(dag, r);
    // r borrow ends here
    h.run(
        &mut world,
        Msg {
            payload: &[1],
            seq: 3,
        },
    );
    assert_eq!(**world.resource::<ResU64>(), 30);
}

#[test]
fn hrtb_callback() {
    use nexus_rt::IntoCallback;
    struct Logger {
        count: u64,
    }
    fn log_msg(ctx: &mut Logger, mut out: ResMut<ResU64>, msg: Msg<'_>) {
        ctx.count += 1;
        **out = msg.seq + ctx.count;
    }
    let mut wb = WorldBuilder::new();
    wb.register(ResU64(0));
    let mut world = wb.build();
    let r = world.registry();
    let cb = log_msg.into_callback(Logger { count: 0 }, r);
    let mut h = register_handler(cb, r);
    // r borrow ends here
    h.run(
        &mut world,
        Msg {
            payload: &[],
            seq: 10,
        },
    );
    assert_eq!(**world.resource::<ResU64>(), 11);
    h.run(
        &mut world,
        Msg {
            payload: &[],
            seq: 20,
        },
    );
    assert_eq!(**world.resource::<ResU64>(), 22);
}

// NOTE: Box<dyn for<'a> Handler<Msg<'a>>> does NOT satisfy
// IntoHandler<Msg<'static>, Resolved>.
//
// The delegating impl is `impl<E> Handler<E> for Box<dyn Handler<E>>`,
// which gives `Handler<Msg<'static>> for Box<dyn Handler<Msg<'static>>>`.
// But `Box<dyn for<'a> Handler<Msg<'a>>>` is a distinct type — Rust
// doesn't coerce higher-ranked trait objects to monomorphic ones.
//
// In practice this isn't a problem: you don't re-register an already-boxed
// handler. If you need to pass a boxed handler, use it directly rather
// than going through IntoHandler again.

// =========================================================================
// Send bounds — slab-backed resources must be Send for World storage
// =========================================================================

/// All types registered as World resources must satisfy Resource (Send + 'static).
/// These compile tests catch regressions where internal raw pointers or
/// UnsafeCell fields break the auto-Send derivation.
#[cfg(feature = "timer")]
#[test]
fn timer_wheel_satisfies_resource_bound() {
    fn assert_resource<T: nexus_rt::Resource>() {}

    // TimerWheel contains WheelEntry with raw DLL pointers.
    // Without WheelEntry's unsafe Send impl, this fails to compile.
    assert_resource::<nexus_timer::TimerWheel<Box<dyn Handler<std::time::Instant>>>>();
}

#[cfg(feature = "timer")]
#[test]
fn clock_satisfies_resource_bound() {
    fn assert_resource<T: nexus_rt::Resource>() {}
    assert_resource::<nexus_rt::clock::Clock>();
}

#[cfg(feature = "mio")]
#[test]
fn mio_driver_satisfies_resource_bound() {
    fn assert_resource<T: nexus_rt::Resource>() {}

    // MioDriver uses external slab crate (not nexus-slab), which is Send when S: Send.
    assert_resource::<nexus_rt::mio::MioDriver<Box<dyn Handler<::mio::event::Event>>>>();
}

// =============================================================================
// #[derive(View)] tests
// =============================================================================

mod view_derive {
    use nexus_rt::{PipelineBuilder, Res, ResMut, Resource, View, WorldBuilder};

    #[derive(Resource)]
    struct AuditLog(Vec<String>);

    #[derive(Resource)]
    struct RiskLimits {
        max_qty: u64,
    }

    // -- Event types --

    struct NewOrderCommand {
        source: String,
        symbol: String,
        qty: u64,
        price: f64,
    }

    #[allow(dead_code)]
    struct AmendOrderCommand {
        order_id: u64,
        symbol: String,
        qty: u64,
        price: f64,
    }

    // -- Derived view with borrowed + copy fields --

    #[allow(dead_code)]
    #[derive(View)]
    #[source(NewOrderCommand)]
    #[source(AmendOrderCommand)]
    struct OrderView<'a> {
        #[borrow]
        symbol: &'a str,
        qty: u64,
        price: f64,
    }

    // -- Derived view without lifetime (all Copy) --

    #[derive(View)]
    #[source(NewOrderCommand)]
    struct RiskView {
        qty: u64,
        price: f64,
    }

    // -- Reusable steps --

    fn log_order(mut log: ResMut<AuditLog>, v: &OrderView) {
        log.0.push(format!("{} qty={}", v.symbol, v.qty));
    }

    fn check_risk(limits: Res<RiskLimits>, v: &OrderView) -> bool {
        v.qty <= limits.max_qty
    }

    #[test]
    fn derive_basic_tap() {
        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        let mut world = wb.build();
        let reg = world.registry();

        let mut p = PipelineBuilder::<NewOrderCommand>::new()
            .view::<AsOrderView>()
            .tap(log_order, reg)
            .end_view()
            .then(|_: NewOrderCommand| {}, reg);

        p.run(
            &mut world,
            NewOrderCommand {
                source: "test".into(),
                symbol: "BTC".into(),
                qty: 50,
                price: 42000.0,
            },
        );

        assert_eq!(world.resource::<AuditLog>().0, vec!["BTC qty=50"]);
    }

    #[test]
    fn derive_guard_rejects() {
        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        wb.register(RiskLimits { max_qty: 100 });
        let mut world = wb.build();
        let reg = world.registry();

        let mut p = PipelineBuilder::<NewOrderCommand>::new()
            .view::<AsOrderView>()
            .tap(log_order, reg)
            .guard(check_risk, reg)
            .end_view_guarded();

        let result = p.run(
            &mut world,
            NewOrderCommand {
                source: "a".into(),
                symbol: "BTC".into(),
                qty: 50,
                price: 42000.0,
            },
        );
        assert!(result.is_some());

        let result = p.run(
            &mut world,
            NewOrderCommand {
                source: "b".into(),
                symbol: "ETH".into(),
                qty: 200,
                price: 3000.0,
            },
        );
        assert!(result.is_none());
    }

    #[test]
    fn derive_reusable_across_sources() {
        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        let mut world = wb.build();
        let reg = world.registry();

        let mut p_new = PipelineBuilder::<NewOrderCommand>::new()
            .view::<AsOrderView>()
            .tap(log_order, reg)
            .end_view()
            .then(|_: NewOrderCommand| {}, reg);

        let mut p_amend = PipelineBuilder::<AmendOrderCommand>::new()
            .view::<AsOrderView>()
            .tap(log_order, reg)
            .end_view()
            .then(|_: AmendOrderCommand| {}, reg);

        p_new.run(
            &mut world,
            NewOrderCommand {
                source: "a".into(),
                symbol: "BTC".into(),
                qty: 50,
                price: 42000.0,
            },
        );
        p_amend.run(
            &mut world,
            AmendOrderCommand {
                order_id: 123,
                symbol: "ETH".into(),
                qty: 25,
                price: 3000.0,
            },
        );

        let log = &world.resource::<AuditLog>().0;
        assert_eq!(log[0], "BTC qty=50");
        assert_eq!(log[1], "ETH qty=25");
    }

    #[test]
    fn derive_no_lifetime_view() {
        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        let mut world = wb.build();
        let reg = world.registry();

        fn log_risk(mut log: ResMut<AuditLog>, v: &RiskView) {
            log.0.push(format!("risk: qty={} price={}", v.qty, v.price));
        }

        let mut p = PipelineBuilder::<NewOrderCommand>::new()
            .view::<AsRiskView>()
            .tap(log_risk, reg)
            .end_view()
            .then(|_: NewOrderCommand| {}, reg);

        p.run(
            &mut world,
            NewOrderCommand {
                source: "a".into(),
                symbol: "BTC".into(),
                qty: 50,
                price: 42000.0,
            },
        );

        assert_eq!(
            world.resource::<AuditLog>().0,
            vec!["risk: qty=50 price=42000"]
        );
    }

    // -- Field remapping --

    struct ExternalOrder {
        ticker: String,
        quantity: u64,
        px: f64,
    }

    #[derive(View)]
    #[source(ExternalOrder)]
    struct RemappedView<'a> {
        #[borrow]
        #[source(ExternalOrder, from = "ticker")]
        symbol: &'a str,

        #[source(ExternalOrder, from = "quantity")]
        qty: u64,

        #[source(ExternalOrder, from = "px")]
        price: f64,
    }

    // -- Mixed remap: one source matches by name, another remapped --

    struct InternalOrder {
        symbol: String,
        qty: u64,
        price: f64,
    }

    #[derive(View)]
    #[allow(dead_code)]
    #[source(InternalOrder)]
    #[source(ExternalOrder)]
    struct UnifiedView<'a> {
        #[borrow]
        #[source(ExternalOrder, from = "ticker")]
        symbol: &'a str,

        #[source(ExternalOrder, from = "quantity")]
        qty: u64,

        #[source(ExternalOrder, from = "px")]
        price: f64,
    }

    #[test]
    fn derive_mixed_remap_and_match() {
        // InternalOrder: fields match by name
        // ExternalOrder: all fields remapped
        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        let mut world = wb.build();
        let reg = world.registry();

        fn log_unified(mut log: ResMut<AuditLog>, v: &UnifiedView) {
            log.0.push(format!("{} qty={}", v.symbol, v.qty));
        }

        let mut p_internal = PipelineBuilder::<InternalOrder>::new()
            .view::<AsUnifiedView>()
            .tap(log_unified, reg)
            .end_view()
            .then(|_: InternalOrder| {}, reg);

        let mut p_external = PipelineBuilder::<ExternalOrder>::new()
            .view::<AsUnifiedView>()
            .tap(log_unified, reg)
            .end_view()
            .then(|_: ExternalOrder| {}, reg);

        p_internal.run(
            &mut world,
            InternalOrder {
                symbol: "BTC".into(),
                qty: 50,
                price: 42000.0,
            },
        );
        p_external.run(
            &mut world,
            ExternalOrder {
                ticker: "ETH".into(),
                quantity: 25,
                px: 3000.0,
            },
        );

        let log = &world.resource::<AuditLog>().0;
        assert_eq!(log[0], "BTC qty=50");
        assert_eq!(log[1], "ETH qty=25");
    }

    // -- Borrow on Copy type --

    #[derive(Clone, Copy)]
    struct SymbolId(u64);

    struct TypedOrder {
        symbol_id: SymbolId,
        qty: u64,
    }

    #[derive(View)]
    #[source(TypedOrder)]
    struct BorrowCopyView<'a> {
        #[borrow]
        symbol_id: &'a SymbolId,
        qty: u64,
    }

    #[test]
    fn derive_borrow_copy_type() {
        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        let mut world = wb.build();
        let reg = world.registry();

        fn log_id(mut log: ResMut<AuditLog>, v: &BorrowCopyView) {
            log.0.push(format!("id={} qty={}", v.symbol_id.0, v.qty));
        }

        let mut p = PipelineBuilder::<TypedOrder>::new()
            .view::<AsBorrowCopyView>()
            .tap(log_id, reg)
            .end_view()
            .then(|_: TypedOrder| {}, reg);

        p.run(
            &mut world,
            TypedOrder {
                symbol_id: SymbolId(42),
                qty: 100,
            },
        );
        assert_eq!(world.resource::<AuditLog>().0, vec!["id=42 qty=100"]);
    }

    // -- Multiple views from same event --

    #[derive(View)]
    #[source(NewOrderCommand)]
    struct SourceView<'a> {
        #[borrow]
        source: &'a str,
    }

    #[test]
    fn derive_multiple_views_same_event() {
        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        let mut world = wb.build();
        let reg = world.registry();

        fn log_source(mut log: ResMut<AuditLog>, v: &SourceView) {
            log.0.push(format!("from: {}", v.source));
        }

        // Use OrderView first, then SourceView — two different derived views
        let mut p = PipelineBuilder::<NewOrderCommand>::new()
            .view::<AsOrderView>()
            .tap(log_order, reg)
            .end_view()
            .view::<AsSourceView>()
            .tap(log_source, reg)
            .end_view()
            .then(|_: NewOrderCommand| {}, reg);

        p.run(
            &mut world,
            NewOrderCommand {
                source: "ops".into(),
                symbol: "BTC".into(),
                qty: 50,
                price: 42000.0,
            },
        );

        let log = &world.resource::<AuditLog>().0;
        assert_eq!(log[0], "BTC qty=50");
        assert_eq!(log[1], "from: ops");
    }

    // -- DAG with derived view --

    #[test]
    fn derive_dag_integration() {
        use nexus_rt::{DagBuilder, Handler};

        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        let mut world = wb.build();
        let reg = world.registry();

        let dag = DagBuilder::<NewOrderCommand>::new()
            .root(|cmd: NewOrderCommand| cmd, reg)
            .view::<AsOrderView>()
            .tap(log_order, reg)
            .end_view_dag()
            .then(|_: &NewOrderCommand| {}, reg);

        let mut handler = dag.build();
        handler.run(
            &mut world,
            NewOrderCommand {
                source: "test".into(),
                symbol: "SOL".into(),
                qty: 10,
                price: 150.0,
            },
        );

        assert_eq!(world.resource::<AuditLog>().0, vec!["SOL qty=10"]);
    }

    #[test]
    fn derive_field_remap() {
        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        let mut world = wb.build();
        let reg = world.registry();

        fn log_remapped(mut log: ResMut<AuditLog>, v: &RemappedView) {
            log.0
                .push(format!("{} qty={} @{}", v.symbol, v.qty, v.price));
        }

        let mut p = PipelineBuilder::<ExternalOrder>::new()
            .view::<AsRemappedView>()
            .tap(log_remapped, reg)
            .end_view()
            .then(|_: ExternalOrder| {}, reg);

        p.run(
            &mut world,
            ExternalOrder {
                ticker: "SOL-USD".into(),
                quantity: 100,
                px: 150.0,
            },
        );

        assert_eq!(world.resource::<AuditLog>().0, vec!["SOL-USD qty=100 @150"]);
    }

    // -- Generic views --

    struct TypedEvent<T> {
        name: String,
        value: T,
    }

    #[derive(View)]
    #[source(TypedEvent<T>)]
    struct TypedView<'a, T: Copy> {
        #[borrow]
        name: &'a str,
        value: T,
    }

    #[test]
    fn derive_type_param_view() {
        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        let mut world = wb.build();
        let reg = world.registry();

        fn log_typed(mut log: ResMut<AuditLog>, v: &TypedView<u64>) {
            log.0.push(format!("{} val={}", v.name, v.value));
        }

        let mut p = PipelineBuilder::<TypedEvent<u64>>::new()
            .view::<AsTypedView<u64>>()
            .tap(log_typed, reg)
            .end_view()
            .then(|_: TypedEvent<u64>| {}, reg);

        p.run(
            &mut world,
            TypedEvent {
                name: "test".into(),
                value: 42u64,
            },
        );

        assert_eq!(world.resource::<AuditLog>().0, vec!["test val=42"]);
    }

    struct SizedBuffer<const N: usize> {
        data: [u8; N],
        len: usize,
    }

    #[derive(View)]
    #[source(SizedBuffer<N>)]
    struct SizedView<'a, const N: usize> {
        #[borrow]
        data: &'a [u8; N],
        len: usize,
    }

    #[test]
    fn derive_const_param_view() {
        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        let mut world = wb.build();
        let reg = world.registry();

        fn log_sized(mut log: ResMut<AuditLog>, v: &SizedView<4>) {
            log.0.push(format!("data={:?} len={}", v.data, v.len));
        }

        let mut p = PipelineBuilder::<SizedBuffer<4>>::new()
            .view::<AsSizedView<4>>()
            .tap(log_sized, reg)
            .end_view()
            .then(|_: SizedBuffer<4>| {}, reg);

        p.run(
            &mut world,
            SizedBuffer {
                data: [1, 2, 3, 4],
                len: 4,
            },
        );

        assert_eq!(
            world.resource::<AuditLog>().0,
            vec!["data=[1, 2, 3, 4] len=4"]
        );
    }

    struct CopyEvent<T: Copy> {
        x: T,
        y: T,
    }

    #[derive(View)]
    #[source(CopyEvent<T>)]
    struct CopyView<T: Copy> {
        x: T,
        y: T,
    }

    #[test]
    fn derive_no_lifetime_generic_view() {
        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        let mut world = wb.build();
        let reg = world.registry();

        fn log_copy(mut log: ResMut<AuditLog>, v: &CopyView<f64>) {
            log.0.push(format!("x={} y={}", v.x, v.y));
        }

        let mut p = PipelineBuilder::<CopyEvent<f64>>::new()
            .view::<AsCopyView<f64>>()
            .tap(log_copy, reg)
            .end_view()
            .then(|_: CopyEvent<f64>| {}, reg);

        p.run(&mut world, CopyEvent { x: 1.5, y: 2.5 });

        assert_eq!(world.resource::<AuditLog>().0, vec!["x=1.5 y=2.5"]);
    }

    struct PairEvent<K, V> {
        key: K,
        value: V,
    }

    #[derive(View)]
    #[source(PairEvent<K, V>)]
    struct PairView<K: Copy, V: Copy> {
        key: K,
        value: V,
    }

    #[test]
    fn derive_multi_type_param_view() {
        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        let mut world = wb.build();
        let reg = world.registry();

        fn log_pair(mut log: ResMut<AuditLog>, v: &PairView<u32, i64>) {
            log.0.push(format!("key={} val={}", v.key, v.value));
        }

        let mut p = PipelineBuilder::<PairEvent<u32, i64>>::new()
            .view::<AsPairView<u32, i64>>()
            .tap(log_pair, reg)
            .end_view()
            .then(|_: PairEvent<u32, i64>| {}, reg);

        p.run(
            &mut world,
            PairEvent {
                key: 7u32,
                value: -99i64,
            },
        );

        assert_eq!(world.resource::<AuditLog>().0, vec!["key=7 val=-99"]);
    }

    struct DisplayEvent<T: std::fmt::Display> {
        item: T,
    }

    #[derive(View)]
    #[source(DisplayEvent<T>)]
    struct DisplayView<T: std::fmt::Display + Copy> {
        item: T,
    }

    #[test]
    fn derive_bounded_type_param_view() {
        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        let mut world = wb.build();
        let reg = world.registry();

        fn log_display(mut log: ResMut<AuditLog>, v: &DisplayView<i32>) {
            log.0.push(format!("item={}", v.item));
        }

        let mut p = PipelineBuilder::<DisplayEvent<i32>>::new()
            .view::<AsDisplayView<i32>>()
            .tap(log_display, reg)
            .end_view()
            .then(|_: DisplayEvent<i32>| {}, reg);

        p.run(&mut world, DisplayEvent { item: 42 });

        assert_eq!(world.resource::<AuditLog>().0, vec!["item=42"]);
    }

    #[test]
    fn derive_generic_view_pipeline_integration() {
        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        let mut world = wb.build();
        let reg = world.registry();

        fn check_typed(v: &TypedView<u64>) -> bool {
            v.value > 0
        }

        fn log_typed_tap(mut log: ResMut<AuditLog>, v: &TypedView<u64>) {
            log.0.push(format!("passed: {} val={}", v.name, v.value));
        }

        let mut p = PipelineBuilder::<TypedEvent<u64>>::new()
            .view::<AsTypedView<u64>>()
            .guard(check_typed, reg)
            .tap(log_typed_tap, reg)
            .end_view_guarded();

        let result = p.run(
            &mut world,
            TypedEvent {
                name: "good".into(),
                value: 10,
            },
        );
        assert!(result.is_some());

        let result = p.run(
            &mut world,
            TypedEvent {
                name: "bad".into(),
                value: 0,
            },
        );
        assert!(result.is_none());

        assert_eq!(world.resource::<AuditLog>().0, vec!["passed: good val=10"]);
    }

    // Lifetime bound on type param — T: 'a gets stripped from marker struct,
    // 'static is auto-inserted on the impl.
    struct LifetimeBoundEvent<T: 'static> {
        value: T,
    }

    #[derive(View)]
    #[source(LifetimeBoundEvent<T>)]
    struct LifetimeBoundView<'a, T: 'a + Copy> {
        #[borrow]
        value: &'a T,
    }

    #[test]
    fn derive_lifetime_bound_type_param() {
        let mut wb = WorldBuilder::new();
        wb.register(AuditLog(Vec::new()));
        let mut world = wb.build();
        let reg = world.registry();

        fn log_lb(mut log: ResMut<AuditLog>, v: &LifetimeBoundView<u64>) {
            log.0.push(format!("val={}", v.value));
        }

        let mut p = PipelineBuilder::<LifetimeBoundEvent<u64>>::new()
            .view::<AsLifetimeBoundView<u64>>()
            .tap(log_lb, reg)
            .end_view()
            .then(|_: LifetimeBoundEvent<u64>| {}, reg);

        p.run(&mut world, LifetimeBoundEvent { value: 77u64 });

        assert_eq!(world.resource::<AuditLog>().0, vec!["val=77"]);
    }
}

// =========================================================================
// Context-aware pipeline + DAG — compile-time + runtime integration tests
// =========================================================================

mod ctx_pipelines {
    use nexus_rt::{CtxDagBuilder, CtxPipelineBuilder, Res, ResMut, WorldBuilder};

    nexus_rt::new_resource!(
        #[derive(Debug, PartialEq)]
        Val(u64)
    );

    nexus_rt::new_resource!(
        #[derive(Debug, PartialEq)]
        Out(u64)
    );

    struct MyCtx {
        count: u32,
        multiplier: u64,
    }

    // -- Pipeline step functions (compile check) ------------------------------

    fn read_val(ctx: &mut MyCtx, val: Res<Val>, _input: ()) -> u64 {
        ctx.count += 1;
        val.0 * ctx.multiplier
    }

    fn double(_ctx: &mut MyCtx, x: u64) -> u64 {
        x * 2
    }

    fn write_out(_ctx: &mut MyCtx, mut out: ResMut<Out>, val: u64) {
        out.0 = val;
    }

    fn check_positive(_ctx: &mut MyCtx, val: &u64) -> bool {
        *val > 0
    }

    fn log_val(ctx: &mut MyCtx, val: &u64) {
        ctx.count += *val as u32;
    }

    // -- Pipeline: then + guard + map + tap -----------------------------------

    #[test]
    fn ctx_pipeline_three_stage() {
        let mut wb = WorldBuilder::new();
        wb.register(Val(10));
        wb.register(Out(0));
        let mut world = wb.build();
        let reg = world.registry();

        let mut pipeline = CtxPipelineBuilder::<MyCtx, ()>::new()
            .then(read_val, reg)
            .then(double, reg)
            .then(write_out, reg);

        let mut ctx = MyCtx {
            count: 0,
            multiplier: 3,
        };
        pipeline.run(&mut ctx, &mut world, ());

        assert_eq!(world.resource::<Out>().0, 60); // 10 * 3 * 2
        assert_eq!(ctx.count, 1);
    }

    #[test]
    fn ctx_pipeline_guard_and_map() {
        let mut wb = WorldBuilder::new();
        wb.register(Val(10));
        let mut world = wb.build();
        let reg = world.registry();

        let mut pipeline = CtxPipelineBuilder::<MyCtx, ()>::new()
            .then(read_val, reg)
            .guard(check_positive, reg)
            .map(double, reg);

        let mut ctx = MyCtx {
            count: 0,
            multiplier: 5,
        };
        let result = pipeline.run(&mut ctx, &mut world, ());
        assert_eq!(result, Some(100)); // 10 * 5 * 2
    }

    #[test]
    fn ctx_pipeline_tap() {
        let mut wb = WorldBuilder::new();
        wb.register(Val(10));
        let mut world = wb.build();
        let reg = world.registry();

        let mut pipeline = CtxPipelineBuilder::<MyCtx, ()>::new()
            .then(read_val, reg)
            .tap(log_val, reg);

        let mut ctx = MyCtx {
            count: 0,
            multiplier: 1,
        };
        let result = pipeline.run(&mut ctx, &mut world, ());

        assert_eq!(result, 10);
        assert_eq!(ctx.count, 11); // 1 from read_val + 10 from log_val
    }

    #[test]
    fn ctx_pipeline_opaque_step() {
        let mut wb = WorldBuilder::new();
        wb.register(Val(10));
        let mut world = wb.build();
        let reg = world.registry();

        // Opaque closure gets &mut World directly
        let mut pipeline = CtxPipelineBuilder::<MyCtx, ()>::new().then(
            |ctx: &mut MyCtx, w: &mut nexus_rt::World, _input: ()| -> u64 {
                ctx.count += 1;
                w.resource::<Val>().0
            },
            reg,
        );

        let mut ctx = MyCtx {
            count: 0,
            multiplier: 0,
        };
        let result = pipeline.run(&mut ctx, &mut world, ());
        assert_eq!(result, 10);
        assert_eq!(ctx.count, 1);
    }

    // -- DAG: fork + merge ----------------------------------------------------

    #[test]
    fn ctx_dag_fork_merge() {
        let mut wb = WorldBuilder::new();
        wb.register(Val(5));
        let mut world = wb.build();
        let reg = world.registry();

        fn decode(ctx: &mut MyCtx, _input: u32) -> u64 {
            ctx.count += 1;
            42
        }

        fn arm_double(_ctx: &mut MyCtx, val: &u64) -> u64 {
            *val * 2
        }

        fn arm_add_ten(_ctx: &mut MyCtx, val: &u64) -> u64 {
            *val + 10
        }

        fn merge(ctx: &mut MyCtx, a: &u64, b: &u64) {
            ctx.multiplier = *a + *b;
        }

        let mut dag = CtxDagBuilder::<MyCtx, u32>::new()
            .root(decode, reg)
            .fork()
            .arm(|seed| seed.then(arm_double, reg))
            .arm(|seed| seed.then(arm_add_ten, reg))
            .merge(merge, reg)
            .build();

        let mut ctx = MyCtx {
            count: 0,
            multiplier: 0,
        };
        dag.run(&mut ctx, &mut world, 0);

        assert_eq!(ctx.count, 1);
        assert_eq!(ctx.multiplier, 136); // (42 * 2) + (42 + 10) = 84 + 52
    }

    // -- Pipeline builds with void return -------------------------------------

    #[test]
    fn ctx_pipeline_build_void() {
        let mut wb = WorldBuilder::new();
        wb.register(Out(0));
        let mut world = wb.build();
        let reg = world.registry();

        fn sink(ctx: &mut MyCtx, mut out: ResMut<Out>, _input: ()) {
            out.0 = ctx.multiplier;
        }

        let mut pipeline = CtxPipelineBuilder::<MyCtx, ()>::new()
            .then(sink, reg)
            .build();

        let mut ctx = MyCtx {
            count: 0,
            multiplier: 99,
        };
        pipeline.run(&mut ctx, &mut world, ());
        assert_eq!(world.resource::<Out>().0, 99);
    }

    // -- Result combinators ---------------------------------------------------

    #[test]
    fn ctx_pipeline_result_flow() {
        let wb = WorldBuilder::new();
        let mut world = wb.build();
        let reg = world.registry();

        fn parse(_ctx: &mut MyCtx, input: &str) -> Result<u64, String> {
            input
                .parse()
                .map_err(|e: std::num::ParseIntError| e.to_string())
        }

        fn double_ok(_ctx: &mut MyCtx, val: u64) -> u64 {
            val * 2
        }

        fn on_err(ctx: &mut MyCtx, _err: &String) {
            ctx.count += 1;
        }

        let mut pipeline = CtxPipelineBuilder::<MyCtx, &str>::new()
            .then(parse, reg)
            .map(double_ok, reg)
            .inspect_err(on_err, reg);

        let mut ctx = MyCtx {
            count: 0,
            multiplier: 0,
        };

        // Ok path
        let result = pipeline.run(&mut ctx, &mut world, "21");
        assert_eq!(result, Ok(42));
        assert_eq!(ctx.count, 0);

        // Err path
        let result = pipeline.run(&mut ctx, &mut world, "abc");
        assert!(result.is_err());
        assert_eq!(ctx.count, 1);
    }
}

// =========================================================================
// Reactor system — compile-time + runtime integration tests
// =========================================================================

#[cfg(feature = "reactors")]
mod reactors {
    use nexus_notify::Token;
    use nexus_rt::{
        DataSource, DeferredRemovals, IntoReactor, Reactor, ReactorNotify, ReactorSystem, Res,
        ResMut, ResourceId, SourceRegistry, World, WorldBuilder,
    };

    /// Helper: access ReactorNotify via ResourceId to avoid borrow conflicts
    /// with world.registry(). Same pattern as ReactorSystem::dispatch.
    #[allow(clippy::mut_from_ref)]
    fn notify_mut(world: &World, id: ResourceId) -> &mut ReactorNotify {
        // SAFETY: id is a ResourceId for a ReactorNotify registered in this World; no concurrent alias at this call site.
        unsafe { world.get_mut::<ReactorNotify>(id) }
    }

    nexus_rt::new_resource!(
        #[derive(Debug, PartialEq)]
        Counter(u64)
    );

    nexus_rt::new_resource!(
        #[derive(Debug, PartialEq)]
        Output(Vec<String>)
    );

    // -- Step function signatures compile correctly ---------------------------

    /// Context-only step (arity 0 — no Params).
    fn ctx_only_step(ctx: &mut SimpleCtx) {
        ctx.runs += 1;
    }

    /// One Param step.
    fn one_param_step(ctx: &mut SimpleCtx, counter: Res<Counter>) {
        ctx.runs += counter.0 as u32;
    }

    /// Two Param step with mutation.
    fn two_param_step(ctx: &mut SimpleCtx, input: Res<Counter>, mut out: ResMut<Output>) {
        out.0.push(format!("{}:{}", ctx.name, input.0));
        ctx.runs += 1;
    }

    /// Step that self-removes via DeferredRemovals.
    fn self_removing_step(
        ctx: &mut RemovableCtx,
        mut counter: ResMut<Counter>,
        mut removals: ResMut<DeferredRemovals>,
    ) {
        counter.0 += 1;
        ctx.remaining -= 1;
        if ctx.remaining == 0 {
            removals.deregister(ctx.rereactor_id);
        }
    }

    struct SimpleCtx {
        _rereactor_id: Token,
        name: &'static str,
        runs: u32,
    }

    struct RemovableCtx {
        rereactor_id: Token,
        remaining: u32,
    }

    // -- IntoReactor compiles for all arities -----------------------------------

    #[test]
    fn into_reactor_arity0_compiles() {
        let wb = WorldBuilder::new();
        let world = wb.build();
        let reg = world.registry();

        let mut reactor = ctx_only_step.into_reactor(
            SimpleCtx {
                _rereactor_id: Token::new(0),
                name: "test",
                runs: 0,
            },
            reg,
        );
        let mut world = world;
        reactor.run(&mut world);
        assert_eq!(reactor.ctx.runs, 1);
    }

    #[test]
    fn into_reactor_arity1_compiles() {
        let mut wb = WorldBuilder::new();
        wb.register(Counter(10));
        let mut world = wb.build();
        let reg = world.registry();

        let mut reactor = one_param_step.into_reactor(
            SimpleCtx {
                _rereactor_id: Token::new(0),
                name: "test",
                runs: 0,
            },
            reg,
        );
        reactor.run(&mut world);
        assert_eq!(reactor.ctx.runs, 10);
    }

    #[test]
    fn into_reactor_arity2_compiles() {
        let mut wb = WorldBuilder::new();
        wb.register(Counter(42));
        wb.register(Output(Vec::new()));
        let mut world = wb.build();
        let reg = world.registry();

        let mut reactor = two_param_step.into_reactor(
            SimpleCtx {
                _rereactor_id: Token::new(0),
                name: "MM-BTC",
                runs: 0,
            },
            reg,
        );
        reactor.run(&mut world);
        assert_eq!(world.resource::<Output>().0, vec!["MM-BTC:42"]);
    }

    // -- Full system integration: market maker pattern ------------------------

    #[test]
    fn market_maker_pattern() {
        // 3 instruments, shared positions source, per-instrument reactors
        let mut wb = WorldBuilder::new();
        wb.register(Counter(0));
        wb.register(Output(Vec::new()));
        wb.register(ReactorNotify::new(8, 16));
        wb.register(DeferredRemovals::default());
        wb.register(SourceRegistry::new());
        let mut world = wb.build();
        let nid = world.id::<ReactorNotify>();

        let mut system = ReactorSystem::new(&world);

        fn quoting(ctx: &mut SimpleCtx, mut out: ResMut<Output>) {
            out.0.push(format!("quote:{}", ctx.name));
            ctx.runs += 1;
        }

        // Register sources
        let notify = notify_mut(&world, nid);
        let btc_md = notify.register_source();
        let eth_md = notify.register_source();
        let positions = notify.register_source();

        // Map natural keys (before getting registry)
        {
            let sr = world.resource_mut::<SourceRegistry>();
            sr.insert("BTC", btc_md);
            sr.insert("ETH", eth_md);
            sr.insert("positions", positions);
        }

        // Register reactors (registry borrow starts here)
        let reg = world.registry();
        let notify = notify_mut(&world, nid);
        notify
            .register(
                |t| SimpleCtx {
                    _rereactor_id: t,
                    name: "MM-BTC",
                    runs: 0,
                },
                quoting,
                reg,
            )
            .subscribe(btc_md)
            .subscribe(positions);

        notify
            .register(
                |t| SimpleCtx {
                    _rereactor_id: t,
                    name: "MM-ETH",
                    runs: 0,
                },
                quoting,
                reg,
            )
            .subscribe(eth_md)
            .subscribe(positions);

        // Frame 1: BTC data only — only BTC rereactor wakes
        notify_mut(&world, nid).mark(btc_md);
        system.dispatch(&mut world);
        assert_eq!(world.resource::<Output>().0, vec!["quote:MM-BTC"]);

        // Frame 2: position update — both reactors wake (deduped)
        world.resource_mut::<Output>().0.clear();
        notify_mut(&world, nid).mark(positions);
        system.dispatch(&mut world);
        let output = &world.resource::<Output>().0;
        assert_eq!(output.len(), 2);
        assert!(output.contains(&"quote:MM-BTC".to_string()));
        assert!(output.contains(&"quote:MM-ETH".to_string()));

        // Frame 3: BTC + positions — BTC rereactor runs ONCE (dedup)
        world.resource_mut::<Output>().0.clear();
        let notify = notify_mut(&world, nid);
        notify.mark(btc_md);
        notify.mark(positions);
        system.dispatch(&mut world);
        let output = &world.resource::<Output>().0;
        assert_eq!(output.len(), 2); // BTC once + ETH once
    }

    // -- TWAP execution pattern -----------------------------------------------

    #[test]
    fn twap_self_removal_pattern() {
        let mut wb = WorldBuilder::new();
        wb.register(Counter(0));
        wb.register(ReactorNotify::new(4, 8));
        wb.register(DeferredRemovals::default());
        let mut world = wb.build();
        let reg = world.registry();
        let nid = world.id::<ReactorNotify>();

        let mut system = ReactorSystem::new(&world);

        let notify = notify_mut(&world, nid);
        let md_source = notify.register_source();

        // TWAP with 3 slices
        notify
            .register(
                |t| RemovableCtx {
                    rereactor_id: t,
                    remaining: 3,
                },
                self_removing_step,
                reg,
            )
            .subscribe(md_source);

        // 3 frames of market data
        for frame in 1..=4 {
            notify_mut(&world, nid).mark(md_source);
            system.dispatch(&mut world);

            if frame <= 3 {
                assert_eq!(world.resource::<Counter>().0, frame);
                assert_eq!(system.reactor_count(&world), usize::from(frame < 3));
            } else {
                // Frame 4: reactor already removed, counter stays at 3
                assert_eq!(world.resource::<Counter>().0, 3);
            }
        }
    }

    // -- Wire protocol round-trip pattern -------------------------------------

    #[test]
    fn wire_routing_with_source_registry() {
        let mut wb = WorldBuilder::new();
        wb.register(Output(Vec::new()));
        wb.register(ReactorNotify::new(8, 16));
        wb.register(DeferredRemovals::default());
        wb.register(SourceRegistry::new());
        let mut world = wb.build();
        let nid = world.id::<ReactorNotify>();

        let mut system = ReactorSystem::new(&world);

        struct FillCtx {
            rereactor_id: Token,
            instrument: &'static str,
        }

        fn on_fill(ctx: &mut FillCtx, mut out: ResMut<Output>) {
            out.0.push(format!(
                "fill:{}:{}",
                ctx.instrument,
                ctx.rereactor_id.index()
            ));
        }

        #[derive(Hash, Eq, PartialEq, Clone, Copy)]
        struct RoutingKey(usize);

        let (token_0, fill_src_0, token_1, fill_src_1) = {
            let reg = world.registry();
            let notify = notify_mut(&world, nid);

            let fill_src_0 = notify.register_source();
            let token_0 = notify
                .register(
                    |t| FillCtx {
                        rereactor_id: t,
                        instrument: "BTC",
                    },
                    on_fill,
                    reg,
                )
                .subscribe(fill_src_0)
                .token();

            let fill_src_1 = notify.register_source();
            let token_1 = notify
                .register(
                    |t| FillCtx {
                        rereactor_id: t,
                        instrument: "ETH",
                    },
                    on_fill,
                    reg,
                )
                .subscribe(fill_src_1)
                .token();

            (token_0, fill_src_0, token_1, fill_src_1)
        };

        // Map routing keys
        {
            let sr = world.resource_mut::<SourceRegistry>();
            sr.insert(RoutingKey(token_0.index()), fill_src_0);
            sr.insert(RoutingKey(token_1.index()), fill_src_1);
        }

        // Simulate fill arriving for reactor 1 — look up by wire routing key
        let routing_key = RoutingKey(token_1.index());
        let fill_source = world
            .resource::<SourceRegistry>()
            .get(&routing_key)
            .unwrap();
        notify_mut(&world, nid).mark(fill_source);
        system.dispatch(&mut world);

        assert_eq!(
            world.resource::<Output>().0,
            vec![format!("fill:ETH:{}", token_1.index())]
        );
    }

    // -- Dynamic instrument lifecycle with SourceRegistry ---------------------

    #[test]
    fn dynamic_instrument_lifecycle() {
        let mut wb = WorldBuilder::new();
        wb.register(Counter(0));
        wb.register(ReactorNotify::new(8, 16));
        wb.register(DeferredRemovals::default());
        wb.register(SourceRegistry::new());
        let mut world = wb.build();
        let nid = world.id::<ReactorNotify>();

        let mut system = ReactorSystem::new(&world);

        fn step(ctx: &mut SimpleCtx, mut counter: ResMut<Counter>) {
            counter.0 += 1;
            ctx.runs += 1;
        }

        #[derive(Hash, Eq, PartialEq, Clone, Copy)]
        struct Symbol(&'static str);

        // Admin: list BTC
        let btc_src = notify_mut(&world, nid).register_source();
        world
            .resource_mut::<SourceRegistry>()
            .insert(Symbol("BTC"), btc_src);

        {
            let reg = world.registry();
            notify_mut(&world, nid)
                .register(
                    |t| SimpleCtx {
                        _rereactor_id: t,
                        name: "BTC",
                        runs: 0,
                    },
                    step,
                    reg,
                )
                .subscribe(btc_src);
        }

        // Trade BTC
        notify_mut(&world, nid).mark(btc_src);
        system.dispatch(&mut world);
        assert_eq!(world.resource::<Counter>().0, 1);

        // Admin: list ETH (runtime)
        let eth_src = notify_mut(&world, nid).register_source();
        world
            .resource_mut::<SourceRegistry>()
            .insert(Symbol("ETH"), eth_src);

        {
            let reg = world.registry();
            notify_mut(&world, nid)
                .register(
                    |t| SimpleCtx {
                        _rereactor_id: t,
                        name: "ETH",
                        runs: 0,
                    },
                    step,
                    reg,
                )
                .subscribe(eth_src);
        }

        // Trade both
        let notify = notify_mut(&world, nid);
        notify.mark(btc_src);
        notify.mark(eth_src);
        system.dispatch(&mut world);
        assert_eq!(world.resource::<Counter>().0, 3); // 1 + 2

        // Admin: delist BTC
        let removed = world
            .resource_mut::<SourceRegistry>()
            .remove(&Symbol("BTC"))
            .unwrap();
        notify_mut(&world, nid).remove_source(removed);

        // BTC gone, ETH remains
        assert!(!world.resource::<SourceRegistry>().contains(&Symbol("BTC")));
        assert!(world.resource::<SourceRegistry>().contains(&Symbol("ETH")));

        // Only ETH fires
        notify_mut(&world, nid).mark(eth_src);
        system.dispatch(&mut world);
        assert_eq!(world.resource::<Counter>().0, 4);

        // Stale BTC mark is no-op
        notify_mut(&world, nid).mark(btc_src);
        let ran = system.dispatch(&mut world);
        assert!(!ran);
    }

    // -- register_built with impl Reactor -----------------------------------------

    #[test]
    fn register_built_impl_reactor() {
        struct ManualReactor {
            value: u64,
        }

        impl Reactor for ManualReactor {
            fn run(&mut self, world: &mut World) {
                let counter = world.resource_mut::<Counter>();
                counter.0 += self.value;
            }
        }

        let mut wb = WorldBuilder::new();
        wb.register(Counter(0));
        wb.register(ReactorNotify::new(4, 8));
        wb.register(DeferredRemovals::default());
        let mut world = wb.build();
        let nid = world.id::<ReactorNotify>();
        let mut system = ReactorSystem::new(&world);

        let notify = notify_mut(&world, nid);
        let src = notify.register_source();
        notify
            .register_built(ManualReactor { value: 42 })
            .subscribe(src);

        notify_mut(&world, nid).mark(src);
        system.dispatch(&mut world);
        assert_eq!(world.resource::<Counter>().0, 42);
    }

    // -- Heterogeneous reactors in one system -----------------------------------

    #[test]
    fn heterogeneous_reactors() {
        let mut wb = WorldBuilder::new();
        wb.register(Counter(0));
        wb.register(Output(Vec::new()));
        wb.register(ReactorNotify::new(4, 8));
        wb.register(DeferredRemovals::default());
        let mut world = wb.build();
        let reg = world.registry();
        let nid = world.id::<ReactorNotify>();
        let mut system = ReactorSystem::new(&world);

        // Type A: increments counter
        struct CtxA {
            _id: Token,
        }
        fn step_a(_ctx: &mut CtxA, mut c: ResMut<Counter>) {
            c.0 += 1;
        }

        // Type B: appends to output
        struct CtxB {
            _id: Token,
            label: &'static str,
        }
        fn step_b(ctx: &mut CtxB, mut out: ResMut<Output>) {
            out.0.push(ctx.label.to_string());
        }

        let notify = notify_mut(&world, nid);
        let src = notify.register_source();

        // Mix types in one system
        notify
            .register(|t| CtxA { _id: t }, step_a, reg)
            .subscribe(src);
        notify
            .register(
                |t| CtxB {
                    _id: t,
                    label: "hello",
                },
                step_b,
                reg,
            )
            .subscribe(src);

        notify_mut(&world, nid).mark(src);
        system.dispatch(&mut world);

        assert_eq!(world.resource::<Counter>().0, 1);
        assert_eq!(world.resource::<Output>().0, vec!["hello"]);
    }

    // -- Two-phase registration at startup (main pattern) ---------------------

    #[test]
    fn startup_two_phase_registration() {
        // Simulates wiring reactors in main() using create_reactor + into_reactor + insert.
        // No unsafe, no borrow conflicts.
        let mut wb = WorldBuilder::new();
        wb.register(Counter(0));
        wb.register(ReactorNotify::new(8, 16));
        wb.register(DeferredRemovals::default());
        wb.register(SourceRegistry::new());
        let mut world = wb.build();

        let mut system = ReactorSystem::new(&world);

        struct QuotingCtx {
            _rereactor_id: Token,
            _instrument: &'static str,
            layer: u32,
        }

        fn quoting_step(ctx: &mut QuotingCtx, mut counter: ResMut<Counter>) {
            counter.0 += u64::from(ctx.layer);
        }

        // Register data sources
        let btc_md = world.resource_mut::<ReactorNotify>().register_source();
        let eth_md = world.resource_mut::<ReactorNotify>().register_source();
        let positions = world.resource_mut::<ReactorNotify>().register_source();

        // Map natural keys
        {
            let sr = world.resource_mut::<SourceRegistry>();
            sr.insert("BTC", btc_md);
            sr.insert("ETH", eth_md);
            sr.insert("positions", positions);
        }

        // Register BTC quoting reactor — two-phase, safe
        let token = world.resource_mut::<ReactorNotify>().create_reactor();
        let reactor = quoting_step.into_reactor(
            QuotingCtx {
                _rereactor_id: token,
                _instrument: "BTC",
                layer: 1,
            },
            world.registry(),
        );
        world
            .resource_mut::<ReactorNotify>()
            .insert_reactor(token, reactor)
            .subscribe(btc_md)
            .subscribe(positions);

        // Register ETH quoting reactor
        let token = world.resource_mut::<ReactorNotify>().create_reactor();
        let reactor = quoting_step.into_reactor(
            QuotingCtx {
                _rereactor_id: token,
                _instrument: "ETH",
                layer: 2,
            },
            world.registry(),
        );
        world
            .resource_mut::<ReactorNotify>()
            .insert_reactor(token, reactor)
            .subscribe(eth_md)
            .subscribe(positions);

        // Frame 1: BTC data only — BTC rereactor wakes
        world.resource_mut::<ReactorNotify>().mark(btc_md);
        system.dispatch(&mut world);
        assert_eq!(world.resource::<Counter>().0, 1); // layer 1

        // Frame 2: position update — both reactors wake (deduped)
        world.resource_mut::<ReactorNotify>().mark(positions);
        system.dispatch(&mut world);
        assert_eq!(world.resource::<Counter>().0, 4); // 1 + 1 + 2
    }

    // -- Runtime registration from event handler (RegistryRef pattern) --------

    #[test]
    fn runtime_registration_with_registry_ref() {
        // Simulates an event handler registering a reactor at runtime.
        // Uses RegistryRef as a Param — same pattern as scheduling timers.
        use nexus_rt::{Handler, IntoHandler, RegistryRef};

        let mut wb = WorldBuilder::new();
        wb.register(Counter(0));
        wb.register(ReactorNotify::new(8, 16));
        wb.register(DeferredRemovals::default());
        wb.register(SourceRegistry::new());
        let mut world = wb.build();

        let mut system = ReactorSystem::new(&world);

        // Pre-register a data source and map it
        let md_source = world.resource_mut::<ReactorNotify>().register_source();
        world
            .resource_mut::<SourceRegistry>()
            .insert("BTC", md_source);

        // The reactor step function
        struct TwapCtx {
            rereactor_id: Token,
            remaining: u32,
        }

        fn twap_step(
            ctx: &mut TwapCtx,
            mut counter: ResMut<Counter>,
            mut removals: ResMut<DeferredRemovals>,
        ) {
            counter.0 += 1;
            ctx.remaining -= 1;
            if ctx.remaining == 0 {
                removals.deregister(ctx.rereactor_id);
            }
        }

        // The "admin command handler" — takes RegistryRef as a Param
        // to register reactors at runtime.
        fn on_admin_add_twap(
            mut notify: ResMut<ReactorNotify>,
            sources: Res<SourceRegistry>,
            reg: RegistryRef<'_>,
        ) {
            let md = sources.get(&"BTC").expect("BTC not listed");
            notify
                .register(
                    |id| TwapCtx {
                        rereactor_id: id,
                        remaining: 3,
                    },
                    twap_step,
                    &reg,
                )
                .subscribe(md);
        }

        // Build the handler (compile test: RegistryRef works as Param alongside
        // ResMut<ReactorNotify> and Res<SourceRegistry>)
        let mut handler = nexus_rt::no_event(on_admin_add_twap).into_handler(world.registry());

        // Simulate admin command arriving — handler registers the reactor
        handler.run(&mut world, ());
        assert_eq!(system.reactor_count(&world), 1);

        // 3 frames — reactor runs and self-removes
        for frame in 1..=4 {
            world.resource_mut::<ReactorNotify>().mark(md_source);
            system.dispatch(&mut world);

            if frame <= 3 {
                assert_eq!(world.resource::<Counter>().0, frame);
            } else {
                // Frame 4: reactor removed, counter stays at 3
                assert_eq!(world.resource::<Counter>().0, 3);
                assert_eq!(system.reactor_count(&world), 0);
            }
        }
    }

    // -- Pipeline reactor registered at startup ---------------------------------

    #[test]
    fn startup_pipeline_actor() {
        use nexus_rt::CtxPipelineBuilder;

        let mut wb = WorldBuilder::new();
        wb.register(Counter(0));
        wb.register(ReactorNotify::new(4, 8));
        wb.register(DeferredRemovals::default());
        let mut world = wb.build();

        let mut system = ReactorSystem::new(&world);

        struct Ctx {
            _rereactor_id: Token,
            multiplier: u64,
        }

        fn read(_ctx: &mut Ctx, counter: Res<Counter>) -> u64 {
            counter.0
        }

        fn multiply(ctx: &mut Ctx, val: u64) -> u64 {
            val * ctx.multiplier
        }

        fn store(_ctx: &mut Ctx, mut counter: ResMut<Counter>, val: u64) {
            counter.0 = val;
        }

        // Register source
        let src = world.resource_mut::<ReactorNotify>().register_source();

        // Two-phase: alloc token, build pipeline with registry, insert
        let token = world.resource_mut::<ReactorNotify>().create_reactor();
        let reg = world.registry();
        let pipeline = CtxPipelineBuilder::<Ctx, ()>::new()
            .then(nexus_rt::no_event(read), reg)
            .then(multiply, reg)
            .then(store, reg)
            .build();
        let reactor = nexus_rt::PipelineReactor::new(
            Ctx {
                _rereactor_id: token,
                multiplier: 3,
            },
            pipeline,
        );
        world
            .resource_mut::<ReactorNotify>()
            .insert_reactor(token, reactor)
            .subscribe(src);

        // Set initial value and dispatch
        world.resource_mut::<Counter>().0 = 10;
        world.resource_mut::<ReactorNotify>().mark(src);
        system.dispatch(&mut world);
        assert_eq!(world.resource::<Counter>().0, 30); // 10 * 3
    }

    // -- Runtime pipeline reactor via RegistryRef -------------------------------

    #[test]
    fn runtime_pipeline_actor_via_registry_ref() {
        use nexus_rt::{CtxPipelineBuilder, Handler, IntoHandler, PipelineReactor, RegistryRef};

        let mut wb = WorldBuilder::new();
        wb.register(Counter(0));
        wb.register(ReactorNotify::new(4, 8));
        wb.register(DeferredRemovals::default());
        let mut world = wb.build();

        let mut system = ReactorSystem::new(&world);
        let src = world.resource_mut::<ReactorNotify>().register_source();

        struct Ctx {
            _rereactor_id: Token,
        }

        fn double(_ctx: &mut Ctx, counter: Res<Counter>) -> u64 {
            counter.0 * 2
        }

        fn store(_ctx: &mut Ctx, mut counter: ResMut<Counter>, val: u64) {
            counter.0 = val;
        }

        // Handler that builds a pipeline reactor at runtime
        fn on_admin(mut notify: ResMut<ReactorNotify>, reg: RegistryRef<'_>) {
            let pipeline = CtxPipelineBuilder::<Ctx, ()>::new()
                .then(nexus_rt::no_event(double), &reg)
                .then(store, &reg)
                .build();

            // register_built doesn't need the token in context
            notify
                .register_built(PipelineReactor::new(
                    Ctx {
                        _rereactor_id: Token::new(0),
                    },
                    pipeline,
                ))
                // subscribe to source 0 — hardcoded for test simplicity
                .subscribe(DataSource(0));
        }

        let mut handler = nexus_rt::no_event(on_admin).into_handler(world.registry());
        handler.run(&mut world, ());

        world.resource_mut::<Counter>().0 = 5;
        world.resource_mut::<ReactorNotify>().mark(src);
        system.dispatch(&mut world);
        assert_eq!(world.resource::<Counter>().0, 10); // 5 * 2
    }
}
