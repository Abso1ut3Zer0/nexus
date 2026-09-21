//! `.arm()` rejects a duplicate key at construction (issue #723 follow-up).
//!
//! A duplicate key is the silent last-wins overwrite that `select!` would flag
//! as `unreachable_patterns` — a wiring bug. Every dispatch surface panics
//! deterministically at build time (before any dispatch runs) rather than
//! mis-routing at runtime. These cover the ordinal path (`dispatch_variant` /
//! `dispatch_on`), the hash path (`dispatch_map`), and the DAG surface.

// These tests panic at construction, so the arm/enum values are never actually
// dispatched (hence never constructed), and the DAG arm takes `&V` by contract.
#![allow(dead_code)]
#![allow(clippy::trivially_copy_pass_by_ref)]

use nexus_rt::{DagBuilder, Dispatchable, PipelineBuilder, ResMut, Resource, WorldBuilder};

#[derive(Resource, Default)]
struct Log(u64);

#[derive(Dispatchable, Clone, Copy)]
enum Cmd {
    A(u64),
    B(u64),
}

fn on_payload(mut log: ResMut<Log>, x: u64) {
    log.0 += x;
}

#[test]
#[should_panic(expected = "armed more than once")]
fn dispatch_variant_rejects_duplicate_variant() {
    let mut wb = WorldBuilder::new();
    wb.register(Log::default());
    let world = wb.build();
    let r = world.registry();

    let _ = PipelineBuilder::<Cmd>::new().dispatch_variant(r, |d| {
        d.arm(cmd_variants::A, on_payload)
            .arm(cmd_variants::A, on_payload) // duplicate variant -> panic
            .default_noop()
    });
}

#[derive(Dispatchable, Clone, Copy)]
enum Key {
    X,
    Y,
}

#[derive(Clone, Copy)]
struct Msg {
    key: Key,
}

fn on_msg(mut log: ResMut<Log>, _m: Msg) {
    log.0 += 1;
}

#[test]
#[should_panic(expected = "armed more than once")]
fn dispatch_on_rejects_duplicate_key() {
    let mut wb = WorldBuilder::new();
    wb.register(Log::default());
    let world = wb.build();
    let r = world.registry();

    let _ = PipelineBuilder::<Msg>::new().dispatch_on(
        |m: &Msg| m.key,
        r,
        |d| d.arm(Key::X, on_msg).arm(Key::X, on_msg).default_noop(),
    );
}

#[derive(Clone)]
struct Order {
    sym: String,
}

fn on_order(mut log: ResMut<Log>, _o: Order) {
    log.0 += 1;
}

#[test]
#[should_panic(expected = "armed more than once")]
fn dispatch_map_rejects_duplicate_key() {
    let mut wb = WorldBuilder::new();
    wb.register(Log::default());
    let world = wb.build();
    let r = world.registry();

    let _ = PipelineBuilder::<Order>::new().dispatch_map(
        |o: &Order| o.sym.clone(),
        r,
        |d| {
            d.arm("BTC".to_string(), on_order)
                .arm("BTC".to_string(), on_order) // duplicate key -> panic
                .default(on_order)
        },
    );
}

fn dag_on_msg(mut log: ResMut<Log>, _m: &Msg) {
    log.0 += 1;
}

#[test]
#[should_panic(expected = "armed more than once")]
fn dag_dispatch_on_rejects_duplicate_key() {
    let mut wb = WorldBuilder::new();
    wb.register(Log::default());
    let world = wb.build();
    let r = world.registry();

    let _ = DagBuilder::<Msg>::new().root(|m: Msg| m, r).dispatch_on(
        |m: &Msg| m.key,
        r,
        |d| {
            d.arm(Key::X, dag_on_msg)
                .arm(Key::X, dag_on_msg)
                .default_noop()
        },
    );
}
