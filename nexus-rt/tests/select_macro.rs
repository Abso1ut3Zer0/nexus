//! Integration tests for the `select!` macro.

use nexus_rt::{Handler, PipelineBuilder, WorldBuilder, select};

// =============================================================================
// Test enum
// =============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    A,
    B,
    C,
}

// =============================================================================
// Tier 1 — input is the match value directly
// =============================================================================

fn handle_a(v: Kind) {
    assert_eq!(v, Kind::A);
}

fn handle_b(v: Kind) {
    assert_eq!(v, Kind::B);
}

fn handle_c(v: Kind) {
    assert_eq!(v, Kind::C);
}

#[test]
fn select_tier1_basic() {
    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    let mut pipeline = PipelineBuilder::<Kind>::new()
        .then(
            select! {
                reg,
                Kind::A => handle_a,
                Kind::B => handle_b,
                Kind::C => handle_c,
            },
            reg,
        )
        .build();

    pipeline.run(&mut world, Kind::A);
    pipeline.run(&mut world, Kind::B);
    pipeline.run(&mut world, Kind::C);
}

// =============================================================================
// Tier 1 — default arm
// =============================================================================

#[test]
fn select_tier1_default() {
    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    let mut pipeline = PipelineBuilder::<Kind>::new()
        .then(
            select! {
                reg,
                Kind::A => handle_a,
                _ => |_w, _x| { /* default — no-op */ },
            },
            reg,
        )
        .build();

    // All variants handled without panic.
    pipeline.run(&mut world, Kind::A);
    pipeline.run(&mut world, Kind::B);
    pipeline.run(&mut world, Kind::C);
}

// =============================================================================
// Tier 2 — match on a field, arms take the struct
// =============================================================================

#[derive(Debug, Clone, Copy)]
#[allow(dead_code)]
struct Order {
    kind: Kind,
    id: u64,
}

fn handle_order_a(o: Order) {
    assert_eq!(o.kind, Kind::A);
}

fn handle_order_b(o: Order) {
    assert_eq!(o.kind, Kind::B);
}

#[test]
fn select_tier2_key() {
    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    let mut pipeline = PipelineBuilder::<Order>::new()
        .then(
            select! {
                reg,
                key: |o: &Order| o.kind,
                Kind::A => handle_order_a,
                Kind::B => handle_order_b,
                Kind::C => |_o: Order| {},
            },
            reg,
        )
        .build();

    pipeline.run(
        &mut world,
        Order {
            kind: Kind::A,
            id: 1,
        },
    );
    pipeline.run(
        &mut world,
        Order {
            kind: Kind::B,
            id: 2,
        },
    );
    pipeline.run(
        &mut world,
        Order {
            kind: Kind::C,
            id: 3,
        },
    ); // Kind::C reuses handle_order_a — just verifies dispatch, not kind assertion
}

// =============================================================================
// Tier 3 — key + project
// =============================================================================

fn process_id(id: u64) {
    assert!(id > 0);
}

#[test]
fn select_tier3_key_project() {
    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    // Input is (u64, Kind). Match on Kind, arms receive u64.
    let mut pipeline = PipelineBuilder::<(u64, Kind)>::new()
        .then(
            select! {
                reg,
                key:     |(_, k): &(u64, Kind)| *k,
                project: |(id, _)| id,
                Kind::A => process_id,
                Kind::B => process_id,
                Kind::C => process_id,
            },
            reg,
        )
        .build();

    pipeline.run(&mut world, (42, Kind::A));
    pipeline.run(&mut world, (99, Kind::B));
    pipeline.run(&mut world, (7, Kind::C));
}

// =============================================================================
// Tier 3 — with default arm
// =============================================================================

#[test]
fn select_tier3_default() {
    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    let mut pipeline = PipelineBuilder::<(u64, Kind)>::new()
        .then(
            select! {
                reg,
                key:     |(_, k): &(u64, Kind)| *k,
                project: |(id, _)| id,
                Kind::A => process_id,
                _ => |_w, _input: (u64, Kind)| { /* default — sees raw input */ },
            },
            reg,
        )
        .build();

    pipeline.run(&mut world, (42, Kind::A));
    pipeline.run(&mut world, (42, Kind::B));
}

// =============================================================================
// Tier 3 — default arm sees the RAW input (pre-projection)
// =============================================================================
//
// Contract: named arms get the projected value (to match their fixed
// signatures), but the default arm is an inline user closure with no
// pre-existing signature, so it receives the raw pipeline input and can
// access the discriminant for diagnostic logging. This test locks in
// that contract so it can't regress silently.

#[test]
fn select_tier3_default_receives_raw_input() {
    use std::sync::atomic::{AtomicU64, Ordering};

    static OBSERVED_ID: AtomicU64 = AtomicU64::new(0);
    static OBSERVED_KIND: AtomicU64 = AtomicU64::new(99);

    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    let mut pipeline = PipelineBuilder::<(u64, Kind)>::new()
        .then(
            select! {
                reg,
                key:     |(_, k): &(u64, Kind)| *k,
                project: |(id, _)| id,
                Kind::A => process_id,
                _ => |_w, (id, kind): (u64, Kind)| {
                    OBSERVED_ID.store(id, Ordering::SeqCst);
                    OBSERVED_KIND.store(kind as u64, Ordering::SeqCst);
                },
            },
            reg,
        )
        .build();

    // Dispatch with Kind::B — goes to default — must see raw (17, Kind::B).
    pipeline.run(&mut world, (17, Kind::B));
    assert_eq!(OBSERVED_ID.load(Ordering::SeqCst), 17);
    assert_eq!(OBSERVED_KIND.load(Ordering::SeqCst), Kind::B as u64);

    // Different discriminant: must still be seen raw.
    pipeline.run(&mut world, (23, Kind::C));
    assert_eq!(OBSERVED_ID.load(Ordering::SeqCst), 23);
    assert_eq!(OBSERVED_KIND.load(Ordering::SeqCst), Kind::C as u64);
}

// =============================================================================
// Callback form
// =============================================================================

struct Ctx {
    count: u32,
}

fn on_a(ctx: &mut Ctx, _kind: Kind) {
    ctx.count += 1;
}

fn on_b(ctx: &mut Ctx, _kind: Kind) {
    ctx.count += 10;
}

#[test]
fn select_callback_basic() {
    use nexus_rt::CtxPipelineBuilder;

    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    let mut pipeline = CtxPipelineBuilder::<Ctx, Kind>::new()
        .then(
            select! {
                reg,
                ctx: Ctx,
                Kind::A => on_a,
                Kind::B => on_b,
                Kind::C => on_a,
            },
            reg,
        )
        .build();

    let mut ctx = Ctx { count: 0 };
    pipeline.run(&mut ctx, &mut world, Kind::A);
    assert_eq!(ctx.count, 1);
    pipeline.run(&mut ctx, &mut world, Kind::B);
    assert_eq!(ctx.count, 11);
    pipeline.run(&mut ctx, &mut world, Kind::C);
    assert_eq!(ctx.count, 12);
}

#[test]
fn select_callback_mutates_ctx() {
    use nexus_rt::CtxPipelineBuilder;

    fn increment(ctx: &mut Ctx, _kind: Kind) {
        ctx.count += 1;
    }

    fn double_increment(ctx: &mut Ctx, _kind: Kind) {
        ctx.count += 2;
    }

    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    let mut pipeline = CtxPipelineBuilder::<Ctx, Kind>::new()
        .then(
            select! {
                reg,
                ctx: Ctx,
                Kind::A => increment,
                Kind::B => double_increment,
                Kind::C => increment,
            },
            reg,
        )
        .build();

    let mut ctx = Ctx { count: 0 };
    pipeline.run(&mut ctx, &mut world, Kind::A);
    assert_eq!(ctx.count, 1);
    pipeline.run(&mut ctx, &mut world, Kind::B);
    assert_eq!(ctx.count, 3);
    pipeline.run(&mut ctx, &mut world, Kind::C);
    assert_eq!(ctx.count, 4);
}

// =============================================================================
// Built pipeline used directly as a select! arm / .then() step (#693)
//
// A built pipeline is already a resolved step. These tests exercise the
// `IntoCtxStep` / `IntoStep` impls that let a bare built pipeline be a
// select! arm or a nested .then() step with no `Opaque` wrapper closure.
// =============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MsgKind {
    NewOrder,
    Cancel,
}

#[derive(Debug, Clone, Copy)]
struct Decoded {
    kind: MsgKind,
    qty: u32,
}

struct SessionCtx {
    new_orders: u32,
    cancels: u32,
    last_qty: u32,
}

// Ctx side — the primary use case from #693: FIX session decode fanned out
// to per-message-type sub-pipelines. Each arm is a *bare* built pipeline.
#[test]
fn ctx_pipeline_as_select_arm_no_wrapper() {
    use nexus_rt::CtxPipelineBuilder;

    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    // Per-message-type sub-pipelines, each terminal (Out = ()).
    let new_order_pipe = CtxPipelineBuilder::<SessionCtx, Decoded>::new()
        .then(
            |ctx: &mut SessionCtx, m: Decoded| {
                ctx.new_orders += 1;
                ctx.last_qty = m.qty;
            },
            reg,
        )
        .build();

    let cancel_pipe = CtxPipelineBuilder::<SessionCtx, Decoded>::new()
        .then(
            |ctx: &mut SessionCtx, _m: Decoded| {
                ctx.cancels += 1;
            },
            reg,
        )
        .build();

    // The two built pipelines are select! arms directly — no
    // `|ctx, w, m| pipe.run(ctx, w, m)` Opaque wrapper.
    let mut dispatch = CtxPipelineBuilder::<SessionCtx, Decoded>::new()
        .then(
            select! {
                reg,
                ctx: SessionCtx,
                key: |m: &Decoded| m.kind,
                MsgKind::NewOrder => new_order_pipe,
                MsgKind::Cancel   => cancel_pipe,
            },
            reg,
        )
        .build();

    let mut ctx = SessionCtx {
        new_orders: 0,
        cancels: 0,
        last_qty: 0,
    };
    dispatch.run(
        &mut ctx,
        &mut world,
        Decoded {
            kind: MsgKind::NewOrder,
            qty: 7,
        },
    );
    dispatch.run(
        &mut ctx,
        &mut world,
        Decoded {
            kind: MsgKind::Cancel,
            qty: 0,
        },
    );
    dispatch.run(
        &mut ctx,
        &mut world,
        Decoded {
            kind: MsgKind::NewOrder,
            qty: 3,
        },
    );

    assert_eq!(ctx.new_orders, 2);
    assert_eq!(ctx.cancels, 1);
    assert_eq!(ctx.last_qty, 3);
}

// Ctx side — a built pipeline used directly as a nested .then() step.
#[test]
fn ctx_pipeline_as_then_step_no_wrapper() {
    use nexus_rt::CtxPipelineBuilder;

    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    // Terminal sub-pipeline consuming Decoded, producing ().
    let inner = CtxPipelineBuilder::<SessionCtx, Decoded>::new()
        .then(
            |ctx: &mut SessionCtx, m: Decoded| {
                ctx.last_qty = m.qty;
            },
            reg,
        )
        .build();

    // `inner` is a .then() step directly — it produces (), so `outer` is
    // terminal and can be built.
    let mut outer = CtxPipelineBuilder::<SessionCtx, Decoded>::new()
        .then(
            |ctx: &mut SessionCtx, m: Decoded| {
                ctx.new_orders += 1;
                m
            },
            reg,
        )
        .then(inner, reg)
        .build();

    let mut ctx = SessionCtx {
        new_orders: 0,
        cancels: 0,
        last_qty: 0,
    };
    outer.run(
        &mut ctx,
        &mut world,
        Decoded {
            kind: MsgKind::NewOrder,
            qty: 42,
        },
    );
    assert_eq!(ctx.new_orders, 1);
    assert_eq!(ctx.last_qty, 42);
}

// Plain side — a built plain pipeline used directly as a select! arm.
#[test]
fn plain_pipeline_as_select_arm_no_wrapper() {
    use std::sync::atomic::{AtomicU32, Ordering};

    static NEW_ORDERS: AtomicU32 = AtomicU32::new(0);
    static CANCELS: AtomicU32 = AtomicU32::new(0);
    // Reset so the test is deterministic regardless of harness reuse.
    NEW_ORDERS.store(0, Ordering::SeqCst);
    CANCELS.store(0, Ordering::SeqCst);

    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    let new_order_pipe = PipelineBuilder::<Decoded>::new()
        .then(
            |m: Decoded| {
                NEW_ORDERS.fetch_add(m.qty, Ordering::SeqCst);
            },
            reg,
        )
        .build();

    let cancel_pipe = PipelineBuilder::<Decoded>::new()
        .then(
            |_m: Decoded| {
                CANCELS.fetch_add(1, Ordering::SeqCst);
            },
            reg,
        )
        .build();

    let mut dispatch = PipelineBuilder::<Decoded>::new()
        .then(
            select! {
                reg,
                key: |m: &Decoded| m.kind,
                MsgKind::NewOrder => new_order_pipe,
                MsgKind::Cancel   => cancel_pipe,
            },
            reg,
        )
        .build();

    dispatch.run(
        &mut world,
        Decoded {
            kind: MsgKind::NewOrder,
            qty: 5,
        },
    );
    dispatch.run(
        &mut world,
        Decoded {
            kind: MsgKind::Cancel,
            qty: 0,
        },
    );
    dispatch.run(
        &mut world,
        Decoded {
            kind: MsgKind::NewOrder,
            qty: 2,
        },
    );

    assert_eq!(NEW_ORDERS.load(Ordering::SeqCst), 7);
    assert_eq!(CANCELS.load(Ordering::SeqCst), 1);
}

// Plain side — a built plain pipeline used directly as a nested .then() step.
#[test]
fn plain_pipeline_as_then_step_no_wrapper() {
    use std::sync::atomic::{AtomicU32, Ordering};

    static SEEN: AtomicU32 = AtomicU32::new(0);
    // Reset so the test is deterministic regardless of harness reuse.
    SEEN.store(0, Ordering::SeqCst);

    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    let inner = PipelineBuilder::<Decoded>::new()
        .then(
            |m: Decoded| {
                SEEN.store(m.qty, Ordering::SeqCst);
            },
            reg,
        )
        .build();

    let mut outer = PipelineBuilder::<Decoded>::new()
        .then(|m: Decoded| m, reg)
        .then(inner, reg)
        .build();

    outer.run(
        &mut world,
        Decoded {
            kind: MsgKind::NewOrder,
            qty: 99,
        },
    );
    assert_eq!(SEEN.load(Ordering::SeqCst), 99);
}
