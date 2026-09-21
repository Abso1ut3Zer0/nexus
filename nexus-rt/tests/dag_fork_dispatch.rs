//! `dispatch_on` composes *inside* a DAG fork arm (issue #723 follow-up).
//!
//! Every DAG combinator is available on both the chain and a fork arm; this
//! covers the previously-missing fork-arm case for `dispatch_on` (`DagArm` /
//! `CtxDagArm`) by routing within one arm and merging with a plain arm.

#![allow(clippy::trivially_copy_pass_by_ref)] // DAG arms take `&V` by contract

use nexus_rt::{CtxDagBuilder, DagBuilder, Dispatchable, Handler, ResMut, Resource, WorldBuilder};

#[derive(Resource, Default)]
struct Out(i64);

#[derive(Dispatchable, Clone, Copy)]
enum Kind {
    A,
    B,
}

#[derive(Clone, Copy)]
struct Ev {
    kind: Kind,
    v: i64,
}

// Arms of the in-fork dispatch borrow `&Ev` and bubble up an i64.
fn route_a(_e: &Ev) -> i64 {
    100
}
fn route_b(_e: &Ev) -> i64 {
    200
}

// The other fork arm just projects a field.
fn plain_arm(e: &Ev) -> i64 {
    e.v
}

fn combine(mut out: ResMut<Out>, routed: &i64, plain: &i64) {
    out.0 = *routed + *plain;
}

#[test]
fn dispatch_on_inside_dag_fork_arm() {
    let mut wb = WorldBuilder::new();
    wb.register(Out::default());
    let mut world = wb.build();
    let reg = world.registry();

    let mut dag = DagBuilder::<Ev>::new()
        .root(|e: Ev| e, reg)
        .fork()
        .arm(|seed| {
            seed.then(|e: &Ev| *e, reg) // DagArm<Ev, Ev, _>
                .dispatch_on(
                    |e: &Ev| e.kind,
                    reg,
                    // Exhaustive (Kind::A + Kind::B), so no default; arms return i64.
                    |d| d.arm(Kind::A, route_a).arm(Kind::B, route_b),
                )
        })
        .arm(|seed| seed.then(plain_arm, reg))
        .merge(combine, reg)
        .build();

    dag.run(
        &mut world,
        Ev {
            kind: Kind::A,
            v: 5,
        },
    );
    assert_eq!(world.resource::<Out>().0, 105); // 100 (route_a) + 5 (plain_arm)

    dag.run(
        &mut world,
        Ev {
            kind: Kind::B,
            v: 7,
        },
    );
    assert_eq!(world.resource::<Out>().0, 207); // 200 (route_b) + 7 (plain_arm)
}

// --- Context-aware mirror: `CtxDagArm::dispatch_on` inside a ctx fork arm. ---

struct Ctx {
    bump: i64,
}

fn ctx_route_a(c: &mut Ctx, _e: &Ev) -> i64 {
    100 + c.bump
}
fn ctx_route_b(c: &mut Ctx, _e: &Ev) -> i64 {
    200 + c.bump
}
fn ctx_plain(_c: &mut Ctx, e: &Ev) -> i64 {
    e.v
}
fn ctx_combine(_c: &mut Ctx, mut out: ResMut<Out>, routed: &i64, plain: &i64) {
    out.0 = *routed + *plain;
}

#[test]
fn ctx_dispatch_on_inside_dag_fork_arm() {
    let mut wb = WorldBuilder::new();
    wb.register(Out::default());
    let mut world = wb.build();
    let reg = world.registry();

    let mut dag = CtxDagBuilder::<Ctx, Ev>::new()
        .root(|_c: &mut Ctx, e: Ev| e, reg)
        .fork()
        .arm(|seed| {
            seed.then(|_c: &mut Ctx, e: &Ev| *e, reg) // CtxDagArm<Ctx, Ev, Ev, _>
                .dispatch_on(
                    |e: &Ev| e.kind,
                    reg,
                    |d| d.arm(Kind::A, ctx_route_a).arm(Kind::B, ctx_route_b),
                )
        })
        .arm(|seed| seed.then(ctx_plain, reg))
        .merge(ctx_combine, reg)
        .build();

    let mut ctx = Ctx { bump: 1 };
    dag.run(
        &mut ctx,
        &mut world,
        Ev {
            kind: Kind::A,
            v: 5,
        },
    );
    assert_eq!(world.resource::<Out>().0, 106); // (100 + bump) + 5

    dag.run(
        &mut ctx,
        &mut world,
        Ev {
            kind: Kind::B,
            v: 7,
        },
    );
    assert_eq!(world.resource::<Out>().0, 208); // (200 + bump) + 7
}
