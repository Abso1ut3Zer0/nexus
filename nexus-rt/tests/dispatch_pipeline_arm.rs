//! Verifies a **pre-built `Pipeline`** can be handed to a dispatch table as an
//! arm — the runtime-dispatch counterpart of #693 (a built pipeline usable as a
//! `select!` arm). This is what lets you pre-build a pipeline per arm and wire
//! them into `.dispatch_variant` / `.dispatch_on`.

use nexus_rt::{Dispatchable, PipelineBuilder, ResMut, Resource, WorldBuilder};

#[derive(Resource, Default)]
struct Log(Vec<u64>);

#[derive(Dispatchable, Clone, Copy)]
enum Cmd {
    A(u64),
    B(u64),
    C,
}

fn note_a(mut log: ResMut<Log>, p: u64) {
    log.0.push(1000 + p);
}
fn note_b(mut log: ResMut<Log>, p: u64) {
    log.0.push(2000 + p);
}

#[test]
fn dispatch_variant_arm_is_a_prebuilt_pipeline() {
    let mut wb = WorldBuilder::new();
    wb.register(Log::default());
    let mut world = wb.build();
    let r = world.registry();

    // Pre-build a terminal pipeline PER ARM, over the variant's payload type (u64).
    let arm_a = PipelineBuilder::<u64>::new().then(note_a, r).build();
    let arm_b = PipelineBuilder::<u64>::new().then(note_b, r).build();

    let mut dispatch = PipelineBuilder::<Cmd>::new()
        .dispatch_variant(r, |d| {
            d.arm(cmd_variants::A, arm_a) // arm == a whole pre-built pipeline
                .arm(cmd_variants::B, arm_b)
                // C left unset -> no-op fallback.
                .default_noop()
        })
        .build();

    use nexus_rt::Handler;
    dispatch.run(&mut world, Cmd::A(5));
    dispatch.run(&mut world, Cmd::B(7));
    dispatch.run(&mut world, Cmd::C); // no-op

    assert_eq!(world.resource::<Log>().0, vec![1005, 2007]);
}

#[derive(Resource, Default)]
struct OnLog(Vec<u64>);

#[derive(Clone, Copy)]
struct Msg {
    kind: Kind,
    payload: u64,
}
#[derive(Dispatchable, Clone, Copy)]
enum Kind {
    X,
    Y,
}

fn on_x(mut log: ResMut<OnLog>, m: Msg) {
    log.0.push(100 + m.payload);
}

#[test]
fn dispatch_on_arm_is_a_prebuilt_pipeline() {
    let mut wb = WorldBuilder::new();
    wb.register(OnLog::default());
    let mut world = wb.build();
    let r = world.registry();

    // Pre-build a terminal pipeline over the WHOLE value (Msg) as the arm.
    let arm_x = PipelineBuilder::<Msg>::new().then(on_x, r).build();

    let mut dispatch = PipelineBuilder::<Msg>::new()
        .dispatch_on(
            |m: &Msg| m.kind,
            r,
            |d| d.arm(Kind::X, arm_x).default_noop(),
        )
        .build();

    use nexus_rt::Handler;
    dispatch.run(
        &mut world,
        Msg {
            kind: Kind::X,
            payload: 9,
        },
    );
    dispatch.run(
        &mut world,
        Msg {
            kind: Kind::Y,
            payload: 1,
        },
    ); // unset -> no-op

    assert_eq!(world.resource::<OnLog>().0, vec![109]);
}
