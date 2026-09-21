//! Integration tests for the `.dispatch_on()` pipeline combinator
//! (issue #723, Phase 2a) and the tuple-product `Dispatchable` key
//! (Phase 2b).
//!
//! `.dispatch_on()` is terminal keyed dispatch on a *projected* key: `key_fn`
//! maps the value to a [`Dispatchable`] key, and — unlike `.dispatch_variant()`
//! — every arm receives the **whole** value (there is no payload unwrap because
//! a projection carries no variant guarantee). Unlisted keys run a no-op unless
//! a `.default` is set.

use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use nexus_rt::{Dispatchable, Handler, PipelineBuilder, ResMut, Resource, WorldBuilder};

// Projected key: a fieldless discriminant carried as a struct field. `Copy` so
// `key_fn` can read it out of `&Tick` by value.
#[derive(Dispatchable, Clone, Copy)]
enum Source {
    A, // ordinal 0
    B, // ordinal 1
    C, // ordinal 2 — left unset in the wiring below
}

// The whole value each arm receives. `Copy` (POD): arms take it by value, as
// the dispatch API hands the whole value to the chosen arm.
#[derive(Clone, Copy)]
struct Tick {
    source: Source,
    px: u64,
}

// Records which arm fired and the whole-value `px` it saw.
#[derive(Resource, Default)]
struct Log {
    a: Option<u64>,
    b: Option<u64>,
    fallback: Option<u64>,
}

// Named-fn arms: params first, whole value last.
fn on_a(mut log: ResMut<Log>, t: Tick) {
    log.a = Some(t.px);
}

fn on_b(mut log: ResMut<Log>, t: Tick) {
    log.b = Some(t.px);
}

fn on_default(mut log: ResMut<Log>, t: Tick) {
    log.fallback = Some(t.px);
}

#[test]
fn routes_on_projected_key_and_passes_whole_value() {
    let mut wb = WorldBuilder::new();
    wb.register(Log::default());
    let mut world = wb.build();
    let reg = world.registry();

    let mut pipeline = PipelineBuilder::<Tick>::new()
        .dispatch_on(
            |t: &Tick| t.source,
            reg,
            // `Source::C` intentionally unset — `.default_noop()` opts out of
            // the exhaustive-table requirement and no-ops it.
            |d| d.arm(Source::A, on_a).arm(Source::B, on_b).default_noop(),
        )
        .build();

    pipeline.run(
        &mut world,
        Tick {
            source: Source::A,
            px: 100,
        },
    );
    pipeline.run(
        &mut world,
        Tick {
            source: Source::B,
            px: 200,
        },
    );
    pipeline.run(
        &mut world,
        Tick {
            source: Source::C,
            px: 300,
        },
    ); // unset → no-op

    let log = world.resource::<Log>();
    // Right arm fired, and each arm saw the whole `Tick` (its `px`).
    assert_eq!(log.a, Some(100));
    assert_eq!(log.b, Some(200));
    // Unset key hit the no-op fallback — no default installed, nothing ran.
    assert_eq!(log.fallback, None);
}

#[test]
fn unset_keys_route_to_default_when_set() {
    let mut wb = WorldBuilder::new();
    wb.register(Log::default());
    let mut world = wb.build();
    let reg = world.registry();

    let mut pipeline = PipelineBuilder::<Tick>::new()
        .dispatch_on(
            |t: &Tick| t.source,
            reg,
            |d| d.arm(Source::A, on_a).default(on_default),
        )
        .build();

    pipeline.run(
        &mut world,
        Tick {
            source: Source::A,
            px: 11,
        },
    ); // matched arm
    pipeline.run(
        &mut world,
        Tick {
            source: Source::B,
            px: 22,
        },
    ); // unset → default
    pipeline.run(
        &mut world,
        Tick {
            source: Source::C,
            px: 33,
        },
    ); // unset → default

    let log = world.resource::<Log>();
    assert_eq!(log.a, Some(11));
    // Last unset key to hit the default wins the recorded px.
    assert_eq!(log.fallback, Some(33));
    // The default arm is the only thing that ran for B/C; the B arm never fired.
    assert_eq!(log.b, None);
}

#[test]
fn closure_arm_receives_whole_value() {
    // Arity-0 closure arm (no resource params). Captures a Send + 'static sink
    // so the boxed step satisfies `S::Step: Send + 'static`.
    let captured = Arc::new(AtomicU64::new(0));
    let sink = Arc::clone(&captured);

    let mut world = WorldBuilder::new().build();
    let reg = world.registry();

    let mut pipeline = PipelineBuilder::<Tick>::new()
        .dispatch_on(
            |t: &Tick| t.source,
            reg,
            move |d| {
                d.arm(Source::A, move |t: Tick| {
                    sink.store(t.px, Ordering::Relaxed);
                })
                // B, C unset — no-op fallback.
                .default_noop()
            },
        )
        .build();

    pipeline.run(
        &mut world,
        Tick {
            source: Source::A,
            px: 777,
        },
    );
    pipeline.run(
        &mut world,
        Tick {
            source: Source::B,
            px: 999,
        },
    ); // unset → no-op

    assert_eq!(captured.load(Ordering::Relaxed), 777);
}

// -- tuple-product key (Phase 2b) --------------------------------------------

#[derive(Dispatchable, Clone, Copy)]
enum Coarse {
    X, // ordinal 0
    Y, // ordinal 1
}

#[derive(Dispatchable, Clone, Copy)]
enum Fine {
    P, // ordinal 0
    Q, // ordinal 1
    R, // ordinal 2
}

#[derive(Clone, Copy)]
struct Grid {
    a: Coarse,
    b: Fine,
    tag: u64,
}

#[derive(Resource, Default)]
struct PairLog {
    // Which composite ordinal fired, and the tag it saw.
    fired: Vec<(usize, u64)>,
}

fn on_xp(mut log: ResMut<PairLog>, g: Grid) {
    log.fired.push((0, g.tag));
}
fn on_yq(mut log: ResMut<PairLog>, g: Grid) {
    log.fired.push((4, g.tag));
}
fn on_yr(mut log: ResMut<PairLog>, g: Grid) {
    log.fired.push((5, g.tag));
}

#[test]
fn tuple_product_ordinals_are_dense_and_distinct() {
    // 2 * 3 = 6 dense slots, row-major: a.ordinal() * Fine::VARIANTS + b.ordinal().
    assert_eq!(<(Coarse, Fine)>::VARIANTS, 6);

    let all = [
        ((Coarse::X, Fine::P), 0),
        ((Coarse::X, Fine::Q), 1),
        ((Coarse::X, Fine::R), 2),
        ((Coarse::Y, Fine::P), 3),
        ((Coarse::Y, Fine::Q), 4),
        ((Coarse::Y, Fine::R), 5),
    ];
    // Every pair maps to the expected dense ordinal...
    for (pair, expected) in all {
        assert_eq!(pair.ordinal(), expected);
    }
    // ...and the six ordinals are all distinct and fill 0..6.
    let mut seen: Vec<usize> = all.iter().map(|(p, _)| p.ordinal()).collect();
    seen.sort_unstable();
    assert_eq!(seen, (0..6).collect::<Vec<_>>());
}

#[test]
fn dispatch_on_tuple_product_key() {
    let mut wb = WorldBuilder::new();
    wb.register(PairLog::default());
    let mut world = wb.build();
    let reg = world.registry();

    let mut pipeline = PipelineBuilder::<Grid>::new()
        .dispatch_on(
            |g: &Grid| (g.a, g.b),
            reg,
            |d| {
                d.arm((Coarse::X, Fine::P), on_xp)
                    .arm((Coarse::Y, Fine::Q), on_yq)
                    .arm((Coarse::Y, Fine::R), on_yr)
                    // The other three composite slots are unset — no-op fallback.
                    .default_noop()
            },
        )
        .build();

    // Each wired pair fires its own arm; a distinct pair maps to a distinct
    // slot (no collision between (X,P), (Y,Q), (Y,R)).
    pipeline.run(
        &mut world,
        Grid {
            a: Coarse::X,
            b: Fine::P,
            tag: 1,
        },
    );
    pipeline.run(
        &mut world,
        Grid {
            a: Coarse::Y,
            b: Fine::Q,
            tag: 2,
        },
    );
    pipeline.run(
        &mut world,
        Grid {
            a: Coarse::Y,
            b: Fine::R,
            tag: 3,
        },
    );
    // An unwired pair falls through to the no-op.
    pipeline.run(
        &mut world,
        Grid {
            a: Coarse::X,
            b: Fine::Q,
            tag: 4,
        },
    );

    let log = world.resource::<PairLog>();
    assert_eq!(log.fired, vec![(0, 1), (4, 2), (5, 3)]);
}
