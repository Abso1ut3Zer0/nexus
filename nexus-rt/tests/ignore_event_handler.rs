//! The E-agnostic ignore-event raw handler path: `f.into_handler_event_ignored`
//! drops the event for ANY E, including borrowed/non-'static events.
use nexus_rt::{Handler, IntoHandlerIgnoringEvent, Res, ResMut, Resource, WorldBuilder};

#[derive(Resource)]
struct Count(u64);
#[derive(Resource)]
struct Name(&'static str);

fn bump(mut c: ResMut<Count>) {
    c.0 += 1;
}

fn bump_named(name: Res<Name>, mut c: ResMut<Count>) {
    let _ = name.0;
    c.0 += 1;
}

#[test]
fn drops_owned_event() {
    let mut wb = WorldBuilder::new();
    wb.register(Count(0));
    let mut world = wb.build();

    // E = u32 inferred from the Box<dyn Handler<u32>>; event dropped.
    let mut h: Box<dyn Handler<u32>> = Box::new(bump.into_handler_event_ignored(world.registry()));
    h.run(&mut world, 999);
    h.run(&mut world, 7);
    assert_eq!(world.resource::<Count>().0, 2);
}

#[test]
fn drops_borrowed_nonstatic_event() {
    let mut wb = WorldBuilder::new();
    wb.register(Count(0));
    wb.register(Name("wire"));
    let mut world = wb.build();

    // The event is a BORROWED slice — NOT 'static. This is the wire-buffer case.
    fn run_with_borrowed<'a>(
        world: &mut nexus_rt::World,
        h: &mut dyn Handler<&'a [u8]>,
        buf: &'a [u8],
    ) {
        h.run(world, buf);
    }

    let mut h = bump_named.into_handler_event_ignored(world.registry());
    let data = vec![1u8, 2, 3];
    run_with_borrowed(&mut world, &mut h, &data);
    run_with_borrowed(&mut world, &mut h, &data);
    assert_eq!(world.resource::<Count>().0, 2);
}
