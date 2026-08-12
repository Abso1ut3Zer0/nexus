//! `#[derive(Resource)]` on a generic type must produce a *conditional* impl:
//! `Foo<T>: Resource` exactly when `Foo<T>: Send + 'static`. Guards against a
//! regression to an unconditional impl (which would require every instantiation
//! to be Send and fail to compile at the derive).

use std::sync::Arc;

use nexus_rt::{Resource, WorldBuilder};

#[derive(Resource)]
struct Wrap<T>(T);

// A generic with its own where-clause — exercises the predicate-merge path in
// the derive (the type's `where` is preserved, `Self: Send + 'static` appended).
#[derive(Resource)]
struct Bounded<T: Clone>(T);

#[test]
fn generic_resource_registers_for_send_instantiations() {
    let mut wb = WorldBuilder::new();
    wb.register(Wrap(42u64));
    wb.register(Bounded(Arc::new(7u64)));
    let world = wb.build();

    assert_eq!(world.resource::<Wrap<u64>>().0, 42);
    assert_eq!(*world.resource::<Bounded<Arc<u64>>>().0, 7);
}
