// `#[derive(Resource)]` on a generic type is conditional: `Wrap<T>` is a
// `Resource` only when `Wrap<T>: Send + 'static`. Registering a non-Send
// instantiation must therefore be rejected.
use std::rc::Rc;

use nexus_rt::{Resource, WorldBuilder};

#[derive(Resource)]
struct Wrap<T>(T);

fn main() {
    let mut wb = WorldBuilder::new();
    wb.register(Wrap(Rc::new(0u32)));
}
