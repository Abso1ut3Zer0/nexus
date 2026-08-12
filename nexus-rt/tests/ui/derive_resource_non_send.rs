// A non-Send type deriving Resource must still be rejected (supertrait), and the
// error should mention Send — this guards the derive-fix from silently accepting.
use nexus_rt::Resource;

#[derive(Resource)]
struct Bad(std::rc::Rc<u32>);

fn main() {}
