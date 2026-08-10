// Struct with implicit padding between u64 and u32 fields.
// No unsafe impl Pod for Padded; should fail to compile.
#[repr(C)]
struct Padded {
    a: u64,
    b: u32,
}

fn main() {
    nexus_slot::spsc::slot::<Padded>();
}
