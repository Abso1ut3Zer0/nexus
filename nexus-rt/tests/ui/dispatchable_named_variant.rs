// Mistake: #[derive(Dispatchable)] on an enum with a named-field (struct) variant.
// Fix: only unit and tuple variants are supported in this phase.

use nexus_rt::Dispatchable;

#[derive(Dispatchable)]
enum HasStructVariant {
    Ok(u32),
    Bad { field: u32 },
}

fn main() {}
