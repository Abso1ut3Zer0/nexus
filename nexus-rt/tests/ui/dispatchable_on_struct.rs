// Mistake: #[derive(Dispatchable)] on a struct.
// Fix: Dispatchable can only be derived for enums.

use nexus_rt::Dispatchable;

#[derive(Dispatchable)]
struct NotAnEnum {
    x: u32,
}

fn main() {}
