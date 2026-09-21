// Mistake: #[derive(Dispatchable)] on an enum with zero variants.
// Fix: Dispatchable requires an enum with at least one variant.

use nexus_rt::Dispatchable;

#[derive(Dispatchable)]
enum Empty {}

fn main() {}
