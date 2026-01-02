//! Profiling binary for get operations.
//!
//! Run with:
//!   cargo build --release --bin perf_get
//!   perf stat -e cycles,instructions,cache-misses,cache-references \
//!       ./target/release/perf_get

use std::hint::black_box;

const CAPACITY: usize = 100_000;
const ITERATIONS: usize = 100;

fn main() {
    // Setup: allocate and fill
    let mut slab: nexus_slab::Slab<u64> = nexus_slab::Slab::with_capacity(CAPACITY).unwrap();

    let keys: Vec<_> = (0..CAPACITY as u64)
        .map(|i| slab.insert(i).unwrap())
        .collect();

    // Timed section - just gets (sequential)
    for _ in 0..ITERATIONS {
        for key in &keys {
            black_box(slab.get(*key));
        }
    }
}
