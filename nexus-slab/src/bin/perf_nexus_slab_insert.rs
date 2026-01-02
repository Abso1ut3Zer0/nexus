//! Profiling binary for insert operations.
//!
//! Run with:
//!   cargo build --release --bin perf_insert
//!   perf stat -e cycles,instructions,cache-misses,cache-references \
//!       ./target/release/perf_insert
//!
//!   perf record -g ./target/release/perf_insert
//!   perf report

use std::hint::black_box;

const CAPACITY: usize = 100_000;
const ITERATIONS: usize = 100;

fn main() {
    // Pre-allocate outside timing loop
    let mut slabs: Vec<nexus_slab::Slab<u64>> = Vec::with_capacity(ITERATIONS);
    for _ in 0..ITERATIONS {
        let slab = nexus_slab::Slab::with_capacity(CAPACITY).unwrap();
        slabs.push(slab);
    }

    // Timed section - just inserts
    for slab in &mut slabs {
        for i in 0..CAPACITY as u64 {
            black_box(slab.insert(i).unwrap());
        }
    }
}
