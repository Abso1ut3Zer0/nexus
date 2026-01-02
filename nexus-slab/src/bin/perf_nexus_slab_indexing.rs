//! Profiling binary to isolate indexing overhead.
//!
//! This benchmark focuses on the slot_ptr calculation and memory access pattern.
//!
//! Run with:
//!   cargo build --release --bin perf_indexing
//!   perf stat -e cycles,instructions,cache-misses,cache-references,L1-dcache-load-misses \
//!       ./target/release/perf_indexing

use std::hint::black_box;

const CAPACITY: usize = 100_000;
const ITERATIONS: usize = 100;

fn main() {
    // Setup
    let mut slab: nexus_slab::Slab<u64> = nexus_slab::Slab::with_capacity(CAPACITY).unwrap();

    let keys: Vec<_> = (0..CAPACITY as u64)
        .map(|i| slab.insert(i).unwrap())
        .collect();

    // Pseudo-random access pattern to stress cache
    let indices: Vec<usize> = (0..CAPACITY).map(|i| (i * 7919) % CAPACITY).collect();

    // Timed section - random access pattern
    for _ in 0..ITERATIONS {
        for &idx in &indices {
            black_box(slab.get(keys[idx]));
        }
    }
}
