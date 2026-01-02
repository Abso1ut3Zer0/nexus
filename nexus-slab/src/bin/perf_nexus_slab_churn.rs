//! Profiling binary for churn (insert/remove cycles).
//!
//! Run with:
//!   cargo build --release --bin perf_churn
//!   perf stat -e cycles,instructions,cache-misses,cache-references \
//!       ./target/release/perf_churn

use std::hint::black_box;

const CYCLES: usize = 10_000_000;

fn main() {
    let mut slab: nexus_slab::Slab<u64> = nexus_slab::Slab::with_capacity(1024).unwrap();

    // Timed section - insert then immediately remove (hot cache)
    for i in 0..CYCLES as u64 {
        let key = slab.insert(i).unwrap();
        black_box(slab.remove(key));
    }
}
