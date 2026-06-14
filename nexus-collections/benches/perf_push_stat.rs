//! Bare push loop for perf stat analysis.
//!
//! Zero instrumentation — let hardware counters do the work.
//! Pre-allocates all handles upfront, then pushes in one straight run.
//! No pop/clear interleaved — pure push measurement.
//!
//! Run with:
//!   cargo build --release --example perf_push_stat
//!   perf stat -r 25 -e cycles,instructions,... taskset -c 0 ./target/release/examples/perf_push_stat

use std::hint::black_box;

use nexus_collections::slab::RcSlot;
use nexus_collections::slab::heap::{Heap, HeapNode};
use nexus_slab::rc::unbounded::Slab;

const COUNT: usize = 500_000;

struct Xorshift {
    state: u64,
}

impl Xorshift {
    fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next(&mut self) -> u64 {
        self.state ^= self.state << 13;
        self.state ^= self.state >> 7;
        self.state ^= self.state << 17;
        self.state
    }
}

fn main() {
    // SAFETY: single-threaded, no concurrent access
    let slab = unsafe { Slab::<HeapNode<u64>>::with_chunk_capacity(8192) };

    let mut rng = Xorshift::new(0xDEAD_BEEF_CAFE_BABEu64);

    // Pre-allocate all handles
    let handles: Vec<RcSlot<HeapNode<u64>>> = (0..COUNT)
        .map(|_| slab.alloc(HeapNode::new(rng.next())))
        .collect();

    let mut heap = Heap::new();

    // Warmup: push/clear to fault pages and warm TLB
    for handle in &handles {
        heap.link(handle);
    }
    heap.clear(&slab);

    // ---- Measured section: pure push, no cleanup ----
    for handle in &handles {
        heap.link(handle);
        black_box(());
    }

    black_box(&heap);
    heap.clear(&slab);

    // Free all handles to satisfy the slab contract
    for handle in handles {
        slab.free(handle);
    }
}
