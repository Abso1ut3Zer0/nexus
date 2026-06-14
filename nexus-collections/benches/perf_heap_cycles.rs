#![allow(clippy::unnecessary_semicolon)]
//! Heap benchmark: batched, unrolled cycle-accurate latency measurement.
//!
//! Uses `seq_macro::seq!` for compile-time unroll of 100 ops per sample
//! to amortize rdtsc overhead. Same methodology as perf_rbtree.rs.
//!
//! Run with:
//!   cargo build --release --example perf_heap_cycles -p nexus-collections
//!   taskset -c 0 ./target/release/examples/perf_heap_cycles

use seq_macro::seq;
use std::hint::black_box;

use nexus_collections::slab::RcSlot;
use nexus_collections::slab::heap::{Heap, HeapNode};
use nexus_slab::rc::bounded::Slab;

const CAPACITY: usize = 200_000;
const SAMPLES: usize = 50_000;
const WARMUP: usize = 5_000;
const BATCH: usize = 100;

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

#[inline(always)]
fn rdtsc_start() -> u64 {
    unsafe {
        std::arch::x86_64::_mm_lfence();
        std::arch::x86_64::_rdtsc()
    }
}

#[inline(always)]
fn rdtsc_end() -> u64 {
    unsafe {
        let mut aux: u32 = 0;
        let tsc = std::arch::x86_64::__rdtscp(&raw mut aux);
        std::arch::x86_64::_mm_lfence();
        tsc
    }
}

fn percentile(sorted: &[u64], p: f64) -> u64 {
    let idx = ((sorted.len() as f64) * p / 100.0) as usize;
    sorted[idx.min(sorted.len() - 1)]
}

fn print_row(label: &str, samples: &mut [u64]) {
    samples.sort_unstable();
    println!(
        "  {:<32} p50={:>5}  p90={:>5}  p99={:>6}  p999={:>7}  max={:>8}",
        label,
        percentile(samples, 50.0),
        percentile(samples, 90.0),
        percentile(samples, 99.0),
        percentile(samples, 99.9),
        samples[samples.len() - 1],
    );
}

fn main() {
    let slab = unsafe { Slab::<HeapNode<u64>>::with_capacity(CAPACITY) };
    let mut rng = Xorshift::new(0xDEAD_BEEF_CAFE_BABEu64);

    println!("HEAP OPERATION LATENCY (cycles/op) — batched, {BATCH} ops/sample");
    println!("Samples: {SAMPLES}, Warmup: {WARMUP}");
    println!("====================================================================\n");

    // ── LINK (batched) ──────────────────────────────────────────────
    // Pre-allocate 100 handles with random priorities, time linking all.
    println!("LINK ({BATCH} unrolled ops/sample)");
    println!("---");

    // link into empty heap
    {
        let mut heap = Heap::new();
        let mut samples = Vec::with_capacity(SAMPLES);

        for _ in 0..WARMUP {
            let handles: [RcSlot<HeapNode<u64>>; BATCH] =
                std::array::from_fn(|_| slab.alloc(HeapNode::new(rng.next())));
            let s = rdtsc_start();
            seq!(I in 0..100 { heap.link(&handles[I]); });
            let e = rdtsc_end();
            black_box(e - s);
            // Pop all to reset, free handles
            for _ in 0..BATCH {
                if let Some(h) = heap.pop() {
                    slab.free(h);
                }
            }
            for h in handles {
                slab.free(h);
            }
        }

        for _ in 0..SAMPLES {
            let handles: [RcSlot<HeapNode<u64>>; BATCH] =
                std::array::from_fn(|_| slab.alloc(HeapNode::new(rng.next())));
            let s = rdtsc_start();
            seq!(I in 0..100 { heap.link(&handles[I]); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH as u64);
            for _ in 0..BATCH {
                if let Some(h) = heap.pop() {
                    slab.free(h);
                }
            }
            for h in handles {
                slab.free(h);
            }
        }
        print_row("link (empty heap)", &mut samples);
    }

    // link into steady-state heap (~1000 elements)
    {
        let mut heap = Heap::new();
        let steady: Vec<RcSlot<HeapNode<u64>>> = (0..1000)
            .map(|_| {
                let h = slab.alloc(HeapNode::new(rng.next()));
                heap.link(&h);
                h
            })
            .collect();

        let mut samples = Vec::with_capacity(SAMPLES);

        for _ in 0..WARMUP {
            let handles: [RcSlot<HeapNode<u64>>; BATCH] =
                std::array::from_fn(|_| slab.alloc(HeapNode::new(rng.next())));
            let s = rdtsc_start();
            seq!(I in 0..100 { heap.link(&handles[I]); });
            let e = rdtsc_end();
            black_box(e - s);
            // Unlink the batch we just added
            for h in &handles {
                heap.unlink(h, &slab);
            }
            for h in handles {
                slab.free(h);
            }
        }

        for _ in 0..SAMPLES {
            let handles: [RcSlot<HeapNode<u64>>; BATCH] =
                std::array::from_fn(|_| slab.alloc(HeapNode::new(rng.next())));
            let s = rdtsc_start();
            seq!(I in 0..100 { heap.link(&handles[I]); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH as u64);
            for h in &handles {
                heap.unlink(h, &slab);
            }
            for h in handles {
                slab.free(h);
            }
        }
        print_row("link (@1000)", &mut samples);

        heap.clear(&slab);
        for h in steady {
            slab.free(h);
        }
    }

    println!();

    // ── POP (batched) ───────────────────────────────────────────────
    // Fill heap with 100, then time popping all 100.
    println!("POP ({BATCH} unrolled ops/sample)");
    println!("---");

    {
        let mut heap = Heap::new();
        let mut popped: [Option<RcSlot<HeapNode<u64>>>; BATCH] = std::array::from_fn(|_| None);
        let mut samples = Vec::with_capacity(SAMPLES);

        for _ in 0..WARMUP {
            let handles: [RcSlot<HeapNode<u64>>; BATCH] =
                std::array::from_fn(|_| slab.alloc(HeapNode::new(rng.next())));
            for h in &handles {
                heap.link(h);
            }
            let s = rdtsc_start();
            seq!(I in 0..100 { popped[I] = heap.pop(); });
            let e = rdtsc_end();
            black_box(e - s);
            for slot in &mut popped {
                if let Some(h) = slot.take() {
                    slab.free(h);
                }
            }
            for h in handles {
                slab.free(h);
            }
        }

        for _ in 0..SAMPLES {
            let handles: [RcSlot<HeapNode<u64>>; BATCH] =
                std::array::from_fn(|_| slab.alloc(HeapNode::new(rng.next())));
            for h in &handles {
                heap.link(h);
            }
            let s = rdtsc_start();
            seq!(I in 0..100 { popped[I] = heap.pop(); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH as u64);
            for slot in &mut popped {
                if let Some(h) = slot.take() {
                    slab.free(h);
                }
            }
            for h in handles {
                slab.free(h);
            }
        }
        print_row("pop (from 100)", &mut samples);
    }

    // Pop from steady-state heap (~1000 elements), pop 100, re-add 100
    {
        let mut heap = Heap::new();
        for _ in 0..1000 {
            let h = slab.alloc(HeapNode::new(rng.next()));
            heap.link(&h);
            slab.free(h);
        }

        let mut popped: [Option<RcSlot<HeapNode<u64>>>; BATCH] = std::array::from_fn(|_| None);
        let mut samples = Vec::with_capacity(SAMPLES);

        for _ in 0..WARMUP {
            let s = rdtsc_start();
            seq!(I in 0..100 { popped[I] = heap.pop(); });
            let e = rdtsc_end();
            black_box(e - s);
            // Free popped handles, then replenish
            for slot in &mut popped {
                if let Some(h) = slot.take() {
                    slab.free(h);
                }
            }
            for _ in 0..BATCH {
                let h = slab.alloc(HeapNode::new(rng.next()));
                heap.link(&h);
                slab.free(h);
            }
        }

        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            seq!(I in 0..100 { popped[I] = heap.pop(); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH as u64);
            for slot in &mut popped {
                if let Some(h) = slot.take() {
                    slab.free(h);
                }
            }
            for _ in 0..BATCH {
                let h = slab.alloc(HeapNode::new(rng.next()));
                heap.link(&h);
                slab.free(h);
            }
        }
        print_row("pop (@1000 steady)", &mut samples);

        heap.clear(&slab);
    }

    println!();

    // ── UNLINK (batched) ────────────────────────────────────────────
    // Fill heap, then time unlinking specific handles.
    println!("UNLINK ({BATCH} unrolled ops/sample)");
    println!("---");

    {
        let mut heap = Heap::new();
        let mut samples = Vec::with_capacity(SAMPLES);

        for _ in 0..WARMUP {
            let handles: [RcSlot<HeapNode<u64>>; BATCH] =
                std::array::from_fn(|_| slab.alloc(HeapNode::new(rng.next())));
            for h in &handles {
                heap.link(h);
            }
            let s = rdtsc_start();
            seq!(I in 0..100 { heap.unlink(&handles[I], &slab); });
            let e = rdtsc_end();
            black_box(e - s);
            for h in handles {
                slab.free(h);
            }
        }

        for _ in 0..SAMPLES {
            let handles: [RcSlot<HeapNode<u64>>; BATCH] =
                std::array::from_fn(|_| slab.alloc(HeapNode::new(rng.next())));
            for h in &handles {
                heap.link(h);
            }
            let s = rdtsc_start();
            seq!(I in 0..100 { heap.unlink(&handles[I], &slab); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH as u64);
            for h in handles {
                slab.free(h);
            }
        }
        print_row("unlink (from 100)", &mut samples);
    }

    // Unlink from steady-state heap
    {
        let mut heap = Heap::new();
        let steady: Vec<RcSlot<HeapNode<u64>>> = (0..1000)
            .map(|_| {
                let h = slab.alloc(HeapNode::new(rng.next()));
                heap.link(&h);
                h
            })
            .collect();

        let mut samples = Vec::with_capacity(SAMPLES);

        for _ in 0..WARMUP {
            let handles: [RcSlot<HeapNode<u64>>; BATCH] =
                std::array::from_fn(|_| slab.alloc(HeapNode::new(rng.next())));
            for h in &handles {
                heap.link(h);
            }
            let s = rdtsc_start();
            seq!(I in 0..100 { heap.unlink(&handles[I], &slab); });
            let e = rdtsc_end();
            black_box(e - s);
            for h in handles {
                slab.free(h);
            }
        }

        for _ in 0..SAMPLES {
            let handles: [RcSlot<HeapNode<u64>>; BATCH] =
                std::array::from_fn(|_| slab.alloc(HeapNode::new(rng.next())));
            for h in &handles {
                heap.link(h);
            }
            let s = rdtsc_start();
            seq!(I in 0..100 { heap.unlink(&handles[I], &slab); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH as u64);
            for h in handles {
                slab.free(h);
            }
        }
        print_row("unlink (@1000 steady)", &mut samples);

        heap.clear(&slab);
        for h in steady {
            slab.free(h);
        }
    }

    println!();

    // ── TRY_PUSH (alloc + link combined, batched) ───────────────────
    println!("TRY_PUSH (alloc+link, {BATCH} unrolled ops/sample)");
    println!("---");

    {
        let mut heap = Heap::new();
        let mut samples = Vec::with_capacity(SAMPLES);
        let mut buf: [Option<RcSlot<HeapNode<u64>>>; BATCH] = std::array::from_fn(|_| None);

        for _ in 0..WARMUP {
            let s = rdtsc_start();
            seq!(I in 0..100 { buf[I] = heap.try_push(&slab, rng.next()).ok(); });
            let e = rdtsc_end();
            black_box(e - s);
            heap.clear(&slab);
            for slot in &mut buf {
                if let Some(h) = slot.take() {
                    slab.free(h);
                }
            }
        }

        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            seq!(I in 0..100 { buf[I] = heap.try_push(&slab, rng.next()).ok(); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH as u64);
            heap.clear(&slab);
            for slot in &mut buf {
                if let Some(h) = slot.take() {
                    slab.free(h);
                }
            }
        }
        print_row("try_push (empty)", &mut samples);
    }

    println!();

    // ── PEEK (batched read-only) ────────────────────────────────────
    println!("PEEK ({BATCH} unrolled ops/sample)");
    println!("---");

    {
        let mut heap = Heap::new();
        let peek_handles: Vec<RcSlot<HeapNode<u64>>> = (0..1000)
            .map(|_| {
                let h = slab.alloc(HeapNode::new(rng.next()));
                heap.link(&h);
                h
            })
            .collect();

        let mut samples = Vec::with_capacity(SAMPLES);

        for _ in 0..WARMUP {
            seq!(_ in 0..100 { black_box(heap.peek()); });
        }
        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            seq!(_ in 0..100 { black_box(heap.peek()); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH as u64);
        }
        print_row("peek (@1000)", &mut samples);

        heap.clear(&slab);
        for h in peek_handles {
            slab.free(h);
        }
    }
}
