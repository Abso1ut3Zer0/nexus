#![allow(clippy::unnecessary_semicolon, clippy::collection_is_never_read)]
//! Batched benchmark: 100 unrolled ops per sample to amortize rdtsc overhead.
//!
//! The per-op HDR histogram (perf_push_hist) wraps each individual op in
//! rdtsc_start/rdtsc_end. With rdtsc costing ~18-20 cycles and list ops
//! measuring at p50=20-22, the measurement overhead dominates. This benchmark
//! times 100 straight-line (seq!-unrolled) ops per sample and divides by 100,
//! giving sub-cycle resolution on the actual work.
//!
//! Run with:
//!   cargo build --release --example perf_batched
//!   taskset -c 0 ./target/release/examples/perf_batched

use seq_macro::seq;
use std::hint::black_box;

use nexus_collections::slab::RcSlot;
use nexus_collections::slab::heap::{Heap, HeapNode};
use nexus_collections::slab::list::{List, ListNode};
use nexus_slab::rc::bounded::Slab;

const CAPACITY: usize = 200_000;
const SAMPLES: usize = 50_000;
const WARMUP: usize = 5_000;
const BATCH: usize = 100;
const STEADY_SIZE: usize = 25_000;

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
        "  {:<26} p50={:>4}  p90={:>4}  p99={:>5}  p999={:>6}  max={:>8}",
        label,
        percentile(samples, 50.0),
        percentile(samples, 90.0),
        percentile(samples, 99.0),
        percentile(samples, 99.9),
        samples[samples.len() - 1],
    );
}

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
    let heap_slab = unsafe { Slab::<HeapNode<u64>>::with_capacity(CAPACITY) };
    let list_slab = unsafe { Slab::<ListNode<u64>>::with_capacity(CAPACITY) };

    let mut rng = Xorshift::new(0xDEAD_BEEF_CAFE_BABEu64);

    // Pre-allocate heap handles
    let heap_steady: Vec<RcSlot<HeapNode<u64>>> = (0..STEADY_SIZE)
        .map(|_| heap_slab.alloc(HeapNode::new(rng.next())))
        .collect();
    let heap_batch: Vec<RcSlot<HeapNode<u64>>> = (0..BATCH)
        .map(|_| heap_slab.alloc(HeapNode::new(rng.next())))
        .collect();
    let list_steady: Vec<RcSlot<ListNode<u64>>> = (0..STEADY_SIZE)
        .map(|_| list_slab.alloc(ListNode::new(rng.next())))
        .collect();
    let list_batch: Vec<RcSlot<ListNode<u64>>> = (0..BATCH)
        .map(|_| list_slab.alloc(ListNode::new(rng.next())))
        .collect();

    println!(
        "BATCHED OPERATION LATENCY (cycles/op) — {} unrolled ops per sample",
        BATCH
    );
    println!("Samples: {SAMPLES}, Warmup: {WARMUP}");
    println!("================================================================\n");

    // ── HEAP ──────────────────────────────────────────────────────────
    println!("HEAP");
    println!("----");

    // push (growing from empty)
    {
        let mut heap = Heap::new();
        let h = &heap_batch;
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            seq!(I in 0..100 { heap.link(&h[I]); });
            heap.clear(&heap_slab);
        }
        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            seq!(I in 0..100 { heap.link(&h[I]); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH as u64);
            heap.clear(&heap_slab);
        }
        print_row("push (growing)", &mut samples);
    }

    // push (steady @25k)
    {
        let mut heap = Heap::new();
        for h in &heap_steady {
            heap.link(h);
        }
        let h = &heap_batch;
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            seq!(I in 0..100 { heap.link(&h[I]); });
            for hh in h {
                heap.unlink(hh, &heap_slab);
            }
        }
        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            seq!(I in 0..100 { heap.link(&h[I]); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH as u64);
            for hh in h {
                heap.unlink(hh, &heap_slab);
            }
        }
        print_row("push (steady @25k)", &mut samples);
        heap.clear(&heap_slab);
    }

    // pop (from 100 elements, hot cache)
    {
        let mut heap = Heap::new();
        let h = &heap_batch;
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            seq!(I in 0..100 { heap.link(&h[I]); });
            seq!(_ in 0..100 { if let Some(p) = heap.pop() { black_box(&p); heap_slab.free(p); } });
        }
        for _ in 0..SAMPLES {
            seq!(I in 0..100 { heap.link(&h[I]); });
            let s = rdtsc_start();
            seq!(_ in 0..100 { if let Some(p) = heap.pop() { black_box(&p); heap_slab.free(p); } });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH as u64);
        }
        print_row("pop (100 elems)", &mut samples);
    }

    // unlink (from 100 elements)
    {
        let mut heap = Heap::new();
        let h = &heap_batch;
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            seq!(I in 0..100 { heap.link(&h[I]); });
            seq!(I in 0..100 { heap.unlink(&h[I], &heap_slab); });
        }
        for _ in 0..SAMPLES {
            seq!(I in 0..100 { heap.link(&h[I]); });
            let s = rdtsc_start();
            seq!(I in 0..100 { heap.unlink(&h[I], &heap_slab); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH as u64);
        }
        print_row("unlink (100 elems)", &mut samples);
    }

    // unlink_unchecked (from 100 elements)
    {
        let mut heap = Heap::new();
        let h = &heap_batch;
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            seq!(I in 0..100 { heap.link(&h[I]); });
            seq!(I in 0..100 { unsafe { heap.unlink_unchecked(&h[I], &heap_slab) }; });
        }
        for _ in 0..SAMPLES {
            seq!(I in 0..100 { heap.link(&h[I]); });
            let s = rdtsc_start();
            seq!(I in 0..100 { unsafe { heap.unlink_unchecked(&h[I], &heap_slab) }; });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH as u64);
        }
        print_row("unlink_unchecked (100)", &mut samples);
    }

    // try_push (allocation + link)
    {
        let mut heap = Heap::new();
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            let mut handles: Vec<RcSlot<HeapNode<u64>>> = Vec::with_capacity(BATCH);
            for i in 0..BATCH as u64 {
                handles.push(heap.try_push(&heap_slab, i).unwrap());
            }
            heap.clear(&heap_slab);
        }
        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            let _h0 = heap.try_push(&heap_slab, 0).unwrap();
            let _h1 = heap.try_push(&heap_slab, 1).unwrap();
            let e = rdtsc_end();
            samples.push((e - s) / 2);
            heap.clear(&heap_slab);
        }
        print_row("try_push (alloc+link)", &mut samples);
    }

    // peek
    {
        let mut heap = Heap::new();
        for h in heap_batch.iter().take(50) {
            heap.link(h);
        }
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
        print_row("peek", &mut samples);
        heap.clear(&heap_slab);
    }

    println!();

    // ── LIST ──────────────────────────────────────────────────────────
    println!("LIST");
    println!("----");

    // link_back (growing)
    {
        let mut list = List::new();
        let h = &list_batch;
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            seq!(I in 0..100 { list.link_back(&h[I]); });
            list.clear(&list_slab);
        }
        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            seq!(I in 0..100 { list.link_back(&h[I]); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH as u64);
            list.clear(&list_slab);
        }
        print_row("link_back (growing)", &mut samples);
    }

    // link_front (growing)
    {
        let mut list = List::new();
        let h = &list_batch;
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            seq!(I in 0..100 { list.link_front(&h[I]); });
            list.clear(&list_slab);
        }
        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            seq!(I in 0..100 { list.link_front(&h[I]); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH as u64);
            list.clear(&list_slab);
        }
        print_row("link_front (growing)", &mut samples);
    }

    // link_back (steady @25k)
    {
        let mut list = List::new();
        for h in &list_steady {
            list.link_back(h);
        }
        let h = &list_batch;
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            seq!(I in 0..100 { list.link_back(&h[I]); });
            for hh in h {
                list.unlink(hh, &list_slab);
            }
        }
        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            seq!(I in 0..100 { list.link_back(&h[I]); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH as u64);
            for hh in h {
                list.unlink(hh, &list_slab);
            }
        }
        print_row("link_back (steady @25k)", &mut samples);
        list.clear(&list_slab);
    }

    // pop_front
    {
        let mut list = List::new();
        let h = &list_batch;
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            seq!(I in 0..100 { list.link_back(&h[I]); });
            seq!(_ in 0..100 { if let Some(p) = list.pop_front() { black_box(&p); list_slab.free(p); } });
        }
        for _ in 0..SAMPLES {
            seq!(I in 0..100 { list.link_back(&h[I]); });
            let s = rdtsc_start();
            seq!(_ in 0..100 { if let Some(p) = list.pop_front() { black_box(&p); list_slab.free(p); } });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH as u64);
        }
        print_row("pop_front (100 elems)", &mut samples);
    }

    // pop_back
    {
        let mut list = List::new();
        let h = &list_batch;
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            seq!(I in 0..100 { list.link_back(&h[I]); });
            seq!(_ in 0..100 { if let Some(p) = list.pop_back() { black_box(&p); list_slab.free(p); } });
        }
        for _ in 0..SAMPLES {
            seq!(I in 0..100 { list.link_back(&h[I]); });
            let s = rdtsc_start();
            seq!(_ in 0..100 { if let Some(p) = list.pop_back() { black_box(&p); list_slab.free(p); } });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH as u64);
        }
        print_row("pop_back (100 elems)", &mut samples);
    }

    // unlink
    {
        let mut list = List::new();
        let h = &list_batch;
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            seq!(I in 0..100 { list.link_back(&h[I]); });
            seq!(I in 0..100 { list.unlink(&h[I], &list_slab); });
        }
        for _ in 0..SAMPLES {
            seq!(I in 0..100 { list.link_back(&h[I]); });
            let s = rdtsc_start();
            seq!(I in 0..100 { list.unlink(&h[I], &list_slab); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH as u64);
        }
        print_row("unlink (100 elems)", &mut samples);
    }

    // unlink_unchecked
    {
        let mut list = List::new();
        let h = &list_batch;
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            seq!(I in 0..100 { list.link_back(&h[I]); });
            seq!(I in 0..100 { unsafe { list.unlink_unchecked(&h[I], &list_slab) }; });
        }
        for _ in 0..SAMPLES {
            seq!(I in 0..100 { list.link_back(&h[I]); });
            let s = rdtsc_start();
            seq!(I in 0..100 { unsafe { list.unlink_unchecked(&h[I], &list_slab) }; });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH as u64);
        }
        print_row("unlink_unchecked (100)", &mut samples);
    }

    // move_to_front
    {
        let mut list = List::new();
        let h = &list_batch;
        seq!(I in 0..100 { list.link_back(&h[I]); });
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            seq!(I in 0..100 { list.move_to_front(&h[I]); });
        }
        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            seq!(I in 0..100 { list.move_to_front(&h[I]); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH as u64);
        }
        print_row("move_to_front (100)", &mut samples);
        list.clear(&list_slab);
    }

    // move_to_front_unchecked
    {
        let mut list = List::new();
        let h = &list_batch;
        seq!(I in 0..100 { list.link_back(&h[I]); });
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            seq!(I in 0..100 { unsafe { list.move_to_front_unchecked(&h[I]) }; });
        }
        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            seq!(I in 0..100 { unsafe { list.move_to_front_unchecked(&h[I]) }; });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH as u64);
        }
        print_row("move_front_unchecked", &mut samples);
        list.clear(&list_slab);
    }

    // move_to_back
    {
        let mut list = List::new();
        let h = &list_batch;
        seq!(I in 0..100 { list.link_back(&h[I]); });
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            seq!(I in 0..100 { list.move_to_back(&h[I]); });
        }
        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            seq!(I in 0..100 { list.move_to_back(&h[I]); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH as u64);
        }
        print_row("move_to_back (100)", &mut samples);
        list.clear(&list_slab);
    }

    // move_to_back_unchecked
    {
        let mut list = List::new();
        let h = &list_batch;
        seq!(I in 0..100 { list.link_back(&h[I]); });
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            seq!(I in 0..100 { unsafe { list.move_to_back_unchecked(&h[I]) }; });
        }
        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            seq!(I in 0..100 { unsafe { list.move_to_back_unchecked(&h[I]) }; });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH as u64);
        }
        print_row("move_back_unchecked", &mut samples);
        list.clear(&list_slab);
    }

    // try_push_back (allocation + link)
    {
        let mut list = List::new();
        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            for i in 0..BATCH as u64 {
                let _ = list.try_push_back(&list_slab, i);
            }
            list.clear(&list_slab);
        }
        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            let _h0 = list.try_push_back(&list_slab, 0).unwrap();
            let _h1 = list.try_push_back(&list_slab, 1).unwrap();
            let e = rdtsc_end();
            samples.push((e - s) / 2);
            list.clear(&list_slab);
        }
        print_row("try_push_back (alloc+lnk)", &mut samples);
    }
}
