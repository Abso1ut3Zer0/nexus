#![allow(clippy::unnecessary_semicolon, clippy::unnecessary_cast)]
//! List benchmark: batched, unrolled cycle-accurate latency measurement.
//!
//! Uses `seq_macro::seq!` for compile-time unroll of 100 ops per sample
//! to amortize rdtsc overhead. Same methodology as perf_rbtree.rs.
//!
//! Run with:
//!   cargo build --release --example perf_list_cycles -p nexus-collections
//!   taskset -c 0 ./target/release/examples/perf_list_cycles

use seq_macro::seq;
use std::hint::black_box;

use nexus_collections::slab::RcSlot;
use nexus_collections::slab::list::{List, ListNode};
use nexus_slab::rc::bounded::Slab;

const CAPACITY: usize = 200_000;
const SAMPLES: usize = 50_000;
const WARMUP: usize = 5_000;
const BATCH: usize = 100;

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
    let slab = unsafe { Slab::<ListNode<u64>>::with_capacity(CAPACITY) };

    println!("LIST OPERATION LATENCY (cycles/op) — batched, {BATCH} ops/sample");
    println!("Samples: {SAMPLES}, Warmup: {WARMUP}");
    println!("====================================================================\n");

    // ── LINK_BACK (batched) ─────────────────────────────────────────
    // Pre-allocate 100 handles, time linking all, then pop all to reset.
    println!("LINK ({BATCH} unrolled ops/sample)");
    println!("---");

    {
        let mut list = List::new();
        let mut samples = Vec::with_capacity(SAMPLES);

        for _ in 0..WARMUP {
            let handles: [RcSlot<ListNode<u64>>; BATCH] =
                std::array::from_fn(|i| slab.alloc(ListNode::new(i as u64)));
            let s = rdtsc_start();
            seq!(I in 0..100 { list.link_back(&handles[I]); });
            let e = rdtsc_end();
            black_box(e - s);
            // Pop all to reset (returns handles, then free them)
            for _ in 0..BATCH {
                if let Some(h) = list.pop_front() {
                    slab.free(h);
                }
            }
            // Free user handles
            for h in handles {
                slab.free(h);
            }
        }

        for _ in 0..SAMPLES {
            let handles: [RcSlot<ListNode<u64>>; BATCH] =
                std::array::from_fn(|i| slab.alloc(ListNode::new(i as u64)));
            let s = rdtsc_start();
            seq!(I in 0..100 { list.link_back(&handles[I]); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH as u64);
            for _ in 0..BATCH {
                if let Some(h) = list.pop_front() {
                    slab.free(h);
                }
            }
            for h in handles {
                slab.free(h);
            }
        }
        print_row("link_back (empty list)", &mut samples);
    }

    // link_back into steady-state list (~1000 elements)
    {
        let mut list = List::new();
        // Fill with steady-state population
        let steady: Vec<RcSlot<ListNode<u64>>> = (0..1000)
            .map(|i| {
                let h = slab.alloc(ListNode::new(i as u64));
                list.link_back(&h);
                h
            })
            .collect();

        let mut samples = Vec::with_capacity(SAMPLES);

        for _ in 0..WARMUP {
            let handles: [RcSlot<ListNode<u64>>; BATCH] =
                std::array::from_fn(|i| slab.alloc(ListNode::new(i as u64)));
            let s = rdtsc_start();
            seq!(I in 0..100 { list.link_back(&handles[I]); });
            let e = rdtsc_end();
            black_box(e - s);
            for _ in 0..BATCH {
                if let Some(h) = list.pop_back() {
                    slab.free(h);
                }
            }
            for h in handles {
                slab.free(h);
            }
        }

        for _ in 0..SAMPLES {
            let handles: [RcSlot<ListNode<u64>>; BATCH] =
                std::array::from_fn(|i| slab.alloc(ListNode::new(i as u64)));
            let s = rdtsc_start();
            seq!(I in 0..100 { list.link_back(&handles[I]); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH as u64);
            for _ in 0..BATCH {
                if let Some(h) = list.pop_back() {
                    slab.free(h);
                }
            }
            for h in handles {
                slab.free(h);
            }
        }
        print_row("link_back (@1000)", &mut samples);

        // Cleanup steady-state
        list.clear(&slab);
        for h in steady {
            slab.free(h);
        }
    }

    // link_front (empty list)
    {
        let mut list = List::new();
        let mut samples = Vec::with_capacity(SAMPLES);

        for _ in 0..WARMUP {
            let handles: [RcSlot<ListNode<u64>>; BATCH] =
                std::array::from_fn(|i| slab.alloc(ListNode::new(i as u64)));
            let s = rdtsc_start();
            seq!(I in 0..100 { list.link_front(&handles[I]); });
            let e = rdtsc_end();
            black_box(e - s);
            for _ in 0..BATCH {
                if let Some(h) = list.pop_front() {
                    slab.free(h);
                }
            }
            for h in handles {
                slab.free(h);
            }
        }

        for _ in 0..SAMPLES {
            let handles: [RcSlot<ListNode<u64>>; BATCH] =
                std::array::from_fn(|i| slab.alloc(ListNode::new(i as u64)));
            let s = rdtsc_start();
            seq!(I in 0..100 { list.link_front(&handles[I]); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH as u64);
            for _ in 0..BATCH {
                if let Some(h) = list.pop_front() {
                    slab.free(h);
                }
            }
            for h in handles {
                slab.free(h);
            }
        }
        print_row("link_front (empty list)", &mut samples);
    }

    println!();

    // ── POP (batched) ───────────────────────────────────────────────
    println!("POP ({BATCH} unrolled ops/sample)");
    println!("---");

    // pop_front: push 100, then time popping all 100
    {
        let mut list = List::new();
        let mut popped: [Option<RcSlot<ListNode<u64>>>; BATCH] = std::array::from_fn(|_| None);
        let mut samples = Vec::with_capacity(SAMPLES);

        for _ in 0..WARMUP {
            // Setup: push 100
            let handles: [RcSlot<ListNode<u64>>; BATCH] =
                std::array::from_fn(|i| slab.alloc(ListNode::new(i as u64)));
            for h in &handles {
                list.link_back(h);
            }
            let s = rdtsc_start();
            seq!(I in 0..100 { popped[I] = list.pop_front(); });
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
            let handles: [RcSlot<ListNode<u64>>; BATCH] =
                std::array::from_fn(|i| slab.alloc(ListNode::new(i as u64)));
            for h in &handles {
                list.link_back(h);
            }
            let s = rdtsc_start();
            seq!(I in 0..100 { popped[I] = list.pop_front(); });
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
        print_row("pop_front", &mut samples);
    }

    // pop_back: push 100, then time popping all 100
    {
        let mut list = List::new();
        let mut popped: [Option<RcSlot<ListNode<u64>>>; BATCH] = std::array::from_fn(|_| None);
        let mut samples = Vec::with_capacity(SAMPLES);

        for _ in 0..WARMUP {
            let handles: [RcSlot<ListNode<u64>>; BATCH] =
                std::array::from_fn(|i| slab.alloc(ListNode::new(i as u64)));
            for h in &handles {
                list.link_back(h);
            }
            let s = rdtsc_start();
            seq!(I in 0..100 { popped[I] = list.pop_back(); });
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
            let handles: [RcSlot<ListNode<u64>>; BATCH] =
                std::array::from_fn(|i| slab.alloc(ListNode::new(i as u64)));
            for h in &handles {
                list.link_back(h);
            }
            let s = rdtsc_start();
            seq!(I in 0..100 { popped[I] = list.pop_back(); });
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
        print_row("pop_back", &mut samples);
    }

    println!();

    // ── UNLINK (batched) ────────────────────────────────────────────
    // Push 100 keeping handles, then time unlinking all 100.
    // unlink = unwire + free the list's refcount. Our handle still alive.
    println!("UNLINK ({BATCH} unrolled ops/sample)");
    println!("---");

    {
        let mut list = List::new();
        let mut samples = Vec::with_capacity(SAMPLES);

        for _ in 0..WARMUP {
            let handles: [RcSlot<ListNode<u64>>; BATCH] =
                std::array::from_fn(|i| slab.alloc(ListNode::new(i as u64)));
            for h in &handles {
                list.link_back(h);
            }
            let s = rdtsc_start();
            seq!(I in 0..100 { list.unlink(&handles[I], &slab); });
            let e = rdtsc_end();
            black_box(e - s);
            for h in handles {
                slab.free(h);
            }
        }

        for _ in 0..SAMPLES {
            let handles: [RcSlot<ListNode<u64>>; BATCH] =
                std::array::from_fn(|i| slab.alloc(ListNode::new(i as u64)));
            for h in &handles {
                list.link_back(h);
            }
            let s = rdtsc_start();
            seq!(I in 0..100 { list.unlink(&handles[I], &slab); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH as u64);
            for h in handles {
                slab.free(h);
            }
        }
        print_row("unlink (from front)", &mut samples);
    }

    // Unlink from middle of a steady-state list
    {
        let mut list = List::new();
        // Steady-state: 1000 nodes
        let steady: Vec<RcSlot<ListNode<u64>>> = (0..1000)
            .map(|i| {
                let h = slab.alloc(ListNode::new(i as u64));
                list.link_back(&h);
                h
            })
            .collect();

        let mut samples = Vec::with_capacity(SAMPLES);

        for _ in 0..WARMUP {
            // Append 100 to end, then unlink them
            let handles: [RcSlot<ListNode<u64>>; BATCH] =
                std::array::from_fn(|i| slab.alloc(ListNode::new((1000 + i) as u64)));
            for h in &handles {
                list.link_back(h);
            }
            let s = rdtsc_start();
            seq!(I in 0..100 { list.unlink(&handles[I], &slab); });
            let e = rdtsc_end();
            black_box(e - s);
            for h in handles {
                slab.free(h);
            }
        }

        for _ in 0..SAMPLES {
            let handles: [RcSlot<ListNode<u64>>; BATCH] =
                std::array::from_fn(|i| slab.alloc(ListNode::new((1000 + i) as u64)));
            for h in &handles {
                list.link_back(h);
            }
            let s = rdtsc_start();
            seq!(I in 0..100 { list.unlink(&handles[I], &slab); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH as u64);
            for h in handles {
                slab.free(h);
            }
        }
        print_row("unlink (@1000 steady)", &mut samples);

        list.clear(&slab);
        for h in steady {
            slab.free(h);
        }
    }

    println!();

    // ── TRY_PUSH (alloc + link combined, batched) ───────────────────
    println!("TRY_PUSH (alloc+link, {BATCH} unrolled ops/sample)");
    println!("---");

    {
        let mut list = List::new();
        let mut samples = Vec::with_capacity(SAMPLES);
        let mut buf: [Option<RcSlot<ListNode<u64>>>; BATCH] = std::array::from_fn(|_| None);

        for _ in 0..WARMUP {
            let s = rdtsc_start();
            seq!(I in 0..100 { buf[I] = list.try_push_back(&slab, I as u64).ok(); });
            let e = rdtsc_end();
            black_box(e - s);
            list.clear(&slab);
            for slot in &mut buf {
                if let Some(h) = slot.take() {
                    slab.free(h);
                }
            }
        }

        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            seq!(I in 0..100 { buf[I] = list.try_push_back(&slab, I as u64).ok(); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH as u64);
            list.clear(&slab);
            for slot in &mut buf {
                if let Some(h) = slot.take() {
                    slab.free(h);
                }
            }
        }
        print_row("try_push_back (empty)", &mut samples);
    }

    println!();

    // ── FRONT/BACK peek (batched read-only) ─────────────────────────
    println!("PEEK ({BATCH} unrolled ops/sample)");
    println!("---");

    {
        let mut list = List::new();
        let peek_handles: Vec<RcSlot<ListNode<u64>>> = (0..1000)
            .map(|i| {
                let h = slab.alloc(ListNode::new(i as u64));
                list.link_back(&h);
                h
            })
            .collect();

        let mut samples = Vec::with_capacity(SAMPLES);

        for _ in 0..WARMUP {
            seq!(_ in 0..100 { black_box(list.front()); });
        }
        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            seq!(_ in 0..100 { black_box(list.front()); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH as u64);
        }
        print_row("front (@1000)", &mut samples);

        let mut samples = Vec::with_capacity(SAMPLES);
        for _ in 0..WARMUP {
            seq!(_ in 0..100 { black_box(list.back()); });
        }
        for _ in 0..SAMPLES {
            let s = rdtsc_start();
            seq!(_ in 0..100 { black_box(list.back()); });
            let e = rdtsc_end();
            samples.push((e - s) / BATCH as u64);
        }
        print_row("back (@1000)", &mut samples);

        list.clear(&slab);
        for h in peek_handles {
            slab.free(h);
        }
    }
}
