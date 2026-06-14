//! HDR histogram benchmark for all critical heap + list operations.
//!
//! Measures each operation in isolation with rdtscp per-op timing.
//!
//! Run with:
//!   cargo build --release --example perf_push_hist
//!   taskset -c 0 ./target/release/examples/perf_push_hist

use hdrhistogram::Histogram;
use std::hint::black_box;

use nexus_collections::slab::RcSlot;
use nexus_collections::slab::heap::{Heap, HeapNode};
use nexus_collections::slab::list::{List, ListNode};
use nexus_slab::rc::bounded::Slab;

const CAPACITY: usize = 100_000;
const N: usize = 50_000;

#[inline(always)]
fn rdtscp() -> u64 {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        let mut aux: u32 = 0;
        std::arch::x86_64::__rdtscp(&raw mut aux)
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        panic!("rdtscp only supported on x86_64");
    }
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

fn print_hist(label: &str, hist: &Histogram<u64>) {
    println!(
        "  {:<24} p50={:>5}  p90={:>5}  p99={:>5}  p999={:>6}  max={:>8}  (n={})",
        label,
        hist.value_at_quantile(0.50),
        hist.value_at_quantile(0.90),
        hist.value_at_quantile(0.99),
        hist.value_at_quantile(0.999),
        hist.max(),
        hist.len()
    );
}

fn new_hist() -> Histogram<u64> {
    Histogram::new(3).unwrap()
}

fn main() {
    let heap_slab = unsafe { Slab::<HeapNode<u64>>::with_capacity(CAPACITY) };
    let list_slab = unsafe { Slab::<ListNode<u64>>::with_capacity(CAPACITY) };

    let mut rng = Xorshift::new(0xDEAD_BEEF_CAFE_BABEu64);

    // Pre-allocate heap handles
    let heap_handles: Vec<RcSlot<HeapNode<u64>>> = (0..N)
        .map(|_| heap_slab.alloc(HeapNode::new(rng.next())))
        .collect();

    // Pre-allocate list handles
    let list_handles: Vec<RcSlot<ListNode<u64>>> = (0..N)
        .map(|_| list_slab.alloc(ListNode::new(rng.next())))
        .collect();

    println!("OPERATION LATENCY (cycles) — all critical methods");
    println!("================================================================\n");

    // =================================================================
    // HEAP
    // =================================================================
    println!("HEAP");
    println!("----");

    // heap push (growing)
    {
        let mut heap = Heap::new();
        let mut hist = new_hist();
        // warmup
        for h in heap_handles.iter().take(5000) {
            heap.link(h);
        }
        heap.clear(&heap_slab);
        // measure
        for h in &heap_handles {
            let s = rdtscp();
            heap.link(h);
            let e = rdtscp();
            let _ = hist.record(e.wrapping_sub(s));
        }
        print_hist("push (growing)", &hist);
        heap.clear(&heap_slab);
    }

    // heap push (steady-state push-pop)
    {
        let mut heap = Heap::new();
        let mut hist = new_hist();
        let half = N / 2;
        for h in heap_handles.iter().take(half) {
            heap.link(h);
        }
        for h in heap_handles.iter().skip(half) {
            let s = rdtscp();
            heap.link(h);
            let e = rdtscp();
            let _ = hist.record(e.wrapping_sub(s));
            if let Some(p) = heap.pop() {
                black_box(&p);
                heap_slab.free(p);
            }
        }
        print_hist("push (steady @25k)", &hist);
        heap.clear(&heap_slab);
    }

    // heap pop
    {
        let mut heap = Heap::new();
        let mut hist = new_hist();
        for h in &heap_handles {
            heap.link(h);
        }
        while !heap.is_empty() {
            let s = rdtscp();
            let p = heap.pop();
            let e = rdtscp();
            let _ = hist.record(e.wrapping_sub(s));
            if let Some(p) = p {
                black_box(&p);
                heap_slab.free(p);
            }
        }
        print_hist("pop (drain 50k)", &hist);
    }

    // heap unlink (all elements, arbitrary order)
    {
        let mut heap = Heap::new();
        let mut hist = new_hist();
        for h in &heap_handles {
            heap.link(h);
        }
        for h in &heap_handles {
            let s = rdtscp();
            heap.unlink(h, &heap_slab);
            let e = rdtscp();
            let _ = hist.record(e.wrapping_sub(s));
        }
        print_hist("unlink (all, arb order)", &hist);
    }

    // heap unlink_unchecked
    {
        let mut heap = Heap::new();
        let mut hist = new_hist();
        for h in &heap_handles {
            heap.link(h);
        }
        for h in &heap_handles {
            let s = rdtscp();
            unsafe { heap.unlink_unchecked(h, &heap_slab) };
            let e = rdtscp();
            let _ = hist.record(e.wrapping_sub(s));
        }
        print_hist("unlink_unchk (all, arb)", &hist);
    }

    // heap try_push (allocation + link)
    {
        let mut heap = Heap::new();
        let mut hist = new_hist();
        let mut rng2 = Xorshift::new(0xCAFE_BABE_DEAD_BEEFu64);
        // warmup: fill and drain to warm slab freelist
        for _ in 0..5000 {
            let _ = heap.try_push(&heap_slab, rng2.next());
        }
        heap.clear(&heap_slab);
        // measure
        for _ in 0..N {
            let val = rng2.next();
            let s = rdtscp();
            let _h = heap.try_push(&heap_slab, val).unwrap();
            let e = rdtscp();
            let _ = hist.record(e.wrapping_sub(s));
            heap.clear(&heap_slab);
        }
        print_hist("try_push (alloc+link)", &hist);
    }

    // heap peek
    {
        let mut heap = Heap::new();
        let mut hist = new_hist();
        for h in heap_handles.iter().take(N / 2) {
            heap.link(h);
        }
        for _ in 0..N {
            let s = rdtscp();
            let _ = black_box(heap.peek());
            let e = rdtscp();
            let _ = hist.record(e.wrapping_sub(s));
        }
        print_hist("peek", &hist);
        heap.clear(&heap_slab);
    }

    println!();

    // =================================================================
    // LIST
    // =================================================================
    println!("LIST");
    println!("----");

    // list link_back (growing)
    {
        let mut list = List::new();
        let mut hist = new_hist();
        for h in list_handles.iter().take(5000) {
            list.link_back(h);
        }
        list.clear(&list_slab);
        for h in &list_handles {
            let s = rdtscp();
            list.link_back(h);
            let e = rdtscp();
            let _ = hist.record(e.wrapping_sub(s));
        }
        print_hist("link_back (growing)", &hist);
        list.clear(&list_slab);
    }

    // list link_front (growing)
    {
        let mut list = List::new();
        let mut hist = new_hist();
        for h in list_handles.iter().take(5000) {
            list.link_front(h);
        }
        list.clear(&list_slab);
        for h in &list_handles {
            let s = rdtscp();
            list.link_front(h);
            let e = rdtscp();
            let _ = hist.record(e.wrapping_sub(s));
        }
        print_hist("link_front (growing)", &hist);
        list.clear(&list_slab);
    }

    // list link_back (steady-state push-pop)
    {
        let mut list = List::new();
        let mut hist = new_hist();
        let half = N / 2;
        for h in list_handles.iter().take(half) {
            list.link_back(h);
        }
        for h in list_handles.iter().skip(half) {
            let s = rdtscp();
            list.link_back(h);
            let e = rdtscp();
            let _ = hist.record(e.wrapping_sub(s));
            if let Some(p) = list.pop_front() {
                black_box(&p);
                list_slab.free(p);
            }
        }
        print_hist("link_back (steady @25k)", &hist);
        list.clear(&list_slab);
    }

    // list pop_front
    {
        let mut list = List::new();
        let mut hist = new_hist();
        for h in &list_handles {
            list.link_back(h);
        }
        while !list.is_empty() {
            let s = rdtscp();
            let p = list.pop_front();
            let e = rdtscp();
            let _ = hist.record(e.wrapping_sub(s));
            if let Some(p) = p {
                black_box(&p);
                list_slab.free(p);
            }
        }
        print_hist("pop_front (drain 50k)", &hist);
    }

    // list pop_back
    {
        let mut list = List::new();
        let mut hist = new_hist();
        for h in &list_handles {
            list.link_back(h);
        }
        while !list.is_empty() {
            let s = rdtscp();
            let p = list.pop_back();
            let e = rdtscp();
            let _ = hist.record(e.wrapping_sub(s));
            if let Some(p) = p {
                black_box(&p);
                list_slab.free(p);
            }
        }
        print_hist("pop_back (drain 50k)", &hist);
    }

    // list unlink (arbitrary order)
    {
        let mut list = List::new();
        let mut hist = new_hist();
        for h in &list_handles {
            list.link_back(h);
        }
        for h in &list_handles {
            let s = rdtscp();
            list.unlink(h, &list_slab);
            let e = rdtscp();
            let _ = hist.record(e.wrapping_sub(s));
        }
        print_hist("unlink (all, arb order)", &hist);
    }

    // list unlink_unchecked (arbitrary order)
    {
        let mut list = List::new();
        let mut hist = new_hist();
        for h in &list_handles {
            list.link_back(h);
        }
        for h in &list_handles {
            let s = rdtscp();
            unsafe { list.unlink_unchecked(h, &list_slab) };
            let e = rdtscp();
            let _ = hist.record(e.wrapping_sub(s));
        }
        print_hist("unlink_unchk (all, arb)", &hist);
    }

    // list move_to_front (from random positions)
    {
        let mut list = List::new();
        let mut hist = new_hist();
        for h in &list_handles {
            list.link_back(h);
        }
        for h in &list_handles {
            let s = rdtscp();
            list.move_to_front(h);
            let e = rdtscp();
            let _ = hist.record(e.wrapping_sub(s));
        }
        print_hist("move_to_front (all)", &hist);
        list.clear(&list_slab);
    }

    // list move_to_front_unchecked
    {
        let mut list = List::new();
        let mut hist = new_hist();
        for h in &list_handles {
            list.link_back(h);
        }
        for h in &list_handles {
            let s = rdtscp();
            unsafe { list.move_to_front_unchecked(h) };
            let e = rdtscp();
            let _ = hist.record(e.wrapping_sub(s));
        }
        print_hist("move_front_unchk (all)", &hist);
        list.clear(&list_slab);
    }

    // list move_to_back (from random positions)
    {
        let mut list = List::new();
        let mut hist = new_hist();
        for h in &list_handles {
            list.link_back(h);
        }
        for h in list_handles.iter().rev() {
            let s = rdtscp();
            list.move_to_back(h);
            let e = rdtscp();
            let _ = hist.record(e.wrapping_sub(s));
        }
        print_hist("move_to_back (all)", &hist);
        list.clear(&list_slab);
    }

    // list move_to_back_unchecked
    {
        let mut list = List::new();
        let mut hist = new_hist();
        for h in &list_handles {
            list.link_back(h);
        }
        for h in list_handles.iter().rev() {
            let s = rdtscp();
            unsafe { list.move_to_back_unchecked(h) };
            let e = rdtscp();
            let _ = hist.record(e.wrapping_sub(s));
        }
        print_hist("move_back_unchk (all)", &hist);
        list.clear(&list_slab);
    }

    // list try_push_back (allocation + link)
    {
        let mut list = List::new();
        let mut hist = new_hist();
        let mut rng2 = Xorshift::new(0xCAFE_BABE_DEAD_BEEFu64);
        // warmup: fill and drain to warm slab freelist
        for _ in 0..5000 {
            let _ = list.try_push_back(&list_slab, rng2.next());
        }
        list.clear(&list_slab);
        // measure
        for _ in 0..N {
            let val = rng2.next();
            let s = rdtscp();
            let _h = list.try_push_back(&list_slab, val).unwrap();
            let e = rdtscp();
            let _ = hist.record(e.wrapping_sub(s));
            list.clear(&list_slab);
        }
        print_hist("try_push_back (alloc+lnk)", &hist);
    }
}
