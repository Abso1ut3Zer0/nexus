//! Codegen inspection: #[inline(never)] wrappers for all critical methods.
//!
//! Build with:
//!   cargo rustc --package nexus-collections --example perf_codegen --release -- --emit asm -C "llvm-args=-x86-asm-syntax=intel"
//!
//! Then grep for `do_` functions in the .s file.

use nexus_collections::slab::RcSlot;
use nexus_collections::slab::heap::{Heap, HeapNode};
use nexus_collections::slab::list::{List, ListNode};
use nexus_slab::rc::bounded::Slab;
use std::hint::black_box;

// =============================================================================
// Heap wrappers
// =============================================================================

#[inline(never)]
fn heap_link(heap: &mut Heap<u64>, h: &RcSlot<HeapNode<u64>>) {
    heap.link(h);
}

#[inline(never)]
unsafe fn heap_link_unchecked(heap: &mut Heap<u64>, h: &RcSlot<HeapNode<u64>>) {
    unsafe { heap.link_unchecked(h) };
}

#[inline(never)]
fn heap_pop(heap: &mut Heap<u64>) -> Option<RcSlot<HeapNode<u64>>> {
    heap.pop()
}

#[inline(never)]
fn heap_unlink(heap: &mut Heap<u64>, h: &RcSlot<HeapNode<u64>>, slab: &Slab<HeapNode<u64>>) {
    heap.unlink(h, slab);
}

#[inline(never)]
unsafe fn heap_unlink_unchecked(
    heap: &mut Heap<u64>,
    h: &RcSlot<HeapNode<u64>>,
    slab: &Slab<HeapNode<u64>>,
) {
    unsafe { heap.unlink_unchecked(h, slab) };
}

#[inline(never)]
fn heap_try_push(
    heap: &mut Heap<u64>,
    slab: &Slab<HeapNode<u64>>,
    val: u64,
) -> RcSlot<HeapNode<u64>> {
    heap.try_push(slab, val).unwrap()
}

#[inline(never)]
fn heap_peek(heap: &Heap<u64>) -> Option<&HeapNode<u64>> {
    heap.peek()
}

// =============================================================================
// List wrappers
// =============================================================================

#[inline(never)]
fn list_link_back(list: &mut List<u64>, h: &RcSlot<ListNode<u64>>) {
    list.link_back(h);
}

#[inline(never)]
unsafe fn list_link_back_unchecked(list: &mut List<u64>, h: &RcSlot<ListNode<u64>>) {
    unsafe { list.link_back_unchecked(h) };
}

#[inline(never)]
fn list_link_front(list: &mut List<u64>, h: &RcSlot<ListNode<u64>>) {
    list.link_front(h);
}

#[inline(never)]
unsafe fn list_link_front_unchecked(list: &mut List<u64>, h: &RcSlot<ListNode<u64>>) {
    unsafe { list.link_front_unchecked(h) };
}

#[inline(never)]
fn list_unlink(list: &mut List<u64>, h: &RcSlot<ListNode<u64>>, slab: &Slab<ListNode<u64>>) {
    list.unlink(h, slab);
}

#[inline(never)]
unsafe fn list_unlink_unchecked(
    list: &mut List<u64>,
    h: &RcSlot<ListNode<u64>>,
    slab: &Slab<ListNode<u64>>,
) {
    unsafe { list.unlink_unchecked(h, slab) };
}

#[inline(never)]
fn list_try_push_back(
    list: &mut List<u64>,
    slab: &Slab<ListNode<u64>>,
    val: u64,
) -> RcSlot<ListNode<u64>> {
    list.try_push_back(slab, val).unwrap()
}

#[inline(never)]
fn list_pop_front(list: &mut List<u64>) -> Option<RcSlot<ListNode<u64>>> {
    list.pop_front()
}

#[inline(never)]
fn list_pop_back(list: &mut List<u64>) -> Option<RcSlot<ListNode<u64>>> {
    list.pop_back()
}

#[inline(never)]
fn list_move_to_front(list: &mut List<u64>, h: &RcSlot<ListNode<u64>>) {
    list.move_to_front(h);
}

#[inline(never)]
unsafe fn list_move_to_front_unchecked(list: &mut List<u64>, h: &RcSlot<ListNode<u64>>) {
    unsafe { list.move_to_front_unchecked(h) };
}

#[inline(never)]
fn list_move_to_back(list: &mut List<u64>, h: &RcSlot<ListNode<u64>>) {
    list.move_to_back(h);
}

#[inline(never)]
unsafe fn list_move_to_back_unchecked(list: &mut List<u64>, h: &RcSlot<ListNode<u64>>) {
    unsafe { list.move_to_back_unchecked(h) };
}

fn main() {
    let heap_slab = unsafe { Slab::<HeapNode<u64>>::with_capacity(100) };
    let list_slab = unsafe { Slab::<ListNode<u64>>::with_capacity(100) };

    // Heap
    let mut heap = Heap::new();
    let h1 = heap_slab.alloc(HeapNode::new(10));
    let h2 = heap_slab.alloc(HeapNode::new(5));
    let h3 = heap_slab.alloc(HeapNode::new(20));

    heap_link(&mut heap, &h1);
    heap_link(&mut heap, &h2);
    heap_link(&mut heap, &h3);
    black_box(heap_peek(&heap));
    heap_unlink(&mut heap, &h3, &heap_slab);
    // unchecked link + unlink
    unsafe { heap_link_unchecked(&mut heap, &h3) };
    unsafe { heap_unlink_unchecked(&mut heap, &h2, &heap_slab) };
    unsafe { heap_unlink_unchecked(&mut heap, &h3, &heap_slab) };
    while let Some(p) = heap_pop(&mut heap) {
        black_box(p.borrow().value());
        heap_slab.free(p);
    }
    // try_push (allocation path)
    let hp = heap_try_push(&mut heap, &heap_slab, 42);
    black_box(hp.borrow().value());
    heap.clear(&heap_slab);

    // List
    let mut list = List::new();
    let l1 = list_slab.alloc(ListNode::new(10));
    let l2 = list_slab.alloc(ListNode::new(5));
    let l3 = list_slab.alloc(ListNode::new(20));
    let l4 = list_slab.alloc(ListNode::new(30));

    list_link_back(&mut list, &l1);
    list_link_back(&mut list, &l2);
    list_link_front(&mut list, &l3);
    list_link_back(&mut list, &l4);
    list_move_to_front(&mut list, &l2);
    unsafe { list_move_to_front_unchecked(&mut list, &l4) };
    list_move_to_back(&mut list, &l3);
    unsafe { list_move_to_back_unchecked(&mut list, &l1) };
    list_unlink(&mut list, &l4, &list_slab);
    // unchecked link variants
    unsafe { list_link_back_unchecked(&mut list, &l4) };
    list_unlink(&mut list, &l4, &list_slab);
    unsafe { list_link_front_unchecked(&mut list, &l4) };
    unsafe { list_unlink_unchecked(&mut list, &l4, &list_slab) };
    while let Some(p) = list_pop_front(&mut list) {
        black_box(&p.borrow().value);
        list_slab.free(p);
    }
    // pop_back
    list_link_back(&mut list, &l1);
    if let Some(p) = list_pop_back(&mut list) {
        black_box(&p);
        list_slab.free(p);
    }
    // try_push_back (allocation path)
    let lp = list_try_push_back(&mut list, &list_slab, 99);
    black_box(&lp.borrow().value);
    list.clear(&list_slab);
}
