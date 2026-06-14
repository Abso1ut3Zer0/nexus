//! Miri tests for verifying absence of undefined behavior in unsafe
//! collection operations.
//!
//! Run: MIRIFLAGS="-Zmiri-ignore-leaks" cargo +nightly miri test --test miri_tests

use std::cell::Cell;

use nexus_collections::slab::btree::{BTree, BTreeNode};
use nexus_collections::slab::heap::{Heap, HeapNode};
use nexus_collections::slab::list::{List, ListNode};
use nexus_collections::slab::rbtree::{RbNode, RbTree};
use nexus_slab::rc::unbounded::Slab as RcSlab;
use nexus_slab::unbounded::Slab;

// =============================================================================
// Helper Types
// =============================================================================

thread_local! {
    static DROP_COUNT: Cell<usize> = const { Cell::new(0) };
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
struct DropTracker(#[allow(dead_code)] u64);

impl Drop for DropTracker {
    fn drop(&mut self) {
        DROP_COUNT.with(|c| c.set(c.get() + 1));
    }
}

fn reset_drop_count() {
    DROP_COUNT.with(|c| c.set(0));
}

fn get_drop_count() -> usize {
    DROP_COUNT.with(Cell::get)
}

// =============================================================================
// List Tests
// =============================================================================

#[test]
fn list_link_unlink_basic() {
    let slab: RcSlab<ListNode<u64>> = unsafe { RcSlab::with_chunk_capacity(32) };
    let mut list = List::new();

    let h1 = slab.alloc(ListNode::new(10));
    let h2 = slab.alloc(ListNode::new(20));
    let h3 = slab.alloc(ListNode::new(30));

    list.link_back(&h1);
    list.link_back(&h2);
    list.link_back(&h3);
    assert_eq!(list.len(), 3);

    // Unlink middle
    list.unlink(&h2, &slab);
    assert_eq!(list.len(), 2);
    assert_eq!(list.front().unwrap().value, 10);
    assert_eq!(list.back().unwrap().value, 30);

    // h2 still valid (user ref)
    assert_eq!(h2.borrow().value, 20);

    list.clear(&slab);
    slab.free(h1);
    slab.free(h2);
    slab.free(h3);
}

#[test]
fn list_clear_drops_refs() {
    let slab: RcSlab<ListNode<u64>> = unsafe { RcSlab::with_chunk_capacity(32) };
    let mut list = List::new();

    let handles: Vec<_> = (0..5)
        .map(|i| {
            let h = slab.alloc(ListNode::new(i));
            list.link_back(&h);
            h
        })
        .collect();

    assert_eq!(list.len(), 5);
    list.clear(&slab);
    assert!(list.is_empty());

    for h in handles {
        slab.free(h);
    }
}

#[test]
fn list_cursor_traverse_and_remove() {
    let slab: RcSlab<ListNode<u64>> = unsafe { RcSlab::with_chunk_capacity(32) };
    let mut list = List::new();

    let handles: Vec<_> = (0..5).map(|i| list.push_back(&slab, i * 10)).collect();

    // Create cursor, advance to third element (index 2), remove it
    let mut cursor = list.cursor();
    cursor.advance(); // 0
    cursor.advance(); // 10
    cursor.advance(); // 20
    let removed = cursor.remove();
    assert_eq!(removed.borrow().value, 20);

    let _ = cursor;
    assert_eq!(list.len(), 4);

    list.clear(&slab);
    for h in handles {
        slab.free(h);
    }
    slab.free(removed);
}

#[test]
fn list_link_front_back_interleaved() {
    let slab: RcSlab<ListNode<u64>> = unsafe { RcSlab::with_chunk_capacity(32) };
    let mut list = List::new();

    let mut handles = Vec::new();
    for i in 0..10u64 {
        let h = slab.alloc(ListNode::new(i));
        if i % 2 == 0 {
            list.link_back(&h);
        } else {
            list.link_front(&h);
        }
        handles.push(h);
    }

    assert_eq!(list.len(), 10);

    // Drain via pop_front
    while let Some(popped) = list.pop_front() {
        slab.free(popped);
    }
    assert!(list.is_empty());

    for h in handles {
        slab.free(h);
    }
}

#[test]
fn list_single_element() {
    let slab: RcSlab<ListNode<u64>> = unsafe { RcSlab::with_chunk_capacity(32) };
    let mut list = List::new();

    let h = slab.alloc(ListNode::new(42));
    list.link_back(&h);
    assert_eq!(list.len(), 1);
    assert_eq!(list.front().unwrap().value, 42);
    assert_eq!(list.back().unwrap().value, 42);

    list.unlink(&h, &slab);
    assert!(list.is_empty());

    slab.free(h);
}

#[test]
fn list_drop_tracker() {
    reset_drop_count();

    let slab: RcSlab<ListNode<DropTracker>> = unsafe { RcSlab::with_chunk_capacity(32) };
    let mut list = List::new();

    let handles: Vec<_> = (0..5)
        .map(|i| {
            let h = slab.alloc(ListNode::new(DropTracker(i)));
            list.link_back(&h);
            h
        })
        .collect();

    assert_eq!(get_drop_count(), 0);
    list.clear(&slab);

    // Free user handles — last ref, triggers drop
    for h in handles {
        slab.free(h);
    }
    assert_eq!(get_drop_count(), 5);
}

// =============================================================================
// Heap Tests
// =============================================================================

#[test]
fn heap_push_pop_basic() {
    let slab: RcSlab<HeapNode<u64>> = unsafe { RcSlab::with_chunk_capacity(32) };
    let mut heap = Heap::new();

    let mut handles = Vec::new();
    for v in [5, 3, 8, 1, 9, 2, 7, 4, 6, 10] {
        handles.push(heap.push(&slab, v));
    }

    let mut sorted = Vec::new();
    while let Some(popped) = heap.pop() {
        sorted.push(*popped.borrow().value());
        slab.free(popped);
    }
    assert_eq!(sorted, vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);

    for h in handles {
        slab.free(h);
    }
}

#[test]
fn heap_push_pop_reverse_sorted() {
    let slab: RcSlab<HeapNode<u64>> = unsafe { RcSlab::with_chunk_capacity(32) };
    let mut heap = Heap::new();

    let mut handles = Vec::new();
    for v in (1..=10).rev() {
        handles.push(heap.push(&slab, v));
    }

    let mut sorted = Vec::new();
    while let Some(popped) = heap.pop() {
        sorted.push(*popped.borrow().value());
        slab.free(popped);
    }
    assert_eq!(sorted, vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);

    for h in handles {
        slab.free(h);
    }
}

#[test]
fn heap_clear() {
    let slab: RcSlab<HeapNode<u64>> = unsafe { RcSlab::with_chunk_capacity(32) };
    let mut heap = Heap::new();

    let mut handles = Vec::new();
    for v in 0..10 {
        handles.push(heap.push(&slab, v));
    }

    heap.clear(&slab);
    assert!(heap.is_empty());

    for h in handles {
        slab.free(h);
    }
}

#[test]
fn heap_decrease_key() {
    let slab: RcSlab<HeapNode<u64>> = unsafe { RcSlab::with_chunk_capacity(32) };
    let mut heap = Heap::new();

    let mut handles = Vec::new();
    for v in [50, 40, 30, 20, 10] {
        handles.push(heap.push(&slab, v));
    }

    // Unlink 30, push 1 (simulates decrease-key — pairing heap is immutable,
    // so we unlink and re-push with a new node)
    heap.unlink(&handles[2], &slab);
    let new_min = heap.push(&slab, 1);

    let popped = heap.pop().unwrap();
    assert_eq!(*popped.borrow().value(), 1);
    slab.free(popped);

    heap.clear(&slab);
    for h in handles {
        slab.free(h);
    }
    slab.free(new_min);
}

#[test]
fn heap_single_element() {
    let slab: RcSlab<HeapNode<u64>> = unsafe { RcSlab::with_chunk_capacity(32) };
    let mut heap = Heap::new();

    let h = heap.push(&slab, 42);
    assert_eq!(*heap.peek().unwrap().value(), 42);

    let popped = heap.pop().unwrap();
    assert_eq!(*popped.borrow().value(), 42);
    assert!(heap.is_empty());

    slab.free(h);
    slab.free(popped);
}

#[test]
fn heap_drop_tracker() {
    reset_drop_count();

    let slab: RcSlab<HeapNode<DropTracker>> = unsafe { RcSlab::with_chunk_capacity(32) };
    let mut heap = Heap::new();

    let handles: Vec<_> = (0..5).map(|i| heap.push(&slab, DropTracker(i))).collect();

    assert_eq!(get_drop_count(), 0);
    heap.clear(&slab);

    for h in handles {
        slab.free(h);
    }
    assert_eq!(get_drop_count(), 5);
}

// =============================================================================
// RbTree Tests
// =============================================================================

#[test]
fn rbtree_insert_ascending() {
    let slab: Slab<RbNode<u64, u64>> = unsafe { Slab::with_chunk_capacity(32) };
    let mut tree = RbTree::new();

    for i in 1..=20 {
        tree.insert(&slab, i, i * 10);
    }
    assert_eq!(tree.len(), 20);
    tree.verify_invariants();

    // Verify sorted order
    let keys: Vec<u64> = tree.keys().copied().collect();
    assert_eq!(keys, (1..=20).collect::<Vec<_>>());

    tree.clear(&slab);
}

#[test]
fn rbtree_insert_descending() {
    let slab: Slab<RbNode<u64, u64>> = unsafe { Slab::with_chunk_capacity(32) };
    let mut tree = RbTree::new();

    for i in (1..=20).rev() {
        tree.insert(&slab, i, i * 10);
    }
    assert_eq!(tree.len(), 20);
    tree.verify_invariants();

    let keys: Vec<u64> = tree.keys().copied().collect();
    assert_eq!(keys, (1..=20).collect::<Vec<_>>());

    tree.clear(&slab);
}

#[test]
fn rbtree_insert_random_pattern() {
    let slab: Slab<RbNode<u64, u64>> = unsafe { Slab::with_chunk_capacity(32) };
    let mut tree = RbTree::new();

    for i in [10, 5, 15, 3, 7, 12, 20, 1, 4, 6, 8] {
        tree.insert(&slab, i, i * 10);
    }
    assert_eq!(tree.len(), 11);
    tree.verify_invariants();

    tree.clear(&slab);
}

#[test]
fn rbtree_remove_leaf() {
    let slab: Slab<RbNode<u64, u64>> = unsafe { Slab::with_chunk_capacity(32) };
    let mut tree = RbTree::new();

    for i in [10, 5, 15, 3, 7] {
        tree.insert(&slab, i, i * 10);
    }
    tree.verify_invariants();

    // 3 is a leaf
    assert_eq!(tree.remove(&slab, &3), Some(30));
    assert_eq!(tree.len(), 4);
    tree.verify_invariants();

    tree.clear(&slab);
}

#[test]
fn rbtree_remove_node_with_one_child() {
    let slab: Slab<RbNode<u64, u64>> = unsafe { Slab::with_chunk_capacity(32) };
    let mut tree = RbTree::new();

    // Insert in order that creates nodes with single children
    for i in [10, 5, 15, 3, 7, 12, 20, 1] {
        tree.insert(&slab, i, i * 10);
    }
    tree.verify_invariants();

    // Remove 3 which has child 1
    assert_eq!(tree.remove(&slab, &3), Some(30));
    tree.verify_invariants();
    assert_eq!(tree.get(&1), Some(&10));

    tree.clear(&slab);
}

#[test]
fn rbtree_remove_node_with_two_children() {
    let slab: Slab<RbNode<u64, u64>> = unsafe { Slab::with_chunk_capacity(32) };
    let mut tree = RbTree::new();

    for i in [10, 5, 15, 3, 7, 12, 20] {
        tree.insert(&slab, i, i * 10);
    }
    tree.verify_invariants();

    // 5 has children 3 and 7
    assert_eq!(tree.remove(&slab, &5), Some(50));
    tree.verify_invariants();
    assert_eq!(tree.get(&3), Some(&30));
    assert_eq!(tree.get(&7), Some(&70));

    tree.clear(&slab);
}

#[test]
fn rbtree_insert_remove_stress() {
    let slab: Slab<RbNode<u64, u64>> = unsafe { Slab::with_chunk_capacity(64) };
    let mut tree = RbTree::new();

    // Insert 30 values in a mixed pattern
    let insert1: Vec<u64> = vec![
        15, 7, 23, 3, 11, 19, 27, 1, 5, 9, 13, 17, 21, 25, 29, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20,
        22, 24, 26, 28, 30,
    ];
    for &i in &insert1 {
        tree.insert(&slab, i, i * 10);
    }
    assert_eq!(tree.len(), 30);
    tree.verify_invariants();

    // Remove 15 values
    for i in [1, 5, 9, 13, 17, 21, 25, 29, 3, 7, 11, 15, 19, 23, 27] {
        tree.remove(&slab, &i);
    }
    assert_eq!(tree.len(), 15);
    tree.verify_invariants();

    // Insert 10 more
    for i in 31..=40 {
        tree.insert(&slab, i, i * 10);
    }
    assert_eq!(tree.len(), 25);
    tree.verify_invariants();

    tree.clear(&slab);
}

#[test]
fn rbtree_clear() {
    let slab: Slab<RbNode<u64, u64>> = unsafe { Slab::with_chunk_capacity(32) };
    let mut tree = RbTree::new();

    for i in 1..=20 {
        tree.insert(&slab, i, i * 10);
    }

    tree.clear(&slab);
    assert!(tree.is_empty());
    assert_eq!(tree.len(), 0);
}

#[test]
fn rbtree_iteration() {
    let slab: Slab<RbNode<u64, u64>> = unsafe { Slab::with_chunk_capacity(32) };
    let mut tree = RbTree::new();

    for i in [
        10, 5, 15, 3, 7, 12, 20, 1, 4, 6, 8, 11, 13, 17, 25, 2, 9, 14, 18, 30,
    ] {
        tree.insert(&slab, i, i * 10);
    }

    let keys: Vec<u64> = tree.keys().copied().collect();
    let mut sorted = keys.clone();
    sorted.sort_unstable();
    assert_eq!(keys, sorted);

    tree.clear(&slab);
}

#[test]
fn rbtree_range_iteration() {
    let slab: Slab<RbNode<u64, u64>> = unsafe { Slab::with_chunk_capacity(32) };
    let mut tree = RbTree::new();

    for i in 1..=20 {
        tree.insert(&slab, i, i * 10);
    }

    let range_keys: Vec<u64> = tree.range(5..15).map(|(&k, _)| k).collect();
    assert_eq!(range_keys, (5..15).collect::<Vec<_>>());

    tree.clear(&slab);
}

#[test]
fn rbtree_entry_api() {
    let slab: Slab<RbNode<u64, u64>> = unsafe { Slab::with_chunk_capacity(32) };
    let mut tree = RbTree::new();

    // Insert via vacant entry
    match tree.entry(&slab, 10) {
        nexus_collections::slab::rbtree::Entry::Vacant(e) => {
            let v = e.insert(100);
            assert_eq!(*v, 100);
        }
        nexus_collections::slab::rbtree::Entry::Occupied(_) => panic!("expected vacant"),
    }

    // Modify via occupied entry
    match tree.entry(&slab, 10) {
        nexus_collections::slab::rbtree::Entry::Occupied(mut e) => {
            assert_eq!(*e.get(), 100);
            *e.get_mut() = 200;
        }
        nexus_collections::slab::rbtree::Entry::Vacant(_) => panic!("expected occupied"),
    }
    assert_eq!(tree.get(&10), Some(&200));

    // Remove via occupied entry
    match tree.entry(&slab, 10) {
        nexus_collections::slab::rbtree::Entry::Occupied(e) => {
            let (k, v) = e.remove();
            assert_eq!(k, 10);
            assert_eq!(v, 200);
        }
        nexus_collections::slab::rbtree::Entry::Vacant(_) => panic!("expected occupied"),
    }
    assert!(tree.is_empty());

    tree.clear(&slab);
}

#[test]
fn rbtree_first_last_pop() {
    let slab: Slab<RbNode<u64, u64>> = unsafe { Slab::with_chunk_capacity(32) };
    let mut tree = RbTree::new();

    for i in [5, 3, 7, 1, 9, 2, 8, 4, 6, 10] {
        tree.insert(&slab, i, i * 10);
    }

    // Alternate pop_first and pop_last
    assert_eq!(tree.pop_first(&slab), Some((1, 10)));
    assert_eq!(tree.pop_last(&slab), Some((10, 100)));
    assert_eq!(tree.pop_first(&slab), Some((2, 20)));
    assert_eq!(tree.pop_last(&slab), Some((9, 90)));
    assert_eq!(tree.pop_first(&slab), Some((3, 30)));
    assert_eq!(tree.pop_last(&slab), Some((8, 80)));

    assert_eq!(tree.len(), 4);
    tree.verify_invariants();

    tree.clear(&slab);
}

#[test]
fn rbtree_drop_tracker() {
    reset_drop_count();

    let slab: Slab<RbNode<u64, DropTracker>> = unsafe { Slab::with_chunk_capacity(32) };
    let mut tree = RbTree::new();

    for i in 0..10 {
        tree.insert(&slab, i, DropTracker(i));
    }
    assert_eq!(get_drop_count(), 0);

    tree.clear(&slab);
    assert_eq!(get_drop_count(), 10);
}

// =============================================================================
// BTree Tests
// =============================================================================

#[test]
fn btree_insert_until_split() {
    let slab: Slab<BTreeNode<u64, u64, 8>> = unsafe { Slab::with_chunk_capacity(32) };
    let mut tree = BTree::<u64, u64, 8>::new();

    // Insert B values to trigger first root split
    for i in 1..=8 {
        tree.insert(&slab, i, i * 10);
    }
    assert_eq!(tree.len(), 8);
    tree.verify_invariants();

    let keys: Vec<u64> = tree.keys().copied().collect();
    assert_eq!(keys, (1..=8).collect::<Vec<_>>());

    tree.clear(&slab);
}

#[test]
fn btree_insert_causing_cascade_split() {
    let slab: Slab<BTreeNode<u64, u64, 8>> = unsafe { Slab::with_chunk_capacity(32) };
    let mut tree = BTree::<u64, u64, 8>::new();

    // Insert 3*B values to trigger cascading splits
    for i in 1..=24 {
        tree.insert(&slab, i, i * 10);
    }
    assert_eq!(tree.len(), 24);
    tree.verify_invariants();

    tree.clear(&slab);
}

#[test]
fn btree_remove_from_leaf() {
    let slab: Slab<BTreeNode<u64, u64, 8>> = unsafe { Slab::with_chunk_capacity(32) };
    let mut tree = BTree::<u64, u64, 8>::new();

    for i in 1..=10 {
        tree.insert(&slab, i, i * 10);
    }
    tree.verify_invariants();

    assert_eq!(tree.remove(&slab, &3), Some(30));
    assert_eq!(tree.len(), 9);
    tree.verify_invariants();

    tree.clear(&slab);
}

#[test]
fn btree_remove_causing_merge() {
    let slab: Slab<BTreeNode<u64, u64, 8>> = unsafe { Slab::with_chunk_capacity(64) };
    let mut tree = BTree::<u64, u64, 8>::new();

    // Insert enough to create multi-level tree, then remove to trigger merges
    for i in 1..=20 {
        tree.insert(&slab, i, i * 10);
    }
    tree.verify_invariants();

    // Remove many to trigger merge operations
    for i in 1..=10 {
        tree.remove(&slab, &i);
    }
    tree.verify_invariants();

    tree.clear(&slab);
}

#[test]
fn btree_remove_causing_redistribution() {
    let slab: Slab<BTreeNode<u64, u64, 8>> = unsafe { Slab::with_chunk_capacity(64) };
    let mut tree = BTree::<u64, u64, 8>::new();

    // Insert enough to build structure, then selectively remove
    for i in 1..=16 {
        tree.insert(&slab, i, i * 10);
    }
    tree.verify_invariants();

    // Remove from one side to trigger borrow from sibling
    tree.remove(&slab, &1);
    tree.remove(&slab, &2);
    tree.verify_invariants();

    tree.clear(&slab);
}

#[test]
fn btree_insert_remove_stress() {
    let slab: Slab<BTreeNode<u64, u64, 8>> = unsafe { Slab::with_chunk_capacity(64) };
    let mut tree = BTree::<u64, u64, 8>::new();

    // Insert 50 values
    for i in 1..=50 {
        tree.insert(&slab, i, i * 10);
    }
    assert_eq!(tree.len(), 50);
    tree.verify_invariants();

    // Remove 25 interleaved (odds)
    for i in (1..=50).step_by(2) {
        tree.remove(&slab, &i);
    }
    assert_eq!(tree.len(), 25);
    tree.verify_invariants();

    // Insert 15 more
    for i in 51..=65 {
        tree.insert(&slab, i, i * 10);
    }
    assert_eq!(tree.len(), 40);
    tree.verify_invariants();

    tree.clear(&slab);
}

#[test]
fn btree_clear() {
    let slab: Slab<BTreeNode<u64, u64, 8>> = unsafe { Slab::with_chunk_capacity(64) };
    let mut tree = BTree::<u64, u64, 8>::new();

    for i in 1..=30 {
        tree.insert(&slab, i, i * 10);
    }

    tree.clear(&slab);
    assert!(tree.is_empty());
    assert_eq!(tree.len(), 0);
}

#[test]
fn btree_iteration() {
    let slab: Slab<BTreeNode<u64, u64, 8>> = unsafe { Slab::with_chunk_capacity(64) };
    let mut tree = BTree::<u64, u64, 8>::new();

    for i in [
        15, 7, 23, 3, 11, 19, 27, 1, 5, 9, 13, 17, 21, 25, 29, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20,
        22, 24, 26, 28, 30,
    ] {
        tree.insert(&slab, i, i * 10);
    }

    let keys: Vec<u64> = tree.keys().copied().collect();
    let mut sorted = keys.clone();
    sorted.sort_unstable();
    assert_eq!(keys, sorted);

    tree.clear(&slab);
}

#[test]
fn btree_entry_insert_and_remove() {
    let slab: Slab<BTreeNode<u64, u64, 8>> = unsafe { Slab::with_chunk_capacity(32) };
    let mut tree = BTree::<u64, u64, 8>::new();

    // Insert via entry
    match tree.entry(&slab, 10) {
        nexus_collections::slab::btree::Entry::Vacant(e) => {
            let v = e.insert(100);
            assert_eq!(*v, 100);
        }
        nexus_collections::slab::btree::Entry::Occupied(_) => panic!("expected vacant"),
    }

    // Modify via entry
    match tree.entry(&slab, 10) {
        nexus_collections::slab::btree::Entry::Occupied(mut e) => {
            assert_eq!(*e.get(), 100);
            *e.get_mut() = 200;
        }
        nexus_collections::slab::btree::Entry::Vacant(_) => panic!("expected occupied"),
    }
    assert_eq!(tree.get(&10), Some(&200));

    // Remove via entry
    match tree.entry(&slab, 10) {
        nexus_collections::slab::btree::Entry::Occupied(e) => {
            let (k, v) = e.remove();
            assert_eq!(k, 10);
            assert_eq!(v, 200);
        }
        nexus_collections::slab::btree::Entry::Vacant(_) => panic!("expected occupied"),
    }
    assert!(tree.is_empty());

    tree.clear(&slab);
}

#[test]
fn btree_range() {
    let slab: Slab<BTreeNode<u64, u64, 8>> = unsafe { Slab::with_chunk_capacity(64) };
    let mut tree = BTree::<u64, u64, 8>::new();

    for i in 1..=30 {
        tree.insert(&slab, i, i * 10);
    }

    let range_keys: Vec<u64> = tree.range(10..20).map(|(&k, _)| k).collect();
    assert_eq!(range_keys, (10..20).collect::<Vec<_>>());

    tree.clear(&slab);
}

#[test]
fn btree_first_last_pop() {
    let slab: Slab<BTreeNode<u64, u64, 8>> = unsafe { Slab::with_chunk_capacity(32) };
    let mut tree = BTree::<u64, u64, 8>::new();

    for i in 1..=20 {
        tree.insert(&slab, i, i * 10);
    }

    assert_eq!(tree.pop_first(&slab), Some((1, 10)));
    assert_eq!(tree.pop_last(&slab), Some((20, 200)));
    assert_eq!(tree.pop_first(&slab), Some((2, 20)));
    assert_eq!(tree.pop_last(&slab), Some((19, 190)));

    assert_eq!(tree.len(), 16);
    tree.verify_invariants();

    tree.clear(&slab);
}

#[test]
fn btree_drop_tracker() {
    reset_drop_count();

    let slab: Slab<BTreeNode<u64, DropTracker, 8>> = unsafe { Slab::with_chunk_capacity(32) };
    let mut tree = BTree::<u64, DropTracker, 8>::new();

    for i in 0..15 {
        tree.insert(&slab, i, DropTracker(i));
    }
    assert_eq!(get_drop_count(), 0);

    tree.clear(&slab);
    assert_eq!(get_drop_count(), 15);
}
