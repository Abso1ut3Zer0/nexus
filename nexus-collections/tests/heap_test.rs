//! Integration tests for the pairing heap.

use nexus_collections::slab::heap::{Heap, HeapNode};
use nexus_slab::rc::bounded::Slab;
use nexus_slab::rc::unbounded::Slab as UnboundedSlab;

fn make_slab() -> Slab<HeapNode<u64>> {
    unsafe { Slab::with_capacity(100) }
}

#[test]
fn empty_heap() {
    let mut heap = Heap::<u64>::new();
    assert!(heap.is_empty());
    assert_eq!(heap.len(), 0);
    assert!(heap.peek().is_none());
    assert!(heap.pop().is_none());
    let slab = make_slab();
    heap.clear(&slab);
}

#[test]
fn push_and_pop() {
    let slab = make_slab();
    let mut heap = Heap::new();

    let h3 = heap.try_push(&slab, 30).unwrap();
    let h1 = heap.try_push(&slab, 10).unwrap();
    let h2 = heap.try_push(&slab, 20).unwrap();

    assert_eq!(heap.len(), 3);
    assert_eq!(*heap.peek().unwrap().value(), 10);

    let p1 = heap.pop().unwrap();
    assert_eq!(*p1.borrow().value(), 10);

    let p2 = heap.pop().unwrap();
    assert_eq!(*p2.borrow().value(), 20);

    let p3 = heap.pop().unwrap();
    assert_eq!(*p3.borrow().value(), 30);

    assert!(heap.is_empty());

    slab.free(h1);
    slab.free(h2);
    slab.free(h3);
    slab.free(p1);
    slab.free(p2);
    slab.free(p3);
}

#[test]
fn link_and_unlink() {
    let slab = make_slab();
    let mut heap = Heap::new();

    let h1 = slab.alloc(HeapNode::new(10));
    let h2 = slab.alloc(HeapNode::new(5));

    heap.link(&h1);
    heap.link(&h2);
    assert_eq!(heap.len(), 2);

    heap.unlink(&h2, &slab);
    assert_eq!(heap.len(), 1);
    assert_eq!(*heap.peek().unwrap().value(), 10);

    heap.clear(&slab);
    slab.free(h1);
    slab.free(h2);
}

#[test]
fn contains() {
    let slab = make_slab();
    let mut heap = Heap::new();
    let h = slab.alloc(HeapNode::new(42));

    assert!(!heap.contains(&h));
    heap.link(&h);
    assert!(heap.contains(&h));

    heap.clear(&slab);
    slab.free(h);
}

#[test]
fn try_push_full() {
    let slab: Slab<HeapNode<u64>> = unsafe { Slab::with_capacity(1) };
    let mut heap = Heap::new();

    let h = heap.try_push(&slab, 10).unwrap();
    let err = heap.try_push(&slab, 20);
    assert!(err.is_err());

    heap.clear(&slab);
    slab.free(h);
}

#[test]
fn drain() {
    let slab = make_slab();
    let mut heap = Heap::new();

    let h1 = heap.try_push(&slab, 30).unwrap();
    let h2 = heap.try_push(&slab, 10).unwrap();
    let h3 = heap.try_push(&slab, 20).unwrap();

    let values: Vec<u64> = heap
        .drain()
        .map(|h| {
            let v = *h.borrow().value();
            slab.free(h);
            v
        })
        .collect();
    assert_eq!(values, vec![10, 20, 30]);

    assert!(heap.is_empty());

    slab.free(h1);
    slab.free(h2);
    slab.free(h3);
}

#[test]
fn drain_while() {
    let slab = make_slab();
    let mut heap = Heap::new();

    let h1 = heap.try_push(&slab, 10).unwrap();
    let h2 = heap.try_push(&slab, 20).unwrap();
    let h3 = heap.try_push(&slab, 30).unwrap();

    let handles: Vec<_> = heap.drain_while(|n| *n.value() <= 20).collect();
    assert_eq!(handles.len(), 2);
    assert_eq!(heap.len(), 1);
    assert_eq!(*heap.peek().unwrap().value(), 30);

    for h in handles {
        slab.free(h);
    }
    heap.clear(&slab);
    slab.free(h1);
    slab.free(h2);
    slab.free(h3);
}

#[test]
#[should_panic(expected = "already linked")]
fn double_link_panics() {
    let slab = make_slab();
    let mut heap = Heap::new();
    let h = slab.alloc(HeapNode::new(1));
    heap.link(&h);
    heap.link(&h); // should panic
}

#[test]
#[should_panic(expected = "not linked to this heap")]
fn unlink_wrong_heap_panics() {
    let slab = make_slab();
    let mut heap1 = Heap::new();
    let mut heap2 = Heap::new();
    let h = slab.alloc(HeapNode::new(1));
    heap1.link(&h);
    heap2.unlink(&h, &slab); // should panic
}

// =============================================================================
// Unbounded slab path
// =============================================================================

#[test]
fn unbounded_push_and_pop() {
    let slab = unsafe { UnboundedSlab::<HeapNode<u64>>::with_chunk_capacity(4) };
    let mut heap = Heap::new();

    let h3 = heap.push(&slab, 30);
    let h1 = heap.push(&slab, 10);
    let h2 = heap.push(&slab, 20);

    assert_eq!(heap.len(), 3);
    assert_eq!(*heap.peek().unwrap().value(), 10);

    let p1 = heap.pop().unwrap();
    assert_eq!(*p1.borrow().value(), 10);

    let p2 = heap.pop().unwrap();
    assert_eq!(*p2.borrow().value(), 20);

    let p3 = heap.pop().unwrap();
    assert_eq!(*p3.borrow().value(), 30);

    assert!(heap.is_empty());

    slab.free(h1);
    slab.free(h2);
    slab.free(h3);
    slab.free(p1);
    slab.free(p2);
    slab.free(p3);
}

// =============================================================================
// Stress test — freelist integrity
// =============================================================================

#[test]
fn stress_heap_push_pop_cycle() {
    let slab: Slab<HeapNode<u64>> = unsafe { Slab::with_capacity(10_000) };
    let mut heap = Heap::new();

    // First fill
    let mut handles = Vec::new();
    for i in 0..10_000u64 {
        let h = heap.try_push(&slab, i).unwrap();
        handles.push(h);
    }
    assert_eq!(heap.len(), 10_000);

    // Pop all (should come out in sorted order)
    let mut prev = 0u64;
    let mut popped = Vec::new();
    while let Some(p) = heap.pop() {
        let v = *p.borrow().value();
        assert!(v >= prev);
        prev = v;
        popped.push(p);
    }
    assert!(heap.is_empty());
    assert_eq!(popped.len(), 10_000);

    // Free all
    for h in handles {
        slab.free(h);
    }
    for p in popped {
        slab.free(p);
    }

    // Second fill — verifies freelist integrity
    let mut handles2 = Vec::new();
    for i in 0..10_000u64 {
        let h = heap.try_push(&slab, i + 10_000).unwrap();
        handles2.push(h);
    }
    assert_eq!(heap.len(), 10_000);

    // Verify min is correct
    assert_eq!(*heap.peek().unwrap().value(), 10_000);

    heap.clear(&slab);
    for h in handles2 {
        slab.free(h);
    }
}

// =============================================================================
// drain_while — detailed
// =============================================================================

#[test]
fn drain_while_partial() {
    let slab = make_slab();
    let mut heap = Heap::new();

    // Push values 1-10
    let mut handles = Vec::new();
    for i in 1..=10 {
        let h = heap.try_push(&slab, i).unwrap();
        handles.push(h);
    }

    // Drain while value < 5 — should get 1, 2, 3, 4
    let drained: Vec<_> = heap
        .drain_while(|n| *n.value() < 5)
        .map(|h| {
            let v = *h.borrow().value();
            slab.free(h);
            v
        })
        .collect();

    assert_eq!(drained, vec![1, 2, 3, 4]);
    assert_eq!(heap.len(), 6);
    assert_eq!(*heap.peek().unwrap().value(), 5);

    heap.clear(&slab);
    for h in handles {
        slab.free(h);
    }
}

// =============================================================================
// Debug-mode Drop detection
// =============================================================================

#[test]
#[cfg(debug_assertions)]
fn drop_non_empty_heap_panics() {
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let slab = make_slab();
        let mut heap = Heap::new();
        let h = heap.try_push(&slab, 42).unwrap();
        // Forget the handle so its debug Drop doesn't fire first
        std::mem::forget(h);
        // heap drops without clear() — should panic
    }));
    let err = result.expect_err("non-empty heap drop should panic in debug");
    let msg = err
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| err.downcast_ref::<&str>().copied())
        .unwrap_or("");
    assert!(
        msg.contains("Heap dropped with"),
        "unexpected panic message: {msg}"
    );
}

#[test]
#[cfg(debug_assertions)]
fn drop_non_empty_heap_during_unwind_no_double_panic() {
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let slab = make_slab();
        let mut heap = Heap::new();
        let h = heap.try_push(&slab, 42).unwrap();
        std::mem::forget(h);
        panic!("intentional outer panic");
    }));
    let err = result.expect_err("should have panicked");
    let msg = err.downcast_ref::<&str>().copied().unwrap_or("");
    assert_eq!(msg, "intentional outer panic");
}

#[cfg(debug_assertions)]
#[test]
fn non_empty_drop_panics_in_debug() {
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let slab = unsafe { UnboundedSlab::with_chunk_capacity(8) };
        let mut heap = Heap::new();
        heap.push(&slab, 42u64);
        // drop without clear — should panic in debug
    }));
    assert!(
        result.is_err(),
        "dropping non-empty heap should panic in debug"
    );
}
