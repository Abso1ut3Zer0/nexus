//! Integration tests for the RcSlot-based list.

use nexus_collections::slab::list::{List, ListNode};
use nexus_slab::rc::bounded::Slab;
use nexus_slab::rc::unbounded::Slab as UnboundedSlab;

#[derive(Debug)]
#[allow(dead_code)]
struct Order {
    id: u64,
    price: f64,
}

fn make_slab() -> Slab<ListNode<Order>> {
    unsafe { Slab::with_capacity(100) }
}

fn make_u64_slab() -> Slab<ListNode<u64>> {
    unsafe { Slab::with_capacity(100) }
}

// =============================================================================
// Basic operations
// =============================================================================

#[test]
fn empty_list() {
    let mut list = List::<Order>::new();
    assert!(list.is_empty());
    assert_eq!(list.len(), 0);
    assert!(list.front().is_none());
    assert!(list.back().is_none());
    let slab = make_slab();
    list.clear(&slab);
}

#[test]
fn link_back_single() {
    let slab = make_slab();
    let mut list = List::new();
    let h = slab.alloc(ListNode::new(Order { id: 1, price: 10.0 }));

    list.link_back(&h);
    assert_eq!(list.len(), 1);
    assert!(!list.is_empty());
    assert_eq!(h.borrow().value.id, 1);
    assert_eq!(h.refcount(), 2); // user + list

    list.clear(&slab);
    slab.free(h);
}

#[test]
fn link_front_single() {
    let slab = make_slab();
    let mut list = List::new();
    let h = slab.alloc(ListNode::new(Order { id: 2, price: 20.0 }));

    list.link_front(&h);
    assert_eq!(list.len(), 1);

    list.clear(&slab);
    slab.free(h);
}

#[test]
fn push_back_and_pop_front() {
    let slab = make_u64_slab();
    let mut list = List::new();

    let h1 = list.try_push_back(&slab, 10).unwrap();
    let h2 = list.try_push_back(&slab, 20).unwrap();
    let h3 = list.try_push_back(&slab, 30).unwrap();

    assert_eq!(list.len(), 3);
    assert_eq!(list.front().unwrap().value, 10);
    assert_eq!(list.back().unwrap().value, 30);

    let p1 = list.pop_front().unwrap();
    assert_eq!(p1.borrow().value, 10);
    assert_eq!(list.len(), 2);

    let p2 = list.pop_front().unwrap();
    assert_eq!(p2.borrow().value, 20);

    let p3 = list.pop_front().unwrap();
    assert_eq!(p3.borrow().value, 30);

    assert!(list.is_empty());
    assert!(list.pop_front().is_none());

    // Free all handles
    slab.free(h1);
    slab.free(h2);
    slab.free(h3);
    slab.free(p1);
    slab.free(p2);
    slab.free(p3);
}

#[test]
fn push_front_and_pop_back() {
    let slab = make_u64_slab();
    let mut list = List::new();

    let h1 = list.try_push_front(&slab, 10).unwrap();
    let h2 = list.try_push_front(&slab, 20).unwrap();

    assert_eq!(list.front().unwrap().value, 20);
    assert_eq!(list.back().unwrap().value, 10);

    let p = list.pop_back().unwrap();
    assert_eq!(p.borrow().value, 10);

    list.clear(&slab);
    slab.free(h1);
    slab.free(h2);
    slab.free(p);
}

#[test]
fn unlink_middle() {
    let slab = make_u64_slab();
    let mut list = List::new();

    let h1 = list.try_push_back(&slab, 10).unwrap();
    let h2 = list.try_push_back(&slab, 20).unwrap();
    let h3 = list.try_push_back(&slab, 30).unwrap();

    list.unlink(&h2, &slab);
    assert_eq!(list.len(), 2);
    assert_eq!(list.front().unwrap().value, 10);
    assert_eq!(list.back().unwrap().value, 30);

    // h2 is still valid (user still holds a ref)
    assert_eq!(h2.borrow().value, 20);

    list.clear(&slab);
    slab.free(h1);
    slab.free(h2);
    slab.free(h3);
}

#[test]
fn link_after() {
    let slab = make_u64_slab();
    let mut list = List::new();

    let h1 = list.try_push_back(&slab, 10).unwrap();
    let h3 = list.try_push_back(&slab, 30).unwrap();
    let h2 = slab.alloc(ListNode::new(20));

    list.link_after(&h1, &h2);
    assert_eq!(list.len(), 3);

    let p1 = list.pop_front().unwrap();
    let p2 = list.pop_front().unwrap();
    let p3 = list.pop_front().unwrap();
    assert_eq!(p1.borrow().value, 10);
    assert_eq!(p2.borrow().value, 20);
    assert_eq!(p3.borrow().value, 30);

    slab.free(h1);
    slab.free(h2);
    slab.free(h3);
    slab.free(p1);
    slab.free(p2);
    slab.free(p3);
}

#[test]
fn link_before() {
    let slab = make_u64_slab();
    let mut list = List::new();

    let h1 = list.try_push_back(&slab, 10).unwrap();
    let h3 = list.try_push_back(&slab, 30).unwrap();
    let h2 = slab.alloc(ListNode::new(20));

    list.link_before(&h3, &h2);
    assert_eq!(list.len(), 3);

    let p1 = list.pop_front().unwrap();
    let p2 = list.pop_front().unwrap();
    let p3 = list.pop_front().unwrap();
    assert_eq!(p1.borrow().value, 10);
    assert_eq!(p2.borrow().value, 20);
    assert_eq!(p3.borrow().value, 30);

    slab.free(h1);
    slab.free(h2);
    slab.free(h3);
    slab.free(p1);
    slab.free(p2);
    slab.free(p3);
}

#[test]
fn move_to_front() {
    let slab = make_u64_slab();
    let mut list = List::new();

    let h1 = list.try_push_back(&slab, 10).unwrap();
    let h2 = list.try_push_back(&slab, 20).unwrap();
    let h3 = list.try_push_back(&slab, 30).unwrap();

    list.move_to_front(&h3);
    assert_eq!(list.front().unwrap().value, 30);
    assert_eq!(list.back().unwrap().value, 20);

    list.clear(&slab);
    slab.free(h1);
    slab.free(h2);
    slab.free(h3);
}

#[test]
fn move_to_back() {
    let slab = make_u64_slab();
    let mut list = List::new();

    let h1 = list.try_push_back(&slab, 10).unwrap();
    let h2 = list.try_push_back(&slab, 20).unwrap();
    let h3 = list.try_push_back(&slab, 30).unwrap();

    list.move_to_back(&h1);
    assert_eq!(list.front().unwrap().value, 20);
    assert_eq!(list.back().unwrap().value, 10);

    list.clear(&slab);
    slab.free(h1);
    slab.free(h2);
    slab.free(h3);
}

#[test]
fn cursor_forward_traversal() {
    let slab = make_u64_slab();
    let mut list = List::new();

    let h1 = list.try_push_back(&slab, 10).unwrap();
    let h2 = list.try_push_back(&slab, 20).unwrap();
    let h3 = list.try_push_back(&slab, 30).unwrap();

    let mut values = Vec::new();
    let mut cursor = list.cursor();
    while cursor.advance() {
        values.push(cursor.current().unwrap().value);
    }
    assert_eq!(values, vec![10, 20, 30]);

    let _ = cursor;
    list.clear(&slab);
    slab.free(h1);
    slab.free(h2);
    slab.free(h3);
}

#[test]
fn cursor_remove() {
    let slab = make_u64_slab();
    let mut list = List::new();

    let h1 = list.try_push_back(&slab, 10).unwrap();
    let h2 = list.try_push_back(&slab, 20).unwrap();
    let h3 = list.try_push_back(&slab, 30).unwrap();

    let mut cursor = list.cursor();
    cursor.advance(); // at 10
    cursor.advance(); // at 20
    let removed = cursor.remove(); // remove 20, auto-advance to 30
    assert_eq!(removed.borrow().value, 20);
    assert_eq!(cursor.current().unwrap().value, 30);

    let _ = cursor;
    assert_eq!(list.len(), 2);

    list.clear(&slab);
    slab.free(h1);
    slab.free(h2);
    slab.free(h3);
    slab.free(removed);
}

#[test]
#[should_panic(expected = "already linked")]
fn double_link_panics() {
    let slab = make_u64_slab();
    let mut list = List::new();
    let h = slab.alloc(ListNode::new(1));
    list.link_back(&h);
    list.link_back(&h); // should panic
}

#[test]
#[should_panic(expected = "not linked to this list")]
fn unlink_wrong_list_panics() {
    let slab = make_u64_slab();
    let mut list1 = List::new();
    let mut list2 = List::new();
    let h = slab.alloc(ListNode::new(1));
    list1.link_back(&h);
    list2.unlink(&h, &slab); // should panic
}

#[test]
fn contains() {
    let slab = make_u64_slab();
    let mut list = List::new();
    let h = slab.alloc(ListNode::new(42));

    assert!(!list.contains(&h));
    list.link_back(&h);
    assert!(list.contains(&h));

    list.clear(&slab);
    slab.free(h);
}

#[test]
fn is_head_is_tail() {
    let slab = make_u64_slab();
    let mut list = List::new();

    let h1 = list.try_push_back(&slab, 10).unwrap();
    let h2 = list.try_push_back(&slab, 20).unwrap();

    assert!(list.is_head(&h1));
    assert!(!list.is_head(&h2));
    assert!(list.is_tail(&h2));
    assert!(!list.is_tail(&h1));

    list.clear(&slab);
    slab.free(h1);
    slab.free(h2);
}

// =============================================================================
// Unbounded slab path
// =============================================================================

#[test]
fn unbounded_push_back_and_pop_front() {
    let slab = unsafe { UnboundedSlab::<ListNode<u64>>::with_chunk_capacity(4) };
    let mut list = List::new();

    let h1 = list.push_back(&slab, 10);
    let h2 = list.push_back(&slab, 20);
    let h3 = list.push_back(&slab, 30);

    assert_eq!(list.len(), 3);
    assert_eq!(list.front().unwrap().value, 10);
    assert_eq!(list.back().unwrap().value, 30);

    let p1 = list.pop_front().unwrap();
    assert_eq!(p1.borrow().value, 10);
    let p2 = list.pop_front().unwrap();
    assert_eq!(p2.borrow().value, 20);
    let p3 = list.pop_front().unwrap();
    assert_eq!(p3.borrow().value, 30);

    assert!(list.is_empty());

    slab.free(h1);
    slab.free(h2);
    slab.free(h3);
    slab.free(p1);
    slab.free(p2);
    slab.free(p3);
}

#[test]
fn unbounded_push_front_and_pop_back() {
    let slab = unsafe { UnboundedSlab::<ListNode<u64>>::with_chunk_capacity(4) };
    let mut list = List::new();

    let h1 = list.push_front(&slab, 10);
    let h2 = list.push_front(&slab, 20);

    assert_eq!(list.front().unwrap().value, 20);
    assert_eq!(list.back().unwrap().value, 10);

    let p = list.pop_back().unwrap();
    assert_eq!(p.borrow().value, 10);

    list.clear(&slab);
    slab.free(h1);
    slab.free(h2);
    slab.free(p);
}

// =============================================================================
// Stress test — freelist integrity
// =============================================================================

#[test]
fn stress_list_push_pop_cycle() {
    let slab = unsafe { Slab::<ListNode<u64>>::with_capacity(10_000) };
    let mut list = List::new();

    // First fill: push 10K items
    let mut handles = Vec::new();
    for i in 0..10_000 {
        let h = list.try_push_back(&slab, i).unwrap();
        handles.push(h);
    }
    assert_eq!(list.len(), 10_000);

    // Pop all
    let mut popped = Vec::new();
    while let Some(p) = list.pop_front() {
        popped.push(p);
    }
    assert!(list.is_empty());
    assert_eq!(popped.len(), 10_000);

    // Verify order
    for (i, p) in popped.iter().enumerate() {
        assert_eq!(p.borrow().value, i as u64);
    }

    // Free all handles from first fill
    for h in handles {
        slab.free(h);
    }
    for p in popped {
        slab.free(p);
    }

    // Second fill: push 10K again — verifies freelist integrity
    let mut handles2 = Vec::new();
    for i in 0..10_000 {
        let h = list.try_push_back(&slab, i + 10_000).unwrap();
        handles2.push(h);
    }
    assert_eq!(list.len(), 10_000);

    // Verify values on second fill
    let mut cursor = list.cursor();
    let mut idx = 0;
    while cursor.advance() {
        assert_eq!(cursor.current().unwrap().value, (idx + 10_000) as u64);
        idx += 1;
    }
    assert_eq!(idx, 10_000);

    list.clear(&slab);
    for h in handles2 {
        slab.free(h);
    }
}

// =============================================================================
// Cross-collection test
// =============================================================================

#[test]
fn cross_collection_move() {
    let slab = make_u64_slab();
    let mut list_a = List::new();
    let mut list_b = List::new();

    // Alloc a node
    let h = slab.alloc(ListNode::new(42));
    assert_eq!(h.refcount(), 1);

    // Link to list A
    list_a.link_back(&h);
    assert_eq!(h.refcount(), 2); // user + list_a

    // Unlink from A
    list_a.unlink(&h, &slab);
    assert_eq!(h.refcount(), 1); // user only
    assert!(list_a.is_empty());

    // Link to list B
    list_b.link_back(&h);
    assert_eq!(h.refcount(), 2); // user + list_b

    // Unlink from B
    list_b.unlink(&h, &slab);
    assert_eq!(h.refcount(), 1); // user only
    assert!(list_b.is_empty());

    // Free
    slab.free(h);
}

// =============================================================================
// move_to_front / move_to_back with order verification
// =============================================================================

#[test]
fn move_middle_to_front_verify_order() {
    let slab = make_u64_slab();
    let mut list = List::new();

    let h1 = list.try_push_back(&slab, 10).unwrap();
    let h2 = list.try_push_back(&slab, 20).unwrap();
    let h3 = list.try_push_back(&slab, 30).unwrap();

    // Move middle (20) to front: expect [20, 10, 30]
    list.move_to_front(&h2);
    let mut values = Vec::new();
    let mut cursor = list.cursor();
    while cursor.advance() {
        values.push(cursor.current().unwrap().value);
    }
    assert_eq!(values, vec![20, 10, 30]);

    list.clear(&slab);
    slab.free(h1);
    slab.free(h2);
    slab.free(h3);
}

#[test]
fn move_middle_to_back_verify_order() {
    let slab = make_u64_slab();
    let mut list = List::new();

    let h1 = list.try_push_back(&slab, 10).unwrap();
    let h2 = list.try_push_back(&slab, 20).unwrap();
    let h3 = list.try_push_back(&slab, 30).unwrap();

    // Move middle (20) to back: expect [10, 30, 20]
    list.move_to_back(&h2);
    let mut values = Vec::new();
    let mut cursor = list.cursor();
    while cursor.advance() {
        values.push(cursor.current().unwrap().value);
    }
    assert_eq!(values, vec![10, 30, 20]);

    list.clear(&slab);
    slab.free(h1);
    slab.free(h2);
    slab.free(h3);
}

// =============================================================================
// Debug-mode Drop detection
// =============================================================================

#[test]
#[cfg(debug_assertions)]
fn drop_non_empty_list_panics() {
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let slab = make_u64_slab();
        let mut list = List::new();
        let h = slab.alloc(ListNode::new(42));
        list.link_back(&h);
        // Forget the handle so its debug Drop doesn't fire first
        std::mem::forget(h);
        // list drops without clear() — should panic
    }));
    let err = result.expect_err("non-empty list drop should panic in debug");
    let msg = err
        .downcast_ref::<String>()
        .map(std::string::String::as_str)
        .or_else(|| err.downcast_ref::<&str>().copied())
        .unwrap_or("");
    assert!(
        msg.contains("List dropped with"),
        "unexpected panic message: {msg}"
    );
}

#[test]
#[cfg(debug_assertions)]
fn drop_non_empty_list_during_unwind_no_double_panic() {
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let slab = make_u64_slab();
        let mut list = List::new();
        let h = slab.alloc(ListNode::new(42));
        list.link_back(&h);
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
        let mut list = List::new();
        let order = Order {
            id: 1,
            price: 100.0,
        };
        list.push_back(&slab, order);
        // drop without clear — should panic in debug
    }));
    assert!(
        result.is_err(),
        "dropping non-empty list should panic in debug"
    );
}
