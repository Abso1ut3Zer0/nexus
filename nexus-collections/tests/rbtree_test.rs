//! Integration tests for the red-black tree.

use nexus_collections::slab::rbtree::{RbNode, RbTree};
use nexus_slab::bounded::Slab;
use nexus_slab::unbounded::Slab as UnboundedSlab;

fn make_slab() -> Slab<RbNode<u64, String>> {
    unsafe { Slab::with_capacity(200) }
}

fn make_u64_slab() -> Slab<RbNode<u64, u64>> {
    unsafe { Slab::with_capacity(200) }
}

#[test]
fn empty_tree() {
    let tree = RbTree::<u64, String>::new();
    assert!(tree.is_empty());
    assert_eq!(tree.len(), 0);
    assert!(tree.first_key_value().is_none());
    assert!(tree.last_key_value().is_none());
}

#[test]
fn insert_and_get() {
    let slab = make_slab();
    let mut tree = RbTree::new();

    assert!(tree.try_insert(&slab, 10, "ten".into()).unwrap().is_none());
    assert!(
        tree.try_insert(&slab, 20, "twenty".into())
            .unwrap()
            .is_none()
    );
    assert!(tree.try_insert(&slab, 5, "five".into()).unwrap().is_none());

    assert_eq!(tree.len(), 3);
    assert_eq!(tree.get(&10), Some(&String::from("ten")));
    assert_eq!(tree.get(&20), Some(&String::from("twenty")));
    assert_eq!(tree.get(&5), Some(&String::from("five")));
    assert_eq!(tree.get(&99), None);

    tree.verify_invariants();
    tree.clear(&slab);
}

#[test]
fn insert_replaces_value() {
    let slab = make_slab();
    let mut tree = RbTree::new();

    tree.try_insert(&slab, 10, "first".into()).unwrap();
    let old = tree.try_insert(&slab, 10, "second".into()).unwrap();
    assert_eq!(old, Some(String::from("first")));
    assert_eq!(tree.get(&10), Some(&String::from("second")));
    assert_eq!(tree.len(), 1);

    tree.clear(&slab);
}

#[test]
fn remove() {
    let slab = make_u64_slab();
    let mut tree = RbTree::new();

    for i in 0..20 {
        tree.try_insert(&slab, i, i * 10).unwrap();
    }
    tree.verify_invariants();

    assert_eq!(tree.remove(&slab, &10), Some(100));
    assert_eq!(tree.remove(&slab, &10), None);
    assert_eq!(tree.len(), 19);
    tree.verify_invariants();

    tree.clear(&slab);
}

#[test]
fn pop_first_and_last() {
    let slab = make_u64_slab();
    let mut tree = RbTree::new();

    for i in [5, 3, 7, 1, 9] {
        tree.try_insert(&slab, i, i * 10).unwrap();
    }

    assert_eq!(tree.pop_first(&slab), Some((1, 10)));
    assert_eq!(tree.pop_last(&slab), Some((9, 90)));
    assert_eq!(tree.len(), 3);
    tree.verify_invariants();

    tree.clear(&slab);
}

#[test]
fn first_last_key_value() {
    let slab = make_u64_slab();
    let mut tree = RbTree::new();

    tree.try_insert(&slab, 10, 100).unwrap();
    tree.try_insert(&slab, 5, 50).unwrap();
    tree.try_insert(&slab, 20, 200).unwrap();

    assert_eq!(tree.first_key_value(), Some((&5, &50)));
    assert_eq!(tree.last_key_value(), Some((&20, &200)));

    tree.clear(&slab);
}

#[test]
fn iter_sorted() {
    let slab = make_u64_slab();
    let mut tree = RbTree::new();

    for i in [5, 3, 7, 1, 9, 2, 8, 4, 6] {
        tree.try_insert(&slab, i, i * 10).unwrap();
    }

    let keys: Vec<u64> = tree.keys().copied().collect();
    assert_eq!(keys, vec![1, 2, 3, 4, 5, 6, 7, 8, 9]);

    tree.clear(&slab);
}

#[test]
fn range() {
    let slab = make_u64_slab();
    let mut tree = RbTree::new();

    for i in 1..=10 {
        tree.try_insert(&slab, i, i).unwrap();
    }

    let range_keys: Vec<u64> = tree.range(3..=7).map(|(&k, _)| k).collect();
    assert_eq!(range_keys, vec![3, 4, 5, 6, 7]);

    tree.clear(&slab);
}

#[test]
fn entry_occupied() {
    let slab = make_u64_slab();
    let mut tree = RbTree::new();

    tree.try_insert(&slab, 10, 100).unwrap();

    match tree.entry(&slab, 10) {
        nexus_collections::slab::rbtree::Entry::Occupied(mut e) => {
            assert_eq!(*e.get(), 100);
            *e.get_mut() = 200;
        }
        nexus_collections::slab::rbtree::Entry::Vacant(_) => panic!("expected occupied"),
    }

    assert_eq!(tree.get(&10), Some(&200));

    tree.clear(&slab);
}

#[test]
fn entry_vacant_insert() {
    let slab = make_u64_slab();
    let mut tree = RbTree::new();

    match tree.entry(&slab, 10) {
        nexus_collections::slab::rbtree::Entry::Occupied(_) => panic!("expected vacant"),
        nexus_collections::slab::rbtree::Entry::Vacant(e) => {
            let v = e.insert(100);
            assert_eq!(*v, 100);
        }
    }

    assert_eq!(tree.get(&10), Some(&100));

    tree.clear(&slab);
}

#[test]
fn drain() {
    let slab = make_u64_slab();
    let mut tree = RbTree::new();

    for i in [3, 1, 2] {
        tree.try_insert(&slab, i, i * 10).unwrap();
    }

    let pairs: Vec<(u64, u64)> = tree.drain(&slab).collect();
    assert_eq!(pairs, vec![(1, 10), (2, 20), (3, 30)]);
    assert!(tree.is_empty());
}

#[test]
fn cursor_forward() {
    let slab = make_u64_slab();
    let mut tree = RbTree::new();

    for i in 1..=5 {
        tree.try_insert(&slab, i, i * 10).unwrap();
    }

    let mut cursor = tree.cursor_front(&slab);
    let mut keys = Vec::new();
    while cursor.advance() {
        keys.push(*cursor.key().unwrap());
    }
    assert_eq!(keys, vec![1, 2, 3, 4, 5]);

    let _ = cursor;
    tree.clear(&slab);
}

#[test]
fn cursor_remove() {
    let slab = make_u64_slab();
    let mut tree = RbTree::new();

    for i in 1..=5 {
        tree.try_insert(&slab, i, i * 10).unwrap();
    }

    let mut cursor = tree.cursor_front(&slab);
    cursor.advance(); // at 1
    cursor.advance(); // at 2
    let removed = cursor.remove();
    assert_eq!(removed, Some((2, 20)));
    assert_eq!(cursor.key(), Some(&3));

    let _ = cursor;
    assert_eq!(tree.len(), 4);
    tree.verify_invariants();
    tree.clear(&slab);
}

#[test]
fn many_inserts_and_removes() {
    let slab = make_u64_slab();
    let mut tree = RbTree::new();

    for i in 0..100 {
        tree.try_insert(&slab, i, i).unwrap();
    }
    tree.verify_invariants();

    for i in (0..100).step_by(2) {
        tree.remove(&slab, &i);
    }
    tree.verify_invariants();
    assert_eq!(tree.len(), 50);

    tree.clear(&slab);
}

#[test]
fn reverse_comparator() {
    use nexus_collections::slab::Reverse;
    let slab: Slab<RbNode<u64, u64>> = unsafe { Slab::with_capacity(100) };
    let mut tree = RbTree::with_comparator(Reverse);

    tree.try_insert(&slab, 1, 10).unwrap();
    tree.try_insert(&slab, 3, 30).unwrap();
    tree.try_insert(&slab, 2, 20).unwrap();

    assert_eq!(tree.first_key_value(), Some((&3, &30)));
    assert_eq!(tree.last_key_value(), Some((&1, &10)));

    tree.clear(&slab);
}

// =============================================================================
// Unbounded slab — infallible insert
// =============================================================================

#[test]
fn unbounded_insert() {
    let slab: UnboundedSlab<RbNode<u64, u64>> = unsafe { UnboundedSlab::with_chunk_capacity(8) };
    let mut tree = RbTree::new();

    for i in 0..50 {
        assert!(tree.insert(&slab, i, i * 10).is_none());
    }
    tree.verify_invariants();
    assert_eq!(tree.len(), 50);

    // Replace existing
    assert_eq!(tree.insert(&slab, 25, 999), Some(250));
    assert_eq!(tree.get(&25), Some(&999));
    assert_eq!(tree.len(), 50);

    // Sorted iteration
    let keys: Vec<u64> = tree.keys().copied().collect();
    let mut sorted = keys.clone();
    sorted.sort_unstable();
    assert_eq!(keys, sorted);

    tree.clear(&slab);
}

// =============================================================================
// SlabOps trait — generic over bounded/unbounded
// =============================================================================

#[test]
fn slab_ops_trait_generic() {
    use nexus_collections::slab::SlabOps;

    fn insert_and_remove<S: SlabOps<RbNode<u64, u64>>>(tree: &mut RbTree<u64, u64>, slab: &S) {
        // We can't insert generically (try_insert needs concrete slab type),
        // but we can remove and clear generically.
        tree.remove(slab, &1);
        tree.clear(slab);
    }

    // Test with bounded slab
    let bounded_slab: Slab<RbNode<u64, u64>> = unsafe { Slab::with_capacity(100) };
    let mut tree = RbTree::new();
    tree.try_insert(&bounded_slab, 1, 10).unwrap();
    tree.try_insert(&bounded_slab, 2, 20).unwrap();
    insert_and_remove(&mut tree, &bounded_slab);
    assert!(tree.is_empty());

    // Test with unbounded slab
    let unbounded_slab: UnboundedSlab<RbNode<u64, u64>> =
        unsafe { UnboundedSlab::with_chunk_capacity(8) };
    let mut tree = RbTree::new();
    tree.insert(&unbounded_slab, 1, 10);
    tree.insert(&unbounded_slab, 2, 20);
    insert_and_remove(&mut tree, &unbounded_slab);
    assert!(tree.is_empty());
}

// =============================================================================
// Debug-mode Drop detection
// =============================================================================

/// Verifies that dropping a non-empty RbTree panics in debug builds,
/// catching the leak-without-clear() mistake.
#[test]
#[cfg(debug_assertions)]
fn drop_non_empty_tree_panics() {
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let slab: UnboundedSlab<RbNode<u64, u64>> =
            unsafe { UnboundedSlab::with_chunk_capacity(8) };
        let mut tree = RbTree::new();
        tree.insert(&slab, 1, 100);
        // tree dropped here without clear() — should panic
    }));
    let err = result.expect_err("non-empty tree drop should panic in debug");
    let msg = err
        .downcast_ref::<String>()
        .map(std::string::String::as_str)
        .or_else(|| err.downcast_ref::<&str>().copied())
        .unwrap_or("");
    assert!(
        msg.contains("RbTree dropped with"),
        "unexpected panic message: {msg}"
    );
}

/// Verifies the Drop guard does NOT fire during unwinding (no double-panic).
#[test]
#[cfg(debug_assertions)]
fn drop_non_empty_tree_during_unwind_no_double_panic() {
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let slab: UnboundedSlab<RbNode<u64, u64>> =
            unsafe { UnboundedSlab::with_chunk_capacity(8) };
        let mut tree = RbTree::new();
        tree.insert(&slab, 1, 100);
        panic!("intentional outer panic");
    }));
    let err = result.expect_err("should have panicked");
    let msg = err.downcast_ref::<&str>().copied().unwrap_or("");
    assert_eq!(
        msg, "intentional outer panic",
        "should be the outer panic, not the drop panic"
    );
}

#[cfg(debug_assertions)]
#[test]
fn non_empty_drop_panics_in_debug() {
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let slab = unsafe { UnboundedSlab::with_chunk_capacity(8) };
        let mut tree = RbTree::<u64, u64>::new();
        tree.insert(&slab, 1, 100);
        // drop without clear — should panic in debug
    }));
    assert!(
        result.is_err(),
        "dropping non-empty rbtree should panic in debug"
    );
}
