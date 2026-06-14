//! Tests for custom comparator support (Reverse ordering).

use nexus_collections::slab::Reverse;
use nexus_collections::slab::btree::{BTree, BTreeNode};
use nexus_collections::slab::rbtree::{RbNode, RbTree};
use nexus_slab::bounded::Slab;

fn make_rb_slab() -> Slab<RbNode<u64, String>> {
    unsafe { Slab::with_capacity(200) }
}

fn make_bt_slab() -> Slab<BTreeNode<u64, String, 8>> {
    unsafe { Slab::with_capacity(500) }
}

// =============================================================================
// RbTree with Reverse
// =============================================================================

#[test]
fn rbtree_reverse_first_last() {
    let slab = make_rb_slab();
    let mut map = RbTree::with_comparator(Reverse);
    map.try_insert(&slab, 10, "ten".into()).unwrap();
    map.try_insert(&slab, 30, "thirty".into()).unwrap();
    map.try_insert(&slab, 20, "twenty".into()).unwrap();

    assert_eq!(map.first_key_value(), Some((&30, &"thirty".into())));
    assert_eq!(map.last_key_value(), Some((&10, &"ten".into())));
    map.verify_invariants();
    map.clear(&slab);
}

#[test]
fn rbtree_reverse_pop_first() {
    let slab = make_rb_slab();
    let mut map = RbTree::with_comparator(Reverse);
    for k in [50, 30, 80, 10, 70, 20, 60, 40] {
        map.try_insert(&slab, k, format!("{k}")).unwrap();
    }
    map.verify_invariants();

    let mut popped = Vec::new();
    while let Some((k, _)) = map.pop_first(&slab) {
        popped.push(k);
        map.verify_invariants();
    }
    assert_eq!(popped, vec![80, 70, 60, 50, 40, 30, 20, 10]);
}

#[test]
fn rbtree_reverse_iteration_order() {
    let slab = make_rb_slab();
    let mut map = RbTree::with_comparator(Reverse);
    for k in 1..=5 {
        map.try_insert(&slab, k, format!("{k}")).unwrap();
    }

    let keys: Vec<u64> = map.iter().map(|(&k, _)| k).collect();
    assert_eq!(keys, vec![5, 4, 3, 2, 1]);

    map.clear(&slab);
}

#[test]
fn rbtree_reverse_get_and_remove() {
    let slab = make_rb_slab();
    let mut map = RbTree::with_comparator(Reverse);
    map.try_insert(&slab, 10, "ten".into()).unwrap();
    map.try_insert(&slab, 20, "twenty".into()).unwrap();

    assert_eq!(map.get(&10), Some(&"ten".into()));
    assert_eq!(map.get(&20), Some(&"twenty".into()));
    assert_eq!(map.get(&99), None);

    assert_eq!(map.remove(&slab, &10), Some("ten".into()));
    assert_eq!(map.len(), 1);
    assert_eq!(map.get(&10), None);
    map.verify_invariants();
    map.clear(&slab);
}

#[test]
fn rbtree_reverse_stress() {
    let slab = make_rb_slab();
    let mut map = RbTree::with_comparator(Reverse);
    for k in 0..100 {
        map.try_insert(&slab, k, format!("{k}")).unwrap();
    }
    map.verify_invariants();
    assert_eq!(map.len(), 100);

    let keys: Vec<u64> = map.iter().map(|(&k, _)| k).collect();
    assert_eq!(keys, (0..100).rev().collect::<Vec<_>>());

    for k in (0..100).step_by(2) {
        map.remove(&slab, &k);
    }
    map.verify_invariants();
    assert_eq!(map.len(), 50);
    map.clear(&slab);
}

// =============================================================================
// BTree with Reverse
// =============================================================================

#[test]
fn btree_reverse_first_last() {
    let slab = make_bt_slab();
    let mut map = BTree::<u64, String, 8, Reverse>::with_comparator(Reverse);
    map.try_insert(&slab, 10, "ten".into()).unwrap();
    map.try_insert(&slab, 30, "thirty".into()).unwrap();
    map.try_insert(&slab, 20, "twenty".into()).unwrap();

    assert_eq!(map.first_key_value(), Some((&30, &"thirty".into())));
    assert_eq!(map.last_key_value(), Some((&10, &"ten".into())));
    map.verify_invariants();
    map.clear(&slab);
}

#[test]
fn btree_reverse_pop_first() {
    let slab = make_bt_slab();
    let mut map = BTree::<u64, String, 8, Reverse>::with_comparator(Reverse);
    for k in [50, 30, 80, 10, 70, 20, 60, 40] {
        map.try_insert(&slab, k, format!("{k}")).unwrap();
    }
    map.verify_invariants();

    let mut popped = Vec::new();
    while let Some((k, _)) = map.pop_first(&slab) {
        popped.push(k);
        map.verify_invariants();
    }
    assert_eq!(popped, vec![80, 70, 60, 50, 40, 30, 20, 10]);
}

#[test]
fn btree_reverse_iteration_order() {
    let slab = make_bt_slab();
    let mut map = BTree::<u64, String, 8, Reverse>::with_comparator(Reverse);
    for k in 1..=5 {
        map.try_insert(&slab, k, format!("{k}")).unwrap();
    }

    let keys: Vec<u64> = map.iter().map(|(&k, _)| k).collect();
    assert_eq!(keys, vec![5, 4, 3, 2, 1]);

    map.clear(&slab);
}

#[test]
fn btree_reverse_stress() {
    let slab = make_bt_slab();
    let mut map = BTree::<u64, String, 8, Reverse>::with_comparator(Reverse);
    for k in 0..100 {
        map.try_insert(&slab, k, format!("{k}")).unwrap();
    }
    map.verify_invariants();
    assert_eq!(map.len(), 100);

    let keys: Vec<u64> = map.iter().map(|(&k, _)| k).collect();
    assert_eq!(keys, (0..100).rev().collect::<Vec<_>>());

    for k in (0..100).step_by(2) {
        map.remove(&slab, &k);
    }
    map.verify_invariants();
    assert_eq!(map.len(), 50);
    map.clear(&slab);
}
