//! Integration tests for cursor operations.

use nexus_collections::slab::list::{List, ListNode};
use nexus_slab::rc::bounded::Slab;

fn make_slab() -> Slab<ListNode<u64>> {
    unsafe { Slab::with_capacity(100) }
}

#[test]
fn cursor_forward_scan() {
    let slab = make_slab();
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
fn cursor_backward_scan() {
    let slab = make_slab();
    let mut list = List::new();

    let h1 = list.try_push_back(&slab, 10).unwrap();
    let h2 = list.try_push_back(&slab, 20).unwrap();
    let h3 = list.try_push_back(&slab, 30).unwrap();

    let mut values = Vec::new();
    let mut cursor = list.cursor_back();
    while cursor.advance_back() {
        values.push(cursor.current().unwrap().value);
    }
    assert_eq!(values, vec![30, 20, 10]);

    let _ = cursor;
    list.clear(&slab);
    slab.free(h1);
    slab.free(h2);
    slab.free(h3);
}

#[test]
fn cursor_remove_middle() {
    let slab = make_slab();
    let mut list = List::new();

    let h1 = list.try_push_back(&slab, 10).unwrap();
    let h2 = list.try_push_back(&slab, 20).unwrap();
    let h3 = list.try_push_back(&slab, 30).unwrap();

    let mut cursor = list.cursor();
    cursor.advance(); // 10
    cursor.advance(); // 20
    let removed = cursor.remove();
    assert_eq!(removed.borrow().value, 20);

    // Should now be at 30
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
fn cursor_remove_if() {
    let slab = make_slab();
    let mut list = List::new();

    let h1 = list.try_push_back(&slab, 10).unwrap();
    let h2 = list.try_push_back(&slab, 20).unwrap();
    let h3 = list.try_push_back(&slab, 30).unwrap();

    let mut cursor = list.cursor();
    cursor.advance(); // 10
    let not_removed = cursor.remove_if(|n| n.value > 100);
    assert!(not_removed.is_none());

    let removed = cursor.remove_if(|n| n.value == 10);
    assert!(removed.is_some());
    let removed = removed.unwrap();
    assert_eq!(removed.borrow().value, 10);

    let _ = cursor;
    assert_eq!(list.len(), 2);

    list.clear(&slab);
    slab.free(h1);
    slab.free(h2);
    slab.free(h3);
    slab.free(removed);
}

#[test]
fn cursor_empty_list() {
    let mut list = List::<u64>::new();
    let mut cursor = list.cursor();
    assert!(!cursor.advance());
    assert!(cursor.current().is_none());
}

#[test]
#[should_panic(expected = "cursor is not positioned at a node")]
fn cursor_remove_before_start_panics() {
    let mut list = List::<u64>::new();
    let mut cursor = list.cursor();
    cursor.remove(); // should panic — at BeforeStart
}
