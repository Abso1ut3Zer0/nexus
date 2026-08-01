//! Comprehensive tests for the raw Slab API.
//!
//! This test suite covers:
//! - Basic operations (bounded and unbounded)
//! - Drop semantics and tracking
//! - Stress tests and freelist integrity
//! - Edge cases and boundary conditions
//! - Complex types (String, Vec, ZST, large)

use nexus_slab::Slot;
use nexus_slab::bounded::Slab as BoundedSlab;
use nexus_slab::unbounded::Slab as UnboundedSlab;
use std::cell::Cell;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

// =============================================================================
// Helper Types
// =============================================================================

thread_local! {
    static DROP_COUNT: Cell<usize> = const { Cell::new(0) };
}

#[derive(Debug)]
pub struct DropTracker(pub u64);

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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ZeroSized;

pub struct LargeStruct {
    pub data: [u64; 128],
}

pub struct OrderedDrop {
    pub id: usize,
}

static DROP_ORDER: AtomicUsize = AtomicUsize::new(0);

impl Drop for OrderedDrop {
    fn drop(&mut self) {
        DROP_ORDER.fetch_add(1, Ordering::SeqCst);
    }
}

// =============================================================================
// Basic Operations - Bounded
// =============================================================================

#[test]
fn bounded_basic_insert_drop() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(16) };

    assert_eq!(slab.capacity(), 16);

    let slot = slab.alloc(42);
    assert_eq!(*slot, 42);
    // SAFETY: slot was allocated from this slab
    slab.free(slot);
}

#[test]
fn bounded_fill_to_capacity() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(8) };

    let slots: Vec<_> = (0..8).map(|i| slab.alloc(i)).collect();

    assert_eq!(slab.capacity(), 8);
    assert!(slab.try_alloc(100).is_err());

    for (i, slot) in slots.iter().enumerate() {
        assert_eq!(**slot, i as u64);
    }

    // SAFETY: all slots were allocated from this slab
    for slot in slots {
        slab.free(slot);
    }
}

#[test]
fn bounded_capacity_one() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(1) };

    assert_eq!(slab.capacity(), 1);

    let slot = slab.alloc(42);
    assert!(slab.try_alloc(100).is_err());

    // SAFETY: slot was allocated from this slab
    slab.free(slot);

    let slot2 = slab.alloc(100);
    assert_eq!(*slot2, 100);
    // SAFETY: slot2 was allocated from this slab
    slab.free(slot2);
}

// =============================================================================
// Basic Operations - Unbounded
// =============================================================================

#[test]
fn unbounded_basic_insert_drop() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { UnboundedSlab::<u64>::with_chunk_capacity(8) };

    let slot = slab.alloc(100);
    assert_eq!(*slot, 100);
    // SAFETY: slot was allocated from this slab
    slab.free(slot);
}

#[test]
fn unbounded_grows_automatically() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { UnboundedSlab::<u64>::with_chunk_capacity(4) };

    let initial_cap = slab.capacity();

    // Insert more than initial chunk
    let slots: Vec<_> = (0..20).map(|i| slab.alloc(i)).collect();

    assert!(slab.capacity() >= 20);
    assert!(slab.capacity() > initial_cap);

    for (i, slot) in slots.iter().enumerate() {
        assert_eq!(**slot, i as u64);
    }

    // SAFETY: all slots were allocated from this slab
    for slot in slots {
        slab.free(slot);
    }
}

// =============================================================================
// Slot Operations
// =============================================================================

#[test]
fn slot_deref() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(4) };

    let mut slot = slab.alloc(42);
    assert_eq!(*slot, 42);

    *slot = 100;
    assert_eq!(*slot, 100);

    // SAFETY: slot was allocated from this slab
    slab.free(slot);
}

#[test]
fn slot_dealloc_take() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<String>::with_capacity(4) };

    let slot = slab.alloc("hello".to_string());
    // SAFETY: slot was allocated from this slab
    let value = slab.take(slot);

    assert_eq!(value, "hello");
}

#[test]
fn slot_debug_format() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(4) };

    let slot = slab.alloc(42);
    let debug = format!("{:?}", slot);
    assert!(debug.contains("Slot"));
    // SAFETY: slot was allocated from this slab
    slab.free(slot);
}

#[test]
fn slot_size_is_8_bytes() {
    // Slot<T> is 8 bytes (one pointer)
    assert_eq!(std::mem::size_of::<Slot<u64>>(), 8);
    assert_eq!(std::mem::size_of::<Slot<String>>(), 8);
    assert_eq!(std::mem::size_of::<Slot<[u8; 1024]>>(), 8);
}

// =============================================================================
// Multiple Slots and Slabs
// =============================================================================

#[test]
fn multiple_slots_same_slab() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(10) };

    let slot1 = slab.alloc(1);
    let slot2 = slab.alloc(2);
    let slot3 = slab.alloc(3);

    assert_eq!(*slot1, 1);
    assert_eq!(*slot2, 2);
    assert_eq!(*slot3, 3);

    // Pointers should be different
    assert_ne!(slot1.as_ptr(), slot2.as_ptr());
    assert_ne!(slot2.as_ptr(), slot3.as_ptr());
    assert_ne!(slot1.as_ptr(), slot3.as_ptr());

    // SAFETY: slot2 was allocated from this slab
    slab.free(slot2);

    // Insert again - should reuse slot2's slot
    let slot4 = slab.alloc(4);
    assert_eq!(*slot4, 4);

    slab.free(slot1);
    slab.free(slot3);
    slab.free(slot4);
}

#[test]
fn multiple_slabs_independent() {
    // SAFETY: test slabs; single-threaded, all slots freed before drop.
    let slab_a = unsafe { BoundedSlab::<u64>::with_capacity(4) };
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab_b = unsafe { BoundedSlab::<u64>::with_capacity(4) };

    let slot_a = slab_a.alloc(1);
    let slot_b = slab_b.alloc(2);

    assert_eq!(*slot_a, 1);
    assert_eq!(*slot_b, 2);

    slab_a.free(slot_a);
    slab_b.free(slot_b);
}

// =============================================================================
// Panic Tests
// =============================================================================

#[test]
#[should_panic(expected = "slab full")]
fn panic_insert_when_full() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(2) };

    let _s1 = slab.alloc(1);
    let _s2 = slab.alloc(2);
    let _ = slab.alloc(3); // Should panic
}

#[test]
#[should_panic(expected = "capacity must be non-zero")]
fn panic_zero_capacity() {
    // SAFETY: test slab; single-threaded; panics before any slot can be allocated.
    let _ = unsafe { BoundedSlab::<u64>::with_capacity(0) };
}

// =============================================================================
// Drop Semantics (via explicit free)
// =============================================================================

#[test]
fn drop_called_on_free() {
    reset_drop_count();

    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<DropTracker>::with_capacity(4) };

    let slot = slab.alloc(DropTracker(1));
    assert_eq!(get_drop_count(), 0);

    // SAFETY: slot was allocated from this slab
    slab.free(slot);

    assert_eq!(get_drop_count(), 1);
}

#[test]
fn drop_called_multiple() {
    reset_drop_count();

    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<DropTracker>::with_capacity(10) };

    let s1 = slab.alloc(DropTracker(1));
    let s2 = slab.alloc(DropTracker(2));
    let s3 = slab.alloc(DropTracker(3));
    assert_eq!(get_drop_count(), 0);

    slab.free(s1);
    slab.free(s2);
    slab.free(s3);

    assert_eq!(get_drop_count(), 3);
}

#[test]
fn drop_called_on_dealloc_take() {
    reset_drop_count();

    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<DropTracker>::with_capacity(4) };

    let slot = slab.alloc(DropTracker(1));
    // SAFETY: slot was allocated from this slab
    let value = slab.take(slot);
    assert_eq!(get_drop_count(), 0); // Not dropped yet - returned

    drop(value);
    assert_eq!(get_drop_count(), 1); // Now dropped
}

#[test]
fn drop_not_called_on_leak() {
    reset_drop_count();

    // SAFETY: test slab; single-threaded; slot intentionally leaked (disarmed via into_raw).
    let slab = unsafe { BoundedSlab::<DropTracker>::with_capacity(4) };

    let slot = slab.alloc(DropTracker(1));
    // Intentionally leak — disarm debug Drop via into_raw()
    let _ = slot.into_raw();

    assert_eq!(get_drop_count(), 0); // Leaked, not dropped
}

// =============================================================================
// Stress Tests and Freelist Integrity
// =============================================================================

#[test]
fn stress_fill_drain_cycle() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(100) };

    for cycle in 0..10 {
        // Fill
        let slots: Vec<_> = (0..100).map(|i| slab.alloc(i + cycle * 100)).collect();

        // Verify values
        for (i, slot) in slots.iter().enumerate() {
            assert_eq!(**slot, (i + cycle as usize * 100) as u64);
        }

        // Drain
        // SAFETY: all slots were allocated from this slab
        for slot in slots {
            slab.free(slot);
        }
    }
}

#[test]
fn stress_interleaved_insert_remove() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(50) };

    let mut slots = Vec::new();

    for i in 0..1000 {
        if i % 2 == 0 || slots.is_empty() {
            // Insert
            if slots.len() < 50 {
                slots.push(slab.alloc(i));
            }
        } else {
            // Remove
            if let Some(slot) = slots.pop() {
                // SAFETY: slot was allocated from this slab
                slab.free(slot);
            }
        }
    }

    // Clean up remaining
    for slot in slots {
        // SAFETY: slot was allocated from this slab
        slab.free(slot);
    }
}

#[test]
fn stress_slot_reuse() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(1) };

    for i in 0..1000 {
        let slot = slab.alloc(i);
        assert_eq!(*slot, i);
        // SAFETY: slot was allocated from this slab
        slab.free(slot);
    }
}

#[test]
fn stress_unbounded_growth() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { UnboundedSlab::<u64>::with_chunk_capacity(16) };

    let slots: Vec<_> = (0..1000).map(|i| slab.alloc(i)).collect();

    assert!(slab.capacity() >= 1000);

    for (i, slot) in slots.iter().enumerate() {
        assert_eq!(**slot, i as u64);
    }

    // SAFETY: all slots were allocated from this slab
    for slot in slots {
        slab.free(slot);
    }
}

#[test]
fn stress_unbounded_churn() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { UnboundedSlab::<u64>::with_chunk_capacity(8) };

    let mut slots = Vec::new();

    for i in 0..500 {
        // Add some
        for j in 0..5 {
            slots.push(slab.alloc((i * 5 + j) as u64));
        }

        // Remove some
        for _ in 0..3 {
            if !slots.is_empty() {
                let idx = i % slots.len().max(1);
                let slot = slots.swap_remove(idx);
                // SAFETY: slot was allocated from this slab
                slab.free(slot);
            }
        }
    }

    // Clean up
    for slot in slots {
        // SAFETY: slot was allocated from this slab
        slab.free(slot);
    }
}

#[test]
fn freelist_lifo_order() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(4) };

    // Insert 4 items
    let s0 = slab.alloc(0);
    let s1 = slab.alloc(1);
    let s2 = slab.alloc(2);
    let s3 = slab.alloc(3);

    // Save pointers for comparison
    let p1 = s1.as_ptr();
    let p3 = s3.as_ptr();

    // Free in order: s1, s3
    slab.free(s1);
    slab.free(s3);

    // Freelist should have: s3 -> s1 (LIFO)
    // Next insert should get s3's slot
    let new1 = slab.alloc(100);
    assert_eq!(new1.as_ptr(), p3);

    let new2 = slab.alloc(101);
    assert_eq!(new2.as_ptr(), p1);

    slab.free(s0);
    slab.free(s2);
    slab.free(new1);
    slab.free(new2);
}

// =============================================================================
// Complex Types
// =============================================================================

#[test]
fn type_string() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<String>::with_capacity(10) };

    let slot = slab.alloc("hello world".to_string());
    assert_eq!(*slot, "hello world");

    // SAFETY: slot was allocated from this slab
    let value = slab.take(slot);
    assert_eq!(value, "hello world");
}

#[test]
fn type_vec() {
    // SAFETY: slab outlives all slots
    let slab = unsafe { BoundedSlab::<Vec<u64>>::with_capacity(10) };

    let slot = slab.alloc(vec![1, 2, 3, 4, 5]);
    assert_eq!(slot.len(), 5);
    assert_eq!(slot[2], 3);

    // SAFETY: slot was allocated from this slab
    slab.free(slot);
}

#[test]
fn type_box() {
    // SAFETY: slab outlives all slots
    let slab = unsafe { BoundedSlab::<Box<u64>>::with_capacity(10) };

    let slot = slab.alloc(Box::new(42));
    assert_eq!(**slot, 42);

    // SAFETY: slot was allocated from this slab
    slab.free(slot);
}

#[test]
fn type_rc() {
    // SAFETY: slab outlives all slots
    let slab = unsafe { BoundedSlab::<Rc<u64>>::with_capacity(10) };

    let rc = Rc::new(42);
    let slot = slab.alloc(rc.clone());

    assert_eq!(Rc::strong_count(&rc), 2);
    // SAFETY: slot was allocated from this slab
    slab.free(slot);
    assert_eq!(Rc::strong_count(&rc), 1);
}

#[test]
fn type_option() {
    // SAFETY: slab outlives all slots
    let slab = unsafe { BoundedSlab::<Option<String>>::with_capacity(10) };

    let slot1 = slab.alloc(Some("hello".to_string()));
    let slot2 = slab.alloc(None);

    assert_eq!(*slot1, Some("hello".to_string()));
    assert_eq!(*slot2, None);

    slab.free(slot1);
    slab.free(slot2);
}

#[test]
fn type_tuple() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<(u64, String, bool)>::with_capacity(10) };

    let slot = slab.alloc((42, "hello".to_string(), true));
    assert_eq!(slot.0, 42);
    assert_eq!(slot.1, "hello");
    assert!(slot.2);

    // SAFETY: slot was allocated from this slab
    slab.free(slot);
}

#[test]
fn type_large_struct() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<LargeStruct>::with_capacity(10) };

    let mut data = [0u64; 128];
    for (i, d) in data.iter_mut().enumerate() {
        *d = i as u64;
    }

    let slot = slab.alloc(LargeStruct { data });

    for (i, &d) in slot.data.iter().enumerate() {
        assert_eq!(d, i as u64);
    }

    // SAFETY: slot was allocated from this slab
    slab.free(slot);
}

#[test]
fn type_zst() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<ZeroSized>::with_capacity(100) };

    assert_eq!(std::mem::size_of::<ZeroSized>(), 0);

    let slot = slab.alloc(ZeroSized);
    assert_eq!(*slot, ZeroSized);

    // SAFETY: slot was allocated from this slab
    slab.free(slot);
}

#[test]
fn type_unit() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<()>::with_capacity(10) };

    let slot = slab.alloc(());
    assert_eq!(*slot, ());

    // SAFETY: slot was allocated from this slab
    slab.free(slot);
}

// =============================================================================
// Edge Cases
// =============================================================================

#[test]
fn large_capacity() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(100_000) };

    assert_eq!(slab.capacity(), 100_000);

    let slots: Vec<_> = (0..1000).map(|i| slab.alloc(i)).collect();

    // SAFETY: all slots were allocated from this slab
    for slot in slots {
        slab.free(slot);
    }
}

#[test]
fn unbounded_default_chunk_capacity() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { UnboundedSlab::<u64>::with_chunk_capacity(4096) };

    // First insert should trigger chunk allocation
    let slot = slab.alloc(42);
    assert!(slab.capacity() >= 1);

    // SAFETY: slot was allocated from this slab
    slab.free(slot);
}

#[test]
fn slab_debug_format() {
    // SAFETY: test slab; single-threaded, no slots allocated.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(10) };
    let debug = format!("{:?}", slab);
    assert!(debug.contains("Slab"));
    assert!(debug.contains("capacity"));
}

// =============================================================================
// Slot::clone_ptr
// =============================================================================

#[test]
fn slot_clone_ptr() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(4) };

    let slot = slab.alloc(42);
    // SAFETY: we will free the original before the clone becomes dangling,
    // but clone_ptr's contract only requires the slot not be freed while
    // any clone exists — we verify both point to the same value first.
    let clone = unsafe { slot.clone_ptr() };

    assert_eq!(*slot, 42);
    assert_eq!(*clone, 42);
    assert_eq!(slot.as_ptr(), clone.as_ptr());

    // Free the original. The clone is now dangling — that's the unsafe
    // contract. We disarm it via into_raw to avoid the debug drop detector.
    slab.free(slot);
    let _ = clone.into_raw();
}

// =============================================================================
// Byte slab with Drop types
// =============================================================================

#[test]
fn byte_slab_drop_type() {
    use nexus_slab::byte::bounded::Slab as ByteSlab;

    reset_drop_count();

    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab: ByteSlab<64> = unsafe { ByteSlab::with_capacity(4) };

    // Alloc a String (heap-allocated, has Drop)
    let slot = slab.alloc(String::from("hello byte slab"));
    assert_eq!(&*slot, "hello byte slab");
    assert_eq!(get_drop_count(), 0);

    // Free should drop the String
    slab.free(slot);
    assert_eq!(get_drop_count(), 0); // String doesn't use our DropTracker

    // Now test with our DropTracker
    let slot = slab.alloc(DropTracker(99));
    assert_eq!(get_drop_count(), 0);
    slab.free(slot);
    assert_eq!(get_drop_count(), 1);
}

#[test]
fn byte_slab_drop_on_take() {
    use nexus_slab::byte::bounded::Slab as ByteSlab;

    reset_drop_count();

    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab: ByteSlab<64> = unsafe { ByteSlab::with_capacity(4) };

    let slot = slab.alloc(DropTracker(1));
    assert_eq!(get_drop_count(), 0);

    // take extracts without dropping
    let val = slab.take(slot);
    assert_eq!(get_drop_count(), 0);

    // dropping the returned value triggers the drop
    drop(val);
    assert_eq!(get_drop_count(), 1);
}
