//! Miri-specific tests for memory safety verification.
//!
//! Run with: `MIRIFLAGS="-Zmiri-ignore-leaks" cargo +nightly miri test --test miri_tests`
//!
//! The `-Zmiri-ignore-leaks` flag is required because:
//! - Slabs are intentionally leaked (Box::leak for stable addresses)
//! - Leaked slots (via `slot.leak()`) are intentionally not freed
//!
//! These tests verify:
//! - No use-after-free
//! - No double-free
//! - No uninitialized memory access
//! - No invalid pointer arithmetic
//! - Correct drop ordering

use nexus_slab::bounded::Slab as BoundedSlab;
use nexus_slab::unbounded::Slab as UnboundedSlab;
use std::cell::Cell;

// =============================================================================
// Helper Types
// =============================================================================

thread_local! {
    static DROP_COUNT: Cell<usize> = const { Cell::new(0) };
}

#[derive(Debug)]
pub struct DropTracker(#[allow(dead_code)] u64);

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

#[derive(Clone)]
pub struct Large {
    data: [u64; 128],
}

// =============================================================================
// Basic Memory Safety
// =============================================================================

#[test]
fn miri_bounded_basic() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(8) };

    let slot = slab.alloc(42);
    assert_eq!(*slot, 42);
    // SAFETY: slot was allocated from this slab
    slab.free(slot);
}

#[test]
fn miri_unbounded_basic() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { UnboundedSlab::<u64>::with_chunk_capacity(4) };

    let slot = slab.alloc(42);
    assert_eq!(*slot, 42);
    // SAFETY: slot was allocated from this slab
    slab.free(slot);
}

#[test]
fn miri_multiple_inserts() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(8) };

    let s1 = slab.alloc(1);
    let s2 = slab.alloc(2);
    let s3 = slab.alloc(3);

    assert_eq!(*s1, 1);
    assert_eq!(*s2, 2);
    assert_eq!(*s3, 3);

    slab.free(s1);
    slab.free(s2);
    slab.free(s3);
}

#[test]
fn miri_slot_deref_mut() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(4) };

    let mut slot = slab.alloc(42);
    *slot = 100;
    assert_eq!(*slot, 100);

    // SAFETY: slot was allocated from this slab
    slab.free(slot);
}

#[test]
fn miri_slot_replace() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(4) };

    let mut slot = slab.alloc(1);
    let old = std::mem::replace(&mut *slot, 2);
    assert_eq!(old, 1);
    assert_eq!(*slot, 2);

    // SAFETY: slot was allocated from this slab
    slab.free(slot);
}

#[test]
fn miri_slot_into_inner() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(4) };

    let slot = slab.alloc(42);
    // SAFETY: slot was allocated from this slab
    let value = slab.take(slot);
    assert_eq!(value, 42);
}

// =============================================================================
// Drop Safety
// =============================================================================

#[test]
fn miri_drop_on_slot_drop() {
    reset_drop_count();

    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<DropTracker>::with_capacity(4) };

    {
        let slot = slab.alloc(DropTracker(1));
        // SAFETY: slot was allocated from this slab
        slab.free(slot);
    }

    assert_eq!(get_drop_count(), 1);
}

#[test]
fn miri_drop_on_into_inner() {
    reset_drop_count();

    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<DropTracker>::with_capacity(4) };

    let slot = slab.alloc(DropTracker(1));
    // SAFETY: slot was allocated from this slab
    let value = slab.take(slot);
    assert_eq!(get_drop_count(), 0);

    drop(value);
    assert_eq!(get_drop_count(), 1);
}

#[test]
fn miri_drop_on_replace() {
    reset_drop_count();

    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<DropTracker>::with_capacity(4) };

    let mut slot = slab.alloc(DropTracker(1));
    let old = std::mem::replace(&mut *slot, DropTracker(2));
    drop(old);
    assert_eq!(get_drop_count(), 1);

    // SAFETY: slot was allocated from this slab
    slab.free(slot);
    assert_eq!(get_drop_count(), 2);
}

#[test]
fn miri_no_drop_after_leak() {
    reset_drop_count();

    // SAFETY: test slab; single-threaded; slot intentionally leaked (tests drop suppression).
    let slab = unsafe { BoundedSlab::<DropTracker>::with_capacity(4) };

    let slot = slab.alloc(DropTracker(1));
    // Intentionally leak — disarm debug Drop via into_raw()
    let _ = slot.into_raw();

    assert_eq!(get_drop_count(), 0);
}

// =============================================================================
// Heap-Allocated Types
// =============================================================================

#[test]
fn miri_string_insert_drop() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<String>::with_capacity(4) };

    let slot = slab.alloc("hello world".to_string());
    assert_eq!(*slot, "hello world");
    // SAFETY: slot was allocated from this slab
    slab.free(slot);
}

#[test]
fn miri_vec_insert_drop() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<Vec<u64>>::with_capacity(4) };

    let slot = slab.alloc(vec![1, 2, 3, 4, 5]);
    assert_eq!(slot.len(), 5);
    // SAFETY: slot was allocated from this slab
    slab.free(slot);
}

#[test]
fn miri_box_insert_drop() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<Box<[u8; 1024]>>::with_capacity(4) };

    let slot = slab.alloc(Box::new([0u8; 1024]));
    assert_eq!(slot.len(), 1024);
    // SAFETY: slot was allocated from this slab
    slab.free(slot);
}

#[test]
fn miri_string_into_inner() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<String>::with_capacity(4) };

    let slot = slab.alloc("hello".to_string());
    // SAFETY: slot was allocated from this slab
    let value = slab.take(slot);
    assert_eq!(value, "hello");
}

#[test]
fn miri_vec_replace() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<Vec<u64>>::with_capacity(4) };

    let mut slot = slab.alloc(vec![1, 2, 3]);
    let old = std::mem::replace(&mut *slot, vec![4, 5, 6, 7]);

    assert_eq!(old, vec![1, 2, 3]);
    assert_eq!(*slot, vec![4, 5, 6, 7]);

    // SAFETY: slot was allocated from this slab
    slab.free(slot);
}

// =============================================================================
// Slot Reuse
// =============================================================================

#[test]
fn miri_slot_reuse_bounded() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<String>::with_capacity(2) };

    // Fill
    let s1 = slab.alloc("one".to_string());
    let s2 = slab.alloc("two".to_string());

    let p1 = s1.as_ptr();
    let p2 = s2.as_ptr();

    // Dealloc one
    // SAFETY: slot was allocated from this slab
    slab.free(s1);

    // Reuse
    let s3 = slab.alloc("three".to_string());
    assert_eq!(*s3, "three");
    assert_eq!(s3.as_ptr(), p1); // Reused slot 1

    // Dealloc other
    // SAFETY: slot was allocated from this slab
    slab.free(s2);

    // Reuse again
    let s4 = slab.alloc("four".to_string());
    assert_eq!(*s4, "four");
    assert_eq!(s4.as_ptr(), p2); // Reused slot 2

    // Clean up
    slab.free(s3);
    slab.free(s4);
}

#[test]
fn miri_slot_reuse_single() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<String>::with_capacity(1) };

    let mut last_ptr = std::ptr::null_mut();
    for i in 0..10 {
        let slot = slab.alloc(format!("value_{}", i));
        assert_eq!(*slot, format!("value_{}", i));
        // After first iteration, should always reuse same slot
        if i > 0 {
            assert_eq!(slot.as_ptr(), last_ptr);
        }
        last_ptr = slot.as_ptr();
        // SAFETY: slot was allocated from this slab
        slab.free(slot);
    }
}

// =============================================================================
// Unbounded Growth
// =============================================================================

#[test]
fn miri_unbounded_growth() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { UnboundedSlab::<u64>::with_chunk_capacity(4) };

    // Fill multiple chunks
    let slots: Vec<_> = (0..12).map(|i| slab.alloc(i)).collect();

    assert!(slab.capacity() >= 12);

    for (i, slot) in slots.iter().enumerate() {
        assert_eq!(**slot, i as u64);
    }

    // Clean up
    for slot in slots {
        // SAFETY: slot was allocated from this slab
        slab.free(slot);
    }
}

#[test]
fn miri_unbounded_string_growth() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { UnboundedSlab::<String>::with_chunk_capacity(4) };

    let slots: Vec<_> = (0..12)
        .map(|i| slab.alloc(format!("string_{}", i)))
        .collect();

    for (i, slot) in slots.iter().enumerate() {
        assert_eq!(**slot, format!("string_{}", i));
    }

    // Clean up
    for slot in slots {
        // SAFETY: slot was allocated from this slab
        slab.free(slot);
    }
}

// =============================================================================
// Edge Cases
// =============================================================================

#[test]
fn miri_capacity_one() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(1) };

    let slot = slab.alloc(42);
    assert!(slab.try_alloc(100).is_err());
    // SAFETY: slot was allocated from this slab
    slab.free(slot);

    let slot2 = slab.alloc(100);
    assert_eq!(*slot2, 100);
    // SAFETY: slot was allocated from this slab
    slab.free(slot2);
}

#[test]
fn miri_zst() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<ZeroSized>::with_capacity(10) };

    let slot = slab.alloc(ZeroSized);
    assert_eq!(*slot, ZeroSized);
    // SAFETY: slot was allocated from this slab
    slab.free(slot);
}

#[test]
fn miri_large_struct() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<Large>::with_capacity(4) };

    let mut data = [0u64; 128];
    for (i, d) in data.iter_mut().enumerate() {
        *d = i as u64;
    }

    let slot = slab.alloc(Large { data });
    assert_eq!(slot.data[0], 0);
    assert_eq!(slot.data[127], 127);

    // SAFETY: slot was allocated from this slab
    slab.free(slot);
}

// =============================================================================
// Claim Abandonment (H5)
// =============================================================================

#[test]
fn miri_bounded_claim_abandon() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(4) };

    // Claim and abandon — should return slot to freelist
    {
        let claim = slab.claim().unwrap();
        drop(claim);
    }

    // Slab should still be at full capacity
    let slots: Vec<_> = (0..4).map(|i| slab.alloc(i)).collect();
    for slot in slots {
        // SAFETY: slot was allocated from this slab
        slab.free(slot);
    }
}

#[test]
fn miri_bounded_claim_abandon_capacity_one() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(1) };

    // Claim and abandon
    {
        let claim = slab.claim().unwrap();
        drop(claim);
    }

    // Should be able to allocate again
    let slot = slab.alloc(42);
    assert_eq!(*slot, 42);
    // SAFETY: slot was allocated from this slab
    slab.free(slot);
}

#[test]
fn miri_unbounded_claim_abandon() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { UnboundedSlab::<u64>::with_chunk_capacity(4) };

    // Allocate and free to ensure chunk exists
    let slot = slab.alloc(0);
    slab.free(slot);

    // Claim and abandon
    {
        let claim = slab.claim();
        drop(claim);
    }

    // Should still be able to allocate
    let slot = slab.alloc(99);
    assert_eq!(*slot, 99);
    // SAFETY: slot was allocated from this slab
    slab.free(slot);
}

#[test]
fn miri_unbounded_claim_abandon_full_chunk() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { UnboundedSlab::<u64>::with_chunk_capacity(2) };

    // Fill first chunk
    let s1 = slab.alloc(1);
    let s2 = slab.alloc(2);

    // Claim from second chunk, then abandon
    {
        let claim = slab.claim();
        drop(claim);
    }

    // Should still be able to allocate from that chunk
    let s3 = slab.alloc(3);
    assert_eq!(*s3, 3);

    slab.free(s1);
    slab.free(s2);
    slab.free(s3);
}

// =============================================================================
// Claim::write (L8)
// =============================================================================

#[test]
fn miri_bounded_claim_write() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(4) };

    let claim = slab.claim().unwrap();
    let slot = claim.write(42);
    assert_eq!(*slot, 42);
    // SAFETY: slot was allocated from this slab
    slab.free(slot);
}

#[test]
fn miri_bounded_claim_write_string() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<String>::with_capacity(4) };

    let claim = slab.claim().unwrap();
    let slot = claim.write("hello world".to_string());
    assert_eq!(*slot, "hello world");
    // SAFETY: slot was allocated from this slab
    slab.free(slot);
}

#[test]
fn miri_bounded_claim_write_drop_type() {
    reset_drop_count();

    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<DropTracker>::with_capacity(4) };

    let claim = slab.claim().unwrap();
    let slot = claim.write(DropTracker(1));
    assert_eq!(get_drop_count(), 0);
    // SAFETY: slot was allocated from this slab
    slab.free(slot);
    assert_eq!(get_drop_count(), 1);
}

#[test]
fn miri_unbounded_claim_write() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { UnboundedSlab::<u64>::with_chunk_capacity(4) };

    let claim = slab.claim();
    let slot = claim.write(99);
    assert_eq!(*slot, 99);
    // SAFETY: slot was allocated from this slab
    slab.free(slot);
}

// =============================================================================
// Rc Slab — Memory Safety
// =============================================================================

#[cfg(feature = "rc")]
mod rc_tests {
    use super::*;
    use nexus_slab::rc::bounded::Slab as RcSlab;

    #[test]
    fn miri_rc_alloc_clone_borrow_free() {
        // SAFETY: test slab; single-threaded, all handles freed before drop.
        let slab = unsafe { RcSlab::<u64>::with_capacity(8) };

        let h1 = slab.alloc(42);
        assert_eq!(h1.refcount(), 1);

        let h2 = h1.clone();
        assert_eq!(h1.refcount(), 2);
        assert_eq!(h2.refcount(), 2);

        // Shared borrow via h1
        {
            let guard = h1.borrow();
            assert_eq!(*guard, 42);
        }

        // Exclusive borrow via h2
        {
            let mut guard = h2.borrow_mut();
            *guard = 99;
        }

        // Verify mutation visible through h1
        {
            let guard = h1.borrow();
            assert_eq!(*guard, 99);
        }

        slab.free(h2);
        assert_eq!(h1.refcount(), 1);
        slab.free(h1);
    }

    #[test]
    fn miri_rc_drop_counter() {
        reset_drop_count();

        // SAFETY: test slab; single-threaded, all handles freed before drop.
        let slab = unsafe { RcSlab::<DropTracker>::with_capacity(8) };

        let h1 = slab.alloc(DropTracker(1));
        let h2 = h1.clone();
        let h3 = h1.clone();
        assert_eq!(h1.refcount(), 3);
        assert_eq!(get_drop_count(), 0);

        // Freeing first two clones should NOT drop the value
        slab.free(h3);
        assert_eq!(get_drop_count(), 0);
        slab.free(h2);
        assert_eq!(get_drop_count(), 0);

        // Freeing the last handle drops the value exactly once
        slab.free(h1);
        assert_eq!(get_drop_count(), 1);
    }

    #[test]
    fn miri_rc_sequential_borrows_across_clones() {
        // SAFETY: test slab; single-threaded, all handles freed before drop.
        let slab = unsafe { RcSlab::<String>::with_capacity(8) };

        let h1 = slab.alloc(String::from("hello"));
        let h2 = h1.clone();
        let h3 = h1.clone();

        // Sequential shared borrows through different handles
        {
            let g = h1.borrow();
            assert_eq!(&*g, "hello");
        }
        {
            let g = h2.borrow();
            assert_eq!(&*g, "hello");
        }

        // Exclusive borrow through h3
        {
            let mut g = h3.borrow_mut();
            g.push_str(" world");
        }

        // Verify mutation visible through all handles
        {
            let g = h1.borrow();
            assert_eq!(&*g, "hello world");
        }
        {
            let g = h2.borrow();
            assert_eq!(&*g, "hello world");
        }

        slab.free(h3);
        slab.free(h2);
        slab.free(h1);
    }
}

// =============================================================================
// Byte Slab — Memory Safety
// =============================================================================

mod byte_tests {
    use super::*;
    use nexus_slab::byte::bounded::Slab as ByteBoundedSlab;
    use nexus_slab::byte::unbounded::Slab as ByteUnboundedSlab;

    #[test]
    fn miri_byte_bounded_alloc_write_free() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab: ByteBoundedSlab<64> = unsafe { ByteBoundedSlab::with_capacity(8) };

        let ptr = slab.alloc(42u64);
        assert_eq!(*ptr, 42);
        slab.free(ptr);
    }

    #[test]
    fn miri_byte_bounded_alloc_write_different_types() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab: ByteBoundedSlab<64> = unsafe { ByteBoundedSlab::with_capacity(8) };

        // Write a u64 (8 bytes)
        let ptr = slab.alloc(0xDEAD_BEEF_u64);
        assert_eq!(*ptr, 0xDEAD_BEEF_u64);
        slab.free(ptr);

        // Reuse the same slot with a different type: [u8; 32]
        let ptr = slab.alloc([0xABu8; 32]);
        assert_eq!(ptr[0], 0xAB);
        assert_eq!(ptr[31], 0xAB);
        slab.free(ptr);
    }

    #[test]
    fn miri_byte_bounded_abandon_claim() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab: ByteBoundedSlab<64> = unsafe { ByteBoundedSlab::with_capacity(1) };

        // Claim and drop without writing — slot returns to freelist
        {
            let claim = slab.claim();
            drop(claim);
        }

        // Should be able to alloc again
        let ptr = slab.alloc(99u64);
        assert_eq!(*ptr, 99);
        slab.free(ptr);
    }

    #[test]
    fn miri_byte_unbounded_alloc_write_free() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab: ByteUnboundedSlab<64> = unsafe { ByteUnboundedSlab::with_chunk_capacity(4) };

        let ptr = slab.alloc(42u64);
        assert_eq!(*ptr, 42);
        slab.free(ptr);
    }

    #[test]
    fn miri_byte_unbounded_multiple_chunks() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab: ByteUnboundedSlab<64> = unsafe { ByteUnboundedSlab::with_chunk_capacity(2) };

        // Alloc enough to span multiple chunks
        let mut ptrs = Vec::new();
        for i in 0..10u64 {
            ptrs.push(slab.alloc(i));
        }

        // Verify values across chunks
        for (i, ptr) in ptrs.iter().enumerate() {
            assert_eq!(**ptr, i as u64);
        }

        // Free all
        for ptr in ptrs {
            slab.free(ptr);
        }
    }

    #[test]
    fn miri_byte_slab_drop_tracker() {
        reset_drop_count();

        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab: ByteBoundedSlab<64> = unsafe { ByteBoundedSlab::with_capacity(4) };

        let ptr = slab.alloc(DropTracker(1));
        assert_eq!(get_drop_count(), 0);

        // Typed free — should drop the value exactly once
        slab.free(ptr);
        assert_eq!(get_drop_count(), 1);
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn miri_byte_claim_write_aligned_type() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab: ByteBoundedSlab<64> = unsafe { ByteBoundedSlab::with_capacity(4) };

        // f64 has alignment 8 — must be respected
        let claim = slab.claim();
        let ptr = claim.write(1.23456_f64);
        assert_eq!(*ptr, 1.23456_f64);
        slab.free(ptr);
    }
}

// =============================================================================
// Provenance: stored pointer → claim → write through returned pointer
//
// The async-rt slab integration stores a raw pointer to the slab in TLS,
// casts back to &Slab, calls claim_ptr(), and writes through the returned
// pointer. This exercises the exact provenance chain that stacked borrows
// has trouble with (Cell<*mut> read through &self retag). These tests
// verify the pattern is sound under tree borrows and catches regressions
// in slots_ptr / claim_ptr provenance.
// =============================================================================

#[test]
fn miri_bounded_alloc_through_stored_pointer() {
    // Simulate the async-rt pattern: store raw pointer, cast to &Slab,
    // alloc (claim + write), read, free. Exercises the full provenance
    // chain through a stored pointer round-trip.
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(4) };
    let slab_ptr: *const BoundedSlab<u64> = &raw const slab;

    // SAFETY: slab_ptr was obtained from &slab on the current stack; still valid.
    let slab_ref = unsafe { &*slab_ptr };
    let slot = slab_ref.alloc(42u64);
    assert_eq!(*slot, 42);
    slab_ref.free(slot);
}

#[test]
fn miri_bounded_alloc_cycle_through_stored_pointer() {
    // Multiple alloc/free cycles through stored pointer — exercises freelist
    // pointer provenance across reuse.
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(2) };
    let slab_ptr: *const BoundedSlab<u64> = &raw const slab;

    for i in 0..10u64 {
        // SAFETY: slab_ptr was obtained from &slab on the current stack; still valid.
        let slab_ref = unsafe { &*slab_ptr };
        let slot = slab_ref.alloc(i);
        assert_eq!(*slot, i);
        slab_ref.free(slot);
    }
}

#[test]
fn miri_bounded_two_slots_through_stored_pointer() {
    // Claim two slots via alloc, free in reverse order.
    // Exercises freelist pointer provenance when multiple slots are live.
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<String>::with_capacity(4) };
    let slab_ptr: *const BoundedSlab<String> = &raw const slab;

    // SAFETY: slab_ptr was obtained from &slab on the current stack; still valid.
    let slab_ref = unsafe { &*slab_ptr };
    let slot1 = slab_ref.alloc(String::from("first"));
    let slot2 = slab_ref.alloc(String::from("second"));

    assert_eq!(&*slot1, "first");
    assert_eq!(&*slot2, "second");

    slab_ref.free(slot2);
    slab_ref.free(slot1);
}

#[test]
fn miri_bounded_claim_write_through_stored_pointer() {
    // Two-phase alloc (claim + write) through stored pointer.
    // Exercises claim_ptr → write_value provenance chain.
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(4) };
    let slab_ptr: *const BoundedSlab<u64> = &raw const slab;

    // SAFETY: slab_ptr was obtained from &slab on the current stack; still valid.
    let slab_ref = unsafe { &*slab_ptr };
    let claim = slab_ref.claim().unwrap();
    let slot = claim.write(99u64);
    assert_eq!(*slot, 99);
    slab_ref.free(slot);
}

#[test]
fn miri_unbounded_claim_write_through_stored_pointer() {
    // Same pattern for unbounded slab — exercises chunk-based allocation.
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { UnboundedSlab::<u64>::with_chunk_capacity(4) };
    let slab_ptr: *const UnboundedSlab<u64> = &raw const slab;

    for i in 0..20u64 {
        // SAFETY: slab_ptr was obtained from &slab on the current stack; still valid.
        let slab_ref = unsafe { &*slab_ptr };
        let slot = slab_ref.alloc(i);
        assert_eq!(*slot, i);
        slab_ref.free(slot);
    }
}

#[test]
fn miri_unbounded_stored_pointer_cross_chunk() {
    // Allocate enough to trigger chunk growth, all through stored pointer.
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { UnboundedSlab::<u64>::with_chunk_capacity(2) };
    let slab_ptr: *const UnboundedSlab<u64> = &raw const slab;

    // SAFETY: slab_ptr was obtained from &slab on the current stack; still valid.
    let slab_ref = unsafe { &*slab_ptr };

    // 6 allocs with capacity 2 per chunk = 3 chunks
    let s1 = slab_ref.alloc(1);
    let s2 = slab_ref.alloc(2);
    let s3 = slab_ref.alloc(3); // triggers chunk growth
    let s4 = slab_ref.alloc(4);
    let s5 = slab_ref.alloc(5); // triggers chunk growth
    let s6 = slab_ref.alloc(6);

    assert_eq!(*s1, 1);
    assert_eq!(*s6, 6);

    slab_ref.free(s1);
    slab_ref.free(s2);
    slab_ref.free(s3);
    slab_ref.free(s4);
    slab_ref.free(s5);
    slab_ref.free(s6);
}
