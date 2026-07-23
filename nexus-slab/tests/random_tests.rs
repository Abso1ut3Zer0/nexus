//! Randomized stress tests for slab allocator invariants.
//!
//! These tests verify invariants hold under randomized inputs using
//! deterministic RNG seeds for reproducibility:
//! - Freelist maintains integrity under arbitrary insert/remove sequences
//! - Values are never corrupted
//! - Capacity bounds are respected
//! - Drop counting matches expectations

use nexus_slab::Slot;
use nexus_slab::bounded::Slab as BoundedSlab;
use nexus_slab::unbounded::Slab as UnboundedSlab;
use proptest::prelude::*;
use std::collections::HashSet;

// =============================================================================
// Bounded Slab Properties
// =============================================================================

/// Test that values are never corrupted
#[test]
fn bounded_value_integrity_random() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(50) };

    let mut rng = proptest::test_runner::TestRng::deterministic_rng(
        proptest::test_runner::RngAlgorithm::ChaCha,
    );

    // Track expected values
    let mut slots: Vec<(Slot<u64>, u64)> = Vec::new();

    for _ in 0..500 {
        let action: u8 = rng.random_range(0..10);

        match action {
            0..=5 => {
                let value: u64 = rng.random();
                if let Ok(slot) = slab.try_alloc(value) {
                    slots.push((slot, value));
                }
            }
            6..=7 => {
                if let Some((slot, _)) = slots.pop() {
                    // SAFETY: slot was allocated from this slab
                    slab.free(slot);
                }
            }
            8 => {
                if !slots.is_empty() {
                    let idx = rng.random_range(0..slots.len());
                    let (slot, _) = slots.swap_remove(idx);
                    // SAFETY: slot was allocated from this slab
                    slab.free(slot);
                }
            }
            9 => {
                if !slots.is_empty() {
                    let idx = rng.random_range(0..slots.len());
                    let new_value: u64 = rng.random();
                    *slots[idx].0 = new_value;
                    slots[idx].1 = new_value;
                }
            }
            _ => unreachable!(),
        }

        // Invariant: all values match expected
        for (slot, expected) in &slots {
            assert_eq!(**slot, *expected);
        }
    }

    // Clean up remaining slots
    for (slot, _) in slots {
        // SAFETY: slot was allocated from this slab
        slab.free(slot);
    }
}

/// Test capacity is never exceeded (separate tests for each capacity)
#[test]
fn bounded_capacity_never_exceeded_1() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(1) };

    let mut slots = Vec::new();
    for i in 0..200 {
        if let Ok(slot) = slab.try_alloc(i) {
            slots.push(slot);
        }
    }
    assert!(slots.len() <= 1);

    // Clean up
    for slot in slots {
        slab.free(slot);
    }
}

#[test]
fn bounded_capacity_never_exceeded_10() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(10) };

    let mut slots = Vec::new();
    for i in 0..200 {
        if let Ok(slot) = slab.try_alloc(i) {
            slots.push(slot);
        }
    }
    assert!(slots.len() <= 10);

    // Clean up
    for slot in slots {
        slab.free(slot);
    }
}

#[test]
fn bounded_capacity_never_exceeded_50() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(50) };

    let mut slots = Vec::new();
    for i in 0..200 {
        if let Ok(slot) = slab.try_alloc(i) {
            slots.push(slot);
        }
    }
    assert!(slots.len() <= 50);

    // Clean up
    for slot in slots {
        slab.free(slot);
    }
}

/// Test fill/drain cycles maintain integrity
#[test]
fn bounded_fill_drain_integrity() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(20) };

    for cycle in 0..10 {
        // Fill
        let slots: Vec<_> = (0..20)
            .map(|i| slab.alloc((cycle * 20 + i) as u64))
            .collect();

        // Verify values
        for (i, slot) in slots.iter().enumerate() {
            assert_eq!(**slot, (cycle * 20 + i) as u64);
        }

        // Drain — explicitly dealloc all slots
        for slot in slots {
            // SAFETY: slot was allocated from this slab
            slab.free(slot);
        }
    }
}

// =============================================================================
// Unbounded Slab Properties
// =============================================================================

#[test]
fn unbounded_value_integrity_random() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { UnboundedSlab::<u64>::with_chunk_capacity(8) };

    let mut rng = proptest::test_runner::TestRng::deterministic_rng(
        proptest::test_runner::RngAlgorithm::ChaCha,
    );

    let mut slots: Vec<(Slot<u64>, u64)> = Vec::new();

    for _ in 0..500 {
        let action: u8 = rng.random_range(0..10);

        match action {
            0..=5 => {
                let value: u64 = rng.random();
                slots.push((slab.alloc(value), value));
            }
            6..=7 => {
                if let Some((slot, _)) = slots.pop() {
                    // SAFETY: slot was allocated from this slab
                    slab.free(slot);
                }
            }
            8 => {
                if !slots.is_empty() {
                    let idx = rng.random_range(0..slots.len());
                    let (slot, _) = slots.swap_remove(idx);
                    // SAFETY: slot was allocated from this slab
                    slab.free(slot);
                }
            }
            9 => {
                if !slots.is_empty() {
                    let idx = rng.random_range(0..slots.len());
                    let new_value: u64 = rng.random();
                    *slots[idx].0 = new_value;
                    slots[idx].1 = new_value;
                }
            }
            _ => unreachable!(),
        }

        for (slot, expected) in &slots {
            assert_eq!(**slot, *expected);
        }
    }

    // Clean up remaining slots
    for (slot, _) in slots {
        slab.free(slot);
    }
}

#[test]
fn unbounded_growth_maintains_integrity() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { UnboundedSlab::<u64>::with_chunk_capacity(8) };

    // Test with increasing counts in a single slab
    for count in [10, 50, 100, 200] {
        let slots: Vec<_> = (0..count).map(|i| slab.alloc(i as u64)).collect();

        for (i, slot) in slots.iter().enumerate() {
            assert_eq!(**slot, i as u64);
        }

        assert!(slab.capacity() >= count);

        // Clean up for next iteration
        for slot in slots {
            // SAFETY: slot was allocated from this slab
            slab.free(slot);
        }
    }
}

// =============================================================================
// Freelist Properties
// =============================================================================

#[test]
fn freelist_no_duplicates() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(20) };

    let mut rng = proptest::test_runner::TestRng::deterministic_rng(
        proptest::test_runner::RngAlgorithm::ChaCha,
    );

    let mut slots: Vec<Slot<u64>> = Vec::new();
    let mut seen_ptrs = HashSet::new();

    for _ in 0..200 {
        let should_insert = rng.random_bool(0.6) || slots.is_empty();

        if should_insert {
            if let Ok(slot) = slab.try_alloc(0) {
                let ptr = slot.as_ptr();
                // Pointer should not be a duplicate of any currently held slot
                for existing in &slots {
                    assert_ne!(ptr, existing.as_ptr(), "Duplicate slot returned!");
                }
                slots.push(slot);
                seen_ptrs.insert(ptr as usize);
            }
        } else if !slots.is_empty() {
            let idx = rng.random_range(0..slots.len());
            let slot = slots.swap_remove(idx);
            // SAFETY: slot was allocated from this slab
            slab.free(slot);
        }
    }

    // Verify we saw some distinct pointers
    assert!(!seen_ptrs.is_empty());

    // Clean up remaining slots
    for slot in slots {
        slab.free(slot);
    }
}

#[test]
fn freelist_reuses_freed_slots() {
    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<u64>::with_capacity(10) };

    let mut slots: Vec<Slot<u64>> = Vec::new();
    let mut freed_ptrs: Vec<*mut nexus_slab::SlotCell<u64>> = Vec::new();

    for i in 0..100 {
        let should_insert = i % 3 != 2 || slots.is_empty();

        if should_insert {
            if let Ok(slot) = slab.try_alloc(0) {
                let ptr = slot.as_ptr();
                // If we had freed slots, this should reuse one (LIFO)
                if let Some(expected) = freed_ptrs.pop() {
                    assert_eq!(ptr, expected, "Expected LIFO reuse");
                }
                slots.push(slot);
            }
        } else if !slots.is_empty() {
            let slot = slots.pop().unwrap();
            freed_ptrs.push(slot.as_ptr());
            // SAFETY: slot was allocated from this slab
            slab.free(slot);
        }
    }

    // Clean up remaining slots
    for slot in slots {
        slab.free(slot);
    }
}

// =============================================================================
// Drop Counting
// =============================================================================

use std::cell::Cell;

thread_local! {
    static DROP_COUNTER: Cell<usize> = const { Cell::new(0) };
}

pub struct Counted;

impl Drop for Counted {
    fn drop(&mut self) {
        DROP_COUNTER.with(|c| c.set(c.get() + 1));
    }
}

fn reset_counter() {
    DROP_COUNTER.with(|c| c.set(0));
}

fn get_counter() -> usize {
    DROP_COUNTER.with(Cell::get)
}

#[test]
fn drop_count_matches_inserts() {
    reset_counter();

    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<Counted>::with_capacity(100) };

    let count = 50;
    {
        let slots: Vec<_> = (0..count).map(|_| slab.alloc(Counted)).collect();
        // Free all slots - this drops the values
        for slot in slots {
            // SAFETY: slot was allocated from this slab
            slab.free(slot);
        }
    }

    assert_eq!(get_counter(), count);
}

#[test]
fn into_inner_prevents_drop() {
    reset_counter();

    // SAFETY: test slab; single-threaded, all slots freed before drop.
    let slab = unsafe { BoundedSlab::<Counted>::with_capacity(100) };

    let count = 20;
    let slots: Vec<_> = (0..count).map(|_| slab.alloc(Counted)).collect();

    // Take half via free_take (into_inner equivalent)
    let half = count / 2;
    let mut values = Vec::new();
    let mut remaining_slots = Vec::new();

    for (i, slot) in slots.into_iter().enumerate() {
        if i < half {
            // SAFETY: slot was allocated from this slab
            let value = slab.take(slot);
            values.push(value);
        } else {
            remaining_slots.push(slot);
        }
    }

    // Remaining slots not dropped yet
    assert_eq!(get_counter(), 0);

    // Free the rest
    for slot in remaining_slots {
        // SAFETY: slot was allocated from this slab
        slab.free(slot);
    }

    // Half dropped via free, half still in values vec
    assert_eq!(get_counter(), count - half);

    // Now drop the values
    drop(values);
    assert_eq!(get_counter(), count);
}
