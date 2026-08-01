//! Fixed-capacity slab allocator.
//!
//! This module provides a bounded (fixed-capacity) slab allocator.
//!
//! # Example
//!
//! ```
//! use nexus_slab::bounded::Slab;
//!
//! // SAFETY: caller guarantees slab contract (see struct docs)
//! let slab = unsafe { Slab::with_capacity(1024) };
//! let slot = slab.alloc(42u64);
//! assert_eq!(*slot, 42);
//! slab.free(slot);
//! ```

use core::cell::Cell;
use core::fmt;
use core::mem;
use core::ptr;

use alloc::vec::Vec;

use crate::shared::{Full, Slot, SlotCell};

// =============================================================================
// Claim
// =============================================================================

/// A claimed slot that has not yet been written to.
///
/// Created by [`Slab::claim()`]. Must be consumed via [`write()`](Self::write)
/// to complete the allocation. If dropped without calling `write()`, the slot
/// is returned to the freelist.
///
/// The `write()` method is `#[inline]`, enabling the compiler to potentially
/// optimize the value write as a placement new (constructing directly into
/// the slot memory).
pub struct Claim<'a, T> {
    slot_ptr: *mut SlotCell<T>,
    slab: &'a Slab<T>,
}

impl<T> Claim<'_, T> {
    /// Writes the value to the claimed slot and returns the [`Slot`] handle.
    ///
    /// This consumes the claim. The value is written directly to the slot's
    /// memory, which may enable placement new optimization.
    #[inline]
    pub fn write(self, value: T) -> Slot<T> {
        let slot_ptr = self.slot_ptr;
        // SAFETY: We own this slot from claim(), it's valid and vacant
        unsafe {
            (*slot_ptr).write_value(value);
        }
        // Don't run Drop - we're completing the allocation
        mem::forget(self);
        // SAFETY: slot_ptr is valid and now occupied
        unsafe { Slot::from_ptr(slot_ptr) }
    }

    /// Extract the raw slot pointer, consuming the claim without writing.
    ///
    /// Transfers ownership to the caller — the slot will NOT be returned
    /// to the freelist on drop. The caller must either write a value and
    /// eventually free it, or return the slot via `free_ptr()`.
    #[inline]
    pub(crate) fn into_ptr(self) -> *mut SlotCell<T> {
        let ptr = self.slot_ptr;
        mem::forget(self);
        ptr
    }
}

impl<T> fmt::Debug for Claim<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Claim")
            .field("slot_ptr", &self.slot_ptr)
            .finish()
    }
}

impl<T> Drop for Claim<'_, T> {
    fn drop(&mut self) {
        // Abandoned claim - return slot to freelist
        let free_head = self.slab.free_head.get();
        // SAFETY: slot_ptr is valid and still vacant (never written to)
        unsafe {
            (*self.slot_ptr).set_next_free(free_head);
        }
        self.slab.free_head.set(self.slot_ptr);
    }
}

// =============================================================================
// Slab
// =============================================================================

/// Fixed-capacity slab allocator for manual memory management.
///
/// Uses pointer-based freelist for O(1) allocation. ~20-24 cycle operations.
///
/// # Safety Contract
///
/// Construction is `unsafe` because it opts you into manual memory
/// management. By creating a slab, you accept these invariants:
///
/// - **Free from the correct slab.** Passing a [`Slot`] to a different
///   slab's `free()` is undefined behavior — it corrupts the freelist.
///   In debug builds, this is caught by `debug_assert!`.
/// - **Free everything you allocate.** Dropping the slab does NOT drop
///   values in occupied slots. Unfreed slots leak silently.
/// - **Single-threaded.** The slab is `!Send` and `!Sync`.
///
/// ## Why `free()` is safe
///
/// The safety contract is accepted once, at construction. After that:
/// - [`Slot`] is move-only (no `Copy`, no `Clone`) — double-free is
///   prevented by the type system.
/// - `free()` consumes the `Slot` — the handle cannot be used after.
/// - Cross-slab misuse is the only remaining hazard, and it was
///   accepted as the caller's responsibility at construction time.
pub struct Slab<T> {
    /// Slot storage. Wrapped in UnsafeCell for interior mutability.
    slots: core::cell::UnsafeCell<Vec<SlotCell<T>>>,
    /// Fixed capacity, set at construction.
    capacity: usize,
    /// Head of freelist — raw pointer for fast allocation.
    /// NULL when the slab is full.
    pub(crate) free_head: Cell<*mut SlotCell<T>>,
}

impl<T> Slab<T> {
    /// Creates a new slab with the given capacity.
    ///
    /// # Safety
    ///
    /// See [struct-level safety contract](Self).
    ///
    /// # Panics
    ///
    /// Panics if capacity is zero.
    #[inline]
    pub unsafe fn with_capacity(capacity: usize) -> Self {
        assert!(capacity > 0, "capacity must be non-zero");

        let mut slots = Vec::with_capacity(capacity);
        for _ in 0..capacity {
            slots.push(SlotCell::vacant(ptr::null_mut()));
        }

        // Wrap in UnsafeCell BEFORE wiring the freelist so all pointers
        // are derived with write provenance from the UnsafeCell. Deriving
        // pointers from the owned Vec and then moving into UnsafeCell gives
        // them stale (read-only) provenance under stacked borrows.
        let slots = core::cell::UnsafeCell::new(slots);
        // SAFETY: UnsafeCell::get provides write-provenance pointer to the Vec.
        let base = unsafe { (*slots.get()).as_mut_ptr() };

        // Wire up the freelist: each slot's next_free points to the next slot
        for i in 0..(capacity - 1) {
            let next_ptr = base.wrapping_add(i + 1);
            // SAFETY: Slot is vacant, wiring up the freelist during init.
            // base is derived from UnsafeCell with write provenance.
            unsafe { (*base.add(i)).set_next_free(next_ptr) };
        }
        // Last slot points to NULL (end of freelist) — already null from vacant()

        Self {
            slots,
            capacity,
            free_head: Cell::new(base),
        }
    }

    /// Returns the capacity.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// Returns the base pointer to the slots array.
    #[inline]
    pub(crate) fn slots_ptr(&self) -> *mut SlotCell<T> {
        // SAFETY: Derive from *mut Vec (via UnsafeCell::get) to preserve write
        // provenance. Creating &Vec first would give read-only provenance.
        unsafe { (*self.slots.get()).as_mut_ptr() }
    }

    /// Returns `true` if `ptr` falls within this slab's slot array.
    ///
    /// O(1) range check. Used in `debug_assert!` to validate provenance.
    #[doc(hidden)]
    #[inline]
    pub fn contains_ptr(&self, ptr: *const ()) -> bool {
        let base = self.slots_ptr() as usize;
        let end = base + self.capacity * core::mem::size_of::<SlotCell<T>>();
        let addr = ptr as usize;
        addr >= base && addr < end
    }

    // =========================================================================
    // Allocation API
    // =========================================================================

    /// Claims a slot from the freelist without writing a value.
    ///
    /// Returns `None` if the slab is full. The returned [`Claim`] must be
    /// consumed via [`Claim::write()`] to complete the allocation.
    ///
    /// This two-phase allocation enables placement new optimization: the
    /// value can be constructed directly into the slot memory.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_slab::bounded::Slab;
    ///
    /// // SAFETY: caller guarantees slab contract (see struct docs)
    /// let slab = unsafe { Slab::with_capacity(10) };
    /// if let Some(claim) = slab.claim() {
    ///     let slot = claim.write(42u64);
    ///     assert_eq!(*slot, 42);
    ///     slab.free(slot);
    /// }
    /// ```
    #[inline]
    pub fn claim(&self) -> Option<Claim<'_, T>> {
        self.claim_ptr().map(|slot_ptr| Claim {
            slot_ptr,
            slab: self,
        })
    }

    /// Claims a slot from the freelist, returning the raw pointer.
    ///
    /// Returns `None` if the slab is full. This is a low-level API for
    /// macro-generated code that needs to escape TLS closures.
    ///
    /// # Safety Contract
    ///
    /// The caller MUST either:
    /// - Write a value to the slot and use it as an allocated slot, OR
    /// - Return the pointer to the freelist via `free_ptr()` if abandoning
    #[doc(hidden)]
    #[inline]
    pub(crate) fn claim_ptr(&self) -> Option<*mut SlotCell<T>> {
        let slot_ptr = self.free_head.get();

        if slot_ptr.is_null() {
            return None;
        }

        // SAFETY: slot_ptr came from the freelist within this slab.
        // The slot is vacant, so next_free is the active union field.
        let next_free = unsafe { (*slot_ptr).get_next_free() };

        // Update freelist head
        self.free_head.set(next_free);

        Some(slot_ptr)
    }

    /// Allocates a slot and writes the value.
    ///
    /// # Panics
    ///
    /// Panics if the slab is full.
    #[inline]
    pub fn alloc(&self, value: T) -> Slot<T> {
        self.claim().expect("slab full").write(value)
    }

    /// Tries to allocate a slot and write the value.
    ///
    /// Returns `Err(Full(value))` if the slab is at capacity.
    #[inline]
    pub fn try_alloc(&self, value: T) -> Result<Slot<T>, Full<T>> {
        match self.claim() {
            Some(claim) => Ok(claim.write(value)),
            None => Err(Full(value)),
        }
    }

    /// Frees a slot, dropping the value and returning storage to the freelist.
    ///
    /// Consumes the handle — the slot cannot be used after this call.
    /// The caller's safety obligation (free from the correct slab) was
    /// accepted at construction time.
    #[inline]
    // Consumes the slot handle by design — the slot cannot be used after free.
    #[allow(clippy::needless_pass_by_value)]
    pub fn free(&self, slot: Slot<T>) {
        let slot_ptr = slot.into_raw();
        debug_assert!(
            self.contains_ptr(slot_ptr as *const ()),
            "slot was not allocated from this slab"
        );
        // SAFETY: Caller guarantees slot is valid and occupied
        unsafe {
            (*slot_ptr).drop_value_in_place();
            self.free_ptr(slot_ptr);
        }
    }

    /// Frees a slot and returns the value without dropping it.
    ///
    /// Consumes the handle — the slot cannot be used after this call.
    #[inline]
    // Consumes the slot handle by design — the slot cannot be used after this call.
    #[allow(clippy::needless_pass_by_value)]
    pub fn take(&self, slot: Slot<T>) -> T {
        let slot_ptr = slot.into_raw();
        debug_assert!(
            self.contains_ptr(slot_ptr as *const ()),
            "slot was not allocated from this slab"
        );
        // SAFETY: Caller guarantees slot is valid and occupied
        unsafe {
            let value = (*slot_ptr).read_value();
            self.free_ptr(slot_ptr);
            value
        }
    }

    /// Returns a slot to the freelist by pointer.
    ///
    /// Does NOT drop the value — caller must drop before calling.
    ///
    /// # Safety
    ///
    /// - `slot_ptr` must point to a slot within this slab
    /// - Value must already be dropped or moved out
    #[doc(hidden)]
    #[inline]
    pub(crate) unsafe fn free_ptr(&self, slot_ptr: *mut SlotCell<T>) {
        debug_assert!(
            self.contains_ptr(slot_ptr as *const ()),
            "slot was not allocated from this slab"
        );
        let free_head = self.free_head.get();
        // SAFETY: Caller guarantees slot_ptr is valid, transitioning to vacant
        unsafe {
            (*slot_ptr).set_next_free(free_head);
        }
        self.free_head.set(slot_ptr);
    }
}

impl<T> fmt::Debug for Slab<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Slab")
            .field("capacity", &self.capacity)
            .finish()
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::borrow::{Borrow, BorrowMut};

    #[test]
    fn slab_basic() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab = unsafe { Slab::<u64>::with_capacity(100) };
        assert_eq!(slab.capacity(), 100);

        let slot = slab.alloc(42);
        assert_eq!(*slot, 42);
        slab.free(slot);
    }

    #[test]
    fn slab_full() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab = unsafe { Slab::<u64>::with_capacity(2) };
        let s1 = slab.alloc(1);
        let s2 = slab.alloc(2);

        let result = slab.try_alloc(3);
        assert!(result.is_err());
        let recovered = result.unwrap_err().into_inner();
        assert_eq!(recovered, 3);

        slab.free(s1);
        slab.free(s2);
    }

    #[test]
    fn slot_deref_mut() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab = unsafe { Slab::<String>::with_capacity(10) };
        let mut slot = slab.alloc("hello".to_string());
        slot.push_str(" world");
        assert_eq!(&*slot, "hello world");
        slab.free(slot);
    }

    #[test]
    fn slot_dealloc_take() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab = unsafe { Slab::<String>::with_capacity(10) };
        let slot = slab.alloc("hello".to_string());

        let value = slab.take(slot);
        assert_eq!(value, "hello");
    }

    #[test]
    fn slot_size() {
        assert_eq!(std::mem::size_of::<Slot<u64>>(), 8);
    }

    #[test]
    fn slab_debug() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab = unsafe { Slab::<u64>::with_capacity(10) };
        let s = slab.alloc(42);
        let debug = format!("{:?}", slab);
        assert!(debug.contains("Slab"));
        assert!(debug.contains("capacity"));
        slab.free(s);
    }

    #[test]
    fn borrow_traits() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab = unsafe { Slab::<u64>::with_capacity(10) };
        let mut slot = slab.alloc(42);

        let borrowed: &u64 = slot.borrow();
        assert_eq!(*borrowed, 42);

        let borrowed_mut: &mut u64 = slot.borrow_mut();
        *borrowed_mut = 100;
        assert_eq!(*slot, 100);

        slab.free(slot);
    }

    #[cfg(debug_assertions)]
    #[test]
    fn slot_debug_drop_panics() {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            // SAFETY: test slab; slot intentionally not freed (tests debug drop panic).
            let slab = unsafe { Slab::<u64>::with_capacity(10) };
            let _slot = slab.alloc(42u64);
            // slot drops here without being freed
        }));
        assert!(result.is_err(), "Slot should panic on drop in debug mode");
    }

    #[test]
    fn capacity_one() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab = unsafe { Slab::<u64>::with_capacity(1) };

        assert_eq!(slab.capacity(), 1);

        let slot = slab.alloc(42);
        assert!(slab.try_alloc(100).is_err());

        slab.free(slot);

        let slot2 = slab.alloc(100);
        assert_eq!(*slot2, 100);
        slab.free(slot2);
    }
}
