//! Growable slab allocator.
//!
//! This module provides an unbounded (growable) slab allocator.
//! Growth happens by adding independent chunks — no copying.
//!
//! # Example
//!
//! ```
//! use nexus_slab::unbounded::Slab;
//!
//! // SAFETY: caller guarantees slab contract (see struct docs)
//! let slab = unsafe { Slab::with_chunk_capacity(4096) };
//! let slot = slab.alloc(42u64);
//! assert_eq!(*slot, 42);
//! slab.free(slot);
//! ```

use core::cell::Cell;
use core::fmt;
use core::mem;

use alloc::boxed::Box;
use alloc::vec::Vec;

use crate::bounded::Slab as BoundedSlab;
use crate::shared::{Slot, SlotCell};

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
    chunk_idx: usize,
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

    /// Extract the raw slot pointer and chunk index, consuming the claim.
    ///
    /// Transfers ownership to the caller — the slot will NOT be returned
    /// to the freelist on drop. The caller must either write a value and
    /// eventually free it, or return the slot via `free_ptr()`.
    #[inline]
    pub(crate) fn into_ptr(self) -> (*mut SlotCell<T>, usize) {
        let ptr = self.slot_ptr;
        let chunk_idx = self.chunk_idx;
        mem::forget(self);
        (ptr, chunk_idx)
    }
}

impl<T> fmt::Debug for Claim<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Claim")
            .field("slot_ptr", &self.slot_ptr)
            .field("chunk_idx", &self.chunk_idx)
            .finish()
    }
}

impl<T> Drop for Claim<'_, T> {
    fn drop(&mut self) {
        // Abandoned claim — return slot to the correct chunk's freelist
        let chunk = self.slab.chunk(self.chunk_idx);
        let chunk_slab = &*chunk.inner;

        let free_head = chunk_slab.free_head.get();
        let was_full = free_head.is_null();

        // SAFETY: slot_ptr is valid and vacant (claim was never written to).
        unsafe {
            (*self.slot_ptr).set_next_free(free_head);
        }
        chunk_slab.free_head.set(self.slot_ptr);

        // If chunk was full, add it back to the available-space list
        if was_full {
            chunk.next_with_space.set(self.slab.head_with_space.get());
            self.slab.head_with_space.set(self.chunk_idx);
        }
    }
}

// =============================================================================
// Constants
// =============================================================================

/// Sentinel for chunk freelist
const CHUNK_NONE: usize = usize::MAX;

// =============================================================================
// ChunkEntry
// =============================================================================

/// Internal wrapper for a chunk in the growable slab.
struct ChunkEntry<T> {
    inner: Box<BoundedSlab<T>>,
    next_with_space: Cell<usize>,
}

// =============================================================================
// Slab
// =============================================================================

/// Growable slab allocator.
///
/// Uses independent chunks for growth — no copying when the slab grows.
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
    chunks: core::cell::UnsafeCell<Vec<ChunkEntry<T>>>,
    chunk_capacity: Cell<usize>,
    head_with_space: Cell<usize>,
}

impl<T> Slab<T> {
    /// Creates a new slab with the given chunk capacity.
    ///
    /// Chunks are allocated on-demand when slots are requested.
    ///
    /// # Safety
    ///
    /// See [struct-level safety contract](Self).
    ///
    /// # Panics
    ///
    /// Panics if `chunk_capacity` is zero.
    #[inline]
    pub unsafe fn with_chunk_capacity(chunk_capacity: usize) -> Self {
        // SAFETY: caller upholds the slab contract
        unsafe { Builder::new().chunk_capacity(chunk_capacity).build() }
    }

    /// Returns the total capacity across all chunks.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.chunks().len() * self.chunk_capacity.get()
    }

    /// Returns the chunk capacity.
    #[inline]
    pub fn chunk_capacity(&self) -> usize {
        self.chunk_capacity.get()
    }

    #[inline]
    fn chunks(&self) -> &Vec<ChunkEntry<T>> {
        // SAFETY: !Sync prevents shared access across threads.
        // Only one thread can hold &self at a time.
        unsafe { &*self.chunks.get() }
    }

    #[inline]
    #[allow(clippy::mut_from_ref)]
    fn chunks_mut(&self) -> &mut Vec<ChunkEntry<T>> {
        // SAFETY: !Sync prevents shared access across threads.
        // Only one thread can hold &self at a time.
        unsafe { &mut *self.chunks.get() }
    }

    fn chunk(&self, chunk_idx: usize) -> &ChunkEntry<T> {
        let chunks = self.chunks();
        debug_assert!(chunk_idx < chunks.len());
        // SAFETY: chunk_idx is validated by debug_assert above. In release,
        // callers guarantee validity (from claim_ptr or freelist bookkeeping).
        unsafe { chunks.get_unchecked(chunk_idx) }
    }

    /// Returns the number of allocated chunks.
    #[inline]
    pub fn chunk_count(&self) -> usize {
        self.chunks().len()
    }

    /// Returns `true` if `ptr` falls within any chunk's slot array.
    ///
    /// O(chunks) scan. Typically 1–5 chunks. Used in `debug_assert!`
    /// to validate provenance.
    #[doc(hidden)]
    pub fn contains_ptr(&self, ptr: *const ()) -> bool {
        let chunks = self.chunks();
        for chunk in chunks {
            let chunk_slab = &*chunk.inner;
            if chunk_slab.contains_ptr(ptr) {
                return true;
            }
        }
        false
    }

    /// Ensures at least `count` chunks are allocated.
    ///
    /// No-op if the slab already has `count` or more chunks. Only allocates
    /// the difference.
    pub fn reserve_chunks(&self, count: usize) {
        let current = self.chunks().len();
        for _ in current..count {
            self.grow();
        }
    }

    /// Grows the slab by adding a single new chunk.
    fn grow(&self) {
        let chunks = self.chunks_mut();
        let chunk_idx = chunks.len();
        // SAFETY: The outer slab's construction was unsafe, so the caller
        // already accepted the slab contract. Inner chunks inherit that contract.
        let inner = Box::new(unsafe { BoundedSlab::with_capacity(self.chunk_capacity.get()) });

        let entry = ChunkEntry {
            inner,
            next_with_space: Cell::new(self.head_with_space.get()),
        };

        chunks.push(entry);
        self.head_with_space.set(chunk_idx);
    }

    // =========================================================================
    // Allocation API
    // =========================================================================

    /// Claims a slot from the freelist without writing a value.
    ///
    /// Always succeeds — grows the slab if needed. The returned [`Claim`]
    /// must be consumed via [`Claim::write()`] to complete the allocation.
    ///
    /// This two-phase allocation enables placement new optimization: the
    /// value can be constructed directly into the slot memory.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_slab::unbounded::Slab;
    ///
    /// // SAFETY: caller guarantees slab contract (see struct docs)
    /// let slab = unsafe { Slab::with_chunk_capacity(16) };
    /// let claim = slab.claim();
    /// let slot = claim.write(42u64);
    /// assert_eq!(*slot, 42);
    /// slab.free(slot);
    /// ```
    #[inline]
    pub fn claim(&self) -> Claim<'_, T> {
        let (slot_ptr, chunk_idx) = self.claim_ptr();
        Claim {
            slot_ptr,
            slab: self,
            chunk_idx,
        }
    }

    /// Claims a slot from the freelist, returning the raw pointer and chunk index.
    ///
    /// Always succeeds — grows the slab if needed. This is a low-level API for
    /// macro-generated code that needs to escape TLS closures.
    ///
    /// # Safety Contract
    ///
    /// The caller MUST either:
    /// - Write a value to the slot and use it as an allocated slot, OR
    /// - Return the pointer to the freelist via `free_ptr()` if abandoning
    #[doc(hidden)]
    #[inline]
    pub(crate) fn claim_ptr(&self) -> (*mut SlotCell<T>, usize) {
        // Ensure we have space (grow if needed)
        if self.head_with_space.get() == CHUNK_NONE {
            self.grow();
        }

        // Get the chunk with space
        let chunk_idx = self.head_with_space.get();
        let chunk = self.chunk(chunk_idx);
        let chunk_slab = &*chunk.inner;

        // Load freelist head pointer from chunk
        let slot_ptr = chunk_slab.free_head.get();
        debug_assert!(!slot_ptr.is_null(), "chunk on freelist has no free slots");

        // SAFETY: slot_ptr came from the freelist. Slot is vacant, so next_free is active.
        let next_free = unsafe { (*slot_ptr).get_next_free() };

        // Update chunk's freelist head
        chunk_slab.free_head.set(next_free);

        // If chunk is now full, remove from slab's available-chunk list
        if next_free.is_null() {
            self.head_with_space.set(chunk.next_with_space.get());
        }

        (slot_ptr, chunk_idx)
    }

    /// Allocates a slot and writes the value.
    ///
    /// Always succeeds — grows the slab if needed.
    #[inline]
    pub fn alloc(&self, value: T) -> Slot<T> {
        self.claim().write(value)
    }

    /// Frees a slot, dropping the value and returning storage to the freelist.
    ///
    /// Consumes the handle — the slot cannot be used after this call.
    ///
    /// # Performance
    ///
    /// O(n) where n = chunk count, due to chunk lookup. Typically 1-5 chunks.
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
    ///
    /// # Performance
    ///
    /// O(n) where n = chunk count, due to chunk lookup. Typically 1-5 chunks.
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

    /// Returns a slot to the freelist by pointer, given the chunk index.
    ///
    /// O(1) — goes directly to the correct chunk's freelist.
    /// Does NOT drop the value — caller must drop before calling.
    ///
    /// # Safety
    ///
    /// - `slot_ptr` must point to a slot within chunk `chunk_idx`
    /// - Value must already be dropped or moved out
    #[doc(hidden)]
    pub(crate) unsafe fn free_ptr_in_chunk(&self, slot_ptr: *mut SlotCell<T>, chunk_idx: usize) {
        let chunk = self.chunk(chunk_idx);
        let chunk_slab = &*chunk.inner;

        let free_head = chunk_slab.free_head.get();
        let was_full = free_head.is_null();

        // SAFETY: Caller guarantees slot_ptr is in chunk chunk_idx, transitioning to vacant.
        unsafe {
            (*slot_ptr).set_next_free(free_head);
        }
        chunk_slab.free_head.set(slot_ptr);

        if was_full {
            chunk.next_with_space.set(self.head_with_space.get());
            self.head_with_space.set(chunk_idx);
        }
    }

    /// Returns a slot to the freelist by pointer.
    ///
    /// Does NOT drop the value — caller must drop before calling.
    /// Finds the owning chunk via linear scan (typically 1-5 chunks).
    ///
    /// # Safety
    ///
    /// - `slot_ptr` must point to a slot within this slab
    /// - Value must already be dropped or moved out
    #[doc(hidden)]
    pub(crate) unsafe fn free_ptr(&self, slot_ptr: *mut SlotCell<T>) {
        let chunks = self.chunks();
        let cap = self.chunk_capacity.get();

        // Find which chunk owns this pointer
        for (chunk_idx, chunk) in chunks.iter().enumerate() {
            let chunk_slab = &*chunk.inner;
            let base = chunk_slab.slots_ptr();
            let end = base.wrapping_add(cap);

            if slot_ptr >= base && slot_ptr < end {
                let free_head = chunk_slab.free_head.get();
                let was_full = free_head.is_null();

                // SAFETY: slot_ptr is within this chunk's range
                unsafe {
                    (*slot_ptr).set_next_free(free_head);
                }
                chunk_slab.free_head.set(slot_ptr);

                if was_full {
                    chunk.next_with_space.set(self.head_with_space.get());
                    self.head_with_space.set(chunk_idx);
                }
                return;
            }
        }

        unreachable!("free_ptr: slot_ptr not found in any chunk");
    }
}

// =============================================================================
// Builder
// =============================================================================

/// Builder for [`Slab`].
///
/// Configures chunk capacity and optional pre-allocation before constructing
/// the slab. The type parameter only appears at the terminal [`build()`](Self::build)
/// call.
///
/// # Example
///
/// ```
/// use nexus_slab::unbounded::Builder;
///
/// // SAFETY: caller guarantees slab contract (see Slab docs)
/// let slab = unsafe {
///     Builder::new()
///         .chunk_capacity(4096)
///         .initial_chunks(4)
///         .build::<u64>()
/// };
/// let slot = slab.alloc(42);
/// assert_eq!(*slot, 42);
/// slab.free(slot);
/// ```
pub struct Builder {
    chunk_capacity: usize,
    initial_chunks: usize,
}

impl Builder {
    /// Creates a new builder with default settings.
    ///
    /// Defaults: `chunk_capacity = 256`, `initial_chunks = 0` (lazy growth).
    #[inline]
    pub fn new() -> Self {
        Self {
            chunk_capacity: 256,
            initial_chunks: 0,
        }
    }

    /// Sets the capacity of each chunk.
    ///
    /// # Panics
    ///
    /// Panics at [`build()`](Self::build) if zero.
    #[inline]
    pub fn chunk_capacity(mut self, cap: usize) -> Self {
        self.chunk_capacity = cap;
        self
    }

    /// Sets the number of chunks to pre-allocate.
    ///
    /// Default is 0 (lazy growth — chunks allocated on first use).
    #[inline]
    pub fn initial_chunks(mut self, n: usize) -> Self {
        self.initial_chunks = n;
        self
    }

    /// Builds the slab.
    ///
    /// # Safety
    ///
    /// See [`Slab`] safety contract.
    ///
    /// # Panics
    ///
    /// Panics if `chunk_capacity` is zero.
    #[inline]
    pub unsafe fn build<T>(self) -> Slab<T> {
        assert!(self.chunk_capacity > 0, "chunk_capacity must be non-zero");

        let slab = Slab {
            chunks: core::cell::UnsafeCell::new(Vec::new()),
            chunk_capacity: Cell::new(self.chunk_capacity),
            head_with_space: Cell::new(CHUNK_NONE),
        };

        for _ in 0..self.initial_chunks {
            slab.grow();
        }
        slab
    }
}

impl Default for Builder {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Debug for Builder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Builder")
            .field("chunk_capacity", &self.chunk_capacity)
            .field("initial_chunks", &self.initial_chunks)
            .finish()
    }
}

impl<T> fmt::Debug for Slab<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Slab")
            .field("capacity", &self.capacity())
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
        let slab = unsafe { Slab::<u64>::with_chunk_capacity(16) };

        let slot = slab.alloc(42);
        assert_eq!(*slot, 42);
        slab.free(slot);
    }

    #[test]
    fn slab_grows() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab = unsafe { Slab::<u64>::with_chunk_capacity(4) };

        let mut slots = Vec::new();
        for i in 0..10 {
            slots.push(slab.alloc(i));
        }

        assert!(slab.capacity() >= 10);

        for slot in slots {
            slab.free(slot);
        }
    }

    #[test]
    fn slot_deref_mut() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab = unsafe { Slab::<String>::with_chunk_capacity(16) };
        let mut slot = slab.alloc("hello".to_string());
        slot.push_str(" world");
        assert_eq!(&*slot, "hello world");
        slab.free(slot);
    }

    #[test]
    fn slot_dealloc_take() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab = unsafe { Slab::<String>::with_chunk_capacity(16) };
        let slot = slab.alloc("hello".to_string());

        let value = slab.take(slot);
        assert_eq!(value, "hello");
    }

    #[test]
    fn chunk_freelist_maintenance() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab = unsafe { Slab::<u64>::with_chunk_capacity(2) };

        // Fill first chunk
        let s1 = slab.alloc(1);
        let s2 = slab.alloc(2);
        // Triggers growth
        let s3 = slab.alloc(3);

        // Free from first chunk — should add it back to available list
        slab.free(s1);

        // Should reuse the freed slot
        let s4 = slab.alloc(4);

        slab.free(s2);
        slab.free(s3);
        slab.free(s4);
    }

    #[test]
    fn slot_size() {
        assert_eq!(std::mem::size_of::<Slot<u64>>(), 8);
    }

    #[test]
    fn borrow_traits() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab = unsafe { Slab::<u64>::with_chunk_capacity(16) };
        let mut slot = slab.alloc(42);

        let borrowed: &u64 = slot.borrow();
        assert_eq!(*borrowed, 42);

        let borrowed_mut: &mut u64 = slot.borrow_mut();
        *borrowed_mut = 100;
        assert_eq!(*slot, 100);

        slab.free(slot);
    }

    // =========================================================================
    // Builder tests
    // =========================================================================

    #[test]
    fn builder_defaults() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab = unsafe { Builder::new().build::<u64>() };
        assert_eq!(slab.chunk_capacity(), 256);
        assert_eq!(slab.chunk_count(), 0);

        let slot = slab.alloc(42);
        assert_eq!(*slot, 42);
        slab.free(slot);
    }

    #[test]
    fn builder_custom_chunk_capacity() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab = unsafe { Builder::new().chunk_capacity(64).build::<u64>() };
        assert_eq!(slab.chunk_capacity(), 64);

        let slot = slab.alloc(1);
        assert_eq!(slab.capacity(), 64);
        slab.free(slot);
    }

    #[test]
    fn builder_initial_chunks() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab = unsafe {
            Builder::new()
                .chunk_capacity(32)
                .initial_chunks(4)
                .build::<u64>()
        };
        assert_eq!(slab.chunk_count(), 4);
        assert_eq!(slab.capacity(), 128);
    }

    #[test]
    #[should_panic(expected = "chunk_capacity must be non-zero")]
    fn builder_zero_chunk_capacity_panics() {
        // SAFETY: test slab; single-threaded; panics before any slot can be allocated.
        let _slab = unsafe { Builder::new().chunk_capacity(0).build::<u64>() };
    }
}
