//! Internal slab-level bookkeeping for the multi-slab allocator.
//!
//! This module contains the data structures for managing individual slabs
//! (logical memory chunks). The actual slot storage and memory operations
//! are handled in lib.rs - this module is purely bookkeeping.

/// Sentinel value for empty slot freelist (within a slab).
pub(crate) const SLOT_NONE: u32 = u32::MAX;

/// Sentinel value for empty slab list.
pub(crate) const SLAB_NONE: u32 = u32::MAX;

/// A slot in the slab - either vacant or occupied.
///
/// Slots are stored in mmap'd memory and accessed via unsafe pointer ops.
/// The discriminant allows safe checking of slot state.
pub(crate) enum Slot<T> {
    /// Slot is empty and part of the per-slab free list.
    /// `next_free` is a local index within the same slab.
    Vacant { next_free: u32 },
    /// Slot contains a value.
    Occupied { value: T },
}

/// Which list a slab belongs to, or if it's outside any list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SlabState {
    /// Active slab for bump allocation. Not in any list.
    Current,
    /// Fully empty (occupied=0), in empty_head stack. Ready for reset.
    Empty,
    /// Under-utilized (occupied <= sparse_threshold), in sparse_head list.
    Sparse,
    /// Heavily used (occupied > sparse_threshold), in dense_head list.
    Dense,
    /// Fully occupied (occupied == slots_per_slab). Not in any list.
    Full,
}

/// Metadata for a single slab (logical memory chunk).
///
/// Each slab tracks its own bump pointer, freelist, and occupancy count.
/// Slabs are linked into doubly-linked lists based on their state.
///
/// Size: 24 bytes (6 x u32), padded to 32 bytes for cache alignment.
#[derive(Debug)]
pub(crate) struct SlabMeta {
    /// Bump allocation cursor - next slot for bump allocation (local index).
    /// Range: 0..=slots_per_slab. When bump_cursor == slots_per_slab,
    /// no bump slots remain. This is a high-water mark that never decreases
    /// (except on reset when occupied == 0).
    pub bump_cursor: u32,

    /// Number of currently occupied slots.
    pub occupied: u32,

    /// Head of per-slab freelist (local index), or SLOT_NONE if empty.
    pub free_head: u32,

    /// Previous slab in current list (slab index), or SLAB_NONE.
    pub prev: u32,

    /// Next slab in current list (slab index), or SLAB_NONE.
    pub next: u32,

    /// Which list this slab belongs to (or Current/Full if not in a list).
    pub state: SlabState,
}

impl SlabMeta {
    /// Create a new slab in empty state with all slots available for bump allocation.
    #[inline]
    pub const fn new() -> Self {
        Self {
            bump_cursor: 0,
            occupied: 0,
            free_head: SLOT_NONE,
            prev: SLAB_NONE,
            next: SLAB_NONE,
            state: SlabState::Empty,
        }
    }

    /// Returns true if there are slots available for bump allocation.
    #[inline]
    pub const fn has_bump(&self, slots_per_slab: u32) -> bool {
        self.bump_cursor < slots_per_slab
    }

    /// Returns true if no slots are occupied.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.occupied == 0
    }

    /// Returns true if all slots are occupied.
    #[inline]
    pub const fn is_full(&self, slots_per_slab: u32) -> bool {
        self.occupied == slots_per_slab
    }

    /// Reset slab to initial state for reuse.
    ///
    /// Called when an empty slab is recycled for new allocations.
    /// Restores bump allocation from the beginning.
    ///
    /// # Safety contract
    ///
    /// Caller must ensure all slots are actually vacant (occupied == 0).
    #[inline]
    pub fn reset(&mut self) {
        debug_assert!(self.is_empty(), "reset called on non-empty slab");
        self.bump_cursor = 0;
        self.free_head = SLOT_NONE;
        // occupied is already 0
        // prev/next/state managed by caller when moving between lists
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_slab_state() {
        let slab = SlabMeta::new();

        assert_eq!(slab.bump_cursor, 0);
        assert_eq!(slab.occupied, 0);
        assert_eq!(slab.free_head, SLOT_NONE);
        assert_eq!(slab.prev, SLAB_NONE);
        assert_eq!(slab.next, SLAB_NONE);
        assert_eq!(slab.state, SlabState::Empty);
    }

    #[test]
    fn has_bump_boundary_conditions() {
        let mut slab = SlabMeta::new();
        let slots_per_slab = 256;

        // Fresh slab has bump
        assert!(slab.has_bump(slots_per_slab));

        // One before exhaustion
        slab.bump_cursor = 255;
        assert!(slab.has_bump(slots_per_slab));

        // Exactly exhausted
        slab.bump_cursor = 256;
        assert!(!slab.has_bump(slots_per_slab));

        // Beyond (shouldn't happen, but defensive)
        slab.bump_cursor = 257;
        assert!(!slab.has_bump(slots_per_slab));
    }

    #[test]
    fn is_empty_check() {
        let mut slab = SlabMeta::new();

        assert!(slab.is_empty());

        slab.occupied = 1;
        assert!(!slab.is_empty());

        slab.occupied = 0;
        assert!(slab.is_empty());
    }

    #[test]
    fn is_full_check() {
        let mut slab = SlabMeta::new();
        let slots_per_slab = 256;

        assert!(!slab.is_full(slots_per_slab));

        slab.occupied = 255;
        assert!(!slab.is_full(slots_per_slab));

        slab.occupied = 256;
        assert!(slab.is_full(slots_per_slab));
    }

    #[test]
    fn reset_restores_bump_allocation() {
        let mut slab = SlabMeta::new();

        // Simulate usage: slab was fully bumped, then everything freed
        slab.bump_cursor = 256;
        slab.free_head = 10; // Some freelist chain
        slab.occupied = 0; // All freed

        slab.reset();

        assert_eq!(slab.bump_cursor, 0);
        assert_eq!(slab.free_head, SLOT_NONE);
        assert_eq!(slab.occupied, 0);
    }

    #[test]
    fn slab_state_is_copy() {
        fn assert_copy<T: Copy>() {}
        assert_copy::<SlabState>();
    }

    #[test]
    fn slot_size_check() {
        // Ensure Slot discriminant + data is reasonable
        // For a u64 payload, Slot should be 16 bytes (discriminant + padding + u64)
        assert!(std::mem::size_of::<Slot<u64>>() <= 16);
    }

    #[test]
    fn slab_meta_size() {
        // SlabMeta should be compact - 6 x u32 = 24 bytes + enum
        // With alignment, should be <= 32 bytes
        assert!(std::mem::size_of::<SlabMeta>() <= 32);
    }

    #[test]
    fn sentinel_values_are_max() {
        // Sentinels should be u32::MAX so they're invalid indices
        assert_eq!(SLOT_NONE, u32::MAX);
        assert_eq!(SLAB_NONE, u32::MAX);
    }
}
