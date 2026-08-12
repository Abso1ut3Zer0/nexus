//! Timer wheel level — one tier in the hierarchical wheel.
//!
//! Each level has `slots_per_level` slots (default 64). Entries are placed
//! into slots based on their deadline. Non-empty slots are tracked via a
//! `u64` bitmask so poll/next_deadline only visit slots that actually
//! contain entries.
//!
//! Two structures operate here:
//! 1. **Entry DLL** — per-slot doubly-linked list of entries (WheelEntry prev/next).
//! 2. **Active-slot bitmask** — per-level `u64`, one bit per non-empty slot.

use std::cell::Cell;

use crate::entry::{EntryPtr, entry_ref, null_entry};

// =============================================================================
// WheelSlot — one slot position within a level
// =============================================================================

/// A single slot in a timer wheel level.
///
/// Contains the head/tail of the entry DLL. Active-slot tracking is handled
/// by the parent level's bitmask, not by per-slot DLL links.
pub(crate) struct WheelSlot<T> {
    /// Head of the entry DLL (first entry in this slot, or null).
    entry_head: Cell<EntryPtr<T>>,
    /// Tail of the entry DLL (last entry, for O(1) append).
    entry_tail: Cell<EntryPtr<T>>,
    /// Minimum deadline over this slot's entries, or `u64::MAX` when empty.
    ///
    /// Maintained by the **wheel** (in `insert_entry` / `poll_level` / on drain),
    /// NOT by `push_entry` / `remove_entry` — so `TimeoutList`, which reuses this
    /// slot type as its whole list, pays nothing for a field it never reads.
    ///
    /// **Stale-low after a wheel remove:** an under-estimate only ever causes an
    /// unnecessary walk, never a skipped fire; `poll_level` recomputes it exactly
    /// whenever it fully walks the slot. See `wheel::poll_level`.
    min_deadline: Cell<u64>,
}

impl<T: 'static> WheelSlot<T> {
    /// Creates an empty slot (no entries).
    ///
    /// `pub(crate)` so both wheel front-ends can hold slots directly:
    /// the wheel builds an array of them per level, while `TimeoutList`
    /// holds a single one as its whole sorted list.
    pub(crate) fn new() -> Self {
        WheelSlot {
            entry_head: Cell::new(null_entry()),
            entry_tail: Cell::new(null_entry()),
            min_deadline: Cell::new(u64::MAX),
        }
    }

    /// Returns true if this slot has no entries.
    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.entry_head.get().is_null()
    }

    // =========================================================================
    // Entry DLL operations
    // =========================================================================

    /// Appends an entry to the tail of this slot's DLL.
    ///
    /// # Safety
    ///
    /// `entry_ptr` must be a valid, non-null pointer to an occupied slab slot
    /// containing a `WheelEntry<T>`. The entry must not already be in any DLL.
    #[inline]
    pub(crate) unsafe fn push_entry(&self, entry_ptr: EntryPtr<T>) {
        // SAFETY: caller guarantees entry_ptr is valid and occupied
        let entry = unsafe { entry_ref(entry_ptr) };
        entry.set_prev(null_entry());
        entry.set_next(null_entry());

        let tail = self.entry_tail.get();
        if tail.is_null() {
            // Empty list — entry becomes both head and tail
            self.entry_head.set(entry_ptr);
        } else {
            // Append after current tail
            // SAFETY: tail is valid (was set from a previous push)
            let tail_entry = unsafe { entry_ref(tail) };
            tail_entry.set_next(entry_ptr);
            entry.set_prev(tail);
        }
        self.entry_tail.set(entry_ptr);
    }

    /// Removes an entry from this slot's DLL.
    ///
    /// # Safety
    ///
    /// `entry_ptr` must be in THIS slot's DLL. Caller must ensure the entry
    /// is currently linked (not already removed).
    #[inline]
    pub(crate) unsafe fn remove_entry(&self, entry_ptr: EntryPtr<T>) {
        // SAFETY: caller guarantees entry_ptr is valid and in this slot's DLL
        let entry = unsafe { entry_ref(entry_ptr) };
        let prev = entry.prev();
        let next = entry.next();

        if prev.is_null() {
            // Entry was the head
            self.entry_head.set(next);
        } else {
            // SAFETY: prev is valid (was set from a previous push/link)
            unsafe { entry_ref(prev) }.set_next(next);
        }

        if next.is_null() {
            // Entry was the tail
            self.entry_tail.set(prev);
        } else {
            // SAFETY: next is valid (was set from a previous push/link)
            unsafe { entry_ref(next) }.set_prev(prev);
        }

        // Clear links so a double-remove is detectable
        entry.set_prev(null_entry());
        entry.set_next(null_entry());
    }

    /// Returns the head entry pointer (may be null if slot is empty).
    #[inline]
    pub(crate) fn entry_head(&self) -> EntryPtr<T> {
        self.entry_head.get()
    }

    /// Returns the tail entry pointer (may be null if slot is empty).
    ///
    /// Used by `TimeoutList` to peek the last-inserted deadline for the
    /// monotone-insertion `debug_assert`. Not read on any wheel hot path.
    #[inline]
    pub(crate) fn entry_tail(&self) -> EntryPtr<T> {
        self.entry_tail.get()
    }

    /// The cached minimum deadline over this slot's entries (`u64::MAX` when
    /// empty). May be stale-low after a wheel remove — see the field docs.
    #[inline]
    pub(crate) fn min_deadline(&self) -> u64 {
        self.min_deadline.get()
    }

    /// Sets the slot's cached minimum deadline. Wheel-only maintenance.
    #[inline]
    pub(crate) fn set_min_deadline(&self, ticks: u64) {
        self.min_deadline.set(ticks);
    }
}

// =============================================================================
// Level — one tier of the wheel
// =============================================================================

/// One level (tier) in the hierarchical timer wheel.
///
/// All levels have the same number of slots (`slots_per_level`, max 64).
/// Higher levels cover wider time ranges with coarser granularity.
/// Non-empty slots are tracked via a `u64` bitmask for O(1) activation
/// checks and branch-free iteration.
pub(crate) struct Level<T> {
    /// Slot storage — `slots_per_level` slots, heap-allocated once at construction.
    slots: Box<[WheelSlot<T>]>,
    /// Bitmask of non-empty slots. Bit `i` is set iff `slots[i]` has entries.
    active_slots: Cell<u64>,
    /// Bit shift for this level: `level_index * clk_shift`.
    /// Level 0 shift = 0, level 1 shift = clk_shift, level 2 = 2*clk_shift, ...
    shift: u32,
    /// Bitmask: `slots_per_level - 1` (e.g. 63 for 64 slots).
    mask: usize,
    /// Number of ticks this level spans: `slots_per_level << shift`.
    range: u64,
}

impl<T: 'static> Level<T> {
    /// Creates a new level with the given parameters.
    pub(crate) fn new(slots_per_level: usize, level_index: usize, clk_shift: u32) -> Self {
        let shift = (level_index as u32) * clk_shift;

        let slots: Vec<WheelSlot<T>> = (0..slots_per_level).map(|_| WheelSlot::new()).collect();

        Level {
            slots: slots.into_boxed_slice(),
            active_slots: Cell::new(0),
            shift,
            mask: slots_per_level - 1,
            range: (slots_per_level as u64) << shift,
        }
    }

    /// Returns the shift for this level.
    #[cfg(test)]
    #[inline]
    pub(crate) fn shift(&self) -> u32 {
        self.shift
    }

    /// Returns the mask for this level.
    #[cfg(test)]
    #[inline]
    pub(crate) fn mask(&self) -> usize {
        self.mask
    }

    /// Returns the range (in ticks) this level covers.
    #[inline]
    pub(crate) fn range(&self) -> u64 {
        self.range
    }

    /// Computes the slot index for a given deadline.
    #[inline]
    pub(crate) fn slot_index(&self, deadline_ticks: u64) -> usize {
        ((deadline_ticks >> self.shift) as usize) & self.mask
    }

    /// Returns a reference to the slot at the given index.
    #[inline]
    pub(crate) fn slot(&self, index: usize) -> &WheelSlot<T> {
        debug_assert!(index < self.slots.len());
        &self.slots[index]
    }

    // =========================================================================
    // Active-slot bitmask operations
    // =========================================================================

    /// Marks a slot as active (has entries).
    #[inline]
    pub(crate) fn activate_slot(&self, slot_idx: usize) {
        self.active_slots
            .set(self.active_slots.get() | (1 << slot_idx));
    }

    /// Marks a slot as inactive (empty).
    #[inline]
    pub(crate) fn deactivate_slot(&self, slot_idx: usize) {
        self.active_slots
            .set(self.active_slots.get() & !(1 << slot_idx));
    }

    /// Returns the bitmask of active (non-empty) slots.
    #[inline]
    pub(crate) fn active_slots(&self) -> u64 {
        self.active_slots.get()
    }

    /// Returns true if any slot in this level has entries.
    #[inline]
    pub(crate) fn is_active(&self) -> bool {
        self.active_slots.get() != 0
    }

    /// Returns the number of slots per level.
    #[cfg(test)]
    #[inline]
    pub(crate) fn num_slots(&self) -> usize {
        self.slots.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::entry::WheelEntry;
    use nexus_slab::{Slot, unbounded};

    fn make_entry<T>(
        slab: &unbounded::Slab<WheelEntry<T>>,
        deadline: u64,
        value: T,
    ) -> EntryPtr<T> {
        let entry = WheelEntry::new(deadline, value, 1);
        let slot = slab.alloc(entry);
        slot.into_raw()
    }

    #[test]
    fn slot_push_remove_single() {
        // SAFETY: single-threaded test, slab contract upheld
        let slab = unsafe { unbounded::Slab::<WheelEntry<u64>>::with_chunk_capacity(16) };
        let ws = WheelSlot::<u64>::new();

        assert!(ws.is_empty());

        let e1 = make_entry(&slab, 10, 100);
        // SAFETY: e1 is a valid slab-allocated pointer; slot invariant upheld.
        unsafe { ws.push_entry(e1) };
        assert!(!ws.is_empty());

        // SAFETY: e1 was pushed above and is still in the list.
        unsafe { ws.remove_entry(e1) };
        assert!(ws.is_empty());

        // SAFETY: e1 was allocated from this slab via into_raw()
        slab.free(unsafe { Slot::from_raw(e1) });
    }

    #[test]
    fn slot_push_remove_multiple() {
        // SAFETY: single-threaded test, slab contract upheld
        let slab = unsafe { unbounded::Slab::<WheelEntry<u64>>::with_chunk_capacity(16) };
        let ws = WheelSlot::<u64>::new();

        let e1 = make_entry(&slab, 10, 1);
        let e2 = make_entry(&slab, 20, 2);
        let e3 = make_entry(&slab, 30, 3);

        // SAFETY: e1/e2/e3 are valid slab-allocated pointers; slot invariant upheld.
        unsafe {
            ws.push_entry(e1);
            ws.push_entry(e2);
            ws.push_entry(e3);
        }

        // Remove middle
        // SAFETY: e2 was pushed above and is still in the list.
        unsafe { ws.remove_entry(e2) };
        // Head should still be e1, e1.next = e3
        assert_eq!(ws.entry_head(), e1);
        // SAFETY: e1 and e3 are valid slab-allocated pointers still in the list.
        unsafe {
            assert_eq!(entry_ref(e1).next(), e3);
            assert_eq!(entry_ref(e3).prev(), e1);
        }

        // Remove head
        // SAFETY: e1 is still in the list.
        unsafe { ws.remove_entry(e1) };
        assert_eq!(ws.entry_head(), e3);

        // Remove last
        // SAFETY: e3 is still in the list.
        unsafe { ws.remove_entry(e3) };
        assert!(ws.is_empty());

        // SAFETY: all ptrs were allocated from this slab via into_raw()
        unsafe {
            slab.free(Slot::from_raw(e1));
            slab.free(Slot::from_raw(e2));
            slab.free(Slot::from_raw(e3));
        }
    }

    #[test]
    fn level_slot_index_computation() {
        // Level 0: shift=0, mask=63, 64 slots
        let lvl = Level::<u64>::new(64, 0, 3);
        assert_eq!(lvl.shift(), 0);
        assert_eq!(lvl.mask(), 63);
        assert_eq!(lvl.num_slots(), 64);
        assert_eq!(lvl.slot_index(0), 0);
        assert_eq!(lvl.slot_index(1), 1);
        assert_eq!(lvl.slot_index(63), 63);
        assert_eq!(lvl.slot_index(64), 0); // wraps
        assert_eq!(lvl.range(), 64);

        // Level 1: shift=3, mask=63
        let lvl1 = Level::<u64>::new(64, 1, 3);
        assert_eq!(lvl1.shift(), 3);
        assert_eq!(lvl1.mask(), 63);
        assert_eq!(lvl1.num_slots(), 64);
        assert_eq!(lvl1.slot_index(0), 0);
        assert_eq!(lvl1.slot_index(8), 1); // 8 >> 3 = 1
        assert_eq!(lvl1.slot_index(64), 8); // 64 >> 3 = 8
        assert_eq!(lvl1.range(), 512);

        // Level 2: shift=6, mask=63
        let lvl2 = Level::<u64>::new(64, 2, 3);
        assert_eq!(lvl2.shift(), 6);
        assert_eq!(lvl2.slot_index(64), 1); // 64 >> 6 = 1
        assert_eq!(lvl2.slot_index(512), 8); // 512 >> 6 = 8
        assert_eq!(lvl2.range(), 4096);
    }

    #[test]
    fn level_active_slot_bitmask() {
        let lvl = Level::<u64>::new(64, 0, 3);

        assert!(!lvl.is_active());
        assert_eq!(lvl.active_slots(), 0);

        lvl.activate_slot(5);
        assert!(lvl.is_active());
        assert_eq!(lvl.active_slots(), 1 << 5);

        lvl.activate_slot(10);
        assert_eq!(lvl.active_slots(), (1 << 5) | (1 << 10));

        // Idempotent
        lvl.activate_slot(5);
        assert_eq!(lvl.active_slots(), (1 << 5) | (1 << 10));

        lvl.deactivate_slot(5);
        assert_eq!(lvl.active_slots(), 1 << 10);

        lvl.deactivate_slot(10);
        assert!(!lvl.is_active());
    }
}
