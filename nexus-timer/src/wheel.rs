//! Timer wheel — the main data structure.
//!
//! `TimerWheel<T, S>` is a multi-level, no-cascade timer wheel. Entries are
//! placed into a level based on how far in the future their deadline is.
//! Once placed, an entry never moves — poll checks `deadline_ticks <= now`
//! per entry.

use std::cell::Cell;
use std::marker::PhantomData;
use std::mem;
use std::time::{Duration, Instant};

use nexus_slab::{Full, Slot, bounded, unbounded};

use crate::entry::{EntryPtr, WheelEntry, entry_ref};
use crate::handle::TimerHandle;
use crate::level::Level;
use crate::store::{BoundedStore, SlabStore};

// =============================================================================
// WheelBuilder (typestate)
// =============================================================================

/// Builder for configuring a timer wheel.
///
/// Defaults match the Linux kernel timer wheel (1ms tick, 64 slots/level,
/// 8x multiplier, 7 levels → ~4.7 hour range).
///
/// # Examples
///
/// ```
/// use std::time::{Duration, Instant};
/// use nexus_timer::{Wheel, WheelBuilder};
///
/// let now = Instant::now();
///
/// // All defaults
/// let wheel: Wheel<u64> = WheelBuilder::default().unbounded(4096).build(now);
///
/// // Custom config
/// let wheel: Wheel<u64> = WheelBuilder::default()
///     .tick_duration(Duration::from_micros(100))
///     .slots_per_level(32)
///     .unbounded(4096)
///     .build(now);
/// ```
#[derive(Debug, Clone, Copy)]
pub struct WheelBuilder {
    tick_duration: Duration,
    slots_per_level: usize,
    clk_shift: u32,
    num_levels: usize,
}

impl Default for WheelBuilder {
    fn default() -> Self {
        WheelBuilder {
            tick_duration: Duration::from_millis(1),
            slots_per_level: 64,
            clk_shift: 3,
            num_levels: 7,
        }
    }
}

impl WheelBuilder {
    /// Creates a new builder with default configuration.
    pub fn new() -> Self {
        Self::default()
    }

    /// Sets the tick duration. Default: 1ms.
    pub fn tick_duration(mut self, d: Duration) -> Self {
        self.tick_duration = d;
        self
    }

    /// Sets the number of slots per level. Must be a power of 2. Default: 64.
    pub fn slots_per_level(mut self, n: usize) -> Self {
        self.slots_per_level = n;
        self
    }

    /// Sets the bit shift between levels (multiplier = 2^clk_shift). Default: 3 (8x).
    pub fn clk_shift(mut self, s: u32) -> Self {
        self.clk_shift = s;
        self
    }

    /// Sets the number of levels. Default: 7.
    pub fn num_levels(mut self, n: usize) -> Self {
        self.num_levels = n;
        self
    }

    /// Transitions to an unbounded wheel builder.
    ///
    /// `chunk_capacity` is the slab chunk size (entries per chunk). The slab
    /// grows by adding new chunks as needed.
    pub fn unbounded(self, chunk_capacity: usize) -> UnboundedWheelBuilder {
        UnboundedWheelBuilder {
            config: self,
            chunk_capacity,
        }
    }

    /// Transitions to a bounded wheel builder.
    ///
    /// `capacity` is the maximum number of concurrent timers.
    pub fn bounded(self, capacity: usize) -> BoundedWheelBuilder {
        BoundedWheelBuilder {
            config: self,
            capacity,
        }
    }

    fn validate(&self) {
        assert!(
            self.slots_per_level.is_power_of_two(),
            "slots_per_level must be a power of 2, got {}",
            self.slots_per_level
        );
        assert!(
            self.slots_per_level <= 64,
            "slots_per_level must be <= 64 (u64 bitmask), got {}",
            self.slots_per_level
        );
        assert!(self.num_levels > 0, "num_levels must be > 0");
        assert!(
            self.num_levels <= 8,
            "num_levels must be <= 8 (u8 bitmask), got {}",
            self.num_levels
        );
        assert!(self.clk_shift > 0, "clk_shift must be > 0");
        assert!(
            !self.tick_duration.is_zero(),
            "tick_duration must be non-zero"
        );
        let max_shift = (self.num_levels - 1) as u64 * self.clk_shift as u64;
        assert!(
            max_shift < 64,
            "(num_levels - 1) * clk_shift must be < 64, got {}",
            max_shift
        );
        let slots_log2 = self.slots_per_level.trailing_zeros() as u64;
        assert!(
            slots_log2 + max_shift < 64,
            "slots_per_level << max_shift would overflow u64"
        );
        // Cascade progress guard. When a due slot is polled, a not-yet-due entry
        // is relocated to a strictly finer level (see `TimerWheel::poll_level`).
        // That requires a level's per-slot granularity (2^clk_shift) to be
        // smaller than the number of slots per level; otherwise an entry could
        // relocate to the *same* level and poll would live-lock. Both are powers
        // of two, so `2^clk_shift < slots_per_level` iff `clk_shift < slots_log2`
        // (avoids a shift that could overflow for absurd clk_shift). Checked last
        // so a config that also overflows reports the overflow first.
        assert!(
            (self.clk_shift as u64) < slots_log2,
            "2^clk_shift must be < slots_per_level so cascade relocates to a \
             strictly finer level (got clk_shift = {}, slots_per_level = {})",
            self.clk_shift,
            self.slots_per_level,
        );
    }

    fn tick_ns(&self) -> u64 {
        self.tick_duration.as_nanos() as u64
    }
}

/// Terminal builder for an unbounded timer wheel.
///
/// Created via [`WheelBuilder::unbounded`]. The only method is `.build()`.
#[derive(Debug)]
pub struct UnboundedWheelBuilder {
    config: WheelBuilder,
    chunk_capacity: usize,
}

impl UnboundedWheelBuilder {
    /// Builds the unbounded timer wheel.
    ///
    /// # Panics
    ///
    /// Panics if the configuration is invalid (non-power-of-2 slots, zero
    /// levels, zero clk_shift, or zero tick duration).
    pub fn build<T: 'static>(self, now: Instant) -> Wheel<T> {
        self.config.validate();
        // SAFETY: Timer wheel is single-threaded (!Send, !Sync). All slots
        // are freed via Slot::from_raw() + slab.free() before the wheel drops.
        // The slab is never shared across threads.
        let slab = unsafe { unbounded::Slab::with_chunk_capacity(self.chunk_capacity) };
        let levels = build_levels::<T>(&self.config);
        let tick_ns = self.config.tick_ns();
        TimerWheel {
            slab,
            num_levels: self.config.num_levels,
            levels,
            current_ticks: 0,
            tick_ns,
            inv_tick_ns: (1u128 << 64) / tick_ns as u128,
            epoch: now,
            active_levels: 0,
            len: 0,
            min_deadline: Cell::new(None),
            _marker: PhantomData,
        }
    }
}

/// Terminal builder for a bounded timer wheel.
///
/// Created via [`WheelBuilder::bounded`]. The only method is `.build()`.
#[derive(Debug)]
pub struct BoundedWheelBuilder {
    config: WheelBuilder,
    capacity: usize,
}

impl BoundedWheelBuilder {
    /// Builds the bounded timer wheel.
    ///
    /// # Panics
    ///
    /// Panics if the configuration is invalid (non-power-of-2 slots, zero
    /// levels, zero clk_shift, or zero tick duration).
    pub fn build<T: 'static>(self, now: Instant) -> BoundedWheel<T> {
        self.config.validate();
        // SAFETY: Timer wheel is single-threaded (!Send, !Sync). All slots
        // are freed via Slot::from_raw() + slab.free() before the wheel drops.
        // The slab is never shared across threads.
        let slab = unsafe { bounded::Slab::with_capacity(self.capacity) };
        let levels = build_levels::<T>(&self.config);
        let tick_ns = self.config.tick_ns();
        TimerWheel {
            slab,
            num_levels: self.config.num_levels,
            levels,
            current_ticks: 0,
            tick_ns,
            inv_tick_ns: (1u128 << 64) / tick_ns as u128,
            epoch: now,
            active_levels: 0,
            len: 0,
            min_deadline: Cell::new(None),
            _marker: PhantomData,
        }
    }
}

// =============================================================================
// TimerWheel
// =============================================================================

/// A multi-level, no-cascade timer wheel.
///
/// Generic over:
/// - `T` — the user payload stored with each timer.
/// - `S` — the slab storage backend. Defaults to `unbounded::Slab`.
///
/// # Thread Safety
///
/// `Send` but `!Sync`. Can be moved to a thread at setup but must not
/// be shared. All internal raw pointers point into owned allocations
/// (slab chunks, level slot arrays) — moving the wheel moves the heap
/// data with it.
pub struct TimerWheel<
    T: 'static,
    S: SlabStore<Item = WheelEntry<T>> = unbounded::Slab<WheelEntry<T>>,
> {
    slab: S,
    levels: Vec<Level<T>>,
    num_levels: usize,
    active_levels: u8,
    current_ticks: u64,
    tick_ns: u64,
    inv_tick_ns: u128,
    epoch: Instant,
    len: usize,
    min_deadline: Cell<Option<u64>>,
    _marker: PhantomData<*const ()>, // !Send (overridden below), !Sync
}

// SAFETY: TimerWheel<T, S> exclusively owns all memory behind its raw pointers.
//
// Pointer inventory and ownership:
// - Slot `entry_head`/`entry_tail` — point into slab-owned memory (SlotCell
//   in a slab chunk). Slab chunks are Vec<SlotCell<T>> heap allocations.
// - DLL links (`WheelEntry::prev`, `WheelEntry::next`) — point to other
//   SlotCells in the same slab.
// - `Level::slots` — `Box<[WheelSlot<T>]>`, owned by the level.
//
// All pointed-to memory lives inside owned collections (Vec, Box<[T]>).
// When TimerWheel is moved, the heap allocations stay at their addresses —
// the internal pointers remain valid. No thread-local state. No shared
// ownership.
//
// T: Send is required because timer values cross the thread boundary with
// the wheel.
//
// S is NOT required to be Send. Slab types are !Send (raw pointers, Cell)
// but the wheel exclusively owns its slab — no shared access, no aliasing.
// Moving the wheel moves the slab; heap allocations stay at their addresses
// so internal pointers remain valid.
//
// Outstanding TimerHandle<T> values are !Send and cannot follow the wheel
// across threads. They become inert — consuming them requires &mut
// TimerWheel which the original thread no longer has. The debug_assert in
// TimerHandle::drop catches this as a programming error. Worst case is a
// slot leak (refcount stuck at 1), not unsoundness.
#[allow(clippy::non_send_fields_in_send_ty)]
unsafe impl<T: Send + 'static, S: SlabStore<Item = WheelEntry<T>>> Send for TimerWheel<T, S> {}

/// A timer wheel backed by a fixed-capacity slab.
pub type BoundedWheel<T> = TimerWheel<T, bounded::Slab<WheelEntry<T>>>;

/// A timer wheel backed by a growable slab.
pub type Wheel<T> = TimerWheel<T, unbounded::Slab<WheelEntry<T>>>;

// =============================================================================
// Construction
// =============================================================================

impl<T: 'static> Wheel<T> {
    /// Creates an unbounded timer wheel with default configuration.
    ///
    /// `now` fixes the reference epoch — pass one monotone clock source
    /// (e.g. `Instant::now()`) here and to every `schedule`/`poll`. For custom
    /// configuration, use [`WheelBuilder`].
    pub fn unbounded(chunk_capacity: usize, now: Instant) -> Self {
        WheelBuilder::default().unbounded(chunk_capacity).build(now)
    }
}

impl<T: 'static> BoundedWheel<T> {
    /// Creates a bounded timer wheel with default configuration.
    ///
    /// `now` fixes the reference epoch — pass one monotone clock source
    /// (e.g. `Instant::now()`) here and to every `schedule`/`poll`. For custom
    /// configuration, use [`WheelBuilder`].
    pub fn bounded(capacity: usize, now: Instant) -> Self {
        WheelBuilder::default().bounded(capacity).build(now)
    }
}

fn build_levels<T: 'static>(config: &WheelBuilder) -> Vec<Level<T>> {
    (0..config.num_levels)
        .map(|i| Level::new(config.slots_per_level, i, config.clk_shift))
        .collect()
}

// =============================================================================
// Schedule
// =============================================================================

impl<T: 'static, S: SlabStore<Item = WheelEntry<T>>> TimerWheel<T, S> {
    /// Schedules a timer and returns a handle for cancellation.
    ///
    /// The handle must be consumed via [`cancel`](Self::cancel) or
    /// [`free`](Self::free). Dropping it is a programming error.
    ///
    /// # Panics
    ///
    /// Panics if the backing slab is at capacity (bounded slabs only).
    /// This is a capacity planning error — size your wheel for peak load.
    pub fn schedule(&mut self, deadline: Instant, value: T) -> TimerHandle<T> {
        let deadline_ticks = self.instant_to_ticks(deadline);
        let entry = WheelEntry::new(deadline_ticks, value, 2);
        let slot = self.slab.alloc(entry);
        let ptr = slot.into_raw();
        self.insert_entry(ptr, deadline_ticks);
        self.len += 1;
        TimerHandle::new(ptr)
    }

    /// Schedules a fire-and-forget timer (no handle returned).
    ///
    /// The timer will fire during poll and the value will be collected.
    /// Cannot be cancelled.
    ///
    /// # Panics
    ///
    /// Panics if the backing slab is at capacity (bounded slabs only).
    /// This is a capacity planning error — size your wheel for peak load.
    pub fn schedule_forget(&mut self, deadline: Instant, value: T) {
        let deadline_ticks = self.instant_to_ticks(deadline);
        let entry = WheelEntry::new(deadline_ticks, value, 1);
        let slot = self.slab.alloc(entry);
        let ptr = slot.into_raw();
        self.insert_entry(ptr, deadline_ticks);
        self.len += 1;
    }
}

// =============================================================================
// Schedule — fallible (bounded slabs only)
// =============================================================================

impl<T: 'static, S: BoundedStore<Item = WheelEntry<T>>> TimerWheel<T, S> {
    /// Attempts to schedule a timer, returning a handle on success.
    ///
    /// Returns `Err(Full(value))` if the slab is at capacity. Use this
    /// when you need graceful error handling. For the common case where
    /// capacity exhaustion is fatal, use [`schedule`](Self::schedule).
    pub fn try_schedule(&mut self, deadline: Instant, value: T) -> Result<TimerHandle<T>, Full<T>> {
        let deadline_ticks = self.instant_to_ticks(deadline);
        let entry = WheelEntry::new(deadline_ticks, value, 2);
        match self.slab.try_alloc(entry) {
            Ok(slot) => {
                let ptr = slot.into_raw();
                self.insert_entry(ptr, deadline_ticks);
                self.len += 1;
                Ok(TimerHandle::new(ptr))
            }
            Err(full) => {
                // Extract the user's T from the WheelEntry wrapper
                let wheel_entry = full.into_inner();
                // SAFETY: entry was just constructed with Some(value) and never inserted
                // into the wheel — no other code has accessed it. Single-threaded.
                let value = unsafe { wheel_entry.take_value() }
                    .expect("entry was just constructed with Some(value)");
                Err(Full(value))
            }
        }
    }

    /// Attempts to schedule a fire-and-forget timer.
    ///
    /// Returns `Err(Full(value))` if the slab is at capacity. Use this
    /// when you need graceful error handling. For the common case where
    /// capacity exhaustion is fatal, use [`schedule_forget`](Self::schedule_forget).
    pub fn try_schedule_forget(&mut self, deadline: Instant, value: T) -> Result<(), Full<T>> {
        let deadline_ticks = self.instant_to_ticks(deadline);
        let entry = WheelEntry::new(deadline_ticks, value, 1);
        match self.slab.try_alloc(entry) {
            Ok(slot) => {
                let ptr = slot.into_raw();
                self.insert_entry(ptr, deadline_ticks);
                self.len += 1;
                Ok(())
            }
            Err(full) => {
                let wheel_entry = full.into_inner();
                // SAFETY: entry was just constructed with Some(value) and never inserted
                // into the wheel — no other code has accessed it. Single-threaded.
                let value = unsafe { wheel_entry.take_value() }
                    .expect("entry was just constructed with Some(value)");
                Err(Full(value))
            }
        }
    }
}

// =============================================================================
// Cancel / Free / Poll / Query — generic over any store
// =============================================================================

impl<T: 'static, S: SlabStore<Item = WheelEntry<T>>> TimerWheel<T, S> {
    /// Cancels a timer and returns its value.
    ///
    /// - If the timer is still active: unlinks from the wheel, extracts value,
    ///   frees the slab entry. Returns `Some(T)`.
    /// - If the timer already fired (zombie handle): frees the slab entry.
    ///   Returns `None`.
    ///
    /// Consumes the handle (no Drop runs).
    pub fn cancel(&mut self, handle: TimerHandle<T>) -> Option<T> {
        let ptr = handle.ptr;
        // Consume handle without running Drop
        mem::forget(handle);

        // SAFETY: handle guarantees ptr is valid and allocated from our slab.
        let entry = unsafe { entry_ref(ptr) };
        let refs = entry.refs();

        if refs == 2 {
            // Active timer with handle — unlink, extract, free
            // SAFETY: single-threaded access; entry is still in the wheel (refs==2),
            // so the value has not been taken by fire_entry.
            let value = unsafe { entry.take_value() };
            let cancelled_deadline = entry.deadline_ticks();
            self.remove_entry(ptr);
            self.len -= 1;
            if self.len == 0 {
                self.min_deadline.set(None);
            } else if let Some(cur) = self.min_deadline.get()
                && cancelled_deadline == cur
            {
                self.min_deadline.set(None);
            }
            // SAFETY: ptr was allocated from our slab via into_raw()
            self.slab.free(unsafe { Slot::from_raw(ptr) });
            value
        } else {
            // refs == 1 means the wheel already fired this (zombie).
            // The fire path decremented 2→1 and left the entry for us to free.
            debug_assert_eq!(refs, 1, "unexpected refcount {refs} in cancel");
            // SAFETY: ptr was allocated from our slab via into_raw()
            self.slab.free(unsafe { Slot::from_raw(ptr) });
            None
        }
    }

    /// Releases a timer handle without cancelling.
    ///
    /// - If the timer is still active: converts to fire-and-forget (refs 2→1).
    ///   Timer stays in the wheel and will fire normally during poll.
    /// - If the timer already fired (zombie): frees the slab entry (refs 1→0).
    ///
    /// Consumes the handle (no Drop runs).
    pub fn free(&mut self, handle: TimerHandle<T>) {
        let ptr = handle.ptr;
        mem::forget(handle);

        // SAFETY: handle guarantees ptr is valid
        let entry = unsafe { entry_ref(ptr) };
        let new_refs = entry.dec_refs();

        if new_refs == 0 {
            // Was a zombie (fired already, refs was 1) — free the entry
            // SAFETY: ptr was allocated from our slab via into_raw()
            self.slab.free(unsafe { Slot::from_raw(ptr) });
        }
        // new_refs == 1: timer is now fire-and-forget, stays in wheel
    }

    /// Reschedules an active timer to a new deadline.
    ///
    /// Moves the entry from its current slot to the correct slot for
    /// `new_deadline` without extracting or reconstructing the value.
    ///
    /// # Panics
    ///
    /// Panics if the timer has already fired (zombie handle). Only active
    /// timers (refs == 2) can be rescheduled.
    ///
    /// Consumes and returns a new handle (same entry, new position).
    pub fn reschedule(&mut self, handle: TimerHandle<T>, new_deadline: Instant) -> TimerHandle<T> {
        let ptr = handle.ptr;
        mem::forget(handle);

        // SAFETY: handle guarantees ptr is valid
        let entry = unsafe { entry_ref(ptr) };
        assert_eq!(entry.refs(), 2, "cannot reschedule a fired timer");

        let old_deadline = entry.deadline_ticks();

        // Remove from current position
        self.remove_entry(ptr);

        // Update deadline and reinsert
        let new_ticks = self.instant_to_ticks(new_deadline);
        entry.set_deadline_ticks(new_ticks);
        self.insert_entry(ptr, new_ticks);

        // Cache: if old deadline was the cached min and new is later,
        // we may have lost the min. insert_entry already handles
        // new < old (lowers cache), but can't detect old == cached
        // when moving later.
        if let Some(cur) = self.min_deadline.get()
            && old_deadline == cur
            && new_ticks > cur
        {
            self.min_deadline.set(None);
        }

        TimerHandle::new(ptr)
    }

    /// Fires all expired timers, collecting their values into `buf`.
    ///
    /// Returns the number of timers fired.
    pub fn poll(&mut self, now: Instant, buf: &mut Vec<T>) -> usize {
        self.poll_with_limit(now, usize::MAX, buf)
    }

    /// Fires expired timers up to `limit`, collecting values into `buf`.
    ///
    /// Resumable: if the limit is hit, the next call continues where this one
    /// left off (as long as `now` hasn't changed).
    ///
    /// Returns the number of timers fired in this call.
    pub fn poll_with_limit(&mut self, now: Instant, limit: usize, buf: &mut Vec<T>) -> usize {
        let now_ticks = self.instant_to_ticks(now);
        self.current_ticks = now_ticks; // MUST precede the early return — select_level reads it.

        // Fast path: if the cached global minimum is beyond now, nothing is due,
        // so skip the level walk entirely. The cache may be stale-low (a lower
        // bound), so this is conservative — it can miss the shortcut, never fire
        // late.
        if let Some(min) = self.min_deadline.get()
            && min > now_ticks
        {
            return 0;
        }

        let mut fired = 0;
        let mut mask = self.active_levels;

        while mask != 0 && fired < limit {
            let lvl_idx = mask.trailing_zeros() as usize;
            mask &= mask - 1; // clear lowest set bit
            fired += self.poll_level(lvl_idx, now_ticks, limit - fired, buf);
        }

        // Refresh the global-min cache from the (now-healed) per-slot minima.
        // poll_level heals every slot it walks, so this recomputes an accurate
        // minimum (> now when nothing is due). Without it the cache can stay
        // stale-low (<= now) after a cancel or a no-fire poll, permanently
        // defeating the early-exit above and making next_deadline() report a
        // past instant. Cheap now — one compare per active slot. (If a limit
        // truncated the poll, a walked-but-not-drained slot stays stale-low, so
        // the cache stays <= now and the next poll correctly re-enters.)
        self.min_deadline.set(self.walk_min_deadline());

        fired
    }

    /// Returns an `Instant` no later than when the next timer fires, or `None`
    /// if the wheel is empty.
    ///
    /// **Lower bound, not exact.** The per-slot minima are stale-low after a
    /// cancel/fire (they are not recomputed on removal — see the design), so the
    /// returned instant may be *earlier* than the true next deadline, never
    /// later. It is safe as a sleep/wake bound: you may wake early and find
    /// nothing due, but you can never miss a timer.
    ///
    /// O(1) on cache hit; otherwise ~one compare per active slot to recompute.
    pub fn next_deadline(&self) -> Option<Instant> {
        if let Some(ticks) = self.min_deadline.get() {
            return Some(self.ticks_to_instant(ticks));
        }
        if self.len == 0 {
            return None;
        }
        let min_ticks = self.walk_min_deadline();
        self.min_deadline.set(min_ticks);
        min_ticks.map(|t| self.ticks_to_instant(t))
    }

    /// Recomputes the wheel's minimum deadline from the per-slot minima —
    /// ~one compare per active slot, not one per entry.
    ///
    /// The per-slot minima may be stale-low (see `WheelSlot::min_deadline`), so
    /// the result is a **lower bound**: it may be earlier than the true minimum,
    /// never later. Callers (`next_deadline`, the poll early-exit) treat it
    /// conservatively — an under-estimate only ever costs extra work.
    #[cold]
    fn walk_min_deadline(&self) -> Option<u64> {
        // `any` (not `min_ticks != u64::MAX`) is the emptiness test: a real
        // far-future deadline can saturate to exactly u64::MAX in
        // `instant_to_ticks`, so the sentinel value is a legitimate minimum.
        let mut min_ticks = u64::MAX;
        let mut any = false;
        let mut lvl_mask = self.active_levels;
        while lvl_mask != 0 {
            let lvl_idx = lvl_mask.trailing_zeros() as usize;
            lvl_mask &= lvl_mask - 1;
            let level = &self.levels[lvl_idx];
            let mut slot_mask = level.active_slots();
            while slot_mask != 0 {
                let slot_idx = slot_mask.trailing_zeros() as usize;
                slot_mask &= slot_mask - 1;
                any = true;
                min_ticks = min_ticks.min(level.slot(slot_idx).min_deadline());
            }
        }
        any.then_some(min_ticks)
    }

    /// Test-only **exact** minimum deadline via a full entry walk (ignoring the
    /// per-slot minima) — the ground truth the lower-bound [`next_deadline`] is
    /// checked against.
    #[cfg(test)]
    fn next_deadline_uncached(&self) -> Option<Instant> {
        let mut min_ticks: Option<u64> = None;
        let mut lvl_mask = self.active_levels;
        while lvl_mask != 0 {
            let lvl_idx = lvl_mask.trailing_zeros() as usize;
            lvl_mask &= lvl_mask - 1;
            let level = &self.levels[lvl_idx];
            let mut slot_mask = level.active_slots();
            while slot_mask != 0 {
                let slot_idx = slot_mask.trailing_zeros() as usize;
                slot_mask &= slot_mask - 1;
                let slot = level.slot(slot_idx);
                let mut entry_ptr = slot.entry_head();
                while !entry_ptr.is_null() {
                    // SAFETY: entry_ptr is in this slot's DLL
                    let entry = unsafe { entry_ref(entry_ptr) };
                    let dt = entry.deadline_ticks();
                    min_ticks = Some(min_ticks.map_or(dt, |c| c.min(dt)));
                    entry_ptr = entry.next();
                }
            }
        }
        min_ticks.map(|t| self.ticks_to_instant(t))
    }

    /// Returns the number of timers currently in the wheel.
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns true if the wheel contains no timers.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    // =========================================================================
    // Internal: tick conversion
    // =========================================================================

    #[inline]
    fn instant_to_ticks(&self, instant: Instant) -> u64 {
        let dur = instant.saturating_duration_since(self.epoch);
        let nanos = dur.as_nanos().min(u64::MAX as u128) as u64;
        ((nanos as u128 * self.inv_tick_ns) >> 64) as u64
    }

    #[inline]
    fn ticks_to_instant(&self, ticks: u64) -> Instant {
        self.epoch + Duration::from_nanos(ticks.saturating_mul(self.tick_ns))
    }

    // =========================================================================
    // Internal: level selection
    // =========================================================================

    /// Selects the appropriate level for a deadline.
    ///
    /// Walks levels from finest to coarsest, picking the first level whose
    /// range can represent the delta. Clamps to the highest level if the
    /// deadline exceeds the wheel's total range.
    #[inline]
    fn select_level(&self, deadline_ticks: u64) -> usize {
        let delta = deadline_ticks.saturating_sub(self.current_ticks);

        for (i, level) in self.levels.iter().enumerate() {
            if delta < level.range() {
                return i;
            }
        }

        // Beyond max range — clamp to highest level
        self.num_levels - 1
    }

    // =========================================================================
    // Internal: entry insertion into a level's slot
    // =========================================================================

    /// Inserts an entry into the appropriate level and slot.
    ///
    /// Records the level and slot index on the entry so `remove_entry` can
    /// find it without recomputing (which would be unsound after time advances).
    #[inline]
    #[allow(clippy::needless_pass_by_ref_mut)]
    fn insert_entry(&mut self, entry_ptr: EntryPtr<T>, deadline_ticks: u64) {
        let lvl_idx = self.select_level(deadline_ticks);
        let slot_idx = self.levels[lvl_idx].slot_index(deadline_ticks);

        // Record location on the entry for O(1) lookup at cancel time.
        // SAFETY: entry_ptr is valid (just allocated)
        let entry = unsafe { entry_ref(entry_ptr) };
        entry.set_location(lvl_idx as u8, slot_idx as u16);

        // SAFETY: entry_ptr is valid (just allocated), not in any DLL yet
        unsafe { self.levels[lvl_idx].slot(slot_idx).push_entry(entry_ptr) };

        // Per-slot min: this entry may lower the slot's minimum. (Maintained here,
        // not in push_entry, so TimeoutList's shared slot pays nothing.)
        {
            let slot = self.levels[lvl_idx].slot(slot_idx);
            slot.set_min_deadline(slot.min_deadline().min(deadline_ticks));
        }

        // Activate slot and level (idempotent — OR is a no-op if already set)
        self.levels[lvl_idx].activate_slot(slot_idx);
        self.active_levels |= 1 << lvl_idx;

        // Cache: new entry may lower the minimum.
        // len is incremented by the caller AFTER insert_entry returns,
        // so self.len == 0 means the wheel was empty before this insert.
        match self.min_deadline.get() {
            None if self.len == 0 => {
                self.min_deadline.set(Some(deadline_ticks));
            }
            Some(cur) if deadline_ticks < cur => {
                self.min_deadline.set(Some(deadline_ticks));
            }
            _ => {}
        }
    }

    /// Removes an entry from its level's slot DLL.
    ///
    /// Reads the stored level and slot index from the entry (set at insertion
    /// time). Does NOT recompute from delta — that would be unsound after
    /// `current_ticks` advances.
    #[inline]
    #[allow(clippy::needless_pass_by_ref_mut)]
    fn remove_entry(&mut self, entry_ptr: EntryPtr<T>) {
        // SAFETY: entry_ptr is valid (caller guarantee)
        let entry = unsafe { entry_ref(entry_ptr) };

        let lvl_idx = entry.level() as usize;
        let slot_idx = entry.slot_idx() as usize;

        // SAFETY: entry_ptr is in this slot's DLL (invariant from insert_entry)
        unsafe { self.levels[lvl_idx].slot(slot_idx).remove_entry(entry_ptr) };

        if self.levels[lvl_idx].slot(slot_idx).is_empty() {
            // Drained: reset the slot min so an empty slot never reports a
            // stale-low deadline. A non-empty slot is left stale-low on purpose
            // (safe — see WheelSlot::min_deadline).
            self.levels[lvl_idx]
                .slot(slot_idx)
                .set_min_deadline(u64::MAX);
            self.levels[lvl_idx].deactivate_slot(slot_idx);
            if !self.levels[lvl_idx].is_active() {
                self.active_levels &= !(1 << lvl_idx);
            }
        }
    }

    // =========================================================================
    // Internal: fire an entry
    // =========================================================================

    /// Fires a single entry: extracts value, decrements refcount, possibly frees.
    ///
    /// Returns `Some(T)` if the value was still present (not already cancelled).
    #[inline]
    fn fire_entry(&mut self, entry_ptr: EntryPtr<T>) -> Option<T> {
        // SAFETY: entry_ptr is valid (we're walking the DLL)
        let entry = unsafe { entry_ref(entry_ptr) };

        let fired_deadline = entry.deadline_ticks();

        // Extract value
        // SAFETY: single-threaded
        let value = unsafe { entry.take_value() };

        let new_refs = entry.dec_refs();
        if new_refs == 0 {
            // Fire-and-forget (was refs=1) — free the slab entry immediately
            // SAFETY: entry_ptr was allocated from our slab via into_raw()
            self.slab.free(unsafe { Slot::from_raw(entry_ptr) });
        }
        // new_refs == 1: handle exists (was refs=2), entry becomes zombie.
        // Handle holder will free via cancel() or free().

        self.len -= 1;

        if self.len == 0 {
            self.min_deadline.set(None);
        } else if let Some(cur) = self.min_deadline.get()
            && fired_deadline == cur
        {
            self.min_deadline.set(None);
        }

        value
    }

    // =========================================================================
    // Internal: poll a single level
    // =========================================================================

    /// Polls a single level for expired entries up to `limit`.
    ///
    fn poll_level(
        &mut self,
        lvl_idx: usize,
        now_ticks: u64,
        limit: usize,
        buf: &mut Vec<T>,
    ) -> usize {
        let mut fired = 0;
        let mut mask = self.levels[lvl_idx].active_slots();

        while mask != 0 && fired < limit {
            let slot_idx = mask.trailing_zeros() as usize;
            mask &= mask - 1;

            let slot_ptr = self.levels[lvl_idx].slot(slot_idx) as *const crate::level::WheelSlot<T>;
            // SAFETY: slot_ptr points into self.levels[lvl_idx].slots
            // (Box<[WheelSlot<T>]>), a stable heap allocation never reallocated
            // during poll. fire_entry and insert_entry mutate self.slab, self.len,
            // self.active_levels, self.min_deadline, and *other* levels' slots —
            // cascade relocates only to strictly finer levels (< lvl_idx), never
            // this slot — so this slot's backing memory is untouched and `slot`
            // stays valid across the loop.
            let slot = unsafe { &*slot_ptr };

            // Slot-skip: if the slot's minimum deadline is beyond now, nothing
            // in it is due — do not touch a single entry. Stale-low is safe: it
            // only costs an unnecessary walk (handled below), never a skip.
            if slot.min_deadline() > now_ticks {
                continue;
            }

            let mut new_min = u64::MAX; // min over entries that stay in this slot
            let mut entry_ptr = slot.entry_head();

            while !entry_ptr.is_null() && fired < limit {
                // SAFETY: entry_ptr is in this slot's DLL
                let entry = unsafe { entry_ref(entry_ptr) };
                let next_entry = entry.next(); // captured before any unlink below
                let dt = entry.deadline_ticks();

                if dt <= now_ticks {
                    // Due — fire it.
                    // SAFETY: entry_ptr is in this slot's DLL (from entry_head,
                    // walked via next pointers within the same slot).
                    unsafe { slot.remove_entry(entry_ptr) };
                    if let Some(value) = self.fire_entry(entry_ptr) {
                        buf.push(value);
                    }
                    fired += 1;
                } else if self.select_level(dt) < lvl_idx {
                    // Not due, and it now belongs at a strictly finer level:
                    // cascade it down instead of re-walking it every poll until
                    // this slot's span passes. The target (< lvl_idx) is never this
                    // slot, so the walk terminates and the entry is not re-processed
                    // this poll (finer levels are polled first). current_ticks ==
                    // now_ticks (set in poll_with_limit before this loop), so
                    // insert_entry selects the correct finer level.
                    // SAFETY: entry_ptr is in this slot's DLL.
                    unsafe { slot.remove_entry(entry_ptr) };
                    self.insert_entry(entry_ptr, dt);
                } else {
                    // Not due, and still belongs at this level. This happens when a
                    // far entry shares the slot via the modular index: deadlines a
                    // full level-range apart map to the same slot, so a slot made
                    // due by its earliest entry can also hold entries that are not
                    // yet within a finer level's reach. Leave it in place (it fires
                    // or cascades on a later poll) and track it as the slot's
                    // surviving minimum.
                    new_min = new_min.min(dt);
                }

                entry_ptr = next_entry;
            }

            // If we walked the whole slot, its minimum is exactly the min over the
            // entries that stayed (u64::MAX — the empty sentinel — when the slot
            // drained via fires + cascades). A limit-truncated walk (entry_ptr
            // non-null) leaves the min stale-low; the next poll re-walks and heals.
            if entry_ptr.is_null() {
                slot.set_min_deadline(new_min);
            }

            if slot.is_empty() {
                self.levels[lvl_idx].deactivate_slot(slot_idx);
            }
        }

        // Deactivate level if all slots drained
        if !self.levels[lvl_idx].is_active() {
            self.active_levels &= !(1 << lvl_idx);
        }

        fired
    }
}

// =============================================================================
// Drop
// =============================================================================

impl<T: 'static, S: SlabStore<Item = WheelEntry<T>>> Drop for TimerWheel<T, S> {
    fn drop(&mut self) {
        // Walk active levels and slots via bitmasks, free every entry.
        let mut lvl_mask = self.active_levels;
        while lvl_mask != 0 {
            let lvl_idx = lvl_mask.trailing_zeros() as usize;
            lvl_mask &= lvl_mask - 1;

            let level = &self.levels[lvl_idx];
            let mut slot_mask = level.active_slots();
            while slot_mask != 0 {
                let slot_idx = slot_mask.trailing_zeros() as usize;
                slot_mask &= slot_mask - 1;

                let slot = level.slot(slot_idx);
                let mut entry_ptr = slot.entry_head();
                while !entry_ptr.is_null() {
                    // SAFETY: entry_ptr is in this slot's DLL
                    let entry = unsafe { entry_ref(entry_ptr) };
                    let next_entry = entry.next();

                    // SAFETY: entry_ptr was allocated from our slab via into_raw()
                    self.slab.free(unsafe { Slot::from_raw(entry_ptr) });

                    entry_ptr = next_entry;
                }
            }
        }
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{Duration, Instant};

    fn ms(millis: u64) -> Duration {
        Duration::from_millis(millis)
    }

    // -------------------------------------------------------------------------
    // Thread safety
    // -------------------------------------------------------------------------

    fn assert_send<T: Send>() {}

    #[test]
    fn wheel_is_send() {
        assert_send::<Wheel<u64>>();
        assert_send::<BoundedWheel<u64>>();
    }

    // -------------------------------------------------------------------------
    // Construction
    // -------------------------------------------------------------------------

    #[test]
    fn default_config() {
        let now = Instant::now();
        let wheel: Wheel<u64> = Wheel::unbounded(1024, now);
        assert!(wheel.is_empty());
        assert_eq!(wheel.len(), 0);
    }

    #[test]
    fn bounded_construction() {
        let now = Instant::now();
        let wheel: BoundedWheel<u64> = BoundedWheel::bounded(128, now);
        assert!(wheel.is_empty());
    }

    #[test]
    #[should_panic(expected = "slots_per_level must be a power of 2")]
    fn invalid_config_non_power_of_two() {
        let now = Instant::now();
        WheelBuilder::default()
            .slots_per_level(65)
            .unbounded(1024)
            .build::<u64>(now);
    }

    // -------------------------------------------------------------------------
    // Schedule + Cancel
    // -------------------------------------------------------------------------

    #[test]
    fn schedule_and_cancel() {
        let now = Instant::now();
        let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

        let h = wheel.schedule(now + ms(50), 42);
        assert_eq!(wheel.len(), 1);

        let val = wheel.cancel(h);
        assert_eq!(val, Some(42));
        assert_eq!(wheel.len(), 0);
    }

    #[test]
    fn schedule_forget_fires() {
        let now = Instant::now();
        let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

        wheel.schedule_forget(now + ms(10), 99);
        assert_eq!(wheel.len(), 1);

        let mut buf = Vec::new();
        let fired = wheel.poll(now + ms(20), &mut buf);
        assert_eq!(fired, 1);
        assert_eq!(buf, vec![99]);
        assert_eq!(wheel.len(), 0);
    }

    #[test]
    fn cancel_after_fire_returns_none() {
        let now = Instant::now();
        let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

        let h = wheel.schedule(now + ms(10), 42);

        let mut buf = Vec::new();
        wheel.poll(now + ms(20), &mut buf);
        assert_eq!(buf, vec![42]);

        // Handle is now a zombie
        let val = wheel.cancel(h);
        assert_eq!(val, None);
    }

    #[test]
    fn free_active_timer_becomes_fire_and_forget() {
        let now = Instant::now();
        let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

        let h = wheel.schedule(now + ms(10), 42);
        wheel.free(h); // releases handle, timer stays
        assert_eq!(wheel.len(), 1);

        let mut buf = Vec::new();
        wheel.poll(now + ms(20), &mut buf);
        assert_eq!(buf, vec![42]);
        assert_eq!(wheel.len(), 0);
    }

    #[test]
    fn free_zombie_handle() {
        let now = Instant::now();
        let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

        let h = wheel.schedule(now + ms(10), 42);

        let mut buf = Vec::new();
        wheel.poll(now + ms(20), &mut buf);

        // Handle is zombie, free should clean up
        wheel.free(h);
    }

    // -------------------------------------------------------------------------
    // Bounded wheel
    // -------------------------------------------------------------------------

    #[test]
    fn bounded_full() {
        let now = Instant::now();
        let mut wheel: BoundedWheel<u64> = BoundedWheel::bounded(2, now);

        let h1 = wheel.try_schedule(now + ms(10), 1).unwrap();
        let h2 = wheel.try_schedule(now + ms(20), 2).unwrap();

        let err = wheel.try_schedule(now + ms(30), 3);
        assert!(err.is_err());
        let recovered = err.unwrap_err().into_inner();
        assert_eq!(recovered, 3);

        // Cancel one, should have room
        wheel.cancel(h1);
        let h3 = wheel.try_schedule(now + ms(30), 3).unwrap();

        // Clean up handles
        wheel.free(h2);
        wheel.free(h3);
    }

    #[test]
    fn bounded_schedule_forget_full() {
        let now = Instant::now();
        let mut wheel: BoundedWheel<u64> = BoundedWheel::bounded(1, now);

        wheel.try_schedule_forget(now + ms(10), 1).unwrap();
        let err = wheel.try_schedule_forget(now + ms(20), 2);
        assert!(err.is_err());
    }

    // -------------------------------------------------------------------------
    // Poll
    // -------------------------------------------------------------------------

    #[test]
    fn poll_respects_deadline() {
        let now = Instant::now();
        let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

        wheel.schedule_forget(now + ms(10), 1);
        wheel.schedule_forget(now + ms(50), 2);
        wheel.schedule_forget(now + ms(100), 3);

        let mut buf = Vec::new();

        // At 20ms: only timer 1 should fire
        let fired = wheel.poll(now + ms(20), &mut buf);
        assert_eq!(fired, 1);
        assert_eq!(buf, vec![1]);
        assert_eq!(wheel.len(), 2);

        // At 60ms: timer 2 fires
        buf.clear();
        let fired = wheel.poll(now + ms(60), &mut buf);
        assert_eq!(fired, 1);
        assert_eq!(buf, vec![2]);

        // At 200ms: timer 3 fires
        buf.clear();
        let fired = wheel.poll(now + ms(200), &mut buf);
        assert_eq!(fired, 1);
        assert_eq!(buf, vec![3]);

        assert!(wheel.is_empty());
    }

    #[test]
    fn poll_with_limit() {
        let now = Instant::now();
        let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

        for i in 0..10 {
            wheel.schedule_forget(now + ms(1), i);
        }

        let mut buf = Vec::new();

        // Fire 3 at a time
        let fired = wheel.poll_with_limit(now + ms(5), 3, &mut buf);
        assert_eq!(fired, 3);
        assert_eq!(wheel.len(), 7);

        let fired = wheel.poll_with_limit(now + ms(5), 3, &mut buf);
        assert_eq!(fired, 3);
        assert_eq!(wheel.len(), 4);

        // Fire remaining
        let fired = wheel.poll(now + ms(5), &mut buf);
        assert_eq!(fired, 4);
        assert!(wheel.is_empty());
        assert_eq!(buf.len(), 10);
    }

    // -------------------------------------------------------------------------
    // Multi-level
    // -------------------------------------------------------------------------

    #[test]
    fn timers_across_levels() {
        let now = Instant::now();
        let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

        // Level 0: 0-63ms
        wheel.schedule_forget(now + ms(5), 0);
        // Level 1: 64-511ms
        wheel.schedule_forget(now + ms(200), 1);
        // Level 2: 512-4095ms
        wheel.schedule_forget(now + ms(1000), 2);

        let mut buf = Vec::new();

        wheel.poll(now + ms(10), &mut buf);
        assert_eq!(buf, vec![0]);

        buf.clear();
        wheel.poll(now + ms(250), &mut buf);
        assert_eq!(buf, vec![1]);

        buf.clear();
        wheel.poll(now + ms(1500), &mut buf);
        assert_eq!(buf, vec![2]);

        assert!(wheel.is_empty());
    }

    // -------------------------------------------------------------------------
    // next_deadline
    // -------------------------------------------------------------------------

    #[test]
    fn next_deadline_empty() {
        let now = Instant::now();
        let wheel: Wheel<u64> = Wheel::unbounded(1024, now);
        assert!(wheel.next_deadline().is_none());
    }

    #[test]
    fn next_deadline_returns_earliest() {
        let now = Instant::now();
        let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

        wheel.schedule_forget(now + ms(100), 1);
        wheel.schedule_forget(now + ms(50), 2);
        wheel.schedule_forget(now + ms(200), 3);

        let next = wheel.next_deadline().unwrap();
        // Should be close to now + 50ms (within tick granularity)
        let delta = next.duration_since(now);
        assert!(delta >= ms(49) && delta <= ms(51));
    }

    #[test]
    fn next_deadline_cache_invalidates_on_cancel() {
        let now = Instant::now();
        let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

        let h1 = wheel.schedule(now + ms(50), 1);
        wheel.schedule_forget(now + ms(100), 2);
        wheel.schedule_forget(now + ms(200), 3);

        // Cached at 50ms
        let d1 = wheel.next_deadline().unwrap();
        assert!(d1.duration_since(now) >= ms(49) && d1.duration_since(now) <= ms(51));

        // Cancel the earliest — cache invalidated, should return ~100ms
        wheel.cancel(h1);
        let d2 = wheel.next_deadline().unwrap();
        assert!(d2.duration_since(now) >= ms(99) && d2.duration_since(now) <= ms(101));
    }

    #[test]
    fn next_deadline_cache_invalidates_on_fire() {
        let now = Instant::now();
        let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

        wheel.schedule_forget(now + ms(50), 1);
        wheel.schedule_forget(now + ms(100), 2);
        wheel.schedule_forget(now + ms(200), 3);

        // Prime cache
        let _ = wheel.next_deadline();

        // Fire earliest via poll
        let mut buf = Vec::new();
        wheel.poll(now + ms(60), &mut buf);
        assert_eq!(buf, vec![1]);

        // Cache invalidated, should return ~100ms
        let d = wheel.next_deadline().unwrap();
        assert!(d.duration_since(now) >= ms(99) && d.duration_since(now) <= ms(101));
    }

    #[test]
    fn next_deadline_cache_updates_on_insert() {
        let now = Instant::now();
        let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

        wheel.schedule_forget(now + ms(100), 1);
        let d1 = wheel.next_deadline().unwrap();
        assert!(d1.duration_since(now) >= ms(99) && d1.duration_since(now) <= ms(101));

        // Insert an earlier timer — cache should update
        wheel.schedule_forget(now + ms(30), 2);
        let d2 = wheel.next_deadline().unwrap();
        assert!(d2.duration_since(now) >= ms(29) && d2.duration_since(now) <= ms(31));
    }

    #[test]
    fn next_deadline_after_reschedule_later() {
        let now = Instant::now();
        let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

        let h_a = wheel.schedule(now + ms(50), 1);
        wheel.schedule_forget(now + ms(100), 2);

        let d1 = wheel.next_deadline().unwrap();
        assert!(d1.duration_since(now) >= ms(49) && d1.duration_since(now) <= ms(51));

        // Reschedule A later — B becomes earliest
        let h_a = wheel.reschedule(h_a, now + ms(200));
        let d2 = wheel.next_deadline().unwrap();
        assert!(d2.duration_since(now) >= ms(99) && d2.duration_since(now) <= ms(101));
        mem::forget(h_a);
    }

    #[test]
    fn next_deadline_after_reschedule_earlier() {
        let now = Instant::now();
        let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

        let h_a = wheel.schedule(now + ms(100), 1);
        wheel.schedule_forget(now + ms(50), 2);

        let d1 = wheel.next_deadline().unwrap();
        assert!(d1.duration_since(now) >= ms(49) && d1.duration_since(now) <= ms(51));

        // Reschedule A earlier — A becomes new earliest
        let h_a = wheel.reschedule(h_a, now + ms(25));
        let d2 = wheel.next_deadline().unwrap();
        assert!(d2.duration_since(now) >= ms(24) && d2.duration_since(now) <= ms(26));
        mem::forget(h_a);
    }

    #[test]
    fn next_deadline_repeated_calls_stable() {
        let now = Instant::now();
        let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

        wheel.schedule_forget(now + ms(50), 1);
        wheel.schedule_forget(now + ms(100), 2);
        wheel.schedule_forget(now + ms(200), 3);

        let d1 = wheel.next_deadline();
        let d2 = wheel.next_deadline();
        let d3 = wheel.next_deadline();
        assert_eq!(d1, d2);
        assert_eq!(d2, d3);
    }

    // -------------------------------------------------------------------------
    // Reciprocal precision
    // -------------------------------------------------------------------------

    #[test]
    fn reciprocal_instant_to_ticks_precision() {
        // Reciprocal multiply is at most 1 tick low vs true integer division.
        // Verify across multiple tick_ns values and multiples.
        let now = Instant::now();

        for &tick_ns in &[1_000_000u64, 1_000, 100, 999_999, 7_500_000] {
            let wheel: Wheel<u64> = WheelBuilder::default()
                .tick_duration(Duration::from_nanos(tick_ns))
                .unbounded(64)
                .build(now);

            for n in 0..500u64 {
                let nanos = n * tick_ns;
                let instant = now + Duration::from_nanos(nanos);
                let got = wheel.instant_to_ticks(instant);
                let exact = nanos / tick_ns;
                let diff = exact as i64 - got as i64;
                assert!(
                    diff >= 0 && diff <= 1,
                    "tick_ns={tick_ns}, n={n}: exact={exact}, got={got}, diff={diff}",
                );
            }
        }
    }

    // -------------------------------------------------------------------------
    // Deadline in the past
    // -------------------------------------------------------------------------

    #[test]
    fn deadline_in_the_past_fires_immediately() {
        let now = Instant::now();
        let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

        // Schedule at epoch (which is "now" at construction)
        wheel.schedule_forget(now, 42);

        let mut buf = Vec::new();
        let fired = wheel.poll(now + ms(1), &mut buf);
        assert_eq!(fired, 1);
        assert_eq!(buf, vec![42]);
    }

    // -------------------------------------------------------------------------
    // Deadline beyond max range — clamped
    // -------------------------------------------------------------------------

    #[test]
    fn deadline_beyond_max_range_clamped() {
        let now = Instant::now();
        let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

        // Way in the future — should clamp to highest level
        let h = wheel.schedule(now + Duration::from_secs(100_000), 99);
        assert_eq!(wheel.len(), 1);

        // Won't fire at any reasonable time but will fire when enough ticks pass
        let mut buf = Vec::new();
        wheel.poll(now + Duration::from_secs(100_001), &mut buf);
        assert_eq!(buf, vec![99]);

        // Note: handle was already consumed by the poll (fire-and-forget path won't
        // apply since refs=2). Actually the handle still exists. Let's clean up.
        // The timer already fired, so cancel returns None.
        // Actually buf got the value, which means it fired. But handle still needs cleanup.
        // We already pushed the value so we need to handle the zombie.
        // Wait — we used schedule (refs=2), poll fired it (refs 2→1 zombie), handle `h` exists.
        // Actually we consumed it with the poll — no we didn't, we still have `h`.

        // h is a zombie handle now
        let val = wheel.cancel(h);
        assert_eq!(val, None);
    }

    // -------------------------------------------------------------------------
    // Drop
    // -------------------------------------------------------------------------

    #[test]
    fn drop_cleans_up_active_entries() {
        let now = Instant::now();
        let mut wheel: Wheel<String> = Wheel::unbounded(1024, now);

        for i in 0..100 {
            wheel.schedule_forget(now + ms(i * 10), format!("timer-{i}"));
        }

        assert_eq!(wheel.len(), 100);
        // Drop should free all entries without leaking
        drop(wheel);
    }

    #[test]
    fn drop_with_outstanding_handles() {
        let now = Instant::now();
        let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

        // Schedule but DON'T cancel — just free the handles
        let h1 = wheel.schedule(now + ms(10), 1);
        let h2 = wheel.schedule(now + ms(20), 2);

        // Free the handles (convert to fire-and-forget) so they don't debug_assert
        wheel.free(h1);
        wheel.free(h2);

        // Drop the wheel — should clean up the entries
        drop(wheel);
    }

    // -------------------------------------------------------------------------
    // Level selection
    // -------------------------------------------------------------------------

    #[test]
    fn level_selection_boundaries() {
        let now = Instant::now();
        let wheel: Wheel<u64> = Wheel::unbounded(1024, now);

        // Level 0: delta < 64
        assert_eq!(wheel.select_level(0), 0);
        assert_eq!(wheel.select_level(63), 0);

        // Level 1: 64 <= delta < 512
        assert_eq!(wheel.select_level(64), 1);
        assert_eq!(wheel.select_level(511), 1);

        // Level 2: 512 <= delta < 4096
        assert_eq!(wheel.select_level(512), 2);
    }

    // -------------------------------------------------------------------------
    // Bug fix validation: cancel after time advance
    // -------------------------------------------------------------------------

    #[test]
    fn cancel_after_time_advance() {
        // The critical bug: schedule at T+500ms (level 2, delta=500 ticks),
        // poll at T+400ms (no fire, but current_ticks advances to 400),
        // cancel at T+400ms. Old code would recompute delta = 500-400 = 100
        // → level 1. But the entry is in level 2. Stored location fixes this.
        let now = Instant::now();
        let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

        let h = wheel.schedule(now + ms(500), 42);
        assert_eq!(wheel.len(), 1);

        // Advance time — timer doesn't fire (deadline is 500ms)
        let mut buf = Vec::new();
        let fired = wheel.poll(now + ms(400), &mut buf);
        assert_eq!(fired, 0);
        assert!(buf.is_empty());

        // Cancel after time advance — must find the entry in the correct slot
        let val = wheel.cancel(h);
        assert_eq!(val, Some(42));
        assert_eq!(wheel.len(), 0);
    }

    // -------------------------------------------------------------------------
    // Per-slot min: stale-low safety
    // -------------------------------------------------------------------------

    #[test]
    fn slot_min_stale_low_after_cancel_still_fires() {
        // Cancelling the earliest entry in a non-empty slot leaves that slot's
        // cached min stale-low (the per-slot minima are not recomputed on
        // remove). Poll must still fire the SURVIVORS at the right times — never
        // skip a due entry, never fire an early one.
        let now = Instant::now();
        let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

        // 3000 / 3001 / 3002 ms all land in the same level-2 slot.
        let h0 = wheel.schedule(now + ms(3000), 0);
        wheel.schedule_forget(now + ms(3001), 1);
        wheel.schedule_forget(now + ms(3002), 2);

        // Cancel the earliest — the slot min now points at 3000 (gone): stale-low.
        assert_eq!(wheel.cancel(h0), Some(0));

        let mut buf = Vec::new();
        assert_eq!(wheel.poll(now + ms(3000), &mut buf), 0, "nothing due yet");
        assert!(buf.is_empty());

        let fired = wheel.poll(now + ms(3002), &mut buf);
        assert_eq!(fired, 2, "both survivors fire once due");
        buf.sort_unstable();
        assert_eq!(buf, vec![1, 2]);
    }

    #[test]
    fn slot_min_resets_on_drain_and_reinsert() {
        // A drained slot resets its min to u64::MAX; a later insert must set the
        // min fresh, not inherit a stale value.
        let now = Instant::now();
        let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

        wheel.schedule_forget(now + ms(3000), 0);
        let mut buf = Vec::new();
        assert_eq!(wheel.poll(now + ms(3000), &mut buf), 1);
        assert!(wheel.is_empty());
        assert!(wheel.next_deadline().is_none());

        // Re-insert (likely into the same drained slot).
        wheel.schedule_forget(now + ms(3000), 1);
        let nd = wheel.next_deadline().expect("non-empty");
        assert!(nd <= now + ms(3000)); // lower bound — never later than the true deadline
        buf.clear();
        assert_eq!(wheel.poll(now + ms(2999), &mut buf), 0);
        assert_eq!(wheel.poll(now + ms(3000), &mut buf), 1);
    }

    #[test]
    fn poll_refreshes_stale_low_cache() {
        // Cancelling the slot-min entry leaves the slot min — and, once read, the
        // global cache — stale-low, pointing at the cancelled deadline. A poll
        // that finds nothing due must refresh the cache off that stale value;
        // otherwise it stays <= now forever, defeating the early-exit and making
        // next_deadline() report a past instant.
        let now = Instant::now();
        let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

        // 3000 / 3002 ms share a slot. Cancel the earlier one.
        let h0 = wheel.schedule(now + ms(3000), 0);
        wheel.schedule_forget(now + ms(3002), 1);
        assert_eq!(wheel.cancel(h0), Some(0));

        // Populate the (now stale-low) cache: it points at the cancelled 3000.
        let stale = wheel.next_deadline().expect("non-empty");
        assert!(stale <= now + ms(3000));

        // Poll past 3000 but before 3002 — nothing fires; the slot heals to 3002
        // and the cache is refreshed at the end of the poll.
        let mut buf = Vec::new();
        assert_eq!(wheel.poll(now + ms(3001), &mut buf), 0);

        // Regression: without the poll-end refresh this would still be the
        // cancelled ~3000 (in the past). It must now reflect the survivor —
        // compared against the captured stale value so tick-rounding is irrelevant.
        let refreshed = wheel.next_deadline().expect("non-empty");
        assert!(
            refreshed > stale,
            "cache must refresh past the stale-low value after a no-fire poll",
        );
    }

    // -------------------------------------------------------------------------
    // Same-slot entries
    // -------------------------------------------------------------------------

    #[test]
    fn multiple_entries_same_slot() {
        let now = Instant::now();
        let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

        // All 5 timers at the same deadline → same slot
        let mut handles = Vec::new();
        for i in 0..5 {
            handles.push(wheel.schedule(now + ms(10), i));
        }
        assert_eq!(wheel.len(), 5);

        // Cancel the middle ones
        let v2 = wheel.cancel(handles.remove(2));
        assert_eq!(v2, Some(2));
        let v0 = wheel.cancel(handles.remove(0));
        assert_eq!(v0, Some(0));
        assert_eq!(wheel.len(), 3);

        // Poll — remaining 3 should fire
        let mut buf = Vec::new();
        let fired = wheel.poll(now + ms(20), &mut buf);
        assert_eq!(fired, 3);

        // Clean up zombie handles
        for h in handles {
            let val = wheel.cancel(h);
            assert_eq!(val, None); // already fired
        }
    }

    // -------------------------------------------------------------------------
    // Level boundary
    // -------------------------------------------------------------------------

    #[test]
    fn entry_at_level_boundary() {
        // Default config: level 0 range = 64 ticks (64ms).
        // A deadline at exactly tick 64 should go to level 1, not level 0.
        let now = Instant::now();
        let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

        let h = wheel.schedule(now + ms(64), 99);
        assert_eq!(wheel.len(), 1);

        // Should NOT fire at 63ms
        let mut buf = Vec::new();
        let fired = wheel.poll(now + ms(63), &mut buf);
        assert_eq!(fired, 0);

        // Should fire at 64ms
        let fired = wheel.poll(now + ms(65), &mut buf);
        assert_eq!(fired, 1);
        assert_eq!(buf, vec![99]);

        // Clean up zombie handle
        wheel.cancel(h);
    }

    // -------------------------------------------------------------------------
    // Bookmark/resumption with mixed expiry
    // -------------------------------------------------------------------------

    #[test]
    fn poll_with_limit_mixed_expiry() {
        let now = Instant::now();
        let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

        // 3 expired at poll time, 2 not
        wheel.schedule_forget(now + ms(5), 1);
        wheel.schedule_forget(now + ms(5), 2);
        wheel.schedule_forget(now + ms(5), 3);
        wheel.schedule_forget(now + ms(500), 4); // not expired
        wheel.schedule_forget(now + ms(500), 5); // not expired
        assert_eq!(wheel.len(), 5);

        let mut buf = Vec::new();

        // Fire 2 of the 3 expired
        let fired = wheel.poll_with_limit(now + ms(10), 2, &mut buf);
        assert_eq!(fired, 2);
        assert_eq!(wheel.len(), 3);

        // Fire remaining expired (1 more)
        let fired = wheel.poll_with_limit(now + ms(10), 5, &mut buf);
        assert_eq!(fired, 1);
        assert_eq!(wheel.len(), 2);

        // The 2 unexpired should still be there
        assert_eq!(buf.len(), 3);
    }

    // -------------------------------------------------------------------------
    // Re-add after drain
    // -------------------------------------------------------------------------

    #[test]
    fn reuse_after_full_drain() {
        let now = Instant::now();
        let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

        // Round 1: schedule and drain
        for i in 0..10 {
            wheel.schedule_forget(now + ms(1), i);
        }
        let mut buf = Vec::new();
        wheel.poll(now + ms(5), &mut buf);
        assert_eq!(buf.len(), 10);
        assert!(wheel.is_empty());

        // Round 2: schedule and drain again — wheel must work normally
        buf.clear();
        for i in 10..20 {
            wheel.schedule_forget(now + ms(100), i);
        }
        assert_eq!(wheel.len(), 10);

        wheel.poll(now + ms(200), &mut buf);
        assert_eq!(buf.len(), 10);
        assert!(wheel.is_empty());
    }

    // -------------------------------------------------------------------------
    // All levels active simultaneously
    // -------------------------------------------------------------------------

    #[test]
    fn all_levels_active() {
        let now = Instant::now();
        let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

        // Schedule one timer per level with increasing distances.
        // Level 0: <64ms, Level 1: 64-511ms, Level 2: 512-4095ms, etc.
        let distances = [10, 100, 1000, 5000, 40_000, 300_000, 3_000_000];
        let mut handles: Vec<TimerHandle<u64>> = Vec::new();
        for (i, &d) in distances.iter().enumerate() {
            handles.push(wheel.schedule(now + ms(d), i as u64));
        }
        assert_eq!(wheel.len(), 7);

        // Cancel in a shuffled order: 4, 1, 6, 0, 3, 5, 2
        let order = [4, 1, 6, 0, 3, 5, 2];
        // Take ownership by swapping with dummies — actually we need to
        // cancel by index. Let's use Option to track.
        let mut opt_handles: Vec<Option<TimerHandle<u64>>> =
            handles.into_iter().map(Some).collect();

        for &idx in &order {
            let h = opt_handles[idx].take().unwrap();
            let val = wheel.cancel(h);
            assert_eq!(val, Some(idx as u64));
        }
        assert!(wheel.is_empty());
    }

    // -------------------------------------------------------------------------
    // Poll values match
    // -------------------------------------------------------------------------

    #[test]
    fn poll_values_match() {
        let now = Instant::now();
        let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

        let expected: Vec<u64> = (100..110).collect();
        for &v in &expected {
            wheel.schedule_forget(now + ms(5), v);
        }

        let mut buf = Vec::new();
        wheel.poll(now + ms(10), &mut buf);

        buf.sort_unstable();
        assert_eq!(buf, expected);
    }

    // -------------------------------------------------------------------------
    // Reschedule
    // -------------------------------------------------------------------------

    #[test]
    fn reschedule_moves_deadline() {
        let now = Instant::now();
        let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

        let h = wheel.schedule(now + ms(100), 42);
        assert_eq!(wheel.len(), 1);

        // Reschedule to earlier
        let h = wheel.reschedule(h, now + ms(50));
        assert_eq!(wheel.len(), 1);

        // Should NOT fire at 40ms
        let mut buf = Vec::new();
        let fired = wheel.poll(now + ms(40), &mut buf);
        assert_eq!(fired, 0);

        // Should fire at 50ms
        let fired = wheel.poll(now + ms(55), &mut buf);
        assert_eq!(fired, 1);
        assert_eq!(buf, vec![42]);

        // Clean up zombie
        wheel.cancel(h);
    }

    #[test]
    fn reschedule_to_later() {
        let now = Instant::now();
        let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

        let h = wheel.schedule(now + ms(50), 7);

        // Reschedule to later
        let h = wheel.reschedule(h, now + ms(200));

        // Should NOT fire at original deadline
        let mut buf = Vec::new();
        let fired = wheel.poll(now + ms(60), &mut buf);
        assert_eq!(fired, 0);

        // Should fire at new deadline
        let fired = wheel.poll(now + ms(210), &mut buf);
        assert_eq!(fired, 1);
        assert_eq!(buf, vec![7]);

        wheel.cancel(h);
    }

    #[test]
    #[should_panic(expected = "cannot reschedule a fired timer")]
    fn reschedule_panics_on_zombie() {
        let now = Instant::now();
        let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

        let h = wheel.schedule(now + ms(10), 42);

        let mut buf = Vec::new();
        wheel.poll(now + ms(20), &mut buf);

        // h is now a zombie — reschedule should panic
        let _h = wheel.reschedule(h, now + ms(100));
    }

    // -------------------------------------------------------------------------
    // Non-default builder configurations (L13)
    // -------------------------------------------------------------------------

    #[test]
    fn custom_slots_per_level() {
        let now = Instant::now();
        // 32 slots/level instead of default 64
        let mut wheel: Wheel<u64> = WheelBuilder::default()
            .slots_per_level(32)
            .unbounded(256)
            .build(now);

        // Level 0 range = 32 ticks (32ms with 1ms tick)
        // Deadline at 20ms should go to level 0
        let h1 = wheel.schedule(now + ms(20), 1);
        // Deadline at 40ms should go to level 1 (>= 32 ticks)
        let h2 = wheel.schedule(now + ms(40), 2);

        let mut buf = Vec::new();
        wheel.poll(now + ms(25), &mut buf);
        assert_eq!(buf, vec![1]);

        buf.clear();
        wheel.poll(now + ms(50), &mut buf);
        assert_eq!(buf, vec![2]);

        wheel.cancel(h1);
        wheel.cancel(h2);
    }

    #[test]
    fn custom_clk_shift() {
        let now = Instant::now();
        // clk_shift=2 means 4x multiplier between levels (instead of 8x)
        let mut wheel: Wheel<u64> = WheelBuilder::default()
            .clk_shift(2)
            .unbounded(256)
            .build(now);

        // Level 0: 64 slots × 1ms = 64ms range
        // Level 1: 64 slots × 4ms = 256ms range (with 4x multiplier)
        let h1 = wheel.schedule(now + ms(50), 1); // level 0
        let h2 = wheel.schedule(now + ms(100), 2); // level 1 (>= 64 ticks, <256 ticks)

        let mut buf = Vec::new();
        wheel.poll(now + ms(55), &mut buf);
        assert_eq!(buf, vec![1]);

        buf.clear();
        wheel.poll(now + ms(110), &mut buf);
        assert_eq!(buf, vec![2]);

        wheel.cancel(h1);
        wheel.cancel(h2);
    }

    #[test]
    fn custom_num_levels() {
        let now = Instant::now();
        // Only 3 levels instead of 7
        let mut wheel: Wheel<u64> = WheelBuilder::default()
            .num_levels(3)
            .unbounded(256)
            .build(now);

        // Level 0: 64ms, Level 1: 512ms, Level 2: 4096ms
        // Max range is level 2 = 4096ms. Beyond that, clamped.
        let h = wheel.schedule(now + ms(3000), 42);
        assert_eq!(wheel.len(), 1);

        let mut buf = Vec::new();
        wheel.poll(now + ms(3100), &mut buf);
        assert_eq!(buf, vec![42]);

        wheel.cancel(h);
    }

    #[test]
    fn custom_tick_duration() {
        let now = Instant::now();
        // 100μs ticks instead of 1ms
        let mut wheel: Wheel<u64> = WheelBuilder::default()
            .tick_duration(Duration::from_micros(100))
            .unbounded(256)
            .build(now);

        // 1ms = 10 ticks, should be level 0 (< 64 ticks)
        wheel.schedule_forget(now + ms(1), 1);
        // 10ms = 100 ticks, should be level 1 (>= 64 ticks)
        wheel.schedule_forget(now + ms(10), 2);

        let mut buf = Vec::new();
        wheel.poll(now + ms(2), &mut buf);
        assert_eq!(buf, vec![1]);

        buf.clear();
        wheel.poll(now + ms(15), &mut buf);
        assert_eq!(buf, vec![2]);
    }

    #[test]
    fn bounded_custom_config() {
        let now = Instant::now();
        let mut wheel: BoundedWheel<u64> = WheelBuilder::default()
            .slots_per_level(16)
            .num_levels(4)
            .bounded(8)
            .build(now);

        // Fill to capacity
        let mut handles = Vec::new();
        for i in 0..8 {
            handles.push(wheel.try_schedule(now + ms(i * 10 + 10), i).unwrap());
        }
        assert!(wheel.try_schedule(now + ms(100), 99).is_err());

        // Cancel one, schedule another
        wheel.cancel(handles.remove(0));
        let h = wheel.try_schedule(now + ms(100), 99).unwrap();
        handles.push(h);

        // Clean up
        for h in handles {
            wheel.cancel(h);
        }
    }

    // -------------------------------------------------------------------------
    // Builder validation (L13)
    // -------------------------------------------------------------------------

    #[test]
    #[should_panic(expected = "slots_per_level must be <= 64")]
    fn invalid_config_too_many_slots() {
        let now = Instant::now();
        WheelBuilder::default()
            .slots_per_level(128)
            .unbounded(1024)
            .build::<u64>(now);
    }

    #[test]
    #[should_panic(expected = "num_levels must be > 0")]
    fn invalid_config_zero_levels() {
        let now = Instant::now();
        WheelBuilder::default()
            .num_levels(0)
            .unbounded(1024)
            .build::<u64>(now);
    }

    #[test]
    #[should_panic(expected = "num_levels must be <= 8")]
    fn invalid_config_too_many_levels() {
        let now = Instant::now();
        WheelBuilder::default()
            .num_levels(9)
            .unbounded(1024)
            .build::<u64>(now);
    }

    #[test]
    #[should_panic(expected = "clk_shift must be > 0")]
    fn invalid_config_zero_shift() {
        let now = Instant::now();
        WheelBuilder::default()
            .clk_shift(0)
            .unbounded(1024)
            .build::<u64>(now);
    }

    #[test]
    #[should_panic(expected = "tick_duration must be non-zero")]
    fn invalid_config_zero_tick() {
        let now = Instant::now();
        WheelBuilder::default()
            .tick_duration(Duration::ZERO)
            .unbounded(1024)
            .build::<u64>(now);
    }

    #[test]
    #[should_panic(expected = "overflow")]
    fn invalid_config_shift_overflow() {
        let now = Instant::now();
        // 8 levels × clk_shift=8 = 56 bits shift on level 7
        // Plus 64 slots (6 bits) = 62 bits, should be OK
        // But 8 levels × clk_shift=9 = 63 + 6 = 69 bits — overflow
        WheelBuilder::default()
            .num_levels(8)
            .clk_shift(9)
            .unbounded(1024)
            .build::<u64>(now);
    }

    #[test]
    #[should_panic(expected = "strictly finer level")]
    fn invalid_config_cascade_progress() {
        let now = Instant::now();
        // slots_per_level = 4 (2^2), clk_shift = 3 → 2^3 = 8 >= 4, so a not-due
        // entry could relocate to the *same* level and poll would live-lock.
        // Must be rejected at build time.
        WheelBuilder::default()
            .slots_per_level(4)
            .clk_shift(3)
            .num_levels(2)
            .unbounded(64)
            .build::<u64>(now);
    }

    // -------------------------------------------------------------------------
    // Cascade tests (#668)
    // -------------------------------------------------------------------------

    #[test]
    fn cascaded_entry_fires_at_its_deadline() {
        let now = Instant::now();
        let mut wheel: Wheel<u64> = WheelBuilder::default().unbounded(256).build(now);

        // Both deadlines land in the same level-2 slot (46): 3000>>6 == 3005>>6.
        // At now=3000 the slot's min (3000) is due, so the slot is walked: 3000
        // fires, and 3005 (not yet due) cascades down to a finer level rather
        // than being re-walked. It must still fire at its exact deadline.
        wheel.schedule_forget(now + ms(3000), 1);
        wheel.schedule_forget(now + ms(3005), 2);

        let mut buf = Vec::new();
        wheel.poll(now + ms(3000), &mut buf);
        assert_eq!(buf, vec![1], "3000 fires, 3005 cascades");

        buf.clear();
        wheel.poll(now + ms(3005), &mut buf);
        assert_eq!(buf, vec![2], "cascaded entry fires at its exact deadline");
        assert!(wheel.is_empty());
    }

    #[test]
    fn cancel_after_cascade() {
        let now = Instant::now();
        let mut wheel: Wheel<u64> = WheelBuilder::default().unbounded(256).build(now);

        wheel.schedule_forget(now + ms(3000), 1);
        let h = wheel.schedule(now + ms(3005), 2); // cascades on the 3000 poll

        let mut buf = Vec::new();
        wheel.poll(now + ms(3000), &mut buf);
        assert_eq!(buf, vec![1]);
        assert_eq!(wheel.len(), 1, "cascaded entry still live");

        // cancel must find the entry at its new (finer) location and return it.
        assert_eq!(wheel.cancel(h), Some(2));
        assert_eq!(wheel.len(), 0);
    }

    // -------------------------------------------------------------------------
    // Miri-compatible tests (L12)
    // -------------------------------------------------------------------------
    // These tests exercise the raw pointer paths (DLL operations, entry
    // lifecycle, poll) with Drop types to catch UB under Miri.

    #[test]
    fn miri_schedule_cancel_drop_type() {
        let now = Instant::now();
        let mut wheel: Wheel<String> = Wheel::unbounded(64, now);

        let h = wheel.schedule(now + ms(50), "hello".to_string());
        let val = wheel.cancel(h);
        assert_eq!(val, Some("hello".to_string()));
        assert!(wheel.is_empty());
    }

    #[test]
    fn miri_poll_fires_drop_type() {
        let now = Instant::now();
        let mut wheel: Wheel<String> = Wheel::unbounded(64, now);

        wheel.schedule_forget(now + ms(10), "a".to_string());
        wheel.schedule_forget(now + ms(10), "b".to_string());
        wheel.schedule_forget(now + ms(10), "c".to_string());

        let mut buf = Vec::new();
        let fired = wheel.poll(now + ms(20), &mut buf);
        assert_eq!(fired, 3);
        assert_eq!(buf.len(), 3);
        assert!(wheel.is_empty());
    }

    #[test]
    fn miri_cancel_zombie_drop_type() {
        let now = Instant::now();
        let mut wheel: Wheel<String> = Wheel::unbounded(64, now);

        let h = wheel.schedule(now + ms(10), "zombie".to_string());

        let mut buf = Vec::new();
        wheel.poll(now + ms(20), &mut buf);
        assert_eq!(buf, vec!["zombie".to_string()]);

        // h is now a zombie — cancel frees the entry
        let val = wheel.cancel(h);
        assert_eq!(val, None);
    }

    #[test]
    fn miri_free_active_and_zombie() {
        let now = Instant::now();
        let mut wheel: Wheel<String> = Wheel::unbounded(64, now);

        // Active → fire-and-forget via free
        let h1 = wheel.schedule(now + ms(10), "active".to_string());
        wheel.free(h1);

        // Poll fires the fire-and-forget entry
        let mut buf = Vec::new();
        wheel.poll(now + ms(20), &mut buf);
        assert_eq!(buf, vec!["active".to_string()]);

        // Zombie → free
        let h2 = wheel.schedule(now + ms(10), "will-fire".to_string());
        buf.clear();
        wheel.poll(now + ms(20), &mut buf);
        wheel.free(h2); // zombie cleanup
    }

    #[test]
    fn miri_reschedule_drop_type() {
        let now = Instant::now();
        let mut wheel: Wheel<String> = Wheel::unbounded(64, now);

        let h = wheel.schedule(now + ms(100), "moveme".to_string());
        let h = wheel.reschedule(h, now + ms(50));

        let mut buf = Vec::new();
        wheel.poll(now + ms(55), &mut buf);
        assert_eq!(buf, vec!["moveme".to_string()]);

        wheel.cancel(h);
    }

    #[test]
    fn miri_dll_multi_entry_same_slot() {
        // Multiple entries in same slot exercises DLL push/remove paths
        let now = Instant::now();
        let mut wheel: Wheel<Vec<u8>> = Wheel::unbounded(64, now);

        let mut handles = Vec::new();
        for i in 0..5 {
            handles.push(wheel.schedule(now + ms(10), vec![i; 32]));
        }

        // Cancel middle, then head, then tail
        let v2 = wheel.cancel(handles.remove(2));
        assert_eq!(v2.unwrap(), vec![2; 32]);

        let v0 = wheel.cancel(handles.remove(0));
        assert_eq!(v0.unwrap(), vec![0; 32]);

        // Poll remaining
        let mut buf = Vec::new();
        wheel.poll(now + ms(20), &mut buf);
        assert_eq!(buf.len(), 3);

        // Clean up zombie handles
        for h in handles {
            wheel.cancel(h);
        }
    }

    #[test]
    fn miri_drop_wheel_with_entries() {
        let now = Instant::now();
        let mut wheel: Wheel<String> = Wheel::unbounded(64, now);

        // Schedule entries across multiple levels
        for i in 0..20 {
            wheel.schedule_forget(now + ms(i * 100), format!("entry-{i}"));
        }
        assert_eq!(wheel.len(), 20);

        // Drop with active entries — must not leak or UB
        drop(wheel);
    }

    #[test]
    fn miri_bounded_lifecycle() {
        let now = Instant::now();
        let mut wheel: BoundedWheel<String> = BoundedWheel::bounded(4, now);

        let h1 = wheel.try_schedule(now + ms(10), "a".to_string()).unwrap();
        let h2 = wheel.try_schedule(now + ms(20), "b".to_string()).unwrap();
        let h3 = wheel.try_schedule(now + ms(30), "c".to_string()).unwrap();
        let h4 = wheel.try_schedule(now + ms(40), "d".to_string()).unwrap();

        // Full
        let err = wheel.try_schedule(now + ms(50), "e".to_string());
        assert!(err.is_err());

        // Cancel and reuse
        wheel.cancel(h1);
        let h5 = wheel.try_schedule(now + ms(50), "e".to_string()).unwrap();

        // Poll fires some
        let mut buf = Vec::new();
        wheel.poll(now + ms(25), &mut buf);

        // Clean up all remaining handles
        wheel.cancel(h2);
        wheel.free(h3);
        wheel.free(h4);
        wheel.free(h5);
    }

    #[test]
    fn miri_cascade_relocate_drop_type() {
        // Exercises the cascade relocate path (insert_entry called while this
        // slot's `&WheelSlot` is held) with a Drop type, to catch any aliasing
        // UB in that hot-path borrow.
        let now = Instant::now();
        let mut wheel: Wheel<String> = Wheel::unbounded(64, now);

        // Same level-2 slot: 3000>>6 == 3005>>6. At now=3000 the "fires" entry
        // fires and the "cascades" entry relocates to a finer level.
        wheel.schedule_forget(now + ms(3000), "fires".to_string());
        wheel.schedule_forget(now + ms(3005), "cascades".to_string());

        let mut buf = Vec::new();
        wheel.poll(now + ms(3000), &mut buf);
        assert_eq!(buf, vec!["fires".to_string()]);

        buf.clear();
        wheel.poll(now + ms(3005), &mut buf);
        assert_eq!(buf, vec!["cascades".to_string()]);
        assert!(wheel.is_empty());
    }
}

#[cfg(test)]
mod proptests {
    use super::*;
    use proptest::prelude::*;
    use std::collections::HashSet;
    use std::mem;
    use std::time::{Duration, Instant};

    /// Operation in a schedule/cancel interleaving.
    #[derive(Debug, Clone)]
    enum Op {
        /// Schedule a timer at `deadline_ms` milliseconds from epoch.
        Schedule { deadline_ms: u64 },
        /// Cancel the timer at the given index (modulo outstanding handles).
        Cancel { idx: usize },
    }

    fn op_strategy() -> impl Strategy<Value = Op> {
        prop_oneof![
            // Schedule with deadlines from 1ms to 10_000ms
            (1u64..10_000).prop_map(|deadline_ms| Op::Schedule { deadline_ms }),
            // Cancel at random index
            any::<usize>().prop_map(|idx| Op::Cancel { idx }),
        ]
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(500))]

        /// Fuzz schedule/cancel interleaving.
        ///
        /// Random sequence of schedule and cancel operations. Invariants:
        /// - `len` always matches outstanding active timers
        /// - cancel on active handle returns `Some`
        /// - poll collects all un-cancelled values
        #[test]
        fn fuzz_schedule_cancel_interleaving(ops in proptest::collection::vec(op_strategy(), 1..200)) {
            let now = Instant::now();
            let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

            let mut handles: Vec<TimerHandle<u64>> = Vec::new();
            let mut active_values: HashSet<u64> = HashSet::new();
            let mut next_id: u64 = 0;

            for op in &ops {
                match op {
                    Op::Schedule { deadline_ms } => {
                        let id = next_id;
                        next_id += 1;
                        let h = wheel.schedule(now + Duration::from_millis(*deadline_ms), id);
                        handles.push(h);
                        active_values.insert(id);
                    }
                    Op::Cancel { idx } => {
                        if !handles.is_empty() {
                            let i = idx % handles.len();
                            let h = handles.swap_remove(i);
                            let val = wheel.cancel(h);
                            // Value should be Some (all handles are for active timers)
                            let v = val.unwrap();
                            assert!(active_values.remove(&v));
                        }
                    }
                }
                // len must match active values
                prop_assert_eq!(wheel.len(), active_values.len());
            }

            // Poll everything — should collect exactly the remaining active values
            let mut buf = Vec::new();
            // Use a far-future time to fire everything
            wheel.poll(now + Duration::from_secs(100_000), &mut buf);

            // Clean up zombie handles (poll fired them, handles still exist)
            for h in handles {
                mem::forget(h);
            }

            let fired_set: HashSet<u64> = buf.into_iter().collect();
            prop_assert_eq!(fired_set, active_values);
            prop_assert!(wheel.is_empty());
        }

        /// Fuzz poll timing.
        ///
        /// Schedule N timers with random deadlines. Poll at random increasing
        /// times. Assert every timer fires exactly once, fired deadlines are
        /// all <= poll time, unfired deadlines are all > poll time.
        #[test]
        fn fuzz_poll_timing(
            deadlines in proptest::collection::vec(1u64..5000, 1..100),
            poll_times in proptest::collection::vec(1u64..10_000, 1..20),
        ) {
            let now = Instant::now();
            let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);

            // Schedule all timers (fire-and-forget)
            for (i, &d) in deadlines.iter().enumerate() {
                wheel.schedule_forget(now + Duration::from_millis(d), i as u64);
            }

            // Sort poll times to be monotonically increasing
            let mut sorted_times: Vec<u64> = poll_times;
            sorted_times.sort_unstable();
            sorted_times.dedup();

            let mut all_fired: Vec<u64> = Vec::new();

            for &t in &sorted_times {
                let mut buf = Vec::new();
                wheel.poll(now + Duration::from_millis(t), &mut buf);

                // Every fired entry should have deadline_ms <= t
                for &id in &buf {
                    let deadline_ms = deadlines[id as usize];
                    prop_assert!(deadline_ms <= t,
                        "Timer {} with deadline {}ms fired at {}ms", id, deadline_ms, t);
                }

                all_fired.extend(buf);
            }

            // Fire everything remaining
            let mut final_buf = Vec::new();
            wheel.poll(now + Duration::from_secs(100_000), &mut final_buf);
            all_fired.extend(final_buf);

            // Every timer should have fired exactly once
            all_fired.sort_unstable();
            let expected: Vec<u64> = (0..deadlines.len() as u64).collect();
            prop_assert_eq!(all_fired, expected, "Not all timers fired exactly once");
            prop_assert!(wheel.is_empty());
        }

        /// Fuzz next_deadline cache correctness.
        ///
        /// Random sequence of schedule, schedule_forget, cancel, reschedule,
        /// and poll operations. After each operation, verifies the cached
        /// `next_deadline()` matches the uncached full walk.
        #[test]
        fn fuzz_next_deadline_cache(
            ops in proptest::collection::vec(deadline_op_strategy(), 1..300),
        ) {
            let now = Instant::now();
            let mut wheel: Wheel<u64> = Wheel::unbounded(1024, now);
            let mut handles: Vec<(TimerHandle<u64>, u64)> = Vec::new();
            let mut next_id: u64 = 0;

            for op in &ops {
                match op {
                    DeadlineOp::Schedule { deadline_ms } => {
                        let h = wheel.schedule(now + Duration::from_millis(*deadline_ms), next_id);
                        handles.push((h, *deadline_ms));
                        next_id += 1;
                    }
                    DeadlineOp::ScheduleForget { deadline_ms } => {
                        wheel.schedule_forget(now + Duration::from_millis(*deadline_ms), next_id);
                        next_id += 1;
                    }
                    DeadlineOp::Cancel { idx } => {
                        if !handles.is_empty() {
                            let i = idx % handles.len();
                            let (h, _) = handles.swap_remove(i);
                            wheel.cancel(h);
                        }
                    }
                    DeadlineOp::Reschedule { idx, new_deadline_ms } => {
                        if !handles.is_empty() {
                            let i = idx % handles.len();
                            let (h, _) = handles.swap_remove(i);
                            let new_h = wheel.reschedule(h, now + Duration::from_millis(*new_deadline_ms));
                            handles.push((new_h, *new_deadline_ms));
                        }
                    }
                    DeadlineOp::Poll { at_ms } => {
                        let mut buf = Vec::new();
                        wheel.poll(now + Duration::from_millis(*at_ms), &mut buf);
                        // Free zombie handles whose timers just fired.
                        // A handle is a zombie if its deadline_ms <= at_ms.
                        let at = *at_ms;
                        let mut i = 0;
                        while i < handles.len() {
                            if handles[i].1 <= at {
                                let (h, _) = handles.swap_remove(i);
                                wheel.free(h);
                            } else {
                                i += 1;
                            }
                        }
                    }
                }

                // Contract: `next_deadline()` is a LOWER BOUND — the per-slot
                // minima are stale-low after removal, so it may report earlier
                // than the true next fire, never later. Assert it never exceeds
                // the exact minimum, and that emptiness agrees.
                let cached = wheel.next_deadline();
                let exact = wheel.next_deadline_uncached();
                prop_assert_eq!(
                    cached.is_none(),
                    exact.is_none(),
                    "emptiness disagrees after {:?}",
                    op
                );
                if let (Some(c), Some(e)) = (cached, exact) {
                    prop_assert!(
                        c <= e,
                        "next_deadline {:?} exceeded exact {:?} after {:?}",
                        c,
                        e,
                        op
                    );
                }
            }

            for (h, _) in handles {
                mem::forget(h);
            }
        }
    }

    #[derive(Debug, Clone)]
    enum DeadlineOp {
        Schedule { deadline_ms: u64 },
        ScheduleForget { deadline_ms: u64 },
        Cancel { idx: usize },
        Reschedule { idx: usize, new_deadline_ms: u64 },
        Poll { at_ms: u64 },
    }

    fn deadline_op_strategy() -> impl Strategy<Value = DeadlineOp> {
        prop_oneof![
            (1u64..10_000).prop_map(|deadline_ms| DeadlineOp::Schedule { deadline_ms }),
            (1u64..10_000).prop_map(|deadline_ms| DeadlineOp::ScheduleForget { deadline_ms }),
            any::<usize>().prop_map(|idx| DeadlineOp::Cancel { idx }),
            (any::<usize>(), 1u64..10_000).prop_map(|(idx, new_deadline_ms)| {
                DeadlineOp::Reschedule {
                    idx,
                    new_deadline_ms,
                }
            }),
            (1u64..10_000).prop_map(|at_ms| DeadlineOp::Poll { at_ms }),
        ]
    }
}
