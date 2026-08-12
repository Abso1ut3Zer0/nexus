//! Fixed-duration timeout list — a sorted front-end over the wheel machinery.
//!
//! `TimeoutList<T, S>` schedules every timer with the **same** duration, fixed
//! at construction. Because the duration is constant and the clock is monotone,
//! deadlines are monotone in insertion order: appending each new entry at the
//! tail of one intrusive DLL keeps the list sorted with no comparisons. Poll
//! then walks from the head and stops at the first not-due entry — **O(fired)**,
//! not O(population) as the wheel's per-entry scan is. `next_deadline()` is the
//! head's deadline: exact, O(1), no cache.
//!
//! # When to use this instead of [`TimerWheel`](crate::TimerWheel)
//!
//! A wheel earns its keep when deadlines are *arbitrary* — timers interleaved
//! among earlier and later expirations. But a large class of callers schedule
//! **one fixed timeout for everything** (a flat 5 s deadline on every item).
//! For that workload the wheel buckets by deadline and walks buckets to solve
//! an ordering problem that does not exist. `TimeoutList` exploits the single
//! duration directly.
//!
//! # The invariant is structural, not documented
//!
//! There is no per-call `deadline` parameter anywhere in this API. Deadlines
//! are computed internally as `now + timeout`. Out-of-order insertion is
//! *unrepresentable*, not merely prohibited — one caller passing a shorter
//! deadline would break ordering and fire timers late, the worst failure shape
//! because it is invisible until it matters. A `debug_assert!` on insert is the
//! backstop for clock weirdness (a `now` that goes backwards).
//!
//! # Reuse
//!
//! [`WheelEntry`](crate::WheelEntry), [`TimerHandle`], the slab
//! [`store`](crate::store) traits, and the DLL splice logic (`WheelSlot`) are
//! shared verbatim with the wheel — this front-end is the same machinery with
//! one head/tail pair in place of `Vec<Level>`, and the whole `min_deadline`
//! cache removed (the head *is* the min).

use std::marker::PhantomData;
use std::mem;
use std::time::{Duration, Instant};

use nexus_slab::{Full, Slot, bounded, unbounded};

use crate::entry::{EntryPtr, WheelEntry, entry_ref};
use crate::handle::TimerHandle;
use crate::level::WheelSlot;
use crate::store::{BoundedStore, SlabStore};

// =============================================================================
// TimeoutListBuilder (typestate)
// =============================================================================

/// Builder for a [`TimeoutList`], mirroring [`WheelBuilder`](crate::WheelBuilder).
///
/// The timeout duration is fixed up front in [`new`](Self::new) — that is the
/// whole point of the type, so it cannot be a per-schedule parameter later.
///
/// # Examples
///
/// ```
/// use std::time::{Duration, Instant};
/// use nexus_timer::{TimeoutList, TimeoutListBuilder};
///
/// let now = Instant::now();
///
/// // 5-second timeout, unbounded storage, default 1ms tick.
/// let list: TimeoutList<u64> = TimeoutListBuilder::new(Duration::from_secs(5))
///     .unbounded(4096)
///     .build(now);
///
/// // Custom tick, bounded storage.
/// let list: nexus_timer::BoundedTimeoutList<u64> =
///     TimeoutListBuilder::new(Duration::from_millis(250))
///         .tick_duration(Duration::from_micros(100))
///         .bounded(1024)
///         .build(now);
/// ```
#[derive(Debug, Clone, Copy)]
pub struct TimeoutListBuilder {
    timeout: Duration,
    tick_duration: Duration,
}

impl TimeoutListBuilder {
    /// Creates a builder with the fixed timeout every timer will use.
    ///
    /// Tick duration defaults to 1ms. The timeout must be non-zero.
    pub fn new(timeout: Duration) -> Self {
        TimeoutListBuilder {
            timeout,
            tick_duration: Duration::from_millis(1),
        }
    }

    /// Sets the tick duration (internal time quantum). Default: 1ms.
    pub fn tick_duration(mut self, d: Duration) -> Self {
        self.tick_duration = d;
        self
    }

    /// Transitions to an unbounded (growable) builder.
    ///
    /// `chunk_capacity` is the slab chunk size (entries per chunk); the slab
    /// grows by adding chunks as needed.
    pub fn unbounded(self, chunk_capacity: usize) -> UnboundedTimeoutListBuilder {
        UnboundedTimeoutListBuilder {
            config: self,
            chunk_capacity,
        }
    }

    /// Transitions to a bounded (fixed-capacity) builder.
    ///
    /// `capacity` is the maximum number of concurrent timers.
    pub fn bounded(self, capacity: usize) -> BoundedTimeoutListBuilder {
        BoundedTimeoutListBuilder {
            config: self,
            capacity,
        }
    }

    fn validate(&self) {
        assert!(!self.timeout.is_zero(), "timeout must be non-zero");
        assert!(
            !self.tick_duration.is_zero(),
            "tick_duration must be non-zero"
        );
    }

    #[inline]
    fn tick_ns(&self) -> u64 {
        self.tick_duration.as_nanos().min(u64::MAX as u128) as u64
    }

    /// Fixed timeout expressed in whole ticks (rounded up, minimum 1 tick).
    ///
    /// Ceiling division so the effective timeout is never *shorter* than
    /// requested. Computed once at build time — never on the hot path.
    #[inline]
    fn timeout_ticks(&self) -> u64 {
        let tick_ns = self.tick_ns() as u128;
        let timeout_ns = self.timeout.as_nanos();
        let ticks = timeout_ns.div_ceil(tick_ns);
        ticks.min(u64::MAX as u128).max(1) as u64
    }
}

/// Terminal builder for an unbounded [`TimeoutList`].
///
/// Created via [`TimeoutListBuilder::unbounded`]. The only method is `.build()`.
#[derive(Debug)]
pub struct UnboundedTimeoutListBuilder {
    config: TimeoutListBuilder,
    chunk_capacity: usize,
}

impl UnboundedTimeoutListBuilder {
    /// Builds the unbounded timeout list.
    ///
    /// # Panics
    ///
    /// Panics if the configuration is invalid (zero timeout or zero tick).
    pub fn build<T: 'static>(self, now: Instant) -> TimeoutList<T> {
        self.config.validate();
        let tick_ns = self.config.tick_ns();
        let timeout_ticks = self.config.timeout_ticks();
        // SAFETY: TimeoutList is single-threaded (!Sync). Every slot is freed
        // via Slot::from_raw() + slab.free() before the list drops. The slab is
        // never shared across threads.
        let slab = unsafe { unbounded::Slab::with_chunk_capacity(self.chunk_capacity) };
        TimeoutList {
            list: WheelSlot::new(),
            slab,
            timeout_ticks,
            tick_ns,
            inv_tick_ns: (1u128 << 64) / tick_ns as u128,
            epoch: now,
            len: 0,
            _marker: PhantomData,
        }
    }
}

/// Terminal builder for a bounded [`TimeoutList`].
///
/// Created via [`TimeoutListBuilder::bounded`]. The only method is `.build()`.
#[derive(Debug)]
pub struct BoundedTimeoutListBuilder {
    config: TimeoutListBuilder,
    capacity: usize,
}

impl BoundedTimeoutListBuilder {
    /// Builds the bounded timeout list.
    ///
    /// # Panics
    ///
    /// Panics if the configuration is invalid (zero timeout or zero tick).
    pub fn build<T: 'static>(self, now: Instant) -> BoundedTimeoutList<T> {
        self.config.validate();
        let tick_ns = self.config.tick_ns();
        let timeout_ticks = self.config.timeout_ticks();
        // SAFETY: TimeoutList is single-threaded (!Sync). Every slot is freed
        // via Slot::from_raw() + slab.free() before the list drops. The slab is
        // never shared across threads.
        let slab = unsafe { bounded::Slab::with_capacity(self.capacity) };
        TimeoutList {
            list: WheelSlot::new(),
            slab,
            timeout_ticks,
            tick_ns,
            inv_tick_ns: (1u128 << 64) / tick_ns as u128,
            epoch: now,
            len: 0,
            _marker: PhantomData,
        }
    }
}

// =============================================================================
// TimeoutList
// =============================================================================

/// A fixed-duration timeout list with O(fired) poll and O(1) exact next-deadline.
///
/// Generic over:
/// - `T` — the user payload stored with each timer.
/// - `S` — the slab storage backend. Defaults to `unbounded::Slab`.
///
/// Every timer uses the same duration, fixed at construction. See the
/// [module docs](crate::timeout_list) for the invariant this exploits.
///
/// # No `reschedule`
///
/// Rescheduling *later* is push-to-tail and stays ordered, but rescheduling
/// *earlier* would break the sort — and the two are indistinguishable in a
/// single API. So no `reschedule` is offered: callers `cancel` and re-`schedule`,
/// which is the same two operations without the ordering hazard. (This mirrors
/// the wheel's `reschedule`, deliberately omitted here.)
///
/// # Thread Safety
///
/// `Send` but `!Sync`. Can be moved to a thread at setup but must not be
/// shared. All internal raw pointers point into owned allocations (slab
/// chunks) — moving the list moves the heap data with it.
pub struct TimeoutList<
    T: 'static,
    S: SlabStore<Item = WheelEntry<T>> = unbounded::Slab<WheelEntry<T>>,
> {
    /// The whole sorted list: one head/tail intrusive DLL. Reuses the wheel's
    /// `WheelSlot` splice logic (push at tail, unlink from anywhere).
    list: WheelSlot<T>,
    slab: S,
    /// Fixed timeout in ticks. Added to `now` on every schedule.
    timeout_ticks: u64,
    tick_ns: u64,
    inv_tick_ns: u128,
    epoch: Instant,
    len: usize,
    _marker: PhantomData<*const ()>, // !Send (overridden below), !Sync
}

// SAFETY: TimeoutList<T, S> exclusively owns all memory behind its raw
// pointers. The slot head/tail and the WheelEntry prev/next links point into
// slab-owned memory (SlotCell in a slab chunk, a Vec<SlotCell<T>> heap
// allocation). When the list is moved, those heap allocations stay at their
// addresses, so the internal pointers remain valid. No thread-local state, no
// shared ownership.
//
// T: Send is required because timer values cross the thread boundary with the
// list. S is NOT required to be Send: slab types are !Send (raw pointers,
// Cell), but the list exclusively owns its slab — no shared access, no
// aliasing. Outstanding TimerHandle<T> values are !Send and cannot follow the
// list across threads; they become inert (consuming one requires &mut
// TimeoutList, which the original thread no longer has). Worst case is a slot
// leak (refcount stuck at 1), not unsoundness — the same reasoning as the
// wheel.
#[allow(clippy::non_send_fields_in_send_ty)]
unsafe impl<T: Send + 'static, S: SlabStore<Item = WheelEntry<T>>> Send for TimeoutList<T, S> {}

/// A timeout list backed by a fixed-capacity slab.
pub type BoundedTimeoutList<T> = TimeoutList<T, bounded::Slab<WheelEntry<T>>>;

// =============================================================================
// Construction convenience
// =============================================================================

impl<T: 'static> TimeoutList<T> {
    /// Creates an unbounded timeout list with the default 1ms tick.
    ///
    /// For custom tick duration, use [`TimeoutListBuilder`].
    pub fn unbounded(timeout: Duration, chunk_capacity: usize, now: Instant) -> Self {
        TimeoutListBuilder::new(timeout)
            .unbounded(chunk_capacity)
            .build(now)
    }
}

impl<T: 'static> BoundedTimeoutList<T> {
    /// Creates a bounded timeout list with the default 1ms tick.
    ///
    /// For custom tick duration, use [`TimeoutListBuilder`].
    pub fn bounded(timeout: Duration, capacity: usize, now: Instant) -> Self {
        TimeoutListBuilder::new(timeout)
            .bounded(capacity)
            .build(now)
    }
}

// =============================================================================
// Schedule
// =============================================================================

impl<T: 'static, S: SlabStore<Item = WheelEntry<T>>> TimeoutList<T, S> {
    /// Schedules a timer for `now + timeout` and returns a handle for cancellation.
    ///
    /// The handle must be consumed via [`cancel`](Self::cancel) or
    /// [`free`](Self::free). Dropping it is a programming error.
    ///
    /// `now` must be monotonically non-decreasing across calls (a plain
    /// `Instant::now()` at each call site satisfies this). A `now` that goes
    /// backwards trips a `debug_assert!` in debug builds.
    ///
    /// # Panics
    ///
    /// Panics if the backing slab is at capacity (bounded slabs only). This is
    /// a capacity planning error — size the list for peak load.
    pub fn schedule(&mut self, now: Instant, value: T) -> TimerHandle<T> {
        let deadline_ticks = self.deadline_for(now);
        let entry = WheelEntry::new(deadline_ticks, value, 2);
        let ptr = self.slab.alloc(entry).into_raw();
        self.insert_entry(ptr, deadline_ticks);
        self.len += 1;
        TimerHandle::new(ptr)
    }

    /// Schedules a fire-and-forget timer for `now + timeout` (no handle returned).
    ///
    /// The timer fires during poll and its value is collected. It cannot be
    /// cancelled. See [`schedule`](Self::schedule) for the `now` monotonicity
    /// requirement.
    ///
    /// # Panics
    ///
    /// Panics if the backing slab is at capacity (bounded slabs only).
    pub fn schedule_forget(&mut self, now: Instant, value: T) {
        let deadline_ticks = self.deadline_for(now);
        let entry = WheelEntry::new(deadline_ticks, value, 1);
        let ptr = self.slab.alloc(entry).into_raw();
        self.insert_entry(ptr, deadline_ticks);
        self.len += 1;
    }
}

// =============================================================================
// Schedule — fallible (bounded slabs only)
// =============================================================================

impl<T: 'static, S: BoundedStore<Item = WheelEntry<T>>> TimeoutList<T, S> {
    /// Attempts to schedule a timer, returning a handle on success.
    ///
    /// Returns `Err(Full(value))` — with the caller's `T` recovered, not the
    /// internal `WheelEntry` — if the slab is at capacity. Use this when
    /// capacity exhaustion should be handled gracefully; otherwise use
    /// [`schedule`](Self::schedule).
    pub fn try_schedule(&mut self, now: Instant, value: T) -> Result<TimerHandle<T>, Full<T>> {
        let deadline_ticks = self.deadline_for(now);
        let entry = WheelEntry::new(deadline_ticks, value, 2);
        match self.slab.try_alloc(entry) {
            Ok(slot) => {
                let ptr = slot.into_raw();
                self.insert_entry(ptr, deadline_ticks);
                self.len += 1;
                Ok(TimerHandle::new(ptr))
            }
            Err(full) => Err(Full(recover_value(full))),
        }
    }

    /// Attempts to schedule a fire-and-forget timer.
    ///
    /// Returns `Err(Full(value))` — with the caller's `T` recovered — if the
    /// slab is at capacity. Otherwise use [`schedule_forget`](Self::schedule_forget).
    pub fn try_schedule_forget(&mut self, now: Instant, value: T) -> Result<(), Full<T>> {
        let deadline_ticks = self.deadline_for(now);
        let entry = WheelEntry::new(deadline_ticks, value, 1);
        match self.slab.try_alloc(entry) {
            Ok(slot) => {
                let ptr = slot.into_raw();
                self.insert_entry(ptr, deadline_ticks);
                self.len += 1;
                Ok(())
            }
            Err(full) => Err(Full(recover_value(full))),
        }
    }
}

/// Extracts the user's `T` from a `Full<WheelEntry<T>>` produced by a rejected
/// `try_alloc`. The entry was just constructed with `Some(value)` and never
/// inserted, so the value is present.
#[inline]
fn recover_value<T>(full: Full<WheelEntry<T>>) -> T {
    let wheel_entry = full.into_inner();
    // SAFETY: entry was just constructed with Some(value) and never inserted
    // into the list — no other code has accessed it. Single-threaded.
    unsafe { wheel_entry.take_value() }.expect("entry was just constructed with Some(value)")
}

// =============================================================================
// Cancel / Free / Poll / Query — generic over any store
// =============================================================================

impl<T: 'static, S: SlabStore<Item = WheelEntry<T>>> TimeoutList<T, S> {
    /// Cancels a timer and returns its value.
    ///
    /// - Still active (refs == 2): unlinks from the list, extracts the value,
    ///   frees the slab entry. Returns `Some(T)`. O(1) — a mid-list unlink,
    ///   no residency, no tombstone.
    /// - Already fired (zombie handle, refs == 1): frees the slab entry.
    ///   Returns `None`.
    ///
    /// Consumes the handle (no Drop runs).
    pub fn cancel(&mut self, handle: TimerHandle<T>) -> Option<T> {
        let ptr = handle.ptr;
        // Consume handle without running Drop.
        mem::forget(handle);

        // SAFETY: handle guarantees ptr is valid and allocated from our slab.
        let entry = unsafe { entry_ref(ptr) };
        let refs = entry.refs();

        if refs == 2 {
            // Active timer with handle — unlink, extract, free.
            // SAFETY: single-threaded; entry is still in the list (refs == 2),
            // so the value has not been taken by fire_entry.
            let value = unsafe { entry.take_value() };
            // SAFETY: ptr is in self.list's DLL (invariant from insert_entry).
            unsafe { self.list.remove_entry(ptr) };
            self.len -= 1;
            // SAFETY: ptr was allocated from our slab via into_raw().
            self.slab.free(unsafe { Slot::from_raw(ptr) });
            value
        } else {
            // refs == 1: the list already fired this (zombie). The fire path
            // decremented 2 -> 1 and left the entry for us to free.
            debug_assert_eq!(refs, 1, "unexpected refcount {refs} in cancel");
            // SAFETY: ptr was allocated from our slab via into_raw().
            self.slab.free(unsafe { Slot::from_raw(ptr) });
            None
        }
    }

    /// Releases a timer handle without cancelling.
    ///
    /// - Still active: converts to fire-and-forget (refs 2 -> 1). The timer
    ///   stays in the list and fires normally during poll.
    /// - Already fired (zombie): frees the slab entry (refs 1 -> 0).
    ///
    /// Consumes the handle (no Drop runs).
    pub fn free(&mut self, handle: TimerHandle<T>) {
        let ptr = handle.ptr;
        mem::forget(handle);

        // SAFETY: handle guarantees ptr is valid.
        let entry = unsafe { entry_ref(ptr) };
        let new_refs = entry.dec_refs();

        if new_refs == 0 {
            // Was a zombie (fired already, refs was 1) — free the entry.
            // SAFETY: ptr was allocated from our slab via into_raw().
            self.slab.free(unsafe { Slot::from_raw(ptr) });
        }
        // new_refs == 1: timer is now fire-and-forget, stays in the list.
    }

    /// Fires all expired timers, collecting their values into `buf`.
    ///
    /// Returns the number of timers fired. O(fired): the list is sorted, so
    /// this walks from the head and stops at the first not-due entry.
    pub fn poll(&mut self, now: Instant, buf: &mut Vec<T>) -> usize {
        self.poll_with_limit(now, usize::MAX, buf)
    }

    /// Fires expired timers up to `limit`, collecting values into `buf`.
    ///
    /// Returns the number fired in this call. Truncation is resumable: this
    /// stops at a head that is either not-due or beyond `limit`, and the next
    /// call picks up at exactly that head. No bookmark is needed — the sorted
    /// list *is* the cursor. (The wheel needs a resumption argument because it
    /// re-derives its scan position each call; here there is nothing to
    /// re-derive.)
    pub fn poll_with_limit(&mut self, now: Instant, limit: usize, buf: &mut Vec<T>) -> usize {
        let now_ticks = self.instant_to_ticks(now);
        let mut fired = 0;

        while fired < limit {
            let ptr = self.list.entry_head();
            if ptr.is_null() {
                break;
            }
            // SAFETY: ptr is the non-null head of self.list's DLL.
            let entry = unsafe { entry_ref(ptr) };

            #[cfg(test)]
            {
                poll_examined_inc();
            }

            if entry.deadline_ticks() > now_ticks {
                // Sorted: nothing behind the head is due either.
                break;
            }

            // SAFETY: ptr is the current head of self.list's DLL.
            unsafe { self.list.remove_entry(ptr) };
            if let Some(value) = self.fire_entry(ptr) {
                buf.push(value);
            }
            fired += 1;
        }

        fired
    }

    /// Returns the `Instant` of the next timer that will fire, or `None` if empty.
    ///
    /// O(1), exact: the sorted list's head *is* the minimum deadline. No cache.
    pub fn next_deadline(&self) -> Option<Instant> {
        let head = self.list.entry_head();
        if head.is_null() {
            return None;
        }
        // SAFETY: head is non-null and points into self.list's DLL.
        let ticks = unsafe { entry_ref(head) }.deadline_ticks();
        Some(self.ticks_to_instant(ticks))
    }

    /// Returns the number of timers currently in the list.
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns true if the list contains no timers.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    // =========================================================================
    // Internal: tick conversion (replicated from the wheel)
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

    /// Deadline in ticks for a timer scheduled at `now`: `now + fixed timeout`.
    ///
    /// Saturating add guards the (unrealistic, ~584-year) case where `now` is
    /// far enough out that the tick count plus the timeout would overflow u64.
    #[inline]
    fn deadline_for(&self, now: Instant) -> u64 {
        self.instant_to_ticks(now)
            .saturating_add(self.timeout_ticks)
    }

    // =========================================================================
    // Internal: insert / fire
    // =========================================================================

    /// Appends an entry at the tail of the sorted list.
    ///
    /// Correctness rests on the caller's `deadline_ticks` being >= the current
    /// tail's — guaranteed by a monotone `now` and a constant timeout. The
    /// `debug_assert!` is the backstop for a clock that goes backwards.
    #[inline]
    fn insert_entry(&mut self, entry_ptr: EntryPtr<T>, deadline_ticks: u64) {
        // The entry's `level`/`slot_idx` stay at their `WheelEntry::new` default
        // of (0, 0): a single sorted list has no slot to record, and the unlink
        // path (`WheelSlot::remove_entry`) splices via prev/next and never reads
        // location. So there is no `set_location` write on this hot path.
        debug_assert!(
            {
                let tail = self.list.entry_tail();
                // SAFETY: tail, when non-null, points into self.list's DLL.
                tail.is_null() || deadline_ticks >= unsafe { entry_ref(tail) }.deadline_ticks()
            },
            "TimeoutList: deadline {deadline_ticks} inserted out of order \
             (did `now` go backwards?)",
        );

        // SAFETY: entry_ptr is valid (just allocated) and not in any DLL yet.
        unsafe { self.list.push_entry(entry_ptr) };
    }

    /// Fires a single entry: extracts value, decrements refcount, possibly frees.
    ///
    /// Returns `Some(T)` if the value was still present (not already cancelled).
    /// The caller has already unlinked `entry_ptr` from the list.
    #[inline]
    fn fire_entry(&mut self, entry_ptr: EntryPtr<T>) -> Option<T> {
        // SAFETY: entry_ptr was the head we just unlinked; still a live slab slot.
        let entry = unsafe { entry_ref(entry_ptr) };

        // SAFETY: single-threaded.
        let value = unsafe { entry.take_value() };

        let new_refs = entry.dec_refs();
        if new_refs == 0 {
            // Fire-and-forget (was refs == 1) — free the slab entry immediately.
            // SAFETY: entry_ptr was allocated from our slab via into_raw().
            self.slab.free(unsafe { Slot::from_raw(entry_ptr) });
        }
        // new_refs == 1: handle exists (was refs == 2), entry becomes a zombie.
        // The handle holder frees it via cancel() or free().

        self.len -= 1;
        value
    }
}

// =============================================================================
// Drop
// =============================================================================

impl<T: 'static, S: SlabStore<Item = WheelEntry<T>>> Drop for TimeoutList<T, S> {
    fn drop(&mut self) {
        // Walk the single list, free every remaining entry so nothing leaks.
        let mut entry_ptr = self.list.entry_head();
        while !entry_ptr.is_null() {
            // SAFETY: entry_ptr is in self.list's DLL.
            let next_entry = unsafe { entry_ref(entry_ptr) }.next();
            // SAFETY: entry_ptr was allocated from our slab via into_raw().
            self.slab.free(unsafe { Slot::from_raw(entry_ptr) });
            entry_ptr = next_entry;
        }
    }
}

// =============================================================================
// Test-only instrumentation: entries examined during poll
// =============================================================================
//
// A nothing-due poll must be flat across population — it examines only the
// head (one deadline compare) and fires nothing, never scanning the list the
// way the wheel does. This counter proves that: tests reset it, poll, and
// assert the count is 1 (non-empty, nothing due) regardless of population.

#[cfg(test)]
thread_local! {
    static POLL_EXAMINED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
fn poll_examined_inc() {
    POLL_EXAMINED.with(|c| c.set(c.get() + 1));
}

#[cfg(test)]
fn poll_examined_reset() {
    POLL_EXAMINED.with(|c| c.set(0));
}

#[cfg(test)]
fn poll_examined_get() -> usize {
    POLL_EXAMINED.with(std::cell::Cell::get)
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

    fn list_50ms(now: Instant) -> TimeoutList<u64> {
        TimeoutList::unbounded(ms(50), 1024, now)
    }

    // -------------------------------------------------------------------------
    // Thread safety
    // -------------------------------------------------------------------------

    fn assert_send<T: Send>() {}

    #[test]
    fn timeout_list_is_send() {
        assert_send::<TimeoutList<u64>>();
        assert_send::<BoundedTimeoutList<u64>>();
    }

    // -------------------------------------------------------------------------
    // Construction
    // -------------------------------------------------------------------------

    #[test]
    fn default_construction() {
        let now = Instant::now();
        let list = list_50ms(now);
        assert!(list.is_empty());
        assert_eq!(list.len(), 0);
        assert!(list.next_deadline().is_none());
    }

    #[test]
    fn bounded_construction() {
        let now = Instant::now();
        let list: BoundedTimeoutList<u64> = BoundedTimeoutList::bounded(ms(50), 128, now);
        assert!(list.is_empty());
    }

    #[test]
    #[should_panic(expected = "timeout must be non-zero")]
    fn invalid_zero_timeout() {
        let now = Instant::now();
        TimeoutListBuilder::new(Duration::ZERO)
            .unbounded(64)
            .build::<u64>(now);
    }

    #[test]
    #[should_panic(expected = "tick_duration must be non-zero")]
    fn invalid_zero_tick() {
        let now = Instant::now();
        TimeoutListBuilder::new(ms(50))
            .tick_duration(Duration::ZERO)
            .unbounded(64)
            .build::<u64>(now);
    }

    // -------------------------------------------------------------------------
    // Lifecycle (ported from wheel.rs)
    // -------------------------------------------------------------------------

    #[test]
    fn schedule_and_cancel() {
        let now = Instant::now();
        let mut list = list_50ms(now);

        let h = list.schedule(now, 42);
        assert_eq!(list.len(), 1);

        let val = list.cancel(h);
        assert_eq!(val, Some(42));
        assert_eq!(list.len(), 0);
    }

    #[test]
    fn schedule_forget_fires() {
        let now = Instant::now();
        let mut list = list_50ms(now);

        list.schedule_forget(now, 99);
        assert_eq!(list.len(), 1);

        let mut buf = Vec::new();
        let fired = list.poll(now + ms(60), &mut buf);
        assert_eq!(fired, 1);
        assert_eq!(buf, vec![99]);
        assert_eq!(list.len(), 0);
    }

    #[test]
    fn cancel_after_fire_returns_none() {
        let now = Instant::now();
        let mut list = list_50ms(now);

        let h = list.schedule(now, 42);

        let mut buf = Vec::new();
        list.poll(now + ms(60), &mut buf);
        assert_eq!(buf, vec![42]);

        // Handle is now a zombie.
        let val = list.cancel(h);
        assert_eq!(val, None);
    }

    #[test]
    fn free_active_timer_becomes_fire_and_forget() {
        let now = Instant::now();
        let mut list = list_50ms(now);

        let h = list.schedule(now, 42);
        list.free(h); // releases handle, timer stays
        assert_eq!(list.len(), 1);

        let mut buf = Vec::new();
        list.poll(now + ms(60), &mut buf);
        assert_eq!(buf, vec![42]);
        assert_eq!(list.len(), 0);
    }

    #[test]
    fn free_zombie_handle() {
        let now = Instant::now();
        let mut list = list_50ms(now);

        let h = list.schedule(now, 42);

        let mut buf = Vec::new();
        list.poll(now + ms(60), &mut buf);

        // Handle is a zombie, free cleans up.
        list.free(h);
    }

    // -------------------------------------------------------------------------
    // Bounded full
    // -------------------------------------------------------------------------

    #[test]
    fn bounded_full() {
        let now = Instant::now();
        let mut list: BoundedTimeoutList<u64> = BoundedTimeoutList::bounded(ms(50), 2, now);

        let h1 = list.try_schedule(now, 1).unwrap();
        let h2 = list.try_schedule(now, 2).unwrap();

        let err = list.try_schedule(now, 3);
        assert!(err.is_err());
        // The caller's T is recovered, not the WheelEntry wrapper.
        let recovered = err.unwrap_err().into_inner();
        assert_eq!(recovered, 3);

        // Cancel one, room again.
        list.cancel(h1);
        let h3 = list.try_schedule(now, 3).unwrap();

        list.free(h2);
        list.free(h3);
    }

    #[test]
    fn bounded_schedule_forget_full() {
        let now = Instant::now();
        let mut list: BoundedTimeoutList<u64> = BoundedTimeoutList::bounded(ms(50), 1, now);

        list.try_schedule_forget(now, 1).unwrap();
        let err = list.try_schedule_forget(now, 2);
        assert!(err.is_err());
        assert_eq!(err.unwrap_err().into_inner(), 2);
    }

    // -------------------------------------------------------------------------
    // Ordering / FIFO
    // -------------------------------------------------------------------------

    #[test]
    fn poll_respects_deadline() {
        let now = Instant::now();
        let mut list = list_50ms(now);

        // Fixed 50ms timeout; schedule at staggered `now`s.
        list.schedule_forget(now, 1); // deadline ~50ms
        list.schedule_forget(now + ms(40), 2); // deadline ~90ms
        list.schedule_forget(now + ms(90), 3); // deadline ~140ms

        let mut buf = Vec::new();

        let fired = list.poll(now + ms(60), &mut buf);
        assert_eq!(fired, 1);
        assert_eq!(buf, vec![1]);
        assert_eq!(list.len(), 2);

        buf.clear();
        let fired = list.poll(now + ms(100), &mut buf);
        assert_eq!(fired, 1);
        assert_eq!(buf, vec![2]);

        buf.clear();
        let fired = list.poll(now + ms(200), &mut buf);
        assert_eq!(fired, 1);
        assert_eq!(buf, vec![3]);

        assert!(list.is_empty());
    }

    #[test]
    fn mid_list_cancel_preserves_fifo() {
        let now = Instant::now();
        let mut list = list_50ms(now);

        // Five timers at strictly increasing `now`s → strictly increasing
        // deadlines, in insertion order.
        let mut handles: Vec<_> = (0..5u64).map(|i| list.schedule(now + ms(i), i)).collect();
        assert_eq!(list.len(), 5);

        // Cancel index 2 (value 2), then index 0 (value 0). Remaining, in
        // list order: [1, 3, 4].
        let v2 = list.cancel(handles.remove(2));
        assert_eq!(v2, Some(2));
        let v0 = list.cancel(handles.remove(0));
        assert_eq!(v0, Some(0));
        assert_eq!(list.len(), 3);

        let mut buf = Vec::new();
        let fired = list.poll(now + ms(1000), &mut buf);
        assert_eq!(fired, 3);
        // Exact Vec equality — FIFO order, not sorted-after-the-fact.
        assert_eq!(buf, vec![1, 3, 4]);

        // Remaining handles are zombies now.
        for h in handles {
            assert_eq!(list.cancel(h), None);
        }
    }

    // -------------------------------------------------------------------------
    // poll_with_limit truncation + resumption
    // -------------------------------------------------------------------------

    #[test]
    fn poll_with_limit_truncation_then_resumption() {
        let now = Instant::now();
        let mut list = list_50ms(now);

        for i in 0..10u64 {
            list.schedule_forget(now + ms(i), i);
        }

        let mut buf = Vec::new();
        let poll_at = now + ms(1000);

        let fired = list.poll_with_limit(poll_at, 3, &mut buf);
        assert_eq!(fired, 3);
        assert_eq!(list.len(), 7);

        let fired = list.poll_with_limit(poll_at, 3, &mut buf);
        assert_eq!(fired, 3);
        assert_eq!(list.len(), 4);

        let fired = list.poll(poll_at, &mut buf);
        assert_eq!(fired, 4);
        assert!(list.is_empty());

        // Full set, in order, across the truncated calls.
        assert_eq!(buf, (0..10u64).collect::<Vec<_>>());
    }

    #[test]
    fn poll_with_limit_mixed_expiry() {
        let now = Instant::now();
        let mut list = list_50ms(now);

        // Three due at poll time, two not.
        list.schedule_forget(now, 1);
        list.schedule_forget(now, 2);
        list.schedule_forget(now, 3);
        list.schedule_forget(now + ms(500), 4); // deadline ~550ms
        list.schedule_forget(now + ms(500), 5);
        assert_eq!(list.len(), 5);

        let mut buf = Vec::new();

        let fired = list.poll_with_limit(now + ms(60), 2, &mut buf);
        assert_eq!(fired, 2);
        assert_eq!(list.len(), 3);

        let fired = list.poll_with_limit(now + ms(60), 5, &mut buf);
        assert_eq!(fired, 1); // only the third due entry; 4 and 5 not due
        assert_eq!(list.len(), 2);

        assert_eq!(buf, vec![1, 2, 3]);
    }

    // -------------------------------------------------------------------------
    // next_deadline
    // -------------------------------------------------------------------------

    #[test]
    fn next_deadline_is_head_before_and_after_cancel() {
        let now = Instant::now();
        let mut list = list_50ms(now);

        let h0 = list.schedule(now, 0); // deadline ~ now+50
        list.schedule_forget(now + ms(30), 1); // deadline ~ now+80
        list.schedule_forget(now + ms(60), 2); // deadline ~ now+110

        // Head is the first-scheduled: ~ now + 50ms.
        let d0 = list.next_deadline().unwrap();
        let delta0 = d0.duration_since(now);
        assert!(delta0 >= ms(49) && delta0 <= ms(51), "delta0 = {delta0:?}");

        // Cancel the head — next deadline becomes the second entry (~now+80ms).
        assert_eq!(list.cancel(h0), Some(0));
        let d1 = list.next_deadline().unwrap();
        let delta1 = d1.duration_since(now);
        assert!(delta1 >= ms(79) && delta1 <= ms(81), "delta1 = {delta1:?}");
    }

    #[test]
    fn next_deadline_empty_after_drain() {
        let now = Instant::now();
        let mut list = list_50ms(now);
        list.schedule_forget(now, 1);

        let mut buf = Vec::new();
        list.poll(now + ms(60), &mut buf);
        assert!(list.next_deadline().is_none());
    }

    // -------------------------------------------------------------------------
    // Nothing-due poll touches (examines) only the head — flat across population
    // -------------------------------------------------------------------------

    #[test]
    fn nothing_due_poll_examines_only_head() {
        let now = Instant::now();

        for &population in &[100usize, 1_000, 10_000, 50_000] {
            // Big timeout so nothing is due at poll time.
            let mut list: TimeoutList<u64> =
                TimeoutList::unbounded(Duration::from_secs(3600), population + 16, now);
            for i in 0..population as u64 {
                list.schedule_forget(now, i);
            }
            assert_eq!(list.len(), population);

            let mut buf = Vec::new();
            poll_examined_reset();
            let fired = list.poll(now + ms(1), &mut buf); // nothing due
            assert_eq!(fired, 0);
            assert!(buf.is_empty());

            // Exactly one entry examined (the head), regardless of population.
            // This is the O(1) nothing-due property — no population scan.
            assert_eq!(
                poll_examined_get(),
                1,
                "population {population}: nothing-due poll examined more than the head",
            );
        }
    }

    #[test]
    fn nothing_due_poll_empty_examines_zero() {
        let now = Instant::now();
        let mut list = list_50ms(now);

        let mut buf = Vec::new();
        poll_examined_reset();
        let fired = list.poll(now + ms(1), &mut buf);
        assert_eq!(fired, 0);
        // Empty list: literally zero entries touched.
        assert_eq!(poll_examined_get(), 0);
    }

    // -------------------------------------------------------------------------
    // Same-deadline entries (all scheduled at the same `now`)
    // -------------------------------------------------------------------------

    #[test]
    fn multiple_entries_same_deadline() {
        let now = Instant::now();
        let mut list = list_50ms(now);

        let mut handles: Vec<_> = (0..5u64).map(|i| list.schedule(now, i)).collect();
        assert_eq!(list.len(), 5);

        let v2 = list.cancel(handles.remove(2));
        assert_eq!(v2, Some(2));
        let v0 = list.cancel(handles.remove(0));
        assert_eq!(v0, Some(0));
        assert_eq!(list.len(), 3);

        let mut buf = Vec::new();
        let fired = list.poll(now + ms(60), &mut buf);
        assert_eq!(fired, 3);
        assert_eq!(buf, vec![1, 3, 4]);

        for h in handles {
            assert_eq!(list.cancel(h), None);
        }
    }

    // -------------------------------------------------------------------------
    // Reuse after drain
    // -------------------------------------------------------------------------

    #[test]
    fn reuse_after_full_drain() {
        let now = Instant::now();
        let mut list = list_50ms(now);

        for i in 0..10u64 {
            list.schedule_forget(now, i);
        }
        let mut buf = Vec::new();
        list.poll(now + ms(60), &mut buf);
        assert_eq!(buf.len(), 10);
        assert!(list.is_empty());

        buf.clear();
        for i in 10..20u64 {
            list.schedule_forget(now + ms(100), i);
        }
        assert_eq!(list.len(), 10);
        list.poll(now + ms(200), &mut buf);
        assert_eq!(buf.len(), 10);
        assert!(list.is_empty());
    }

    // -------------------------------------------------------------------------
    // Drop
    // -------------------------------------------------------------------------

    #[test]
    fn drop_cleans_up_active_entries() {
        // Prove the list drops the VALUES of unfired timers on `Drop`, not just
        // that it reclaims the slab slots. `unbounded::Slab::free` drops the
        // value (store.rs), but nothing else in the suite verifies it — the miri
        // run uses `-Zmiri-ignore-leaks`, so a value leak would slip straight
        // past. A `Drop`-counting value makes the property observable.
        use std::sync::Arc;
        use std::sync::atomic::{AtomicUsize, Ordering};

        struct DropCounter(Arc<AtomicUsize>);
        impl Drop for DropCounter {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::Relaxed);
            }
        }

        let dropped = Arc::new(AtomicUsize::new(0));
        let now = Instant::now();
        let mut list: TimeoutList<DropCounter> = TimeoutList::unbounded(ms(50), 1024, now);
        for i in 0..100u64 {
            list.schedule_forget(now + ms(i), DropCounter(Arc::clone(&dropped)));
        }
        assert_eq!(list.len(), 100);

        drop(list);
        assert_eq!(
            dropped.load(Ordering::Relaxed),
            100,
            "every unfired timer's value must be dropped when the list is dropped",
        );
    }

    #[test]
    fn drop_with_outstanding_handles() {
        // Dropping the list must free the VALUES of handle-bearing (refs == 2)
        // entries too, even when the handles were never consumed — the one Drop
        // path `drop_cleans_up_active_entries` (refs == 1) does not cover. The
        // handles are `mem::forget`ed to stand in for "still outstanding"
        // without tripping `TimerHandle`'s drop debug_assert.
        use std::sync::Arc;
        use std::sync::atomic::{AtomicUsize, Ordering};

        struct DropCounter(Arc<AtomicUsize>);
        impl Drop for DropCounter {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::Relaxed);
            }
        }

        let dropped = Arc::new(AtomicUsize::new(0));
        let now = Instant::now();
        let mut list: TimeoutList<DropCounter> = TimeoutList::unbounded(ms(50), 1024, now);
        for i in 0..100u64 {
            let h = list.schedule(now + ms(i), DropCounter(Arc::clone(&dropped)));
            std::mem::forget(h); // outstanding handle — never consumed (refs stays 2)
        }
        assert_eq!(list.len(), 100);

        drop(list);
        assert_eq!(
            dropped.load(Ordering::Relaxed),
            100,
            "handle-bearing (refs == 2) timer values must be dropped with the list",
        );
    }

    // -------------------------------------------------------------------------
    // Deadline-in-the-past fires immediately
    // -------------------------------------------------------------------------

    #[test]
    fn poll_far_past_deadline_fires() {
        let now = Instant::now();
        let mut list = list_50ms(now);

        list.schedule_forget(now, 42);
        let mut buf = Vec::new();
        // Way past the 50ms deadline.
        let fired = list.poll(now + ms(10_000), &mut buf);
        assert_eq!(fired, 1);
        assert_eq!(buf, vec![42]);
    }

    // -------------------------------------------------------------------------
    // Miri-compatible tests (raw-pointer paths with a Drop type)
    // -------------------------------------------------------------------------

    #[test]
    fn miri_schedule_cancel_drop_type() {
        let now = Instant::now();
        let mut list: TimeoutList<String> = TimeoutList::unbounded(ms(50), 64, now);

        let h = list.schedule(now, "hello".to_string());
        let val = list.cancel(h);
        assert_eq!(val, Some("hello".to_string()));
        assert!(list.is_empty());
    }

    #[test]
    fn miri_poll_fires_drop_type() {
        let now = Instant::now();
        let mut list: TimeoutList<String> = TimeoutList::unbounded(ms(10), 64, now);

        list.schedule_forget(now, "a".to_string());
        list.schedule_forget(now, "b".to_string());
        list.schedule_forget(now, "c".to_string());

        let mut buf = Vec::new();
        let fired = list.poll(now + ms(20), &mut buf);
        assert_eq!(fired, 3);
        assert_eq!(buf, vec!["a".to_string(), "b".to_string(), "c".to_string()]);
        assert!(list.is_empty());
    }

    #[test]
    fn miri_cancel_zombie_drop_type() {
        let now = Instant::now();
        let mut list: TimeoutList<String> = TimeoutList::unbounded(ms(10), 64, now);

        let h = list.schedule(now, "zombie".to_string());

        let mut buf = Vec::new();
        list.poll(now + ms(20), &mut buf);
        assert_eq!(buf, vec!["zombie".to_string()]);

        let val = list.cancel(h);
        assert_eq!(val, None);
    }

    #[test]
    fn miri_free_active_and_zombie() {
        let now = Instant::now();
        let mut list: TimeoutList<String> = TimeoutList::unbounded(ms(10), 64, now);

        // Active → fire-and-forget via free.
        let h1 = list.schedule(now, "active".to_string());
        list.free(h1);

        let mut buf = Vec::new();
        list.poll(now + ms(20), &mut buf);
        assert_eq!(buf, vec!["active".to_string()]);

        // Zombie → free.
        let h2 = list.schedule(now, "will-fire".to_string());
        buf.clear();
        list.poll(now + ms(20), &mut buf);
        list.free(h2);
    }

    #[test]
    fn miri_mid_list_unlink_drop_type() {
        let now = Instant::now();
        let mut list: TimeoutList<Vec<u8>> = TimeoutList::unbounded(ms(10), 64, now);

        let mut handles: Vec<_> = (0..5u8)
            .map(|i| list.schedule(now + Duration::from_micros(i as u64), vec![i; 32]))
            .collect();

        // Cancel middle, then head.
        let v2 = list.cancel(handles.remove(2));
        assert_eq!(v2.unwrap(), vec![2u8; 32]);
        let v0 = list.cancel(handles.remove(0));
        assert_eq!(v0.unwrap(), vec![0u8; 32]);

        let mut buf = Vec::new();
        list.poll(now + ms(20), &mut buf);
        assert_eq!(buf.len(), 3);

        for h in handles {
            assert_eq!(list.cancel(h), None);
        }
    }

    #[test]
    fn miri_drop_list_with_entries() {
        let now = Instant::now();
        let mut list: TimeoutList<String> = TimeoutList::unbounded(ms(50), 64, now);

        for i in 0..20u64 {
            list.schedule_forget(now + ms(i), format!("entry-{i}"));
        }
        assert_eq!(list.len(), 20);
        drop(list);
    }

    #[test]
    fn miri_bounded_lifecycle() {
        let now = Instant::now();
        let mut list: BoundedTimeoutList<String> = BoundedTimeoutList::bounded(ms(30), 4, now);

        let h1 = list.try_schedule(now, "a".to_string()).unwrap();
        let h2 = list.try_schedule(now, "b".to_string()).unwrap();
        let h3 = list.try_schedule(now, "c".to_string()).unwrap();
        let h4 = list.try_schedule(now, "d".to_string()).unwrap();

        assert!(list.try_schedule(now, "e".to_string()).is_err());

        list.cancel(h1);
        let h5 = list.try_schedule(now, "e".to_string()).unwrap();

        let mut buf = Vec::new();
        list.poll(now + ms(40), &mut buf);

        // Everything fired; remaining handles are zombies.
        list.free(h2);
        list.free(h3);
        list.free(h4);
        list.free(h5);
    }
}

// =============================================================================
// Property tests
// =============================================================================

#[cfg(test)]
mod proptests {
    use super::*;
    use proptest::prelude::*;
    use std::collections::{HashMap, HashSet};
    use std::time::{Duration, Instant};

    const TIMEOUT_MS: u64 = 100;
    // With a 1ms tick and an exact-multiple timeout, the reciprocal tick
    // conversion is at most one tick low, so a timer can fire at most 1ms
    // before its nominal `schedule_now + TIMEOUT_MS` deadline.
    const EARLY_SLOP_MS: u64 = 1;

    #[derive(Debug, Clone)]
    enum Op {
        Schedule,
        ScheduleForget,
        Cancel { idx: usize },
        Poll,
        Advance,
    }

    fn op_strategy() -> impl Strategy<Value = (Op, u64)> {
        // Every op carries a non-negative clock advance, keeping `now`
        // monotone so the fixed-timeout deadlines stay sorted.
        let advance = 0u64..500;
        let op = prop_oneof![
            Just(Op::Schedule),
            Just(Op::ScheduleForget),
            any::<usize>().prop_map(|idx| Op::Cancel { idx }),
            Just(Op::Poll),
            Just(Op::Advance),
        ];
        (op, advance)
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(400))]

        /// Random schedule / schedule_forget / cancel / poll interleaving.
        ///
        /// Invariants:
        /// - `len` always matches the live (scheduled, not cancelled, not
        ///   fired) count.
        /// - every value fires exactly once.
        /// - no value fires before its deadline (within 1ms tick slop).
        /// - each poll's output is non-decreasing in deadline.
        #[test]
        fn fuzz_schedule_cancel_poll(ops in proptest::collection::vec(op_strategy(), 1..300)) {
            let now = Instant::now();
            let mut list: TimeoutList<u64> = TimeoutList::unbounded(
                Duration::from_millis(TIMEOUT_MS),
                4096,
                now,
            );

            // value -> nominal deadline_ms (schedule clock + TIMEOUT_MS)
            let mut live: HashMap<u64, u64> = HashMap::new();
            // outstanding active handles: (handle, value, deadline_ms)
            let mut handles: Vec<(TimerHandle<u64>, u64, u64)> = Vec::new();
            let mut fired: HashSet<u64> = HashSet::new();
            let mut clock: u64 = 0;
            let mut next_id: u64 = 0;

            for (op, advance) in &ops {
                clock += *advance; // monotone

                match op {
                    Op::Schedule => {
                        let id = next_id;
                        next_id += 1;
                        let deadline = clock + TIMEOUT_MS;
                        let h = list.schedule(now + Duration::from_millis(clock), id);
                        handles.push((h, id, deadline));
                        live.insert(id, deadline);
                    }
                    Op::ScheduleForget => {
                        let id = next_id;
                        next_id += 1;
                        let deadline = clock + TIMEOUT_MS;
                        list.schedule_forget(now + Duration::from_millis(clock), id);
                        live.insert(id, deadline);
                    }
                    Op::Cancel { idx } => {
                        if !handles.is_empty() {
                            let i = idx % handles.len();
                            let (h, val, _) = handles.swap_remove(i);
                            // Handles only ever hold active timers here (zombies
                            // are freed right after each poll), so cancel returns
                            // Some.
                            let r = list.cancel(h);
                            prop_assert_eq!(r, Some(val));
                            prop_assert!(live.remove(&val).is_some());
                            prop_assert!(!fired.contains(&val));
                        }
                    }
                    Op::Poll => {
                        let mut buf = Vec::new();
                        list.poll(now + Duration::from_millis(clock), &mut buf);

                        let mut prev_deadline = 0u64;
                        for &v in &buf {
                            let deadline = *live.get(&v)
                                .expect("fired value must be live");
                            // No early fire (within tick slop).
                            prop_assert!(
                                deadline <= clock + EARLY_SLOP_MS,
                                "value {} deadline {}ms fired at {}ms",
                                v, deadline, clock,
                            );
                            // Non-decreasing in deadline within this poll.
                            prop_assert!(deadline >= prev_deadline);
                            prev_deadline = deadline;
                            // Fires exactly once.
                            prop_assert!(fired.insert(v));
                            live.remove(&v);
                        }

                        // Free zombie handles whose timers just fired.
                        let fired_now: HashSet<u64> = buf.iter().copied().collect();
                        let mut i = 0;
                        while i < handles.len() {
                            if fired_now.contains(&handles[i].1) {
                                let (h, _, _) = handles.swap_remove(i);
                                list.free(h);
                            } else {
                                i += 1;
                            }
                        }
                    }
                    Op::Advance => {}
                }

                prop_assert_eq!(list.len(), live.len());
            }

            // Fire everything remaining.
            let mut buf = Vec::new();
            list.poll(now + Duration::from_secs(1_000_000), &mut buf);
            for &v in &buf {
                prop_assert!(fired.insert(v));
                prop_assert!(live.remove(&v).is_some());
            }
            // All remaining handles are zombies now.
            for (h, _, _) in handles {
                list.free(h);
            }

            prop_assert!(live.is_empty());
            prop_assert!(list.is_empty());
        }
    }
}
