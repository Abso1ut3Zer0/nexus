//! # nexus-slab
//!
//! A high-performance slab allocator optimized for predictable latency.
//!
//! ## Design Philosophy
//!
//! Unlike traditional slab allocators that immediately reuse freed slots (LIFO),
//! nexus-slab prioritizes sequential "bump" allocation for cache locality. The
//! key insight is that by tracking occupancy per slab, we can detect when slabs
//! fully drain and reset them for fresh bump allocation.
//!
//! ## Allocation Priority
//!
//! 1. **Bump** from current slab (sequential, cache-friendly)
//! 2. **Empty slab** from empty list → reset → bump (fresh sequential)
//! 3. **Freelist** from retired slabs (scattered but no syscall)
//! 4. **Grow** new slab (syscall, last resort)
//!
//! ## Retire Threshold
//!
//! Slabs are retired before reaching 100% capacity (default 75%). This gives
//! slabs a better chance to fully drain, enabling bump allocation recovery.
//! Tradeoff: higher threshold = more memory efficient, lower = better drain odds.

#![warn(missing_docs)]

use std::ptr::{self, NonNull};

mod sys;

// =============================================================================
// Constants
// =============================================================================

const SLAB_NONE: u32 = u32::MAX;
const SLOT_NONE: u32 = u32::MAX;

/// Fixed mode: pre-allocated, bounded capacity.
pub const FIXED: bool = true;
/// Dynamic mode: grows on demand.
pub const DYNAMIC: bool = false;

// =============================================================================
// Key
// =============================================================================

/// Opaque handle to an allocated slot.
///
/// Keys are stable for the lifetime of the allocation. After `remove()`,
/// the key becomes invalid and must not be used.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Key(u64);

impl Key {
    #[inline]
    fn new(slab: u32, slot: u32) -> Self {
        Self(((slab as u64) << 32) | (slot as u64))
    }

    /// Slab id getter method.
    #[inline]
    pub fn slab(self) -> u32 {
        (self.0 >> 32) as u32
    }

    /// Slot id getter method within a slab.
    #[inline]
    pub fn slot(self) -> u32 {
        self.0 as u32
    }

    /// Unsafe constructor.
    #[inline]
    pub const unsafe fn from_raw(value: u64) -> Self {
        Self(value)
    }
}

// =============================================================================
// Errors
// =============================================================================

/// Returned when inserting into a full fixed-capacity slab.
#[derive(Debug)]
pub struct Full<T>(pub T);

/// Errors that can occur when building a slab.
#[derive(Debug)]
pub enum SlabError {
    /// Slot size exceeds slab size.
    SlotTooLarge {
        /// Size of a single slot in bytes.
        slot_size: usize,
        /// Size of a slab in bytes.
        slab_size: usize,
    },
    /// Zero capacity requested for fixed slab.
    ZeroCapacity,
    /// OS memory allocation failed.
    Allocation(std::io::Error),
}

// =============================================================================
// Slot
// =============================================================================

enum Slot<T> {
    Vacant { next: u32 },
    Occupied { value: T },
}

// =============================================================================
// SlabMeta
// =============================================================================

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum SlabState {
    Current,
    Empty,
    HasFreelist,
    Full,
}

struct SlabMeta {
    bump_cursor: u32,
    occupied: u32,
    free_head: u32,
    prev: u32,
    next: u32,
    state: SlabState,
}

impl SlabMeta {
    const fn new() -> Self {
        Self {
            bump_cursor: 0,
            occupied: 0,
            free_head: SLOT_NONE,
            prev: SLAB_NONE,
            next: SLAB_NONE,
            state: SlabState::Empty,
        }
    }

    fn reset(&mut self) {
        debug_assert!(self.occupied == 0, "reset called on non-empty slab");
        self.bump_cursor = 0;
        self.free_head = SLOT_NONE;
    }
}

// =============================================================================
// Slab
// =============================================================================

/// A slab allocator with configurable growth mode.
///
/// Use [`DynamicSlab`] for growable or [`FixedSlab`] for bounded capacity.
pub struct Slab<T, const MODE: bool> {
    // Fixed mode: single contiguous mmap region (held for RAII)
    #[allow(dead_code)]
    fixed_pages: Option<sys::Pages>,
    fixed_slots: NonNull<Slot<T>>,

    // Dynamic mode: per-slab allocations (empty for Fixed)
    slab_pages: Vec<sys::Pages>,
    slab_bases: Vec<NonNull<Slot<T>>>,

    slabs: Vec<SlabMeta>,
    slots_capacity: usize,

    // List heads
    empty_head: u32,
    freelist_head: u32,
    current: u32,

    len: usize,
    slots_per_slab: u32,
    retire_threshold: u32,
    slab_bytes: usize, // Needed for dynamic growth
}

/// A growable slab allocator.
pub type DynamicSlab<T> = Slab<T, DYNAMIC>;

/// A fixed-capacity slab allocator.
pub type FixedSlab<T> = Slab<T, FIXED>;

unsafe impl<T: Send, const MODE: bool> Send for Slab<T, MODE> {}

impl<T> DynamicSlab<T> {
    /// Create a new dynamic slab with default settings.
    pub fn new() -> Result<Self, SlabError> {
        SlabBuilder::default().build()
    }
}

impl<T, const MODE: bool> Slab<T, MODE> {
    /// Returns the number of occupied slots.
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns true if no slots are occupied.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns the total slot capacity.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.slots_capacity
    }

    /// Returns the number of slabs.
    #[inline]
    pub fn slab_count(&self) -> usize {
        self.slabs.len()
    }

    /// Returns slots per slab.
    #[inline]
    pub fn slots_per_slab(&self) -> u32 {
        self.slots_per_slab
    }

    // -------------------------------------------------------------------------
    // Core Operations
    // -------------------------------------------------------------------------

    /// Insert a value, returning its key.
    ///
    /// # Errors
    ///
    /// Returns `Err(Full(value))` if the slab is at capacity (fixed mode only).
    pub fn insert(&mut self, value: T) -> Result<Key, Full<T>> {
        // 1. Bump from current slab
        if self.current != SLAB_NONE {
            let slab_idx = self.current;
            let meta = &self.slabs[slab_idx as usize];

            if meta.bump_cursor < self.slots_per_slab {
                // Check if we should retire early (prefer empty slab or grow for fresh bump)
                let can_retire = meta.occupied >= self.retire_threshold
                    && (self.empty_head != SLAB_NONE || MODE == DYNAMIC);

                if can_retire {
                    self.retire_current();
                    // Fall through to empty list / grow path
                } else {
                    // Continue bumping on current
                    let slot_idx = self.slabs[slab_idx as usize].bump_cursor;
                    self.slabs[slab_idx as usize].bump_cursor += 1;
                    self.slabs[slab_idx as usize].occupied += 1;
                    self.len += 1;

                    unsafe {
                        let ptr = self.slot_ptr(slab_idx, slot_idx);
                        ptr::write(ptr, Slot::Occupied { value });
                    }

                    return Ok(Key::new(slab_idx, slot_idx));
                }
            } else {
                // Bump exhausted, retire current
                self.retire_current();
            }
        }

        // 2. Empty slab → reset → bump
        if self.empty_head != SLAB_NONE {
            let slab_idx = self.pop_list(SlabState::Empty);
            self.slabs[slab_idx as usize].reset();
            self.slabs[slab_idx as usize].state = SlabState::Current;
            self.current = slab_idx;
            return self.insert(value);
        }

        // 3. Freelist from retired slab (all slabs above threshold)
        if self.freelist_head != SLAB_NONE {
            let slab_idx = self.freelist_head;
            let slot_idx = self.freelist_pop(slab_idx);

            self.slabs[slab_idx as usize].occupied += 1;
            self.len += 1;

            // Check if freelist exhausted
            if self.slabs[slab_idx as usize].free_head == SLOT_NONE {
                self.unlink(slab_idx);
                self.slabs[slab_idx as usize].state = SlabState::Full;
            }

            unsafe {
                let ptr = self.slot_ptr(slab_idx, slot_idx);
                ptr::write(ptr, Slot::Occupied { value });
            }

            return Ok(Key::new(slab_idx, slot_idx));
        }

        // 4. Grow (dynamic) or Full (fixed)
        if MODE == DYNAMIC {
            match self.grow() {
                Ok(slab_idx) => {
                    self.slabs[slab_idx as usize].state = SlabState::Current;
                    self.current = slab_idx;
                    return self.insert(value);
                }
                Err(_) => {}
            }
        }

        Err(Full(value))
    }

    /// Get a reference to the value at `key`.
    ///
    /// # Panics
    ///
    /// Panics if the key is invalid or the slot is vacant.
    #[inline]
    pub fn get(&self, key: Key) -> &T {
        let slab_idx = key.slab();
        let slot_idx = key.slot();

        assert!(
            (slab_idx as usize) < self.slabs.len(),
            "slab index out of bounds"
        );

        unsafe {
            let ptr = self.slot_ptr(slab_idx, slot_idx);
            match &*ptr {
                Slot::Occupied { value } => value,
                Slot::Vacant { .. } => panic!("get called on vacant slot"),
            }
        }
    }

    /// Get a mutable reference to the value at `key`.
    ///
    /// # Panics
    ///
    /// Panics if the key is invalid or the slot is vacant.
    #[inline]
    pub fn get_mut(&mut self, key: Key) -> &mut T {
        let slab_idx = key.slab();
        let slot_idx = key.slot();

        assert!(
            (slab_idx as usize) < self.slabs.len(),
            "slab index out of bounds"
        );

        unsafe {
            let ptr = self.slot_ptr(slab_idx, slot_idx);
            match &mut *ptr {
                Slot::Occupied { value } => value,
                Slot::Vacant { .. } => panic!("get_mut called on vacant slot"),
            }
        }
    }

    /// Remove and return the value at `key`.
    ///
    /// # Panics
    ///
    /// Panics if the key is invalid or the slot is vacant.
    pub fn remove(&mut self, key: Key) -> T {
        let slab_idx = key.slab();
        let slot_idx = key.slot();

        assert!(
            (slab_idx as usize) < self.slabs.len(),
            "slab index out of bounds"
        );

        let value = unsafe {
            let ptr = self.slot_ptr(slab_idx, slot_idx);
            match ptr::read(ptr) {
                Slot::Occupied { value } => value,
                Slot::Vacant { .. } => panic!("remove called on vacant slot"),
            }
        };

        // Read current state before mutation
        let old_state = self.slabs[slab_idx as usize].state;

        // Push to per-slab freelist
        self.freelist_push(slab_idx, slot_idx);
        self.slabs[slab_idx as usize].occupied -= 1;
        self.len -= 1;

        let new_occupied = self.slabs[slab_idx as usize].occupied;

        // State transitions
        if new_occupied == 0 {
            // Slab is now empty - move to empty list
            if old_state == SlabState::HasFreelist {
                self.unlink(slab_idx);
            } else if old_state == SlabState::Current {
                self.current = SLAB_NONE;
            }
            self.push_list(SlabState::Empty, slab_idx);
            self.slabs[slab_idx as usize].state = SlabState::Empty;
        } else if old_state == SlabState::Full {
            // Was full, now has freelist
            self.push_list(SlabState::HasFreelist, slab_idx);
            self.slabs[slab_idx as usize].state = SlabState::HasFreelist;
        }
        // If already HasFreelist or Current, no state change needed

        value
    }

    /// Returns true if the key points to an occupied slot.
    #[inline]
    pub fn contains(&self, key: Key) -> bool {
        let slab_idx = key.slab();
        let slot_idx = key.slot();

        if (slab_idx as usize) >= self.slabs.len() {
            return false;
        }

        if slot_idx >= self.slots_per_slab {
            return false;
        }

        unsafe {
            let ptr = self.slot_ptr(slab_idx, slot_idx);
            matches!(&*ptr, Slot::Occupied { .. })
        }
    }

    /// Remove all elements, resetting slabs for bump allocation.
    pub fn clear(&mut self) {
        // Drop all occupied values
        for slab_idx in 0..self.slabs.len() {
            let meta = &self.slabs[slab_idx];
            for slot_idx in 0..meta.bump_cursor {
                unsafe {
                    let ptr = self.slot_ptr(slab_idx as u32, slot_idx);
                    if matches!(&*ptr, Slot::Occupied { .. }) {
                        ptr::drop_in_place(ptr);
                    }
                }
            }
        }

        // Reset all slab metadata and rebuild empty list
        let num_slabs = self.slabs.len();
        for i in 0..num_slabs {
            self.slabs[i] = SlabMeta::new();
            self.slabs[i].prev = if i > 0 { (i - 1) as u32 } else { SLAB_NONE };
            self.slabs[i].next = if i < num_slabs - 1 {
                (i + 1) as u32
            } else {
                SLAB_NONE
            };
            self.slabs[i].state = SlabState::Empty;
        }

        self.empty_head = if num_slabs > 0 { 0 } else { SLAB_NONE };
        self.freelist_head = SLAB_NONE;
        self.current = SLAB_NONE;
        self.len = 0;
    }

    // -------------------------------------------------------------------------
    // Internal: Slot Access
    // -------------------------------------------------------------------------

    #[inline]
    unsafe fn slot_ptr(&self, slab_idx: u32, slot_idx: u32) -> *mut Slot<T> {
        if MODE == FIXED {
            // Contiguous block: global offset
            let global = (slab_idx as usize) * (self.slots_per_slab as usize) + (slot_idx as usize);
            debug_assert!(global < self.slots_capacity);
            unsafe { self.fixed_slots.as_ptr().add(global) }
        } else {
            // Per-slab: direct lookup
            debug_assert!((slab_idx as usize) < self.slab_bases.len());
            unsafe {
                self.slab_bases[slab_idx as usize]
                    .as_ptr()
                    .add(slot_idx as usize)
            }
        }
    }

    // -------------------------------------------------------------------------
    // Internal: Per-slab Freelist
    // -------------------------------------------------------------------------

    fn freelist_pop(&mut self, slab_idx: u32) -> u32 {
        let free_head = self.slabs[slab_idx as usize].free_head;
        debug_assert!(free_head != SLOT_NONE);

        let next = unsafe {
            let ptr = self.slot_ptr(slab_idx, free_head);
            match &*ptr {
                Slot::Vacant { next } => *next,
                Slot::Occupied { .. } => panic!("freelist corruption"),
            }
        };

        self.slabs[slab_idx as usize].free_head = next;
        free_head
    }

    fn freelist_push(&mut self, slab_idx: u32, slot_idx: u32) {
        let old_head = self.slabs[slab_idx as usize].free_head;

        unsafe {
            let ptr = self.slot_ptr(slab_idx, slot_idx);
            ptr::write(ptr, Slot::Vacant { next: old_head });
        }

        self.slabs[slab_idx as usize].free_head = slot_idx;
    }

    // -------------------------------------------------------------------------
    // Internal: List Operations
    // -------------------------------------------------------------------------

    fn list_head_mut(&mut self, state: SlabState) -> &mut u32 {
        match state {
            SlabState::Empty => &mut self.empty_head,
            SlabState::HasFreelist => &mut self.freelist_head,
            _ => panic!("invalid list state"),
        }
    }

    fn pop_list(&mut self, state: SlabState) -> u32 {
        let head = *self.list_head_mut(state);
        debug_assert!(head != SLAB_NONE);

        let next = self.slabs[head as usize].next;

        if next != SLAB_NONE {
            self.slabs[next as usize].prev = SLAB_NONE;
        }

        *self.list_head_mut(state) = next;
        self.slabs[head as usize].prev = SLAB_NONE;
        self.slabs[head as usize].next = SLAB_NONE;

        head
    }

    fn push_list(&mut self, state: SlabState, slab_idx: u32) {
        let old_head = *self.list_head_mut(state);

        self.slabs[slab_idx as usize].prev = SLAB_NONE;
        self.slabs[slab_idx as usize].next = old_head;

        if old_head != SLAB_NONE {
            self.slabs[old_head as usize].prev = slab_idx;
        }

        *self.list_head_mut(state) = slab_idx;
    }

    fn unlink(&mut self, slab_idx: u32) {
        let prev = self.slabs[slab_idx as usize].prev;
        let next = self.slabs[slab_idx as usize].next;
        let state = self.slabs[slab_idx as usize].state;

        if prev != SLAB_NONE {
            self.slabs[prev as usize].next = next;
        } else {
            // Was head
            *self.list_head_mut(state) = next;
        }

        if next != SLAB_NONE {
            self.slabs[next as usize].prev = prev;
        }

        self.slabs[slab_idx as usize].prev = SLAB_NONE;
        self.slabs[slab_idx as usize].next = SLAB_NONE;
    }

    // -------------------------------------------------------------------------
    // Internal: Current Slab Management
    // -------------------------------------------------------------------------

    fn retire_current(&mut self) {
        if self.current == SLAB_NONE {
            return;
        }

        let slab_idx = self.current;
        let meta = &self.slabs[slab_idx as usize];

        if meta.free_head != SLOT_NONE {
            // Has freelist entries
            self.slabs[slab_idx as usize].state = SlabState::HasFreelist;
            self.push_list(SlabState::HasFreelist, slab_idx);
        } else if meta.occupied == 0 {
            // Empty (shouldn't happen but handle it)
            self.slabs[slab_idx as usize].state = SlabState::Empty;
            self.push_list(SlabState::Empty, slab_idx);
        } else {
            // Full (no freelist, occupied > 0)
            self.slabs[slab_idx as usize].state = SlabState::Full;
        }

        self.current = SLAB_NONE;
    }

    // -------------------------------------------------------------------------
    // Internal: Growth (Dynamic mode only)
    // -------------------------------------------------------------------------

    fn grow(&mut self) -> Result<u32, SlabError> {
        debug_assert!(MODE == DYNAMIC, "grow called in fixed mode");

        // Allocate new slab
        let new_pages = sys::Pages::alloc(self.slab_bytes).map_err(SlabError::Allocation)?;
        let base = NonNull::new(new_pages.as_ptr() as *mut Slot<T>).expect("mmap returned null");

        let slab_idx = self.slabs.len() as u32;

        self.slab_pages.push(new_pages);
        self.slab_bases.push(base);
        self.slabs.push(SlabMeta::new());
        self.slots_capacity += self.slots_per_slab as usize;

        Ok(slab_idx)
    }
}

impl<T, const MODE: bool> Drop for Slab<T, MODE> {
    fn drop(&mut self) {
        // Drop all occupied values
        for slab_idx in 0..self.slabs.len() {
            let meta = &self.slabs[slab_idx];
            for slot_idx in 0..meta.bump_cursor {
                unsafe {
                    let ptr = self.slot_ptr(slab_idx as u32, slot_idx);
                    if matches!(&*ptr, Slot::Occupied { .. }) {
                        ptr::drop_in_place(ptr);
                    }
                }
            }
        }
        // Pages dropped automatically via RAII (both fixed_pages and slab_pages)
    }
}

// =============================================================================
// Builder
// =============================================================================

/// Builder for creating slabs.
#[derive(Default)]
pub struct SlabBuilder {
    capacity: Option<usize>,
    slab_megabytes: Option<usize>,
    retire_percent: Option<u8>,
    huge_pages: bool,
    mlock: bool,
}

impl SlabBuilder {
    /// Set the initial/maximum capacity in slots.
    ///
    /// For dynamic slabs, this is a hint for pre-allocation.
    /// For fixed slabs, this is required and sets the hard limit.
    pub fn capacity(mut self, capacity: usize) -> Self {
        self.capacity = Some(capacity);
        self
    }

    /// Set the slab size in megabytes (default: 2MB).
    pub fn slab_megabytes(mut self, mb: usize) -> Self {
        self.slab_megabytes = Some(mb);
        self
    }

    /// Set the retire threshold as a percentage (default: 75%).
    ///
    /// Slabs are retired when occupancy reaches this percentage, giving them
    /// a chance to drain completely and reset for bump allocation.
    pub fn retire_percent(mut self, percent: u8) -> Self {
        self.retire_percent = Some(percent.min(100));
        self
    }

    /// Use huge pages (MAP_HUGETLB on Linux).
    pub fn huge_pages(mut self, enabled: bool) -> Self {
        self.huge_pages = enabled;
        self
    }

    /// Lock pages in memory (mlock).
    pub fn mlock(mut self, enabled: bool) -> Self {
        self.mlock = enabled;
        self
    }

    /// Build a fixed-capacity slab.
    pub fn fixed(self) -> FixedSlabBuilder {
        FixedSlabBuilder { inner: self }
    }

    /// Build a dynamic (growable) slab.
    pub fn build<T>(self) -> Result<DynamicSlab<T>, SlabError> {
        self.build_impl()
    }

    fn build_impl<T, const MODE: bool>(self) -> Result<Slab<T, MODE>, SlabError> {
        let slab_bytes = self.slab_megabytes.unwrap_or(2) * 1024 * 1024;
        let slot_size = std::mem::size_of::<Slot<T>>().max(1);

        if slot_size > slab_bytes {
            return Err(SlabError::SlotTooLarge {
                slot_size,
                slab_size: slab_bytes,
            });
        }

        let slots_per_slab = (slab_bytes / slot_size) as u32;
        let retire_percent = self.retire_percent.unwrap_or(75) as u32;
        let retire_threshold = (slots_per_slab * retire_percent / 100).max(1);

        // Calculate number of slabs needed
        let capacity = self.capacity.unwrap_or(slots_per_slab as usize);
        if MODE == FIXED && capacity == 0 {
            return Err(SlabError::ZeroCapacity);
        }

        let num_slabs = (capacity + slots_per_slab as usize - 1) / slots_per_slab as usize;

        // Mode-specific initialization
        let (fixed_pages, fixed_slots, slab_pages, slab_bases, total_slots) = if MODE == FIXED {
            // Fixed: single contiguous allocation
            let total_slots = num_slabs * slots_per_slab as usize;
            let total_bytes = total_slots * slot_size;

            #[cfg(target_os = "linux")]
            let pages = if self.huge_pages {
                sys::Pages::alloc_hugetlb(total_bytes).map_err(SlabError::Allocation)?
            } else {
                sys::Pages::alloc(total_bytes).map_err(SlabError::Allocation)?
            };

            #[cfg(not(target_os = "linux"))]
            let pages = sys::Pages::alloc(total_bytes).map_err(SlabError::Allocation)?;

            if self.mlock {
                pages.mlock().map_err(SlabError::Allocation)?;
            }

            let slots = NonNull::new(pages.as_ptr() as *mut Slot<T>).expect("mmap returned null");

            (Some(pages), slots, Vec::new(), Vec::new(), total_slots)
        } else {
            // Dynamic: start with one slab, grow on demand
            let pages = sys::Pages::alloc(slab_bytes).map_err(SlabError::Allocation)?;
            let base = NonNull::new(pages.as_ptr() as *mut Slot<T>).expect("mmap returned null");

            // Dummy pointer for fixed_slots (never used in dynamic mode)
            let dummy = NonNull::dangling();

            (
                None,
                dummy,
                vec![pages],
                vec![base],
                slots_per_slab as usize,
            )
        };

        // Initialize slab metadata
        let actual_num_slabs = if MODE == FIXED { num_slabs } else { 1 };
        let mut slabs = Vec::with_capacity(actual_num_slabs);
        for i in 0..actual_num_slabs {
            let mut meta = SlabMeta::new();
            meta.prev = if i > 0 { (i - 1) as u32 } else { SLAB_NONE };
            meta.next = if i < actual_num_slabs - 1 {
                (i + 1) as u32
            } else {
                SLAB_NONE
            };
            meta.state = SlabState::Empty;
            slabs.push(meta);
        }

        // First slab becomes current
        let (current, empty_head) = if actual_num_slabs > 0 {
            slabs[0].state = SlabState::Current;
            slabs[0].prev = SLAB_NONE;
            slabs[0].next = SLAB_NONE;

            let empty_head = if actual_num_slabs > 1 {
                slabs[1].prev = SLAB_NONE;
                1
            } else {
                SLAB_NONE
            };

            (0, empty_head)
        } else {
            (SLAB_NONE, SLAB_NONE)
        };

        Ok(Slab {
            fixed_pages,
            fixed_slots,
            slab_pages,
            slab_bases,
            slabs,
            slots_capacity: total_slots,
            empty_head,
            freelist_head: SLAB_NONE,
            current,
            len: 0,
            slots_per_slab,
            retire_threshold,
            slab_bytes,
        })
    }
}

/// Builder for fixed-capacity slabs.
pub struct FixedSlabBuilder {
    inner: SlabBuilder,
}

impl FixedSlabBuilder {
    /// Set the maximum capacity in slots (required).
    pub fn capacity(mut self, capacity: usize) -> Self {
        self.inner.capacity = Some(capacity);
        self
    }

    /// Set the slab size in megabytes (default: 2MB).
    pub fn slab_megabytes(mut self, mb: usize) -> Self {
        self.inner.slab_megabytes = Some(mb);
        self
    }

    /// Set the retire threshold as a percentage (default: 75%).
    pub fn retire_percent(mut self, percent: u8) -> Self {
        self.inner.retire_percent = Some(percent.min(100));
        self
    }

    /// Use huge pages (MAP_HUGETLB on Linux).
    pub fn huge_pages(mut self, enabled: bool) -> Self {
        self.inner.huge_pages = enabled;
        self
    }

    /// Lock pages in memory (mlock).
    pub fn mlock(mut self, enabled: bool) -> Self {
        self.inner.mlock = enabled;
        self
    }

    /// Build the fixed-capacity slab.
    pub fn build<T>(self) -> Result<FixedSlab<T>, SlabError> {
        if self.inner.capacity.is_none() || self.inner.capacity == Some(0) {
            return Err(SlabError::ZeroCapacity);
        }
        self.inner.build_impl()
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use std::sync::atomic::{AtomicUsize, Ordering};

    #[test]
    fn basic_insert_get_remove() {
        let mut slab = DynamicSlab::<u64>::new().unwrap();

        let k1 = slab.insert(42).unwrap();
        let k2 = slab.insert(100).unwrap();

        assert_eq!(*slab.get(k1), 42);
        assert_eq!(*slab.get(k2), 100);
        assert_eq!(slab.len(), 2);

        assert_eq!(slab.remove(k1), 42);
        assert_eq!(slab.len(), 1);

        assert_eq!(slab.remove(k2), 100);
        assert!(slab.is_empty());
    }

    #[test]
    fn fixed_slab_full() {
        let mut slab: FixedSlab<u64> = SlabBuilder::default()
            .fixed()
            .capacity(100)
            .slab_megabytes(1)
            .build()
            .unwrap();

        let capacity = slab.capacity();

        // Fill to capacity
        for i in 0..capacity {
            slab.insert(i as u64).unwrap();
        }

        // Next insert should fail
        let result = slab.insert(9999);
        assert!(matches!(result, Err(Full(9999))));
    }

    #[test]
    fn reuse_after_remove() {
        let mut slab: FixedSlab<u64> = SlabBuilder::default()
            .fixed()
            .capacity(100)
            .build()
            .unwrap();

        let capacity = slab.capacity();

        // Fill
        let mut keys = Vec::new();
        for i in 0..capacity {
            keys.push(slab.insert(i as u64).unwrap());
        }

        // Remove one
        slab.remove(keys[50]);

        // Should be able to insert
        let new_key = slab.insert(999).unwrap();
        assert_eq!(*slab.get(new_key), 999);
    }

    #[test]
    fn drop_calls_destructors() {
        let drop_count = Arc::new(AtomicUsize::new(0));

        #[derive(Debug)]
        struct DropCounter(Arc<AtomicUsize>);
        impl Drop for DropCounter {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }

        {
            let mut slab = DynamicSlab::<DropCounter>::new().unwrap();
            for _ in 0..100 {
                slab.insert(DropCounter(drop_count.clone())).unwrap();
            }
        }

        assert_eq!(drop_count.load(Ordering::SeqCst), 100);
    }

    #[test]
    fn slab_becomes_empty_after_all_removes() {
        let mut slab: FixedSlab<u64> = SlabBuilder::default()
            .fixed()
            .capacity(1000)
            .slab_megabytes(1)
            .retire_percent(75)
            .build()
            .unwrap();

        // Insert some values
        let mut keys = Vec::new();
        for i in 0..100 {
            keys.push(slab.insert(i as u64).unwrap());
        }

        // Remove all
        for key in keys {
            slab.remove(key);
        }

        assert!(slab.is_empty());

        // Should be able to insert again (bump allocation)
        let k = slab.insert(42).unwrap();
        assert_eq!(*slab.get(k), 42);
    }

    #[test]
    fn clear_resets_for_bump() {
        let mut slab = DynamicSlab::<u64>::new().unwrap();

        // Fill with some values
        for i in 0..1000 {
            slab.insert(i).unwrap();
        }

        slab.clear();
        assert!(slab.is_empty());

        // Should be bump allocating again
        let k = slab.insert(42).unwrap();
        assert_eq!(*slab.get(k), 42);
    }

    #[test]
    fn dynamic_grows_beyond_initial() {
        let mut slab: DynamicSlab<u64> = SlabBuilder::default()
            .slab_megabytes(1) // Smaller slabs for faster test
            .build()
            .unwrap();

        let initial_capacity = slab.capacity();
        let initial_slabs = slab.slab_count();

        // Insert more than one slab's worth
        let target = initial_capacity + 1000;
        for i in 0..target {
            slab.insert(i as u64).unwrap();
        }

        assert!(slab.capacity() > initial_capacity);
        assert!(slab.slab_count() > initial_slabs);
        assert_eq!(slab.len(), target);

        // Verify values
        // (can't easily verify keys since we don't track them, but len is correct)
    }

    #[test]
    fn dynamic_growth_preserves_existing() {
        let mut slab = DynamicSlab::<u64>::new().unwrap();

        // Insert some values and track keys
        let mut keys = Vec::new();
        for i in 0..100 {
            keys.push(slab.insert(i as u64).unwrap());
        }

        // Force growth by inserting a lot more
        let initial_capacity = slab.capacity();
        while slab.capacity() == initial_capacity {
            slab.insert(999).unwrap();
        }

        // Original keys should still be valid
        for (i, key) in keys.iter().enumerate() {
            assert_eq!(*slab.get(*key), i as u64);
        }
    }
}
