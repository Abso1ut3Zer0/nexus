//! # nexus-slab
//!
//! A high-performance slab allocator optimized for predictable latency.
//!
//! ## Design Philosophy
//!
//! This allocator prioritizes sequential "bump" allocation for cache locality,
//! falling back to LIFO freelist reuse. By tracking occupancy per slab, we can
//! detect when slabs fully drain and reset them for fresh bump allocation.
//!
//! ## Allocation Priority
//!
//! 1. **Bump** from current slab (sequential, cache-friendly)
//! 2. **Freelist** from current slab (LIFO, cache-hot)
//! 3. **Empty slab** → reset → bump (fresh sequential)
//! 4. **Freelist** from other slabs (scattered but no syscall)
//! 5. **Grow** new slab (dynamic only)
//!
//! ## Builder Tiers
//!
//! - [`Slab::with_capacity`] - Simple API, sane defaults, always dynamic
//! - [`SlabBuilder`] - Power user control over memory layout
//! - [`SlabBuilder::fixed`] - Pre-allocated bounded capacity

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

// Default slab size for simple API (256KB - small for drain recovery)
const DEFAULT_SLAB_BYTES: usize = 256 * 1024;

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

    /// Returns the slab index.
    #[inline]
    pub fn slab(self) -> u32 {
        (self.0 >> 32) as u32
    }

    /// Returns the slot index within the slab.
    #[inline]
    pub fn slot(self) -> u32 {
        self.0 as u32
    }

    /// Constructs a key from a raw u64 value.
    ///
    /// # Safety
    ///
    /// The caller must ensure the raw value represents a valid key
    /// that was previously obtained from this slab.
    #[inline]
    pub const unsafe fn from_raw(value: u64) -> Self {
        Self(value)
    }

    /// Returns the raw u64 representation of this key.
    #[inline]
    pub const fn into_raw(self) -> u64 {
        self.0
    }
}

// =============================================================================
// Errors
// =============================================================================

/// Returned when inserting into a full fixed-capacity slab.
#[derive(Debug)]
pub struct Full<T>(
    /// The value that could not be inserted.
    pub T,
);

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
    /// Zero capacity requested.
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
    /// Active slab for allocation
    Current,
    /// No occupied slots, can reset for bump
    Empty,
    /// Has freelist entries available
    HasFreelist,
    /// Fully exhausted (no bump, no freelist)
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

    // Dynamic mode: per-slab allocations
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
    slab_bytes: usize,
}

/// A growable slab allocator.
pub type DynamicSlab<T> = Slab<T, DYNAMIC>;

/// A fixed-capacity slab allocator.
pub type FixedSlab<T> = Slab<T, FIXED>;

unsafe impl<T: Send, const MODE: bool> Send for Slab<T, MODE> {}

impl<T> DynamicSlab<T> {
    /// Create a new dynamic slab with the given capacity hint.
    ///
    /// This is the simple API with sane defaults:
    /// - Pre-allocates enough slabs to hold `capacity` items
    /// - Uses 256KB slabs (good balance for drain recovery)
    /// - Grows automatically when needed
    ///
    /// For more control, use [`SlabBuilder`].
    pub fn with_capacity(capacity: usize) -> Result<Self, SlabError> {
        if capacity == 0 {
            return Err(SlabError::ZeroCapacity);
        }

        let slot_size = std::mem::size_of::<Slot<T>>().max(1);
        let slab_bytes = DEFAULT_SLAB_BYTES;

        if slot_size > slab_bytes {
            return Err(SlabError::SlotTooLarge {
                slot_size,
                slab_size: slab_bytes,
            });
        }

        let slots_per_slab = slab_bytes / slot_size;
        let num_slabs = (capacity + slots_per_slab - 1) / slots_per_slab;

        Self::build_dynamic(slab_bytes, slots_per_slab as u32, num_slabs)
    }

    fn build_dynamic(
        slab_bytes: usize,
        slots_per_slab: u32,
        num_slabs: usize,
    ) -> Result<Self, SlabError> {
        let num_slabs = num_slabs.max(1);

        let mut slab_pages = Vec::with_capacity(num_slabs);
        let mut slab_bases = Vec::with_capacity(num_slabs);
        let mut slabs = Vec::with_capacity(num_slabs);

        for i in 0..num_slabs {
            let pages = sys::Pages::alloc(slab_bytes).map_err(SlabError::Allocation)?;
            let base = NonNull::new(pages.as_ptr() as *mut Slot<T>).expect("mmap returned null");

            slab_pages.push(pages);
            slab_bases.push(base);

            let mut meta = SlabMeta::new();
            meta.prev = if i > 0 { (i - 1) as u32 } else { SLAB_NONE };
            meta.next = if i < num_slabs - 1 {
                (i + 1) as u32
            } else {
                SLAB_NONE
            };
            meta.state = SlabState::Empty;
            slabs.push(meta);
        }

        // First slab becomes current
        slabs[0].state = SlabState::Current;
        slabs[0].prev = SLAB_NONE;
        slabs[0].next = SLAB_NONE;

        let empty_head = if num_slabs > 1 {
            slabs[1].prev = SLAB_NONE;
            1
        } else {
            SLAB_NONE
        };

        Ok(Slab {
            fixed_pages: None,
            fixed_slots: NonNull::dangling(),
            slab_pages,
            slab_bases,
            slabs,
            slots_capacity: num_slabs * slots_per_slab as usize,
            empty_head,
            freelist_head: SLAB_NONE,
            current: 0,
            len: 0,
            slots_per_slab,
            slab_bytes,
        })
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
        if self.current != SLAB_NONE {
            let slab_idx = self.current;
            let meta = &self.slabs[slab_idx as usize];

            // 1. Bump from current (sequential)
            if meta.bump_cursor < self.slots_per_slab {
                return Ok(self.bump_alloc(slab_idx, value));
            }

            // 2. Freelist from current (LIFO, cache-hot)
            if meta.free_head != SLOT_NONE {
                return Ok(self.freelist_alloc(slab_idx, value));
            }

            // Current exhausted → retire to Full
            self.slabs[slab_idx as usize].state = SlabState::Full;
            self.current = SLAB_NONE;
        }

        // 3. Empty slab → reset → bump
        if self.empty_head != SLAB_NONE {
            let slab_idx = self.pop_list(SlabState::Empty);
            self.slabs[slab_idx as usize].reset();
            self.slabs[slab_idx as usize].state = SlabState::Current;
            self.current = slab_idx;
            return Ok(self.bump_alloc(slab_idx, value));
        }

        // 4. Freelist from other slabs
        if self.freelist_head != SLAB_NONE {
            let slab_idx = self.freelist_head;
            let key = self.freelist_alloc(slab_idx, value);

            // Check if slab's freelist exhausted
            if self.slabs[slab_idx as usize].free_head == SLOT_NONE {
                self.unlink(slab_idx);
                self.slabs[slab_idx as usize].state = SlabState::Full;
            }

            return Ok(key);
        }

        // 5. Grow (dynamic) or Full (fixed)
        if MODE == DYNAMIC {
            match self.grow() {
                Ok(slab_idx) => {
                    self.slabs[slab_idx as usize].state = SlabState::Current;
                    self.current = slab_idx;
                    return Ok(self.bump_alloc(slab_idx, value));
                }
                Err(_) => {}
            }
        }

        Err(Full(value))
    }

    #[inline]
    fn bump_alloc(&mut self, slab_idx: u32, value: T) -> Key {
        let slot_idx = self.slabs[slab_idx as usize].bump_cursor;
        self.slabs[slab_idx as usize].bump_cursor += 1;
        self.slabs[slab_idx as usize].occupied += 1;
        self.len += 1;

        unsafe {
            let ptr = self.slot_ptr(slab_idx, slot_idx);
            ptr::write(ptr, Slot::Occupied { value });
        }

        Key::new(slab_idx, slot_idx)
    }

    #[inline]
    fn freelist_alloc(&mut self, slab_idx: u32, value: T) -> Key {
        let slot_idx = self.freelist_pop(slab_idx);
        self.slabs[slab_idx as usize].occupied += 1;
        self.len += 1;

        unsafe {
            let ptr = self.slot_ptr(slab_idx, slot_idx);
            ptr::write(ptr, Slot::Occupied { value });
        }

        Key::new(slab_idx, slot_idx)
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

        let old_state = self.slabs[slab_idx as usize].state;

        // Push to per-slab freelist
        self.freelist_push(slab_idx, slot_idx);
        self.slabs[slab_idx as usize].occupied -= 1;
        self.len -= 1;

        let new_occupied = self.slabs[slab_idx as usize].occupied;

        // State transitions
        if new_occupied == 0 {
            // Slab is now empty
            match old_state {
                SlabState::HasFreelist => self.unlink(slab_idx),
                SlabState::Current => self.current = SLAB_NONE,
                _ => {}
            }
            self.push_list(SlabState::Empty, slab_idx);
            self.slabs[slab_idx as usize].state = SlabState::Empty;
        } else if old_state == SlabState::Full {
            // Was full, now has freelist
            self.push_list(SlabState::HasFreelist, slab_idx);
            self.slabs[slab_idx as usize].state = SlabState::HasFreelist;
        }

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

        // Reset all metadata and rebuild empty list
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

        // First slab becomes current
        if num_slabs > 0 {
            self.slabs[0].state = SlabState::Current;
            self.slabs[0].prev = SLAB_NONE;
            self.slabs[0].next = SLAB_NONE;
            self.current = 0;

            self.empty_head = if num_slabs > 1 {
                self.slabs[1].prev = SLAB_NONE;
                1
            } else {
                SLAB_NONE
            };
        } else {
            self.current = SLAB_NONE;
            self.empty_head = SLAB_NONE;
        }

        self.freelist_head = SLAB_NONE;
        self.len = 0;
    }

    // -------------------------------------------------------------------------
    // Internal: Slot Access
    // -------------------------------------------------------------------------

    #[inline]
    unsafe fn slot_ptr(&self, slab_idx: u32, slot_idx: u32) -> *mut Slot<T> {
        if MODE == FIXED {
            let global = (slab_idx as usize) * (self.slots_per_slab as usize) + (slot_idx as usize);
            debug_assert!(global < self.slots_capacity);
            unsafe { self.fixed_slots.as_ptr().add(global) }
        } else {
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
            *self.list_head_mut(state) = next;
        }

        if next != SLAB_NONE {
            self.slabs[next as usize].prev = prev;
        }

        self.slabs[slab_idx as usize].prev = SLAB_NONE;
        self.slabs[slab_idx as usize].next = SLAB_NONE;
    }

    // -------------------------------------------------------------------------
    // Internal: Growth (Dynamic mode only)
    // -------------------------------------------------------------------------

    fn grow(&mut self) -> Result<u32, SlabError> {
        debug_assert!(MODE == DYNAMIC, "grow called in fixed mode");

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
    }
}

// =============================================================================
// Builder (Power User)
// =============================================================================

/// Builder for creating slabs with fine-grained control.
///
/// For simple usage, prefer [`DynamicSlab::with_capacity`].
#[derive(Default)]
pub struct SlabBuilder {
    capacity: Option<usize>,
    slab_bytes: Option<usize>,
    num_slabs: Option<usize>,
    huge_pages: bool,
    mlock: bool,
}

impl SlabBuilder {
    /// Create a new builder.
    pub fn new() -> Self {
        Self::default()
    }

    /// Set the initial capacity hint in slots.
    ///
    /// For dynamic slabs, this determines pre-allocation.
    /// For fixed slabs, this sets the hard limit.
    pub fn capacity(mut self, capacity: usize) -> Self {
        self.capacity = Some(capacity);
        self
    }

    /// Set the slab size in bytes (default: 256KB).
    ///
    /// Smaller slabs drain faster (more bump recovery).
    /// Larger slabs may benefit from THP (2MB+).
    pub fn slab_bytes(mut self, bytes: usize) -> Self {
        self.slab_bytes = Some(bytes);
        self
    }

    /// Set the number of slabs to pre-allocate.
    ///
    /// Overrides calculation from capacity.
    pub fn num_slabs(mut self, n: usize) -> Self {
        self.num_slabs = Some(n);
        self
    }

    /// Use huge pages (MAP_HUGETLB on Linux).
    ///
    /// Requires slab_bytes to be a multiple of huge page size.
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
    ///
    /// Fixed slabs use a single contiguous allocation and never grow.
    pub fn fixed(self) -> FixedSlabBuilder {
        FixedSlabBuilder { inner: self }
    }

    /// Build a dynamic (growable) slab.
    pub fn build<T>(self) -> Result<DynamicSlab<T>, SlabError> {
        let slab_bytes = self.slab_bytes.unwrap_or(DEFAULT_SLAB_BYTES);
        let slot_size = std::mem::size_of::<Slot<T>>().max(1);

        if slot_size > slab_bytes {
            return Err(SlabError::SlotTooLarge {
                slot_size,
                slab_size: slab_bytes,
            });
        }

        let slots_per_slab = (slab_bytes / slot_size) as u32;

        let num_slabs = if let Some(n) = self.num_slabs {
            n
        } else if let Some(cap) = self.capacity {
            (cap + slots_per_slab as usize - 1) / slots_per_slab as usize
        } else {
            1
        };

        if num_slabs == 0 {
            return Err(SlabError::ZeroCapacity);
        }

        // Build with possible huge pages / mlock
        let mut slab_pages = Vec::with_capacity(num_slabs);
        let mut slab_bases = Vec::with_capacity(num_slabs);
        let mut slabs = Vec::with_capacity(num_slabs);

        for i in 0..num_slabs {
            #[cfg(target_os = "linux")]
            let pages = if self.huge_pages {
                sys::Pages::alloc_hugetlb(slab_bytes).map_err(SlabError::Allocation)?
            } else {
                sys::Pages::alloc(slab_bytes).map_err(SlabError::Allocation)?
            };

            #[cfg(not(target_os = "linux"))]
            let pages = sys::Pages::alloc(slab_bytes).map_err(SlabError::Allocation)?;

            if self.mlock {
                pages.mlock().map_err(SlabError::Allocation)?;
            }

            let base = NonNull::new(pages.as_ptr() as *mut Slot<T>).expect("mmap returned null");

            slab_pages.push(pages);
            slab_bases.push(base);

            let mut meta = SlabMeta::new();
            meta.prev = if i > 0 { (i - 1) as u32 } else { SLAB_NONE };
            meta.next = if i < num_slabs - 1 {
                (i + 1) as u32
            } else {
                SLAB_NONE
            };
            meta.state = SlabState::Empty;
            slabs.push(meta);
        }

        slabs[0].state = SlabState::Current;
        slabs[0].prev = SLAB_NONE;
        slabs[0].next = SLAB_NONE;

        let empty_head = if num_slabs > 1 {
            slabs[1].prev = SLAB_NONE;
            1
        } else {
            SLAB_NONE
        };

        Ok(Slab {
            fixed_pages: None,
            fixed_slots: NonNull::dangling(),
            slab_pages,
            slab_bases,
            slabs,
            slots_capacity: num_slabs * slots_per_slab as usize,
            empty_head,
            freelist_head: SLAB_NONE,
            current: 0,
            len: 0,
            slots_per_slab,
            slab_bytes,
        })
    }
}

// =============================================================================
// FixedSlabBuilder
// =============================================================================

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

    /// Set the slab size in bytes.
    pub fn slab_bytes(mut self, bytes: usize) -> Self {
        self.inner.slab_bytes = Some(bytes);
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
        let capacity = self.inner.capacity.ok_or(SlabError::ZeroCapacity)?;
        if capacity == 0 {
            return Err(SlabError::ZeroCapacity);
        }

        let slab_bytes = self.inner.slab_bytes.unwrap_or(DEFAULT_SLAB_BYTES);
        let slot_size = std::mem::size_of::<Slot<T>>().max(1);

        if slot_size > slab_bytes {
            return Err(SlabError::SlotTooLarge {
                slot_size,
                slab_size: slab_bytes,
            });
        }

        let slots_per_slab = (slab_bytes / slot_size) as u32;
        let num_slabs = (capacity + slots_per_slab as usize - 1) / slots_per_slab as usize;
        let total_slots = num_slabs * slots_per_slab as usize;
        let total_bytes = total_slots * slot_size;

        // Single contiguous allocation
        #[cfg(target_os = "linux")]
        let pages = if self.inner.huge_pages {
            sys::Pages::alloc_hugetlb(total_bytes).map_err(SlabError::Allocation)?
        } else {
            sys::Pages::alloc(total_bytes).map_err(SlabError::Allocation)?
        };

        #[cfg(not(target_os = "linux"))]
        let pages = sys::Pages::alloc(total_bytes).map_err(SlabError::Allocation)?;

        if self.inner.mlock {
            pages.mlock().map_err(SlabError::Allocation)?;
        }

        let slots = NonNull::new(pages.as_ptr() as *mut Slot<T>).expect("mmap returned null");

        // Initialize slab metadata
        let mut slabs = Vec::with_capacity(num_slabs);
        for i in 0..num_slabs {
            let mut meta = SlabMeta::new();
            meta.prev = if i > 0 { (i - 1) as u32 } else { SLAB_NONE };
            meta.next = if i < num_slabs - 1 {
                (i + 1) as u32
            } else {
                SLAB_NONE
            };
            meta.state = SlabState::Empty;
            slabs.push(meta);
        }

        slabs[0].state = SlabState::Current;
        slabs[0].prev = SLAB_NONE;
        slabs[0].next = SLAB_NONE;

        let empty_head = if num_slabs > 1 {
            slabs[1].prev = SLAB_NONE;
            1
        } else {
            SLAB_NONE
        };

        Ok(Slab {
            fixed_pages: Some(pages),
            fixed_slots: slots,
            slab_pages: Vec::new(),
            slab_bases: Vec::new(),
            slabs,
            slots_capacity: total_slots,
            empty_head,
            freelist_head: SLAB_NONE,
            current: 0,
            len: 0,
            slots_per_slab,
            slab_bytes,
        })
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
        let mut slab = DynamicSlab::<u64>::with_capacity(100).unwrap();

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
    fn simple_api() {
        let mut slab = DynamicSlab::<String>::with_capacity(1000).unwrap();

        let k = slab.insert("hello".to_string()).unwrap();
        assert_eq!(slab.get(k), "hello");
    }

    #[test]
    fn fixed_slab_full() {
        let mut slab: FixedSlab<u64> = SlabBuilder::new().fixed().capacity(100).build().unwrap();

        let capacity = slab.capacity();

        for i in 0..capacity {
            slab.insert(i as u64).unwrap();
        }

        let result = slab.insert(9999);
        assert!(matches!(result, Err(Full(9999))));
    }

    #[test]
    fn reuse_after_remove() {
        let mut slab: FixedSlab<u64> = SlabBuilder::new().fixed().capacity(100).build().unwrap();

        let capacity = slab.capacity();

        let mut keys = Vec::new();
        for i in 0..capacity {
            keys.push(slab.insert(i as u64).unwrap());
        }

        slab.remove(keys[50]);

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
            let mut slab = DynamicSlab::<DropCounter>::with_capacity(100).unwrap();
            for _ in 0..100 {
                slab.insert(DropCounter(drop_count.clone())).unwrap();
            }
        }

        assert_eq!(drop_count.load(Ordering::SeqCst), 100);
    }

    #[test]
    fn slab_drains_to_empty() {
        let mut slab = DynamicSlab::<u64>::with_capacity(100).unwrap();

        let mut keys = Vec::new();
        for i in 0..100 {
            keys.push(slab.insert(i as u64).unwrap());
        }

        for key in keys {
            slab.remove(key);
        }

        assert!(slab.is_empty());

        // Should bump allocate again
        let k = slab.insert(42).unwrap();
        assert_eq!(*slab.get(k), 42);
    }

    #[test]
    fn clear_resets_for_bump() {
        let mut slab = DynamicSlab::<u64>::with_capacity(1000).unwrap();

        for i in 0..500 {
            slab.insert(i).unwrap();
        }

        slab.clear();
        assert!(slab.is_empty());

        let k = slab.insert(42).unwrap();
        assert_eq!(*slab.get(k), 42);
    }

    #[test]
    fn dynamic_grows() {
        let mut slab = DynamicSlab::<u64>::with_capacity(100).unwrap();

        let initial_capacity = slab.capacity();
        let initial_slabs = slab.slab_count();

        // Insert beyond initial capacity
        for i in 0..(initial_capacity + 1000) {
            slab.insert(i as u64).unwrap();
        }

        assert!(slab.capacity() > initial_capacity);
        assert!(slab.slab_count() > initial_slabs);
    }

    #[test]
    fn key_from_raw() {
        let mut slab = DynamicSlab::<u64>::with_capacity(100).unwrap();

        let k1 = slab.insert(42).unwrap();
        let raw = k1.into_raw();

        let k2 = unsafe { Key::from_raw(raw) };
        assert_eq!(*slab.get(k2), 42);
    }

    #[test]
    fn key_accessors() {
        let key = Key::new(5, 10);
        assert_eq!(key.slab(), 5);
        assert_eq!(key.slot(), 10);
    }

    #[test]
    fn power_user_builder() {
        let slab: DynamicSlab<u64> = SlabBuilder::new()
            .capacity(10000)
            .slab_bytes(512 * 1024) // 512KB slabs
            .build()
            .unwrap();

        assert!(slab.capacity() >= 10000);
    }

    #[test]
    fn contains() {
        let mut slab = DynamicSlab::<u64>::with_capacity(100).unwrap();

        let k = slab.insert(42).unwrap();
        assert!(slab.contains(k));

        slab.remove(k);
        assert!(!slab.contains(k));
    }
}
