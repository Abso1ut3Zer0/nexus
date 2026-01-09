//! # nexus-slab
//!
//! A high-performance slab allocator optimized for **predictable tail latency**.
//!
//! # Use Case
//!
//! Designed for latency-critical systems (trading, real-time, game servers) where
//! worst-case performance matters more than average-case throughput. Typical slab
//! allocators using `Vec` exhibit bimodal p999 latency due to reallocation copying;
//! `nexus-slab` provides consistent p999 by using independently-allocated slabs that
//! grow without copying existing data.
//!
//! # Performance Characteristics
//!
//! | Metric | nexus-slab | Typical Vec-based |
//! |--------|------------|-------------------|
//! | p50    | ~24 cycles | ~22 cycles        |
//! | p99    | ~28 cycles | ~24 cycles        |
//! | p999   | ~40-44 cycles (consistent) | 30-2400 cycles (bimodal) |
//! | max    | ~500-800K cycles (growth) | ~1.5-2M cycles (realloc+copy) |
//!
//! Trade a few cycles on median for **predictable** tail latency.
//!
//! # Architecture
//!
//! ## Two-Level Freelist
//!
//! ```text
//! slabs_head ─► Slab 2 ─► Slab 0 ─► NONE
//!                 │         │
//!                 ▼         ▼
//!              [slots]   [slots]     Slab 1 (full, not on freelist)
//! ```
//!
//! - **Slab freelist**: Which slabs have available space (O(1) lookup)
//! - **Slot freelist**: Which slots within a slab are free (per-slab, LIFO)
//!
//! ## Memory Layout
//!
//! ```text
//! Slab 0                        Slab 1
//! ┌─────────────────────┐       ┌─────────────────────┐
//! │ Slot 0              │       │ Slot 0              │
//! │ ┌─────┬───────────┐ │       │ ┌─────┬───────────┐ │
//! │ │ tag │   value   │ │       │ │ tag │   value   │ │
//! │ └─────┴───────────┘ │       │ └─────┴───────────┘ │
//! │ Slot 1              │       │ Slot 1              │
//! │ ┌─────┬───────────┐ │       │ ...                 │
//! │ │ tag │   value   │ │       └─────────────────────┘
//! │ └─────┴───────────┘ │
//! │ ...                 │       SlabMeta[]
//! └─────────────────────┘       ┌─────────────────────┐
//!                               │ bump_cursor: u32    │
//!                               │ occupied: u32       │
//!                               │ freelist_head: u32  │
//!                               │ next_free_slab: u32 │
//!                               └─────────────────────┘
//! ```
//!
//! ## Slot Tag Encoding
//!
//! Each slot has a `tag: u32` that serves double duty:
//!
//! - **Occupied**: `tag == SLOT_OCCUPIED` (0xFFFF_FFFE), value is valid
//! - **Vacant (end of chain)**: `tag == SLOT_NONE` (0xFFFF_FFFF)
//! - **Vacant (chained)**: `tag < slots_per_slab`, points to next free slot
//!
//! Freelists are **intra-slab only** - chains never cross slab boundaries.
//! This enables slabs to drain independently.
//!
//! ## Allocation Strategy
//!
//! 1. **Check slab freelist head** - O(1) access to a slab with space
//! 2. **Slot freelist first (LIFO)**: Reuse recently-freed slots for cache locality
//! 3. **Bump allocation**: Sequential allocation when slot freelist is empty
//! 4. **Pop exhausted slabs**: Remove from slab freelist when full
//! 5. **Growth**: Allocate new slab when all are full (dynamic mode only)
//!
//! ## Remove: LIFO Cache-Hot Behavior
//!
//! On remove, the freed slot is pushed onto the slab's freelist:
//!
//! ```text
//! Remove slot X from slab S:
//! ┌─────────────────────────────────────────────────────────┐
//! │ 1. Read value from X                                    │
//! │ 2. X.tag ← S.freelist_head (chain to old head)          │
//! │ 3. S.freelist_head ← X (freed slot becomes new head)    │
//! │ 4. If S was full: push S to front of slab freelist      │
//! └─────────────────────────────────────────────────────────┘
//! ```
//!
//! When a full slab gains a free slot, it's pushed to the **front** of the
//! slab freelist (LIFO), so the next insert uses cache-hot memory.
//!
//! ## Growth (Dynamic Mode)
//!
//! When the slab freelist is empty, a new slab is allocated and becomes
//! the freelist head. This cost is amortized over `slots_per_slab` allocations
//! (typically ~16K slots per 256KB slab for 16-byte values).
//!
//! # Example
//!
//! ```
//! use nexus_slab::DynamicSlab;
//!
//! let mut slab = DynamicSlab::with_capacity(1000).unwrap();
//!
//! let key = slab.insert(42);
//! assert_eq!(*slab.get(key), 42);
//!
//! let value = slab.remove(key);
//! assert_eq!(value, 42);
//! ```
//!
//! # Fixed vs Dynamic Mode
//!
//! - **Fixed**: Pre-allocates all memory upfront. Returns `Full` when exhausted.
//!   Use when capacity is known and you want zero allocation after init.
//!
//! - **Dynamic**: Grows by adding new slabs. Use when capacity is unbounded
//!   but growth is infrequent.

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

const DEFAULT_SLAB_BYTES: usize = 256 * 1024;

// =============================================================================
// Key
// =============================================================================

/// Opaque handle to an allocated slot.
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
    #[inline]
    pub const unsafe fn from_raw(value: u64) -> Self {
        Self(value)
    }

    /// Returns the raw u64 representation.
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
    /// Zero capacity requested.
    ZeroCapacity,
    /// OS memory allocation failed.
    Allocation(std::io::Error),
}

// =============================================================================
// Slot
// =============================================================================

// Sentinel value indicating slot is occupied (not a freelist pointer)
const SLOT_OCCUPIED: u32 = u32::MAX - 1;

/// Slot layout:
/// - Vacant: tag = next slot index (intra-slab) or SLOT_NONE for end of chain
/// - Occupied: tag = SLOT_OCCUPIED, value contains user data
#[repr(C)]
struct Slot<T> {
    tag: u32,
    value: std::mem::MaybeUninit<T>,
}

impl<T> Slot<T> {
    #[inline]
    fn is_occupied(&self) -> bool {
        self.tag == SLOT_OCCUPIED
    }
}

// =============================================================================
// VacantEntry
// =============================================================================

/// A vacant entry in the slab, allowing key inspection before insertion.
///
/// Useful for self-referential structures where the value needs to know its own key.
///
/// # Example
///
/// ```ignore
/// struct Node {
///     id: Key,
///     data: u64,
/// }
///
/// let mut slab = DynamicSlab::with_capacity(100)?;
/// let entry = slab.vacant_entry()?;
/// let key = entry.key();
/// entry.insert(Node { id: key, data: 42 });
/// ```
pub struct VacantEntry<'a, T, const MODE: bool> {
    slab: &'a mut Slab<T, MODE>,
    key: Key,
}

impl<'a, T, const MODE: bool> VacantEntry<'a, T, MODE> {
    /// Returns the key that will be assigned to the value once inserted.
    #[inline]
    pub fn key(&self) -> Key {
        self.key
    }

    /// Insert a value into the entry, consuming it.
    #[inline]
    pub fn insert(self, value: T) {
        let ptr = self.slab.slot_ptr_mut(self.key.slab(), self.key.slot());

        unsafe {
            (*ptr).tag = SLOT_OCCUPIED;
            (*ptr).value.write(value);
        }

        self.slab.len += 1;
        self.slab.slabs[self.key.slab() as usize].occupied += 1;
    }
}

// =============================================================================
// SlabMeta
// =============================================================================

struct SlabMeta {
    bump_cursor: u32,
    occupied: u32,
    freelist_head: u32, // Head of this slab's freelist, SLOT_NONE if empty
    next_free_slab: u32,
}

impl SlabMeta {
    const fn new() -> Self {
        Self {
            bump_cursor: 0,
            occupied: 0,
            freelist_head: SLOT_NONE,
            next_free_slab: SLAB_NONE,
        }
    }
}

// =============================================================================
// Slab
// =============================================================================

/// A slab allocator with configurable growth mode.
pub struct Slab<T, const MODE: bool> {
    slabs_head: u32,

    len: usize,
    max_len: usize, // For FIXED mode: user-requested capacity limit (0 = unlimited for DYNAMIC)
    slots_per_slab: u32,

    slabs: Vec<SlabMeta>,

    // Storage
    #[allow(dead_code)]
    fixed_pages: Option<sys::Pages>,
    slab_pages: Vec<sys::Pages>,
    slab_bases: Vec<NonNull<Slot<T>>>,

    slab_bytes: usize,
}

/// A growable slab allocator.
pub type DynamicSlab<T> = Slab<T, DYNAMIC>;

/// A fixed-capacity slab allocator.
pub type FixedSlab<T> = Slab<T, FIXED>;

unsafe impl<T: Send, const MODE: bool> Send for Slab<T, MODE> {}

impl<T> DynamicSlab<T> {
    /// Create a new dynamic slab with the given capacity hint.
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

        for _ in 0..num_slabs {
            let pages = sys::Pages::alloc(slab_bytes).map_err(SlabError::Allocation)?;
            let base = NonNull::new(pages.as_ptr() as *mut Slot<T>).expect("mmap returned null");

            slab_pages.push(pages);
            slab_bases.push(base);
            slabs.push(SlabMeta::new());
        }

        // Initialize slab freelist - all slabs except first go on freelist
        let mut slabs_head = SLAB_NONE;
        for i in (0..num_slabs).rev() {
            slabs[i].next_free_slab = slabs_head;
            slabs_head = i as u32;
        }

        Ok(Slab {
            slabs_head,
            len: 0,
            max_len: 0, // Dynamic mode: no limit
            slots_per_slab,
            slabs,
            fixed_pages: None,
            slab_pages,
            slab_bases,
            slab_bytes,
        })
    }
}

impl<T> Slab<T, DYNAMIC> {
    /// Insert a value, returning its key.
    ///
    /// Grows if needed. Panics on allocation failure.
    #[inline]
    pub fn insert(&mut self, value: T) -> Key {
        let (slab_idx, slot_idx) = self.alloc();
        self.write_slot(slab_idx, slot_idx, value)
    }

    /// Get a vacant entry for the next slot.
    ///
    /// Grows if needed. Panics on allocation failure.
    #[inline]
    pub fn vacant_entry(&mut self) -> VacantEntry<'_, T, DYNAMIC> {
        let (slab_idx, slot_idx) = self.alloc();
        VacantEntry {
            slab: self,
            key: Key::new(slab_idx, slot_idx),
        }
    }

    /// Allocate a slot. Grows if needed, panics on allocation failure.
    #[inline]
    fn alloc(&mut self) -> (u32, u32) {
        if self.slabs_head == SLAB_NONE {
            return self.alloc_grow();
        }

        let slab_idx = self.slabs_head;

        // Copy base pointer first to avoid borrow conflict with meta
        // SAFETY: slab_idx came from slabs_head which isn't SLAB_NONE,
        // so it's a valid index we created
        let base = unsafe { *self.slab_bases.get_unchecked(slab_idx as usize) };
        let meta = unsafe { self.slabs.get_unchecked_mut(slab_idx as usize) };

        let head = meta.freelist_head;
        if head != SLOT_NONE {
            // SAFETY: head came from freelist, so it's a valid slot index
            let ptr = unsafe { base.as_ptr().add(head as usize) };
            let next = unsafe { (*ptr).tag };
            meta.freelist_head = next;

            if next == SLOT_NONE && meta.bump_cursor >= self.slots_per_slab {
                self.slabs_head = meta.next_free_slab;
            }

            return (slab_idx, head);
        }

        let cursor = meta.bump_cursor;
        meta.bump_cursor = cursor + 1;

        if cursor + 1 >= self.slots_per_slab {
            self.slabs_head = meta.next_free_slab;
        }

        (slab_idx, cursor)
    }

    #[cold]
    #[inline(never)]
    fn alloc_grow(&mut self) -> (u32, u32) {
        let slab_idx = self.grow();
        self.slabs_head = slab_idx;
        self.slabs[slab_idx as usize].bump_cursor = 1;
        (slab_idx, 0)
    }

    /// Grow by adding a new slab. Panics on allocation failure.
    #[cold]
    #[inline(never)]
    fn grow(&mut self) -> u32 {
        let new_pages = sys::Pages::alloc(self.slab_bytes).expect("slab allocation failed");
        let base = NonNull::new(new_pages.as_ptr() as *mut Slot<T>).expect("alloc returned null");

        let slab_idx = self.slabs.len() as u32;

        self.slab_pages.push(new_pages);
        self.slab_bases.push(base);
        self.slabs.push(SlabMeta::new());

        slab_idx
    }
}

impl<T> Slab<T, FIXED> {
    /// Attempt to insert a value.
    ///
    /// Returns `Err(Full)` if at capacity.
    #[inline]
    pub fn try_insert(&mut self, value: T) -> Result<Key, Full<T>> {
        match self.alloc() {
            Some((slab_idx, slot_idx)) => Ok(self.write_slot(slab_idx, slot_idx, value)),
            None => Err(Full(value)),
        }
    }

    /// Attempt to get a vacant entry.
    ///
    /// Returns `None` if at capacity.
    #[inline]
    pub fn try_vacant_entry(&mut self) -> Option<VacantEntry<'_, T, FIXED>> {
        let (slab_idx, slot_idx) = self.alloc()?;
        Some(VacantEntry {
            slab: self,
            key: Key::new(slab_idx, slot_idx),
        })
    }

    /// Try to allocate a slot. Returns None if full.
    #[inline]
    fn alloc(&mut self) -> Option<(u32, u32)> {
        // Check user-requested capacity limit
        if self.len >= self.max_len {
            return None;
        }

        if self.slabs_head == SLAB_NONE {
            return None;
        }

        let slab_idx = self.slabs_head;

        // SAFETY: slab_idx came from slabs_head which isn't SLAB_NONE,
        // so it's a valid index we created
        let base = unsafe { *self.slab_bases.get_unchecked(slab_idx as usize) };
        let meta = unsafe { self.slabs.get_unchecked_mut(slab_idx as usize) };

        let head = meta.freelist_head;
        if head != SLOT_NONE {
            // SAFETY: head came from freelist, so it's a valid slot index
            let ptr = unsafe { base.as_ptr().add(head as usize) };
            let next = unsafe { (*ptr).tag };
            meta.freelist_head = next;

            if next == SLOT_NONE && meta.bump_cursor >= self.slots_per_slab {
                self.slabs_head = meta.next_free_slab;
            }

            return Some((slab_idx, head));
        }

        let cursor = meta.bump_cursor;
        meta.bump_cursor = cursor + 1;

        if cursor + 1 >= self.slots_per_slab {
            self.slabs_head = meta.next_free_slab;
        }

        Some((slab_idx, cursor))
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
        if MODE == FIXED && self.max_len > 0 {
            self.max_len
        } else {
            self.slabs.len() * self.slots_per_slab as usize
        }
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
    // Get
    // -------------------------------------------------------------------------

    /// Get a reference to the value at `key`.
    #[inline]
    pub fn get(&self, key: Key) -> &T {
        let slab_idx = key.slab();
        let slot_idx = key.slot();

        assert!(
            (slab_idx as usize) < self.slab_bases.len() && slot_idx < self.slots_per_slab,
            "invalid key: out of bounds"
        );

        // SAFETY: bounds verified above
        let base = unsafe { *self.slab_bases.get_unchecked(slab_idx as usize) };
        let ptr = unsafe { base.as_ptr().add(slot_idx as usize) };

        assert!(
            unsafe { (*ptr).is_occupied() },
            "invalid key: slot is vacant"
        );
        unsafe { (*ptr).value.assume_init_ref() }
    }

    /// Get a mutable reference to the value at `key`.
    #[inline]
    pub fn get_mut(&mut self, key: Key) -> &mut T {
        let slab_idx = key.slab();
        let slot_idx = key.slot();

        assert!(
            (slab_idx as usize) < self.slab_bases.len() && slot_idx < self.slots_per_slab,
            "invalid key: out of bounds"
        );

        let base = unsafe { *self.slab_bases.get_unchecked(slab_idx as usize) };
        let ptr = unsafe { base.as_ptr().add(slot_idx as usize) };

        assert!(
            unsafe { (*ptr).is_occupied() },
            "invalid key: slot is vacant"
        );
        unsafe { (*ptr).value.assume_init_mut() }
    }

    // -------------------------------------------------------------------------
    // Remove
    // -------------------------------------------------------------------------

    /// Remove and return the value at `key`.
    pub fn remove(&mut self, key: Key) -> T {
        let slab_idx = key.slab();
        let slot_idx = key.slot();

        assert!(
            (slab_idx as usize) < self.slab_bases.len() && slot_idx < self.slots_per_slab,
            "invalid key: out of bounds"
        );

        let base = unsafe { *self.slab_bases.get_unchecked(slab_idx as usize) };
        let ptr = unsafe { base.as_ptr().add(slot_idx as usize) };

        assert!(
            unsafe { (*ptr).is_occupied() },
            "invalid key: slot is vacant"
        );

        let value = unsafe { (*ptr).value.assume_init_read() };

        self.len -= 1;
        let meta = unsafe { self.slabs.get_unchecked_mut(slab_idx as usize) };

        let was_full = meta.freelist_head == SLOT_NONE && meta.bump_cursor >= self.slots_per_slab;

        unsafe {
            (*ptr).tag = meta.freelist_head;
        }
        meta.freelist_head = slot_idx;
        meta.occupied -= 1;

        if was_full {
            meta.next_free_slab = self.slabs_head;
            self.slabs_head = slab_idx;
        }

        value
    }

    /// Returns true if the key points to an occupied slot.
    pub fn contains(&self, key: Key) -> bool {
        let slab_idx = key.slab();
        let slot_idx = key.slot();

        // Return false for out of bounds, don't panic
        if slab_idx as usize >= self.slab_bases.len() || slot_idx >= self.slots_per_slab {
            return false;
        }

        let base = unsafe { *self.slab_bases.get_unchecked(slab_idx as usize) };
        let ptr = unsafe { base.as_ptr().add(slot_idx as usize) };

        unsafe { (*ptr).is_occupied() }
    }

    /// Remove all elements.
    pub fn clear(&mut self) {
        // Drop all occupied values
        for slab_idx in 0..self.slabs.len() {
            let meta = &self.slabs[slab_idx];
            for slot_idx in 0..meta.bump_cursor {
                unsafe {
                    let ptr = self.slot_ptr_mut(slab_idx as u32, slot_idx);
                    if (*ptr).is_occupied() {
                        ptr::drop_in_place((*ptr).value.as_mut_ptr());
                    }
                }
            }
        }

        // Reset metadata
        for meta in &mut self.slabs {
            *meta = SlabMeta::new();
        }

        // Rebuild slab freelist with all slabs
        self.slabs_head = 0;
        for i in 0..self.slabs.len() {
            self.slabs[i].next_free_slab = if i + 1 < self.slabs.len() {
                (i + 1) as u32
            } else {
                SLAB_NONE
            };
        }

        self.len = 0;
    }

    // -------------------------------------------------------------------------
    // Internal
    // -------------------------------------------------------------------------

    #[inline(always)]
    fn write_slot(&mut self, slab_idx: u32, slot_idx: u32, value: T) -> Key {
        // SAFETY: slab_idx/slot_idx came from alloc() which guarantees validity
        let base = unsafe { *self.slab_bases.get_unchecked(slab_idx as usize) };
        let ptr = unsafe { base.as_ptr().add(slot_idx as usize) };

        unsafe {
            (*ptr).tag = SLOT_OCCUPIED;
            (*ptr).value.write(value);
        }

        let meta = unsafe { self.slabs.get_unchecked_mut(slab_idx as usize) };
        meta.occupied += 1;
        self.len += 1;

        Key::new(slab_idx, slot_idx)
    }

    #[inline]
    fn slot_ptr(&self, slab_idx: u32, slot_idx: u32) -> *const Slot<T> {
        unsafe {
            self.slab_bases[slab_idx as usize]
                .as_ptr()
                .add(slot_idx as usize)
        }
    }

    #[inline]
    fn slot_ptr_mut(&mut self, slab_idx: u32, slot_idx: u32) -> *mut Slot<T> {
        self.slot_ptr(slab_idx, slot_idx) as *mut Slot<T>
    }
}

impl<T, const MODE: bool> Drop for Slab<T, MODE> {
    fn drop(&mut self) {
        for slab_idx in 0..self.slabs.len() {
            let meta = &self.slabs[slab_idx];
            for slot_idx in 0..meta.bump_cursor {
                unsafe {
                    let ptr = self.slot_ptr(slab_idx as u32, slot_idx);
                    if (*ptr).is_occupied() {
                        ptr::drop_in_place((*ptr.cast_mut()).value.as_mut_ptr());
                    }
                }
            }
        }
    }
}

// =============================================================================
// Builder
// =============================================================================

/// Builder for creating slabs with fine-grained control.
#[derive(Default)]
pub struct SlabBuilder {
    capacity: Option<usize>,
    slab_bytes: Option<usize>,
    #[cfg(unix)]
    huge_pages: bool,
    #[cfg(unix)]
    mlock: bool,
}

impl SlabBuilder {
    /// Create a new builder.
    pub fn new() -> Self {
        Self::default()
    }

    /// Set the initial capacity hint in slots.
    pub fn capacity(mut self, capacity: usize) -> Self {
        self.capacity = Some(capacity);
        self
    }

    /// Set the slab size in bytes.
    pub fn slab_bytes(mut self, bytes: usize) -> Self {
        self.slab_bytes = Some(bytes);
        self
    }

    /// Use huge pages (MAP_HUGETLB on Linux).
    #[cfg(unix)]
    pub fn huge_pages(mut self, enabled: bool) -> Self {
        self.huge_pages = enabled;
        self
    }

    /// Lock pages in memory (mlock).
    #[cfg(unix)]
    pub fn mlock(mut self, enabled: bool) -> Self {
        self.mlock = enabled;
        self
    }

    /// Build a fixed-capacity slab.
    pub fn fixed(self) -> FixedSlabBuilder {
        FixedSlabBuilder { inner: self }
    }

    /// Build a dynamic slab.
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

        let num_slabs = if let Some(cap) = self.capacity {
            (cap + slots_per_slab as usize - 1) / slots_per_slab as usize
        } else {
            1
        };

        if num_slabs == 0 {
            return Err(SlabError::ZeroCapacity);
        }

        let mut slab_pages = Vec::with_capacity(num_slabs);
        let mut slab_bases = Vec::with_capacity(num_slabs);
        let mut slabs = Vec::with_capacity(num_slabs);

        for _ in 0..num_slabs {
            // Change from #[cfg(target_os = "linux")] to:
            #[cfg(unix)]
            let pages = if self.huge_pages {
                sys::Pages::alloc_hugetlb(slab_bytes).map_err(SlabError::Allocation)?
            } else {
                sys::Pages::alloc(slab_bytes).map_err(SlabError::Allocation)?
            };

            #[cfg(not(unix))]
            let pages = sys::Pages::alloc(slab_bytes).map_err(SlabError::Allocation)?;

            #[cfg(unix)]
            if self.mlock {
                pages.mlock().map_err(SlabError::Allocation)?;
            }

            let base = NonNull::new(pages.as_ptr() as *mut Slot<T>).expect("alloc returned null");
            slab_pages.push(pages);
            slab_bases.push(base);
            slabs.push(SlabMeta::new());
        }

        // Initialize slab freelist - all slabs except first go on freelist
        let mut slabs_head = SLAB_NONE;
        for i in (0..num_slabs).rev() {
            slabs[i].next_free_slab = slabs_head;
            slabs_head = i as u32;
        }

        Ok(Slab {
            slabs_head,
            len: 0,
            max_len: 0, // Dynamic mode: no limit
            slots_per_slab,
            slabs,
            fixed_pages: None,
            slab_pages,
            slab_bases,
            slab_bytes,
        })
    }
}

/// Builder for fixed-capacity slabs.
pub struct FixedSlabBuilder {
    inner: SlabBuilder,
}

impl FixedSlabBuilder {
    /// Set the maximum capacity in slots.
    pub fn capacity(mut self, capacity: usize) -> Self {
        self.inner.capacity = Some(capacity);
        self
    }

    /// Set the slab size in bytes.
    pub fn slab_bytes(mut self, bytes: usize) -> Self {
        self.inner.slab_bytes = Some(bytes);
        self
    }

    /// Use huge pages.
    #[cfg(unix)]
    pub fn huge_pages(mut self, enabled: bool) -> Self {
        self.inner.huge_pages = enabled;
        self
    }

    /// Lock pages in memory.
    #[cfg(unix)]
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

        let mut slab_pages = Vec::with_capacity(num_slabs);
        let mut slab_bases = Vec::with_capacity(num_slabs);
        let mut slabs = Vec::with_capacity(num_slabs);

        for _ in 0..num_slabs {
            #[cfg(unix)]
            let pages = if self.inner.huge_pages {
                sys::Pages::alloc_hugetlb(slab_bytes).map_err(SlabError::Allocation)?
            } else {
                sys::Pages::alloc(slab_bytes).map_err(SlabError::Allocation)?
            };

            #[cfg(not(unix))]
            let pages = sys::Pages::alloc(slab_bytes).map_err(SlabError::Allocation)?;

            #[cfg(unix)]
            if self.inner.mlock {
                pages.mlock().map_err(SlabError::Allocation)?;
            }

            let base = NonNull::new(pages.as_ptr() as *mut Slot<T>).expect("alloc returned null");
            slab_pages.push(pages);
            slab_bases.push(base);
            slabs.push(SlabMeta::new());
        }

        // Initialize slab freelist
        let mut slabs_head = SLAB_NONE;
        for i in (0..num_slabs).rev() {
            slabs[i].next_free_slab = slabs_head;
            slabs_head = i as u32;
        }

        Ok(Slab {
            slabs_head,
            len: 0,
            max_len: capacity,
            slots_per_slab,
            slabs,
            fixed_pages: None,
            slab_pages,
            slab_bases,
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
    use std::collections::{HashMap, HashSet};
    use std::sync::Arc;
    use std::sync::atomic::{AtomicUsize, Ordering};

    // =========================================================================
    // Basic Operations
    // =========================================================================

    #[test]
    fn basic_insert_get_remove() {
        let mut slab = DynamicSlab::<u64>::with_capacity(100).unwrap();

        let k1 = slab.insert(42);
        let k2 = slab.insert(100);

        assert_eq!(*slab.get(k1), 42);
        assert_eq!(*slab.get(k2), 100);
        assert_eq!(slab.len(), 2);

        assert_eq!(slab.remove(k1), 42);
        assert_eq!(slab.len(), 1);

        assert_eq!(slab.remove(k2), 100);
        assert!(slab.is_empty());
    }

    #[test]
    fn get_mut_modifies_value() {
        let mut slab = DynamicSlab::<u64>::with_capacity(100).unwrap();

        let k = slab.insert(42);
        *slab.get_mut(k) = 100;

        assert_eq!(*slab.get(k), 100);
    }

    #[test]
    fn contains_returns_correct_state() {
        let mut slab = DynamicSlab::<u64>::with_capacity(100).unwrap();

        let k = slab.insert(42);
        assert!(slab.contains(k));

        slab.remove(k);
        assert!(!slab.contains(k));
    }

    #[test]
    fn contains_invalid_key_returns_false() {
        let slab = DynamicSlab::<u64>::with_capacity(100).unwrap();

        // Key pointing to non-existent slab
        let fake_key = Key::new(999, 0);
        assert!(!slab.contains(fake_key));

        // Key pointing to non-existent slot
        let fake_key2 = Key::new(0, 999999);
        assert!(!slab.contains(fake_key2));
    }

    #[test]
    fn vacant_entry_self_referential() {
        #[derive(Debug, PartialEq)]
        struct Node {
            id: Key,
            data: u64,
        }

        let mut slab = DynamicSlab::<Node>::with_capacity(100).unwrap();

        let entry = slab.vacant_entry();
        let key = entry.key();
        entry.insert(Node { id: key, data: 42 });

        let node = slab.get(key);
        assert_eq!(node.id, key);
        assert_eq!(node.data, 42);
    }

    #[test]
    fn vacant_entry_fixed_full() {
        let mut slab: FixedSlab<u64> = SlabBuilder::new().fixed().capacity(2).build().unwrap();

        let e1 = slab.try_vacant_entry().unwrap();
        e1.insert(1);

        let e2 = slab.try_vacant_entry().unwrap();
        e2.insert(2);

        assert!(slab.try_vacant_entry().is_none());
    }

    // =========================================================================
    // LIFO / Freelist Behavior
    // =========================================================================

    #[test]
    fn insert_after_remove_uses_freed_slot_lifo() {
        let mut slab = DynamicSlab::<u64>::with_capacity(100).unwrap();

        let _k1 = slab.insert(1);
        let k2 = slab.insert(2);
        let _k3 = slab.insert(3);

        // Remove k2 - this slot should be reused next (LIFO)
        slab.remove(k2);

        let k4 = slab.insert(4);
        assert_eq!(k4.slab(), k2.slab());
        assert_eq!(k4.slot(), k2.slot());
        assert_eq!(*slab.get(k4), 4);
    }

    #[test]
    fn freelist_chain_works_correctly() {
        let mut slab = DynamicSlab::<u64>::with_capacity(100).unwrap();

        // Insert several values
        let _k1 = slab.insert(1);
        let k2 = slab.insert(2);
        let k3 = slab.insert(3);
        let _k4 = slab.insert(4);

        // Remove in order: k2, k3 (builds chain k3 -> k2)
        slab.remove(k2);
        slab.remove(k3);

        // Insert should get k3 first (LIFO), then k2
        let new1 = slab.insert(10);
        let new2 = slab.insert(20);

        assert_eq!(new1.slot(), k3.slot());
        assert_eq!(new2.slot(), k2.slot());
        assert_eq!(*slab.get(new1), 10);
        assert_eq!(*slab.get(new2), 20);
    }

    #[test]
    fn multiple_removes_build_chain() {
        let mut slab = DynamicSlab::<u64>::with_capacity(1000).unwrap();

        // Insert 10 values
        let mut keys: Vec<Key> = Vec::new();
        for i in 0..10 {
            keys.push(slab.insert(i));
        }

        // Remove slots 2, 4, 6, 8 (even indices after 0)
        let removed: Vec<Key> = vec![keys[2], keys[4], keys[6], keys[8]];
        for &k in &removed {
            slab.remove(k);
        }

        // Reinsert 4 values - should get slots back in LIFO order
        let mut reinserted = Vec::new();
        for i in 0..4 {
            reinserted.push(slab.insert(100 + i));
        }

        // LIFO: last removed first
        assert_eq!(reinserted[0].slot(), keys[8].slot());
        assert_eq!(reinserted[1].slot(), keys[6].slot());
        assert_eq!(reinserted[2].slot(), keys[4].slot());
        assert_eq!(reinserted[3].slot(), keys[2].slot());
    }

    // =========================================================================
    // No Double Allocation (Critical Invariant)
    // =========================================================================

    #[test]
    fn no_double_allocation() {
        let mut slab = DynamicSlab::<u64>::with_capacity(1000).unwrap();
        let mut allocated_keys: HashSet<(u32, u32)> = HashSet::new();

        // Insert 500 values
        let mut keys = Vec::new();
        for i in 0..500 {
            let k = slab.insert(i);
            let key_tuple = (k.slab(), k.slot());
            assert!(
                !allocated_keys.contains(&key_tuple),
                "Double allocation detected on insert! slab={}, slot={}",
                k.slab(),
                k.slot()
            );
            allocated_keys.insert(key_tuple);
            keys.push(k);
        }

        // Remove every other one
        for i in (0..500).step_by(2) {
            let k = keys[i];
            allocated_keys.remove(&(k.slab(), k.slot()));
            slab.remove(k);
        }

        // Insert 250 more
        for i in 0..250 {
            let k = slab.insert(1000 + i);
            let key_tuple = (k.slab(), k.slot());
            assert!(
                !allocated_keys.contains(&key_tuple),
                "Double allocation detected on reinsert! slab={}, slot={}",
                k.slab(),
                k.slot()
            );
            allocated_keys.insert(key_tuple);
        }

        assert_eq!(slab.len(), 500);
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn no_double_allocation_stress() {
        let mut slab = DynamicSlab::<u64>::with_capacity(100).unwrap();
        let mut live_keys: HashMap<(u32, u32), u64> = HashMap::new();

        for round in 0..100 {
            // Insert batch
            for i in 0..50 {
                let val = (round * 1000 + i) as u64;
                let k = slab.insert(val);
                let key_tuple = (k.slab(), k.slot());

                if let Some(old_val) = live_keys.get(&key_tuple) {
                    panic!(
                        "Double allocation! slab={}, slot={} already has value {}, tried to insert {}",
                        k.slab(),
                        k.slot(),
                        old_val,
                        val
                    );
                }
                live_keys.insert(key_tuple, val);
            }

            // Remove some
            let keys_to_remove: Vec<_> = live_keys.keys().take(25).cloned().collect();

            for (slab_idx, slot_idx) in keys_to_remove {
                let key = Key::new(slab_idx, slot_idx);
                let val = slab.remove(key);
                let expected = live_keys.remove(&(slab_idx, slot_idx)).unwrap();
                assert_eq!(val, expected, "Value mismatch on remove");
            }
        }
    }

    // =========================================================================
    // Fixed Capacity
    // =========================================================================

    #[test]
    fn fixed_slab_full() {
        let mut slab: FixedSlab<u64> = SlabBuilder::new().fixed().capacity(100).build().unwrap();

        let capacity = slab.capacity();
        assert_eq!(capacity, 100);

        for i in 0..capacity {
            slab.try_insert(i as u64).unwrap();
        }

        let result = slab.try_insert(9999);
        assert!(matches!(result, Err(Full(9999))));
    }

    #[test]
    fn fixed_slab_reuse_after_remove() {
        let mut slab: FixedSlab<u64> = SlabBuilder::new().fixed().capacity(100).build().unwrap();

        let capacity = slab.capacity();

        let mut keys = Vec::new();
        for i in 0..capacity {
            keys.push(slab.try_insert(i as u64).unwrap());
        }

        // Full
        assert!(slab.try_insert(999).is_err());

        // Remove one
        slab.remove(keys[50]);

        // Can insert again
        let new_key = slab.try_insert(999).unwrap();
        assert_eq!(*slab.get(new_key), 999);

        // Full again
        assert!(slab.try_insert(1000).is_err());
    }

    // =========================================================================
    // Dynamic Growth
    // =========================================================================

    #[test]
    fn dynamic_grows() {
        let mut slab = DynamicSlab::<u64>::with_capacity(100).unwrap();

        let initial_capacity = slab.capacity();
        let initial_slabs = slab.slab_count();

        for i in 0..(initial_capacity + 1000) {
            slab.insert(i as u64);
        }

        assert!(slab.capacity() > initial_capacity);
        assert!(slab.slab_count() > initial_slabs);
    }

    #[test]
    fn dynamic_growth_preserves_existing_values() {
        let mut slab = DynamicSlab::<u64>::with_capacity(100).unwrap();

        let initial_capacity = slab.capacity();

        // Fill initial capacity
        let mut keys = Vec::new();
        for i in 0..initial_capacity {
            keys.push(slab.insert(i as u64));
        }

        // Force growth
        for i in 0..1000 {
            slab.insert((initial_capacity + i) as u64);
        }

        // Verify original values still accessible
        for (i, &k) in keys.iter().enumerate() {
            assert_eq!(*slab.get(k), i as u64);
        }
    }

    // =========================================================================
    // Cross-Slab Transitions (freelist_head save/restore)
    // =========================================================================

    #[test]
    fn slab_freelist_lifo_on_remove() {
        let mut slab: DynamicSlab<u64> = SlabBuilder::new().slab_bytes(4096).build().unwrap();

        let slots_per_slab = slab.slots_per_slab() as usize;

        // Fill slab 0 completely, spill into slab 1
        let mut keys = Vec::new();
        for i in 0..(slots_per_slab + 10) {
            keys.push(slab.insert(i as u64));
        }

        // Remove from slab 0 (was full) - pushes to front of slab freelist
        let k0 = keys[0];
        assert_eq!(k0.slab(), 0);
        slab.remove(k0);

        // Next insert should use slab 0 (LIFO)
        let new_key = slab.insert(999);
        assert_eq!(new_key.slab(), 0);
        assert_eq!(new_key.slot(), k0.slot()); // Reuses same slot
    }

    // =========================================================================
    // Clear
    // =========================================================================

    #[test]
    fn clear_resets_slab() {
        let mut slab = DynamicSlab::<u64>::with_capacity(100).unwrap();

        for i in 0..50 {
            slab.insert(i);
        }

        slab.clear();
        assert!(slab.is_empty());
        assert_eq!(slab.len(), 0);

        // Can insert again
        let k = slab.insert(42);
        assert_eq!(*slab.get(k), 42);
    }

    #[test]
    fn clear_calls_destructors() {
        let drop_count = Arc::new(AtomicUsize::new(0));

        #[derive(Debug)]
        struct DropCounter(Arc<AtomicUsize>);
        impl Drop for DropCounter {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }

        let mut slab = DynamicSlab::<DropCounter>::with_capacity(100).unwrap();
        for _ in 0..50 {
            slab.insert(DropCounter(drop_count.clone()));
        }

        assert_eq!(drop_count.load(Ordering::SeqCst), 0);

        slab.clear();

        assert_eq!(drop_count.load(Ordering::SeqCst), 50);
    }

    // =========================================================================
    // Drop
    // =========================================================================

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
                slab.insert(DropCounter(drop_count.clone()));
            }
        }

        assert_eq!(drop_count.load(Ordering::SeqCst), 100);
    }

    #[test]
    fn drop_only_drops_occupied_slots() {
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
            let mut keys = Vec::new();

            for _ in 0..100 {
                keys.push(slab.insert(DropCounter(drop_count.clone())));
            }

            // Remove 30 (these get dropped immediately)
            for i in 0..30 {
                slab.remove(keys[i]);
            }

            assert_eq!(drop_count.load(Ordering::SeqCst), 30);
        }

        // Remaining 70 dropped when slab is dropped
        assert_eq!(drop_count.load(Ordering::SeqCst), 100);
    }

    // =========================================================================
    // Key Operations
    // =========================================================================

    #[test]
    fn key_from_raw_roundtrip() {
        let mut slab = DynamicSlab::<u64>::with_capacity(100).unwrap();

        let k1 = slab.insert(42);
        let raw = k1.into_raw();

        let k2 = unsafe { Key::from_raw(raw) };
        assert_eq!(k1, k2);
        assert_eq!(*slab.get(k2), 42);
    }

    #[test]
    fn key_components() {
        let key = Key::new(5, 123);
        assert_eq!(key.slab(), 5);
        assert_eq!(key.slot(), 123);
    }

    // =========================================================================
    // Edge Cases
    // =========================================================================

    #[test]
    fn single_slot_capacity() {
        let mut slab: FixedSlab<u64> = SlabBuilder::new().fixed().capacity(1).build().unwrap();

        let k = slab.try_insert(42).unwrap();
        assert_eq!(*slab.get(k), 42);

        assert!(slab.try_insert(100).is_err());

        slab.remove(k);

        let k2 = slab.try_insert(100).unwrap();
        assert_eq!(*slab.get(k2), 100);
    }

    #[test]
    fn zero_sized_type() {
        let mut slab = DynamicSlab::<()>::with_capacity(1000).unwrap();

        let mut keys = Vec::new();
        for _ in 0..100 {
            keys.push(slab.insert(()));
        }

        assert_eq!(slab.len(), 100);

        for k in keys {
            slab.remove(k);
        }

        assert!(slab.is_empty());
    }

    #[test]
    fn large_value_type() {
        #[derive(Clone, PartialEq, Debug)]
        struct Large([u64; 64]); // 512 bytes

        let mut slab = DynamicSlab::<Large>::with_capacity(100).unwrap();

        let val = Large([42; 64]);
        let k = slab.insert(val.clone());

        assert_eq!(*slab.get(k), val);
    }

    // =========================================================================
    // Stress Tests
    // =========================================================================

    #[test]
    #[cfg_attr(miri, ignore)]
    fn stress_insert_remove_cycles() {
        let mut slab = DynamicSlab::<u64>::with_capacity(1000).unwrap();
        let mut keys: Vec<Key> = Vec::new();
        let mut expected: HashMap<(u32, u32), u64> = HashMap::new();

        for cycle in 0..100 {
            // Insert phase
            for i in 0..100 {
                let val = (cycle * 1000 + i) as u64;
                let k = slab.insert(val);
                keys.push(k);
                expected.insert((k.slab(), k.slot()), val);
            }

            // Verify all values
            for (&(s, sl), &val) in &expected {
                let k = Key::new(s, sl);
                assert_eq!(*slab.get(k), val);
            }

            // Remove half
            let drain_count = keys.len() / 2;
            for _ in 0..drain_count {
                let k = keys.pop().unwrap();
                let val = slab.remove(k);
                let expected_val = expected.remove(&(k.slab(), k.slot())).unwrap();
                assert_eq!(val, expected_val);
            }
        }
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn stress_random_operations() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        fn pseudo_random(seed: u64) -> u64 {
            let mut hasher = DefaultHasher::new();
            seed.hash(&mut hasher);
            hasher.finish()
        }

        let mut slab = DynamicSlab::<u64>::with_capacity(1000).unwrap();
        let mut live: HashMap<(u32, u32), u64> = HashMap::new();
        let mut seed = 12345u64;

        for _ in 0..10000 {
            seed = pseudo_random(seed);

            if live.is_empty() || seed % 3 != 0 {
                // Insert (2/3 probability when not empty)
                let val = seed;
                let k = slab.insert(val);
                live.insert((k.slab(), k.slot()), val);
            } else {
                // Remove (1/3 probability)
                let idx = (seed as usize) % live.len();
                let &(s, sl) = live.keys().nth(idx).unwrap();
                let k = Key::new(s, sl);
                let val = slab.remove(k);
                let expected = live.remove(&(s, sl)).unwrap();
                assert_eq!(val, expected);
            }
        }

        assert_eq!(slab.len(), live.len());
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn stress_fill_drain_cycles() {
        let mut slab: FixedSlab<u64> = SlabBuilder::new().fixed().capacity(500).build().unwrap();

        for cycle in 0..10 {
            // Fill completely
            let mut keys = Vec::new();
            for i in 0..500 {
                let k = slab.try_insert((cycle * 1000 + i) as u64).unwrap();
                keys.push(k);
            }

            assert!(slab.try_insert(0).is_err());
            assert_eq!(slab.len(), 500);

            // Verify all values
            for (i, &k) in keys.iter().enumerate() {
                assert_eq!(*slab.get(k), (cycle * 1000 + i) as u64);
            }

            // Drain completely
            for (i, k) in keys.into_iter().enumerate() {
                let val = slab.remove(k);
                assert_eq!(val, (cycle * 1000 + i) as u64);
            }

            assert!(slab.is_empty());
        }
    }

    // =========================================================================
    // Drain Behavior (Slab Reset)
    // =========================================================================

    #[test]
    fn slab_drains_to_empty() {
        let mut slab: DynamicSlab<u64> = SlabBuilder::new().slab_bytes(4096).build().unwrap();

        let slots_per_slab = slab.slots_per_slab() as usize;

        // Fill first slab
        let mut keys = Vec::new();
        for i in 0..slots_per_slab {
            let k = slab.insert(i as u64);
            assert_eq!(k.slab(), 0);
            keys.push(k);
        }

        assert_eq!(slab.len(), slots_per_slab);

        // Remove all from slab 0
        for k in keys {
            slab.remove(k);
        }

        // Slab should be empty
        assert_eq!(slab.len(), 0);
        assert!(slab.is_empty());
    }

    // =========================================================================
    // Builder Tests
    // =========================================================================

    #[test]
    fn builder_custom_slab_bytes() {
        let slab: DynamicSlab<u64> = SlabBuilder::new().slab_bytes(64 * 1024).build().unwrap();

        // Should have fewer slots per slab than default 256KB
        assert!(slab.slots_per_slab() < (256 * 1024 / 16) as u32);
    }

    #[test]
    fn builder_capacity() {
        let slab: DynamicSlab<u64> = SlabBuilder::new().capacity(10000).build().unwrap();

        assert!(slab.capacity() >= 10000);
    }

    #[test]
    fn builder_slot_too_large_error() {
        #[repr(C)]
        struct Huge([u8; 1024 * 1024]); // 1MB

        let result: Result<DynamicSlab<Huge>, SlabError> = SlabBuilder::new()
            .slab_bytes(4096) // 4KB slab
            .build();

        assert!(matches!(result, Err(SlabError::SlotTooLarge { .. })));
    }
}
