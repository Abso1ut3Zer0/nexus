//! # nexus-slab
//!
//! A high-performance slab allocator optimized for **predictable tail latency**.
//!
//! # Use Case
//!
//! Designed for latency-critical systems (trading, real-time, game servers) where
//! worst-case performance matters more than average-case throughput. Typical slab
//! allocators using `Vec` exhibit bimodal p999 latency due to reallocation copying;
//! `nexus-slab` provides consistent p999 by using mmap-backed slabs that grow
//! independently.
//!
//! # Performance Characteristics
//!
//! | Metric | nexus-slab | Typical Vec-based |
//! |--------|------------|-------------------|
//! | p50    | ~26 cycles | ~22 cycles        |
//! | p99    | ~32 cycles | ~24 cycles        |
//! | p999   | ~50-60 cycles (consistent) | 40-3000 cycles (bimodal) |
//! | max    | ~500-800K cycles (mmap) | ~1.5-2M cycles (realloc+copy) |
//!
//! Trade a few cycles on median for **predictable** tail latency.
//!
//! # Architecture
//!
//! ## Memory Layout
//!
//! ```text
//! Slab 0 (mmap region)          Slab 1 (mmap region)
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
//! ## Two-Pointer Allocation
//!
//! The allocator maintains two slot positions:
//!
//! - `current`: The slot that will be used on the **next insert**
//! - `next`: The slot that will become `current` **after** that insert
//!
//! ```text
//! Insert flow:
//! ┌─────────────────────────────────────────────────────────┐
//! │ 1. Write value to current slot                         │
//! │ 2. Mark slot as OCCUPIED                               │
//! │ 3. current ← next                                      │
//! │ 4. Compute new next (follow chain or bump allocate)    │
//! └─────────────────────────────────────────────────────────┘
//! ```
//!
//! This design pre-computes the next allocation point, keeping the hot path
//! to a simple write + pointer advance.
//!
//! ## Per-Slab Freelists & Draining
//!
//! Each slab maintains its own freelist via `SlabMeta::freelist_head`.
//! When allocation switches to a different slab (due to remove), the old
//! slab's freelist head is preserved:
//!
//! ```text
//! Remove from Slab B while current is in Slab A:
//! ┌─────────────────────────────────────────────────────────┐
//! │ 1. Save: slabs[A].freelist_head ← current_slot         │
//! │ 2. Freed slot in B becomes new current                 │
//! │ 3. Future inserts stay in B until exhausted            │
//! │ 4. When B exhausted, can return to A via freelist_head │
//! └─────────────────────────────────────────────────────────┘
//! ```
//!
//! This concentrates allocation activity in fewer slabs, allowing inactive
//! slabs to drain. When `occupied == 0`, a slab can be reset to bump
//! allocation (sequential memory access pattern).
//!
//! ## Remove: LIFO Cache-Hot Behavior
//!
//! On remove, the freed slot becomes `current` immediately:
//!
//! ```text
//! Remove slot X:
//! ┌─────────────────────────────────────────────────────────┐
//! │ 1. Read value from X                                   │
//! │ 2. Chain: X.tag ← current_slot (if same slab)          │
//! │         or X.tag ← SLOT_NONE (if different slab)       │
//! │ 3. current ← X (just-freed slot, still in L1 cache)    │
//! │ 4. Compute new next                                    │
//! └─────────────────────────────────────────────────────────┘
//! ```
//!
//! LIFO reuse means the next insert writes to cache-hot memory, reducing
//! cache misses on high-churn workloads.
//!
//! ## Growth (Dynamic Mode)
//!
//! When all slabs are exhausted:
//!
//! 1. `mmap` a new slab region (~500K cycles, rare)
//! 2. Initialize first slot, set as `current`
//! 3. Continue with bump allocation
//!
//! Mmap cost is amortized over `slots_per_slab` allocations (typically
//! ~16K slots per 256KB slab for 16-byte values).
//!
//! ## Advance Next Algorithm
//!
//! `advance_next()` determines where to allocate after the current slot:
//!
//! ```text
//! 1. If current.tag is a valid chain pointer → next = chain target
//! 2. Else if current slab has bump room → next = bump allocate
//! 3. Else scan other slabs:
//!    a. Check freelist_head (saved chains from previous visits)
//!    b. Check bump cursors
//! 4. If nothing found → next = NONE (will trigger grow on insert)
//! ```
//!
//! Preference for staying in the current slab maintains cache locality
//! and enables draining of other slabs.
//!
//! # Example
//!
//! ```ignore
//! use nexus_slab::DynamicSlab;
//!
//! let mut slab = DynamicSlab::with_capacity(1000)?;
//!
//! let key = slab.insert(42)?;
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
//! - **Dynamic**: Grows by adding new slabs. Each growth is an mmap syscall.
//!   Use when capacity is unbounded but growth is infrequent.

#![warn(missing_docs)]

use std::ptr::{self, NonNull};

mod sys;

// =============================================================================
// Constants
// =============================================================================

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
}

impl SlabMeta {
    const fn new() -> Self {
        Self {
            bump_cursor: 0,
            occupied: 0,
            freelist_head: SLOT_NONE,
        }
    }
}

// =============================================================================
// Slab
// =============================================================================

/// A slab allocator with configurable growth mode.
pub struct Slab<T, const MODE: bool> {
    // Which slab to try first on insert (locality hint)
    active_slab: u32,

    len: usize,
    max_len: usize, // For FIXED mode: user-requested capacity limit (0 = unlimited for DYNAMIC)
    slots_per_slab: u32,

    slabs: Vec<SlabMeta>,

    // Storage
    #[allow(dead_code)]
    fixed_pages: Option<sys::Pages>,
    fixed_slots: NonNull<Slot<T>>,
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

        Ok(Slab {
            active_slab: 0,
            len: 0,
            max_len: 0, // Dynamic mode: no limit
            slots_per_slab,
            slabs,
            fixed_pages: None,
            fixed_slots: NonNull::dangling(),
            slab_pages,
            slab_bases,
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
    // Insert
    // -------------------------------------------------------------------------

    /// Insert a value, returning its key.
    #[inline]
    pub fn insert(&mut self, value: T) -> Result<Key, Full<T>> {
        // For FIXED mode, check capacity limit
        if MODE == FIXED && self.max_len > 0 && self.len >= self.max_len {
            return Err(Full(value));
        }

        // Try active slab first (locality)
        if let Some((slab_idx, slot_idx)) = self.alloc_from_slab(self.active_slab as usize) {
            return self.write_slot(slab_idx, slot_idx, value);
        }

        // Try other slabs
        for idx in 0..self.slabs.len() {
            if idx == self.active_slab as usize {
                continue;
            }
            if let Some((slab_idx, slot_idx)) = self.alloc_from_slab(idx) {
                self.active_slab = slab_idx;
                return self.write_slot(slab_idx, slot_idx, value);
            }
        }

        // Try to grow (dynamic mode only)
        if MODE == DYNAMIC {
            if let Ok(slab_idx) = self.grow() {
                self.active_slab = slab_idx;
                let slot_idx = 0;
                self.slabs[slab_idx as usize].bump_cursor = 1;
                return self.write_slot(slab_idx, slot_idx, value);
            }
        }

        Err(Full(value))
    }

    /// Get a vacant entry, allowing key inspection before insertion.
    ///
    /// Returns `Err(Full(()))` if the slab is full (fixed mode only).
    #[inline]
    pub fn vacant_entry(&mut self) -> Result<VacantEntry<'_, T, MODE>, Full<()>> {
        // For FIXED mode, check capacity limit
        if MODE == FIXED && self.max_len > 0 && self.len >= self.max_len {
            return Err(Full(()));
        }

        // Try active slab first (locality)
        if let Some((slab_idx, slot_idx)) = self.alloc_from_slab(self.active_slab as usize) {
            return Ok(VacantEntry {
                slab: self,
                key: Key::new(slab_idx, slot_idx),
            });
        }

        // Try other slabs
        for idx in 0..self.slabs.len() {
            if idx == self.active_slab as usize {
                continue;
            }
            if let Some((slab_idx, slot_idx)) = self.alloc_from_slab(idx) {
                self.active_slab = slab_idx;
                return Ok(VacantEntry {
                    slab: self,
                    key: Key::new(slab_idx, slot_idx),
                });
            }
        }

        // Try to grow (dynamic mode only)
        if MODE == DYNAMIC {
            if let Ok(slab_idx) = self.grow() {
                self.active_slab = slab_idx;
                let slot_idx = 0;
                self.slabs[slab_idx as usize].bump_cursor = 1;
                return Ok(VacantEntry {
                    slab: self,
                    key: Key::new(slab_idx, slot_idx),
                });
            }
        }

        Err(Full(()))
    }

    /// Try to allocate a slot from the given slab.
    /// Returns Some((slab_idx, slot_idx)) if successful.
    #[inline(always)]
    fn alloc_from_slab(&mut self, idx: usize) -> Option<(u32, u32)> {
        // SAFETY: idx is either active_slab (always valid) or from bounded loop
        let (head, cursor) = unsafe {
            let meta = self.slabs.get_unchecked(idx);
            (meta.freelist_head, meta.bump_cursor)
        };

        if head != SLOT_NONE {
            // SAFETY: freelist_head is valid slot index when not SLOT_NONE
            let ptr = unsafe { self.slot_ptr_unchecked(idx as u32, head) };
            let next = unsafe { (*ptr).tag };
            unsafe { self.slabs.get_unchecked_mut(idx).freelist_head = next };
            return Some((idx as u32, head));
        }

        if cursor < self.slots_per_slab {
            unsafe { self.slabs.get_unchecked_mut(idx).bump_cursor = cursor + 1 };
            return Some((idx as u32, cursor));
        }

        None
    }

    #[inline(always)]
    fn write_slot(&mut self, slab_idx: u32, slot_idx: u32, value: T) -> Result<Key, Full<T>> {
        // SAFETY: slab_idx/slot_idx from alloc_from_slab, always valid
        let ptr = unsafe { self.slot_ptr_unchecked_mut(slab_idx, slot_idx) };

        unsafe {
            (*ptr).tag = SLOT_OCCUPIED;
            (*ptr).value.write(value);
        }

        self.len += 1;
        // SAFETY: slab_idx from alloc_from_slab, always valid
        unsafe { self.slabs.get_unchecked_mut(slab_idx as usize).occupied += 1 };

        Ok(Key::new(slab_idx, slot_idx))
    }

    // -------------------------------------------------------------------------
    // Get
    // -------------------------------------------------------------------------

    /// Get a reference to the value at `key`.
    #[inline]
    pub fn get(&self, key: Key) -> &T {
        let ptr = self.slot_ptr(key.slab(), key.slot());

        unsafe {
            let slot = &*ptr;
            assert!(slot.is_occupied(), "get called on vacant slot");
            slot.value.assume_init_ref()
        }
    }

    /// Get a mutable reference to the value at `key`.
    #[inline]
    pub fn get_mut(&mut self, key: Key) -> &mut T {
        let ptr = self.slot_ptr_mut(key.slab(), key.slot());

        unsafe {
            let slot = &mut *ptr;
            assert!(slot.is_occupied(), "get_mut called on vacant slot");
            slot.value.assume_init_mut()
        }
    }

    // -------------------------------------------------------------------------
    // Remove
    // -------------------------------------------------------------------------

    /// Remove and return the value at `key`.
    pub fn remove(&mut self, key: Key) -> T {
        let slab_idx = key.slab();
        let slot_idx = key.slot();
        let ptr = self.slot_ptr_mut(slab_idx, slot_idx);

        let value = unsafe {
            let slot = &*ptr;
            assert!(slot.is_occupied(), "remove called on vacant slot");
            slot.value.assume_init_read()
        };

        self.len -= 1;
        let meta = &mut self.slabs[slab_idx as usize];
        meta.occupied -= 1;

        // Push onto this slab's freelist
        unsafe {
            (*ptr).tag = meta.freelist_head;
        }
        meta.freelist_head = slot_idx;

        // Hint: prefer this slab next (cache-hot)
        self.active_slab = slab_idx;

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
            (*ptr).is_occupied()
        }
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

        self.active_slab = 0;
        self.len = 0;
    }

    // -------------------------------------------------------------------------
    // Internal: Slot Access
    // -------------------------------------------------------------------------

    #[inline]
    fn slot_ptr(&self, slab_idx: u32, slot_idx: u32) -> *const Slot<T> {
        if MODE == FIXED {
            let global = (slab_idx as usize) * (self.slots_per_slab as usize) + (slot_idx as usize);
            unsafe { self.fixed_slots.as_ptr().add(global) }
        } else {
            unsafe {
                self.slab_bases[slab_idx as usize]
                    .as_ptr()
                    .add(slot_idx as usize)
            }
        }
    }

    #[inline]
    fn slot_ptr_mut(&mut self, slab_idx: u32, slot_idx: u32) -> *mut Slot<T> {
        self.slot_ptr(slab_idx, slot_idx) as *mut Slot<T>
    }

    /// Unchecked slot pointer - caller guarantees valid indices
    #[inline(always)]
    unsafe fn slot_ptr_unchecked(&self, slab_idx: u32, slot_idx: u32) -> *const Slot<T> {
        if MODE == FIXED {
            let global = (slab_idx as usize) * (self.slots_per_slab as usize) + (slot_idx as usize);
            unsafe { self.fixed_slots.as_ptr().add(global) }
        } else {
            unsafe {
                self.slab_bases
                    .get_unchecked(slab_idx as usize)
                    .as_ptr()
                    .add(slot_idx as usize)
            }
        }
    }

    #[inline(always)]
    unsafe fn slot_ptr_unchecked_mut(&mut self, slab_idx: u32, slot_idx: u32) -> *mut Slot<T> {
        unsafe { self.slot_ptr_unchecked(slab_idx, slot_idx) as *mut _ }
    }

    // -------------------------------------------------------------------------
    // Internal: Growth
    // -------------------------------------------------------------------------

    fn grow(&mut self) -> Result<u32, SlabError> {
        let new_pages = sys::Pages::alloc(self.slab_bytes).map_err(SlabError::Allocation)?;
        let base = NonNull::new(new_pages.as_ptr() as *mut Slot<T>).expect("mmap returned null");

        let slab_idx = self.slabs.len() as u32;

        self.slab_pages.push(new_pages);
        self.slab_bases.push(base);
        self.slabs.push(SlabMeta::new());

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
    pub fn capacity(mut self, capacity: usize) -> Self {
        self.capacity = Some(capacity);
        self
    }

    /// Set the slab size in bytes.
    pub fn slab_bytes(mut self, bytes: usize) -> Self {
        self.slab_bytes = Some(bytes);
        self
    }

    /// Set the number of slabs to pre-allocate.
    pub fn num_slabs(mut self, n: usize) -> Self {
        self.num_slabs = Some(n);
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

        let mut slab_pages = Vec::with_capacity(num_slabs);
        let mut slab_bases = Vec::with_capacity(num_slabs);
        let mut slabs = Vec::with_capacity(num_slabs);

        for _ in 0..num_slabs {
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
            slabs.push(SlabMeta::new());
        }

        Ok(Slab {
            active_slab: 0,
            len: 0,
            max_len: 0, // Dynamic mode: no limit
            slots_per_slab,
            slabs,
            fixed_pages: None,
            fixed_slots: NonNull::dangling(),
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
    pub fn huge_pages(mut self, enabled: bool) -> Self {
        self.inner.huge_pages = enabled;
        self
    }

    /// Lock pages in memory.
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

        let mut slabs = Vec::with_capacity(num_slabs);
        for _ in 0..num_slabs {
            slabs.push(SlabMeta::new());
        }

        Ok(Slab {
            active_slab: 0,
            len: 0,
            max_len: capacity, // Fixed mode: enforce user-requested capacity
            slots_per_slab,
            slabs,
            fixed_pages: Some(pages),
            fixed_slots: slots,
            slab_pages: Vec::new(),
            slab_bases: Vec::new(),
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
    fn get_mut_modifies_value() {
        let mut slab = DynamicSlab::<u64>::with_capacity(100).unwrap();

        let k = slab.insert(42).unwrap();
        *slab.get_mut(k) = 100;

        assert_eq!(*slab.get(k), 100);
    }

    #[test]
    fn contains_returns_correct_state() {
        let mut slab = DynamicSlab::<u64>::with_capacity(100).unwrap();

        let k = slab.insert(42).unwrap();
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

        let entry = slab.vacant_entry().unwrap();
        let key = entry.key();
        entry.insert(Node { id: key, data: 42 });

        let node = slab.get(key);
        assert_eq!(node.id, key);
        assert_eq!(node.data, 42);
    }

    #[test]
    fn vacant_entry_fixed_full() {
        let mut slab: FixedSlab<u64> = SlabBuilder::new().fixed().capacity(2).build().unwrap();

        let e1 = slab.vacant_entry().unwrap();
        e1.insert(1);

        let e2 = slab.vacant_entry().unwrap();
        e2.insert(2);

        assert!(slab.vacant_entry().is_err());
    }

    // =========================================================================
    // LIFO / Freelist Behavior
    // =========================================================================

    #[test]
    fn insert_after_remove_uses_freed_slot_lifo() {
        let mut slab = DynamicSlab::<u64>::with_capacity(100).unwrap();

        let _k1 = slab.insert(1).unwrap();
        let k2 = slab.insert(2).unwrap();
        let _k3 = slab.insert(3).unwrap();

        // Remove k2 - this slot should be reused next (LIFO)
        slab.remove(k2);

        let k4 = slab.insert(4).unwrap();
        assert_eq!(k4.slab(), k2.slab());
        assert_eq!(k4.slot(), k2.slot());
        assert_eq!(*slab.get(k4), 4);
    }

    #[test]
    fn freelist_chain_works_correctly() {
        let mut slab = DynamicSlab::<u64>::with_capacity(100).unwrap();

        // Insert several values
        let _k1 = slab.insert(1).unwrap();
        let k2 = slab.insert(2).unwrap();
        let k3 = slab.insert(3).unwrap();
        let _k4 = slab.insert(4).unwrap();

        // Remove in order: k2, k3 (builds chain k3 -> k2)
        slab.remove(k2);
        slab.remove(k3);

        // Insert should get k3 first (LIFO), then k2
        let new1 = slab.insert(10).unwrap();
        let new2 = slab.insert(20).unwrap();

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
            keys.push(slab.insert(i).unwrap());
        }

        // Remove slots 2, 4, 6, 8 (even indices after 0)
        let removed: Vec<Key> = vec![keys[2], keys[4], keys[6], keys[8]];
        for &k in &removed {
            slab.remove(k);
        }

        // Reinsert 4 values - should get slots back in LIFO order
        let mut reinserted = Vec::new();
        for i in 0..4 {
            reinserted.push(slab.insert(100 + i).unwrap());
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
            let k = slab.insert(i).unwrap();
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
            let k = slab.insert(1000 + i).unwrap();
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
    fn no_double_allocation_stress() {
        let mut slab = DynamicSlab::<u64>::with_capacity(100).unwrap();
        let mut live_keys: HashMap<(u32, u32), u64> = HashMap::new();

        for round in 0..100 {
            // Insert batch
            for i in 0..50 {
                let val = (round * 1000 + i) as u64;
                let k = slab.insert(val).unwrap();
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
            slab.insert(i as u64).unwrap();
        }

        let result = slab.insert(9999);
        assert!(matches!(result, Err(Full(9999))));
    }

    #[test]
    fn fixed_slab_reuse_after_remove() {
        let mut slab: FixedSlab<u64> = SlabBuilder::new().fixed().capacity(100).build().unwrap();

        let capacity = slab.capacity();

        let mut keys = Vec::new();
        for i in 0..capacity {
            keys.push(slab.insert(i as u64).unwrap());
        }

        // Full
        assert!(slab.insert(999).is_err());

        // Remove one
        slab.remove(keys[50]);

        // Can insert again
        let new_key = slab.insert(999).unwrap();
        assert_eq!(*slab.get(new_key), 999);

        // Full again
        assert!(slab.insert(1000).is_err());
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
            slab.insert(i as u64).unwrap();
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
            keys.push(slab.insert(i as u64).unwrap());
        }

        // Force growth
        for i in 0..1000 {
            slab.insert((initial_capacity + i) as u64).unwrap();
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
    fn cross_slab_freelist_preserved() {
        // Use small slab size to force multiple slabs
        let mut slab: DynamicSlab<u64> = SlabBuilder::new()
            .slab_bytes(4096) // Small slabs: 4096 / 16 = 256 slots per slab
            .build()
            .unwrap();

        let slots_per_slab = slab.slots_per_slab() as usize;

        // Fill first slab completely and start second
        let mut keys_slab0 = Vec::new();
        let mut keys_slab1 = Vec::new();

        for i in 0..(slots_per_slab + 10) {
            let k = slab.insert(i as u64).unwrap();
            if k.slab() == 0 {
                keys_slab0.push(k);
            } else {
                keys_slab1.push(k);
            }
        }

        // Remove some from slab 0 (builds freelist there)
        let removed_from_0: Vec<Key> = keys_slab0.iter().take(5).cloned().collect();
        for &k in &removed_from_0 {
            slab.remove(k);
        }

        // Remove from slab 1 - this switches current slab
        // Slab 0's freelist should be saved to freelist_head
        let k1 = keys_slab1[0];
        slab.remove(k1);

        // Insert - should use slab 1's freed slot first
        let new1 = slab.insert(999).unwrap();
        assert_eq!(new1.slab(), k1.slab());

        // Now exhaust slab 1's remaining bump room
        // Slab 1 had 10 slots used, 1 freed and reused, so ~246 bump slots remain
        // Insert enough to exhaust it and force find_next_slot to check freelist_head
        let mut found_slab0 = false;
        for _ in 0..(slots_per_slab + 50) {
            let k = slab.insert(0).unwrap();
            if k.slab() == 0 {
                found_slab0 = true;
                break;
            }
        }

        assert!(found_slab0, "Should have returned to slab 0's freelist");
    }

    // =========================================================================
    // Clear
    // =========================================================================

    #[test]
    fn clear_resets_slab() {
        let mut slab = DynamicSlab::<u64>::with_capacity(100).unwrap();

        for i in 0..50 {
            slab.insert(i).unwrap();
        }

        slab.clear();
        assert!(slab.is_empty());
        assert_eq!(slab.len(), 0);

        // Can insert again
        let k = slab.insert(42).unwrap();
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
            slab.insert(DropCounter(drop_count.clone())).unwrap();
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
                slab.insert(DropCounter(drop_count.clone())).unwrap();
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
                keys.push(slab.insert(DropCounter(drop_count.clone())).unwrap());
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

        let k1 = slab.insert(42).unwrap();
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

        let k = slab.insert(42).unwrap();
        assert_eq!(*slab.get(k), 42);

        assert!(slab.insert(100).is_err());

        slab.remove(k);

        let k2 = slab.insert(100).unwrap();
        assert_eq!(*slab.get(k2), 100);
    }

    #[test]
    fn zero_sized_type() {
        let mut slab = DynamicSlab::<()>::with_capacity(1000).unwrap();

        let mut keys = Vec::new();
        for _ in 0..100 {
            keys.push(slab.insert(()).unwrap());
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
        let k = slab.insert(val.clone()).unwrap();

        assert_eq!(*slab.get(k), val);
    }

    // =========================================================================
    // Stress Tests
    // =========================================================================

    #[test]
    fn stress_insert_remove_cycles() {
        let mut slab = DynamicSlab::<u64>::with_capacity(1000).unwrap();
        let mut keys: Vec<Key> = Vec::new();
        let mut expected: HashMap<(u32, u32), u64> = HashMap::new();

        for cycle in 0..100 {
            // Insert phase
            for i in 0..100 {
                let val = (cycle * 1000 + i) as u64;
                let k = slab.insert(val).unwrap();
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
                let k = slab.insert(val).unwrap();
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
    fn stress_fill_drain_cycles() {
        let mut slab: FixedSlab<u64> = SlabBuilder::new().fixed().capacity(500).build().unwrap();

        for cycle in 0..10 {
            // Fill completely
            let mut keys = Vec::new();
            for i in 0..500 {
                let k = slab.insert((cycle * 1000 + i) as u64).unwrap();
                keys.push(k);
            }

            assert!(slab.insert(0).is_err());
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
            let k = slab.insert(i as u64).unwrap();
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
    fn builder_num_slabs() {
        let slab: DynamicSlab<u64> = SlabBuilder::new().num_slabs(5).build().unwrap();

        assert_eq!(slab.slab_count(), 5);
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
