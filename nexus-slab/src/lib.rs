//! nexus-slab v2 - Multi-slab allocator optimized for bump allocation.
//!
//! Organizes memory into logical slabs (default 2MB each) to encourage
//! transparent huge page (THP) backing. Uses bump allocation within slabs
//! for sequential, cache-friendly access patterns.
//!
//! # Example
//!
//! ```ignore
//! use nexus_slab::{Slab, SlabBuilder, FixedSlab, DynamicSlab};
//!
//! // Dynamic (growable, THP best-effort)
//! let mut slab: DynamicSlab<u64> = SlabBuilder::default().build()?;
//!
//! // Fixed (pre-allocated, optional huge pages/mlock)
//! let mut slab: FixedSlab<u64> = SlabBuilder::default()
//!     .fixed()
//!     .capacity(1_000_000)
//!     .huge_pages(true)
//!     .mlock(true)
//!     .build()?;
//! ```

mod meta;
mod sys;

use meta::{SLAB_NONE, SLOT_NONE, SlabMeta, SlabState, Slot};

use std::mem;
use std::ptr;

// =============================================================================
// Mode Constants
// =============================================================================

/// Fixed-size slab mode - pre-allocated, no growth.
pub const FIXED: bool = true;

/// Dynamic slab mode - grows on demand.
pub const DYNAMIC: bool = false;

/// Type alias for fixed-size slab.
pub type FixedSlab<T> = Slab<T, FIXED>;

/// Type alias for dynamic slab.
pub type DynamicSlab<T> = Slab<T, DYNAMIC>;

const DEFAULT_SPARSE_THRESHOLD_DIV: u32 = 8; // 12.5%
const DEFAULT_SPARSE_CEILING_DIV: u32 = 2;

// =============================================================================
// Public Types
// =============================================================================

/// Error returned when the slab is full.
/// Contains the value that could not be inserted, allowing recovery.
#[derive(Debug)]
pub struct Full<T>(
    /// The value that could not be inserted.
    pub T,
);

/// Opaque key identifying a slot. Encodes slab_index and slot_index.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Key(u64);

/// Error during slab construction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SlabError {
    /// Slot size exceeds slab size. Use a smaller type or larger slabs.
    SlotTooLarge { slot_size: usize, slab_bytes: usize },
    /// Huge pages requested but not available.
    HugePagesUnavailable,
    /// mlock failed (likely RLIMIT_MEMLOCK too low).
    MlockFailed,
    /// Memory allocation failed.
    AllocationFailed,
    /// Capacity is zero.
    ZeroCapacity,
}

impl std::fmt::Display for SlabError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SlabError::SlotTooLarge {
                slot_size,
                slab_bytes,
            } => {
                write!(
                    f,
                    "slot size ({slot_size}) exceeds slab size ({slab_bytes})"
                )
            }
            SlabError::HugePagesUnavailable => write!(f, "huge pages unavailable"),
            SlabError::MlockFailed => write!(f, "mlock failed"),
            SlabError::AllocationFailed => write!(f, "memory allocation failed"),
            SlabError::ZeroCapacity => write!(f, "capacity cannot be zero"),
        }
    }
}

impl std::error::Error for SlabError {}

// =============================================================================
// Builders
// =============================================================================

/// Builder for dynamic slab (grows on demand).
///
/// Call `.fixed()` to switch to fixed allocation mode.
#[derive(Clone, Debug)]
pub struct SlabBuilder {
    capacity: Option<usize>,
    slab_megabytes: usize,
    sparse_threshold: Option<u32>,
    sparse_ceiling: Option<u32>,
}

/// Builder for fixed-size slab (pre-allocated, optional huge pages/mlock).
///
/// Created via `SlabBuilder::default().fixed()`.
#[derive(Clone, Debug)]
pub struct FixedSlabBuilder {
    capacity: Option<usize>,
    slab_megabytes: usize,
    sparse_threshold: Option<u32>,
    sparse_ceiling: Option<u32>,
    huge_pages: bool,
    mlock: bool,
    populate: bool,
}

impl Default for SlabBuilder {
    fn default() -> Self {
        Self {
            capacity: None,
            slab_megabytes: 2,
            sparse_threshold: None,
            sparse_ceiling: None,
        }
    }
}

impl SlabBuilder {
    /// Pre-allocate capacity for at least this many slots.
    /// Slab can grow beyond this. Default: starts with one slab.
    pub fn capacity(mut self, slots: usize) -> Self {
        self.capacity = Some(slots);
        self
    }

    /// Size of each logical slab in megabytes. Default: 2 (2MB, THP-friendly).
    /// slots_per_slab derived at build time: (slab_mb * 1MB) / size_of::<Slot<T>>()
    ///
    /// If you need smaller allocations, use the `slab` crate instead.
    pub fn slab_megabytes(mut self, mb: usize) -> Self {
        self.slab_megabytes = mb;
        self
    }

    /// Sparse threshold - slab enters sparse list at or below this.
    /// Default: slots_per_slab / 8 (12.5%).
    pub fn sparse_threshold(mut self, n: u32) -> Self {
        self.sparse_threshold = Some(n);
        self
    }

    /// Sparse ceiling - slab graduates from sparse above this.
    /// Default: slots_per_slab * 3 / 4 (75%).
    pub fn sparse_ceiling(mut self, n: u32) -> Self {
        self.sparse_ceiling = Some(n);
        self
    }

    /// Convert to fixed-size builder.
    pub fn fixed(self) -> FixedSlabBuilder {
        FixedSlabBuilder {
            capacity: self.capacity,
            slab_megabytes: self.slab_megabytes,
            sparse_threshold: self.sparse_threshold,
            sparse_ceiling: self.sparse_ceiling,
            huge_pages: false,
            mlock: false,
            populate: false,
        }
    }

    /// Build a dynamic slab (grows on demand, THP best-effort).
    pub fn build<T>(self) -> Result<DynamicSlab<T>, SlabError> {
        let slab_bytes = self.slab_megabytes * 1024 * 1024;
        let slot_size = mem::size_of::<Slot<T>>();

        if slot_size > slab_bytes {
            return Err(SlabError::SlotTooLarge {
                slot_size,
                slab_bytes,
            });
        }

        let slots_per_slab = (slab_bytes / slot_size) as u32;
        let sparse_threshold = self
            .sparse_threshold
            .unwrap_or(slots_per_slab / DEFAULT_SPARSE_THRESHOLD_DIV);
        let sparse_ceiling = self
            .sparse_ceiling
            .unwrap_or(slots_per_slab / DEFAULT_SPARSE_CEILING_DIV);

        // Determine initial slabs needed
        let initial_slabs = match self.capacity {
            Some(cap) if cap > 0 => (cap as u32).div_ceil(slots_per_slab) as usize,
            _ => 1,
        };

        let slots_capacity = initial_slabs * slots_per_slab as usize;
        let total_bytes = slots_capacity * slot_size;

        // Allocate slot storage via sys::Pages
        let pages_alloc =
            sys::Pages::alloc(total_bytes).map_err(|_| SlabError::AllocationFailed)?;
        let slots = pages_alloc.as_ptr() as *mut Slot<T>;

        // Initialize slab metadata - all start as Empty
        let mut slabs = Vec::with_capacity(initial_slabs);
        for _ in 0..initial_slabs {
            slabs.push(SlabMeta::new());
        }

        // Link all slabs into empty list
        let empty_head = if initial_slabs > 0 {
            for i in 0..initial_slabs {
                slabs[i].prev = if i > 0 { (i - 1) as u32 } else { SLAB_NONE };
                slabs[i].next = if i < initial_slabs - 1 {
                    (i + 1) as u32
                } else {
                    SLAB_NONE
                };
                slabs[i].state = SlabState::Empty;
            }
            0
        } else {
            SLAB_NONE
        };

        Ok(Slab {
            pages: Some(pages_alloc),
            slots,
            slots_capacity,
            slabs,
            empty_head,
            sparse_head: SLAB_NONE,
            dense_head: SLAB_NONE,
            current: SLAB_NONE,
            len: 0,
            slots_per_slab,
            sparse_threshold,
            sparse_ceiling,
        })
    }
}

impl FixedSlabBuilder {
    /// Maximum capacity in slots. Rounds up to fill slabs.
    /// Required for fixed mode.
    pub fn capacity(mut self, slots: usize) -> Self {
        self.capacity = Some(slots);
        self
    }

    /// Size of each logical slab in megabytes. Default: 2 (2MB).
    /// slots_per_slab derived at build time: (slab_mb * 1MB) / size_of::<Slot<T>>()
    ///
    /// If you need smaller allocations, use the `slab` crate instead.
    pub fn slab_megabytes(mut self, mb: usize) -> Self {
        self.slab_megabytes = mb;
        self
    }

    /// Sparse threshold - slab enters sparse list at or below this.
    /// Default: slots_per_slab / 8 (12.5%).
    pub fn sparse_threshold(mut self, n: u32) -> Self {
        self.sparse_threshold = Some(n);
        self
    }

    /// Sparse ceiling - slab graduates from sparse above this.
    /// Default: slots_per_slab * 3 / 4 (75%).
    pub fn sparse_ceiling(mut self, n: u32) -> Self {
        self.sparse_ceiling = Some(n);
        self
    }

    /// Use explicit 2MB huge pages (requires hugetlbfs configured).
    /// Default: false.
    pub fn huge_pages(mut self, enabled: bool) -> Self {
        self.huge_pages = enabled;
        self
    }

    /// Lock memory (prevent swapping, avoid page faults).
    /// Default: false.
    pub fn mlock(mut self, enabled: bool) -> Self {
        self.mlock = enabled;
        self
    }

    /// Fault all pages at init (MAP_POPULATE), avoid first-touch faults.
    /// Default: false.
    pub fn populate(mut self, enabled: bool) -> Self {
        self.populate = enabled;
        self
    }

    /// Build a fixed-size slab (pre-allocated, no growth).
    pub fn build<T>(self) -> Result<FixedSlab<T>, SlabError> {
        let capacity = self.capacity.ok_or(SlabError::ZeroCapacity)?;
        if capacity == 0 {
            return Err(SlabError::ZeroCapacity);
        }

        let slab_bytes = self.slab_megabytes * 1024 * 1024;
        let slot_size = mem::size_of::<Slot<T>>();

        if slot_size > slab_bytes {
            return Err(SlabError::SlotTooLarge {
                slot_size,
                slab_bytes,
            });
        }

        let slots_per_slab = (slab_bytes / slot_size) as u32;
        let sparse_threshold = self.sparse_threshold.unwrap_or(slots_per_slab / 8);
        let sparse_ceiling = self.sparse_ceiling.unwrap_or(slots_per_slab * 3 / 4);

        let num_slabs = (capacity as u32).div_ceil(slots_per_slab) as usize;
        let slots_capacity = num_slabs * slots_per_slab as usize;
        let total_bytes = slots_capacity * slot_size;

        // Allocate slot storage with optional huge pages
        #[cfg(target_os = "linux")]
        let pages_alloc = if self.huge_pages {
            sys::Pages::alloc_hugetlb(total_bytes).map_err(|_| SlabError::HugePagesUnavailable)?
        } else {
            sys::Pages::alloc(total_bytes).map_err(|_| SlabError::AllocationFailed)?
        };

        #[cfg(not(target_os = "linux"))]
        let pages_alloc = {
            if self.huge_pages {
                return Err(SlabError::HugePagesUnavailable);
            }
            sys::Pages::alloc(total_bytes).map_err(|_| SlabError::AllocationFailed)?
        };

        // Apply mlock if requested
        if self.mlock {
            pages_alloc.mlock().map_err(|_| SlabError::MlockFailed)?;
        }

        let slots = pages_alloc.as_ptr() as *mut Slot<T>;

        // Initialize slab metadata - all start as Empty
        let mut slabs = Vec::with_capacity(num_slabs);
        for _ in 0..num_slabs {
            slabs.push(SlabMeta::new());
        }

        // Link all slabs into empty list
        let empty_head = if num_slabs > 0 {
            for i in 0..num_slabs {
                slabs[i].prev = if i > 0 { (i - 1) as u32 } else { SLAB_NONE };
                slabs[i].next = if i < num_slabs - 1 {
                    (i + 1) as u32
                } else {
                    SLAB_NONE
                };
                slabs[i].state = SlabState::Empty;
            }
            0
        } else {
            SLAB_NONE
        };

        Ok(Slab {
            pages: Some(pages_alloc),
            slots,
            slots_capacity,
            slabs,
            empty_head,
            sparse_head: SLAB_NONE,
            dense_head: SLAB_NONE,
            current: SLAB_NONE,
            len: 0,
            slots_per_slab,
            sparse_threshold,
            sparse_ceiling,
        })
    }
}

// =============================================================================
// Slab
// =============================================================================

/// Multi-slab allocator optimized for bump allocation.
///
/// The `MODE` const generic determines allocation strategy:
/// - `FIXED`: Pre-allocated, no growth. Falls back to freelist when bump exhausted.
/// - `DYNAMIC`: Grows on demand. Prefers growing over freelist to maximize bump allocation.
pub struct Slab<T, const MODE: bool> {
    // Slot storage (mmap'd via sys::Pages)
    pages: Option<sys::Pages>,
    slots: *mut Slot<T>,
    slots_capacity: usize,

    // Slab bookkeeping
    slabs: Vec<SlabMeta>,

    // List heads (intrusive doubly-linked through slabs)
    empty_head: u32,
    sparse_head: u32,
    dense_head: u32,

    // Active bump slab
    current: u32,

    // Counts
    len: usize,

    // Config (derived at build time)
    slots_per_slab: u32,
    sparse_threshold: u32,
    sparse_ceiling: u32,
}

// =============================================================================
// Key
// =============================================================================

impl Key {
    /// Extract slab index.
    #[inline]
    pub const fn slab(self) -> u32 {
        (self.0 >> 32) as u32
    }

    /// Extract slot index within slab.
    #[inline]
    pub const fn slot(self) -> u32 {
        self.0 as u32
    }

    /// Construct from slab and slot indices.
    #[inline]
    pub(crate) const fn new(slab: u32, slot: u32) -> Self {
        Self(((slab as u64) << 32) | (slot as u64))
    }

    #[inline]
    pub const unsafe fn from_raw(raw: u64) -> Self {
        Self(raw)
    }
}

// =============================================================================
// Public API
// =============================================================================

impl<T> DynamicSlab<T> {
    /// Create slab with default config (dynamic mode, 2MB slabs).
    pub fn new() -> Result<DynamicSlab<T>, SlabError> {
        SlabBuilder::default().build()
    }
}

impl<T, const MODE: bool> Slab<T, MODE> {
    /// Allocate a slot, returning its key.
    ///
    /// # Allocation Strategy
    ///
    /// **Fixed mode (`FIXED`):**
    /// 1. Bump on current slab
    /// 2. Pop from empty list (reset for bump)
    /// 3. Freelist from sparse slabs (reclaim stragglers)
    /// 4. Freelist from dense slabs (last resort)
    /// 5. `Err(Full)` when at capacity
    ///
    /// **Dynamic mode (`DYNAMIC`):**
    /// 1. Bump on current slab
    /// 2. Pop from empty list (reset for bump)
    /// 3. Grow new slab (stay in bump mode)
    /// 4. Freelist from sparse/dense (only on OOM)
    /// 5. `Err(Full)` only on OOM
    pub fn insert(&mut self, value: T) -> Result<Key, Full<T>> {
        // Fast path: bump on current slab (same for both modes)
        if self.current != SLAB_NONE {
            let has_bump = self.slabs[self.current as usize].has_bump(self.slots_per_slab);
            if has_bump {
                let slot_idx = self.bump_alloc();
                let key = Key::new(self.current, slot_idx);

                unsafe {
                    let ptr = self.slot_ptr(self.current, slot_idx);
                    ptr::write(ptr, Slot::Occupied { value });
                }

                self.len += 1;
                return Ok(key);
            }

            // Current exhausted, retire it
            self.retire_current();
        }

        // Try empty list (same for both modes - gives us bump capacity back)
        if self.empty_head != SLAB_NONE {
            let slab_idx = self.pop_list(SlabState::Empty);
            self.slabs[slab_idx as usize].reset();
            self.slabs[slab_idx as usize].state = SlabState::Current;
            self.current = slab_idx;

            return self.insert(value);
        }

        // Mode-specific paths diverge here
        if MODE == DYNAMIC {
            // Dynamic: prefer growing to stay in bump mode
            match self.grow() {
                Ok(slab_idx) => {
                    self.slabs[slab_idx as usize].state = SlabState::Current;
                    self.current = slab_idx;
                    return self.insert(value);
                }
                Err(_) => {
                    // OOM - fall through to freelist as last resort
                }
            }
        }

        // Freelist fallback (primary path for FIXED, fallback for DYNAMIC on OOM)

        // Try sparse list
        if self.sparse_head != SLAB_NONE {
            let slab_idx = self.sparse_head;
            let slot_idx = self.freelist_pop(slab_idx);
            self.slabs[slab_idx as usize].occupied += 1;

            // Check if should graduate from sparse
            if self.slabs[slab_idx as usize].occupied > self.sparse_ceiling {
                self.unlink(slab_idx);
                self.push_list(SlabState::Dense, slab_idx);
                self.slabs[slab_idx as usize].state = SlabState::Dense;
            }

            let key = Key::new(slab_idx, slot_idx);

            unsafe {
                let ptr = self.slot_ptr(slab_idx, slot_idx);
                ptr::write(ptr, Slot::Occupied { value });
            }

            self.len += 1;
            return Ok(key);
        }

        // Try dense list
        if self.dense_head != SLAB_NONE {
            let slab_idx = self.dense_head;
            let slot_idx = self.freelist_pop(slab_idx);
            self.slabs[slab_idx as usize].occupied += 1;

            // Check if now full
            if self.slabs[slab_idx as usize].is_full(self.slots_per_slab) {
                self.unlink(slab_idx);
                self.slabs[slab_idx as usize].state = SlabState::Full;
            }

            let key = Key::new(slab_idx, slot_idx);

            unsafe {
                let ptr = self.slot_ptr(slab_idx, slot_idx);
                ptr::write(ptr, Slot::Occupied { value });
            }

            self.len += 1;
            return Ok(key);
        }

        // No capacity
        Err(Full(value))
    }

    /// Remove and return value at key.
    ///
    /// # Panics
    /// Panics if key is invalid or slot is vacant.
    pub fn remove(&mut self, key: Key) -> T {
        let slab_idx = key.slab();
        let slot_idx = key.slot();

        assert!(
            (slab_idx as usize) < self.slabs.len(),
            "invalid key: slab index out of bounds"
        );
        assert!(
            slot_idx < self.slots_per_slab,
            "invalid key: slot index out of bounds"
        );

        // Read and replace with vacant
        let value = unsafe {
            let ptr = self.slot_ptr(slab_idx, slot_idx);
            match ptr::read(ptr) {
                Slot::Occupied { value } => {
                    // Push onto freelist
                    self.freelist_push(slab_idx, slot_idx);
                    value
                }
                Slot::Vacant { .. } => panic!("removing from vacant slot"),
            }
        };

        // Decrement counts - avoid holding borrow across method calls
        self.slabs[slab_idx as usize].occupied -= 1;
        self.len -= 1;

        // Read state info for transition logic
        let old_state = self.slabs[slab_idx as usize].state;
        let occupied = self.slabs[slab_idx as usize].occupied;

        // State transitions
        match old_state {
            SlabState::Current => {
                // Stays current until bump exhausts
            }
            SlabState::Full => {
                // Now has capacity - transition to appropriate list
                if occupied <= self.sparse_threshold {
                    self.slabs[slab_idx as usize].state = SlabState::Sparse;
                    self.push_list(SlabState::Sparse, slab_idx);
                } else {
                    self.slabs[slab_idx as usize].state = SlabState::Dense;
                    self.push_list(SlabState::Dense, slab_idx);
                }
            }
            SlabState::Dense => {
                if occupied == 0 {
                    self.unlink(slab_idx);
                    self.slabs[slab_idx as usize].state = SlabState::Empty;
                    self.push_list(SlabState::Empty, slab_idx);
                } else if occupied <= self.sparse_threshold {
                    self.unlink(slab_idx);
                    self.slabs[slab_idx as usize].state = SlabState::Sparse;
                    self.push_list(SlabState::Sparse, slab_idx);
                }
            }
            SlabState::Sparse => {
                if occupied == 0 {
                    self.unlink(slab_idx);
                    self.slabs[slab_idx as usize].state = SlabState::Empty;
                    self.push_list(SlabState::Empty, slab_idx);
                }
            }
            SlabState::Empty => {
                unreachable!("cannot remove from empty slab")
            }
        }

        value
    }

    /// Get shared reference to value at key.
    ///
    /// # Panics
    /// Panics if key is invalid or slot is vacant.
    pub fn get(&self, key: Key) -> &T {
        let slab_idx = key.slab();
        let slot_idx = key.slot();

        assert!(
            (slab_idx as usize) < self.slabs.len(),
            "invalid key: slab index out of bounds"
        );
        assert!(
            slot_idx < self.slots_per_slab,
            "invalid key: slot index out of bounds"
        );

        unsafe {
            let ptr = self.slot_ptr(slab_idx, slot_idx);
            match &*ptr {
                Slot::Occupied { value } => value,
                Slot::Vacant { .. } => panic!("accessing vacant slot"),
            }
        }
    }

    /// Get mutable reference to value at key.
    ///
    /// # Panics
    /// Panics if key is invalid or slot is vacant.
    pub fn get_mut(&mut self, key: Key) -> &mut T {
        let slab_idx = key.slab();
        let slot_idx = key.slot();

        assert!(
            (slab_idx as usize) < self.slabs.len(),
            "invalid key: slab index out of bounds"
        );
        assert!(
            slot_idx < self.slots_per_slab,
            "invalid key: slot index out of bounds"
        );

        unsafe {
            let ptr = self.slot_ptr(slab_idx, slot_idx);
            match &mut *ptr {
                Slot::Occupied { value } => value,
                Slot::Vacant { .. } => panic!("accessing vacant slot"),
            }
        }
    }

    /// Returns true if key points to an occupied slot.
    pub fn contains(&self, key: Key) -> bool {
        let slab_idx = key.slab();
        let slot_idx = key.slot();

        if (slab_idx as usize) >= self.slabs.len() || slot_idx >= self.slots_per_slab {
            return false;
        }

        unsafe {
            let ptr = self.slot_ptr(slab_idx, slot_idx);
            matches!(&*ptr, Slot::Occupied { .. })
        }
    }

    /// Remove all elements from the slab.
    ///
    /// Drops all occupied values and resets all slabs to empty state,
    /// ready for reuse via bump allocation.
    pub fn clear(&mut self) {
        // Drop all occupied values
        for slab_idx in 0..self.slabs.len() {
            let slab = &self.slabs[slab_idx];
            for slot_idx in 0..slab.bump_cursor {
                unsafe {
                    let ptr = self.slot_ptr(slab_idx as u32, slot_idx);
                    if let Slot::Occupied { .. } = &*ptr {
                        ptr::drop_in_place(ptr);
                    }
                }
            }
        }

        // Reset all slab metadata and rebuild empty list
        for i in 0..self.slabs.len() {
            self.slabs[i] = SlabMeta::new();
            self.slabs[i].prev = if i > 0 { (i - 1) as u32 } else { SLAB_NONE };
            self.slabs[i].next = if i < self.slabs.len() - 1 {
                (i + 1) as u32
            } else {
                SLAB_NONE
            };
            self.slabs[i].state = SlabState::Empty;
        }

        // Reset list heads
        self.empty_head = if self.slabs.is_empty() { SLAB_NONE } else { 0 };
        self.sparse_head = SLAB_NONE;
        self.dense_head = SLAB_NONE;
        self.current = SLAB_NONE;
        self.len = 0;
    }

    /// Number of occupied slots.
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns true if no slots are occupied.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Total slot capacity.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.slots_capacity
    }

    /// Slots per logical slab (derived from slab_megabytes / slot_size).
    #[inline]
    pub fn slots_per_slab(&self) -> u32 {
        self.slots_per_slab
    }

    /// Number of allocated slabs.
    #[inline]
    pub fn slab_count(&self) -> usize {
        self.slabs.len()
    }
}

// =============================================================================
// Internal: List operations
// =============================================================================

impl<T, const MODE: bool> Slab<T, MODE> {
    /// Unlink slab from its current list. O(1).
    fn unlink(&mut self, slab_idx: u32) {
        let slab = &self.slabs[slab_idx as usize];
        let prev = slab.prev;
        let next = slab.next;
        let state = slab.state;

        if prev != SLAB_NONE {
            self.slabs[prev as usize].next = next;
        } else {
            // Was head of list
            *self.list_head_mut(state) = next;
        }

        if next != SLAB_NONE {
            self.slabs[next as usize].prev = prev;
        }

        self.slabs[slab_idx as usize].prev = SLAB_NONE;
        self.slabs[slab_idx as usize].next = SLAB_NONE;
    }

    /// Push slab to front of specified list. O(1).
    fn push_list(&mut self, state: SlabState, slab_idx: u32) {
        let head = *self.list_head_mut(state);

        self.slabs[slab_idx as usize].next = head;
        self.slabs[slab_idx as usize].prev = SLAB_NONE;

        if head != SLAB_NONE {
            self.slabs[head as usize].prev = slab_idx;
        }

        *self.list_head_mut(state) = slab_idx;
    }

    /// Pop slab from front of specified list. O(1).
    ///
    /// # Panics
    /// Panics if list is empty.
    fn pop_list(&mut self, state: SlabState) -> u32 {
        let head = *self.list_head_mut(state);
        debug_assert!(head != SLAB_NONE, "pop from empty list");

        let next = self.slabs[head as usize].next;

        *self.list_head_mut(state) = next;
        if next != SLAB_NONE {
            self.slabs[next as usize].prev = SLAB_NONE;
        }

        self.slabs[head as usize].prev = SLAB_NONE;
        self.slabs[head as usize].next = SLAB_NONE;

        head
    }

    /// Get mutable reference to list head for given state.
    fn list_head_mut(&mut self, state: SlabState) -> &mut u32 {
        match state {
            SlabState::Empty => &mut self.empty_head,
            SlabState::Sparse => &mut self.sparse_head,
            SlabState::Dense => &mut self.dense_head,
            SlabState::Current | SlabState::Full => {
                panic!("Current and Full states are not linked lists")
            }
        }
    }
}

// =============================================================================
// Internal: Allocation
// =============================================================================

impl<T, const MODE: bool> Slab<T, MODE> {
    /// Bump allocate from current slab. Returns slot index.
    ///
    /// Note: Does NOT increment `len` or write the slot - caller must do both.
    fn bump_alloc(&mut self) -> u32 {
        debug_assert!(self.current != SLAB_NONE);
        let slab = &mut self.slabs[self.current as usize];
        debug_assert!(slab.has_bump(self.slots_per_slab));

        let slot_idx = slab.bump_cursor;
        slab.bump_cursor += 1;
        slab.occupied += 1;

        slot_idx
    }

    /// Pop from slab's freelist. Returns slot index.
    ///
    /// Note: Does NOT increment `occupied` - caller must do so.
    fn freelist_pop(&mut self, slab_idx: u32) -> u32 {
        let slot_idx = self.slabs[slab_idx as usize].free_head;
        debug_assert!(slot_idx != SLOT_NONE, "freelist_pop on empty freelist");

        // Read next from slot - get ptr before any mutable borrow
        let next = unsafe {
            let ptr = self.slot_ptr(slab_idx, slot_idx);
            match &*ptr {
                Slot::Vacant { next_free } => *next_free,
                Slot::Occupied { .. } => panic!("freelist corruption: occupied slot in freelist"),
            }
        };

        self.slabs[slab_idx as usize].free_head = next;
        slot_idx
    }

    /// Push slot onto slab's freelist.
    fn freelist_push(&mut self, slab_idx: u32, slot_idx: u32) {
        let old_head = self.slabs[slab_idx as usize].free_head;

        // Write to slot - get ptr before any mutable borrow
        unsafe {
            let ptr = self.slot_ptr(slab_idx, slot_idx);
            ptr::write(
                ptr,
                Slot::Vacant {
                    next_free: old_head,
                },
            );
        }

        self.slabs[slab_idx as usize].free_head = slot_idx;
    }

    /// Retire current slab (bump exhausted) → Full or Dense/Sparse state.
    fn retire_current(&mut self) {
        if self.current == SLAB_NONE {
            return;
        }

        let slab_idx = self.current;
        let slab = &mut self.slabs[slab_idx as usize];

        // Current slab bump exhausted, but might have freelist from removals
        if slab.is_full(self.slots_per_slab) {
            slab.state = SlabState::Full;
        } else if slab.occupied <= self.sparse_threshold {
            slab.state = SlabState::Sparse;
            self.push_list(SlabState::Sparse, slab_idx);
        } else {
            slab.state = SlabState::Dense;
            self.push_list(SlabState::Dense, slab_idx);
        }

        self.current = SLAB_NONE;
    }

    /// Grow by one slab. Returns new slab index.
    fn grow(&mut self) -> Result<u32, SlabError> {
        let new_slab_idx = self.slabs.len() as u32;
        let new_slots_count = self.slots_capacity + self.slots_per_slab as usize;
        let slot_size = mem::size_of::<Slot<T>>();
        let new_bytes = new_slots_count * slot_size;

        // Allocate new pages
        let new_pages = sys::Pages::alloc(new_bytes).map_err(|_| SlabError::AllocationFailed)?;
        let new_slots = new_pages.as_ptr() as *mut Slot<T>;

        // Copy existing data
        if !self.slots.is_null() && self.slots_capacity > 0 {
            unsafe {
                ptr::copy_nonoverlapping(self.slots, new_slots, self.slots_capacity);
            }
        }

        // Replace old pages with new (old pages will be dropped)
        self.pages = Some(new_pages);
        self.slots = new_slots;
        self.slots_capacity = new_slots_count;

        // Add new slab metadata
        self.slabs.push(SlabMeta::new());

        Ok(new_slab_idx)
    }

    /// Convert slab + slot indices to global slot index.
    #[inline]
    fn global_slot(&self, slab_idx: u32, slot_idx: u32) -> usize {
        (slab_idx as usize) * (self.slots_per_slab as usize) + (slot_idx as usize)
    }

    /// Get slot pointer.
    ///
    /// # Safety
    /// Caller must ensure slab_idx and slot_idx are in bounds.
    #[inline]
    unsafe fn slot_ptr(&self, slab_idx: u32, slot_idx: u32) -> *mut Slot<T> {
        let global = self.global_slot(slab_idx, slot_idx);
        // SAFETY: Caller guarantees indices are in bounds
        unsafe { self.slots.add(global) }
    }
}

impl<T, const MODE: bool> Drop for Slab<T, MODE> {
    fn drop(&mut self) {
        // Drop all occupied values
        for slab_idx in 0..self.slabs.len() {
            let slab = &self.slabs[slab_idx];
            // Only check slots up to bump_cursor (slots beyond were never touched)
            for slot_idx in 0..slab.bump_cursor {
                unsafe {
                    let ptr = self.slot_ptr(slab_idx as u32, slot_idx);
                    if let Slot::Occupied { .. } = &*ptr {
                        ptr::drop_in_place(ptr);
                    }
                }
            }
        }

        // Memory deallocation happens automatically when self.pages is dropped
    }
}

unsafe impl<T: Send, const MODE: bool> Send for Slab<T, MODE> {}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use std::sync::atomic::{AtomicUsize, Ordering};

    // =========================================================================
    // Key
    // =========================================================================

    #[test]
    fn key_roundtrip() {
        let key = Key::new(123, 456);
        assert_eq!(key.slab(), 123);
        assert_eq!(key.slot(), 456);
    }

    #[test]
    fn key_max_values() {
        let key = Key::new(u32::MAX - 1, u32::MAX - 1);
        assert_eq!(key.slab(), u32::MAX - 1);
        assert_eq!(key.slot(), u32::MAX - 1);
    }

    #[test]
    fn key_zero() {
        let key = Key::new(0, 0);
        assert_eq!(key.slab(), 0);
        assert_eq!(key.slot(), 0);
    }

    // =========================================================================
    // Builders
    // =========================================================================

    #[test]
    fn dynamic_slab_default() {
        let slab: DynamicSlab<u64> = SlabBuilder::default().build().unwrap();
        assert_eq!(slab.len(), 0);
        assert!(slab.is_empty());
        assert!(slab.capacity() > 0);
    }

    #[test]
    fn dynamic_slab_new() {
        let slab = DynamicSlab::<u64>::new().unwrap();
        assert!(slab.is_empty());
    }

    #[test]
    fn dynamic_slab_with_capacity() {
        let slab: DynamicSlab<u64> = SlabBuilder::default().capacity(1_000_000).build().unwrap();
        assert!(slab.capacity() >= 1_000_000);
    }

    #[test]
    fn fixed_slab_requires_capacity() {
        let result: Result<FixedSlab<u64>, _> = SlabBuilder::default().fixed().build();
        assert!(matches!(result, Err(SlabError::ZeroCapacity)));
    }

    #[test]
    fn fixed_slab_zero_capacity_error() {
        let result: Result<FixedSlab<u64>, _> = SlabBuilder::default().fixed().capacity(0).build();
        assert!(matches!(result, Err(SlabError::ZeroCapacity)));
    }

    #[test]
    fn fixed_slab_with_capacity() {
        let slab: FixedSlab<u64> = SlabBuilder::default()
            .fixed()
            .capacity(1000)
            .build()
            .unwrap();
        assert!(slab.capacity() >= 1000);
    }

    #[test]
    fn slot_too_large_error() {
        // 1 byte slab can't fit any reasonable slot
        let result: Result<DynamicSlab<u64>, _> = SlabBuilder::default().slab_megabytes(0).build();
        // slab_megabytes(0) means 0 bytes, slot size > 0
        assert!(matches!(result, Err(SlabError::SlotTooLarge { .. })));
    }

    // =========================================================================
    // Basic Operations
    // =========================================================================

    #[test]
    fn insert_and_get() {
        let mut slab = DynamicSlab::<u64>::new().unwrap();
        let key = slab.insert(42).unwrap();
        assert_eq!(*slab.get(key), 42);
    }

    #[test]
    fn insert_and_get_mut() {
        let mut slab = DynamicSlab::<u64>::new().unwrap();
        let key = slab.insert(42).unwrap();
        *slab.get_mut(key) = 100;
        assert_eq!(*slab.get(key), 100);
    }

    #[test]
    fn insert_and_remove() {
        let mut slab = DynamicSlab::<u64>::new().unwrap();
        let key = slab.insert(42).unwrap();
        assert_eq!(slab.len(), 1);
        let value = slab.remove(key);
        assert_eq!(value, 42);
        assert_eq!(slab.len(), 0);
    }

    #[test]
    fn contains() {
        let mut slab = DynamicSlab::<u64>::new().unwrap();
        let key = slab.insert(42).unwrap();
        assert!(slab.contains(key));
        slab.remove(key);
        assert!(!slab.contains(key));
    }

    #[test]
    fn contains_invalid_key() {
        let slab = DynamicSlab::<u64>::new().unwrap();
        let fake_key = Key::new(999, 999);
        assert!(!slab.contains(fake_key));
    }

    #[test]
    fn len_and_is_empty() {
        let mut slab = DynamicSlab::<u64>::new().unwrap();
        assert!(slab.is_empty());
        assert_eq!(slab.len(), 0);

        let k1 = slab.insert(1).unwrap();
        assert!(!slab.is_empty());
        assert_eq!(slab.len(), 1);

        let k2 = slab.insert(2).unwrap();
        assert_eq!(slab.len(), 2);

        slab.remove(k1);
        assert_eq!(slab.len(), 1);

        slab.remove(k2);
        assert!(slab.is_empty());
    }

    #[test]
    #[should_panic(expected = "vacant")]
    fn get_vacant_panics() {
        let mut slab = DynamicSlab::<u64>::new().unwrap();
        let key = slab.insert(42).unwrap();
        slab.remove(key);
        let _ = slab.get(key); // Should panic
    }

    #[test]
    #[should_panic(expected = "vacant")]
    fn remove_vacant_panics() {
        let mut slab = DynamicSlab::<u64>::new().unwrap();
        let key = slab.insert(42).unwrap();
        slab.remove(key);
        slab.remove(key); // Should panic
    }

    #[test]
    #[should_panic(expected = "out of bounds")]
    fn get_invalid_slab_panics() {
        let slab = DynamicSlab::<u64>::new().unwrap();
        let fake_key = Key::new(999, 0);
        let _ = slab.get(fake_key);
    }

    // =========================================================================
    // Multiple Inserts
    // =========================================================================

    #[test]
    fn insert_many() {
        let mut slab = DynamicSlab::<u64>::new().unwrap();
        let mut keys = Vec::new();

        for i in 0..1000 {
            let key = slab.insert(i).unwrap();
            keys.push(key);
        }

        assert_eq!(slab.len(), 1000);

        for (i, key) in keys.iter().enumerate() {
            assert_eq!(*slab.get(*key), i as u64);
        }
    }

    #[test]
    fn insert_remove_insert_reuses_slots() {
        let mut slab = DynamicSlab::<u64>::new().unwrap();

        let _k1 = slab.insert(1).unwrap();
        let k2 = slab.insert(2).unwrap();
        let _k3 = slab.insert(3).unwrap();

        slab.remove(k2);

        // New insert should reuse k2's slot (via freelist)
        // or bump (if current slab still has bump capacity)
        let k4 = slab.insert(4).unwrap();
        assert_eq!(*slab.get(k4), 4);
        assert_eq!(slab.len(), 3);
    }

    // =========================================================================
    // Dynamic Mode - Growth
    // =========================================================================

    #[test]
    fn dynamic_grows_beyond_initial() {
        let mut slab: DynamicSlab<u64> = SlabBuilder::default()
            .slab_megabytes(1) // Smaller slabs for faster test
            .build()
            .unwrap();

        let initial_capacity = slab.capacity();
        let initial_slabs = slab.slab_count();

        // Insert more than one slab's worth
        let slots_per_slab = slab.slots_per_slab() as usize;
        for i in 0..(slots_per_slab + 100) {
            slab.insert(i as u64).unwrap();
        }

        assert!(slab.capacity() > initial_capacity);
        assert!(slab.slab_count() > initial_slabs);
    }

    // =========================================================================
    // Fixed Mode - Bounded
    // =========================================================================

    #[test]
    fn fixed_returns_full_at_capacity() {
        let mut slab: FixedSlab<u64> = SlabBuilder::default()
            .slab_megabytes(1)
            .fixed()
            .capacity(100)
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
    fn fixed_can_reuse_after_remove() {
        let mut slab: FixedSlab<u64> = SlabBuilder::default()
            .slab_megabytes(1)
            .fixed()
            .capacity(100)
            .build()
            .unwrap();

        let capacity = slab.capacity();

        // Fill completely
        let mut keys = Vec::new();
        for i in 0..capacity {
            keys.push(slab.insert(i as u64).unwrap());
        }

        // Remove one
        slab.remove(keys[50]);

        // Should be able to insert again
        let new_key = slab.insert(999).unwrap();
        assert_eq!(*slab.get(new_key), 999);
    }

    // =========================================================================
    // Drop Behavior
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
            let mut slab = DynamicSlab::<DropCounter>::new().unwrap();
            for _ in 0..100 {
                slab.insert(DropCounter(drop_count.clone())).unwrap();
            }
            assert_eq!(drop_count.load(Ordering::SeqCst), 0);
        }

        assert_eq!(drop_count.load(Ordering::SeqCst), 100);
    }

    #[test]
    fn remove_calls_destructor() {
        let drop_count = Arc::new(AtomicUsize::new(0));

        #[derive(Debug)]
        struct DropCounter(Arc<AtomicUsize>);
        impl Drop for DropCounter {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }

        let mut slab = DynamicSlab::<DropCounter>::new().unwrap();
        let key = slab.insert(DropCounter(drop_count.clone())).unwrap();

        assert_eq!(drop_count.load(Ordering::SeqCst), 0);
        slab.remove(key);
        assert_eq!(drop_count.load(Ordering::SeqCst), 1);
    }

    // =========================================================================
    // State Transitions (Sparse/Dense)
    // =========================================================================

    #[test]
    fn slab_transitions_through_states() {
        // Use small slab to make thresholds easy to hit
        let mut slab: DynamicSlab<u64> = SlabBuilder::default().slab_megabytes(1).build().unwrap();

        let slots_per_slab = slab.slots_per_slab() as usize;

        // Fill first slab completely (becomes Full when retired)
        let mut keys = Vec::new();
        for i in 0..slots_per_slab {
            keys.push(slab.insert(i as u64).unwrap());
        }

        // Remove most - should transition through Dense -> Sparse -> Empty
        for key in keys.drain(..) {
            slab.remove(key);
        }

        assert!(slab.is_empty());
    }

    #[test]
    fn sparse_threshold_hysteresis() {
        let mut slab: DynamicSlab<u64> = SlabBuilder::default()
            .slab_megabytes(1)
            .sparse_threshold(10)
            .sparse_ceiling(50)
            .build()
            .unwrap();

        let slots_per_slab = slab.slots_per_slab() as usize;

        // Fill and remove to create freelist entries
        let mut keys = Vec::new();
        for i in 0..slots_per_slab {
            keys.push(slab.insert(i as u64).unwrap());
        }

        // Remove down to sparse threshold
        while slab.len() > 10 {
            slab.remove(keys.pop().unwrap());
        }

        // Insert back up - should stay sparse until ceiling
        for i in 0..40 {
            slab.insert(i as u64).unwrap();
        }

        // Insert beyond ceiling - should graduate to dense
        for i in 0..20 {
            slab.insert(i as u64).unwrap();
        }
    }

    // =========================================================================
    // Edge Cases
    // =========================================================================

    #[test]
    fn zero_sized_type() {
        let mut slab = DynamicSlab::<()>::new().unwrap();
        let k1 = slab.insert(()).unwrap();
        let k2 = slab.insert(()).unwrap();
        assert_eq!(slab.len(), 2);
        slab.remove(k1);
        assert_eq!(slab.len(), 1);
        slab.remove(k2);
        assert!(slab.is_empty());
    }

    #[test]
    fn large_value() {
        #[derive(Debug, Clone)]
        struct Big([u8; 4096]);

        let mut slab = DynamicSlab::<Big>::new().unwrap();
        let key = slab.insert(Big([42; 4096])).unwrap();
        assert_eq!(slab.get(key).0[0], 42);
        assert_eq!(slab.get(key).0[4095], 42);
    }

    #[test]
    fn string_values() {
        let mut slab = DynamicSlab::<String>::new().unwrap();
        let k1 = slab.insert("hello".to_string()).unwrap();
        let k2 = slab.insert("world".to_string()).unwrap();

        assert_eq!(slab.get(k1), "hello");
        assert_eq!(slab.get(k2), "world");

        slab.remove(k1);
        slab.remove(k2);
        assert!(slab.is_empty());
    }
}
