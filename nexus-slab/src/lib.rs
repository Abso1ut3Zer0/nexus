//! High-performance pre-allocated slab with page-aligned memory.
//!
//! `nexus-slab` provides a fixed-capacity container that:
//! - Uses direct OS allocation (`mmap`/`VirtualAlloc`) for page-aligned memory
//! - Prefaults all pages at allocation to avoid runtime page faults
//! - Optionally locks pages in RAM to prevent swapping
//! - Provides O(1) insert, get, and remove operations
//!
//! # Example
//!
//! ```no_run
//! use nexus_slab::Slab;
//!
//! // Create and allocate in one step (preferred)
//! let mut slab = Slab::<String>::with_capacity(1000)?;
//! println!("Allocated {} bytes for {} slots", slab.memory_size(), slab.capacity());
//!
//! // Optionally lock in RAM for latency-critical applications
//! if let Err(e) = slab.mlock() {
//!     eprintln!("Warning: mlock failed: {}", e);
//! }
//!
//! let key = slab.insert("hello".to_string())?;
//! assert_eq!(slab.get(key), Some(&"hello".to_string()));
//!
//! let removed = slab.remove(key);
//! assert_eq!(removed, Some("hello".to_string()));
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```
//!
//! # Allocation Modes
//!
//! Two allocation methods support different mental models:
//!
//! ```no_run
//! use nexus_slab::Slab;
//!
//! // Business logic: "I need space for 100K orders"
//! let mut orders = Slab::<Order>::with_capacity(100_000)?;
//!
//! // Systems/ops: "I have 256MB budget for this cache"
//! let mut cache = Slab::<CacheEntry>::with_capacity_bytes(256 * 1024 * 1024)?;
//! # struct Order; struct CacheEntry;
//! # Ok::<(), std::io::Error>(())
//! ```
//!
//! # Key Safety
//!
//! **Important:** Like the `slab` crate, it is the caller's responsibility
//! to not use stale keys. Accessing a slot after it has been removed and
//! reused will return the new value, not an error.
//!
//! # Thread-Local Pattern
//!
//! For `thread_local!` which requires const initialization, use the unsafe
//! [`new_unallocated`](Slab::new_unallocated) constructor:
//!
//! ```no_run
//! use std::cell::RefCell;
//! use nexus_slab::Slab;
//!
//! thread_local! {
//!     // SAFETY: We call alloc() in init() before any other use
//!     static ORDERS: RefCell<Slab<u64>> = const {
//!         RefCell::new(unsafe { Slab::new_unallocated() })
//!     };
//! }
//!
//! fn init() -> std::io::Result<()> {
//!     ORDERS.with(|cell| {
//!         let bytes = cell.borrow_mut().alloc(10_000)?;
//!         println!("Thread-local slab: {} bytes", bytes);
//!         Ok(())
//!     })
//! }
//! ```
//!
//! # Platform Support
//!
//! - **Unix** (Linux, macOS, BSD): Fully supported
//! - **Windows**: Experimental, requires `unstable-windows` feature

#![warn(missing_docs)]

pub mod sys;

use std::fmt;
use std::io;
use std::marker::PhantomData;
use std::ptr;

use sys::Pages;

/// Sentinel value for empty free list.
const NONE: u32 = u32::MAX;

/// Compute slot size with natural alignment.
const fn slot_size<T>() -> usize {
    std::mem::size_of::<Slot<T>>()
}

/// A slot in the slab - either vacant (part of free list) or occupied with a value.
///
/// This enum-based design keeps the discriminant and data on the same cache line,
/// matching the slab crate's proven approach.
enum Slot<T> {
    /// Slot is empty and part of the free list.
    Vacant { next_free: u32 },
    /// Slot contains a value.
    Occupied { value: T },
}

/// Handle to a value in the slab.
///
/// Keys are simple indices. It is the caller's responsibility to not use
/// stale keys after removal - accessing a removed-and-reused slot will
/// return the new value.
///
/// Keys are `Copy` and can be stored in other data structures.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct Key(u32);

impl Key {
    /// Returns the raw index.
    #[inline]
    pub const fn index(self) -> u32 {
        self.0
    }

    /// Creates a key from a raw index.
    ///
    /// # Safety
    ///
    /// The caller must ensure the index refers to a valid, occupied slot.
    #[inline]
    pub const unsafe fn from_raw(index: u32) -> Self {
        Self(index)
    }
}

/// Error returned when the slab is full.
///
/// Contains the value that could not be inserted, allowing recovery.
#[derive(Debug)]
pub struct Full<T>(
    /// The value that could not be inserted.
    pub T,
);

impl<T> Full<T> {
    /// Returns the value that could not be inserted.
    pub fn into_inner(self) -> T {
        self.0
    }
}

impl<T> fmt::Display for Full<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "slab is full")
    }
}

impl<T: fmt::Debug> std::error::Error for Full<T> {}

/// A pre-allocated slab with fixed capacity.
///
/// See [crate-level documentation](crate) for details.
#[repr(C)]
pub struct Slab<T> {
    // === Hot path (first cache line) ===
    /// Direct pointer to slot buffer. Null if unallocated.
    buffer: *mut Slot<T>,

    /// Head of the LIFO free list, or NONE if full.
    /// When in sequential mode (no holes), equals `len`.
    free_head: u32,

    /// Number of occupied slots.
    len: u32,

    /// Total number of slots.
    capacity: u32,

    /// Padding for alignment.
    _pad: u32,

    // === Cold path ===
    /// Backing memory pages. Kept for Drop/mlock/munlock.
    pages: Option<Pages>,

    /// Marker for T ownership.
    _marker: PhantomData<T>,
}

impl<T> Slab<T> {
    /// Creates a new slab with at least the specified capacity.
    ///
    /// This is the preferred constructor. Memory is allocated and prefaulted
    /// immediately, so the slab is ready to use.
    ///
    /// The actual capacity may be higher due to page alignment.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - `min_capacity` is zero
    /// - Memory allocation fails
    ///
    /// # Example
    ///
    /// ```no_run
    /// use nexus_slab::Slab;
    ///
    /// let mut slab = Slab::<u64>::with_capacity(1000)?;
    /// assert!(slab.capacity() >= 1000);
    /// # Ok::<(), std::io::Error>(())
    /// ```
    pub fn with_capacity(min_capacity: usize) -> io::Result<Self> {
        // SAFETY: We immediately call alloc() before returning
        let mut slab = unsafe { Self::new_unallocated() };
        slab.alloc(min_capacity)?;
        Ok(slab)
    }

    /// Creates a new slab using at most the specified number of bytes.
    ///
    /// This is useful when working within a memory budget rather than
    /// a specific item count.
    ///
    /// The actual memory usage may be lower due to page alignment.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - `max_bytes` is smaller than one page
    /// - Memory allocation fails
    ///
    /// # Example
    ///
    /// ```no_run
    /// use nexus_slab::Slab;
    ///
    /// // Allocate up to 1MB for the cache
    /// let mut cache = Slab::<CacheEntry>::with_capacity_bytes(1024 * 1024)?;
    /// # struct CacheEntry;
    /// # Ok::<(), std::io::Error>(())
    /// ```
    pub fn with_capacity_bytes(max_bytes: usize) -> io::Result<Self> {
        // SAFETY: We immediately call alloc_bytes() before returning
        let mut slab = unsafe { Self::new_unallocated() };
        slab.alloc_bytes(max_bytes)?;
        Ok(slab)
    }

    /// Creates a new slab backed by reserved huge pages (hugetlbfs).
    ///
    /// Unlike regular allocation which uses Transparent Huge Pages (THP)
    /// as a hint, this method **guarantees** huge pages are used or fails.
    /// This provides deterministic performance without TLB pressure.
    ///
    /// # System Setup Required
    ///
    /// Huge pages must be reserved before use:
    ///
    /// ```bash
    /// # Reserve 512 huge pages (1GB on x86_64 with 2MB pages)
    /// echo 512 | sudo tee /proc/sys/vm/nr_hugepages
    ///
    /// # Or permanently via /etc/sysctl.conf:
    /// # vm.nr_hugepages = 512
    ///
    /// # Or via kernel boot parameter:
    /// # hugepages=512
    /// ```
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - No huge pages are reserved on the system
    /// - Not enough free huge pages for the requested capacity
    /// - Platform doesn't support hugetlbfs (non-Linux)
    ///
    /// # Example
    ///
    /// ```no_run
    /// use nexus_slab::Slab;
    ///
    /// // Allocate with guaranteed huge pages
    /// let mut slab = Slab::<Order>::with_capacity_hugetlb(100_000)?;
    /// # struct Order;
    /// # Ok::<(), std::io::Error>(())
    /// ```
    #[cfg(target_os = "linux")]
    pub fn with_capacity_hugetlb(min_capacity: usize) -> io::Result<Self> {
        // SAFETY: We immediately call alloc_hugetlb() before returning
        let mut slab = unsafe { Self::new_unallocated() };
        slab.alloc_hugetlb(min_capacity)?;
        Ok(slab)
    }

    /// Creates an unallocated slab for use in contexts requiring const initialization.
    ///
    /// # Safety
    ///
    /// This function is unsafe because the returned slab is in an uninitialized state.
    /// The caller must ensure [`alloc`](Self::alloc) or [`alloc_bytes`](Self::alloc_bytes)
    /// is called before any operations that access slots.
    ///
    /// While using an unallocated slab won't cause undefined behavior (operations
    /// will fail gracefully with `Full` or `None`), it violates the expected
    /// invariant that a constructed slab is ready to use.
    ///
    /// # Use Case
    ///
    /// This exists primarily for `thread_local!` which requires const initialization:
    ///
    /// ```no_run
    /// use std::cell::RefCell;
    /// use nexus_slab::Slab;
    ///
    /// thread_local! {
    ///     // SAFETY: We call alloc() in init() before any other use
    ///     static ORDERS: RefCell<Slab<u64>> = const {
    ///         RefCell::new(unsafe { Slab::new_unallocated() })
    ///     };
    /// }
    ///
    /// fn init() -> std::io::Result<()> {
    ///     ORDERS.with(|cell| cell.borrow_mut().alloc(10_000))?;
    ///     Ok(())
    /// }
    /// ```
    ///
    /// For normal use, prefer [`with_capacity`](Self::with_capacity).
    #[must_use]
    pub const unsafe fn new_unallocated() -> Self {
        Self {
            buffer: std::ptr::null_mut(),
            free_head: NONE,
            len: 0,
            capacity: 0,
            _pad: 0,
            pages: None,
            _marker: PhantomData,
        }
    }

    /// Allocates memory for at least `min_capacity` items.
    ///
    /// The actual capacity may be higher due to page alignment.
    /// Returns the number of bytes allocated.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The slab is already allocated
    /// - `min_capacity` is zero
    /// - Memory allocation fails
    pub fn alloc(&mut self, min_capacity: usize) -> io::Result<usize> {
        if self.is_allocated() {
            return Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                "slab already allocated",
            ));
        }

        if min_capacity == 0 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "capacity must be non-zero",
            ));
        }

        if min_capacity > u32::MAX as usize {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "capacity exceeds maximum",
            ));
        }

        let slot_size = slot_size::<T>();
        let page_size = sys::page_size();
        let slots_per_page = (page_size / slot_size).max(1);

        // Round UP to guarantee minimum capacity
        let num_pages = (min_capacity + slots_per_page - 1) / slots_per_page;

        self.alloc_pages(num_pages, false)
    }

    /// Allocates memory using at most `max_bytes` of memory.
    ///
    /// The actual memory usage may be lower due to page alignment.
    /// Returns the number of bytes allocated.
    ///
    /// This is useful when working within a memory budget rather than
    /// a specific item count.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The slab is already allocated
    /// - `max_bytes` is smaller than one page
    /// - Memory allocation fails
    pub fn alloc_bytes(&mut self, max_bytes: usize) -> io::Result<usize> {
        if self.is_allocated() {
            return Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                "slab already allocated",
            ));
        }

        let page_size = sys::page_size();

        // Round DOWN to guarantee memory budget
        let num_pages = max_bytes / page_size;

        if num_pages == 0 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!(
                    "max_bytes ({}) smaller than one page ({})",
                    max_bytes, page_size
                ),
            ));
        }

        self.alloc_pages(num_pages, false)
    }

    /// Allocates memory backed by reserved huge pages (hugetlbfs).
    ///
    /// This is the deferred allocation version of [`with_capacity_hugetlb`].
    ///
    /// # System Setup Required
    ///
    /// See [`with_capacity_hugetlb`](Self::with_capacity_hugetlb) for setup instructions.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The slab is already allocated
    /// - `min_capacity` is zero
    /// - No huge pages are reserved/available
    #[cfg(target_os = "linux")]
    pub fn alloc_hugetlb(&mut self, min_capacity: usize) -> io::Result<usize> {
        if self.is_allocated() {
            return Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                "slab already allocated",
            ));
        }

        if min_capacity == 0 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "capacity must be non-zero",
            ));
        }

        if min_capacity > u32::MAX as usize {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "capacity exceeds maximum",
            ));
        }

        let slot_size = slot_size::<T>();
        let huge_page_size = sys::huge_page_size();
        let slots_per_page = (huge_page_size / slot_size).max(1);

        // Round UP to guarantee minimum capacity
        let num_pages = (min_capacity + slots_per_page - 1) / slots_per_page;

        self.alloc_pages(num_pages, true)
    }

    /// Internal: allocate exactly `num_pages` pages.
    #[cfg(target_os = "linux")]
    fn alloc_pages(&mut self, num_pages: usize, use_hugetlb: bool) -> io::Result<usize> {
        let slot_size = slot_size::<T>();
        let page_size = if use_hugetlb {
            sys::huge_page_size()
        } else {
            sys::page_size()
        };
        let slots_per_page = (page_size / slot_size).max(1);

        let capacity = num_pages * slots_per_page;
        let total_size = num_pages * page_size;

        if capacity > u32::MAX as usize {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "capacity exceeds maximum",
            ));
        }

        let pages = if use_hugetlb {
            Pages::alloc_hugetlb(total_size)?
        } else {
            Pages::alloc(total_size)?
        };

        // Set buffer pointer first
        self.buffer = pages.as_ptr() as *mut Slot<T>;

        // Initialize free list - all slots point to next (sequential layout)
        // This enables the sequential fast path on first fill
        for i in 0..capacity {
            let slot_ptr = unsafe { self.buffer.add(i) };
            let next = if i + 1 < capacity {
                (i + 1) as u32
            } else {
                NONE
            };
            unsafe {
                ptr::write(slot_ptr, Slot::Vacant { next_free: next });
            }
        }

        self.pages = Some(pages);
        self.capacity = capacity as u32;
        self.free_head = 0; // Start in sequential mode

        Ok(total_size)
    }

    /// Internal: allocate exactly `num_pages` pages (non-Linux version).
    #[cfg(not(target_os = "linux"))]
    fn alloc_pages(&mut self, num_pages: usize, _use_hugetlb: bool) -> io::Result<usize> {
        let slot_size = slot_size::<T>();
        let page_size = sys::page_size();
        let slots_per_page = (page_size / slot_size).max(1);

        let capacity = num_pages * slots_per_page;
        let total_size = num_pages * page_size;

        if capacity > u32::MAX as usize {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "capacity exceeds maximum",
            ));
        }

        let pages = Pages::alloc(total_size)?;

        // Set buffer pointer first
        self.buffer = pages.as_ptr() as *mut Slot<T>;

        // Initialize free list - all slots point to next (sequential layout)
        // This enables the sequential fast path on first fill
        for i in 0..capacity {
            let slot_ptr = unsafe { self.buffer.add(i) };
            let next = if i + 1 < capacity {
                (i + 1) as u32
            } else {
                NONE
            };
            unsafe {
                ptr::write(slot_ptr, Slot::Vacant { next_free: next });
            }
        }

        self.pages = Some(pages);
        self.capacity = capacity as u32;
        self.free_head = 0; // Start in sequential mode

        Ok(total_size)
    }

    /// Returns `true` if memory has been allocated.
    #[inline]
    pub fn is_allocated(&self) -> bool {
        !self.buffer.is_null()
    }

    /// Returns a pointer to the slot at the given index.
    #[inline(always)]
    unsafe fn slot_ptr(&self, index: u32) -> *mut Slot<T> {
        unsafe { self.buffer.add(index as usize) }
    }

    /// Inserts a value into the slab, returning a key.
    ///
    /// The key can be used to retrieve or remove the value later.
    ///
    /// # Errors
    ///
    /// Returns `Err(Full(value))` if the slab is full or not allocated.
    #[inline]
    pub fn insert(&mut self, value: T) -> Result<Key, Full<T>> {
        // Fast path: sequential fill (no holes from removals)
        // When len == free_head, slots 0..len are all occupied and
        // free_head points to the next available slot (which is at index len)
        if self.len == self.free_head && self.len < self.capacity {
            let index = self.len;
            unsafe {
                ptr::write(self.slot_ptr(index), Slot::Occupied { value });
            }
            self.len += 1;
            // Advance free_head, or set to NONE if now full
            if self.len < self.capacity {
                self.free_head = self.len;
            } else {
                self.free_head = NONE;
            }
            return Ok(Key(index));
        }

        // Slow path: free list traversal (has holes from removals)
        if self.free_head == NONE {
            return Err(Full(value));
        }

        let index = self.free_head;

        // Safety: free_head is valid when not NONE and we're allocated
        let slot_ptr = unsafe { self.slot_ptr(index) };

        // Get next free from current slot
        let next_free = unsafe {
            match &*slot_ptr {
                Slot::Vacant { next_free } => *next_free,
                Slot::Occupied { .. } => std::hint::unreachable_unchecked(),
            }
        };

        // Write occupied slot
        unsafe {
            ptr::write(slot_ptr, Slot::Occupied { value });
        }

        self.free_head = next_free;
        self.len += 1;

        Ok(Key(index))
    }

    /// Returns a vacant entry that can be used to insert a value.
    ///
    /// This is useful for self-referential structures where the value
    /// needs to know its own key before being inserted.
    ///
    /// If the returned [`VacantEntry`] is dropped without calling
    /// [`insert`](VacantEntry::insert), the slot is automatically
    /// returned to the free list.
    ///
    /// # Errors
    ///
    /// Returns `Err(Full(()))` if the slab is full or not allocated.
    #[inline]
    pub fn vacant_entry(&mut self) -> Result<VacantEntry<'_, T>, Full<()>> {
        // Fast path: sequential fill
        if self.len == self.free_head && self.len < self.capacity {
            let index = self.len;
            // Advance free_head
            if self.len + 1 < self.capacity {
                self.free_head = self.len + 1;
            } else {
                self.free_head = NONE;
            }
            return Ok(VacantEntry {
                slab: self,
                index,
                inserted: false,
            });
        }

        // Slow path: free list
        if self.free_head == NONE {
            return Err(Full(()));
        }

        let index = self.free_head;

        // Safety: free_head is valid when not NONE and we're allocated
        let slot_ptr = unsafe { self.slot_ptr(index) };

        // Get next free and update head
        let next_free = unsafe {
            match &*slot_ptr {
                Slot::Vacant { next_free } => *next_free,
                Slot::Occupied { .. } => std::hint::unreachable_unchecked(),
            }
        };

        self.free_head = next_free;

        Ok(VacantEntry {
            slab: self,
            index,
            inserted: false,
        })
    }

    /// Removes a value from the slab by key.
    ///
    /// Returns `Some(value)` if the slot was occupied, `None` if it was empty.
    ///
    /// # Warning
    ///
    /// If the key refers to a slot that was previously removed and reused,
    /// this will remove the new value. It is the caller's responsibility
    /// to track key validity.
    #[inline]
    pub fn remove(&mut self, key: Key) -> Option<T> {
        let index = key.0;
        if index >= self.capacity {
            return None;
        }

        // Safety: index is bounds-checked
        let slot_ptr = unsafe { self.slot_ptr(index) };

        match unsafe { &*slot_ptr } {
            Slot::Vacant { .. } => None,
            Slot::Occupied { .. } => {
                // Swap the value
                let old_slot = std::mem::replace(
                    unsafe { &mut *slot_ptr },
                    Slot::Vacant {
                        next_free: self.free_head,
                    },
                );
                let value = match old_slot {
                    Slot::Occupied { value } => value,
                    Slot::Vacant { .. } => unsafe { std::hint::unreachable_unchecked() },
                };

                self.free_head = index;
                self.len -= 1;

                Some(value)
            }
        }
    }

    /// Returns a reference to the value for the given key.
    ///
    /// Returns `None` if the slot is not occupied.
    ///
    /// # Warning
    ///
    /// If the key refers to a slot that was previously removed and reused,
    /// this will return the new value. It is the caller's responsibility
    /// to track key validity.
    #[inline]
    pub fn get(&self, key: Key) -> Option<&T> {
        let index = key.0;
        if index >= self.capacity {
            return None;
        }

        // Safety: index is bounds-checked
        let slot = unsafe { &*self.slot_ptr(index) };

        match slot {
            Slot::Vacant { .. } => None,
            Slot::Occupied { value } => Some(value),
        }
    }

    /// Returns a mutable reference to the value for the given key.
    ///
    /// Returns `None` if the slot is not occupied.
    #[inline]
    pub fn get_mut(&mut self, key: Key) -> Option<&mut T> {
        let index = key.0;
        if index >= self.capacity {
            return None;
        }

        // Safety: index is bounds-checked
        let slot = unsafe { &mut *self.slot_ptr(index) };

        match slot {
            Slot::Vacant { .. } => None,
            Slot::Occupied { value } => Some(value),
        }
    }

    /// Returns a reference without bounds checking.
    ///
    /// # Safety
    ///
    /// The key must refer to a valid, occupied slot.
    #[inline]
    pub unsafe fn get_unchecked(&self, key: Key) -> &T {
        let slot = unsafe { &*self.slot_ptr(key.0) };
        match slot {
            Slot::Occupied { value } => value,
            Slot::Vacant { .. } => unsafe { std::hint::unreachable_unchecked() },
        }
    }

    /// Returns a mutable reference without bounds checking.
    ///
    /// # Safety
    ///
    /// The key must refer to a valid, occupied slot.
    #[inline]
    pub unsafe fn get_unchecked_mut(&mut self, key: Key) -> &mut T {
        let slot = unsafe { &mut *self.slot_ptr(key.0) };
        match slot {
            Slot::Occupied { value } => value,
            Slot::Vacant { .. } => unsafe { std::hint::unreachable_unchecked() },
        }
    }

    /// Removes without bounds checking.
    ///
    /// # Safety
    ///
    /// The key must refer to a valid, occupied slot.
    #[inline]
    pub unsafe fn remove_unchecked(&mut self, key: Key) -> T {
        let index = key.0;
        let slot_ptr = unsafe { self.slot_ptr(index) };

        let old_slot = std::mem::replace(
            unsafe { &mut *slot_ptr },
            Slot::Vacant {
                next_free: self.free_head,
            },
        );

        let value = match old_slot {
            Slot::Occupied { value } => value,
            Slot::Vacant { .. } => unsafe { std::hint::unreachable_unchecked() },
        };

        self.free_head = index;
        self.len -= 1;

        value
    }

    /// Returns `true` if the slot for the given key is occupied.
    #[inline]
    pub fn contains(&self, key: Key) -> bool {
        let index = key.0;
        if index >= self.capacity {
            return false;
        }

        let slot = unsafe { &*self.slot_ptr(index) };
        matches!(slot, Slot::Occupied { .. })
    }

    /// Returns the number of occupied slots.
    #[inline]
    pub const fn len(&self) -> usize {
        self.len as usize
    }

    /// Returns the total capacity (number of slots).
    ///
    /// Returns 0 if not allocated.
    #[inline]
    pub const fn capacity(&self) -> usize {
        self.capacity as usize
    }

    /// Returns `true` if no slots are occupied.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns `true` if all slots are occupied (or not allocated).
    #[inline]
    pub const fn is_full(&self) -> bool {
        self.free_head == NONE
    }

    /// Removes all values from the slab, resetting it to empty.
    ///
    /// This drops all contained values but keeps the underlying memory allocated.
    /// After clearing, the slab has `len() == 0` and all capacity is available.
    ///
    /// This also resets the slab to sequential mode, enabling the fast path
    /// for subsequent inserts.
    pub fn clear(&mut self) {
        if self.buffer.is_null() {
            return;
        }

        if self.len == 0 {
            // No values to drop, just reset to sequential mode
            self.free_head = 0;
            return;
        }

        // Drop all occupied values and rebuild free list
        for i in 0..self.capacity {
            let slot_ptr = unsafe { self.slot_ptr(i) };
            let slot = unsafe { &*slot_ptr };

            if let Slot::Occupied { .. } = slot {
                // Drop the value
                unsafe { ptr::drop_in_place(slot_ptr) };
            }

            // Rebuild free list: each slot points to next (sequential layout)
            let next = if i + 1 < self.capacity { i + 1 } else { NONE };
            unsafe {
                ptr::write(slot_ptr, Slot::Vacant { next_free: next });
            }
        }

        self.free_head = 0; // Reset to sequential mode
        self.len = 0;
    }

    /// Returns the total size of backing memory in bytes.
    ///
    /// Returns 0 if not allocated.
    #[inline]
    pub fn memory_size(&self) -> usize {
        self.pages.as_ref().map_or(0, |p| p.size())
    }

    /// Locks all pages in physical RAM, preventing swapping.
    ///
    /// This ensures memory accesses never trigger page faults due to
    /// swapping, which is critical for latency-sensitive applications.
    ///
    /// # Privileges
    ///
    /// Requires elevated privileges:
    /// - **Linux**: `CAP_IPC_LOCK` or sufficient `RLIMIT_MEMLOCK`
    /// - **macOS**: Generally works without special privileges
    /// - **Windows**: `SeLockMemoryPrivilege`
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The slab is not allocated
    /// - Insufficient privileges
    /// - Resource limits exceeded
    pub fn mlock(&self) -> io::Result<()> {
        match &self.pages {
            Some(pages) => pages.mlock(),
            None => Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "slab not allocated",
            )),
        }
    }

    /// Attempt to collapse regular pages into huge pages.
    ///
    /// This is a synchronous request to the kernel to collapse the backing
    /// 4KB pages into 2MB huge pages NOW, rather than waiting for the
    /// background `khugepaged` daemon.
    ///
    /// This is stronger than the THP hint given at allocation time, but
    /// still best-effort - it may partially succeed or fail entirely if
    /// contiguous physical memory is not available.
    ///
    /// # When to Use
    ///
    /// Call this after allocation but before the hot path begins:
    ///
    /// ```no_run
    /// use nexus_slab::Slab;
    ///
    /// let mut slab = Slab::<Order>::with_capacity(100_000)?;
    ///
    /// // Best effort - try to get huge pages
    /// if let Err(e) = slab.try_collapse() {
    ///     eprintln!("Warning: huge page collapse failed: {}", e);
    /// }
    ///
    /// // Now use slab in hot path...
    /// # struct Order;
    /// # Ok::<(), std::io::Error>(())
    /// ```
    ///
    /// # Compatibility
    ///
    /// - **Linux 6.1+**: Full support via `MADV_COLLAPSE`
    /// - **Older Linux**: Returns `Ok(())` (no-op)
    /// - **Other platforms**: Returns `Ok(())` (no-op)
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The slab is not allocated
    /// - The kernel rejects the request (e.g., severe memory pressure)
    pub fn try_collapse(&self) -> io::Result<()> {
        match &self.pages {
            Some(pages) => pages.try_collapse(),
            None => Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "slab not allocated",
            )),
        }
    }

    /// Unlocks pages, allowing them to be swapped.
    ///
    /// This is automatically done on drop, so explicit calls are rarely needed.
    ///
    /// # Errors
    ///
    /// Returns an error if the slab is not allocated.
    pub fn munlock(&self) -> io::Result<()> {
        match &self.pages {
            Some(pages) => pages.munlock(),
            None => Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "slab not allocated",
            )),
        }
    }
}

impl<T> Drop for Slab<T> {
    fn drop(&mut self) {
        if self.buffer.is_null() {
            return;
        }

        // Drop all occupied values
        for i in 0..self.capacity {
            let slot_ptr = unsafe { self.slot_ptr(i) };
            let slot = unsafe { &*slot_ptr };
            if let Slot::Occupied { .. } = slot {
                unsafe { ptr::drop_in_place(slot_ptr) };
            }
        }
        // Pages are dropped automatically
    }
}

// Safety: Slab owns its data and can be sent to another thread if T can be.
unsafe impl<T: Send> Send for Slab<T> {}

impl<T> fmt::Debug for Slab<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Slab")
            .field("allocated", &self.is_allocated())
            .field("len", &self.len)
            .field("capacity", &self.capacity)
            .field("memory_size", &self.memory_size())
            .finish()
    }
}

/// A vacant entry in the slab, ready to be filled.
///
/// Obtained from [`Slab::vacant_entry`]. This reserves a slot and provides
/// the key before the value is inserted, enabling self-referential structures.
///
/// If dropped without calling [`insert`](VacantEntry::insert), the slot is
/// automatically returned to the free list.
pub struct VacantEntry<'a, T> {
    slab: &'a mut Slab<T>,
    index: u32,
    inserted: bool,
}

impl<'a, T> VacantEntry<'a, T> {
    /// Returns the key that will be associated with the inserted value.
    #[inline]
    pub fn key(&self) -> Key {
        Key(self.index)
    }

    /// Inserts a value into the vacant entry, returning the key.
    #[inline]
    pub fn insert(mut self, value: T) -> Key {
        let key = self.key();

        // Safety: index is valid from vacant_entry creation
        let slot_ptr = unsafe { self.slab.slot_ptr(self.index) };
        unsafe {
            ptr::write(slot_ptr, Slot::Occupied { value });
        }
        self.slab.len += 1;

        self.inserted = true;
        key
    }
}

impl<T> Drop for VacantEntry<'_, T> {
    fn drop(&mut self) {
        if !self.inserted {
            // Return slot to free list
            let slot_ptr = unsafe { self.slab.slot_ptr(self.index) };
            unsafe {
                ptr::write(
                    slot_ptr,
                    Slot::Vacant {
                        next_free: self.slab.free_head,
                    },
                );
            }
            self.slab.free_head = self.index;
        }
    }
}

impl<T> fmt::Debug for VacantEntry<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("VacantEntry")
            .field("key", &self.key())
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ============================================================================
    // Memory Layout Tests
    // ============================================================================

    #[test]
    fn key_size() {
        assert_eq!(std::mem::size_of::<Key>(), 4);
    }

    #[test]
    fn slot_size_u64() {
        // Slot<u64> = enum tag (8 bytes due to alignment) + u64 (8 bytes) = 16 bytes
        let size = slot_size::<u64>();
        println!("Slot<u64> size: {} bytes", size);
        assert_eq!(size, 16);
    }

    #[test]
    fn slab_struct_layout() {
        // Verify hot fields are at the start
        let size = std::mem::size_of::<Slab<u64>>();
        println!("Slab<u64> size: {} bytes", size);
        // buffer(8) + free_head(4) + len(4) + capacity(4) + _pad(4) = 24 bytes hot
        // + Option<Pages> + PhantomData
    }

    // ============================================================================
    // Constructor Tests
    // ============================================================================

    #[test]
    fn with_capacity_allocates() {
        let slab = Slab::<u64>::with_capacity(100).unwrap();
        assert!(slab.is_allocated());
        assert!(slab.capacity() >= 100);
    }

    #[test]
    fn with_capacity_bytes_respects_budget() {
        let budget = 64 * 1024;
        let slab = Slab::<u64>::with_capacity_bytes(budget).unwrap();
        assert!(slab.is_allocated());
        assert!(slab.memory_size() <= budget);
        assert!(slab.capacity() > 0);
    }

    #[test]
    fn new_unallocated_is_unallocated() {
        let slab: Slab<u64> = unsafe { Slab::new_unallocated() };
        assert!(!slab.is_allocated());
        assert_eq!(slab.capacity(), 0);
    }

    #[test]
    fn new_unallocated_then_alloc() {
        let mut slab: Slab<u64> = unsafe { Slab::new_unallocated() };
        assert!(!slab.is_allocated());

        slab.alloc(100).unwrap();
        assert!(slab.is_allocated());
        assert!(slab.capacity() >= 100);
    }

    // ============================================================================
    // Unallocated Behavior
    // ============================================================================

    #[test]
    fn unallocated_state() {
        let slab: Slab<u64> = unsafe { Slab::new_unallocated() };

        assert!(!slab.is_allocated());
        assert_eq!(slab.capacity(), 0);
        assert_eq!(slab.len(), 0);
        assert!(slab.is_empty());
        assert!(slab.is_full());
        assert_eq!(slab.memory_size(), 0);
    }

    #[test]
    fn unallocated_insert_fails() {
        let mut slab: Slab<u64> = unsafe { Slab::new_unallocated() };
        let result = slab.insert(42);
        assert!(result.is_err());
    }

    #[test]
    fn unallocated_get_returns_none() {
        let slab: Slab<u64> = unsafe { Slab::new_unallocated() };
        assert_eq!(slab.get(Key(0)), None);
    }

    // ============================================================================
    // Allocation
    // ============================================================================

    #[test]
    fn alloc_returns_bytes() {
        let mut slab: Slab<u64> = unsafe { Slab::new_unallocated() };
        let bytes = slab.alloc(100).unwrap();

        assert!(bytes > 0);
        assert_eq!(bytes, slab.memory_size());
        assert!(slab.is_allocated());
        assert!(slab.capacity() >= 100);
    }

    #[test]
    fn double_alloc_fails() {
        let mut slab = Slab::<u64>::with_capacity(100).unwrap();

        assert!(slab.alloc(100).is_err());
        assert!(slab.alloc_bytes(4096).is_err());
    }

    #[test]
    fn alloc_zero_fails() {
        let mut slab: Slab<u64> = unsafe { Slab::new_unallocated() };
        assert!(slab.alloc(0).is_err());
    }

    // ============================================================================
    // Basic Operations
    // ============================================================================

    #[test]
    fn insert_get_remove() {
        let mut slab = Slab::<u64>::with_capacity(16).unwrap();

        let key = slab.insert(42).unwrap();
        assert_eq!(slab.get(key), Some(&42));
        assert_eq!(slab.len(), 1);

        assert_eq!(slab.remove(key), Some(42));
        assert_eq!(slab.get(key), None);
        assert_eq!(slab.len(), 0);
    }

    #[test]
    fn get_mut_modifies_value() {
        let mut slab = Slab::<u64>::with_capacity(16).unwrap();

        let key = slab.insert(10).unwrap();
        *slab.get_mut(key).unwrap() = 20;

        assert_eq!(slab.get(key), Some(&20));
    }

    #[test]
    fn contains() {
        let mut slab = Slab::<u64>::with_capacity(16).unwrap();

        let key = slab.insert(42).unwrap();
        assert!(slab.contains(key));

        slab.remove(key);
        assert!(!slab.contains(key));
    }

    // ============================================================================
    // Sequential Fast Path
    // ============================================================================

    #[test]
    fn sequential_insert_uses_fast_path() {
        let mut slab = Slab::<u64>::with_capacity(8).unwrap();

        // Sequential inserts should use indices 0, 1, 2, ...
        let k0 = slab.insert(0).unwrap();
        let k1 = slab.insert(1).unwrap();
        let k2 = slab.insert(2).unwrap();

        assert_eq!(k0.index(), 0);
        assert_eq!(k1.index(), 1);
        assert_eq!(k2.index(), 2);
    }

    #[test]
    fn remove_breaks_sequential_mode() {
        let mut slab = Slab::<u64>::with_capacity(8).unwrap();

        let k0 = slab.insert(0).unwrap();
        let k1 = slab.insert(1).unwrap();
        let _k2 = slab.insert(2).unwrap();

        // Remove from middle
        slab.remove(k1);

        // Next insert should reuse k1's slot (LIFO free list)
        let k3 = slab.insert(3).unwrap();
        assert_eq!(k3.index(), k1.index());

        // Next insert should reuse k0's slot? No, k0 wasn't removed.
        // It should use next free (slot 3 originally, but we're in free list mode now)
        slab.remove(k0);
        let k4 = slab.insert(4).unwrap();
        assert_eq!(k4.index(), k0.index()); // LIFO: last removed is first reused
    }

    #[test]
    fn clear_resets_to_sequential_mode() {
        let mut slab = Slab::<u64>::with_capacity(8).unwrap();

        // Fill with holes
        let k0 = slab.insert(0).unwrap();
        let k1 = slab.insert(1).unwrap();
        slab.remove(k0);
        slab.remove(k1);

        // Clear should reset to sequential mode
        slab.clear();

        // Now inserts should be sequential again
        let k0 = slab.insert(10).unwrap();
        let k1 = slab.insert(11).unwrap();
        assert_eq!(k0.index(), 0);
        assert_eq!(k1.index(), 1);
    }

    // ============================================================================
    // Slot Reuse (No Generation Protection)
    // ============================================================================

    #[test]
    fn slot_reuse_returns_new_value() {
        let mut slab = Slab::<u64>::with_capacity(16).unwrap();

        // Fill sequentially first, then remove to enter free list mode
        let _k0 = slab.insert(0).unwrap();
        let key1 = slab.insert(100).unwrap();
        slab.remove(key1);

        let key2 = slab.insert(200).unwrap();

        // Same index reused (LIFO)
        assert_eq!(key1.0, key2.0);

        // Old key now sees new value (caller's responsibility to track!)
        assert_eq!(slab.get(key1), Some(&200));
    }

    #[test]
    fn lifo_free_list() {
        let mut slab = Slab::<u64>::with_capacity(16).unwrap();

        let k0 = slab.insert(0).unwrap();
        let k1 = slab.insert(1).unwrap();
        let k2 = slab.insert(2).unwrap();

        slab.remove(k0);
        slab.remove(k2);
        slab.remove(k1);

        // LIFO: k1 removed last, reused first
        let new_key = slab.insert(100).unwrap();
        assert_eq!(new_key.0, k1.0);
    }

    // ============================================================================
    // Capacity and Fullness
    // ============================================================================

    #[test]
    fn fill_to_capacity() {
        let mut slab = Slab::<u64>::with_capacity(4).unwrap();
        let capacity = slab.capacity();

        let mut keys = Vec::new();
        for i in 0..capacity {
            keys.push(slab.insert(i as u64).unwrap());
        }

        assert!(slab.is_full());
        assert_eq!(slab.len(), capacity);
        assert!(slab.insert(999).is_err());
    }

    #[test]
    fn full_insert_returns_value() {
        let mut slab = Slab::<String>::with_capacity(1).unwrap();
        let capacity = slab.capacity();

        for i in 0..capacity {
            slab.insert(format!("item-{}", i)).unwrap();
        }

        let result = slab.insert("overflow".to_string());
        match result {
            Err(Full(s)) => assert_eq!(s, "overflow"),
            Ok(_) => panic!("expected full error"),
        }
    }

    // ============================================================================
    // Type Variety
    // ============================================================================

    #[test]
    fn zero_sized_type() {
        let mut slab = Slab::<()>::with_capacity(16).unwrap();

        let k1 = slab.insert(()).unwrap();
        let k2 = slab.insert(()).unwrap();

        assert_eq!(slab.get(k1), Some(&()));
        assert_eq!(slab.get(k2), Some(&()));
    }

    #[test]
    fn string_type() {
        let mut slab = Slab::<String>::with_capacity(16).unwrap();

        let key = slab.insert("hello world".to_string()).unwrap();
        assert_eq!(slab.get(key), Some(&"hello world".to_string()));
    }

    #[test]
    fn large_aligned_type() {
        #[derive(Debug)]
        #[repr(C, align(128))]
        struct BigAligned {
            data: [u8; 256],
        }

        let mut slab = Slab::<BigAligned>::with_capacity(16).unwrap();

        let key = slab.insert(BigAligned { data: [42; 256] }).unwrap();
        assert_eq!(slab.get(key).unwrap().data[0], 42);
    }

    // ============================================================================
    // Drop Behavior
    // ============================================================================

    #[test]
    fn drop_cleans_up_values() {
        use std::sync::atomic::{AtomicUsize, Ordering};

        static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

        #[derive(Debug)]
        struct DropCounter;
        impl Drop for DropCounter {
            fn drop(&mut self) {
                DROP_COUNT.fetch_add(1, Ordering::SeqCst);
            }
        }

        DROP_COUNT.store(0, Ordering::SeqCst);

        {
            let mut slab = Slab::<DropCounter>::with_capacity(16).unwrap();
            slab.insert(DropCounter).unwrap();
            slab.insert(DropCounter).unwrap();
            slab.insert(DropCounter).unwrap();
        }

        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), 3);
    }

    #[test]
    fn remove_drops_value() {
        use std::sync::atomic::{AtomicUsize, Ordering};

        static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

        #[derive(Debug)]
        struct DropCounter;
        impl Drop for DropCounter {
            fn drop(&mut self) {
                DROP_COUNT.fetch_add(1, Ordering::SeqCst);
            }
        }

        DROP_COUNT.store(0, Ordering::SeqCst);

        let mut slab = Slab::<DropCounter>::with_capacity(16).unwrap();

        let key = slab.insert(DropCounter).unwrap();
        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), 0);

        slab.remove(key);
        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), 1);
    }

    // ============================================================================
    // Vacant Entry
    // ============================================================================

    #[test]
    fn vacant_entry_basic() {
        let mut slab = Slab::<u64>::with_capacity(16).unwrap();

        let entry = slab.vacant_entry().unwrap();
        let key = entry.key();
        let returned_key = entry.insert(42);

        assert_eq!(key, returned_key);
        assert_eq!(slab.get(key), Some(&42));
    }

    #[test]
    fn vacant_entry_self_referential() {
        #[derive(Debug, PartialEq)]
        struct Node {
            self_key: Key,
            data: u64,
        }

        let mut slab = Slab::<Node>::with_capacity(16).unwrap();

        let entry = slab.vacant_entry().unwrap();
        let key = entry.key();
        entry.insert(Node {
            self_key: key,
            data: 42,
        });

        let node = slab.get(key).unwrap();
        assert_eq!(node.self_key, key);
        assert_eq!(node.data, 42);
    }

    #[test]
    fn vacant_entry_drop_returns_to_free_list() {
        let mut slab = Slab::<u64>::with_capacity(16).unwrap();

        {
            let entry = slab.vacant_entry().unwrap();
            let _key = entry.key();
            // Dropped without insert
        }

        assert_eq!(slab.len(), 0);
        assert!(!slab.is_full());
    }

    // ============================================================================
    // Unchecked Operations
    // ============================================================================

    #[test]
    fn get_unchecked_works() {
        let mut slab = Slab::<u64>::with_capacity(16).unwrap();
        let key = slab.insert(42).unwrap();

        let val = unsafe { slab.get_unchecked(key) };
        assert_eq!(*val, 42);
    }

    #[test]
    fn get_unchecked_mut_works() {
        let mut slab = Slab::<u64>::with_capacity(16).unwrap();
        let key = slab.insert(42).unwrap();

        unsafe {
            *slab.get_unchecked_mut(key) = 100;
        }
        assert_eq!(slab.get(key), Some(&100));
    }

    #[test]
    fn remove_unchecked_works() {
        let mut slab = Slab::<u64>::with_capacity(16).unwrap();
        let key = slab.insert(42).unwrap();

        let val = unsafe { slab.remove_unchecked(key) };
        assert_eq!(val, 42);
        assert_eq!(slab.len(), 0);
    }

    // ============================================================================
    // Stress Tests
    // ============================================================================

    #[test]
    fn stress_insert_remove_cycle() {
        let mut slab = Slab::<u64>::with_capacity(1).unwrap();

        for i in 0..10_000u64 {
            let key = slab.insert(i).unwrap();
            assert_eq!(slab.get(key), Some(&i));
            assert_eq!(slab.remove(key), Some(i));
        }
    }

    #[test]
    fn stress_fill_drain_cycles() {
        let mut slab = Slab::<u64>::with_capacity(64).unwrap();
        let capacity = slab.capacity();

        for _ in 0..100 {
            let mut keys = Vec::with_capacity(capacity);

            for i in 0..capacity {
                keys.push(slab.insert(i as u64).unwrap());
            }
            assert!(slab.is_full());

            for key in keys {
                slab.remove(key);
            }
            assert!(slab.is_empty());
        }
    }

    // ============================================================================
    // Send Safety
    // ============================================================================

    #[test]
    fn slab_is_send() {
        fn assert_send<T: Send>() {}
        assert_send::<Slab<u64>>();
        assert_send::<Slab<String>>();
    }

    #[test]
    fn move_across_threads() {
        use std::thread;

        let mut slab = Slab::<u64>::with_capacity(100).unwrap();

        let key = slab.insert(42).unwrap();

        let handle = thread::spawn(move || {
            assert_eq!(slab.get(key), Some(&42));
            slab.remove(key);
            slab
        });

        let slab = handle.join().unwrap();
        assert_eq!(slab.len(), 0);
    }

    // ============================================================================
    // Key Properties
    // ============================================================================

    #[test]
    fn key_is_copy() {
        fn assert_copy<T: Copy>() {}
        assert_copy::<Key>();
    }

    #[test]
    fn key_is_eq() {
        assert_eq!(Key(1), Key(1));
        assert_ne!(Key(1), Key(2));
    }

    #[test]
    fn key_is_hashable() {
        use std::collections::HashMap;

        let mut slab = Slab::<u64>::with_capacity(16).unwrap();

        let key = slab.insert(42).unwrap();

        let mut map = HashMap::new();
        map.insert(key, "value");

        assert_eq!(map.get(&key), Some(&"value"));
    }

    // ============================================================================
    // Debug Impls
    // ============================================================================

    #[test]
    fn slab_debug_format() {
        let slab = Slab::<u64>::with_capacity(16).unwrap();
        let debug_str = format!("{:?}", slab);
        assert!(debug_str.contains("Slab"));
    }

    #[test]
    fn key_debug_format() {
        let key = Key(42);
        let debug_str = format!("{:?}", key);
        assert!(debug_str.contains("42"));
    }

    // ============================================================================
    // Clear
    // ============================================================================

    #[test]
    fn clear_empties_slab() {
        let mut slab = Slab::<u64>::with_capacity(16).unwrap();

        let k1 = slab.insert(1).unwrap();
        let k2 = slab.insert(2).unwrap();
        let k3 = slab.insert(3).unwrap();

        assert_eq!(slab.len(), 3);

        slab.clear();

        assert_eq!(slab.len(), 0);
        assert!(slab.is_empty());
        assert!(!slab.is_full());
        assert_eq!(slab.get(k1), None);
        assert_eq!(slab.get(k2), None);
        assert_eq!(slab.get(k3), None);
    }

    #[test]
    fn clear_allows_reuse() {
        let mut slab = Slab::<u64>::with_capacity(16).unwrap();

        for i in 0..10 {
            slab.insert(i).unwrap();
        }
        slab.clear();

        // Can insert again
        for i in 0..10 {
            slab.insert(i * 100).unwrap();
        }
        assert_eq!(slab.len(), 10);
    }

    #[test]
    fn clear_drops_values() {
        use std::sync::atomic::{AtomicUsize, Ordering};

        static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

        #[derive(Debug)]
        struct DropCounter;
        impl Drop for DropCounter {
            fn drop(&mut self) {
                DROP_COUNT.fetch_add(1, Ordering::SeqCst);
            }
        }

        DROP_COUNT.store(0, Ordering::SeqCst);

        let mut slab = Slab::<DropCounter>::with_capacity(16).unwrap();

        slab.insert(DropCounter).unwrap();
        slab.insert(DropCounter).unwrap();
        slab.insert(DropCounter).unwrap();

        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), 0);

        slab.clear();

        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), 3);
    }

    #[test]
    fn clear_on_empty_is_noop() {
        let mut slab = Slab::<u64>::with_capacity(16).unwrap();

        slab.clear(); // Should not panic
        assert_eq!(slab.len(), 0);
    }

    #[test]
    fn clear_on_unallocated_is_noop() {
        let mut slab: Slab<u64> = unsafe { Slab::new_unallocated() };
        slab.clear(); // Should not panic
        assert_eq!(slab.len(), 0);
    }
}
