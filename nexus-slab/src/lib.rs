//! High-performance pre-allocated slab with generational indices.
//!
//! `nexus-slab` provides a fixed-capacity container that:
//! - Uses direct OS allocation (`mmap`/`VirtualAlloc`) for page-aligned memory
//! - Prefaults all pages at allocation to avoid runtime page faults
//! - Uses generation counters to detect stale keys and prevent use-after-free
//! - Uses power-of-two slot sizes for bit-shift indexing (no division)
//! - Optionally locks pages in RAM to prevent swapping
//!
//! # Example
//!
//! ```no_run
//! use nexus_slab::Slab;
//!
//! // Create unallocated, then allocate
//! let mut slab: Slab<String> = Slab::new();
//! let bytes = slab.alloc(1000)?;
//! println!("Allocated {} bytes for {} slots", bytes, slab.capacity());
//!
//! // Optionally lock in RAM for latency-critical applications
//! if let Err(e) = slab.mlock() {
//!     eprintln!("Warning: mlock failed: {}", e);
//! }
//!
//! let key = slab.insert("hello".to_string())?;
//! assert_eq!(slab.get(key), Some(&"hello".to_string()));
//!
//! slab.remove(key);
//! assert_eq!(slab.get(key), None); // Generation mismatch
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
//! let mut orders: Slab<Order> = Slab::new();
//! orders.alloc(100_000)?;  // Capacity >= 100K guaranteed
//!
//! // Systems/ops: "I have 256MB budget for this cache"
//! let mut cache: Slab<CacheEntry> = Slab::new();
//! cache.alloc_bytes(256 * 1024 * 1024)?;  // Memory <= 256MB guaranteed
//! # struct Order; struct CacheEntry;
//! # Ok::<(), std::io::Error>(())
//! ```
//!
//! # Key Safety
//!
//! Keys cannot be fabricated - they can only be obtained from [`Slab::insert`].
//! Each key contains a generation counter that is checked on every access,
//! preventing use-after-free bugs:
//!
//! ```no_run
//! # use nexus_slab::Slab;
//! # let mut slab: Slab<u64> = Slab::new();
//! # slab.alloc(16)?;
//! let key1 = slab.insert(100)?;
//! slab.remove(key1);
//!
//! let key2 = slab.insert(200)?; // Reuses same slot
//!
//! // Old key is invalid even though it points to an occupied slot
//! assert_eq!(slab.get(key1), None);
//! assert_eq!(slab.get(key2), Some(&200));
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```
//!
//! # Thread-Local Pattern
//!
//! The const constructor enables thread-local usage:
//!
//! ```no_run
//! use std::cell::RefCell;
//! use nexus_slab::Slab;
//!
//! thread_local! {
//!     static ORDERS: RefCell<Slab<u64>> = const { RefCell::new(Slab::new()) };
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
use std::mem::ManuallyDrop;

use sys::Pages;

/// Sentinel value for empty free list.
const NONE: u32 = u32::MAX;

/// Compute padded slot size as next power of two.
const fn padded_slot_size<T>() -> usize {
    let base_size = std::mem::size_of::<Slot<T>>();
    let align = std::mem::align_of::<Slot<T>>();

    // Ensure at least alignment
    let size = if base_size < align { align } else { base_size };

    // Round to next power of two
    size.next_power_of_two()
}

/// Compute shift amount for indexing: index << shift = byte offset.
const fn slot_shift<T>() -> u32 {
    padded_slot_size::<T>().trailing_zeros()
}

/// A slot in the slab, either occupied with a value or part of the free list.
#[repr(C)]
struct Slot<T> {
    /// Generation counter, incremented on each insert.
    generation: u64,

    /// 0 = free, 1 = occupied.
    occupied: u32,

    /// Padding for alignment.
    _padding: u32,

    /// The actual data or free list link.
    data: SlotData<T>,
}

/// Union to overlay value storage with free list pointer.
union SlotData<T> {
    /// The stored value when slot is occupied.
    value: ManuallyDrop<T>,

    /// Index of next free slot when this slot is free.
    next_free: u32,
}

/// Opaque handle to a value in the slab.
///
/// Keys can only be obtained from [`Slab::insert`] and contain a generation
/// counter that is validated on every access. This prevents stale key access
/// and use-after-free bugs when a slot is reused.
///
/// Keys are `Copy` and can be stored in other data structures (e.g., `HashMap`,
/// `Vec`) to reference slab entries.
///
/// # Layout
///
/// Keys are 16 bytes (128 bits):
/// - 32-bit index (max ~4.3B slots)
/// - 64-bit generation (effectively infinite reuse cycles)
#[derive(Copy, Clone, Eq, PartialEq, Hash)]
#[repr(C, align(16))]
pub struct Key {
    index: u32,
    _padding: u32,
    generation: u64,
}

const _: () = assert!(std::mem::size_of::<Key>() == 16);

impl Key {
    #[inline]
    fn new(index: u32, generation: u64) -> Self {
        Self {
            index,
            _padding: 0,
            generation,
        }
    }

    #[inline]
    fn index(self) -> u32 {
        self.index
    }

    #[inline]
    fn generation(self) -> u64 {
        self.generation
    }
}

impl fmt::Debug for Key {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Key")
            .field("index", &self.index)
            .field("generation", &self.generation)
            .finish()
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

/// A pre-allocated slab with fixed capacity and generational indices.
///
/// See [crate-level documentation](crate) for details.
pub struct Slab<T> {
    /// Backing memory pages, None if not yet allocated.
    pages: Option<Pages>,

    /// Total number of slots.
    capacity: u32,

    /// Number of occupied slots.
    len: u32,

    /// Head of the LIFO free list, or NONE if full.
    free_head: u32,

    /// Bit shift for slot indexing: index << slot_shift = byte offset.
    slot_shift: u32,

    /// Marker for T ownership.
    _marker: PhantomData<T>,
}

impl<T> Slab<T> {
    /// Creates an unallocated slab.
    ///
    /// No memory is allocated until [`alloc`](Self::alloc) or
    /// [`alloc_bytes`](Self::alloc_bytes) is called.
    ///
    /// An unallocated slab has zero capacity and behaves as if full:
    /// - `insert()` returns `Err(Full)`
    /// - `get()` returns `None`
    /// - `capacity()` returns `0`
    ///
    /// This is a const function, enabling use in statics and thread-locals.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_slab::Slab;
    ///
    /// const SLAB: Slab<u64> = Slab::new();
    /// ```
    #[must_use]
    pub const fn new() -> Self {
        Self {
            pages: None,
            capacity: 0,
            len: 0,
            free_head: NONE,
            slot_shift: slot_shift::<T>(),
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
    ///
    /// # Example
    ///
    /// ```no_run
    /// use nexus_slab::Slab;
    ///
    /// let mut slab: Slab<u64> = Slab::new();
    /// let bytes = slab.alloc(10_000)?;
    /// println!("Allocated {} bytes for {} slots", bytes, slab.capacity());
    /// # Ok::<(), std::io::Error>(())
    /// ```
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

        let slot_size = padded_slot_size::<T>();
        let page_size = sys::page_size();
        let slots_per_page = (page_size / slot_size).max(1);

        // Round UP to guarantee minimum capacity
        let num_pages = (min_capacity + slots_per_page - 1) / slots_per_page;

        self.alloc_pages(num_pages)
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
    ///
    /// # Example
    ///
    /// ```no_run
    /// use nexus_slab::Slab;
    ///
    /// let mut cache: Slab<[u8; 256]> = Slab::new();
    /// let bytes = cache.alloc_bytes(64 * 1024 * 1024)?; // 64MB budget
    /// println!("Allocated {} bytes for {} slots", bytes, cache.capacity());
    /// # Ok::<(), std::io::Error>(())
    /// ```
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

        self.alloc_pages(num_pages)
    }

    /// Internal: allocate exactly `num_pages` pages.
    fn alloc_pages(&mut self, num_pages: usize) -> io::Result<usize> {
        let slot_size = padded_slot_size::<T>();
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

        // Initialize free list
        let base = pages.as_ptr();
        for i in 0..capacity {
            // Safety: i is within allocated capacity
            let slot = unsafe { &mut *(base.add(i << self.slot_shift) as *mut Slot<T>) };
            slot.generation = 0;
            slot.occupied = 0;
            slot._padding = 0;
            slot.data.next_free = if i + 1 < capacity {
                (i + 1) as u32
            } else {
                NONE
            };
        }

        self.pages = Some(pages);
        self.capacity = capacity as u32;
        self.free_head = 0;

        Ok(total_size)
    }

    /// Returns `true` if memory has been allocated.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_slab::Slab;
    ///
    /// let mut slab: Slab<u64> = Slab::new();
    /// assert!(!slab.is_allocated());
    ///
    /// // slab.alloc(100).unwrap();
    /// // assert!(slab.is_allocated());
    /// ```
    #[inline]
    pub const fn is_allocated(&self) -> bool {
        self.pages.is_some()
    }

    /// Returns a pointer to the slot at the given index.
    ///
    /// # Safety
    ///
    /// Caller must ensure `index < capacity` and slab is allocated.
    #[inline]
    unsafe fn slot_ptr(&self, index: u32) -> *mut Slot<T> {
        debug_assert!(index < self.capacity);
        debug_assert!(self.is_allocated());

        unsafe {
            let base = self.pages.as_ref().unwrap_unchecked().as_ptr();
            base.add((index as usize) << self.slot_shift) as *mut Slot<T>
        }
    }

    /// Inserts a value into the slab, returning a key.
    ///
    /// The key can be used to retrieve or remove the value later.
    ///
    /// # Errors
    ///
    /// Returns `Err(Full(value))` if the slab is full or not allocated.
    ///
    /// # Example
    ///
    /// ```no_run
    /// # use nexus_slab::Slab;
    /// # let mut slab: Slab<u64> = Slab::new();
    /// # slab.alloc(16)?;
    /// let key = slab.insert(42)?;
    /// assert_eq!(slab.get(key), Some(&42));
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn insert(&mut self, value: T) -> Result<Key, Full<T>> {
        if self.free_head == NONE {
            return Err(Full(value));
        }

        let index = self.free_head;

        // Safety: free_head is valid when not NONE and we're allocated
        let slot = unsafe { &mut *self.slot_ptr(index) };

        // Pop from free list
        self.free_head = unsafe { slot.data.next_free };

        // Increment generation and write value
        slot.generation = slot.generation.wrapping_add(1);
        slot.occupied = 1;
        slot.data.value = ManuallyDrop::new(value);

        self.len += 1;

        Ok(Key::new(index, slot.generation))
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
    ///
    /// # Example
    ///
    /// ```no_run
    /// # use nexus_slab::{Slab, Key};
    /// struct Node {
    ///     self_key: Key,
    ///     data: u64,
    /// }
    ///
    /// let mut slab: Slab<Node> = Slab::new();
    /// slab.alloc(100)?;
    ///
    /// let entry = slab.vacant_entry()?;
    /// let key = entry.key();
    /// entry.insert(Node { self_key: key, data: 42 });
    ///
    /// // The node knows its own key
    /// assert_eq!(slab.get(key).unwrap().self_key, key);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn vacant_entry(&mut self) -> Result<VacantEntry<'_, T>, Full<()>> {
        if self.free_head == NONE {
            return Err(Full(()));
        }

        let index = self.free_head;

        // Safety: free_head is valid when not NONE and we're allocated
        let slot = unsafe { &mut *self.slot_ptr(index) };

        // Pop from free list
        self.free_head = unsafe { slot.data.next_free };

        // Increment generation now so the key is stable
        slot.generation = slot.generation.wrapping_add(1);
        let generation = slot.generation;

        // Note: occupied stays 0 until insert() is called
        // Note: len is not incremented until insert() is called

        Ok(VacantEntry {
            slab: self,
            index,
            generation,
            inserted: false,
        })
    }

    /// Removes a value from the slab by key.
    ///
    /// Returns `Some(value)` if the key was valid, `None` if the key was
    /// stale or invalid.
    ///
    /// # Example
    ///
    /// ```no_run
    /// # use nexus_slab::Slab;
    /// # let mut slab: Slab<String> = Slab::new();
    /// # slab.alloc(16)?;
    /// let key = slab.insert("hello".to_string())?;
    /// assert_eq!(slab.remove(key), Some("hello".to_string()));
    /// assert_eq!(slab.remove(key), None); // Already removed
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn remove(&mut self, key: Key) -> Option<T> {
        let index = key.index();
        if index >= self.capacity {
            return None;
        }

        // Safety: index is bounds-checked
        let slot = unsafe { &mut *self.slot_ptr(index) };

        // Validate generation and occupancy
        if slot.generation != key.generation() || slot.occupied == 0 {
            return None;
        }

        // Take the value
        let value = unsafe { ManuallyDrop::take(&mut slot.data.value) };

        // Mark as free and push to free list (LIFO)
        slot.occupied = 0;
        slot.data.next_free = self.free_head;
        self.free_head = index;

        self.len -= 1;

        Some(value)
    }

    /// Returns a reference to the value for the given key.
    ///
    /// Returns `None` if the key is stale or invalid.
    ///
    /// # Example
    ///
    /// ```no_run
    /// # use nexus_slab::Slab;
    /// # let mut slab: Slab<u64> = Slab::new();
    /// # slab.alloc(16)?;
    /// let key = slab.insert(42)?;
    /// assert_eq!(slab.get(key), Some(&42));
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn get(&self, key: Key) -> Option<&T> {
        let index = key.index();
        if index >= self.capacity {
            return None;
        }

        // Safety: index is bounds-checked
        let slot = unsafe { &*self.slot_ptr(index) };

        if slot.generation != key.generation() || slot.occupied == 0 {
            return None;
        }

        Some(unsafe { &slot.data.value })
    }

    /// Returns a mutable reference to the value for the given key.
    ///
    /// Returns `None` if the key is stale or invalid.
    #[inline]
    pub fn get_mut(&mut self, key: Key) -> Option<&mut T> {
        let index = key.index();
        if index >= self.capacity {
            return None;
        }

        // Safety: index is bounds-checked
        let slot = unsafe { &mut *self.slot_ptr(index) };

        if slot.generation != key.generation() || slot.occupied == 0 {
            return None;
        }

        Some(unsafe { &mut slot.data.value })
    }

    /// Returns an entry providing guaranteed-valid access to a value.
    ///
    /// The returned [`Entry`] proves the key is valid, so its methods
    /// are infallible (no `Option` wrapper).
    ///
    /// # Example
    ///
    /// ```no_run
    /// # use nexus_slab::Slab;
    /// # let mut slab: Slab<String> = Slab::new();
    /// # slab.alloc(16)?;
    /// let key = slab.insert("hello".to_string())?;
    ///
    /// if let Some(mut entry) = slab.entry(key) {
    ///     entry.get_mut().push_str(" world");
    ///     assert_eq!(entry.get(), "hello world");
    /// }
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn entry(&mut self, key: Key) -> Option<Entry<'_, T>> {
        let index = key.index();
        if index >= self.capacity {
            return None;
        }

        // Safety: index is bounds-checked
        let slot = unsafe { &mut *self.slot_ptr(index) };

        if slot.generation != key.generation() || slot.occupied == 0 {
            return None;
        }

        Some(Entry {
            slot,
            _marker: PhantomData,
        })
    }

    /// Returns `true` if the key is valid and points to an occupied slot.
    #[inline]
    pub fn contains(&self, key: Key) -> bool {
        self.get(key).is_some()
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
    ///
    /// # Example
    ///
    /// ```no_run
    /// # use nexus_slab::Slab;
    /// let mut slab: Slab<u64> = Slab::new();
    /// slab.alloc(10_000)?;
    ///
    /// match slab.mlock() {
    ///     Ok(()) => println!("Pages locked in RAM"),
    ///     Err(e) => eprintln!("Warning: mlock failed: {}", e),
    /// }
    /// # Ok::<(), std::io::Error>(())
    /// ```
    pub fn mlock(&self) -> io::Result<()> {
        match &self.pages {
            Some(pages) => pages.mlock(),
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

impl<T> Default for Slab<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Drop for Slab<T> {
    fn drop(&mut self) {
        if self.pages.is_none() {
            return;
        }

        // Drop all occupied values
        for i in 0..self.capacity {
            // Safety: i is within capacity and we're allocated
            let slot = unsafe { &mut *self.slot_ptr(i) };
            if slot.occupied != 0 {
                unsafe { ManuallyDrop::drop(&mut slot.data.value) };
            }
        }
        // Pages are dropped automatically via Option<Pages>::drop
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

/// An entry providing guaranteed-valid access to a slot.
///
/// Obtained from [`Slab::entry`]. The existence of an `Entry` proves the
/// key was valid at the time of lookup, so access methods are infallible.
///
/// The borrow checker ensures the slab cannot be modified (including removing
/// this entry) while the `Entry` exists.
pub struct Entry<'a, T> {
    slot: &'a mut Slot<T>,
    _marker: PhantomData<&'a mut Slab<T>>,
}

impl<'a, T> Entry<'a, T> {
    /// Returns a reference to the value.
    ///
    /// This is infallible because `Entry` existence proves validity.
    #[inline]
    pub fn get(&self) -> &T {
        // Safety: Entry can only be created for valid, occupied slots
        unsafe { &self.slot.data.value }
    }

    /// Returns a mutable reference to the value.
    ///
    /// This is infallible because `Entry` existence proves validity.
    #[inline]
    pub fn get_mut(&mut self) -> &mut T {
        // Safety: Entry can only be created for valid, occupied slots
        unsafe { &mut self.slot.data.value }
    }
}

impl<T: fmt::Debug> fmt::Debug for Entry<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Entry").field(self.get()).finish()
    }
}

/// A vacant entry in the slab, ready to be filled.
///
/// Obtained from [`Slab::vacant_entry`]. This reserves a slot and provides
/// the key before the value is inserted, enabling self-referential structures.
///
/// If dropped without calling [`insert`](VacantEntry::insert), the slot is
/// automatically returned to the free list.
///
/// # Example
///
/// ```no_run
/// # use nexus_slab::Slab;
/// struct Node {
///     key: nexus_slab::Key,
///     data: u64,
/// }
///
/// let mut slab: Slab<Node> = Slab::new();
/// slab.alloc(100)?;
///
/// let entry = slab.vacant_entry()?;
/// let key = entry.key();
/// entry.insert(Node { key, data: 42 });
///
/// assert_eq!(slab.get(key).unwrap().key, key);
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
pub struct VacantEntry<'a, T> {
    slab: &'a mut Slab<T>,
    index: u32,
    generation: u64,
    inserted: bool,
}

impl<'a, T> VacantEntry<'a, T> {
    /// Returns the key that will be associated with the inserted value.
    ///
    /// This key is valid immediately and can be embedded in the value
    /// being inserted.
    #[inline]
    pub fn key(&self) -> Key {
        Key::new(self.index, self.generation)
    }

    /// Inserts a value into the vacant entry, returning the key.
    ///
    /// This consumes the `VacantEntry`. The returned key is the same
    /// as what [`key`](VacantEntry::key) would have returned.
    ///
    /// # Example
    ///
    /// ```no_run
    /// # use nexus_slab::Slab;
    /// let mut slab: Slab<u64> = Slab::new();
    /// slab.alloc(100)?;
    ///
    /// let entry = slab.vacant_entry()?;
    /// let key = entry.insert(42);
    ///
    /// assert_eq!(slab.get(key), Some(&42));
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[inline]
    pub fn insert(mut self, value: T) -> Key {
        let key = self.key();

        // Safety: index is valid from vacant_entry creation
        let slot = unsafe { &mut *self.slab.slot_ptr(self.index) };
        slot.occupied = 1;
        slot.data.value = ManuallyDrop::new(value);
        self.slab.len += 1;

        // Mark as inserted so Drop doesn't return to free list
        self.inserted = true;

        key
    }
}

impl<T> Drop for VacantEntry<'_, T> {
    fn drop(&mut self) {
        if !self.inserted {
            // Return slot to free list
            // Safety: index is valid from vacant_entry creation
            let slot = unsafe { &mut *self.slab.slot_ptr(self.index) };
            slot.data.next_free = self.slab.free_head;
            self.slab.free_head = self.index;
            // Note: generation was already incremented, that's fine - it just
            // means this abandoned key will never accidentally match
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
    fn key_size_and_alignment() {
        assert_eq!(std::mem::size_of::<Key>(), 16);
        assert_eq!(std::mem::align_of::<Key>(), 16);
    }

    #[test]
    fn key_field_offsets() {
        let key = Key::new(0xDEADBEEF, 0x123456789ABCDEF0);
        assert_eq!(key.index(), 0xDEADBEEF);
        assert_eq!(key.generation(), 0x123456789ABCDEF0);
    }

    #[test]
    fn slot_size_is_power_of_two() {
        assert!(padded_slot_size::<u8>().is_power_of_two());
        assert!(padded_slot_size::<u64>().is_power_of_two());
        assert!(padded_slot_size::<[u8; 100]>().is_power_of_two());
        assert!(padded_slot_size::<[u8; 1000]>().is_power_of_two());
    }

    #[test]
    fn slot_shift_matches_size() {
        assert_eq!(1 << slot_shift::<u8>(), padded_slot_size::<u8>());
        assert_eq!(1 << slot_shift::<u64>(), padded_slot_size::<u64>());
        assert_eq!(
            1 << slot_shift::<[u8; 100]>(),
            padded_slot_size::<[u8; 100]>()
        );
    }

    // ============================================================================
    // Const Construction
    // ============================================================================

    #[test]
    fn const_new() {
        const SLAB: Slab<u64> = Slab::new();
        assert!(!SLAB.is_allocated());
        assert_eq!(SLAB.capacity(), 0);
    }

    #[test]
    fn default_is_unallocated() {
        let slab: Slab<u64> = Slab::default();
        assert!(!slab.is_allocated());
    }

    // ============================================================================
    // Unallocated Behavior
    // ============================================================================

    #[test]
    fn unallocated_state() {
        let slab: Slab<u64> = Slab::new();

        assert!(!slab.is_allocated());
        assert_eq!(slab.capacity(), 0);
        assert_eq!(slab.len(), 0);
        assert!(slab.is_empty());
        assert!(slab.is_full());
        assert_eq!(slab.memory_size(), 0);
    }

    #[test]
    fn unallocated_insert_fails() {
        let mut slab: Slab<u64> = Slab::new();
        let result = slab.insert(42);
        assert!(result.is_err());

        // Value is returned
        match result {
            Err(Full(v)) => assert_eq!(v, 42),
            Ok(_) => panic!("expected Full error"),
        }
    }

    #[test]
    fn unallocated_get_returns_none() {
        let slab: Slab<u64> = Slab::new();
        let fake_key = Key::new(0, 1);
        assert_eq!(slab.get(fake_key), None);
    }

    #[test]
    fn unallocated_mlock_fails() {
        let slab: Slab<u64> = Slab::new();
        assert!(slab.mlock().is_err());
    }

    #[test]
    fn unallocated_munlock_fails() {
        let slab: Slab<u64> = Slab::new();
        assert!(slab.munlock().is_err());
    }

    // ============================================================================
    // Allocation
    // ============================================================================

    #[test]
    fn alloc_returns_bytes() {
        let mut slab: Slab<u64> = Slab::new();
        let bytes = slab.alloc(100).unwrap();

        assert!(bytes > 0);
        assert_eq!(bytes, slab.memory_size());
        assert!(slab.is_allocated());
        assert!(slab.capacity() >= 100);
    }

    #[test]
    fn alloc_rounds_up_capacity() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(100).unwrap();

        // Capacity is at least what we asked for
        assert!(slab.capacity() >= 100);
    }

    #[test]
    fn alloc_bytes_respects_budget() {
        let mut slab: Slab<u64> = Slab::new();
        let budget = 64 * 1024; // 64KB
        let bytes = slab.alloc_bytes(budget).unwrap();

        // Never exceeds budget
        assert!(bytes <= budget);
        assert!(bytes > 0);
        assert!(slab.capacity() > 0);
    }

    #[test]
    fn alloc_bytes_rounds_down() {
        let page_size = sys::page_size();
        let mut slab: Slab<u64> = Slab::new();

        // Request 1.5 pages, should get 1 page
        let bytes = slab.alloc_bytes(page_size + page_size / 2).unwrap();
        assert_eq!(bytes, page_size);
    }

    #[test]
    fn double_alloc_fails() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(100).unwrap();

        assert!(slab.alloc(100).is_err());
        assert!(slab.alloc_bytes(4096).is_err());
    }

    #[test]
    fn alloc_zero_fails() {
        let mut slab: Slab<u64> = Slab::new();
        assert!(slab.alloc(0).is_err());
    }

    #[test]
    fn alloc_bytes_too_small_fails() {
        let mut slab: Slab<u64> = Slab::new();
        assert!(slab.alloc_bytes(100).is_err()); // Less than page size
    }

    #[test]
    fn memory_is_page_aligned() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(100).unwrap();

        let page_size = sys::page_size();
        assert_eq!(slab.memory_size() % page_size, 0);
    }

    // ============================================================================
    // Basic Operations
    // ============================================================================

    #[test]
    fn insert_get_remove() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(16).unwrap();

        let key = slab.insert(42).unwrap();
        assert_eq!(slab.get(key), Some(&42));
        assert_eq!(slab.len(), 1);

        assert_eq!(slab.remove(key), Some(42));
        assert_eq!(slab.get(key), None);
        assert_eq!(slab.len(), 0);
    }

    #[test]
    fn get_mut_modifies_value() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(16).unwrap();

        let key = slab.insert(10).unwrap();
        *slab.get_mut(key).unwrap() = 20;

        assert_eq!(slab.get(key), Some(&20));
    }

    #[test]
    fn contains() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(16).unwrap();

        let key = slab.insert(42).unwrap();
        assert!(slab.contains(key));

        slab.remove(key);
        assert!(!slab.contains(key));
    }

    #[test]
    fn entry_api() {
        let mut slab: Slab<String> = Slab::new();
        slab.alloc(16).unwrap();

        let key = slab.insert("hello".to_string()).unwrap();

        {
            let mut entry = slab.entry(key).unwrap();
            entry.get_mut().push_str(" world");
            assert_eq!(entry.get(), "hello world");
        }

        assert_eq!(slab.get(key), Some(&"hello world".to_string()));
    }

    #[test]
    fn entry_on_invalid_key_returns_none() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(16).unwrap();

        let key = slab.insert(42).unwrap();
        slab.remove(key);

        assert!(slab.entry(key).is_none());
    }

    // ============================================================================
    // Stale Key Detection (Use-After-Free Prevention)
    // ============================================================================

    #[test]
    fn generation_prevents_stale_access() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(16).unwrap();

        let key1 = slab.insert(100).unwrap();
        slab.remove(key1);

        let key2 = slab.insert(200).unwrap();

        // Same index, different generation
        assert_eq!(key1.index(), key2.index());
        assert_ne!(key1.generation(), key2.generation());

        // Old key returns None
        assert_eq!(slab.get(key1), None);
        assert_eq!(slab.get_mut(key1), None);
        assert_eq!(slab.remove(key1), None);

        // New key works
        assert_eq!(slab.get(key2), Some(&200));
    }

    #[test]
    fn generation_increments_on_reuse() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(1).unwrap();

        let mut prev_gen = 0;
        for i in 0..100 {
            let key = slab.insert(i).unwrap();
            assert!(key.generation() > prev_gen);
            prev_gen = key.generation();
            slab.remove(key);
        }
    }

    #[test]
    fn stale_key_to_occupied_slot_fails() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(16).unwrap();

        let key1 = slab.insert(100).unwrap();
        slab.remove(key1);
        let _key2 = slab.insert(200).unwrap();

        // key1 points to an occupied slot but with wrong generation
        assert_eq!(slab.get(key1), None);
    }

    // ============================================================================
    // Invalid Key Handling
    // ============================================================================

    #[test]
    fn out_of_bounds_index_returns_none() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(16).unwrap();

        let fake_key = Key::new(999999, 1);
        assert_eq!(slab.get(fake_key), None);
        assert_eq!(slab.get_mut(fake_key), None);
        assert_eq!(slab.remove(fake_key), None);
        assert!(slab.entry(fake_key).is_none());
    }

    #[test]
    fn wrong_generation_returns_none() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(16).unwrap();

        let key = slab.insert(42).unwrap();
        let bad_key = Key::new(key.index(), key.generation() + 1);

        assert_eq!(slab.get(bad_key), None);
    }

    #[test]
    fn key_to_free_slot_returns_none() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(16).unwrap();

        let key = slab.insert(42).unwrap();
        slab.remove(key);

        // Same generation but slot is now free
        assert_eq!(slab.get(key), None);
    }

    // ============================================================================
    // Capacity and Fullness
    // ============================================================================

    #[test]
    fn fill_to_capacity() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(4).unwrap();
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
        let mut slab: Slab<String> = Slab::new();
        slab.alloc(1).unwrap();
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

    #[test]
    fn lifo_free_list() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(16).unwrap();

        let k0 = slab.insert(0).unwrap();
        let k1 = slab.insert(1).unwrap();
        let k2 = slab.insert(2).unwrap();

        slab.remove(k0);
        slab.remove(k2);
        slab.remove(k1);

        // LIFO: k1 removed last, reused first
        let new_key = slab.insert(100).unwrap();
        assert_eq!(new_key.index(), k1.index());
    }

    // ============================================================================
    // Type Variety
    // ============================================================================

    #[test]
    fn zero_sized_type() {
        let mut slab: Slab<()> = Slab::new();
        slab.alloc(16).unwrap();

        let k1 = slab.insert(()).unwrap();
        let k2 = slab.insert(()).unwrap();

        assert_eq!(slab.get(k1), Some(&()));
        assert_eq!(slab.get(k2), Some(&()));

        slab.remove(k1);
        assert_eq!(slab.get(k1), None);
    }

    #[test]
    fn string_type() {
        let mut slab: Slab<String> = Slab::new();
        slab.alloc(16).unwrap();

        let key = slab.insert("hello world".to_string()).unwrap();
        assert_eq!(slab.get(key), Some(&"hello world".to_string()));
    }

    #[test]
    fn vec_type() {
        let mut slab: Slab<Vec<u64>> = Slab::new();
        slab.alloc(16).unwrap();

        let key = slab.insert(vec![1, 2, 3, 4, 5]).unwrap();
        assert_eq!(slab.get(key), Some(&vec![1, 2, 3, 4, 5]));
    }

    #[test]
    fn large_aligned_type() {
        #[derive(Debug)]
        #[repr(C, align(128))]
        struct BigAligned {
            data: [u8; 256],
        }

        let mut slab: Slab<BigAligned> = Slab::new();
        slab.alloc(16).unwrap();

        let key = slab.insert(BigAligned { data: [42; 256] }).unwrap();
        assert_eq!(slab.get(key).unwrap().data[0], 42);
        assert_eq!(slab.get(key).unwrap().data[255], 42);
    }

    #[test]
    fn option_type() {
        let mut slab: Slab<Option<u64>> = Slab::new();
        slab.alloc(16).unwrap();

        let k1 = slab.insert(Some(42)).unwrap();
        let k2 = slab.insert(None).unwrap();

        assert_eq!(slab.get(k1), Some(&Some(42)));
        assert_eq!(slab.get(k2), Some(&None));
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
            let mut slab: Slab<DropCounter> = Slab::new();
            slab.alloc(16).unwrap();
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

        let mut slab: Slab<DropCounter> = Slab::new();
        slab.alloc(16).unwrap();

        let key = slab.insert(DropCounter).unwrap();
        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), 0);

        slab.remove(key);
        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn partial_fill_drop() {
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
            let mut slab: Slab<DropCounter> = Slab::new();
            slab.alloc(100).unwrap();

            // Only insert a few
            slab.insert(DropCounter).unwrap();
            slab.insert(DropCounter).unwrap();

            // Remove one
            let key = slab.insert(DropCounter).unwrap();
            slab.remove(key); // Drop count = 1
        }
        // Remaining 2 dropped

        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), 3);
    }

    #[test]
    fn unallocated_drop_is_safe() {
        let slab: Slab<String> = Slab::new();
        drop(slab); // Should not panic
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

        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(100).unwrap();

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
        let k1 = Key::new(1, 100);
        let k2 = Key::new(1, 100);
        let k3 = Key::new(1, 101);
        let k4 = Key::new(2, 100);

        assert_eq!(k1, k2);
        assert_ne!(k1, k3);
        assert_ne!(k1, k4);
    }

    #[test]
    fn key_is_hashable() {
        use std::collections::HashMap;

        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(16).unwrap();

        let key = slab.insert(42).unwrap();

        let mut map = HashMap::new();
        map.insert(key, "value");

        assert_eq!(map.get(&key), Some(&"value"));
    }

    #[test]
    fn key_debug_format() {
        let key = Key::new(42, 7);
        let debug_str = format!("{:?}", key);
        assert!(debug_str.contains("42"));
        assert!(debug_str.contains("7"));
    }

    // ============================================================================
    // Stress Tests
    // ============================================================================

    #[test]
    fn stress_insert_remove_cycle() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(1).unwrap();

        for i in 0..10_000u64 {
            let key = slab.insert(i).unwrap();
            assert_eq!(slab.get(key), Some(&i));
            assert_eq!(slab.remove(key), Some(i));
        }
    }

    #[test]
    fn stress_fill_drain_cycles() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(64).unwrap();
        let capacity = slab.capacity();

        for cycle in 0..100 {
            let mut keys = Vec::with_capacity(capacity);

            // Fill
            for i in 0..capacity {
                let val = (cycle * capacity + i) as u64;
                keys.push(slab.insert(val).unwrap());
            }
            assert!(slab.is_full());

            // Drain
            for (i, key) in keys.iter().enumerate() {
                let expected = (cycle * capacity + i) as u64;
                assert_eq!(slab.remove(*key), Some(expected));
            }
            assert!(slab.is_empty());
        }
    }

    #[test]
    fn stress_random_operations() {
        use std::collections::HashMap;

        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(256).unwrap();

        let mut reference: HashMap<u32, u64> = HashMap::new();
        let mut next_val = 0u64;

        for i in 0..10_000 {
            if i % 3 != 0 && !slab.is_full() {
                // Insert
                let key = slab.insert(next_val).unwrap();
                reference.insert(key.index(), next_val);
                next_val += 1;
            } else if !slab.is_empty() {
                // Remove first valid key we find
                if let Some((&idx, _)) = reference.iter().next() {
                    // Find key with this index
                    for g in 1..1000u64 {
                        let key = Key::new(idx, g);
                        if let Some(val) = slab.remove(key) {
                            assert_eq!(reference.remove(&idx), Some(val));
                            break;
                        }
                    }
                }
            }
        }

        // Verify remaining entries
        assert_eq!(slab.len(), reference.len());
    }

    #[test]
    fn stress_many_generations() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(1).unwrap();

        let mut keys = Vec::new();

        // Accumulate many generations worth of stale keys
        for i in 0..1000u64 {
            let key = slab.insert(i).unwrap();
            keys.push(key);
            slab.remove(key);
        }

        // Insert one more
        let final_key = slab.insert(9999).unwrap();

        // All old keys should be invalid
        for key in &keys {
            assert_eq!(slab.get(*key), None);
        }

        // Current key works
        assert_eq!(slab.get(final_key), Some(&9999));
    }

    // ============================================================================
    // Determinism
    // ============================================================================

    #[test]
    fn deterministic_key_assignment() {
        let run = || {
            let mut slab: Slab<u64> = Slab::new();
            slab.alloc(16).unwrap();

            let k1 = slab.insert(1).unwrap();
            let k2 = slab.insert(2).unwrap();
            let k3 = slab.insert(3).unwrap();

            (k1, k2, k3)
        };

        let (a1, a2, a3) = run();
        let (b1, b2, b3) = run();

        assert_eq!(a1.index(), b1.index());
        assert_eq!(a2.index(), b2.index());
        assert_eq!(a3.index(), b3.index());
    }

    #[test]
    fn deterministic_after_remove() {
        let run = || {
            let mut slab: Slab<u64> = Slab::new();
            slab.alloc(16).unwrap();

            let k1 = slab.insert(1).unwrap();
            let k2 = slab.insert(2).unwrap();
            slab.remove(k1);
            let k3 = slab.insert(3).unwrap();

            (k1, k2, k3)
        };

        let (a1, a2, a3) = run();
        let (b1, b2, b3) = run();

        // k3 should reuse k1's slot
        assert_eq!(a3.index(), a1.index());
        assert_eq!(b3.index(), b1.index());
        assert_eq!(a2.index(), b2.index());
    }

    // ============================================================================
    // Debug Impls
    // ============================================================================

    #[test]
    fn slab_debug_format() {
        let slab: Slab<u64> = Slab::new();
        let debug_str = format!("{:?}", slab);
        assert!(debug_str.contains("Slab"));
        assert!(debug_str.contains("allocated"));
        assert!(debug_str.contains("len"));
        assert!(debug_str.contains("capacity"));
    }

    #[test]
    fn entry_debug_format() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(16).unwrap();

        let key = slab.insert(42).unwrap();
        let entry = slab.entry(key).unwrap();

        let debug_str = format!("{:?}", entry);
        assert!(debug_str.contains("Entry"));
        assert!(debug_str.contains("42"));
    }

    #[test]
    fn full_error_debug_format() {
        let err = Full(42u64);
        let debug_str = format!("{:?}", err);
        assert!(debug_str.contains("Full"));
        assert!(debug_str.contains("42"));
    }

    #[test]
    fn full_error_display_format() {
        let err = Full(42u64);
        let display_str = format!("{}", err);
        assert!(display_str.contains("full"));
    }

    // ============================================================================
    // Edge Cases
    // ============================================================================

    #[test]
    fn single_slot_slab() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(1).unwrap();

        // May have more than 1 slot due to page rounding
        let capacity = slab.capacity();
        assert!(capacity >= 1);

        // Verify we can cycle through insert/remove
        for i in 0..100 {
            let key = slab.insert(i).unwrap();
            assert_eq!(slab.get(key), Some(&i));
            slab.remove(key);
        }
    }

    #[test]
    fn large_allocation() {
        let mut slab: Slab<u64> = Slab::new();
        let bytes = slab.alloc(100_000).unwrap();

        assert!(slab.capacity() >= 100_000);
        assert!(bytes > 0);

        // Can actually use it
        let key = slab.insert(42).unwrap();
        assert_eq!(slab.get(key), Some(&42));
    }

    #[test]
    fn alloc_bytes_exact_page() {
        let page_size = sys::page_size();
        let mut slab: Slab<u64> = Slab::new();

        let bytes = slab.alloc_bytes(page_size).unwrap();
        assert_eq!(bytes, page_size);
    }

    #[test]
    fn alloc_bytes_multiple_pages() {
        let page_size = sys::page_size();
        let mut slab: Slab<u64> = Slab::new();

        let bytes = slab.alloc_bytes(page_size * 10).unwrap();
        assert_eq!(bytes, page_size * 10);
    }

    // ============================================================================
    // Vacant Entry Tests
    // ============================================================================

    #[test]
    fn vacant_entry_basic() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(16).unwrap();

        let entry = slab.vacant_entry().unwrap();
        let key = entry.key();
        let returned_key = entry.insert(42);

        assert_eq!(key, returned_key);
        assert_eq!(slab.get(key), Some(&42));
        assert_eq!(slab.len(), 1);
    }

    #[test]
    fn vacant_entry_self_referential() {
        #[derive(Debug, PartialEq)]
        struct Node {
            self_key: Key,
            data: u64,
        }

        let mut slab: Slab<Node> = Slab::new();
        slab.alloc(16).unwrap();

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
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(16).unwrap();

        let initial_capacity = slab.capacity();

        // Get a vacant entry but don't insert
        {
            let entry = slab.vacant_entry().unwrap();
            let _key = entry.key();
            // entry dropped here without insert
        }

        // Slot should be back in free list
        assert_eq!(slab.len(), 0);
        assert!(!slab.is_full());

        // Should be able to fill to capacity
        for i in 0..initial_capacity {
            slab.insert(i as u64).unwrap();
        }
        assert!(slab.is_full());
    }

    #[test]
    fn vacant_entry_abandoned_key_is_invalid() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(16).unwrap();

        // Get key from abandoned entry
        let abandoned_key = {
            let entry = slab.vacant_entry().unwrap();
            entry.key()
            // entry dropped here
        };

        // Insert something else (reuses same slot with different generation)
        let valid_key = slab.insert(42).unwrap();

        // Abandoned key should be invalid
        assert_eq!(slab.get(abandoned_key), None);

        // Valid key works
        assert_eq!(slab.get(valid_key), Some(&42));
    }

    #[test]
    fn vacant_entry_on_full_slab_fails() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(1).unwrap();
        let capacity = slab.capacity();

        // Fill it
        for i in 0..capacity {
            slab.insert(i as u64).unwrap();
        }

        // vacant_entry should fail
        assert!(slab.vacant_entry().is_err());
    }

    #[test]
    fn vacant_entry_on_unallocated_fails() {
        let mut slab: Slab<u64> = Slab::new();
        assert!(slab.vacant_entry().is_err());
    }

    #[test]
    fn vacant_entry_key_matches_insert_key() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(16).unwrap();

        let entry = slab.vacant_entry().unwrap();
        let pre_key = entry.key();
        let post_key = entry.insert(99);

        assert_eq!(pre_key, post_key);
        assert_eq!(pre_key.index(), post_key.index());
        assert_eq!(pre_key.generation(), post_key.generation());
    }

    #[test]
    fn vacant_entry_multiple_sequential() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(16).unwrap();

        let e1 = slab.vacant_entry().unwrap();
        let k1 = e1.insert(1);

        let e2 = slab.vacant_entry().unwrap();
        let k2 = e2.insert(2);

        let e3 = slab.vacant_entry().unwrap();
        let k3 = e3.insert(3);

        assert_eq!(slab.get(k1), Some(&1));
        assert_eq!(slab.get(k2), Some(&2));
        assert_eq!(slab.get(k3), Some(&3));
        assert_eq!(slab.len(), 3);
    }

    #[test]
    fn vacant_entry_interleaved_with_insert() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(16).unwrap();

        let k1 = slab.insert(1).unwrap();

        let entry = slab.vacant_entry().unwrap();
        let k2 = entry.insert(2);

        let k3 = slab.insert(3).unwrap();

        assert_eq!(slab.get(k1), Some(&1));
        assert_eq!(slab.get(k2), Some(&2));
        assert_eq!(slab.get(k3), Some(&3));
    }

    #[test]
    fn vacant_entry_drop_then_reuse() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(1).unwrap();

        // Create and abandon multiple entries
        for _ in 0..10 {
            let _entry = slab.vacant_entry().unwrap();
        }

        // Still have capacity
        assert_eq!(slab.len(), 0);

        // Can still insert
        let key = slab.insert(42).unwrap();
        assert_eq!(slab.get(key), Some(&42));
    }

    #[test]
    fn vacant_entry_debug_format() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(16).unwrap();

        let entry = slab.vacant_entry().unwrap();
        let debug_str = format!("{:?}", entry);
        assert!(debug_str.contains("VacantEntry"));
        assert!(debug_str.contains("key"));
    }

    #[test]
    fn vacant_entry_stress() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(64).unwrap();

        for i in 0..1000u64 {
            if i % 3 == 0 {
                // Use vacant_entry
                let entry = slab.vacant_entry().unwrap();
                let key = entry.key();
                entry.insert(i);
                assert_eq!(slab.get(key), Some(&i));
                slab.remove(key);
            } else {
                // Use regular insert
                let key = slab.insert(i).unwrap();
                assert_eq!(slab.get(key), Some(&i));
                slab.remove(key);
            }
        }
    }
}
