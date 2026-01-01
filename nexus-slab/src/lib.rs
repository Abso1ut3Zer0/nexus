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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn const_new() {
        const SLAB: Slab<u64> = Slab::new();
        assert!(!SLAB.is_allocated());
        assert_eq!(SLAB.capacity(), 0);
    }

    #[test]
    fn unallocated_behavior() {
        let mut slab: Slab<u64> = Slab::new();

        assert!(!slab.is_allocated());
        assert_eq!(slab.capacity(), 0);
        assert_eq!(slab.len(), 0);
        assert!(slab.is_empty());
        assert!(slab.is_full()); // No free slots
        assert_eq!(slab.memory_size(), 0);

        // Insert fails
        let result = slab.insert(42);
        assert!(result.is_err());

        // Get returns None for any key
        let fake_key = Key::new(0, 1);
        assert_eq!(slab.get(fake_key), None);
    }

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
    fn alloc_bytes_respects_budget() {
        let mut slab: Slab<u64> = Slab::new();
        let budget = 64 * 1024; // 64KB
        let bytes = slab.alloc_bytes(budget).unwrap();

        assert!(bytes <= budget);
        assert!(bytes > 0);
        assert!(slab.capacity() > 0);
    }

    #[test]
    fn double_alloc_fails() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(100).unwrap();

        let result = slab.alloc(100);
        assert!(result.is_err());

        let result = slab.alloc_bytes(4096);
        assert!(result.is_err());
    }

    #[test]
    fn alloc_zero_fails() {
        let mut slab: Slab<u64> = Slab::new();
        let result = slab.alloc(0);
        assert!(result.is_err());
    }

    #[test]
    fn alloc_bytes_too_small_fails() {
        let mut slab: Slab<u64> = Slab::new();
        let result = slab.alloc_bytes(100); // Less than page size
        assert!(result.is_err());
    }

    #[test]
    fn basic_insert_get_remove() {
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
    fn generation_prevents_stale_access() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(16).unwrap();

        let key1 = slab.insert(100).unwrap();
        slab.remove(key1);

        let key2 = slab.insert(200).unwrap();

        // Same index, different generation
        assert_eq!(key1.index(), key2.index());
        assert_ne!(key1.generation(), key2.generation());

        // Old key doesn't work
        assert_eq!(slab.get(key1), None);
        // New key works
        assert_eq!(slab.get(key2), Some(&200));
    }

    #[test]
    fn fill_and_drain() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(4).unwrap();
        let capacity = slab.capacity();

        // Fill to actual capacity
        let mut keys = Vec::new();
        for i in 0..capacity {
            keys.push(slab.insert(i as u64).unwrap());
        }

        assert!(slab.is_full());
        assert!(slab.insert(999).is_err());

        // Remove two keys
        let k1 = keys[1];
        let k3 = keys[3];
        slab.remove(k1);
        slab.remove(k3);

        // LIFO: k3's slot reused first
        let k4 = slab.insert(4).unwrap();
        assert_eq!(k4.index(), k3.index());

        // Then k1's slot
        let k5 = slab.insert(5).unwrap();
        assert_eq!(k5.index(), k1.index());
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
    fn contains() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(16).unwrap();

        let key = slab.insert(42).unwrap();
        assert!(slab.contains(key));

        slab.remove(key);
        assert!(!slab.contains(key));
    }

    #[test]
    fn drop_cleans_up() {
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
    fn full_returns_value() {
        let mut slab: Slab<String> = Slab::new();
        slab.alloc(1).unwrap();
        let capacity = slab.capacity();

        // Fill to capacity
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
    fn invalid_key_returns_none() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(16).unwrap();

        // Fabricated key
        let fake_key = Key::new(999, 42);
        assert_eq!(slab.get(fake_key), None);
        assert_eq!(slab.get_mut(fake_key), None);
        assert_eq!(slab.remove(fake_key), None);
        assert!(slab.entry(fake_key).is_none());
    }

    #[test]
    fn power_of_two_slot_size() {
        assert!(padded_slot_size::<u8>().is_power_of_two());
        assert!(padded_slot_size::<u64>().is_power_of_two());
        assert!(padded_slot_size::<[u8; 100]>().is_power_of_two());
        assert!(padded_slot_size::<[u8; 1000]>().is_power_of_two());
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
    fn many_generations() {
        let mut slab: Slab<u64> = Slab::new();
        slab.alloc(1).unwrap();

        let mut prev_gen = 0;
        for i in 0..1000 {
            let key = slab.insert(i).unwrap();
            assert!(key.generation() > prev_gen || prev_gen == 0);
            prev_gen = key.generation();
            slab.remove(key);
        }
    }

    #[test]
    fn debug_impl() {
        let slab: Slab<u64> = Slab::new();
        let debug_str = format!("{:?}", slab);
        assert!(debug_str.contains("Slab"));
        assert!(debug_str.contains("allocated"));
        assert!(debug_str.contains("len"));
        assert!(debug_str.contains("capacity"));
    }

    #[test]
    fn key_debug_impl() {
        let key = Key::new(42, 7);
        let debug_str = format!("{:?}", key);
        assert!(debug_str.contains("42"));
        assert!(debug_str.contains("7"));
    }

    #[test]
    fn mlock_without_alloc_fails() {
        let slab: Slab<u64> = Slab::new();
        let result = slab.mlock();
        assert!(result.is_err());
    }

    #[test]
    fn default_is_unallocated() {
        let slab: Slab<u64> = Slab::default();
        assert!(!slab.is_allocated());
    }
}
