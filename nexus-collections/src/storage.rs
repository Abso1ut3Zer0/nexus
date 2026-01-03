//! Storage trait for slab-like containers with stable indices.
//!
//! Storage provides insert/remove/get operations where indices remain
//! valid until explicitly removed. This enables node-based data structures
//! (lists, skip lists, heaps) to use indices instead of pointers.

use crate::Index;

use core::mem::MaybeUninit;
use core::ptr::NonNull;
use std::alloc::{Layout, alloc, dealloc, handle_alloc_error};
use std::marker::PhantomData;

/// Slab-like storage with stable indices.
///
/// # Requirements
///
/// Implementations must provide:
/// - **Stable indices**: an index remains valid until explicitly removed
/// - **O(1)** insert, remove, get operations
/// - **Slot reuse**: removed slots can be reused by future inserts
///
/// # Implementations
///
/// - `BoxedStorage<T>` - runtime capacity, heap allocated (in this crate)
/// - `slab::Slab<T>` - growable, heap allocated (feature `slab`)
/// - `nexus_slab::Slab<T>` - page-aligned, mlockable (feature `nexus-slab`)
pub trait Storage<T> {
    /// Index type for this storage.
    type Index: Index;

    /// Error type for failed insertions.
    ///
    /// - `Full<T>` for fixed-capacity storage
    /// - `Infallible` for growable storage
    type Error;

    /// Inserts a value, returning its stable index.
    fn try_insert(&mut self, value: T) -> Result<Self::Index, Self::Error>;

    /// Removes and returns the value at `index`, if present.
    fn remove(&mut self, index: Self::Index) -> Option<T>;

    /// Returns a reference to the value at `index`, if present.
    fn get(&self, index: Self::Index) -> Option<&T>;

    /// Returns a mutable reference to the value at `index`, if present.
    fn get_mut(&mut self, index: Self::Index) -> Option<&mut T>;

    /// Returns a reference without bounds checking.
    ///
    /// # Safety
    ///
    /// `index` must be valid and occupied.
    unsafe fn get_unchecked(&self, index: Self::Index) -> &T;

    /// Returns a mutable reference without bounds checking.
    ///
    /// # Safety
    ///
    /// `index` must be valid and occupied.
    unsafe fn get_unchecked_mut(&mut self, index: Self::Index) -> &mut T;

    /// Removes an element without bounds checking.
    ///
    /// # Safety
    ///
    /// The index must be valid and occupied.
    unsafe fn remove_unchecked(&mut self, index: Self::Index) -> T;
}

/// Error returned when fixed-capacity storage is full.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Full<T>(pub T);

impl<T> Full<T> {
    /// Returns the value that could not be inserted.
    pub fn into_inner(self) -> T {
        self.0
    }
}

impl<T> core::fmt::Display for Full<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "storage is full")
    }
}

impl<T: core::fmt::Debug> std::error::Error for Full<T> {}

// =============================================================================
// BoxedStorage - runtime capacity, single allocation, bitmap occupancy
// =============================================================================

/// Fixed-capacity storage with runtime-determined size.
///
/// Uses a single heap allocation containing:
/// - Entry array (`MaybeUninit<T>`)
/// - Occupancy bitmap (`u64` words)
/// - Free stack (indices)
///
/// Capacity is rounded up to the next power of 2 for bitmap efficiency.
///
/// # Example
///
/// ```
/// use nexus_collections::{BoxedStorage, Storage};
///
/// let mut storage: BoxedStorage<u64> = BoxedStorage::with_capacity(1000);
/// assert!(storage.capacity() >= 1000); // Rounded to 1024
///
/// let idx = storage.try_insert(42).unwrap();
/// assert_eq!(storage.get(idx), Some(&42));
/// ```
pub struct BoxedStorage<T, Idx: Index = u32> {
    /// Single allocation containing entries, bitmap, and free stack.
    ptr: NonNull<u8>,
    /// Capacity (always power of 2).
    capacity: usize,
    /// Number of free slots.
    free_len: usize,
    /// Cached layout for deallocation.
    layout: Layout,
    /// Offset to bitmap from ptr.
    bitmap_offset: usize,
    /// Offset to free stack from ptr.
    free_stack_offset: usize,
    _marker: PhantomData<(T, Idx)>,
}

impl<T, Idx: Index> BoxedStorage<T, Idx> {
    /// Creates storage with at least `min_capacity` slots.
    ///
    /// Actual capacity is rounded up to the next power of 2.
    ///
    /// # Panics
    ///
    /// Panics if `min_capacity` is 0 or exceeds the index type's maximum.
    pub fn with_capacity(min_capacity: usize) -> Self {
        assert!(min_capacity > 0, "capacity must be > 0");

        // Round up to power of 2 for bitmap efficiency
        let capacity = min_capacity.next_power_of_two();

        assert!(
            capacity <= Idx::NONE.as_usize(),
            "capacity exceeds index type maximum"
        );

        // Calculate layout
        // Layout: [entries][padding][bitmap][padding][free_stack]
        let entries_layout = Layout::array::<MaybeUninit<T>>(capacity).unwrap();
        let bitmap_words = bitmap_words(capacity);
        let bitmap_layout = Layout::array::<u64>(bitmap_words).unwrap();
        let free_stack_layout = Layout::array::<Idx>(capacity).unwrap();

        let (layout, bitmap_offset) = entries_layout.extend(bitmap_layout).unwrap();
        let (layout, free_stack_offset) = layout.extend(free_stack_layout).unwrap();
        let layout = layout.pad_to_align();

        // Allocate
        let ptr = unsafe { alloc(layout) };
        if ptr.is_null() {
            handle_alloc_error(layout);
        }
        let ptr = unsafe { NonNull::new_unchecked(ptr) };

        // Initialize bitmap to all zeros (all slots free, but we track via free_stack)
        unsafe {
            let bitmap_ptr = ptr.as_ptr().add(bitmap_offset) as *mut u64;
            core::ptr::write_bytes(bitmap_ptr, 0, bitmap_words);
        }

        // Initialize free stack
        unsafe {
            let free_stack_ptr = ptr.as_ptr().add(free_stack_offset) as *mut Idx;
            for i in 0..capacity {
                free_stack_ptr.add(i).write(Idx::from_usize(i));
            }
        }

        Self {
            ptr,
            capacity,
            free_len: capacity,
            layout,
            bitmap_offset,
            free_stack_offset,
            _marker: PhantomData,
        }
    }

    /// Returns the capacity.
    #[inline]
    pub const fn capacity(&self) -> usize {
        self.capacity
    }

    /// Returns the number of occupied slots.
    #[inline]
    pub const fn len(&self) -> usize {
        self.capacity - self.free_len
    }

    /// Returns `true` if no slots are occupied.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.free_len == self.capacity
    }

    /// Returns `true` if all slots are occupied.
    #[inline]
    pub const fn is_full(&self) -> bool {
        self.free_len == 0
    }

    /// Removes all elements from storage.
    ///
    /// This drops all stored values and makes all slots available for reuse.
    ///
    /// # Warning
    ///
    /// If any data structures (List, Heap, etc.) still reference indices in
    /// this storage, they will have dangling references. Only call this when
    /// you know nothing else references the storage, or after clearing those
    /// data structures first.
    ///
    /// For owned wrappers like [`OwnedList`] and [`OwnedHeap`], this is handled
    /// automatically.
    pub fn clear(&mut self) {
        // Drop all occupied values
        for i in 0..self.capacity {
            if self.is_occupied(i) {
                // Safety: slot is occupied
                unsafe {
                    let ptr = self.entries_ptr().add(i);
                    std::ptr::drop_in_place((*ptr).as_mut_ptr());
                }
            }
        }

        // Reset bitmap to all zeros (all vacant)
        unsafe {
            std::ptr::write_bytes(self.bitmap_ptr(), 0, bitmap_words(self.capacity));
        }

        // Rebuild free stack
        let free_stack = self.free_stack_ptr();
        for i in 0..self.capacity {
            unsafe {
                *free_stack.add(i) = Idx::from_usize(i);
            }
        }
        self.free_len = self.capacity;
    }

    #[inline]
    fn entries_ptr(&self) -> *mut MaybeUninit<T> {
        self.ptr.as_ptr() as *mut MaybeUninit<T>
    }

    #[inline]
    fn bitmap_ptr(&self) -> *mut u64 {
        unsafe { self.ptr.as_ptr().add(self.bitmap_offset) as *mut u64 }
    }

    #[inline]
    fn free_stack_ptr(&self) -> *mut Idx {
        unsafe { self.ptr.as_ptr().add(self.free_stack_offset) as *mut Idx }
    }

    #[inline]
    fn is_occupied(&self, idx: usize) -> bool {
        let word = idx / 64;
        let bit = idx % 64;
        unsafe {
            let bitmap = self.bitmap_ptr();
            (*bitmap.add(word) & (1 << bit)) != 0
        }
    }

    #[inline]
    fn set_occupied(&mut self, idx: usize) {
        let word = idx / 64;
        let bit = idx % 64;
        unsafe {
            let bitmap = self.bitmap_ptr();
            *bitmap.add(word) |= 1 << bit;
        }
    }

    #[inline]
    fn set_vacant(&mut self, idx: usize) {
        let word = idx / 64;
        let bit = idx % 64;
        unsafe {
            let bitmap = self.bitmap_ptr();
            *bitmap.add(word) &= !(1 << bit);
        }
    }
}

impl<T, Idx: Index> Storage<T> for BoxedStorage<T, Idx> {
    type Index = Idx;
    type Error = Full<T>;

    #[inline]
    fn try_insert(&mut self, value: T) -> Result<Self::Index, Self::Error> {
        if self.free_len == 0 {
            return Err(Full(value));
        }

        self.free_len -= 1;
        let idx = unsafe { *self.free_stack_ptr().add(self.free_len) };
        let i = idx.as_usize();

        unsafe {
            self.entries_ptr().add(i).write(MaybeUninit::new(value));
        }
        self.set_occupied(i);

        Ok(idx)
    }

    #[inline]
    fn remove(&mut self, index: Self::Index) -> Option<T> {
        let i = index.as_usize();
        if i >= self.capacity || !self.is_occupied(i) {
            return None;
        }

        self.set_vacant(i);
        let value = unsafe { self.entries_ptr().add(i).read().assume_init() };

        unsafe {
            self.free_stack_ptr().add(self.free_len).write(index);
        }
        self.free_len += 1;

        Some(value)
    }

    #[inline]
    fn get(&self, index: Self::Index) -> Option<&T> {
        let i = index.as_usize();
        if i >= self.capacity || !self.is_occupied(i) {
            return None;
        }

        Some(unsafe { (*self.entries_ptr().add(i)).assume_init_ref() })
    }

    #[inline]
    fn get_mut(&mut self, index: Self::Index) -> Option<&mut T> {
        let i = index.as_usize();
        if i >= self.capacity || !self.is_occupied(i) {
            return None;
        }

        Some(unsafe { (*self.entries_ptr().add(i)).assume_init_mut() })
    }

    #[inline]
    unsafe fn get_unchecked(&self, index: Self::Index) -> &T {
        unsafe { (*self.entries_ptr().add(index.as_usize())).assume_init_ref() }
    }

    #[inline]
    unsafe fn get_unchecked_mut(&mut self, index: Self::Index) -> &mut T {
        unsafe { (*self.entries_ptr().add(index.as_usize())).assume_init_mut() }
    }

    #[inline]
    unsafe fn remove_unchecked(&mut self, index: Self::Index) -> T {
        let i = index.as_usize();

        self.set_vacant(i);
        let value = unsafe { self.entries_ptr().add(i).read().assume_init() };

        unsafe {
            self.free_stack_ptr().add(self.free_len).write(index);
        }
        self.free_len += 1;

        value
    }
}

impl<T, Idx: Index> Drop for BoxedStorage<T, Idx> {
    fn drop(&mut self) {
        // Drop all occupied entries
        for i in 0..self.capacity {
            if self.is_occupied(i) {
                unsafe {
                    self.entries_ptr().add(i).read().assume_init_drop();
                }
            }
        }

        // Deallocate
        unsafe {
            dealloc(self.ptr.as_ptr(), self.layout);
        }
    }
}

// Safety: BoxedStorage owns its data, safe to send if T is Send
unsafe impl<T: Send, Idx: Index> Send for BoxedStorage<T, Idx> {}

// =============================================================================
// slab::Slab implementation
// =============================================================================

#[cfg(feature = "slab")]
impl<T> Storage<T> for slab::Slab<T> {
    type Index = usize;
    type Error = core::convert::Infallible;

    #[inline]
    fn try_insert(&mut self, value: T) -> Result<Self::Index, Self::Error> {
        Ok(self.insert(value))
    }

    #[inline]
    fn remove(&mut self, index: Self::Index) -> Option<T> {
        self.try_remove(index)
    }

    #[inline]
    fn get(&self, index: Self::Index) -> Option<&T> {
        self.get(index)
    }

    #[inline]
    fn get_mut(&mut self, index: Self::Index) -> Option<&mut T> {
        self.get_mut(index)
    }

    #[inline]
    unsafe fn get_unchecked(&self, index: Self::Index) -> &T {
        unsafe { self.get(index).unwrap_unchecked() }
    }

    #[inline]
    unsafe fn get_unchecked_mut(&mut self, index: Self::Index) -> &mut T {
        unsafe { self.get_mut(index).unwrap_unchecked() }
    }

    #[inline]
    unsafe fn remove_unchecked(&mut self, index: Self::Index) -> T {
        // slab
        self.remove(index)
    }
}

// =============================================================================
// nexus_slab::Slab implementation
// =============================================================================

#[cfg(feature = "nexus-slab")]
impl<T> Storage<T> for nexus_slab::Slab<T> {
    type Index = nexus_slab::Key;
    type Error = nexus_slab::Full<T>;

    #[inline]
    fn try_insert(&mut self, value: T) -> Result<Self::Index, Self::Error> {
        self.insert(value)
    }

    #[inline]
    fn remove(&mut self, index: Self::Index) -> Option<T> {
        self.remove(index)
    }

    #[inline]
    fn get(&self, index: Self::Index) -> Option<&T> {
        self.get(index)
    }

    #[inline]
    fn get_mut(&mut self, index: Self::Index) -> Option<&mut T> {
        self.get_mut(index)
    }

    #[inline]
    unsafe fn get_unchecked(&self, index: Self::Index) -> &T {
        unsafe { self.get_unchecked(index) }
    }

    #[inline]
    unsafe fn get_unchecked_mut(&mut self, index: Self::Index) -> &mut T {
        unsafe { self.get_unchecked_mut(index) }
    }

    #[inline]
    unsafe fn remove_unchecked(&mut self, index: Self::Index) -> T {
        unsafe { self.remove_unchecked(index) }
    }
}

#[inline]
const fn bitmap_words(capacity: usize) -> usize {
    (capacity + 63) / 64
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_is_empty() {
        let storage: BoxedStorage<u64> = BoxedStorage::with_capacity(16);
        assert!(storage.is_empty());
        assert!(!storage.is_full());
        assert_eq!(storage.len(), 0);
        assert_eq!(storage.capacity(), 16);
    }

    #[test]
    fn capacity_rounds_to_power_of_two() {
        let storage: BoxedStorage<u64> = BoxedStorage::with_capacity(100);
        assert_eq!(storage.capacity(), 128);

        let storage: BoxedStorage<u64> = BoxedStorage::with_capacity(1000);
        assert_eq!(storage.capacity(), 1024);
    }

    #[test]
    fn insert_get_remove() {
        let mut storage: BoxedStorage<u64> = BoxedStorage::with_capacity(16);

        let idx = storage.try_insert(42).unwrap();
        assert_eq!(storage.len(), 1);
        assert_eq!(storage.get(idx), Some(&42));

        let removed = storage.remove(idx);
        assert_eq!(removed, Some(42));
        assert_eq!(storage.get(idx), None);
        assert_eq!(storage.len(), 0);
    }

    #[test]
    fn get_mut() {
        let mut storage: BoxedStorage<u64> = BoxedStorage::with_capacity(16);

        let idx = storage.try_insert(10).unwrap();
        *storage.get_mut(idx).unwrap() = 20;

        assert_eq!(storage.get(idx), Some(&20));
    }

    #[test]
    fn fill_to_capacity() {
        let mut storage: BoxedStorage<u64> = BoxedStorage::with_capacity(4);

        let k0 = storage.try_insert(0).unwrap();
        let k1 = storage.try_insert(1).unwrap();
        let k2 = storage.try_insert(2).unwrap();
        let k3 = storage.try_insert(3).unwrap();

        assert!(storage.is_full());

        let err = storage.try_insert(4);
        assert!(err.is_err());
        assert_eq!(err.unwrap_err().into_inner(), 4);

        assert_eq!(storage.get(k0), Some(&0));
        assert_eq!(storage.get(k1), Some(&1));
        assert_eq!(storage.get(k2), Some(&2));
        assert_eq!(storage.get(k3), Some(&3));
    }

    #[test]
    fn slot_reuse() {
        let mut storage: BoxedStorage<u64> = BoxedStorage::with_capacity(4);

        let k0 = storage.try_insert(0).unwrap();
        let _k1 = storage.try_insert(1).unwrap();

        storage.remove(k0);

        // Next insert reuses k0's slot (LIFO)
        let k2 = storage.try_insert(2).unwrap();
        assert_eq!(k2, k0);
    }

    #[test]
    fn remove_nonexistent() {
        let mut storage: BoxedStorage<u64> = BoxedStorage::with_capacity(16);

        let idx = storage.try_insert(42).unwrap();
        storage.remove(idx);

        // Double remove returns None
        assert_eq!(storage.remove(idx), None);
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
            let mut storage: BoxedStorage<DropCounter> = BoxedStorage::with_capacity(8);
            storage.try_insert(DropCounter).unwrap();
            storage.try_insert(DropCounter).unwrap();
            storage.try_insert(DropCounter).unwrap();
        }

        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), 3);
    }

    #[test]
    fn large_capacity() {
        let mut storage: BoxedStorage<u64> = BoxedStorage::with_capacity(4096);
        assert_eq!(storage.capacity(), 4096);

        // Fill it
        let mut keys = Vec::with_capacity(4096);
        for i in 0..4096 {
            keys.push(storage.try_insert(i as u64).unwrap());
        }
        assert!(storage.is_full());

        // Verify all values
        for (i, key) in keys.iter().enumerate() {
            assert_eq!(storage.get(*key), Some(&(i as u64)));
        }
    }

    #[test]
    fn u16_index() {
        let mut storage: BoxedStorage<u64, u16> = BoxedStorage::with_capacity(100);

        let idx = storage.try_insert(42).unwrap();
        assert_eq!(storage.get(idx), Some(&42));
    }

    #[cfg(feature = "slab")]
    mod slab_tests {
        use super::*;

        #[test]
        fn insert_get_remove() {
            let mut storage = slab::Slab::new();

            let idx = storage.try_insert(42).unwrap();
            assert_eq!(storage.get(idx), Some(&42));

            let removed = storage.remove(idx);
            assert_eq!(removed, 42);
            assert_eq!(storage.get(idx), None);
        }

        #[test]
        fn slot_reuse() {
            let mut storage = slab::Slab::new();

            let idx1 = storage.try_insert(1).unwrap();
            storage.remove(idx1);

            let idx2 = storage.try_insert(2).unwrap();
            assert_eq!(idx1, idx2); // Slot reused
        }
    }

    #[cfg(feature = "nexus-slab")]
    mod nexus_slab_tests {
        use super::*;

        #[test]
        fn insert_get_remove() {
            let mut storage: nexus_slab::Slab<u64> = nexus_slab::Slab::with_capacity(16).unwrap();

            let idx = storage.try_insert(42).unwrap();
            assert_eq!(storage.get(idx), Some(&42));

            let removed = storage.remove(idx);
            assert_eq!(removed, Some(42));
            assert_eq!(storage.get(idx), None);
        }
    }

    #[test]
    #[ignore]
    fn bench_boxed_storage() {
        use std::time::Instant;

        const CAPACITY: usize = 4096;
        const ITERATIONS: usize = 100_000;

        let mut storage: BoxedStorage<u64> = BoxedStorage::with_capacity(CAPACITY);

        // Warmup
        for i in 0..CAPACITY {
            storage.try_insert(i as u64).unwrap();
        }
        for i in 0..CAPACITY {
            storage.remove(u32::from_usize(i));
        }

        // Collect timings
        let mut insert_ns = Vec::with_capacity(ITERATIONS);
        let mut get_ns = Vec::with_capacity(ITERATIONS);
        let mut remove_ns = Vec::with_capacity(ITERATIONS);

        for i in 0..ITERATIONS {
            // Insert
            let start = Instant::now();
            let idx = storage.try_insert(i as u64).unwrap();
            insert_ns.push(start.elapsed().as_nanos() as u64);

            // Get
            let start = Instant::now();
            let _ = std::hint::black_box(storage.get(idx));
            get_ns.push(start.elapsed().as_nanos() as u64);

            // Remove
            let start = Instant::now();
            let _ = std::hint::black_box(storage.remove(idx));
            remove_ns.push(start.elapsed().as_nanos() as u64);
        }

        // Sort for percentiles
        insert_ns.sort_unstable();
        get_ns.sort_unstable();
        remove_ns.sort_unstable();

        fn percentile(sorted: &[u64], p: f64) -> u64 {
            let idx = ((p / 100.0) * sorted.len() as f64) as usize;
            sorted[idx.min(sorted.len() - 1)]
        }

        fn print_stats(name: &str, sorted: &[u64]) {
            println!(
                "{:8} | p50: {:4} ns | p90: {:4} ns | p99: {:4} ns | p999: {:5} ns",
                name,
                percentile(sorted, 50.0),
                percentile(sorted, 90.0),
                percentile(sorted, 99.0),
                percentile(sorted, 99.9),
            );
        }

        println!(
            "\nBoxedStorage<u64> ({} iterations, capacity {})",
            ITERATIONS, CAPACITY
        );
        println!("---------------------------------------------------------");
        print_stats("insert", &insert_ns);
        print_stats("get", &get_ns);
        print_stats("remove", &remove_ns);
        println!();
    }

    #[cfg(all(target_arch = "x86_64", target_os = "linux"))]
    #[test]
    #[ignore]
    fn bench_boxed_storage_tsc() {
        const CAPACITY: usize = 4096;
        const ITERATIONS: usize = 100_000;

        #[inline]
        fn rdtsc() -> u64 {
            unsafe {
                core::arch::x86_64::_mm_lfence();
                core::arch::x86_64::_rdtsc()
            }
        }

        let mut storage: BoxedStorage<u64> = BoxedStorage::with_capacity(CAPACITY);

        // Warmup
        for i in 0..CAPACITY {
            storage.try_insert(i as u64).unwrap();
        }
        for i in 0..CAPACITY {
            storage.remove(u32::from_usize(i));
        }

        // Collect timings
        let mut insert_cycles = Vec::with_capacity(ITERATIONS);
        let mut get_cycles = Vec::with_capacity(ITERATIONS);
        let mut remove_cycles = Vec::with_capacity(ITERATIONS);

        for i in 0..ITERATIONS {
            // Insert
            let start = rdtsc();
            let idx = storage.try_insert(i as u64).unwrap();
            let end = rdtsc();
            insert_cycles.push(end - start);

            // Get
            let start = rdtsc();
            let _ = std::hint::black_box(storage.get(idx));
            let end = rdtsc();
            get_cycles.push(end - start);

            // Remove
            let start = rdtsc();
            let _ = std::hint::black_box(storage.remove(idx));
            let end = rdtsc();
            remove_cycles.push(end - start);
        }

        // Sort for percentiles
        insert_cycles.sort_unstable();
        get_cycles.sort_unstable();
        remove_cycles.sort_unstable();

        fn percentile(sorted: &[u64], p: f64) -> u64 {
            let idx = ((p / 100.0) * sorted.len() as f64) as usize;
            sorted[idx.min(sorted.len() - 1)]
        }

        fn print_stats(name: &str, sorted: &[u64]) {
            println!(
                "{:8} | p50: {:5} cycles | p90: {:5} cycles | p99: {:5} cycles | p999: {:6} cycles",
                name,
                percentile(sorted, 50.0),
                percentile(sorted, 90.0),
                percentile(sorted, 99.0),
                percentile(sorted, 99.9),
            );
        }

        println!(
            "\nBoxedStorage<u64> ({} iterations, capacity {})",
            ITERATIONS, CAPACITY
        );
        println!("------------------------------------------------------------------------");
        print_stats("insert", &insert_cycles);
        print_stats("get", &get_cycles);
        print_stats("remove", &remove_cycles);
        println!();
    }
}
