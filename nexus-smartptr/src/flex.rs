//! Inline storage with heap fallback.
//!
//! [`Flex<T, B>`] tries to store a `?Sized` value inline. If the concrete
//! type is too large or over-aligned, it falls back to a heap allocation.
//! Construction never panics (unlike [`Flat`](crate::Flat)).
//!
//! `B` is a buffer marker type — `size_of::<Flex<dyn Trait, B32>>() == 32`.
//!
//! The heap pointer doubles as the inline/heap discriminant:
//! null means inline, non-null is the heap address.

use core::marker::PhantomData;
use core::mem::{self, MaybeUninit};
use core::ops::{Deref, DerefMut};
use core::ptr;

use alloc::alloc::{Layout, alloc, dealloc, handle_alloc_error};

use crate::Buffer;
use crate::meta::{self, Metadata};

extern crate alloc;

/// Size of the metadata word.
const META_SIZE: usize = mem::size_of::<Metadata>();

/// Size of the heap pointer / discriminant slot.
const PTR_SIZE: usize = mem::size_of::<*mut u8>();

/// Compile-time check that the buffer can hold the overhead fields.
///
/// For ?Sized T: B::CAPACITY >= 2 * pointer size (metadata + heap pointer).
/// For Sized T: B::CAPACITY >= pointer size (heap pointer only).
const fn assert_flex_buffer<T: ?Sized, B: Buffer>() {
    if meta::is_fat_ptr::<T>() {
        assert!(
            B::CAPACITY >= META_SIZE + PTR_SIZE,
            "Flex: buffer too small for ?Sized overhead (metadata + heap pointer)"
        );
    } else {
        assert!(
            B::CAPACITY >= PTR_SIZE,
            "Flex: buffer too small for Sized overhead (heap pointer)"
        );
    }
}

/// Inline storage with heap fallback for `?Sized` types.
///
/// Stores a trait object (or slice) inline when it fits, otherwise
/// heap-allocates. Use [`is_inline`](Flex::is_inline) to query which
/// path was taken.
///
/// The total struct size equals `size_of::<B>()`.
///
/// # Layout
///
/// The heap pointer slot doubles as the inline/heap discriminant
/// (null = inline, non-null = heap address).
///
/// - **?Sized T**: `[metadata(ptr)][heap_ptr(ptr)][value(B − 2*ptr)]`
/// - **Sized T**: `[heap_ptr(ptr)][value(B − ptr)]`
///
/// Use the [`flex!`](crate::flex!) macro for `?Sized` construction,
/// or [`Flex::new`] for `Sized` types.
///
/// # Compile-time safety
///
/// Buffers too small for the overhead produce a compile error:
///
/// ```compile_fail
/// nexus_smartptr::define_buffer!(B8, 8);
/// trait Foo { fn foo(&self); }
/// struct Bar;
/// impl Foo for Bar { fn foo(&self) {} }
/// // B8 can't fit ?Sized overhead (metadata + heap pointer = 16 bytes).
/// let _: nexus_smartptr::Flex<dyn Foo, B8> = nexus_smartptr::flex!(Bar);
/// ```
#[repr(C)]
pub struct Flex<T: ?Sized, B: Buffer> {
    inner: MaybeUninit<B>,
    _marker: PhantomData<T>,
}

impl<T: ?Sized, B: Buffer> Flex<T, B> {
    /// Byte offset where the heap-pointer / discriminant lives.
    const PTR_OFFSET: usize = if meta::is_fat_ptr::<T>() {
        META_SIZE
    } else {
        0
    };

    /// Byte offset where the inline value starts.
    const VALUE_OFFSET: usize = Self::PTR_OFFSET + PTR_SIZE;

    /// Returns the usable inline value capacity in bytes.
    ///
    /// For `Sized` types: `B::CAPACITY - 8` (heap pointer slot).
    /// For `?Sized` types: `B::CAPACITY - 16` (metadata + heap pointer).
    pub const fn capacity() -> usize {
        B::CAPACITY.saturating_sub(Self::VALUE_OFFSET)
    }

    /// Returns `true` if the value is stored inline (no heap allocation).
    pub fn is_inline(&self) -> bool {
        self.heap_ptr().is_null()
    }

    /// Reads the heap-pointer / discriminant slot.
    #[inline(always)]
    fn heap_ptr(&self) -> *mut u8 {
        let base = self.inner.as_ptr().cast::<u8>();
        // SAFETY: PTR_OFFSET + PTR_SIZE <= B::CAPACITY (enforced by const assert).
        unsafe { base.add(Self::PTR_OFFSET).cast::<*mut u8>().read() }
    }

    /// Constructs a `Flex` from a concrete value and a (possibly fat) pointer.
    ///
    /// This is an implementation detail of the [`flex!`](crate::flex!) macro.
    /// Do not call directly.
    ///
    /// # Safety
    ///
    /// `ptr` must be a pointer whose metadata (vtable/length) corresponds to `V`.
    /// The [`flex!`](crate::flex!) macro guarantees this via unsizing coercion.
    #[doc(hidden)]
    pub unsafe fn new_raw<V>(val: V, ptr: *const T) -> Self {
        // Compile-time: buffer must fit the overhead fields.
        const { assert_flex_buffer::<T, B>() }

        let size = mem::size_of::<V>();
        let align = mem::align_of::<V>();
        let metadata = meta::extract_metadata(ptr);

        if size <= Self::capacity() && align <= mem::align_of::<usize>() {
            Self::new_inline(val, metadata)
        } else {
            Self::new_heap(val, metadata)
        }
    }

    /// Inline construction path.
    fn new_inline<V>(val: V, metadata: Metadata) -> Self {
        let mut this: Self = Flex {
            inner: MaybeUninit::uninit(),
            _marker: PhantomData,
        };
        let base = this.inner.as_mut_ptr().cast::<u8>();

        // SAFETY: buffer has capacity for overhead + value.
        // align(8) on buffer satisfies usize alignment.
        unsafe {
            if meta::is_fat_ptr::<T>() {
                // Write metadata at offset 0.
                base.cast::<*const ()>().write(metadata.0);
            }
            // Write null heap_ptr (= inline discriminant).
            base.add(Self::PTR_OFFSET)
                .cast::<*mut u8>()
                .write(ptr::null_mut());
            // Write value after the overhead.
            base.add(Self::VALUE_OFFSET).cast::<V>().write(val);
        }

        this
    }

    /// Heap construction path.
    fn new_heap<V>(val: V, metadata: Metadata) -> Self {
        let layout = Layout::new::<V>();
        let heap = if layout.size() == 0 {
            // ZST: dangling pointer, no allocation.
            core::ptr::NonNull::<V>::dangling().as_ptr().cast::<u8>()
        } else {
            // SAFETY: layout has non-zero size.
            let p = unsafe { alloc(layout) };
            if p.is_null() {
                handle_alloc_error(layout);
            }
            // SAFETY: p is valid, aligned for V, with sufficient size.
            unsafe {
                p.cast::<V>().write(val);
            }
            p
        };

        let mut this: Self = Flex {
            inner: MaybeUninit::uninit(),
            _marker: PhantomData,
        };
        let base = this.inner.as_mut_ptr().cast::<u8>();

        // SAFETY: writing metadata + heap pointer within buffer bounds.
        unsafe {
            if meta::is_fat_ptr::<T>() {
                base.cast::<*const ()>().write(metadata.0);
            }
            base.add(Self::PTR_OFFSET).cast::<*mut u8>().write(heap);
        }

        this
    }

    /// Returns the data pointer (to inline value or heap allocation).
    #[inline(always)]
    fn data_ptr(&self) -> *const () {
        let hp = self.heap_ptr();
        if hp.is_null() {
            // Inline: value lives after the overhead.
            let base = self.inner.as_ptr().cast::<u8>();
            // SAFETY: VALUE_OFFSET is within buffer bounds (enforced by const assert).
            unsafe { base.add(Self::VALUE_OFFSET) }.cast::<()>()
        } else {
            hp.cast::<()>().cast_const()
        }
    }

    /// Returns the mutable data pointer.
    #[inline(always)]
    fn data_ptr_mut(&mut self) -> *mut () {
        let hp = self.heap_ptr();
        if hp.is_null() {
            let base = self.inner.as_mut_ptr().cast::<u8>();
            // SAFETY: VALUE_OFFSET is within buffer bounds (enforced by const assert).
            unsafe { base.add(Self::VALUE_OFFSET) }.cast::<()>()
        } else {
            hp.cast::<()>()
        }
    }

    /// Returns a (possibly fat) pointer to the stored value.
    #[inline(always)]
    fn as_ptr(&self) -> *const T {
        let data = self.data_ptr();
        if meta::is_fat_ptr::<T>() {
            let base = self.inner.as_ptr().cast::<u8>();
            // SAFETY: metadata at offset 0, preserved from construction.
            let metadata = Metadata(unsafe { base.cast::<*const ()>().read() });
            // SAFETY: data and metadata come from a valid Flex; metadata matches the concrete type.
            unsafe { meta::make_ptr(data, metadata) }
        } else {
            // SAFETY: Sized T; data is a valid data pointer.
            unsafe { meta::make_ptr(data, Metadata::NULL) }
        }
    }

    /// Returns a mutable (possibly fat) pointer to the stored value.
    #[inline(always)]
    fn as_mut_ptr(&mut self) -> *mut T {
        let data = self.data_ptr_mut();
        if meta::is_fat_ptr::<T>() {
            let base = self.inner.as_ptr().cast::<u8>();
            // SAFETY: metadata written at offset 0 during construction.
            let metadata = Metadata(unsafe { base.cast::<*const ()>().read() });
            // SAFETY: data and metadata come from a valid Flex; metadata matches the concrete type.
            unsafe { meta::make_ptr_mut(data, metadata) }
        } else {
            // SAFETY: Sized T; data is a valid data pointer.
            unsafe { meta::make_ptr_mut(data, Metadata::NULL) }
        }
    }
}

// -- Methods only for Sized T --
impl<T, B: Buffer> Flex<T, B> {
    /// Constructs a `Flex` from a `Sized` value.
    ///
    /// Stores inline if the value fits, otherwise heap-allocates.
    ///
    /// # Examples
    ///
    /// ```
    /// use nexus_smartptr::{Flex, B32};
    ///
    /// let f: Flex<u64, B32> = Flex::new(42);
    /// assert!(f.is_inline());
    /// assert_eq!(*f, 42);
    /// ```
    pub fn new(val: T) -> Self {
        // Compile-time: buffer must fit the overhead fields.
        const { assert_flex_buffer::<T, B>() }

        let size = mem::size_of::<T>();
        let align = mem::align_of::<T>();
        if size <= Self::capacity() && align <= mem::align_of::<usize>() {
            Self::new_inline(val, Metadata::NULL)
        } else {
            Self::new_heap(val, Metadata::NULL)
        }
    }
}

impl<T: ?Sized, B: Buffer> Deref for Flex<T, B> {
    type Target = T;

    #[inline(always)]
    fn deref(&self) -> &T {
        // SAFETY: the stored value is valid and initialized.
        unsafe { &*self.as_ptr() }
    }
}

impl<T: ?Sized, B: Buffer> DerefMut for Flex<T, B> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: same as Deref, plus exclusive access via &mut self.
        unsafe { &mut *self.as_mut_ptr() }
    }
}

impl<T: ?Sized, B: Buffer> Drop for Flex<T, B> {
    fn drop(&mut self) {
        let hp = self.heap_ptr();
        if hp.is_null() {
            // Inline: drop in place.
            // SAFETY: as_mut_ptr returns a valid pointer to the stored value.
            unsafe {
                ptr::drop_in_place(self.as_mut_ptr());
            }
        } else {
            // Heap: get layout BEFORE drop_in_place.
            let fat = self.as_mut_ptr();
            // SAFETY: value is still alive, fat pointer is valid.
            let layout = Layout::for_value(unsafe { &*fat });
            // SAFETY: fat points to the heap-allocated value.
            unsafe {
                ptr::drop_in_place(fat);
            }
            if layout.size() > 0 {
                // SAFETY: heap was allocated with this layout.
                // Size > 0 means this isn't a dangling ZST pointer.
                unsafe {
                    dealloc(hp, layout);
                }
            }
        }
    }
}

// SAFETY: Flex<T, B> logically owns a T. The raw pointer in the heap slot
// is an owned allocation — not shared. Send/Sync depend only on T.
// MaybeUninit<B> is raw storage, not a meaningful Send/Sync participant.
#[allow(clippy::non_send_fields_in_send_ty)]
unsafe impl<T: ?Sized + Send, B: Buffer> Send for Flex<T, B> {}
// SAFETY: same as Send above; Sync depends only on T.
unsafe impl<T: ?Sized + Sync, B: Buffer> Sync for Flex<T, B> {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{B16, B32, B64};
    use core::fmt::Display;
    use std::sync::atomic::{AtomicUsize, Ordering};

    trait Greet {
        fn greet(&self) -> &str;
    }

    struct Hello;
    impl Greet for Hello {
        fn greet(&self) -> &'static str {
            "hello"
        }
    }

    #[allow(dead_code)]
    struct World(u64);
    impl Greet for World {
        fn greet(&self) -> &'static str {
            "world"
        }
    }

    fn make_flex_greet<V: Greet + 'static, B: Buffer>(val: V) -> Flex<dyn Greet, B> {
        let ptr: *const dyn Greet = &val as &dyn Greet;
        // SAFETY: ptr coerced from val above; metadata matches V.
        unsafe { Flex::new_raw(val, ptr) }
    }

    #[test]
    fn total_size_matches_buffer() {
        assert_eq!(mem::size_of::<Flex<dyn Greet, B16>>(), 16);
        assert_eq!(mem::size_of::<Flex<dyn Greet, B32>>(), 32);
        assert_eq!(mem::size_of::<Flex<dyn Greet, B64>>(), 64);
        assert_eq!(mem::size_of::<Flex<u64, B32>>(), 32);
    }

    #[test]
    fn capacity_unsized() {
        assert_eq!(Flex::<dyn Greet, B16>::capacity(), 0);
        assert_eq!(Flex::<dyn Greet, B32>::capacity(), 16);
        assert_eq!(Flex::<dyn Greet, B64>::capacity(), 48);
    }

    #[test]
    fn capacity_sized() {
        assert_eq!(Flex::<u64, B16>::capacity(), 8);
        assert_eq!(Flex::<u64, B32>::capacity(), 24);
    }

    #[test]
    fn sized_new_inline() {
        let f: Flex<u64, B32> = Flex::new(42);
        assert!(f.is_inline());
        assert_eq!(*f, 42);
    }

    #[test]
    fn sized_new_heap() {
        // [u64; 4] = 32 bytes, B16 Sized capacity = 8 bytes
        let f: Flex<[u64; 4], B16> = Flex::new([1, 2, 3, 4]);
        assert!(!f.is_inline());
        assert_eq!(*f, [1, 2, 3, 4]);
    }

    #[test]
    fn sized_deref_mut_inline() {
        let mut f: Flex<u64, B16> = Flex::new(10);
        assert!(f.is_inline());
        *f = 20;
        assert_eq!(*f, 20);
    }

    #[test]
    fn sized_deref_mut_heap() {
        let mut f: Flex<[u64; 4], B16> = Flex::new([0u64; 4]);
        assert!(!f.is_inline());
        f[0] = 99;
        assert_eq!(f[0], 99);
    }

    #[test]
    fn zst_always_inline() {
        let f: Flex<dyn Greet, B32> = make_flex_greet(Hello);
        assert!(f.is_inline());
        assert_eq!(f.greet(), "hello");
    }

    #[test]
    fn small_value_inline() {
        let f: Flex<dyn Greet, B32> = make_flex_greet(World(42));
        assert!(f.is_inline());
        assert_eq!(f.greet(), "world");
    }

    #[test]
    fn large_value_heap() {
        // [u64; 8] = 64 bytes, B32 ?Sized capacity = 16 bytes
        #[allow(dead_code)]
        struct Big([u64; 8]);
        impl Greet for Big {
            fn greet(&self) -> &'static str {
                "big"
            }
        }

        let f: Flex<dyn Greet, B32> = make_flex_greet(Big([0xAB; 8]));
        assert!(!f.is_inline());
        assert_eq!(f.greet(), "big");
    }

    #[test]
    fn b16_unsized_zero_capacity_goes_to_heap() {
        // B16 has 0 bytes value capacity for ?Sized — non-ZSTs must go to heap.
        let f: Flex<dyn Greet, B16> = make_flex_greet(World(7));
        assert!(!f.is_inline());
        assert_eq!(f.greet(), "world");
    }

    #[test]
    fn b16_unsized_zst_still_inline() {
        let f: Flex<dyn Greet, B16> = make_flex_greet(Hello);
        assert!(f.is_inline());
        assert_eq!(f.greet(), "hello");
    }

    #[test]
    fn deref_mut_inline() {
        trait Increment {
            fn inc(&mut self);
            fn val(&self) -> u64;
        }

        struct Counter(u64);
        impl Increment for Counter {
            fn inc(&mut self) {
                self.0 += 1;
            }
            fn val(&self) -> u64 {
                self.0
            }
        }

        fn make<V: Increment + 'static, B: Buffer>(val: V) -> Flex<dyn Increment, B> {
            let ptr: *const dyn Increment = &val as &dyn Increment;
            // SAFETY: ptr coerced from val above; metadata matches V.
            unsafe { Flex::new_raw(val, ptr) }
        }

        let mut f: Flex<dyn Increment, B32> = make(Counter(0));
        assert!(f.is_inline());
        f.inc();
        f.inc();
        assert_eq!(f.val(), 2);
    }

    #[test]
    fn deref_mut_heap() {
        trait Accumulate {
            fn push(&mut self, v: u64);
            fn sum(&self) -> u64;
        }

        struct BigAccum {
            data: [u64; 15],
            count: usize,
        }
        impl BigAccum {
            fn new() -> Self {
                BigAccum {
                    data: [0; 15],
                    count: 0,
                }
            }
        }
        impl Accumulate for BigAccum {
            fn push(&mut self, v: u64) {
                self.data[self.count] = v;
                self.count += 1;
            }
            fn sum(&self) -> u64 {
                self.data[..self.count].iter().sum()
            }
        }

        fn make<V: Accumulate + 'static, B: Buffer>(val: V) -> Flex<dyn Accumulate, B> {
            let ptr: *const dyn Accumulate = &val as &dyn Accumulate;
            // SAFETY: ptr coerced from val above; metadata matches V.
            unsafe { Flex::new_raw(val, ptr) }
        }

        let mut f: Flex<dyn Accumulate, B32> = make(BigAccum::new());
        assert!(!f.is_inline());
        f.push(10);
        f.push(20);
        assert_eq!(f.sum(), 30);
    }

    #[test]
    fn drop_inline() {
        static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

        struct Dropper;
        impl Drop for Dropper {
            fn drop(&mut self) {
                DROP_COUNT.fetch_add(1, Ordering::Relaxed);
            }
        }
        impl Greet for Dropper {
            fn greet(&self) -> &'static str {
                "dropping"
            }
        }

        DROP_COUNT.store(0, Ordering::Relaxed);
        {
            let f: Flex<dyn Greet, B32> = make_flex_greet(Dropper);
            assert!(f.is_inline());
            assert_eq!(f.greet(), "dropping");
        }
        assert_eq!(DROP_COUNT.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn drop_heap() {
        static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

        #[allow(dead_code)]
        struct BigDropper([u64; 8]);
        impl Drop for BigDropper {
            fn drop(&mut self) {
                DROP_COUNT.fetch_add(1, Ordering::Relaxed);
            }
        }
        impl Greet for BigDropper {
            fn greet(&self) -> &'static str {
                "big drop"
            }
        }

        DROP_COUNT.store(0, Ordering::Relaxed);
        {
            let f: Flex<dyn Greet, B32> = make_flex_greet(BigDropper([0; 8]));
            assert!(!f.is_inline());
            assert_eq!(f.greet(), "big drop");
        }
        assert_eq!(DROP_COUNT.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn drop_heap_sized() {
        static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

        #[allow(dead_code)]
        struct BigDropper([u64; 8]);
        impl Drop for BigDropper {
            fn drop(&mut self) {
                DROP_COUNT.fetch_add(1, Ordering::Relaxed);
            }
        }

        DROP_COUNT.store(0, Ordering::Relaxed);
        {
            let f: Flex<BigDropper, B16> = Flex::new(BigDropper([0; 8]));
            assert!(!f.is_inline());
        }
        assert_eq!(DROP_COUNT.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn display_trait_object_inline() {
        let val: u32 = 42;
        let ptr: *const dyn Display = &val as &dyn Display;
        // SAFETY: ptr coerced from val above; metadata matches V.
        let f: Flex<dyn Display, B32> = unsafe { Flex::new_raw(val, ptr) };
        assert!(f.is_inline());
        assert_eq!(format!("{}", &*f), "42");
    }

    #[test]
    fn exact_fit_is_inline() {
        // [usize; 2] = 16 bytes, B32 ?Sized capacity = 16 bytes — exact fit
        #[allow(dead_code)]
        struct Exact([usize; 2]);
        impl Greet for Exact {
            fn greet(&self) -> &'static str {
                "exact"
            }
        }

        let f: Flex<dyn Greet, B32> = make_flex_greet(Exact([1, 2]));
        assert!(f.is_inline());
        assert_eq!(f.greet(), "exact");
    }

    #[test]
    fn one_byte_over_goes_to_heap() {
        // [usize; 2] + u8 = 17 bytes (with padding: 24), B32 ?Sized capacity = 16
        #[repr(C)]
        struct OneTooMany {
            _data: [usize; 2],
            _extra: u8,
        }
        impl Greet for OneTooMany {
            fn greet(&self) -> &'static str {
                "spilled"
            }
        }

        let f: Flex<dyn Greet, B32> = make_flex_greet(OneTooMany {
            _data: [0; 2],
            _extra: 0,
        });
        assert!(!f.is_inline());
        assert_eq!(f.greet(), "spilled");
    }

    #[test]
    fn macro_construction_inline() {
        let f: Flex<dyn Greet, B32> = crate::flex!(Hello);
        assert!(f.is_inline());
        assert_eq!(f.greet(), "hello");
    }

    #[test]
    fn macro_construction_heap() {
        #[allow(dead_code)]
        struct Big([u64; 8]);
        impl Greet for Big {
            fn greet(&self) -> &'static str {
                "big"
            }
        }

        let f: Flex<dyn Greet, B32> = crate::flex!(Big([0; 8]));
        assert!(!f.is_inline());
        assert_eq!(f.greet(), "big");
    }
}
