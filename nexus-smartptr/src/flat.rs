//! Inline-only trait object storage.
//!
//! [`Flat<T, B>`] stores a `?Sized` value (typically `dyn Trait`) inline
//! in a fixed-size buffer. No heap allocation, ever. Panics at construction
//! if the concrete type doesn't fit.
//!
//! `B` is a buffer marker type — `size_of::<Flat<dyn Trait, B32>>() == 32`.

use core::marker::PhantomData;
use core::mem::{self, MaybeUninit};
use core::ops::{Deref, DerefMut};
use core::ptr;

use crate::Buffer;
use crate::meta::{self, Metadata};

/// Size of the metadata word (vtable pointer or slice length).
const META_SIZE: usize = mem::size_of::<Metadata>();

/// Compile-time check that the buffer can hold the metadata overhead.
///
/// For ?Sized T: B::CAPACITY >= 8 (metadata word).
/// For Sized T: no constraint (no metadata overhead).
const fn assert_flat_buffer<T: ?Sized, B: Buffer>() {
    if meta::is_fat_ptr::<T>() {
        assert!(
            B::CAPACITY >= META_SIZE,
            "Flat: buffer must be at least pointer-sized for ?Sized types"
        );
    }
}

/// Inline-only storage for `?Sized` types.
///
/// Stores a trait object (or slice) directly in a buffer of type `B`.
/// The total struct size equals `size_of::<B>()`.
///
/// - **Sized T**: full buffer capacity, value at offset 0.
/// - **?Sized T**: one pointer-sized word reserved for metadata, value follows.
///
/// Use the [`flat!`](crate::flat!) macro for `?Sized` construction,
/// or [`Flat::new`] for `Sized` types.
///
/// # Compile-time safety
///
/// The `?Sized` metadata overhead (one pointer-sized word) is validated at compile time
/// for hand-implemented [`Buffer`](crate::Buffer) types. All predefined
/// buffers (`B16`+) satisfy this constraint.
#[repr(C)]
pub struct Flat<T: ?Sized, B: Buffer> {
    inner: MaybeUninit<B>,
    _marker: PhantomData<T>,
}

// -- Methods for all T (including ?Sized) --
impl<T: ?Sized, B: Buffer> Flat<T, B> {
    /// Returns the usable value capacity in bytes.
    ///
    /// For `Sized` types, this is the full buffer. For `?Sized` types,
    /// one pointer-sized word is reserved for metadata (vtable or slice length).
    pub const fn capacity() -> usize {
        if meta::is_fat_ptr::<T>() {
            B::CAPACITY.saturating_sub(META_SIZE)
        } else {
            B::CAPACITY
        }
    }

    /// Constructs a `Flat` from a concrete value and a (possibly fat) pointer.
    ///
    /// This is an implementation detail of the [`flat!`](crate::flat!) macro.
    /// Do not call directly.
    ///
    /// # Panics
    ///
    /// - If `size_of::<V>()` exceeds [`capacity()`](Self::capacity).
    /// - If `align_of::<V>()` exceeds `align_of::<usize>()`.
    ///
    /// # Safety
    ///
    /// `ptr` must be a pointer whose metadata (vtable/length) corresponds to `V`.
    /// The [`flat!`](crate::flat!) macro guarantees this via unsizing coercion.
    #[doc(hidden)]
    pub unsafe fn new_raw<V>(val: V, ptr: *const T) -> Self {
        // Compile-time: buffer must fit the metadata overhead.
        const { assert_flat_buffer::<T, B>() }

        let size = mem::size_of::<V>();
        let align = mem::align_of::<V>();

        assert!(
            size <= Self::capacity(),
            "nexus_smartptr::Flat: value of type `{}` ({size} bytes) exceeds \
             capacity ({} bytes)",
            core::any::type_name::<V>(),
            Self::capacity(),
        );
        assert!(
            align <= mem::align_of::<usize>(),
            "nexus_smartptr::Flat: alignment of `{}` ({align}) exceeds \
             buffer alignment ({})",
            core::any::type_name::<V>(),
            mem::align_of::<usize>(),
        );

        let metadata = meta::extract_metadata(ptr);

        let mut this: Self = Flat {
            inner: MaybeUninit::uninit(),
            _marker: PhantomData,
        };

        let base = this.inner.as_mut_ptr().cast::<u8>();
        // SAFETY: we verified size <= capacity and align <= align_of::<usize>().
        // Buffer has align(8) >= align_of::<usize>().
        unsafe {
            if meta::is_fat_ptr::<T>() {
                // ?Sized: metadata at offset 0, value at offset META_SIZE.
                base.cast::<*const ()>().write(metadata.0);
                base.add(META_SIZE).cast::<V>().write(val);
            } else {
                // Sized: value at offset 0, full capacity.
                base.cast::<V>().write(val);
            }
        }

        this
    }

    /// Returns a (possibly fat) pointer to the stored value.
    #[inline(always)]
    fn as_ptr(&self) -> *const T {
        let base = self.inner.as_ptr().cast::<u8>();
        if meta::is_fat_ptr::<T>() {
            // SAFETY: metadata was written at offset 0 during construction.
            // Reading as *const () preserves provenance.
            let metadata = Metadata(unsafe { base.cast::<*const ()>().read() });
            // SAFETY: buffer has at least META_SIZE capacity (verified at construction).
            let data = unsafe { base.add(META_SIZE) }.cast::<()>();
            // SAFETY: data points to the value, metadata matches the concrete type.
            unsafe { meta::make_ptr(data, metadata) }
        } else {
            // SAFETY: value is at offset 0. For Sized T, no metadata needed.
            unsafe { meta::make_ptr(base.cast::<()>(), Metadata::NULL) }
        }
    }

    /// Returns a mutable (possibly fat) pointer to the stored value.
    #[inline(always)]
    fn as_mut_ptr(&mut self) -> *mut T {
        let base = self.inner.as_mut_ptr().cast::<u8>();
        if meta::is_fat_ptr::<T>() {
            // SAFETY: metadata written at offset 0 during construction.
            let metadata = Metadata(unsafe { base.cast::<*const ()>().read() });
            // SAFETY: buffer has at least META_SIZE capacity (verified at construction).
            let data = unsafe { base.add(META_SIZE) }.cast::<()>();
            // SAFETY: data points to value, metadata matches the concrete type.
            unsafe { meta::make_ptr_mut(data, metadata) }
        } else {
            // SAFETY: value at offset 0; Sized T needs no metadata.
            unsafe { meta::make_ptr_mut(base.cast::<()>(), Metadata::NULL) }
        }
    }
}

// -- Methods only for Sized T --
impl<T, B: Buffer> Flat<T, B> {
    /// Constructs a `Flat` from a `Sized` value.
    ///
    /// The value is stored at offset 0 with full buffer capacity.
    ///
    /// # Panics
    ///
    /// - If `size_of::<T>()` exceeds `B::CAPACITY`.
    /// - If `align_of::<T>()` exceeds `align_of::<usize>()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use nexus_smartptr::{Flat, B32};
    ///
    /// let f: Flat<u64, B32> = Flat::new(42);
    /// assert_eq!(*f, 42);
    /// ```
    pub fn new(val: T) -> Self {
        assert!(
            mem::size_of::<T>() <= B::CAPACITY,
            "nexus_smartptr::Flat: value of type `{}` ({} bytes) exceeds \
             buffer capacity ({} bytes)",
            core::any::type_name::<T>(),
            mem::size_of::<T>(),
            B::CAPACITY,
        );
        assert!(
            mem::align_of::<T>() <= mem::align_of::<usize>(),
            "nexus_smartptr::Flat: alignment of `{}` ({}) exceeds \
             buffer alignment ({})",
            core::any::type_name::<T>(),
            mem::align_of::<T>(),
            mem::align_of::<usize>(),
        );

        let mut this: Self = Flat {
            inner: MaybeUninit::uninit(),
            _marker: PhantomData,
        };

        // SAFETY: value at offset 0. size/align verified above.
        // Buffer has align(8) >= align_of::<usize>().
        unsafe {
            this.inner.as_mut_ptr().cast::<T>().write(val);
        }

        this
    }
}

impl<T: ?Sized, B: Buffer> Deref for Flat<T, B> {
    type Target = T;

    #[inline(always)]
    fn deref(&self) -> &T {
        // SAFETY: inner contains a valid, initialized value.
        // as_ptr reconstructs the correct (fat or thin) pointer.
        unsafe { &*self.as_ptr() }
    }
}

impl<T: ?Sized, B: Buffer> DerefMut for Flat<T, B> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: same as Deref, plus exclusive access via &mut self.
        unsafe { &mut *self.as_mut_ptr() }
    }
}

impl<T: ?Sized, B: Buffer> Drop for Flat<T, B> {
    fn drop(&mut self) {
        // SAFETY: as_mut_ptr returns a valid pointer to the stored value.
        // After drop_in_place, inner is uninitialized — no further access.
        unsafe {
            ptr::drop_in_place(self.as_mut_ptr());
        }
    }
}

// SAFETY: Flat<T, B> logically owns a T. The raw pointer in metadata is just
// a vtable pointer (not a data pointer), so Send/Sync depend only on T.
// MaybeUninit<B> is raw storage, not a meaningful Send/Sync participant.
#[allow(clippy::non_send_fields_in_send_ty)]
unsafe impl<T: ?Sized + Send, B: Buffer> Send for Flat<T, B> {}
// SAFETY: same as Send above; Sync depends only on T.
unsafe impl<T: ?Sized + Sync, B: Buffer> Sync for Flat<T, B> {}

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

    fn make_flat_greet<V: Greet + 'static, B: Buffer>(val: V) -> Flat<dyn Greet, B> {
        let ptr: *const dyn Greet = &val as &dyn Greet;
        // SAFETY: ptr coerced from val above; metadata matches V.
        unsafe { Flat::new_raw(val, ptr) }
    }

    #[test]
    fn total_size_matches_buffer() {
        assert_eq!(mem::size_of::<Flat<dyn Greet, B16>>(), 16);
        assert_eq!(mem::size_of::<Flat<dyn Greet, B32>>(), 32);
        assert_eq!(mem::size_of::<Flat<dyn Greet, B64>>(), 64);
        assert_eq!(mem::size_of::<Flat<u64, B32>>(), 32);
    }

    #[test]
    fn sized_capacity_is_full_buffer() {
        assert_eq!(Flat::<u64, B32>::capacity(), 32);
        assert_eq!(Flat::<u64, B64>::capacity(), 64);
    }

    #[test]
    fn unsized_capacity_reserves_metadata() {
        assert_eq!(Flat::<dyn Greet, B16>::capacity(), 8);
        assert_eq!(Flat::<dyn Greet, B32>::capacity(), 24);
        assert_eq!(Flat::<dyn Greet, B64>::capacity(), 56);
    }

    #[test]
    fn sized_new() {
        let f: Flat<u64, B32> = Flat::new(42);
        assert_eq!(*f, 42);
    }

    #[test]
    fn sized_new_struct() {
        #[derive(Debug, PartialEq)]
        struct Pair(u64, u64);

        let f: Flat<Pair, B32> = Flat::new(Pair(1, 2));
        assert_eq!(*f, Pair(1, 2));
    }

    #[test]
    fn sized_deref_mut() {
        let mut f: Flat<u64, B16> = Flat::new(10);
        *f = 20;
        assert_eq!(*f, 20);
    }

    #[test]
    fn zst_inline() {
        let f: Flat<dyn Greet, B16> = make_flat_greet(Hello);
        assert_eq!(f.greet(), "hello");
    }

    #[test]
    fn non_zst_inline() {
        let f: Flat<dyn Greet, B32> = make_flat_greet(World(42));
        assert_eq!(f.greet(), "world");
    }

    #[test]
    fn deref_mut_trait_object() {
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

        fn make<V: Increment + 'static, B: Buffer>(val: V) -> Flat<dyn Increment, B> {
            let ptr: *const dyn Increment = &val as &dyn Increment;
            // SAFETY: ptr coerced from val above; metadata matches V.
            unsafe { Flat::new_raw(val, ptr) }
        }

        let mut f: Flat<dyn Increment, B32> = make(Counter(0));
        f.inc();
        f.inc();
        assert_eq!(f.val(), 2);
    }

    #[test]
    fn drop_runs() {
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
            let f: Flat<dyn Greet, B16> = make_flat_greet(Dropper);
            assert_eq!(f.greet(), "dropping");
        }
        assert_eq!(DROP_COUNT.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn drop_runs_sized() {
        static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

        #[allow(dead_code)]
        struct Dropper(u64);
        impl Drop for Dropper {
            fn drop(&mut self) {
                DROP_COUNT.fetch_add(1, Ordering::Relaxed);
            }
        }

        DROP_COUNT.store(0, Ordering::Relaxed);
        {
            let _f: Flat<Dropper, B16> = Flat::new(Dropper(99));
        }
        assert_eq!(DROP_COUNT.load(Ordering::Relaxed), 1);
    }

    #[test]
    #[should_panic(expected = "exceeds capacity")]
    fn panics_on_overflow_unsized() {
        #[allow(dead_code)]
        struct Big([u64; 8]);
        impl Greet for Big {
            fn greet(&self) -> &'static str {
                "big"
            }
        }
        let _: Flat<dyn Greet, B16> = make_flat_greet(Big([0; 8]));
    }

    #[test]
    #[should_panic(expected = "exceeds buffer capacity")]
    fn panics_on_overflow_sized() {
        let _: Flat<[u64; 8], B16> = Flat::new([0u64; 8]);
    }

    #[test]
    fn display_trait_object() {
        let val: u32 = 42;
        let ptr: *const dyn Display = &val as &dyn Display;
        // SAFETY: ptr coerced from val above; metadata matches V.
        let f: Flat<dyn Display, B32> = unsafe { Flat::new_raw(val, ptr) };
        assert_eq!(format!("{}", &*f), "42");
    }

    #[test]
    fn different_concrete_types_same_trait() {
        let f1: Flat<dyn Greet, B32> = make_flat_greet(Hello);
        let f2: Flat<dyn Greet, B32> = make_flat_greet(World(99));
        assert_eq!(f1.greet(), "hello");
        assert_eq!(f2.greet(), "world");
    }

    #[test]
    fn macro_construction() {
        let f: Flat<dyn Greet, B32> = crate::flat!(Hello);
        assert_eq!(f.greet(), "hello");
    }

    #[test]
    fn macro_display() {
        let f: Flat<dyn Display, B32> = crate::flat!(42_u32);
        assert_eq!(format!("{}", &*f), "42");
    }
}
