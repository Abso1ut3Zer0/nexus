//! Type-erased byte slab allocation.
//!
//! Store heterogeneous types in a single slab. Each slot is `N` bytes
//! with pointer alignment. Any `T` that fits (`size_of::<T>() <= N`,
//! `align_of::<T>() <= 8`) can be stored.
//!
//! Two variants mirror the typed slab API:
//! - [`bounded::Slab`] — fixed capacity, returns `Err(Full)` when full
//! - [`unbounded::Slab`] — grows via chunks, never fails
//!
//! # Example
//!
//! ```
//! use nexus_slab::byte::bounded::Slab;
//!
//! // SAFETY: caller guarantees slab contract (see struct docs)
//! let slab: Slab<128> = unsafe { Slab::with_capacity(64) };
//!
//! let ptr = slab.alloc(42u64);
//! assert_eq!(*ptr, 42);
//! slab.free(ptr);
//!
//! // Different type, same slab
//! let ptr = slab.alloc([1.0f64; 8]);
//! assert_eq!(ptr[0], 1.0);
//! slab.free(ptr);
//! ```

use core::marker::PhantomData;

// =============================================================================
// AlignedBytes
// =============================================================================

/// Fixed-size byte storage with pointer alignment.
///
/// Used as the backing type for byte slabs. The 8-byte alignment
/// matches the `next_free` pointer in [`SlotCell`](crate::SlotCell)
/// and covers all common types (up to `u64`, pointers, most structs).
///
/// Types requiring greater than 8-byte alignment (e.g., SIMD vectors)
/// cannot be stored in a byte slab.
///
/// `Copy` ensures `drop_in_place` is a compile-time no-op.
#[derive(Clone, Copy)]
#[repr(C, align(8))]
pub struct AlignedBytes<const N: usize> {
    bytes: [u8; N],
}

// =============================================================================
// Slot
// =============================================================================

/// Typed handle to a value stored in a byte slab.
///
/// The slab stores raw bytes, but this handle remembers the original
/// type `T`. Provides safe `Deref`/`DerefMut` access. Move-only —
/// cannot be copied or cloned.
///
/// # Debug Leak Detection
///
/// Same as [`Slot`](crate::Slot) — panics on drop in debug
/// builds if not freed.
pub struct Slot<T> {
    ptr: *mut u8,
    _marker: PhantomData<T>,
}

impl<T> Slot<T> {
    /// Creates a duplicate pointer to the same slot.
    ///
    /// # Safety
    ///
    /// Caller must ensure the slot is not freed while any clone exists.
    #[inline]
    pub unsafe fn clone_ptr(&self) -> Self {
        Slot {
            ptr: self.ptr,
            _marker: PhantomData,
        }
    }

    /// Returns a raw pointer to the underlying byte storage.
    #[inline]
    pub fn as_ptr(&self) -> *mut u8 {
        self.ptr
    }

    /// Consumes the handle, returning the raw pointer without running Drop.
    ///
    /// Reconstruct via [`from_raw()`](Self::from_raw). Disarms the debug
    /// leak detector.
    #[inline]
    pub fn into_raw(self) -> *mut u8 {
        let ptr = self.ptr;
        core::mem::forget(self);
        ptr
    }

    /// Reconstructs a `Slot` from a raw pointer previously obtained
    /// via [`into_raw()`](Self::into_raw).
    ///
    /// # Safety
    ///
    /// `ptr` must point to a valid, initialized `T` within a byte slab,
    /// originally obtained from `into_raw()`.
    #[inline]
    pub unsafe fn from_raw(ptr: *mut u8) -> Self {
        Slot {
            ptr,
            _marker: PhantomData,
        }
    }

    /// Returns a pinned reference to the value.
    ///
    /// # Unsound: deprecated
    ///
    /// This method is unsound for `!Unpin` types and will be removed in 2.4.0.
    /// A stable address is only half of `Pin`'s contract; the value must also
    /// never be moved out until it is dropped, and safe code can move it:
    /// [`Slab::take`](crate::byte::bounded::Slab::take) moves it out by value,
    /// and `mem::swap` through `DerefMut` moves two of them. For `T: Unpin`,
    /// use `Pin::new(&*slot)` instead. A sound pinned handle that consumes the
    /// `Slot` ships in 2.4.0 (issue #751).
    #[deprecated(
        since = "2.3.5",
        note = "unsound for !Unpin types: the value can be moved through safe take()/DerefMut; use Pin::new for Unpin types, or the PinnedSlot handle in 2.4.0"
    )]
    #[inline]
    pub fn pin(&self) -> core::pin::Pin<&T> {
        // SAFETY: the address is stable (byte slab storage never moves), but
        // the second half of Pin's contract, that the value is never moved
        // out, cannot be guaranteed from a handle that also offers safe
        // `take()` and `DerefMut`. Deprecated for that reason; see its docs.
        unsafe { core::pin::Pin::new_unchecked(&**self) }
    }

    /// Returns a pinned mutable reference to the value.
    ///
    /// # Unsound: deprecated
    ///
    /// See [`pin()`](Self::pin). Same defect, same removal in 2.4.0. For
    /// `T: Unpin`, use `Pin::new(&mut *slot)` instead.
    #[deprecated(
        since = "2.3.5",
        note = "unsound for !Unpin types: the value can be moved through safe take()/DerefMut; use Pin::new for Unpin types, or the PinnedSlot handle in 2.4.0"
    )]
    #[inline]
    pub fn pin_mut(&mut self) -> core::pin::Pin<&mut T> {
        // SAFETY: not fully upheld; see `pin()`. Deprecated for that reason.
        unsafe { core::pin::Pin::new_unchecked(&mut **self) }
    }
}

impl<T> core::ops::Deref for Slot<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        // SAFETY: ptr points to a valid, initialized T within the slab.
        unsafe { &*self.ptr.cast::<T>() }
    }
}

impl<T> core::ops::DerefMut for Slot<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: We have &mut self, guaranteeing exclusive access.
        unsafe { &mut *self.ptr.cast::<T>() }
    }
}

impl<T> core::convert::AsRef<T> for Slot<T> {
    #[inline]
    fn as_ref(&self) -> &T {
        self
    }
}

impl<T> core::convert::AsMut<T> for Slot<T> {
    #[inline]
    fn as_mut(&mut self) -> &mut T {
        self
    }
}

impl<T> core::borrow::Borrow<T> for Slot<T> {
    #[inline]
    fn borrow(&self) -> &T {
        self
    }
}

impl<T> core::borrow::BorrowMut<T> for Slot<T> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut T {
        self
    }
}

impl<T: core::fmt::Debug> core::fmt::Debug for Slot<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("byte::Slot")
            .field("value", &**self)
            .finish()
    }
}

#[cfg(debug_assertions)]
impl<T> Drop for Slot<T> {
    fn drop(&mut self) {
        #[cfg(feature = "std")]
        if std::thread::panicking() {
            return;
        }
        panic!(
            "byte::Slot<{}> dropped without being freed — call slab.free(ptr) or slab.take(ptr)",
            core::any::type_name::<T>()
        );
    }
}

// =============================================================================
// ByteClaim — reserved byte slot handle
// =============================================================================

/// A reserved byte slab slot.
///
/// Write a value with [`.write()`](Self::write) or raw bytes with
/// [`.write_raw()`](Self::write_raw). If dropped without writing, the
/// slot is returned to the freelist automatically. Works with both
/// bounded and unbounded byte slabs.
pub struct ByteClaim<'a> {
    ptr: *mut u8,
    slab_ptr: *const u8,
    free: unsafe fn(*const u8, *mut u8, usize),
    chunk_idx: usize,
    slot_size: usize,
    _borrow: core::marker::PhantomData<&'a ()>,
}

impl ByteClaim<'_> {
    /// Create a claim from raw components.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a valid, vacant slab slot.
    /// - `slab_ptr` must point to the originating slab.
    /// - `free(slab_ptr, ptr, chunk_idx)` must correctly return the slot to the freelist.
    /// - `chunk_idx` must be the owning chunk index (0 for bounded slabs).
    /// - `slot_size` must be the actual slot capacity in bytes.
    pub(crate) unsafe fn from_raw_parts(
        ptr: *mut u8,
        slab_ptr: *const u8,
        free: unsafe fn(*const u8, *mut u8, usize),
        chunk_idx: usize,
        slot_size: usize,
    ) -> Self {
        Self {
            ptr,
            slab_ptr,
            free,
            chunk_idx,
            slot_size,
            _borrow: core::marker::PhantomData,
        }
    }

    /// Write a typed value into the slot. Consumes the claim.
    ///
    /// # Panics
    ///
    /// - Panics if `size_of::<T>() > slot_size`
    /// - Panics if `align_of::<T>() > 8`
    #[inline]
    pub fn write<T>(self, value: T) -> Slot<T> {
        validate_type_dynamic::<T>(self.slot_size);

        // SAFETY: ptr is a valid, vacant slot with slot_size >= size_of::<T>().
        // AlignedBytes guarantees 8-byte alignment. validate_type checked fit.
        unsafe { core::ptr::write(self.ptr.cast::<T>(), value) };

        let ptr = self.ptr;
        // Don't run Drop — the slot is now occupied.
        core::mem::forget(self);

        Slot {
            ptr,
            _marker: core::marker::PhantomData,
        }
    }

    /// Copy raw bytes into the slot. Consumes the claim.
    ///
    /// Returns the raw pointer to the written data.
    ///
    /// # Safety
    ///
    /// - `src` must point to `size` valid bytes.
    ///
    /// # Panics
    ///
    /// - Panics if `size > slot_size`.
    #[inline]
    pub unsafe fn write_raw(self, src: *const u8, size: usize) -> *mut u8 {
        assert!(
            size <= self.slot_size,
            "write_raw size ({size}) exceeds slot size ({})",
            self.slot_size
        );

        // SAFETY: ptr is valid and vacant with slot_size >= size. Caller guarantees src validity.
        unsafe { core::ptr::copy_nonoverlapping(src, self.ptr, size) };

        let ptr = self.ptr;
        core::mem::forget(self);
        ptr
    }

    /// Raw pointer to the reserved slot.
    #[inline]
    pub fn as_ptr(&self) -> *mut u8 {
        self.ptr
    }

    /// Slot capacity in bytes.
    #[inline]
    pub fn slot_size(&self) -> usize {
        self.slot_size
    }

    /// Chunk index (for unbounded slabs). Always 0 for bounded.
    #[inline]
    pub fn chunk_idx(&self) -> usize {
        self.chunk_idx
    }
}

impl Drop for ByteClaim<'_> {
    fn drop(&mut self) {
        // Slot was claimed but never written — return to freelist.
        // SAFETY: free was set at claim time to the correct slab's freelist
        // return function. The slot is vacant (no value to drop).
        unsafe { (self.free)(self.slab_ptr, self.ptr, self.chunk_idx) };
    }
}

impl core::fmt::Debug for ByteClaim<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ByteClaim")
            .field("ptr", &self.ptr)
            .field("slot_size", &self.slot_size)
            .finish()
    }
}

/// Validates that `T` fits in the given slot size with appropriate alignment.
/// Used by `ByteClaim::write()` where the slot size is known at runtime.
#[inline]
fn validate_type_dynamic<T>(slot_size: usize) {
    assert!(
        core::mem::size_of::<T>() <= slot_size,
        "type {} ({} bytes) exceeds byte slab slot size ({slot_size} bytes)",
        core::any::type_name::<T>(),
        core::mem::size_of::<T>(),
    );
    assert!(
        core::mem::align_of::<T>() <= 8,
        "type {} (align {}) exceeds byte slab alignment (8)",
        core::any::type_name::<T>(),
        core::mem::align_of::<T>(),
    );
}

/// Validates that `T` fits in `N` bytes with appropriate alignment.
#[inline]
fn validate_type<T, const N: usize>() {
    assert!(
        core::mem::size_of::<T>() <= N,
        "type {} ({} bytes) exceeds byte slab slot size ({N} bytes)",
        core::any::type_name::<T>(),
        core::mem::size_of::<T>(),
    );
    assert!(
        core::mem::align_of::<T>() <= 8,
        "type {} (align {}) exceeds byte slab alignment (8)",
        core::any::type_name::<T>(),
        core::mem::align_of::<T>(),
    );
}

pub mod bounded;
pub mod unbounded;
