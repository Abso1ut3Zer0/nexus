//! Growable reference-counted slab.

use core::marker::PhantomData;

use super::{RcCell, RcSlot};

/// Growable slab with reference-counted handles.
///
/// Wraps [`crate::unbounded::Slab`] with `RcCell<T>` storage.
/// Never fails — grows via chunks when full.
///
/// # Surface
///
/// Mirrors [`crate::unbounded::Slab`]: [`Builder`],
/// [`capacity`](Self::capacity), [`chunk_capacity`](Self::chunk_capacity),
/// [`chunk_count`](Self::chunk_count), [`reserve_chunks`](Self::reserve_chunks),
/// [`alloc`](Self::alloc), [`free`](Self::free). Two deliberate differences:
///
/// - **No `take()`.** Taking the value out while other `RcSlot` handles are
///   live (refcount > 0) would leave them pointing at a vacated slot. Rc
///   slabs free by refcount only; the value is dropped when the last handle
///   is freed.
/// - **No `try_alloc()`.** Unbounded slabs grow and can never be `Full`.
///
/// `claim()` (allocate now, write later) is not offered yet: it needs a claim
/// type that resolves to an `RcSlot<T>`, and is parked until a caller exists.
/// # Thread Safety
///
/// `!Send` and `!Sync`. The refcount is a non-atomic `Cell`, so the slab and
/// every `RcSlot` it hands out stay on one thread:
///
/// ```compile_fail,E0277
/// fn assert_send<T: Send>() {}
/// assert_send::<nexus_slab::rc::unbounded::Slab<u64>>();
/// ```
pub struct Slab<T> {
    inner: crate::unbounded::Slab<RcCell<T>>,
    /// Pins the slab to one thread. The inner typed slab is `Send`, but the
    /// refcount in every `RcCell` is a non-atomic `Cell`, so an Rc slab and
    /// its handles must stay together on the thread that created them.
    _not_send: PhantomData<*const ()>,
}

impl<T> Slab<T> {
    /// Creates a new Rc slab with the given chunk capacity.
    ///
    /// # Safety
    ///
    /// See [`crate::unbounded::Slab`] safety contract.
    #[inline]
    pub unsafe fn with_chunk_capacity(chunk_capacity: usize) -> Self {
        Self {
            // SAFETY: Caller upholds the slab contract.
            inner: unsafe { crate::unbounded::Slab::with_chunk_capacity(chunk_capacity) },
            _not_send: PhantomData,
        }
    }

    /// Allocates a value. Never fails — grows if needed.
    #[inline]
    pub fn alloc(&self, value: T) -> RcSlot<T> {
        let slot = self.inner.alloc(RcCell::new(value));
        // SAFETY: slot is valid and occupied with RcCell<T>. Cast is sound
        // because SlotCell value is at offset 0 (repr(C) union).
        unsafe { RcSlot::from_ptr(slot.into_raw().cast()) }
    }

    /// Frees a handle. Decrements refcount; deallocates on last free.
    #[inline]
    // Consumes the handle by design — refcount-decrementing free, the
    // handle cannot be used after this call.
    #[allow(clippy::needless_pass_by_value)]
    pub fn free(&self, handle: RcSlot<T>) {
        let count = handle.dec_ref();
        if count == 0 {
            // SAFETY: Refcount is 0 — no other handles exist. Drop the value
            // and return the slot to the freelist.
            unsafe { handle.drop_value() };
            let cell_ptr = handle.slot_cell_ptr();
            core::mem::forget(handle);
            // SAFETY: cell_ptr is within this slab. Value already dropped above.
            unsafe { self.inner.free_ptr(cell_ptr) };
        } else {
            core::mem::forget(handle);
        }
    }

    /// Returns the total capacity across all chunks.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Returns the chunk capacity.
    #[inline]
    pub fn chunk_capacity(&self) -> usize {
        self.inner.chunk_capacity()
    }

    /// Returns the number of allocated chunks.
    #[inline]
    pub fn chunk_count(&self) -> usize {
        self.inner.chunk_count()
    }

    /// Ensures at least `count` chunks are allocated.
    ///
    /// No-op if the slab already has `count` or more chunks. Only allocates
    /// the difference.
    #[inline]
    pub fn reserve_chunks(&self, count: usize) {
        self.inner.reserve_chunks(count);
    }

    /// Returns `true` if `ptr` falls within this slab's slot storage.
    ///
    /// O(chunks) scan. Typically 1–5 chunks. Used in `debug_assert!`
    /// to validate provenance.
    #[doc(hidden)]
    #[inline]
    pub fn contains_ptr(&self, ptr: *const ()) -> bool {
        self.inner.contains_ptr(ptr)
    }
}

impl<T> core::fmt::Debug for Slab<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("rc::unbounded::Slab")
            .field("capacity", &self.capacity())
            .finish()
    }
}

// =============================================================================
// Builder
// =============================================================================

/// Builder for [`Slab`].
///
/// Same surface as [`crate::unbounded::Builder`]; the type parameter only
/// appears at the terminal [`build()`](Self::build) call.
///
/// # Example
///
/// ```
/// use nexus_slab::rc::unbounded::Builder;
///
/// // SAFETY: caller guarantees slab contract (see Slab docs)
/// let slab = unsafe {
///     Builder::new()
///         .chunk_capacity(64)
///         .initial_chunks(2)
///         .build::<u64>()
/// };
/// assert_eq!(slab.chunk_count(), 2);
/// let h = slab.alloc(42);
/// assert_eq!(*h.borrow(), 42);
/// slab.free(h);
/// ```
#[derive(Debug, Clone)]
pub struct Builder {
    inner: crate::unbounded::Builder,
}

impl Builder {
    /// Creates a new builder with the same defaults as
    /// [`crate::unbounded::Builder::new`]: `chunk_capacity = 256`,
    /// `initial_chunks = 0` (lazy growth).
    #[inline]
    pub fn new() -> Self {
        Self {
            inner: crate::unbounded::Builder::new(),
        }
    }

    /// Sets the capacity of each chunk.
    ///
    /// # Panics
    ///
    /// Panics at [`build()`](Self::build) if zero.
    #[inline]
    pub fn chunk_capacity(mut self, cap: usize) -> Self {
        self.inner = self.inner.chunk_capacity(cap);
        self
    }

    /// Sets the number of chunks to pre-allocate.
    ///
    /// Default is 0 (lazy growth — chunks allocated on first use).
    #[inline]
    pub fn initial_chunks(mut self, n: usize) -> Self {
        self.inner = self.inner.initial_chunks(n);
        self
    }

    /// Builds the Rc slab.
    ///
    /// # Safety
    ///
    /// See [`crate::unbounded::Slab`] safety contract.
    ///
    /// # Panics
    ///
    /// Panics if `chunk_capacity` is zero.
    #[inline]
    pub unsafe fn build<T>(self) -> Slab<T> {
        Slab {
            // SAFETY: caller upholds the slab contract.
            inner: unsafe { self.inner.build::<RcCell<T>>() },
            _not_send: PhantomData,
        }
    }
}

impl Default for Builder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alloc_borrow_free() {
        // SAFETY: test slab; single-threaded, all handles freed before drop.
        let slab = unsafe { Slab::with_chunk_capacity(4) };
        let h1 = slab.alloc(42u64);
        let h2 = h1.clone();

        assert_eq!(h1.refcount(), 2);
        {
            let g = h1.borrow();
            assert_eq!(*g, 42);
        }

        slab.free(h2);
        slab.free(h1);
    }

    #[test]
    fn grows_automatically() {
        // SAFETY: test slab; single-threaded, all handles freed before drop.
        let slab = unsafe { Slab::with_chunk_capacity(2) };
        let mut handles = alloc::vec::Vec::new();
        for i in 0..100u64 {
            handles.push(slab.alloc(i));
        }
        for (i, h) in handles.iter().enumerate() {
            let g = h.borrow();
            assert_eq!(*g, i as u64);
        }
        for h in handles {
            slab.free(h);
        }
    }

    // Parity guard (#702): every introspection method on `unbounded::Slab`
    // exists here with the same meaning. If a method is added to the plain
    // slab, add it here and extend this test.
    #[test]
    fn builder_and_introspection_match_plain_unbounded() {
        // SAFETY: test slabs; single-threaded, all handles/slots freed before drop.
        let (rc, plain) = unsafe {
            (
                Builder::new()
                    .chunk_capacity(8)
                    .initial_chunks(2)
                    .build::<u64>(),
                crate::unbounded::Builder::new()
                    .chunk_capacity(8)
                    .initial_chunks(2)
                    .build::<u64>(),
            )
        };
        assert_eq!(rc.chunk_capacity(), plain.chunk_capacity());
        assert_eq!(rc.chunk_count(), plain.chunk_count());
        assert_eq!(rc.capacity(), plain.capacity());
        assert_eq!(rc.capacity(), 16);

        rc.reserve_chunks(4);
        plain.reserve_chunks(4);
        assert_eq!(rc.chunk_count(), 4);
        assert_eq!(rc.chunk_count(), plain.chunk_count());
        assert_eq!(rc.capacity(), plain.capacity());
        rc.reserve_chunks(1); // no-op when already larger
        assert_eq!(rc.chunk_count(), 4);

        let h = rc.alloc(1u64);
        let s = plain.alloc(1u64);
        assert!(rc.contains_ptr(h.as_ptr().cast::<()>().cast_const()));
        assert!(plain.contains_ptr(s.as_ptr().cast::<()>().cast_const()));
        let local = 0u64;
        assert!(!rc.contains_ptr(core::ptr::from_ref(&local).cast::<()>()));
        rc.free(h);
        plain.free(s);
    }

    #[test]
    fn builder_defaults_match_plain() {
        // SAFETY: test slabs; nothing allocated.
        let (rc, plain) = unsafe {
            (
                Builder::default().build::<u8>(),
                crate::unbounded::Builder::default().build::<u8>(),
            )
        };
        assert_eq!(rc.chunk_capacity(), plain.chunk_capacity());
        assert_eq!(rc.chunk_count(), plain.chunk_count());
        assert_eq!(
            rc.chunk_count(),
            0,
            "lazy growth: no chunks until first alloc"
        );
    }

    #[test]
    #[should_panic(expected = "chunk_capacity must be non-zero")]
    fn builder_rejects_zero_chunk_capacity() {
        // SAFETY: test slab; panics before any handle can be allocated.
        let _slab = unsafe { Builder::new().chunk_capacity(0).build::<u64>() };
    }

    #[test]
    fn capacity_tracks_growth() {
        // SAFETY: test slab; single-threaded, all handles freed before drop.
        let slab = unsafe { Slab::with_chunk_capacity(2) };
        assert_eq!(slab.capacity(), 0);
        let a = slab.alloc(1u64);
        assert_eq!((slab.chunk_count(), slab.capacity()), (1, 2));
        let b = slab.alloc(2u64);
        let c = slab.alloc(3u64);
        assert_eq!((slab.chunk_count(), slab.capacity()), (2, 4));
        slab.free(a);
        slab.free(b);
        slab.free(c);
    }
}
