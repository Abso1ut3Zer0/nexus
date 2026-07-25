//! Fixed-capacity reference-counted slab.

use super::{RcCell, RcSlot};
use crate::shared::Full;

/// Fixed-capacity slab with reference-counted handles.
///
/// Wraps [`crate::bounded::Slab`] with `RcCell<T>` storage. The user
/// works with `RcSlot<T>` — the refcount header is invisible.
///
/// # Contract
///
/// Same as [`crate::bounded::Slab`]: construction is `unsafe`, the
/// caller accepts manual memory management. Every `RcSlot` must be
/// freed via [`free()`](Self::free). The slot is deallocated when the
/// last handle is freed.
pub struct Slab<T> {
    inner: crate::bounded::Slab<RcCell<T>>,
}

impl<T> Slab<T> {
    /// Creates a new Rc slab with the given capacity.
    ///
    /// # Safety
    ///
    /// See [`crate::bounded::Slab`] safety contract.
    #[inline]
    pub unsafe fn with_capacity(capacity: usize) -> Self {
        Self {
            // SAFETY: Caller upholds the slab contract.
            inner: unsafe { crate::bounded::Slab::with_capacity(capacity) },
        }
    }

    /// Allocates a value, returning an `RcSlot` with refcount 1.
    ///
    /// # Panics
    ///
    /// Panics if the slab is full.
    #[inline]
    pub fn alloc(&self, value: T) -> RcSlot<T> {
        let slot = self.inner.alloc(RcCell::new(value));
        // SAFETY: slot is valid and occupied with RcCell<T>. into_raw disarms
        // the Slot leak detector. The cast is sound because SlotCell value is
        // at offset 0 (repr(C) union), so *mut SlotCell<RcCell<T>> == *mut RcCell<T>.
        unsafe { RcSlot::from_ptr(slot.into_raw().cast()) }
    }

    /// Tries to allocate. Returns `Err(Full(value))` if full.
    #[inline]
    pub fn try_alloc(&self, value: T) -> Result<RcSlot<T>, Full<T>> {
        match self.inner.try_alloc(RcCell::new(value)) {
            // SAFETY: Same as alloc — slot is valid, occupied, cast is sound.
            Ok(slot) => Ok(unsafe { RcSlot::from_ptr(slot.into_raw().cast()) }),
            Err(Full(rc_cell)) => Err(Full(rc_cell.into_inner())),
        }
    }

    /// Frees a handle. Decrements refcount; deallocates on last free.
    ///
    /// Consumes the handle — cannot be used after.
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

    /// Returns the capacity.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }
}

impl<T> core::fmt::Debug for Slab<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("rc::bounded::Slab")
            .field("capacity", &self.capacity())
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alloc_borrow_free() {
        // SAFETY: test slab; single-threaded, all handles freed before drop.
        let slab = unsafe { Slab::with_capacity(10) };
        let handle = slab.alloc(42u64);

        assert_eq!(handle.refcount(), 1);
        {
            let guard = handle.borrow();
            assert_eq!(*guard, 42);
        }
        slab.free(handle);
    }

    #[test]
    fn clone_and_free_both() {
        // SAFETY: test slab; single-threaded, all handles freed before drop.
        let slab = unsafe { Slab::with_capacity(10) };
        let h1 = slab.alloc(42u64);
        let h2 = h1.clone();

        assert_eq!(h1.refcount(), 2);
        slab.free(h2);
        assert_eq!(h1.refcount(), 1);
        slab.free(h1);
    }

    #[test]
    fn borrow_and_borrow_mut() {
        // SAFETY: test slab; single-threaded, all handles freed before drop.
        let slab = unsafe { Slab::with_capacity(10) };
        let handle = slab.alloc(String::from("hello"));

        {
            let guard = handle.borrow();
            assert_eq!(&*guard, "hello");
        }
        {
            let mut guard = handle.borrow_mut();
            guard.push_str(" world");
        }
        {
            let guard = handle.borrow();
            assert_eq!(&*guard, "hello world");
        }
        slab.free(handle);
    }

    #[test]
    fn mutation_visible_across_clones() {
        // SAFETY: test slab; single-threaded, all handles freed before drop.
        let slab = unsafe { Slab::with_capacity(10) };
        let h1 = slab.alloc(1u64);
        let h2 = h1.clone();

        {
            let mut g = h1.borrow_mut();
            *g = 99;
        }
        {
            let g = h2.borrow();
            assert_eq!(*g, 99);
        }

        slab.free(h2);
        slab.free(h1);
    }

    #[test]
    #[should_panic(expected = "already borrowed")]
    fn double_borrow_panics() {
        // SAFETY: test slab; single-threaded, all handles freed before drop.
        let slab = unsafe { Slab::with_capacity(10) };
        let h1 = slab.alloc(42u64);
        let h2 = h1.clone();

        let _g1 = h1.borrow();
        let _g2 = h2.borrow();
    }

    #[test]
    #[should_panic(expected = "already borrowed")]
    fn borrow_while_mut_panics() {
        // SAFETY: test slab; single-threaded, all handles freed before drop.
        let slab = unsafe { Slab::with_capacity(10) };
        let h1 = slab.alloc(42u64);
        let h2 = h1.clone();

        let _g1 = h1.borrow_mut();
        let _g2 = h2.borrow();
    }

    #[test]
    fn try_alloc_full() {
        // SAFETY: test slab; single-threaded, all handles freed before drop.
        let slab = unsafe { Slab::with_capacity(1) };
        let h1 = slab.alloc(1u64);

        let result = slab.try_alloc(2u64);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().0, 2);

        slab.free(h1);
    }

    #[test]
    fn drop_tracking() {
        use core::cell::Cell;

        struct DropCounter<'a> {
            count: &'a Cell<u32>,
        }
        impl Drop for DropCounter<'_> {
            fn drop(&mut self) {
                self.count.set(self.count.get() + 1);
            }
        }

        let drops = Cell::new(0);
        // SAFETY: test slab; single-threaded, all handles freed before drop.
        let slab = unsafe { Slab::with_capacity(10) };

        let h1 = slab.alloc(DropCounter { count: &drops });
        let h2 = h1.clone();

        slab.free(h2);
        assert_eq!(drops.get(), 0);

        slab.free(h1);
        assert_eq!(drops.get(), 1);
    }

    #[test]
    #[should_panic(expected = "already borrowed")]
    fn mut_while_borrow_panics() {
        // SAFETY: test slab; single-threaded, all handles freed before drop.
        let slab = unsafe { Slab::with_capacity(10) };
        let h1 = slab.alloc(42u64);
        let h2 = h1.clone();

        let _g1 = h1.borrow();
        let _g2 = h2.borrow_mut(); // panics
    }

    #[test]
    fn pin_and_pin_mut() {
        // SAFETY: test slab; single-threaded, all handles freed before drop.
        let slab = unsafe { Slab::with_capacity(10) };
        let handle = slab.alloc(42u64);

        {
            let pinned = handle.pin();
            assert_eq!(*pinned, 42);
        }
        {
            let mut pinned = handle.pin_mut();
            *pinned = 99;
        }
        {
            let g = handle.borrow();
            assert_eq!(*g, 99);
        }
        slab.free(handle);
    }

    #[test]
    fn into_raw_from_raw_roundtrip() {
        // SAFETY: test slab; single-threaded, all handles freed before drop.
        let slab = unsafe { Slab::with_capacity(10) };
        let handle = slab.alloc(42u64);

        let raw = handle.into_raw();
        // SAFETY: raw was obtained from into_raw() just above; refcount is still non-zero.
        let handle = unsafe { crate::RcSlot::from_raw(raw) };

        {
            let g = handle.borrow();
            assert_eq!(*g, 42);
        }
        slab.free(handle);
    }

    #[test]
    fn freelist_integrity_after_rc_cycle() {
        // SAFETY: test slab; single-threaded, all handles freed before drop.
        let slab = unsafe { Slab::with_capacity(4) };

        // Fill
        let h1 = slab.alloc(1u64);
        let h2 = slab.alloc(2u64);
        let h3 = slab.alloc(3u64);
        let h4 = slab.alloc(4u64);
        assert!(slab.try_alloc(5u64).is_err());

        // Free all
        slab.free(h4);
        slab.free(h3);
        slab.free(h2);
        slab.free(h1);

        // Realloc — verify freelist is intact
        let h1 = slab.alloc(10u64);
        let h2 = slab.alloc(20u64);
        let h3 = slab.alloc(30u64);
        let h4 = slab.alloc(40u64);

        {
            assert_eq!(*h1.borrow(), 10);
        }
        {
            assert_eq!(*h2.borrow(), 20);
        }
        {
            assert_eq!(*h3.borrow(), 30);
        }
        {
            assert_eq!(*h4.borrow(), 40);
        }

        slab.free(h4);
        slab.free(h3);
        slab.free(h2);
        slab.free(h1);
    }

    #[cfg(debug_assertions)]
    #[test]
    fn debug_drop_panics() {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            // SAFETY: test slab; handle intentionally not freed (tests debug drop panic).
            let slab = unsafe { Slab::with_capacity(10) };
            let _h = slab.alloc(42u64);
        }));
        assert!(result.is_err());
    }
}
