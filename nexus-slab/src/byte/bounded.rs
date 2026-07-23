//! Fixed-capacity type-erased byte slab.

use core::marker::PhantomData;
use core::mem;

use crate::shared::{Full, SlotCell};

use super::{AlignedBytes, Slot, validate_type};

/// Fixed-capacity byte slab. Mirrors [`crate::bounded::Slab`] but stores
/// heterogeneous types in fixed-size byte slots.
///
/// # Safety Contract
///
/// Construction is `unsafe` because it opts you into manual memory
/// management. By creating a slab, you accept these invariants:
///
/// - **Free from the correct slab.** Passing a [`Slot`] to a different
///   slab's `free()` is undefined behavior — it corrupts the freelist.
///   In debug builds, this is caught by `debug_assert!`.
/// - **Free everything you allocate.** Dropping the slab does NOT drop
///   values in occupied slots. Unfreed slots leak silently.
/// - **Single-threaded.** The slab is `!Send` and `!Sync`.
///
/// ## Why `free()` is safe
///
/// The safety contract is accepted once, at construction. After that:
/// - [`Slot`] is move-only (no `Copy`, no `Clone`) — double-free is
///   prevented by the type system.
/// - `free()` consumes the `Slot` — the handle cannot be used after.
/// - Cross-slab misuse is the only remaining hazard, and it was
///   accepted as the caller's responsibility at construction time.
pub struct Slab<const N: usize> {
    inner: crate::bounded::Slab<AlignedBytes<N>>,
}

impl<const N: usize> Slab<N> {
    /// Creates a byte slab with the given capacity.
    ///
    /// # Safety
    ///
    /// See [`crate::bounded::Slab`] safety contract.
    ///
    /// # Panics
    ///
    /// Panics if capacity is zero.
    #[inline]
    pub unsafe fn with_capacity(capacity: usize) -> Self {
        Self {
            // SAFETY: caller upholds the slab contract
            inner: unsafe { crate::bounded::Slab::with_capacity(capacity) },
        }
    }

    /// Allocates a value in the byte slab.
    ///
    /// # Panics
    ///
    /// - Panics if `size_of::<T>() > N`
    /// - Panics if `align_of::<T>() > 8`
    /// - Panics if the slab is full
    #[inline]
    pub fn alloc<T>(&self, value: T) -> Slot<T> {
        self.try_alloc(value)
            .unwrap_or_else(|_| panic!("byte slab full"))
    }

    /// Tries to allocate a value. Returns `Err(Full(value))` if full.
    ///
    /// # Panics
    ///
    /// - Panics if `size_of::<T>() > N`
    /// - Panics if `align_of::<T>() > 8`
    pub fn try_alloc<T>(&self, value: T) -> Result<Slot<T>, Full<T>> {
        validate_type::<T, N>();

        let Some(slot_ptr) = self.inner.claim_ptr() else {
            return Err(Full(value));
        };

        // SAFETY: slot_ptr is a valid, vacant SlotCell<AlignedBytes<N>>.
        // AlignedBytes<N> is repr(C, align(8)) so the value region is
        // suitably aligned for T (asserted above: align <= 8).
        unsafe {
            let data_ptr = slot_ptr.cast::<T>();
            core::ptr::write(data_ptr, value);
        }

        Ok(Slot {
            ptr: slot_ptr.cast::<u8>(),
            _marker: PhantomData,
        })
    }

    /// Try to reserve a slot without writing. Returns `None` if full.
    ///
    /// The returned [`super::ByteClaim`] can be written to with `.write(value)`
    /// or `.write_raw(src, size)`. If dropped without writing, the slot
    /// is returned to the freelist.
    #[inline]
    pub fn try_claim(&self) -> Option<super::ByteClaim<'_>> {
        let claim = self.inner.claim()?;
        let ptr = claim.into_ptr().cast::<u8>();
        let slab_ptr = core::ptr::from_ref(&self.inner).cast::<u8>();
        // SAFETY: ptr is a valid vacant slot. Bounded = single chunk (idx 0).
        Some(unsafe { super::ByteClaim::from_raw_parts(ptr, slab_ptr, free_raw_impl::<N>, 0, N) })
    }

    /// Reserve a slot without writing. Panics if full.
    #[inline]
    pub fn claim(&self) -> super::ByteClaim<'_> {
        self.try_claim().expect("byte slab full")
    }

    /// Free a raw pointer without dropping content.
    ///
    /// # Safety
    ///
    /// `ptr` must point to a slot in this slab (claimed or allocated).
    #[inline]
    pub unsafe fn free_raw(&self, ptr: *mut u8) {
        // SAFETY: Caller guarantees ptr is a valid slot in this slab.
        unsafe {
            self.inner.free_ptr(ptr.cast());
        }
    }

    /// Claim a slot and copy raw bytes into it. Returns a raw pointer.
    ///
    /// # Safety
    ///
    /// - `src` must point to `size` valid bytes.
    /// - `size` must be <= `N`.
    ///
    /// # Panics
    ///
    /// - Panics if `size > N`.
    /// - Panics if the slab is full.
    #[inline]
    pub unsafe fn alloc_raw(&self, src: *const u8, size: usize) -> *mut u8 {
        assert!(size <= N, "raw alloc size {size} exceeds slot size {N}");
        let slot_ptr = self
            .inner
            .claim_ptr()
            .unwrap_or_else(|| panic!("byte slab full"));
        let dst = slot_ptr.cast::<u8>();
        // SAFETY: dst is a valid vacant slot. Caller guarantees src has `size` valid bytes.
        unsafe { core::ptr::copy_nonoverlapping(src, dst, size) };
        dst
    }

    /// Frees a value, dropping it and returning the slot to the freelist.
    ///
    /// Consumes the handle — the slot cannot be used after this call.
    #[inline]
    pub fn free<T>(&self, ptr: Slot<T>) {
        let data_ptr = ptr.ptr;
        debug_assert!(
            self.inner.contains_ptr(data_ptr as *const ()),
            "slot was not allocated from this slab"
        );
        mem::forget(ptr);

        // SAFETY: Slot handle guarantees data_ptr is valid and occupied with a T.
        // forget(ptr) disarms the debug leak detector. free_ptr returns the slot
        // to the freelist after the value is dropped.
        unsafe {
            core::ptr::drop_in_place(data_ptr.cast::<T>());
            self.inner
                .free_ptr(data_ptr.cast::<SlotCell<AlignedBytes<N>>>());
        }
    }

    /// Takes the value out without dropping it, freeing the slot.
    ///
    /// Consumes the handle — the slot cannot be used after this call.
    #[inline]
    pub fn take<T>(&self, ptr: Slot<T>) -> T {
        let data_ptr = ptr.ptr;
        debug_assert!(
            self.inner.contains_ptr(data_ptr as *const ()),
            "slot was not allocated from this slab"
        );
        mem::forget(ptr);

        // SAFETY: Slot handle guarantees data_ptr is valid and occupied with a T.
        // read moves the value out, then free_ptr returns the slot to the freelist.
        unsafe {
            let value = core::ptr::read(data_ptr.cast::<T>());
            self.inner
                .free_ptr(data_ptr.cast::<SlotCell<AlignedBytes<N>>>());
            value
        }
    }

    /// Returns the capacity.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }
}

/// Monomorphized free function for `ByteClaim::Drop`.
///
/// Casts the slab pointer back to the correct bounded `Slab<AlignedBytes<N>>`
/// and returns the slot to its freelist. `AlignedBytes<N>` is `Copy` so
/// `drop_in_place` is a no-op — safe for vacant (unwritten) slots.
///
/// # Safety
///
/// - `slab_ptr` must point to a live `crate::bounded::Slab<AlignedBytes<N>>`.
/// - `slot_ptr` must point to a slot within that slab.
unsafe fn free_raw_impl<const N: usize>(slab_ptr: *const u8, slot_ptr: *mut u8, _chunk_idx: usize) {
    // SAFETY: Caller guarantees slab_ptr points to a live bounded Slab<AlignedBytes<N>>.
    let slab = unsafe { &*(slab_ptr as *const crate::bounded::Slab<super::AlignedBytes<N>>) };
    // SAFETY: Bounded slab has one chunk — chunk_idx is ignored.
    // free_ptr returns the slot to the freelist. For vacant slots
    // (ByteClaim abandoned without writing), no value needs dropping.
    unsafe {
        slab.free_ptr(slot_ptr.cast());
    }
}

impl<const N: usize> core::fmt::Debug for Slab<N> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("byte::bounded::Slab")
            .field("slot_size", &N)
            .field("capacity", &self.capacity())
            .finish()
    }
}

#[cfg(test)]
#[allow(clippy::float_cmp)]
mod tests {
    use super::*;

    #[test]
    fn basic_alloc_free() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab: Slab<128> = unsafe { Slab::with_capacity(10) };
        let ptr = slab.alloc(42u64);
        assert_eq!(*ptr, 42);
        slab.free(ptr);
    }

    #[test]
    fn heterogeneous_types() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab: Slab<128> = unsafe { Slab::with_capacity(10) };

        let p1 = slab.alloc(42u64);
        let p2 = slab.alloc([1.0f64; 4]);
        let p3 = slab.alloc(String::from("hello"));

        assert_eq!(*p1, 42);
        assert_eq!(p2[0], 1.0);
        assert_eq!(&*p3, "hello");

        slab.free(p3);
        slab.free(p2);
        slab.free(p1);
    }

    #[test]
    fn take_returns_value() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab: Slab<64> = unsafe { Slab::with_capacity(10) };
        let ptr = slab.alloc(String::from("owned"));
        let val = slab.take(ptr);
        assert_eq!(val, "owned");
    }

    #[test]
    fn full_returns_error() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab: Slab<64> = unsafe { Slab::with_capacity(1) };
        let p1 = slab.alloc(1u64);
        let result = slab.try_alloc(2u64);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().0, 2);
        slab.free(p1);
    }

    #[test]
    #[should_panic(expected = "exceeds byte slab slot size")]
    fn rejects_oversized_type() {
        // SAFETY: test slab; single-threaded; panics before allocation on type mismatch.
        let slab: Slab<8> = unsafe { Slab::with_capacity(1) };
        let _p = slab.alloc([0u64; 2]);
    }

    #[test]
    fn deref_mut() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab: Slab<64> = unsafe { Slab::with_capacity(10) };
        let mut ptr = slab.alloc(String::from("hello"));
        ptr.push_str(" world");
        assert_eq!(&*ptr, "hello world");
        slab.free(ptr);
    }

    #[test]
    fn reuse_after_free() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab: Slab<64> = unsafe { Slab::with_capacity(1) };
        let ptr = slab.alloc(1u64);
        slab.free(ptr);
        let ptr = slab.alloc(2u64);
        assert_eq!(*ptr, 2);
        slab.free(ptr);
    }

    #[cfg(debug_assertions)]
    #[test]
    fn debug_drop_panics() {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            // SAFETY: test slab; slot intentionally not freed (tests debug drop panic).
            let slab: Slab<64> = unsafe { Slab::with_capacity(10) };
            let _ptr = slab.alloc(42u64);
        }));
        assert!(result.is_err());
    }

    // ========================================================================
    // ByteClaim tests
    // ========================================================================

    #[test]
    fn claim_write_typed() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab: Slab<64> = unsafe { Slab::with_capacity(4) };
        let claim = slab.claim();
        let slot = claim.write(42u64);
        assert_eq!(*slot, 42);
        slab.free(slot);
    }

    #[test]
    fn claim_write_raw() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab: Slab<64> = unsafe { Slab::with_capacity(4) };
        let claim = slab.claim();
        let val: u64 = 99;
        // SAFETY: val is on the stack; size_of::<u64>() bytes are initialized.
        let ptr =
            unsafe { claim.write_raw(&raw const val as *const u8, core::mem::size_of::<u64>()) };
        // SAFETY: ptr was written with write_raw above; points to an initialized u64.
        assert_eq!(unsafe { *(ptr as *const u64) }, 99);
        // SAFETY: ptr was obtained from write_raw above; points to an initialized u64 slot.
        let slot = unsafe { super::Slot::<u64>::from_raw(ptr) };
        slab.free(slot);
    }

    #[test]
    fn claim_drop_returns_to_freelist() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab: Slab<64> = unsafe { Slab::with_capacity(1) };

        // Claim the only slot, then drop without writing.
        let claim = slab.claim();
        drop(claim);

        // Slot should be back — we can claim again.
        let claim = slab.claim();
        let slot = claim.write(7u64);
        assert_eq!(*slot, 7);
        slab.free(slot);
    }

    #[test]
    fn try_claim_returns_none_when_full() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab: Slab<64> = unsafe { Slab::with_capacity(1) };
        let _held = slab.claim();

        assert!(slab.try_claim().is_none());
    }

    #[test]
    fn try_claim_succeeds_after_abandon() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab: Slab<64> = unsafe { Slab::with_capacity(1) };

        let claim = slab.claim();
        drop(claim); // abandon → returns to freelist

        let claim2 = slab.try_claim();
        assert!(claim2.is_some());
        let slot = claim2.unwrap().write(42u64);
        slab.free(slot);
    }
}
