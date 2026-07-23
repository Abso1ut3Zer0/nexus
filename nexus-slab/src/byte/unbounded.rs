//! Growable type-erased byte slab.

use core::marker::PhantomData;
use core::mem;

use crate::shared::SlotCell;

use super::{AlignedBytes, Slot, validate_type};

/// Growable byte slab. Mirrors [`crate::unbounded::Slab`] but stores
/// heterogeneous types in fixed-size byte slots.
///
/// Grows via independent chunks — no copying, no reallocation of
/// existing slots. Pointers remain valid.
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
    inner: crate::unbounded::Slab<AlignedBytes<N>>,
}

impl<const N: usize> Slab<N> {
    /// Creates a new unbounded byte slab with the given chunk capacity.
    ///
    /// # Safety
    ///
    /// See [struct-level safety contract](Self).
    ///
    /// # Panics
    ///
    /// Panics if `chunk_capacity` is zero.
    #[inline]
    pub unsafe fn with_chunk_capacity(chunk_capacity: usize) -> Self {
        // SAFETY: caller upholds the slab contract
        unsafe { Builder::new().chunk_capacity(chunk_capacity).build::<N>() }
    }

    /// Allocates a value. Never fails — grows if needed.
    ///
    /// # Panics
    ///
    /// - Panics if `size_of::<T>() > N`
    /// - Panics if `align_of::<T>() > 8`
    #[inline]
    pub fn alloc<T>(&self, value: T) -> Slot<T> {
        validate_type::<T, N>();

        let (slot_ptr, _chunk_idx) = self.inner.claim_ptr();

        // SAFETY: slot_ptr is a valid, vacant SlotCell<AlignedBytes<N>>.
        // AlignedBytes<N> is repr(C, align(8)), suitable for T (asserted above).
        unsafe {
            let data_ptr = slot_ptr.cast::<T>();
            core::ptr::write(data_ptr, value);
        }

        Slot {
            ptr: slot_ptr.cast::<u8>(),
            _marker: PhantomData,
        }
    }

    /// Reserve a slot without writing. Always succeeds (grows if needed).
    ///
    /// The returned [`super::ByteClaim`] can be written to with `.write(value)`
    /// or `.write_raw(src, size)`. If dropped without writing, the slot
    /// is returned to the freelist.
    #[inline]
    pub fn claim(&self) -> super::ByteClaim<'_> {
        let claim = self.inner.claim();
        let (ptr, chunk_idx) = claim.into_ptr();
        let slab_ptr = core::ptr::from_ref(&self.inner).cast::<u8>();
        // SAFETY: ptr is a valid, vacant slot. chunk_idx identifies the owning chunk.
        // free_raw_impl will return it to the correct chunk's freelist on drop.
        unsafe {
            super::ByteClaim::from_raw_parts(
                ptr.cast::<u8>(),
                slab_ptr,
                free_raw_impl::<N>,
                chunk_idx,
                N,
            )
        }
    }

    /// Free a raw pointer without dropping content.
    ///
    /// # Safety
    ///
    /// `ptr` must point to a slot in this slab.
    #[inline]
    pub unsafe fn free_raw(&self, ptr: *mut u8) {
        // SAFETY: Caller guarantees ptr is a valid slot in this slab.
        unsafe {
            self.inner.free_ptr(ptr.cast());
        }
    }

    /// Free a raw pointer with known chunk index. O(1) — no linear scan.
    ///
    /// # Safety
    ///
    /// - `ptr` must point to a slot in chunk `chunk_idx` of this slab.
    #[inline]
    pub unsafe fn free_raw_in_chunk(&self, ptr: *mut u8, chunk_idx: usize) {
        // SAFETY: Caller guarantees ptr is in chunk chunk_idx of this slab.
        unsafe {
            self.inner.free_ptr_in_chunk(ptr.cast(), chunk_idx);
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
    #[inline]
    pub unsafe fn alloc_raw(&self, src: *const u8, size: usize) -> *mut u8 {
        assert!(size <= N, "raw alloc size {size} exceeds slot size {N}");
        let (slot_ptr, _chunk_idx) = self.inner.claim_ptr();
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
}

// =============================================================================
// Builder
// =============================================================================

/// Builder for [`Slab`].
///
/// Configures chunk capacity and optional pre-allocation before constructing
/// the slab. The const generic `N` (slot size) only appears at the terminal
/// [`build()`](Self::build) call.
///
/// # Example
///
/// ```
/// use nexus_slab::byte::unbounded::Builder;
///
/// // SAFETY: caller guarantees slab contract (see Slab docs)
/// let slab = unsafe {
///     Builder::new()
///         .chunk_capacity(64)
///         .initial_chunks(2)
///         .build::<256>()
/// };
/// let slot = slab.alloc(42u64);
/// assert_eq!(*slot, 42);
/// slab.free(slot);
/// ```
pub struct Builder {
    chunk_capacity: usize,
    initial_chunks: usize,
}

impl Builder {
    /// Creates a new builder with default settings.
    ///
    /// Defaults: `chunk_capacity = 256`, `initial_chunks = 0` (lazy growth).
    #[inline]
    pub fn new() -> Self {
        Self {
            chunk_capacity: 256,
            initial_chunks: 0,
        }
    }

    /// Sets the capacity of each chunk.
    ///
    /// # Panics
    ///
    /// Panics at [`build()`](Self::build) if zero.
    #[inline]
    pub fn chunk_capacity(mut self, cap: usize) -> Self {
        self.chunk_capacity = cap;
        self
    }

    /// Sets the number of chunks to pre-allocate.
    ///
    /// Default is 0 (lazy growth — chunks allocated on first use).
    #[inline]
    pub fn initial_chunks(mut self, n: usize) -> Self {
        self.initial_chunks = n;
        self
    }

    /// Builds the byte slab.
    ///
    /// # Safety
    ///
    /// See [`Slab`] safety contract.
    ///
    /// # Panics
    ///
    /// Panics if `chunk_capacity` is zero.
    #[inline]
    pub unsafe fn build<const N: usize>(self) -> Slab<N> {
        // SAFETY: Caller upholds the slab contract.
        let inner = unsafe {
            crate::unbounded::Builder::new()
                .chunk_capacity(self.chunk_capacity)
                .initial_chunks(self.initial_chunks)
                .build::<AlignedBytes<N>>()
        };
        Slab { inner }
    }
}

impl Default for Builder {
    fn default() -> Self {
        Self::new()
    }
}

impl core::fmt::Debug for Builder {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Builder")
            .field("chunk_capacity", &self.chunk_capacity)
            .field("initial_chunks", &self.initial_chunks)
            .finish()
    }
}

/// Monomorphized free for `ByteClaim::Drop`.
///
/// Uses `free_ptr_in_chunk` for O(1) freelist return — no linear scan.
unsafe fn free_raw_impl<const N: usize>(slab_ptr: *const u8, slot_ptr: *mut u8, chunk_idx: usize) {
    // SAFETY: Caller guarantees slab_ptr points to a live unbounded Slab<AlignedBytes<N>>.
    let slab = unsafe { &*(slab_ptr as *const crate::unbounded::Slab<super::AlignedBytes<N>>) };
    // SAFETY: slot_ptr is within chunk chunk_idx. free_ptr_in_chunk returns it to the freelist.
    unsafe {
        slab.free_ptr_in_chunk(slot_ptr.cast(), chunk_idx);
    }
}

impl<const N: usize> core::fmt::Debug for Slab<N> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("byte::unbounded::Slab")
            .field("slot_size", &N)
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
        let slab: Slab<64> = unsafe { Slab::with_chunk_capacity(256) };
        let ptr = slab.alloc(42u64);
        assert_eq!(*ptr, 42);
        slab.free(ptr);
    }

    #[test]
    fn heterogeneous_types() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab: Slab<128> = unsafe { Slab::with_chunk_capacity(256) };

        let p1 = slab.alloc(42u64);
        let p2 = slab.alloc(String::from("hello"));
        let p3 = slab.alloc([1.0f64; 8]);

        assert_eq!(*p1, 42);
        assert_eq!(&*p2, "hello");
        assert_eq!(p3[0], 1.0);

        slab.free(p3);
        slab.free(p2);
        slab.free(p1);
    }

    #[test]
    fn grows_automatically() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab: Slab<16> = unsafe { Slab::with_chunk_capacity(2) };
        let mut ptrs = alloc::vec::Vec::new();
        for i in 0..100u64 {
            ptrs.push(slab.alloc(i));
        }
        for (i, ptr) in ptrs.iter().enumerate() {
            assert_eq!(**ptr, i as u64);
        }
        for ptr in ptrs {
            slab.free(ptr);
        }
    }

    #[test]
    fn take_returns_value() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab: Slab<64> = unsafe { Slab::with_chunk_capacity(256) };
        let ptr = slab.alloc(String::from("taken"));
        let val = slab.take(ptr);
        assert_eq!(val, "taken");
    }

    // ========================================================================
    // ByteClaim tests
    // ========================================================================

    #[test]
    fn claim_write_typed() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab: Slab<64> = unsafe { Slab::with_chunk_capacity(256) };
        let claim = slab.claim();
        let slot = claim.write(42u64);
        assert_eq!(*slot, 42);
        slab.free(slot);
    }

    #[test]
    fn claim_drop_returns_to_freelist() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab: Slab<64> = unsafe { Slab::with_chunk_capacity(1) };

        // Claim, then abandon.
        let claim = slab.claim();
        drop(claim);

        // Should be able to claim again.
        let claim = slab.claim();
        let slot = claim.write(99u64);
        assert_eq!(*slot, 99);
        slab.free(slot);
    }

    #[test]
    fn claim_write_raw() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab: Slab<64> = unsafe { Slab::with_chunk_capacity(256) };
        let claim = slab.claim();
        let val: u64 = 77;
        // SAFETY: val is on the stack; size_of::<u64>() bytes are initialized.
        let ptr =
            unsafe { claim.write_raw(&raw const val as *const u8, core::mem::size_of::<u64>()) };
        // SAFETY: ptr was written with write_raw above; points to an initialized u64.
        assert_eq!(unsafe { *(ptr as *const u64) }, 77);
        // SAFETY: ptr was obtained from write_raw above; points to an initialized u64 slot.
        let slot = unsafe { super::Slot::<u64>::from_raw(ptr) };
        slab.free(slot);
    }

    // ========================================================================
    // Builder tests
    // ========================================================================

    #[test]
    fn builder_defaults() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab = unsafe { Builder::new().build::<64>() };
        let slot = slab.alloc(42u64);
        assert_eq!(*slot, 42);
        slab.free(slot);
    }

    #[test]
    fn builder_custom_chunk_capacity() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab = unsafe { Builder::new().chunk_capacity(32).build::<64>() };
        let slot = slab.alloc(1u64);
        slab.free(slot);
    }

    #[test]
    fn builder_initial_chunks() {
        // SAFETY: test slab; single-threaded, all slots freed before drop.
        let slab = unsafe {
            Builder::new()
                .chunk_capacity(16)
                .initial_chunks(3)
                .build::<64>()
        };
        // 3 chunks × 16 slots = 48 total capacity via inner slab
        let mut ptrs = alloc::vec::Vec::new();
        for i in 0..48u64 {
            ptrs.push(slab.alloc(i));
        }
        for ptr in ptrs {
            slab.free(ptr);
        }
    }

    #[test]
    #[should_panic(expected = "chunk_capacity must be non-zero")]
    fn builder_zero_chunk_capacity_panics() {
        // SAFETY: test slab; single-threaded; panics before any slot can be allocated.
        let _slab = unsafe { Builder::new().chunk_capacity(0).build::<64>() };
    }
}
