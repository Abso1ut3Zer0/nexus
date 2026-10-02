//! Reference-counted slab allocation with guarded access.
//!
//! Wraps the raw [`bounded`](crate::bounded) and [`unbounded`](crate::unbounded)
//! slabs with reference counting and borrow guards. The inner slab stores
//! `RcCell<T>` (refcount header + value) while the user works with `RcSlot<T>`.
//!
//! Only one borrow at a time — shared or exclusive. Panics if violated.
//! More conservative than `RefCell`.
//!
//! # Example
//!
//! ```
//! use nexus_slab::rc::bounded::Slab;
//!
//! // SAFETY: caller accepts manual memory management contract
//! let slab = unsafe { Slab::<u64>::with_capacity(1024) };
//!
//! let h1 = slab.alloc(42);
//! let h2 = h1.clone();  // refcount 1 → 2
//!
//! {
//!     let val = h1.borrow();
//!     assert_eq!(*val, 42);
//! }
//!
//! {
//!     let mut val = h2.borrow_mut();
//!     *val = 99;
//! }
//!
//! slab.free(h2);  // refcount 2 → 1
//! slab.free(h1);  // refcount 1 → 0, deallocated
//! ```
//!
//! # Pinning
//!
//! `RcSlot` has no pinned form. Pinned-ness would be a whole-slot property
//! across clones (every handle's `borrow_mut()` would have to yield
//! `Pin<RefMut>`), and std's own `Rc::pin` only offers shared `Pin<&T>`.
//! Parked until a caller exists. For `T: Unpin`,
//! `Pin::new(handle.borrow_mut())` is correct. For `!Unpin` values in a
//! slab, use the plain slab's [`PinnedSlot`](crate::PinnedSlot).

pub mod bounded;
pub mod unbounded;

use core::cell::Cell;
use core::fmt;
use core::marker::PhantomData;
use core::mem::ManuallyDrop;
use core::ops::{Deref, DerefMut};

use crate::shared::SlotCell;

// =============================================================================
// RcCell — storage layout for refcounted slots
// =============================================================================

/// Storage for a reference-counted slab slot.
///
/// When vacant: acts as a freelist node (same as `SlotCell`).
/// When occupied: `state` holds refcount + borrow flag, `value` holds `T`.
///
/// # Layout
///
/// ```text
/// ┌─────────────────────────┐
/// │ state: Cell<usize>      │  8 bytes (refcount + borrow bit)
/// ├─────────────────────────┤
/// │ value: ManuallyDrop<T>  │  size_of::<T>() bytes
/// └─────────────────────────┘
/// ```
///
/// The `state` field is at offset 0 in the value region of the `SlotCell`
/// union. When vacant, the `SlotCell::next_free` pointer occupies the
/// same bytes. This works because `next_free` is pointer-sized
/// and `state` is also pointer-sized (`usize`).
#[repr(C)]
pub struct RcCell<T> {
    /// Bit 63: borrow active (1 = someone has a Ref/RefMut guard).
    /// Bits 0-62: reference count.
    state: Cell<usize>,
    /// The value. Inside `UnsafeCell` to allow mutation through shared
    /// references (same pattern as `RefCell`). `ManuallyDrop` because we
    /// manage the lifetime manually (drop when refcount hits 0).
    value: core::cell::UnsafeCell<ManuallyDrop<T>>,
}

/// Borrow flag — bit 63.
const BORROW_BIT: usize = 1 << (usize::BITS - 1);
/// Mask for the reference count (bits 0-62).
const REFCOUNT_MASK: usize = !BORROW_BIT;

impl<T> RcCell<T> {
    /// Creates a new occupied RcCell with refcount 1, no borrow.
    #[inline]
    pub(crate) fn new(value: T) -> Self {
        RcCell {
            state: Cell::new(1),
            value: core::cell::UnsafeCell::new(ManuallyDrop::new(value)),
        }
    }

    /// Extracts the inner value, consuming the cell.
    #[inline]
    pub(crate) fn into_inner(self) -> T {
        ManuallyDrop::into_inner(self.value.into_inner())
    }

    /// Returns the current reference count (without borrow bit).
    #[inline]
    fn refcount(&self) -> usize {
        self.state.get() & REFCOUNT_MASK
    }

    /// Increments the reference count.
    #[inline]
    fn inc_ref(&self) {
        let state = self.state.get();
        debug_assert!(
            (state & REFCOUNT_MASK) < REFCOUNT_MASK,
            "RcSlot refcount overflow"
        );
        self.state.set(state + 1);
    }

    /// Decrements the reference count. Returns the new count.
    #[inline]
    fn dec_ref(&self) -> usize {
        let state = self.state.get();
        let count = state & REFCOUNT_MASK;
        debug_assert!(count > 0, "RcSlot refcount underflow");
        self.state.set((state & BORROW_BIT) | (count - 1));
        count - 1
    }

    /// Sets the borrow bit. Panics if already set.
    #[inline]
    fn acquire_borrow(&self) {
        let state = self.state.get();
        assert!(
            state & BORROW_BIT == 0,
            "RcSlot<{}> already borrowed",
            core::any::type_name::<T>()
        );
        self.state.set(state | BORROW_BIT);
    }

    /// Clears the borrow bit.
    #[inline]
    fn release_borrow(&self) {
        let state = self.state.get();
        debug_assert!(state & BORROW_BIT != 0, "release_borrow without borrow");
        self.state.set(state & REFCOUNT_MASK);
    }

    /// Returns a reference to the value.
    ///
    /// # Safety
    ///
    /// Caller must have acquired the borrow.
    #[inline]
    unsafe fn value_ref(&self) -> &T {
        // SAFETY: UnsafeCell::get() returns *mut ManuallyDrop<T>.
        // Borrow bit guarantees no concurrent mutation.
        unsafe { &*(self.value.get().cast::<T>()) }
    }

    /// Returns a mutable reference to the value.
    ///
    /// # Safety
    ///
    /// Caller must have acquired the borrow exclusively.
    #[inline]
    #[allow(clippy::mut_from_ref)]
    unsafe fn value_mut(&self) -> &mut T {
        // SAFETY: UnsafeCell::get() provides *mut with proper provenance.
        // Borrow bit guarantees exclusive access.
        unsafe { &mut *(self.value.get().cast::<T>()) }
    }

    /// Returns a raw pointer to the value without acquiring a borrow guard.
    ///
    /// This bypasses the borrow-checking mechanism. The returned pointer is
    /// valid as long as the refcount is non-zero (some `RcSlot` exists).
    ///
    /// Returns `*mut T` (not `*const T`) because `UnsafeCell` grants interior
    /// mutability. The caller must ensure no aliasing violations when
    /// dereferencing.
    #[inline]
    pub fn value_ptr(&self) -> *mut T {
        self.value.get().cast::<T>()
    }

    /// Drops the value in place.
    ///
    /// # Safety
    ///
    /// Must only be called once, when refcount hits 0.
    #[inline]
    unsafe fn drop_value(&self) {
        // SAFETY: UnsafeCell::get() provides *mut with write provenance.
        unsafe {
            core::ptr::drop_in_place(self.value.get().cast::<T>());
        }
    }
}

// =============================================================================
// RcSlot<T> — Reference-counted handle
// =============================================================================

/// Reference-counted handle to a slab-allocated value.
///
/// `RcSlot<T>` is `Clone` — cloning increments the refcount. Each clone
/// must be individually returned to the slab via `free_rc()`. The slot
/// is deallocated when the last handle is freed.
///
/// Access is through guards: [`borrow()`](Self::borrow) returns [`Ref<T>`],
/// [`borrow_mut()`](Self::borrow_mut) returns [`RefMut<T>`]. Only one
/// borrow at a time is allowed — panics if violated.
///
/// # Size
///
/// 8 bytes (one pointer).
pub struct RcSlot<T> {
    /// Points to the `RcCell<T>` inside a `SlotCell<RcCell<T>>`.
    ptr: *mut RcCell<T>,
    _marker: PhantomData<T>,
}

impl<T> RcSlot<T> {
    /// Creates an RcSlot from a pointer to an RcCell.
    ///
    /// # Safety
    ///
    /// `ptr` must point to a valid, occupied RcCell<T> within a slab.
    #[inline]
    pub(crate) unsafe fn from_ptr(ptr: *mut RcCell<T>) -> Self {
        RcSlot {
            ptr,
            _marker: PhantomData,
        }
    }

    /// Returns the raw pointer to the underlying RcCell.
    #[inline]
    pub fn as_ptr(&self) -> *mut RcCell<T> {
        self.ptr
    }

    /// Consumes the handle, returning the raw pointer without running Drop
    /// or modifying the refcount. Disarms the debug leak detector.
    ///
    /// Reconstruct via [`from_raw()`](Self::from_raw).
    #[inline]
    pub fn into_raw(self) -> *mut RcCell<T> {
        let ptr = self.ptr;
        core::mem::forget(self);
        ptr
    }

    /// Reconstructs an `RcSlot` from a raw pointer previously obtained
    /// via [`into_raw()`](Self::into_raw).
    ///
    /// # Safety
    ///
    /// `ptr` must be a valid pointer to an occupied `RcCell<T>` with a
    /// non-zero refcount, originally obtained from `into_raw()`.
    #[inline]
    pub unsafe fn from_raw(ptr: *mut RcCell<T>) -> Self {
        RcSlot {
            ptr,
            _marker: PhantomData,
        }
    }

    /// Returns a raw pointer to the value without acquiring a borrow guard.
    ///
    /// This bypasses the borrow-checking mechanism. Returns a read-only
    /// pointer — use [`value_ptr_mut`](Self::value_ptr_mut) for mutation.
    /// Intended for intrusive collection navigation via `Cell`-based link fields.
    ///
    /// The pointer is valid as long as any `RcSlot` for this slot exists
    /// (refcount > 0). Slab memory never moves.
    ///
    /// # Safety
    ///
    /// The caller must ensure no aliasing violations: do not create a `&mut T`
    /// through this pointer while any `Ref` or `RefMut` guard is active,
    /// and vice versa.
    #[inline]
    pub unsafe fn value_ptr(&self) -> *const T {
        // SAFETY: ptr is valid while any RcSlot exists (refcount > 0).
        unsafe { (*self.ptr).value_ptr().cast_const() }
    }

    /// Returns a raw mutable pointer to the value without acquiring a borrow guard.
    ///
    /// # Safety
    ///
    /// Same as [`Self::value_ptr`], plus: the caller must ensure exclusive access
    /// (no other pointers or guards are reading/writing the value).
    #[inline]
    pub unsafe fn value_ptr_mut(&self) -> *mut T {
        // SAFETY: ptr is valid while any RcSlot exists (refcount > 0).
        unsafe { (*self.ptr).value_ptr() }
    }

    /// Returns the current reference count.
    #[inline]
    pub fn refcount(&self) -> usize {
        // SAFETY: ptr is valid while any RcSlot exists (refcount > 0).
        unsafe { (*self.ptr).refcount() }
    }

    /// Borrows the value, returning a guard that provides `&T`.
    ///
    /// # Panics
    ///
    /// Panics if the slot is already borrowed (by any handle, shared or exclusive).
    #[inline]
    pub fn borrow(&self) -> Ref<'_, T> {
        // SAFETY: ptr is valid (refcount > 0). acquire_borrow panics if already borrowed.
        unsafe { (*self.ptr).acquire_borrow() };
        Ref {
            cell: self.ptr,
            _marker: PhantomData,
        }
    }

    /// Borrows the value mutably, returning a guard that provides `&mut T`.
    ///
    /// # Panics
    ///
    /// Panics if the slot is already borrowed (by any handle, shared or exclusive).
    #[inline]
    pub fn borrow_mut(&self) -> RefMut<'_, T> {
        // SAFETY: ptr is valid (refcount > 0). acquire_borrow panics if already borrowed.
        unsafe { (*self.ptr).acquire_borrow() };
        RefMut {
            cell: self.ptr,
            _marker: PhantomData,
        }
    }

    /// Increments the refcount (used by Clone).
    #[inline]
    fn inc_ref(&self) {
        // SAFETY: ptr is valid while any RcSlot exists (refcount > 0).
        unsafe { (*self.ptr).inc_ref() };
    }

    /// Decrements the refcount. Returns the new count.
    /// If 0, the caller must free the slot.
    #[inline]
    pub(crate) fn dec_ref(&self) -> usize {
        // SAFETY: ptr is valid while any RcSlot exists (refcount > 0).
        unsafe { (*self.ptr).dec_ref() }
    }

    /// Drops the value in the cell. Called when refcount hits 0.
    ///
    /// # Safety
    ///
    /// Must only be called once, when refcount is 0.
    #[inline]
    pub(crate) unsafe fn drop_value(&self) {
        // SAFETY: Caller guarantees refcount is 0 and this is the only call.
        unsafe { (*self.ptr).drop_value() };
    }

    /// Returns the SlotCell pointer (for returning to the freelist).
    ///
    /// The RcCell<T> is stored inside a SlotCell<RcCell<T>>. Since SlotCell
    /// is repr(C) and the value field is at offset 0 (union), the pointer
    /// to RcCell<T> IS the pointer to the SlotCell value region.
    #[inline]
    pub(crate) fn slot_cell_ptr(&self) -> *mut SlotCell<RcCell<T>> {
        self.ptr.cast()
    }
}

impl<T> Clone for RcSlot<T> {
    /// Clones the handle, incrementing the reference count.
    ///
    /// The clone must also be freed via `slab.free_rc()`.
    #[inline]
    fn clone(&self) -> Self {
        self.inc_ref();
        RcSlot {
            ptr: self.ptr,
            _marker: PhantomData,
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for RcSlot<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Can't borrow here (might already be borrowed), just show metadata.
        f.debug_struct("RcSlot")
            .field("refcount", &self.refcount())
            .finish()
    }
}

#[cfg(debug_assertions)]
impl<T> Drop for RcSlot<T> {
    fn drop(&mut self) {
        #[cfg(feature = "std")]
        if std::thread::panicking() {
            return;
        }
        panic!(
            "RcSlot<{}> dropped without being freed — call slab.free(handle)",
            core::any::type_name::<T>()
        );
    }
}

// =============================================================================
// Ref<T> — Shared borrow guard
// =============================================================================

/// Guard providing `&T` access to an `RcSlot`-managed value.
///
/// Created by [`RcSlot::borrow()`]. Releases the borrow on drop.
pub struct Ref<'a, T> {
    cell: *mut RcCell<T>,
    _marker: PhantomData<&'a T>,
}

impl<T> Deref for Ref<'_, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        // SAFETY: Borrow bit is set — no concurrent mutation. Cell pointer is valid.
        unsafe { (*self.cell).value_ref() }
    }
}

impl<T> Drop for Ref<'_, T> {
    #[inline]
    fn drop(&mut self) {
        // SAFETY: Borrow bit was set by acquire_borrow when this guard was created.
        unsafe { (*self.cell).release_borrow() };
    }
}

impl<T: fmt::Debug> fmt::Debug for Ref<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Ref").field("value", &**self).finish()
    }
}

// =============================================================================
// RefMut<T> — Exclusive borrow guard
// =============================================================================

/// Guard providing `&mut T` access to an `RcSlot`-managed value.
///
/// Created by [`RcSlot::borrow_mut()`]. Releases the borrow on drop.
pub struct RefMut<'a, T> {
    cell: *mut RcCell<T>,
    _marker: PhantomData<&'a mut T>,
}

impl<T> Deref for RefMut<'_, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        // SAFETY: Borrow bit is set — no concurrent mutation. Cell pointer is valid.
        unsafe { (*self.cell).value_ref() }
    }
}

impl<T> DerefMut for RefMut<'_, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: Borrow bit guarantees exclusive access. Cell pointer is valid.
        unsafe { (*self.cell).value_mut() }
    }
}

impl<T> Drop for RefMut<'_, T> {
    #[inline]
    fn drop(&mut self) {
        // SAFETY: Borrow bit was set by acquire_borrow when this guard was created.
        unsafe { (*self.cell).release_borrow() };
    }
}

impl<T: fmt::Debug> fmt::Debug for RefMut<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RefMut").field("value", &**self).finish()
    }
}
