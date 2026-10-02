//! Shared internals for bounded and unbounded slab implementations.

use core::borrow::{Borrow, BorrowMut};
use core::fmt;
use core::mem::{ManuallyDrop, MaybeUninit};
use core::ops::{Deref, DerefMut};
use core::pin::Pin;

// =============================================================================
// Full<T>
// =============================================================================

/// Error returned when a bounded allocator is full.
///
/// Contains the value that could not be allocated, allowing recovery.
pub struct Full<T>(pub T);

impl<T> Full<T> {
    /// Consumes the error, returning the value that could not be allocated.
    #[inline]
    pub fn into_inner(self) -> T {
        self.0
    }
}

impl<T> fmt::Debug for Full<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Full(..)")
    }
}

impl<T> fmt::Display for Full<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("allocator full")
    }
}

#[cfg(feature = "std")]
impl<T> std::error::Error for Full<T> {}

// =============================================================================
// SlotCell
// =============================================================================

/// SLUB-style slot: freelist pointer overlaid on value storage.
///
/// When vacant: `next_free` is active — points to next free slot (or null).
/// When occupied: `value` is active — contains the user's `T`.
///
/// These fields occupy the SAME bytes. Writing `value` overwrites `next_free`
/// and vice versa. There is no header, no tag, no sentinel: a live [`Slot`]
/// handle is the proof of occupancy. (`Slot` is a raw handle, not RAII; the
/// caller frees it explicitly.)
///
/// Size: `max(8, size_of::<T>())`.
#[repr(C)]
pub union SlotCell<T> {
    next_free: *mut SlotCell<T>,
    value: ManuallyDrop<MaybeUninit<T>>,
}

impl<T> SlotCell<T> {
    /// Creates a new vacant slot with the given next_free pointer.
    #[inline]
    pub(crate) fn vacant(next_free: *mut SlotCell<T>) -> Self {
        SlotCell { next_free }
    }

    /// Writes a value into this slot, transitioning it from vacant to occupied.
    ///
    /// # Safety
    ///
    /// The slot must be vacant (no live value present).
    #[inline]
    pub(crate) unsafe fn write_value(&mut self, value: T) {
        self.value = ManuallyDrop::new(MaybeUninit::new(value));
    }

    /// Reads the value out of this slot without dropping it.
    ///
    /// # Safety
    ///
    /// The slot must be occupied with a valid `T`.
    /// After this call, the caller owns the value and the slot must not be
    /// read again without a subsequent write.
    #[inline]
    pub(crate) unsafe fn read_value(&self) -> T {
        // SAFETY: Caller guarantees the slot is occupied.
        unsafe { core::ptr::read(self.value.as_ptr()) }
    }

    /// Drops the value in place without returning it.
    ///
    /// # Safety
    ///
    /// The slot must be occupied with a valid `T`.
    #[inline]
    pub(crate) unsafe fn drop_value_in_place(&mut self) {
        // SAFETY: Caller guarantees the slot is occupied.
        unsafe {
            core::ptr::drop_in_place((*self.value).as_mut_ptr());
        }
    }

    /// Returns a reference to the occupied value.
    ///
    /// # Safety
    ///
    /// The slot must be occupied with a valid `T`.
    #[inline]
    pub unsafe fn value_ref(&self) -> &T {
        // SAFETY: Caller guarantees the slot is occupied.
        unsafe { self.value.assume_init_ref() }
    }

    /// Returns a mutable reference to the occupied value.
    ///
    /// # Safety
    ///
    /// The slot must be occupied with a valid `T`.
    /// Caller must have exclusive access.
    #[inline]
    pub unsafe fn value_mut(&mut self) -> &mut T {
        // SAFETY: Caller guarantees the slot is occupied.
        unsafe { (*self.value).assume_init_mut() }
    }

    /// Returns a raw const pointer to the value storage.
    ///
    /// # Safety
    ///
    /// The slot must be occupied.
    #[inline]
    pub unsafe fn value_ptr(&self) -> *const T {
        // SAFETY: Caller guarantees the slot is occupied.
        unsafe { self.value.as_ptr() }
    }

    /// Returns a raw mutable pointer to the value storage from a raw pointer.
    ///
    /// This avoids creating an intermediate `&SlotCell<T>` reference, which
    /// would give the result read-only provenance under stacked borrows.
    /// Use this when you need `*mut T` from a `*mut SlotCell<T>`.
    ///
    /// # Safety
    ///
    /// `ptr` must be non-null and point to an occupied `SlotCell<T>`.
    #[inline]
    pub unsafe fn value_ptr_mut(ptr: *mut SlotCell<T>) -> *mut T {
        // SAFETY: SlotCell is repr(C) and value is ManuallyDrop<MaybeUninit<T>>.
        // ManuallyDrop is repr(transparent), MaybeUninit is repr(transparent)
        // for the value. The value field is at offset 0 (repr(C) union).
        // We cast through the raw pointer without creating a reference,
        // preserving write provenance.
        ptr.cast::<T>()
    }

    /// Returns the next_free pointer.
    ///
    /// # Safety
    ///
    /// The slot must be vacant.
    #[inline]
    pub(crate) unsafe fn get_next_free(&self) -> *mut SlotCell<T> {
        // SAFETY: Caller guarantees the slot is vacant.
        unsafe { self.next_free }
    }

    /// Sets the next_free pointer.
    ///
    /// # Safety
    ///
    /// Caller must be transitioning this slot to vacant.
    #[inline]
    pub(crate) unsafe fn set_next_free(&mut self, next: *mut SlotCell<T>) {
        self.next_free = next;
    }
}

// =============================================================================
// Slot<T> — Raw Pointer Wrapper
// =============================================================================

/// Raw slot handle — pointer wrapper, NOT RAII.
///
/// `Slot<T>` is a thin wrapper around a pointer to a [`SlotCell<T>`]. It is
/// analogous to `malloc` returning a pointer: the caller owns the memory and
/// must explicitly free it via [`Slab::free()`](crate::bounded::Slab::free).
///
/// # Size
///
/// 8 bytes (one pointer).
///
/// # Thread Safety
///
/// `Slot` is `!Send` and `!Sync`. It must only be used from the thread that
/// created it. This is what lets the slab itself be `Send`: a handle can
/// never follow the slab to another thread.
///
/// ```compile_fail,E0277
/// fn assert_send<T: Send>() {}
/// assert_send::<nexus_slab::Slot<u64>>();
/// ```
///
/// # Debug-Mode Leak Detection
///
/// In debug builds, dropping a `Slot` without calling `free()` or
/// `take()` panics. Use [`into_raw()`](Self::into_raw) to extract the
/// pointer and disarm the detector. In release builds there is no `Drop`
/// impl — forgetting to call `free()` silently leaks the slot.
///
/// # Borrow Traits
///
/// `Slot<T>` implements `Borrow<T>` and `BorrowMut<T>`, enabling use as
/// HashMap keys that borrow `T` for lookups.
#[repr(transparent)]
pub struct Slot<T>(*mut SlotCell<T>);

impl<T> Slot<T> {
    /// Internal construction from a raw pointer.
    ///
    /// # Safety
    ///
    /// `ptr` must be a valid pointer to an occupied `SlotCell<T>` within a slab.
    #[inline]
    pub(crate) unsafe fn from_ptr(ptr: *mut SlotCell<T>) -> Self {
        Slot(ptr)
    }

    /// Returns the raw pointer to the slot cell.
    #[inline]
    pub fn as_ptr(&self) -> *mut SlotCell<T> {
        self.0
    }

    /// Consumes the handle, returning the raw pointer without running Drop.
    ///
    /// The caller is responsible for the slot from this point — either
    /// reconstruct via [`from_raw()`](Self::from_raw) or manage manually.
    /// Disarms the debug-mode leak detector.
    #[inline]
    pub fn into_raw(self) -> *mut SlotCell<T> {
        let ptr = self.0;
        core::mem::forget(self);
        ptr
    }

    /// Reconstructs a `Slot` from a raw pointer previously obtained
    /// via [`into_raw()`](Self::into_raw).
    ///
    /// # Safety
    ///
    /// `ptr` must be a valid pointer to an occupied `SlotCell<T>` within
    /// a slab, originally obtained from `into_raw()` on this type.
    #[inline]
    pub unsafe fn from_raw(ptr: *mut SlotCell<T>) -> Self {
        Slot(ptr)
    }

    /// Creates a duplicate pointer to the same slot.
    ///
    /// # Safety
    ///
    /// Caller must ensure the slot is not freed while any clone exists.
    /// Intended for refcounting wrappers (e.g., nexus-collections' RcHandle).
    #[inline]
    pub unsafe fn clone_ptr(&self) -> Self {
        Slot(self.0)
    }

    /// Pins the value for the rest of its life, consuming this handle.
    ///
    /// The returned [`PinnedSlot`] hands out `Pin<&T>` and `Pin<&mut T>` and
    /// nothing that could move the value: no `DerefMut`, no `BorrowMut`, no
    /// `take`. The only way out is
    /// [`Slab::free_pinned`](crate::bounded::Slab::free_pinned), which drops
    /// the value in place. This is the sound way to keep a `!Unpin` value (a
    /// future, a self-referential struct) in a slab.
    ///
    /// For `T: Unpin` no helper is needed; `Pin::new(&mut *slot)` is correct.
    ///
    /// The pinned slot must be freed with `free_pinned` before the slab is
    /// dropped; see [`PinnedSlot`] for why that is a soundness requirement.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_slab::bounded::Slab;
    ///
    /// // SAFETY: caller guarantees slab contract (see struct docs)
    /// let slab = unsafe { Slab::with_capacity(4) };
    /// let mut pinned = slab.alloc(41u64).into_pinned();
    /// *pinned.as_mut() += 1;
    /// assert_eq!(*pinned, 42);
    /// slab.free_pinned(pinned);
    /// ```
    #[inline]
    pub fn into_pinned(self) -> PinnedSlot<T> {
        PinnedSlot(self.into_raw())
    }
}

impl<T> Deref for Slot<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        // SAFETY: Slot was created from a valid, occupied SlotCell.
        unsafe { (*self.0).value_ref() }
    }
}

impl<T> DerefMut for Slot<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: We have &mut self, guaranteeing exclusive access.
        unsafe { (*self.0).value_mut() }
    }
}

impl<T> AsRef<T> for Slot<T> {
    #[inline]
    fn as_ref(&self) -> &T {
        self
    }
}

impl<T> AsMut<T> for Slot<T> {
    #[inline]
    fn as_mut(&mut self) -> &mut T {
        self
    }
}

impl<T> Borrow<T> for Slot<T> {
    #[inline]
    fn borrow(&self) -> &T {
        self
    }
}

impl<T> BorrowMut<T> for Slot<T> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut T {
        self
    }
}

// Slot is intentionally NOT Clone/Copy.
// Move-only semantics prevent double-free at compile time.

impl<T: fmt::Debug> fmt::Debug for Slot<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Slot").field("value", &**self).finish()
    }
}

#[cfg(debug_assertions)]
impl<T> Drop for Slot<T> {
    fn drop(&mut self) {
        #[cfg(feature = "std")]
        if std::thread::panicking() {
            return; // Don't double-panic during unwind
        }
        panic!(
            "Slot<{}> dropped without being freed — call slab.free(slot) or slab.take(slot)",
            core::any::type_name::<T>()
        );
    }
}

// =============================================================================
// PinnedSlot<T> — pinned raw slot handle
// =============================================================================

/// A slot whose value is pinned for the rest of its life.
///
/// Made from a [`Slot`] by [`Slot::into_pinned`], which consumes the only
/// handle that could move the value. From then on nothing can move it out:
/// there is no `DerefMut`, no `BorrowMut`, no `take`. The slab drops it in
/// place via [`Slab::free_pinned`](crate::bounded::Slab::free_pinned). This
/// is the `Box::into_pin` analogue for slab storage.
///
/// # Guarantees
///
/// - The address is stable: slab storage never moves.
/// - The value is never moved out before `free_pinned` drops it in place.
/// - Debug-mode leak detection, same as [`Slot`].
///
/// # Lifetime
///
/// Calling `free_pinned` before the slab drops is a soundness requirement,
/// not hygiene. Forgetting this handle and dropping the slab frees the
/// storage without running the destructor, which is exactly what intrusive
/// structures (a future registered in a waiter list, say) rely on not
/// happening. Debug builds panic on slab drop while the slot is occupied.
/// If the slab must be abandoned, `mem::forget` the slab: leaked storage is
/// never repurposed, so the pin contract holds.
///
/// # Access
///
/// [`as_ref`](Self::as_ref) and [`as_mut`](Self::as_mut) mirror the methods
/// on `Pin<Box<T>>`. `Deref` gives a plain `&T` for reads. There is
/// deliberately no `DerefMut`, `AsMut`, or `BorrowMut`:
///
/// ```compile_fail,E0594
/// # use nexus_slab::bounded::Slab;
/// # let slab = unsafe { Slab::with_capacity(1) };
/// let mut p = slab.alloc(1u64).into_pinned();
/// *p = 2; // no DerefMut: the value cannot be replaced through the handle
/// # slab.free_pinned(p);
/// ```
///
/// and no way back to a movable handle:
///
/// ```compile_fail,E0308
/// # use nexus_slab::bounded::Slab;
/// # let slab = unsafe { Slab::with_capacity(1) };
/// let p = slab.alloc(1u64).into_pinned();
/// let moved = slab.take(p); // take() needs a Slot; a PinnedSlot cannot be moved out
/// ```
///
/// # Thread Safety
///
/// `!Send` and `!Sync`, same as [`Slot`].
///
/// ```compile_fail,E0277
/// fn assert_send<T: Send>() {}
/// assert_send::<nexus_slab::PinnedSlot<u64>>();
/// ```
#[repr(transparent)]
pub struct PinnedSlot<T>(*mut SlotCell<T>);

impl<T> PinnedSlot<T> {
    /// Returns a pinned shared reference to the value.
    #[inline]
    pub fn as_ref(&self) -> Pin<&T> {
        // SAFETY: the address is stable (slab storage never moves) and this
        // handle offers no way to move the value out: no DerefMut, no
        // BorrowMut, no take. `free_pinned` drops it in place. Both halves
        // of Pin's contract hold for the value's whole lifetime.
        unsafe { Pin::new_unchecked((*self.0).value_ref()) }
    }

    /// Returns a pinned mutable reference to the value.
    #[inline]
    pub fn as_mut(&mut self) -> Pin<&mut T> {
        // SAFETY: as `as_ref`, and `&mut self` guarantees exclusive access.
        unsafe { Pin::new_unchecked((*self.0).value_mut()) }
    }

    /// Returns the raw pointer to the slot cell.
    #[inline]
    pub fn as_ptr(&self) -> *mut SlotCell<T> {
        self.0
    }

    /// Consumes the handle, returning the raw pointer without running Drop.
    ///
    /// Disarms the debug-mode leak detector. The value stays pinned: do not
    /// move it out through the pointer. Reconstruct with
    /// [`from_raw()`](Self::from_raw) or free it in place.
    #[inline]
    pub fn into_raw(self) -> *mut SlotCell<T> {
        let ptr = self.0;
        core::mem::forget(self);
        ptr
    }

    /// Reconstructs a `PinnedSlot` from a raw pointer previously obtained
    /// via [`into_raw()`](Self::into_raw).
    ///
    /// # Safety
    ///
    /// `ptr` must have come from `into_raw()` on a `PinnedSlot<T>` for an
    /// occupied slot in a live slab, and the value must not have been moved
    /// out or dropped in between.
    #[inline]
    pub unsafe fn from_raw(ptr: *mut SlotCell<T>) -> Self {
        PinnedSlot(ptr)
    }
}

impl<T> Deref for PinnedSlot<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        // SAFETY: PinnedSlot was created from a valid, occupied SlotCell.
        unsafe { (*self.0).value_ref() }
    }
}

impl<T> Borrow<T> for PinnedSlot<T> {
    #[inline]
    fn borrow(&self) -> &T {
        self
    }
}

// PinnedSlot is intentionally NOT Clone/Copy, and has no DerefMut, AsMut, or
// BorrowMut: any of those would let safe code move the pinned value.

impl<T: fmt::Debug> fmt::Debug for PinnedSlot<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PinnedSlot")
            .field("value", &**self)
            .finish()
    }
}

#[cfg(debug_assertions)]
impl<T> Drop for PinnedSlot<T> {
    fn drop(&mut self) {
        #[cfg(feature = "std")]
        if std::thread::panicking() {
            return; // Don't double-panic during unwind
        }
        panic!(
            "PinnedSlot<{}> dropped without being freed: call slab.free_pinned(slot)",
            core::any::type_name::<T>()
        );
    }
}
