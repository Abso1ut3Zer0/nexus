//! Build-time validation of `Waker` and `Context` layout.
//!
//! `ReusableWaker` constructs a `Waker` and `Context` from raw pointer
//! arrays, relying on specific field ordering. Neither type is `repr(C)`
//! — the layout is a compiler convention, not a language guarantee.
//!
//! This build script validates the layout at compile time. If rustc ever
//! changes the field order, the build fails with a clear error message
//! rather than producing silent UB at runtime.
//!
//! Note: build scripts run on the host, not the target. For cross-compilation,
//! the runtime layout tests in `waker.rs::tests` provide target-side validation.
//! In practice, `Waker`/`Context` layout is a compiler convention (not
//! target-dependent), so host validation is sufficient.

use std::mem::size_of;
use std::ptr;
use std::task::{Context, RawWaker, RawWakerVTable, Waker};

fn noop(_: *const ()) {}
fn clone_waker(p: *const ()) -> RawWaker {
    RawWaker::new(p, &VTABLE)
}
static VTABLE: RawWakerVTable = RawWakerVTable::new(clone_waker, noop, noop, noop);

#[repr(C)]
struct WakerRepr {
    vtable: *const (),
    data: *const (),
}

fn main() {
    // =========================================================================
    // Waker layout: must be [vtable_ptr, data_ptr] at 16 bytes
    // =========================================================================

    assert!(
        size_of::<Waker>() == 16,
        "nexus-async-rt: Waker size is {}, expected 16. \
         ReusableWaker layout assumption is broken.",
        size_of::<Waker>()
    );

    let sentinel = 0xDEAD_BEEF_CAFE_u64 as *const ();
    let raw = RawWaker::new(sentinel, &VTABLE);
    // SAFETY: VTABLE functions are all no-ops; sentinel data pointer is never dereferenced.
    let waker = std::mem::ManuallyDrop::new(unsafe { Waker::from_raw(raw) });

    // SAFETY: ptr is a valid local reference; ptr::read copies bytes to inspect fat pointer layout.
    let repr: WakerRepr = unsafe { ptr::read(ptr::addr_of!(*waker).cast::<WakerRepr>()) };

    assert!(
        repr.vtable == ((&raw const VTABLE) as *const ()),
        "nexus-async-rt: Waker field order is not [vtable, data]. \
         Expected vtable at offset 0. This compiler is not supported."
    );
    assert!(
        repr.data == sentinel,
        "nexus-async-rt: Waker field order is not [vtable, data]. \
         Expected data at offset 8. This compiler is not supported."
    );

    // =========================================================================
    // Context layout: first field must be &Waker, total size <= 32 bytes
    // =========================================================================

    assert!(
        size_of::<Context<'_>>() <= 32,
        "nexus-async-rt: Context size is {}, expected <= 32. \
         ReusableWaker layout assumption is broken.",
        size_of::<Context<'_>>()
    );

    let cx = Context::from_waker(&waker);
    // SAFETY: ptr is a valid local reference; ptr::read copies bytes to inspect fat pointer layout.
    let first_word: *const () = unsafe { ptr::read(ptr::addr_of!(cx).cast::<*const ()>()) };

    assert!(
        first_word == (ptr::addr_of!(*waker) as *const ()),
        "nexus-async-rt: Context first field is not &Waker. \
         ReusableWaker layout assumption is broken."
    );
}
