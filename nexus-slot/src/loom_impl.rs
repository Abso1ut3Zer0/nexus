#[cfg(loom)]
pub(crate) use loom::sync::Arc;
#[cfg(not(loom))]
pub(crate) use std::sync::Arc;

#[cfg(loom)]
pub(crate) use loom::sync::atomic::{AtomicBool, AtomicUsize, Ordering, fence};
#[cfg(not(loom))]
pub(crate) use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering, fence};

#[cfg(loom)]
#[inline(always)]
pub(crate) fn spin_yield() {
    loom::thread::yield_now();
}

#[cfg(not(loom))]
#[inline(always)]
pub(crate) fn spin_yield() {
    core::hint::spin_loop();
}

// Under loom, the seqlock's word-at-a-time Relaxed stores/loads are modeled
// as a single Relaxed AtomicUsize operation. Word-at-a-time correctness is
// separately verified by miri; loom tests the fence/sequence protocol.

#[cfg(loom)]
pub(crate) fn loom_store<T>(data: &AtomicUsize, value: &T) {
    const { assert!(std::mem::size_of::<T>() <= std::mem::size_of::<usize>()) };
    let mut bits = 0usize;
    // SAFETY: T fits in usize (const-asserted). We copy T's bytes into a
    // zero-initialized usize. Remaining bytes stay zero.
    unsafe {
        std::ptr::copy_nonoverlapping(
            (value as *const T).cast::<u8>(),
            std::ptr::addr_of_mut!(bits).cast::<u8>(),
            std::mem::size_of::<T>(),
        );
    }
    data.store(bits, Ordering::Relaxed);
}

#[cfg(loom)]
pub(crate) fn loom_load<T>(data: &AtomicUsize) -> std::mem::MaybeUninit<T> {
    const { assert!(std::mem::size_of::<T>() <= std::mem::size_of::<usize>()) };
    let bits = data.load(Ordering::Relaxed);
    // SAFETY: T fits in usize (const-asserted). We copy size_of::<T>() bytes
    // from the loaded usize into a MaybeUninit<T> buffer. The caller assumes
    // init only after seqlock validation, mirroring the real atomic_load path.
    unsafe {
        let mut value = std::mem::MaybeUninit::<T>::uninit();
        std::ptr::copy_nonoverlapping(
            std::ptr::addr_of!(bits).cast::<u8>(),
            value.as_mut_ptr().cast::<u8>(),
            std::mem::size_of::<T>(),
        );
        value
    }
}
