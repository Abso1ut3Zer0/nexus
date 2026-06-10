use std::sync::atomic::AtomicU32;

pub(crate) const FRAME_HEADER: usize = 8;
pub(crate) const ALIGN: usize = 8;

pub(crate) const TYPE_DATA: u16 = 0;
pub(crate) const TYPE_PAD: u16 = 1;

pub(crate) const fn align_up(n: usize) -> usize {
    (n + ALIGN - 1) & !(ALIGN - 1)
}

pub(crate) const fn footprint(body: usize) -> usize {
    FRAME_HEADER + align_up(body)
}

/// # Safety
/// `base.add(offset)` must be 4-byte-aligned and within the mapping.
#[inline]
pub(crate) unsafe fn commit_len<'a>(base: *mut u8, offset: usize) -> &'a AtomicU32 {
    unsafe { AtomicU32::from_ptr(base.add(offset).cast()) }
}

/// # Safety
/// The frame header at `offset` must be published and within the mapping.
#[inline]
pub(crate) unsafe fn frame_kind(base: *mut u8, offset: usize) -> u16 {
    unsafe { std::ptr::read_unaligned(base.add(offset + 4).cast()) }
}

/// # Safety
/// The 8-byte frame header at `offset` must be within the mapping and
/// reserved for this write.
#[inline]
pub(crate) unsafe fn write_frame_kind(base: *mut u8, offset: usize, kind: u16) {
    unsafe {
        std::ptr::write_unaligned(base.add(offset + 4).cast::<u16>(), kind);
        std::ptr::write_unaligned(base.add(offset + 6).cast::<u16>(), 0);
    }
}

/// # Safety
/// `[offset, offset + size_of::<T>())` must be within the mapping and
/// reserved for this write.
#[inline]
pub(crate) unsafe fn write_val<T: Copy>(base: *mut u8, offset: usize, val: T) {
    unsafe { std::ptr::write_unaligned(base.add(offset).cast(), val) }
}

/// # Safety
/// `[offset, offset + size_of::<T>())` must be within the mapping and
/// the data must be published.
#[inline]
pub(crate) unsafe fn read_val<T: Copy>(base: *mut u8, offset: usize) -> T {
    unsafe { std::ptr::read_unaligned(base.add(offset).cast()) }
}
