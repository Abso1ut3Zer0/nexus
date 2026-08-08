use crate::pod::Pod;

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
pub(crate) unsafe fn read_commit_len(base: *mut u8, offset: usize) -> u32 {
    // SAFETY: caller guarantees base.add(offset) is 4-byte-aligned and within the mapping.
    unsafe { base.add(offset).cast::<u32>().read() }
}

/// # Safety
/// `base.add(offset)` must be 4-byte-aligned and within the mapping.
#[inline]
pub(crate) unsafe fn write_commit_len(base: *mut u8, offset: usize, val: u32) {
    // SAFETY: caller guarantees base.add(offset) is 4-byte-aligned and within the mapping.
    unsafe { base.add(offset).cast::<u32>().write(val) }
}

/// # Safety
/// The frame header at `offset` must be published and within the mapping.
#[inline]
pub(crate) unsafe fn frame_kind(base: *mut u8, offset: usize) -> u16 {
    // SAFETY: caller guarantees the frame header at offset is published and within the mapping.
    unsafe { std::ptr::read_unaligned(base.add(offset + 4).cast()) }
}

/// # Safety
/// The 8-byte frame header at `offset` must be within the mapping and
/// reserved for this write.
#[inline]
pub(crate) unsafe fn write_frame_kind(base: *mut u8, offset: usize, kind: u16) {
    // SAFETY: caller guarantees the 8-byte frame header at offset is within the mapping and reserved.
    unsafe {
        std::ptr::write_unaligned(base.add(offset + 4).cast::<u16>(), kind);
        std::ptr::write_unaligned(base.add(offset + 6).cast::<u16>(), 0);
    }
}

/// # Safety
/// `[offset, offset + size_of::<T>())` must be within the mapping and
/// reserved for this write.
#[inline]
pub(crate) unsafe fn write_val<T: Pod>(base: *mut u8, offset: usize, val: T) {
    // SAFETY: caller guarantees the offset range is within the mapping and reserved for this write.
    unsafe { std::ptr::write_unaligned(base.add(offset).cast(), val) }
}

/// # Safety
/// `[offset, offset + size_of::<T>())` must be within the mapping and
/// the data must be published.
#[inline]
pub(crate) unsafe fn read_val<T: Pod>(base: *mut u8, offset: usize) -> T {
    // SAFETY: caller guarantees the offset range is within the mapping and the data is published.
    unsafe { std::ptr::read_unaligned(base.add(offset).cast()) }
}
