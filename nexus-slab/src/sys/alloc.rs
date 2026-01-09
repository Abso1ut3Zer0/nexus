//! Default implementation using std::alloc.

use std::io;
use std::ptr::NonNull;

use super::Pages;

const PAGE_SIZE: usize = 4096;

pub(crate) fn alloc_pages(size: usize) -> io::Result<Pages> {
    assert!(size > 0, "allocation size must be non-zero");

    let size = (size + PAGE_SIZE - 1) & !(PAGE_SIZE - 1);

    let layout = std::alloc::Layout::from_size_align(size, PAGE_SIZE)
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidInput, e))?;

    let ptr = unsafe { std::alloc::alloc_zeroed(layout) };

    let ptr = NonNull::new(ptr)
        .ok_or_else(|| io::Error::new(io::ErrorKind::OutOfMemory, "allocation failed"))?;

    Ok(Pages { ptr, size })
}

/// # Safety
/// ptr and size must be from a previous alloc_pages call.
pub(crate) unsafe fn drop_pages(ptr: NonNull<u8>, size: usize) {
    let layout = std::alloc::Layout::from_size_align(size, PAGE_SIZE).expect("invalid layout");
    unsafe {
        std::alloc::dealloc(ptr.as_ptr(), layout);
    }
}
