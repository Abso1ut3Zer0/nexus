//! Windows implementation using VirtualAlloc.
//!
//! Requires `unstable-windows` feature.

#[cfg(not(feature = "unstable-windows"))]
compile_error!(
    "Windows support requires the `unstable-windows` feature.\n\
     Note: This is experimental and untested.\n\
     Enable with: nexus-slab = { version = \"...\", features = [\"unstable-windows\"] }"
);

use std::io;
use std::ptr::NonNull;

use windows_sys::Win32::System::Memory::{
    MEM_COMMIT, MEM_RELEASE, MEM_RESERVE, PAGE_READWRITE, VirtualAlloc, VirtualFree, VirtualLock,
};
use windows_sys::Win32::System::SystemInformation::{GetSystemInfo, SYSTEM_INFO};

use super::Pages;

fn page_size() -> usize {
    static PAGE_SIZE: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *PAGE_SIZE.get_or_init(|| {
        let mut info: SYSTEM_INFO = unsafe { std::mem::zeroed() };
        unsafe { GetSystemInfo(&mut info) };
        info.dwPageSize as usize
    })
}

pub(crate) fn alloc_pages(size: usize) -> io::Result<Pages> {
    assert!(size > 0, "allocation size must be non-zero");

    let page_size = page_size();
    let size = (size + page_size - 1) & !(page_size - 1);

    let ptr = unsafe {
        VirtualAlloc(
            std::ptr::null(),
            size,
            MEM_RESERVE | MEM_COMMIT,
            PAGE_READWRITE,
        )
    };

    if ptr.is_null() {
        return Err(io::Error::last_os_error());
    }

    let ptr = NonNull::new(ptr as *mut u8).expect("VirtualAlloc returned null");

    // Prefault all pages
    for offset in (0..size).step_by(page_size) {
        unsafe {
            std::ptr::write_volatile(ptr.as_ptr().add(offset), 0);
        }
    }

    Ok(Pages { ptr, size })
}

pub(crate) fn mlock_impl(ptr: NonNull<u8>, size: usize) -> io::Result<()> {
    let result = unsafe { VirtualLock(ptr.as_ptr() as *const _, size) };
    if result != 0 {
        Ok(())
    } else {
        Err(io::Error::last_os_error())
    }
}

/// # Safety
/// ptr and size must be from a previous alloc_pages call.
pub(crate) unsafe fn drop_pages(ptr: NonNull<u8>, _size: usize) {
    VirtualFree(ptr.as_ptr() as *mut _, 0, MEM_RELEASE);
}
