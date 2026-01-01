//! Unix implementation using mmap.

use std::io;
use std::ptr::NonNull;

use super::Pages;

/// Returns the system page size (typically 4096 bytes).
pub fn page_size() -> usize {
    static PAGE_SIZE: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *PAGE_SIZE.get_or_init(|| {
        // Safety: sysconf is safe to call
        let size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
        assert!(size > 0, "failed to get page size");
        size as usize
    })
}

pub fn alloc_pages(size: usize) -> io::Result<Pages> {
    assert!(size > 0, "allocation size must be non-zero");

    // Round up to page boundary
    let page_size = page_size();
    let size = (size + page_size - 1) & !(page_size - 1);

    let mut flags = libc::MAP_PRIVATE | libc::MAP_ANONYMOUS;

    // MAP_POPULATE: prefault all pages at allocation time
    // This avoids page faults during operation
    #[cfg(target_os = "linux")]
    {
        flags |= libc::MAP_POPULATE;
    }

    // Safety: mmap with MAP_ANONYMOUS doesn't access any file
    let ptr = unsafe {
        libc::mmap(
            std::ptr::null_mut(),
            size,
            libc::PROT_READ | libc::PROT_WRITE,
            flags,
            -1,
            0,
        )
    };

    if ptr == libc::MAP_FAILED {
        return Err(io::Error::last_os_error());
    }

    let ptr = NonNull::new(ptr as *mut u8).expect("mmap returned null");

    // On non-Linux Unix, manually prefault pages
    #[cfg(not(target_os = "linux"))]
    {
        for offset in (0..size).step_by(page_size) {
            // Safety: offset is within allocated region
            unsafe {
                std::ptr::write_volatile(ptr.as_ptr().add(offset), 0);
            }
        }
    }

    Ok(Pages { ptr, size })
}

pub fn mlock_impl(ptr: NonNull<u8>, size: usize) -> io::Result<()> {
    // Safety: ptr and size describe a valid memory region
    let result = unsafe { libc::mlock(ptr.as_ptr() as *const libc::c_void, size) };

    if result == 0 {
        Ok(())
    } else {
        Err(io::Error::last_os_error())
    }
}

pub fn munlock_impl(ptr: NonNull<u8>, size: usize) -> io::Result<()> {
    // Safety: ptr and size describe a valid memory region
    let result = unsafe { libc::munlock(ptr.as_ptr() as *const libc::c_void, size) };

    if result == 0 {
        Ok(())
    } else {
        Err(io::Error::last_os_error())
    }
}

/// # Safety
///
/// ptr and size must be from a previous alloc_pages call.
pub unsafe fn drop_pages(ptr: NonNull<u8>, size: usize) {
    // munlock is implicit - kernel unlocks when region is unmapped
    unsafe {
        libc::munmap(ptr.as_ptr() as *mut libc::c_void, size);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn page_size_is_power_of_two() {
        let ps = page_size();
        assert!(ps.is_power_of_two());
        assert!(ps >= 4096); // Minimum on all modern systems
    }

    #[test]
    fn alloc_single_page() {
        let pages = alloc_pages(1).unwrap();
        assert!(pages.size() >= page_size());
    }

    #[test]
    fn alloc_multiple_pages() {
        let size = page_size() * 10;
        let pages = alloc_pages(size).unwrap();
        assert_eq!(pages.size(), size);
    }

    #[test]
    fn alloc_rounds_up_to_page() {
        let pages = alloc_pages(100).unwrap();
        assert_eq!(pages.size(), page_size());
    }

    #[test]
    fn write_entire_region() {
        let size = page_size() * 4;
        let pages = alloc_pages(size).unwrap();

        // Write to every byte - should not fault (prefaulted)
        unsafe {
            std::ptr::write_bytes(pages.as_ptr(), 0xAB, size);
        }

        // Verify
        unsafe {
            assert_eq!(*pages.as_ptr(), 0xAB);
            assert_eq!(*pages.as_ptr().add(size - 1), 0xAB);
        }
    }
}
