//! Unix implementation using mmap.
//!
//! # Huge Page Support
//!
//! This module provides three tiers of huge page support:
//!
//! 1. **THP (default)**: Uses `MADV_HUGEPAGE` hint. Best-effort, no setup required.
//!
//! 2. **Collapse**: Uses `MADV_COLLAPSE` (Linux 6.1+) to synchronously request
//!    huge pages after allocation. Stronger than THP but still best-effort.
//!
//! 3. **Hugetlb**: Uses `MAP_HUGETLB` for guaranteed huge pages from the
//!    reserved pool. Requires system setup but provides deterministic performance.

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

/// Returns the huge page size (typically 2MB on x86_64).
#[cfg(target_os = "linux")]
pub fn huge_page_size() -> usize {
    static HUGE_PAGE_SIZE: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *HUGE_PAGE_SIZE.get_or_init(|| {
        // Try to read from /proc/meminfo
        if let Ok(contents) = std::fs::read_to_string("/proc/meminfo") {
            for line in contents.lines() {
                if line.starts_with("Hugepagesize:") {
                    if let Some(size_str) = line.split_whitespace().nth(1) {
                        if let Ok(size_kb) = size_str.parse::<usize>() {
                            return size_kb * 1024;
                        }
                    }
                }
            }
        }
        // Default to 2MB if we can't read it
        2 * 1024 * 1024
    })
}

/// Allocate page-aligned memory with THP hint for large allocations.
pub fn alloc_pages(size: usize) -> io::Result<Pages> {
    alloc_pages_impl(size, false)
}

/// Allocate pages backed by reserved huge pages (hugetlbfs).
///
/// Requires huge pages to be reserved on the system:
/// ```bash
/// # Reserve 512 huge pages (1GB on x86_64)
/// echo 512 | sudo tee /proc/sys/vm/nr_hugepages
/// ```
///
/// Returns an error if huge pages are not available.
#[cfg(target_os = "linux")]
pub fn alloc_pages_hugetlb(size: usize) -> io::Result<Pages> {
    alloc_pages_impl(size, true)
}

fn alloc_pages_impl(size: usize, use_hugetlb: bool) -> io::Result<Pages> {
    assert!(size > 0, "allocation size must be non-zero");

    let page_size = page_size();

    #[cfg(target_os = "linux")]
    let (size, flags) = if use_hugetlb {
        // Round up to huge page boundary
        let hps = huge_page_size();
        let size = (size + hps - 1) & !(hps - 1);
        let flags = libc::MAP_PRIVATE | libc::MAP_ANONYMOUS | libc::MAP_HUGETLB;
        (size, flags)
    } else {
        // Round up to regular page boundary
        let size = (size + page_size - 1) & !(page_size - 1);
        let flags = libc::MAP_PRIVATE | libc::MAP_ANONYMOUS;
        (size, flags)
    };

    #[cfg(not(target_os = "linux"))]
    let (size, flags) = {
        let size = (size + page_size - 1) & !(page_size - 1);
        let flags = libc::MAP_PRIVATE | libc::MAP_ANONYMOUS;
        (size, flags)
    };

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

    // For non-hugetlb allocations, request THP before prefaulting
    #[cfg(target_os = "linux")]
    if !use_hugetlb {
        const HUGE_PAGE_THRESHOLD: usize = 2 * 1024 * 1024; // 2MB
        if size >= HUGE_PAGE_THRESHOLD {
            unsafe {
                libc::madvise(ptr.as_ptr() as *mut libc::c_void, size, libc::MADV_HUGEPAGE);
            }
        }
    }

    // Prefault all pages - this happens AFTER the hugepage hint,
    // so the kernel can back them with 2MB pages if available.
    for offset in (0..size).step_by(page_size) {
        unsafe {
            std::ptr::write_volatile(ptr.as_ptr().add(offset), 0);
        }
    }

    Ok(Pages { ptr, size })
}

/// Attempt to collapse regular pages into huge pages.
///
/// This is a stronger hint than `MADV_HUGEPAGE` - it synchronously attempts
/// to collapse the pages NOW rather than waiting for khugepaged.
///
/// Requires Linux 6.1+. Returns `Ok(())` on older kernels (no-op).
/// May partially succeed - some regions may be collapsed while others aren't.
///
/// # Errors
///
/// Returns an error if the kernel rejects the request for reasons other
/// than lack of support (e.g., memory pressure).
#[cfg(target_os = "linux")]
pub fn try_collapse(ptr: NonNull<u8>, size: usize) -> io::Result<()> {
    // MADV_COLLAPSE = 25, added in Linux 6.1
    const MADV_COLLAPSE: i32 = 25;

    let result = unsafe { libc::madvise(ptr.as_ptr() as *mut libc::c_void, size, MADV_COLLAPSE) };

    if result == 0 {
        Ok(())
    } else {
        let err = io::Error::last_os_error();
        // EINVAL means kernel doesn't support MADV_COLLAPSE - that's OK
        if err.raw_os_error() == Some(libc::EINVAL) {
            Ok(())
        } else {
            Err(err)
        }
    }
}

#[cfg(not(target_os = "linux"))]
pub fn try_collapse(_ptr: NonNull<u8>, _size: usize) -> io::Result<()> {
    Ok(()) // No-op on non-Linux
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
    #[cfg(target_os = "linux")]
    fn huge_page_size_is_power_of_two() {
        let hps = huge_page_size();
        assert!(hps.is_power_of_two());
        assert!(hps >= 2 * 1024 * 1024); // At least 2MB
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

    #[test]
    fn try_collapse_does_not_panic() {
        let pages = alloc_pages(4 * 1024 * 1024).unwrap(); // 4MB
        // Should not panic regardless of kernel support
        let _ = try_collapse(NonNull::new(pages.as_ptr()).unwrap(), pages.size());
    }

    #[test]
    #[cfg(target_os = "linux")]
    fn hugetlb_may_fail_without_reserved_pages() {
        // This test just verifies the API works - it may succeed or fail
        // depending on whether huge pages are reserved
        let result = alloc_pages_hugetlb(2 * 1024 * 1024);
        // Either succeeds or fails with ENOMEM - shouldn't panic
        match result {
            Ok(pages) => assert!(pages.size() >= 2 * 1024 * 1024),
            Err(e) => assert!(e.raw_os_error().is_some()),
        }
    }
}
