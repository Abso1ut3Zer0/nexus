//! Unix implementation using mmap.

use std::io;
use std::ptr::NonNull;

use super::Pages;

// =============================================================================
// Page Size Helpers
// =============================================================================

fn page_size() -> usize {
    #[cfg(miri)]
    {
        4096
    }

    #[cfg(not(miri))]
    {
        static PAGE_SIZE: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
        *PAGE_SIZE.get_or_init(|| {
            let size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
            assert!(size > 0, "failed to get page size");
            size as usize
        })
    }
}

#[cfg(target_os = "linux")]
fn huge_page_size() -> usize {
    #[cfg(miri)]
    {
        2 * 1024 * 1024
    }

    #[cfg(not(miri))]
    {
        static HUGE_PAGE_SIZE: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
        *HUGE_PAGE_SIZE.get_or_init(|| read_huge_page_size().unwrap_or(2 * 1024 * 1024))
    }
}

#[cfg(all(target_os = "linux", not(miri)))]
fn read_huge_page_size() -> Option<usize> {
    let contents = std::fs::read_to_string("/proc/meminfo").ok()?;
    let line = contents.lines().find(|l| l.starts_with("Hugepagesize:"))?;
    let size_kb: usize = line.split_whitespace().nth(1)?.parse().ok()?;
    Some(size_kb * 1024)
}

// =============================================================================
// Allocation
// =============================================================================

pub(crate) fn alloc_pages(size: usize) -> io::Result<Pages> {
    alloc_pages_impl(size, false)
}

#[cfg(target_os = "linux")]
pub(crate) fn alloc_pages_hugetlb(size: usize) -> io::Result<Pages> {
    alloc_pages_impl(size, true)
}

#[cfg(miri)]
fn alloc_pages_impl(size: usize, _use_hugetlb: bool) -> io::Result<Pages> {
    assert!(size > 0, "allocation size must be non-zero");

    let page_size = page_size();
    let size = (size + page_size - 1) & !(page_size - 1);

    // Use Vec for Miri - it validates memory safety
    let layout = std::alloc::Layout::from_size_align(size, page_size)
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidInput, e))?;

    let ptr = unsafe { std::alloc::alloc_zeroed(layout) };
    let ptr = NonNull::new(ptr)
        .ok_or_else(|| io::Error::new(io::ErrorKind::OutOfMemory, "allocation failed"))?;

    Ok(Pages { ptr, size })
}

#[cfg(not(miri))]
fn alloc_pages_impl(size: usize, use_hugetlb: bool) -> io::Result<Pages> {
    assert!(size > 0, "allocation size must be non-zero");

    let page_size = page_size();

    #[cfg(target_os = "linux")]
    let (size, flags) = if use_hugetlb {
        let hps = huge_page_size();
        let size = (size + hps - 1) & !(hps - 1);
        let flags = libc::MAP_PRIVATE | libc::MAP_ANONYMOUS | libc::MAP_HUGETLB;
        (size, flags)
    } else {
        let size = (size + page_size - 1) & !(page_size - 1);
        let flags = libc::MAP_PRIVATE | libc::MAP_ANONYMOUS;
        (size, flags)
    };

    #[cfg(not(target_os = "linux"))]
    let (size, flags) = {
        let _ = use_hugetlb;
        let size = (size + page_size - 1) & !(page_size - 1);
        let flags = libc::MAP_PRIVATE | libc::MAP_ANONYMOUS;
        (size, flags)
    };

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

    // Request THP for non-hugetlb allocations >= 2MB
    #[cfg(target_os = "linux")]
    if !use_hugetlb && size >= 2 * 1024 * 1024 {
        unsafe {
            libc::madvise(ptr.as_ptr() as *mut libc::c_void, size, libc::MADV_HUGEPAGE);
        }
    }

    // Prefault all pages
    for offset in (0..size).step_by(page_size) {
        unsafe {
            std::ptr::write_volatile(ptr.as_ptr().add(offset), 0);
        }
    }

    Ok(Pages { ptr, size })
}

// =============================================================================
// Memory Locking
// =============================================================================

pub(crate) fn mlock_impl(ptr: NonNull<u8>, size: usize) -> io::Result<()> {
    #[cfg(miri)]
    {
        let _ = (ptr, size);
        Ok(())
    }

    #[cfg(not(miri))]
    {
        let result = unsafe { libc::mlock(ptr.as_ptr() as *const libc::c_void, size) };
        if result == 0 {
            Ok(())
        } else {
            Err(io::Error::last_os_error())
        }
    }
}

// =============================================================================
// Deallocation
// =============================================================================

/// # Safety
/// ptr and size must be from a previous alloc_pages call.
pub(crate) unsafe fn drop_pages(ptr: NonNull<u8>, size: usize) {
    #[cfg(miri)]
    {
        let page_size = page_size();
        let layout = std::alloc::Layout::from_size_align(size, page_size).expect("invalid layout");
        unsafe {
            std::alloc::dealloc(ptr.as_ptr(), layout);
        }
    }

    #[cfg(not(miri))]
    unsafe {
        libc::munmap(ptr.as_ptr() as *mut libc::c_void, size);
    }
}
