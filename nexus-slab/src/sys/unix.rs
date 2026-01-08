//! Unix implementation using mmap.

use std::io;
use std::ptr::NonNull;

use super::Pages;

fn page_size() -> usize {
    static PAGE_SIZE: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *PAGE_SIZE.get_or_init(|| {
        let size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
        assert!(size > 0, "failed to get page size");
        size as usize
    })
}

#[cfg(target_os = "linux")]
fn huge_page_size() -> usize {
    static HUGE_PAGE_SIZE: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *HUGE_PAGE_SIZE.get_or_init(|| {
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
        2 * 1024 * 1024
    })
}

pub(crate) fn alloc_pages(size: usize) -> io::Result<Pages> {
    alloc_pages_impl(size, false)
}

#[cfg(target_os = "linux")]
pub(crate) fn alloc_pages_hugetlb(size: usize) -> io::Result<Pages> {
    alloc_pages_impl(size, true)
}

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

pub(crate) fn mlock_impl(ptr: NonNull<u8>, size: usize) -> io::Result<()> {
    let result = unsafe { libc::mlock(ptr.as_ptr() as *const libc::c_void, size) };
    if result == 0 {
        Ok(())
    } else {
        Err(io::Error::last_os_error())
    }
}

/// # Safety
/// ptr and size must be from a previous alloc_pages call.
pub(crate) unsafe fn drop_pages(ptr: NonNull<u8>, size: usize) {
    unsafe {
        libc::munmap(ptr.as_ptr() as *mut libc::c_void, size);
    }
}
