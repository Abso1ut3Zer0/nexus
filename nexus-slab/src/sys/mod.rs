//! Platform-specific page allocation (internal).

#[cfg(unix)]
mod unix;

#[cfg(windows)]
mod windows;

use std::ptr::NonNull;

/// A page-aligned memory region allocated directly from the OS.
///
/// Memory is automatically freed when dropped. Pages are prefaulted
/// at allocation time to avoid page faults during operation.
pub(crate) struct Pages {
    ptr: NonNull<u8>,
    size: usize,
}

impl Pages {
    /// Allocate page-aligned memory with THP hint for large allocations.
    pub(crate) fn alloc(size: usize) -> std::io::Result<Self> {
        alloc_pages(size)
    }

    /// Allocate memory backed by reserved huge pages (hugetlbfs).
    #[cfg(target_os = "linux")]
    pub(crate) fn alloc_hugetlb(size: usize) -> std::io::Result<Self> {
        alloc_pages_hugetlb(size)
    }

    /// Returns a pointer to the start of the allocated region.
    #[inline]
    pub(crate) fn as_ptr(&self) -> *mut u8 {
        self.ptr.as_ptr()
    }

    /// Lock pages in physical RAM, preventing swapping.
    pub(crate) fn mlock(&self) -> std::io::Result<()> {
        mlock_impl(self.ptr, self.size)
    }
}

unsafe impl Send for Pages {}

#[cfg(unix)]
use unix::{alloc_pages, drop_pages, mlock_impl};

#[cfg(all(unix, target_os = "linux"))]
use unix::alloc_pages_hugetlb;

#[cfg(windows)]
use windows::{alloc_pages, drop_pages, mlock_impl};

impl Drop for Pages {
    fn drop(&mut self) {
        unsafe { drop_pages(self.ptr, self.size) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alloc_small() {
        let pages = Pages::alloc(1).unwrap();
        assert!(!pages.as_ptr().is_null());
    }

    #[test]
    fn alloc_exact_page() {
        let pages = Pages::alloc(4096).unwrap();
        assert!(!pages.as_ptr().is_null());
    }

    #[test]
    fn alloc_multiple_pages() {
        let pages = Pages::alloc(4096 * 10).unwrap();
        assert!(!pages.as_ptr().is_null());
    }

    #[test]
    fn alloc_large_thp_eligible() {
        // 4MB - should get THP hint on Linux
        let pages = Pages::alloc(4 * 1024 * 1024).unwrap();
        assert!(!pages.as_ptr().is_null());
    }

    #[test]
    fn pointer_is_page_aligned() {
        let pages = Pages::alloc(100).unwrap();
        let addr = pages.as_ptr() as usize;
        assert_eq!(addr % 4096, 0);
    }

    #[test]
    fn can_write_entire_region() {
        let size = 4096 * 4;
        let pages = Pages::alloc(size).unwrap();

        // Should not fault - pages are prefaulted
        unsafe {
            std::ptr::write_bytes(pages.as_ptr(), 0xAB, size);
            assert_eq!(*pages.as_ptr(), 0xAB);
            assert_eq!(*pages.as_ptr().add(size - 1), 0xAB);
        }
    }

    #[test]
    fn mlock_does_not_panic() {
        let pages = Pages::alloc(4096).unwrap();
        // May succeed or fail depending on privileges - just shouldn't panic
        let _ = pages.mlock();
    }

    #[test]
    #[should_panic(expected = "non-zero")]
    fn alloc_zero_panics() {
        let _ = Pages::alloc(0);
    }

    #[test]
    fn drop_deallocates() {
        // Just verify no crash/leak - can't easily verify memory returned to OS
        for _ in 0..100 {
            let pages = Pages::alloc(4096 * 100).unwrap();
            drop(pages);
        }
    }

    #[test]
    #[cfg(target_os = "linux")]
    #[cfg_attr(miri, ignore)]
    fn hugetlb_returns_result() {
        // May succeed or fail depending on system config - shouldn't panic
        let result = Pages::alloc_hugetlb(2 * 1024 * 1024);
        match result {
            Ok(pages) => assert!(!pages.as_ptr().is_null()),
            Err(_) => {} // Expected without reserved huge pages
        }
    }

    #[test]
    fn multiple_concurrent_allocs() {
        let allocations: Vec<_> = (0..10).map(|_| Pages::alloc(4096 * 10).unwrap()).collect();

        // All should have distinct addresses
        for i in 0..allocations.len() {
            for j in (i + 1)..allocations.len() {
                assert_ne!(allocations[i].as_ptr(), allocations[j].as_ptr());
            }
        }
    }
}
