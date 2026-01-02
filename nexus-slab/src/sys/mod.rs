//! Platform-specific page allocation.
//!
//! This module provides direct OS memory allocation with page alignment,
//! prefaulting, and optional page locking (mlock).
//!
//! # Huge Page Support
//!
//! Three tiers of huge page support are available:
//!
//! 1. **THP (default)**: Transparent Huge Pages via `MADV_HUGEPAGE`.
//!    Best-effort, no setup required. Use [`Pages::alloc`].
//!
//! 2. **Collapse**: Synchronous huge page request via `MADV_COLLAPSE`.
//!    Stronger than THP but still best-effort. Use [`Pages::try_collapse`].
//!    Requires Linux 6.1+.
//!
//! 3. **Hugetlb**: Guaranteed huge pages from reserved pool.
//!    Requires system setup but provides deterministic performance.
//!    Use [`Pages::alloc_hugetlb`].
//!
//! # Platform Support
//!
//! - **Unix** (Linux, macOS, BSD): Fully supported via `mmap`
//! - **Windows**: Experimental, requires `unstable-windows` feature

#[cfg(unix)]
mod unix;

#[cfg(windows)]
mod windows;

use std::ptr::NonNull;

/// A page-aligned memory region allocated directly from the OS.
///
/// Memory is automatically freed when dropped. Pages are prefaulted
/// at allocation time to avoid page faults during operation.
///
/// # Example
///
/// ```no_run
/// use nexus_slab::sys::Pages;
///
/// let pages = Pages::alloc(4096 * 10)?;
///
/// // Optionally lock in RAM (requires privileges)
/// if let Err(e) = pages.mlock() {
///     eprintln!("mlock failed: {}", e);
/// }
/// # Ok::<(), std::io::Error>(())
/// ```
pub struct Pages {
    ptr: NonNull<u8>,
    size: usize,
}

impl Pages {
    /// Allocate page-aligned memory with THP hint for large allocations.
    ///
    /// The actual size may be rounded up to a page boundary.
    /// Pages are prefaulted (physically backed) at allocation time.
    ///
    /// For allocations >= 2MB, requests Transparent Huge Pages via
    /// `MADV_HUGEPAGE`. This is a hint - the kernel may or may not
    /// honor it depending on availability.
    ///
    /// # Errors
    ///
    /// Returns an error if allocation fails (e.g., out of memory).
    pub fn alloc(size: usize) -> std::io::Result<Self> {
        alloc_pages(size)
    }

    /// Allocate memory backed by reserved huge pages (hugetlbfs).
    ///
    /// Unlike THP, this provides **guaranteed** huge pages - the allocation
    /// will fail if huge pages are not available rather than falling back
    /// to regular pages.
    ///
    /// # System Setup Required
    ///
    /// Huge pages must be reserved before use:
    ///
    /// ```bash
    /// # Reserve 512 huge pages (1GB on x86_64 with 2MB pages)
    /// echo 512 | sudo tee /proc/sys/vm/nr_hugepages
    ///
    /// # Or at boot via kernel parameter:
    /// # hugepages=512
    /// ```
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - No huge pages are reserved
    /// - Not enough free huge pages
    /// - Platform doesn't support hugetlbfs
    #[cfg(target_os = "linux")]
    pub fn alloc_hugetlb(size: usize) -> std::io::Result<Self> {
        alloc_pages_hugetlb(size)
    }

    /// Attempt to collapse regular pages into huge pages.
    ///
    /// This is a synchronous request to the kernel to collapse the backing
    /// 4KB pages into 2MB huge pages NOW, rather than waiting for the
    /// background `khugepaged` daemon.
    ///
    /// This is stronger than the THP hint given at allocation time, but
    /// still best-effort - it may partially succeed or fail entirely if
    /// contiguous physical memory is not available.
    ///
    /// # Compatibility
    ///
    /// - **Linux 6.1+**: Full support via `MADV_COLLAPSE`
    /// - **Older Linux**: Returns `Ok(())` (no-op)
    /// - **Other platforms**: Returns `Ok(())` (no-op)
    ///
    /// # Errors
    ///
    /// Returns an error if the kernel rejects the request for reasons
    /// other than lack of support (e.g., severe memory pressure).
    pub fn try_collapse(&self) -> std::io::Result<()> {
        try_collapse(self.ptr, self.size)
    }

    /// Returns a pointer to the start of the allocated region.
    #[inline]
    pub fn as_ptr(&self) -> *mut u8 {
        self.ptr.as_ptr()
    }

    /// Returns the size of the allocated region in bytes.
    #[inline]
    pub fn size(&self) -> usize {
        self.size
    }

    /// Lock pages in physical RAM, preventing swapping.
    ///
    /// This ensures memory accesses never trigger page faults due to
    /// swapping, which is critical for latency-sensitive applications.
    ///
    /// # Privileges
    ///
    /// - **Linux**: Requires `CAP_IPC_LOCK` capability or sufficient
    ///   `RLIMIT_MEMLOCK` limit
    /// - **macOS**: Generally works without special privileges
    /// - **Windows**: Requires `SeLockMemoryPrivilege`
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - Insufficient privileges
    /// - Resource limits exceeded (`RLIMIT_MEMLOCK`)
    /// - System out of lockable memory
    pub fn mlock(&self) -> std::io::Result<()> {
        mlock_impl(self.ptr, self.size)
    }

    /// Unlock pages, allowing them to be swapped.
    ///
    /// This is automatically done on drop, so explicit calls are
    /// rarely needed.
    pub fn munlock(&self) -> std::io::Result<()> {
        munlock_impl(self.ptr, self.size)
    }
}

// Safety: Pages is just a pointer to OS-allocated memory.
// Safe to send across threads if nothing else references it.
unsafe impl Send for Pages {}

// Platform-specific implementations

#[cfg(unix)]
use unix::{alloc_pages, drop_pages, mlock_impl, munlock_impl, try_collapse};

#[cfg(unix)]
pub use unix::page_size;

#[cfg(all(unix, target_os = "linux"))]
use unix::alloc_pages_hugetlb;

#[cfg(all(unix, target_os = "linux"))]
pub use unix::huge_page_size;

#[cfg(windows)]
use windows::{alloc_pages, drop_pages, mlock_impl, munlock_impl};

#[cfg(windows)]
pub use windows::page_size;

#[cfg(windows)]
fn try_collapse(_ptr: NonNull<u8>, _size: usize) -> std::io::Result<()> {
    Ok(()) // No-op on Windows
}

impl Drop for Pages {
    fn drop(&mut self) {
        // Safety: ptr and size are valid from allocation
        unsafe { drop_pages(self.ptr, self.size) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alloc_and_write() {
        let pages = Pages::alloc(page_size()).unwrap();

        // Should be able to write without page faults (prefaulted)
        unsafe {
            std::ptr::write_volatile(pages.as_ptr(), 42);
            assert_eq!(std::ptr::read_volatile(pages.as_ptr()), 42);
        }
    }

    #[test]
    fn page_aligned() {
        let pages = Pages::alloc(100).unwrap();
        let addr = pages.as_ptr() as usize;
        assert_eq!(addr % page_size(), 0);
    }

    #[test]
    fn mlock_may_fail_without_privileges() {
        let pages = Pages::alloc(page_size()).unwrap();
        // mlock might succeed or fail depending on privileges - just ensure no panic
        let _ = pages.mlock();
    }

    #[test]
    fn try_collapse_does_not_panic() {
        let pages = Pages::alloc(4 * 1024 * 1024).unwrap();
        // Should not panic regardless of kernel support
        let _ = pages.try_collapse();
    }
}
