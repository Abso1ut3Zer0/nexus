//! Platform-specific page allocation.
//!
//! This module provides direct OS memory allocation with page alignment,
//! prefaulting, and optional page locking (mlock).
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
    /// Allocate page-aligned memory.
    ///
    /// The actual size may be rounded up to a page boundary.
    /// Pages are prefaulted (physically backed) at allocation time.
    ///
    /// # Errors
    ///
    /// Returns an error if allocation fails (e.g., out of memory).
    pub fn alloc(size: usize) -> std::io::Result<Self> {
        alloc_pages(size)
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
use unix::{alloc_pages, drop_pages, mlock_impl, munlock_impl};

#[cfg(unix)]
pub use unix::page_size;

#[cfg(windows)]
use windows::{alloc_pages, drop_pages, mlock_impl, munlock_impl};

#[cfg(windows)]
pub use windows::page_size;

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
}
