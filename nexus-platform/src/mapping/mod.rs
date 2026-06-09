use std::num::NonZeroUsize;
use std::os::fd::{AsFd, BorrowedFd, OwnedFd};
use std::ptr::NonNull;
use std::slice;

#[cfg(target_os = "linux")]
mod linux;

#[cfg(target_os = "linux")]
use linux as imp;

#[cfg(not(target_os = "linux"))]
compile_error!(
    "nexus-platform memory mapping requires Linux. \
     macOS/Windows support is not yet implemented."
);

/// How a mapping shares writes with the backing store and other mappings.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Sharing {
    /// Writes are visible to other mappings and propagated to the backing
    /// store. (`MAP_SHARED` on POSIX.)
    Shared,
    /// Copy-on-write: writes are private to this mapping and never reach
    /// the backing store. (`MAP_PRIVATE` on POSIX.)
    Private,
}

/// Access protection for a mapping.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Protection {
    ReadOnly,
    ReadWrite,
}

/// Kernel hint for expected access pattern on a mapping.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Advice {
    /// No special treatment (default).
    Normal,
    /// Pages will be accessed sequentially.
    Sequential,
    /// Pages will be accessed randomly.
    Random,
    /// Pages will be needed soon — prefetch.
    WillNeed,
    /// Pages will not be needed soon — may be reclaimed.
    DontNeed,
    /// Back this range with huge pages (transparent huge pages).
    /// Linux 2.6.38+. No-op if THP is disabled system-wide.
    #[cfg(target_os = "linux")]
    HugePage,
    /// Do not back this range with huge pages.
    #[cfg(target_os = "linux")]
    NoHugePage,
}

#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct MapOptions {
    pub(crate) pretouch: bool,
    pub(crate) huge_pages: bool,
}

/// Error from memory-mapping operations.
#[derive(Debug)]
pub enum MapError {
    /// An I/O error from the underlying syscall.
    Io(std::io::Error),
    /// The file has zero length and cannot be mapped.
    EmptyFile,
    /// The requested offset + length exceeds the file size.
    OutOfBounds,
    /// Huge pages were requested but the pool is exhausted.
    HugePagesUnavailable(std::io::Error),
}

impl std::fmt::Display for MapError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io(e) => write!(f, "{e}"),
            Self::EmptyFile => write!(f, "file has zero length"),
            Self::OutOfBounds => write!(f, "offset + length exceeds mapping bounds"),
            Self::HugePagesUnavailable(e) => write!(f, "huge pages unavailable: {e}"),
        }
    }
}

impl std::error::Error for MapError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io(e) | Self::HugePagesUnavailable(e) => Some(e),
            _ => None,
        }
    }
}

impl From<std::io::Error> for MapError {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e)
    }
}

/// An mmap'd region of memory backed by a kernel file descriptor.
///
/// This is the common representation shared by [`super::MappedFile`] and
/// (future) `SharedMemory`. It holds the pointer, length, and fd produced
/// by `mmap`, and handles `munmap` on drop. The backing store (persistent
/// file vs tmpfs) is determined by whichever outer type constructed the
/// `Mapping`.
///
/// # Shared-mapping caveat
///
/// For [`Sharing::Shared`] mappings, other processes can modify the mapped
/// bytes at any time. Slice views returned by [`as_slice`](Self::as_slice)
/// may observe partial writes from concurrent writers. The caller must
/// provide synchronization (atomics, locks, protocol-level ordering)
/// when reading data written by another process.
///
/// For [`Sharing::Private`] mappings, writes are copy-on-write and
/// invisible to other processes, so concurrent modification is not a concern.
pub struct Mapping {
    ptr: NonNull<u8>,
    len: NonZeroUsize,
    fd: OwnedFd,
    writable: bool,
}

impl Mapping {
    /// Create a mapping from a raw fd. The fd must already be open and
    /// sized appropriately.
    pub(crate) fn new(
        fd: OwnedFd,
        len: NonZeroUsize,
        offset: u64,
        prot: Protection,
        sharing: Sharing,
        opts: MapOptions,
    ) -> Result<Self, MapError> {
        let ptr = imp::map(fd.as_fd(), len, offset, prot, sharing, opts)?;
        Ok(Self {
            ptr,
            len,
            fd,
            writable: prot == Protection::ReadWrite,
        })
    }

    /// Raw pointer to the start of the mapped region.
    ///
    /// Valid for [`len`](Self::len) bytes as long as this `Mapping` is
    /// alive. For shared mappings, concurrent access through this pointer
    /// must be synchronized by the caller.
    pub fn as_ptr(&self) -> *mut u8 {
        self.ptr.as_ptr()
    }

    /// Length of the mapped region in bytes. Always non-zero.
    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.len.get()
    }

    /// Borrow the underlying file descriptor.
    pub fn as_fd(&self) -> BorrowedFd<'_> {
        self.fd.as_fd()
    }

    /// Whether this mapping was created with [`Protection::ReadWrite`].
    pub fn is_writable(&self) -> bool {
        self.writable
    }

    /// View the mapped region as a byte slice.
    ///
    /// For shared mappings, the bytes may change at any time due to
    /// concurrent writers in other processes. The caller must synchronize
    /// access to ensure consistency. See the [type-level docs](Self) for
    /// details.
    pub fn as_slice(&self) -> &[u8] {
        // SAFETY: ptr is non-null, page-aligned, and valid for `len` bytes
        // for the lifetime of this Mapping (guaranteed by the RAII guard
        // and NonNull construction from a successful mmap).
        unsafe { slice::from_raw_parts(self.ptr.as_ptr(), self.len.get()) }
    }

    /// Copy bytes out of the mapping starting at `offset`.
    ///
    /// Returns the number of bytes read (may be less than `buf.len()` if
    /// `offset + buf.len()` exceeds the mapping length).
    pub fn read_at(&self, buf: &mut [u8], offset: usize) -> usize {
        let avail = self.len.get().saturating_sub(offset);
        let n = buf.len().min(avail);
        if n > 0 {
            // SAFETY: offset is within bounds (checked above), and n bytes
            // from offset are within the mapping. The source and dest do
            // not overlap (mapping vs caller's buffer).
            unsafe {
                std::ptr::copy_nonoverlapping(self.ptr.as_ptr().add(offset), buf.as_mut_ptr(), n);
            }
        }
        n
    }

    /// Copy bytes into the mapping starting at `offset`.
    ///
    /// Returns the number of bytes written (may be less than `data.len()`
    /// if `offset + data.len()` exceeds the mapping length).
    ///
    /// Returns [`std::io::ErrorKind::PermissionDenied`] if the mapping was
    /// created with [`Protection::ReadOnly`].
    ///
    /// For shared mappings, concurrent writers are not coordinated by this
    /// method — the caller must synchronize.
    pub fn write_at(&self, data: &[u8], offset: usize) -> Result<usize, std::io::Error> {
        if !self.writable {
            return Err(std::io::Error::from(std::io::ErrorKind::PermissionDenied));
        }
        let avail = self.len.get().saturating_sub(offset);
        let n = data.len().min(avail);
        if n > 0 {
            // SAFETY: offset is within bounds (checked above), and n bytes
            // from offset are within the mapping. The source and dest do
            // not overlap (caller's buffer vs mapping).
            unsafe {
                std::ptr::copy_nonoverlapping(data.as_ptr(), self.ptr.as_ptr().add(offset), n);
            }
        }
        Ok(n)
    }

    /// Flush dirty pages in the mapping to the backing store.
    ///
    /// Blocks until the write-back is complete.
    pub fn sync(&self) -> Result<(), std::io::Error> {
        imp::msync(self.ptr, self.len)
    }

    /// Initiate an asynchronous flush of dirty pages to the backing store.
    ///
    /// Returns immediately; the kernel schedules the write-back. There is
    /// no notification when it completes.
    pub fn sync_async(&self) -> Result<(), std::io::Error> {
        imp::msync_async(self.ptr, self.len)
    }

    /// Advise the kernel on the expected access pattern for this mapping.
    pub fn advise(&self, advice: Advice) -> Result<(), std::io::Error> {
        imp::madvise(self.ptr, self.len, advice)
    }

    /// Lock the mapped pages in physical memory, preventing them from
    /// being swapped out. Requires `CAP_IPC_LOCK` or sufficient
    /// `RLIMIT_MEMLOCK`.
    pub fn lock(&self) -> Result<(), std::io::Error> {
        imp::mlock(self.ptr, self.len)
    }

    /// Unlock previously locked pages, allowing the kernel to swap them.
    pub fn unlock(&self) -> Result<(), std::io::Error> {
        imp::munlock(self.ptr, self.len)
    }
}

impl Drop for Mapping {
    fn drop(&mut self) {
        imp::unmap(self.ptr, self.len);
    }
}

// SAFETY: the mapping is a raw pointer plus its backing fd. The bytes
// live in kernel-managed memory (file-backed or shared), not thread-local
// state. Concurrent access to the mapped contents must be synchronized
// by the caller — the handle itself is safe to move across threads.
unsafe impl Send for Mapping {}
unsafe impl Sync for Mapping {}
