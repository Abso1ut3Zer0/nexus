use std::ffi::CStr;
use std::num::NonZeroUsize;
use std::os::fd::{AsRawFd, BorrowedFd, FromRawFd, OwnedFd};
use std::ptr::NonNull;

use nix::errno::Errno;
use nix::sys::mman::{self, MapFlags, MsFlags, ProtFlags};

use super::{Advice, MapError, MapOptions, Protection, Sharing};

pub(super) fn map(
    fd: BorrowedFd<'_>,
    len: NonZeroUsize,
    offset: u64,
    prot: Protection,
    sharing: Sharing,
    opts: MapOptions,
) -> Result<NonNull<u8>, MapError> {
    let prot_flags = match prot {
        Protection::ReadOnly => ProtFlags::PROT_READ,
        Protection::ReadWrite => ProtFlags::PROT_READ | ProtFlags::PROT_WRITE,
    };

    let mut map_flags = match sharing {
        Sharing::Shared => MapFlags::MAP_SHARED,
        Sharing::Private => MapFlags::MAP_PRIVATE,
    };
    if opts.pretouch {
        map_flags |= MapFlags::MAP_POPULATE;
    }
    if opts.huge_pages {
        map_flags |= MapFlags::MAP_HUGETLB;
    }

    let offset: nix::libc::off_t = offset.try_into().map_err(|_| {
        MapError::Io(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "offset exceeds off_t range",
        ))
    })?;

    // SAFETY: `len` is non-zero; the kernel chooses the address (`None`).
    // `fd` is a valid open file descriptor, and the caller is responsible
    // for ensuring the backing store is large enough for `offset + len`.
    let ptr = unsafe { mman::mmap(None, len, prot_flags, map_flags, fd, offset) }.map_err(|e| {
        if opts.huge_pages && e == Errno::ENOMEM {
            MapError::HugePagesUnavailable(e.into())
        } else {
            MapError::Io(e.into())
        }
    })?;

    Ok(ptr.cast())
}

pub(super) fn unmap(ptr: NonNull<u8>, len: NonZeroUsize) {
    // SAFETY: ptr and len come from a successful mmap and are unchanged
    // since construction.
    unsafe {
        let _ = mman::munmap(ptr.cast(), len.get());
    }
}

pub(super) fn msync(ptr: NonNull<u8>, len: NonZeroUsize) -> Result<(), std::io::Error> {
    // SAFETY: ptr..ptr+len is a valid mapping from mmap.
    unsafe { mman::msync(ptr.cast(), len.get(), MsFlags::MS_SYNC) }.map_err(std::io::Error::from)
}

pub(super) fn msync_async(ptr: NonNull<u8>, len: NonZeroUsize) -> Result<(), std::io::Error> {
    // SAFETY: ptr..ptr+len is a valid mapping from mmap.
    unsafe { mman::msync(ptr.cast(), len.get(), MsFlags::MS_ASYNC) }.map_err(std::io::Error::from)
}

pub(super) fn madvise(
    ptr: NonNull<u8>,
    len: NonZeroUsize,
    advice: Advice,
) -> Result<(), std::io::Error> {
    let flag = match advice {
        Advice::Normal => nix::libc::MADV_NORMAL,
        Advice::Sequential => nix::libc::MADV_SEQUENTIAL,
        Advice::Random => nix::libc::MADV_RANDOM,
        Advice::WillNeed => nix::libc::MADV_WILLNEED,
        Advice::DontNeed => nix::libc::MADV_DONTNEED,
        Advice::HugePage => nix::libc::MADV_HUGEPAGE,
        Advice::NoHugePage => nix::libc::MADV_NOHUGEPAGE,
    };
    // SAFETY: ptr..ptr+len is a valid mapping from mmap.
    unsafe {
        if nix::libc::madvise(ptr.as_ptr().cast(), len.get(), flag) == 0 {
            Ok(())
        } else {
            Err(std::io::Error::last_os_error())
        }
    }
}

pub(super) fn mlock(ptr: NonNull<u8>, len: NonZeroUsize) -> Result<(), std::io::Error> {
    // SAFETY: ptr..ptr+len is a valid mapping from mmap.
    unsafe {
        if nix::libc::mlock(ptr.as_ptr().cast(), len.get()) == 0 {
            Ok(())
        } else {
            Err(std::io::Error::last_os_error())
        }
    }
}

pub(super) fn munlock(ptr: NonNull<u8>, len: NonZeroUsize) -> Result<(), std::io::Error> {
    // SAFETY: ptr..ptr+len is a valid mapping from mmap.
    unsafe {
        if nix::libc::munlock(ptr.as_ptr().cast(), len.get()) == 0 {
            Ok(())
        } else {
            Err(std::io::Error::last_os_error())
        }
    }
}

// ── POSIX shared memory ──────────────────────────────────────────

pub(super) fn shm_open_create(name: &CStr) -> Result<OwnedFd, MapError> {
    // SAFETY: name is a valid null-terminated C string.
    let fd = unsafe {
        nix::libc::shm_open(name.as_ptr(), nix::libc::O_RDWR | nix::libc::O_CREAT, 0o600)
    };
    if fd < 0 {
        return Err(MapError::Io(std::io::Error::last_os_error()));
    }
    // SAFETY: fd is a valid, newly opened file descriptor.
    Ok(unsafe { OwnedFd::from_raw_fd(fd) })
}

pub(super) fn shm_open_existing(name: &CStr, write: bool) -> Result<OwnedFd, MapError> {
    let flags = if write {
        nix::libc::O_RDWR
    } else {
        nix::libc::O_RDONLY
    };
    // SAFETY: name is a valid null-terminated C string.
    let fd = unsafe { nix::libc::shm_open(name.as_ptr(), flags, 0) };
    if fd < 0 {
        return Err(MapError::Io(std::io::Error::last_os_error()));
    }
    // SAFETY: fd is a valid, newly opened file descriptor.
    Ok(unsafe { OwnedFd::from_raw_fd(fd) })
}

pub(super) fn shm_unlink(name: &CStr) -> Result<(), MapError> {
    // SAFETY: name is a valid null-terminated C string.
    if unsafe { nix::libc::shm_unlink(name.as_ptr()) } < 0 {
        return Err(MapError::Io(std::io::Error::last_os_error()));
    }
    Ok(())
}

pub(super) fn fd_size(fd: &OwnedFd) -> Result<u64, MapError> {
    // SAFETY: stat is all-zeros initialized (valid for integer fields),
    // fd is a valid open descriptor.
    unsafe {
        let mut stat = std::mem::zeroed::<nix::libc::stat>();
        if nix::libc::fstat(fd.as_raw_fd(), &raw mut stat) < 0 {
            return Err(MapError::Io(std::io::Error::last_os_error()));
        }
        Ok(stat.st_size as u64)
    }
}

pub(super) fn ftruncate(fd: &OwnedFd, len: u64) -> Result<(), MapError> {
    let len: nix::libc::off_t = len.try_into().map_err(|_| {
        MapError::Io(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "size exceeds off_t range",
        ))
    })?;
    // SAFETY: fd is a valid open descriptor with write access.
    if unsafe { nix::libc::ftruncate(fd.as_raw_fd(), len) } < 0 {
        return Err(MapError::Io(std::io::Error::last_os_error()));
    }
    Ok(())
}
