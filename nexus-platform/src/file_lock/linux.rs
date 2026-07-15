use std::fs::File;
use std::os::fd::AsFd;

use nix::errno::Errno;
use nix::fcntl::{FcntlArg, fcntl};
use nix::libc;

fn wrlck() -> libc::flock {
    // SAFETY: `flock` is a plain C struct of integers; all-zero is valid.
    let mut lk: libc::flock = unsafe { std::mem::zeroed() };
    lk.l_type = libc::F_WRLCK as libc::c_short;
    lk.l_whence = libc::SEEK_SET as libc::c_short;
    lk.l_start = 0;
    lk.l_len = 0; // entire file
    lk
}

/// Acquire an exclusive OFD lock on `file`, blocking until available.
pub(super) fn lock_exclusive_blocking(file: &File) -> Result<(), std::io::Error> {
    // `F_OFD_SETLKW` blocks, and a signal can interrupt the wait with `EINTR`.
    // "Blocking" must mean "blocks until acquired," so retry on interrupt rather
    // than surface it as a failure.
    loop {
        match fcntl(file.as_fd(), FcntlArg::F_OFD_SETLKW(&wrlck())) {
            Ok(_) => return Ok(()),
            // Interrupted before the lock was acquired: fall through and retry.
            Err(Errno::EINTR) => {}
            Err(e) => return Err(std::io::Error::from(e)),
        }
    }
}

/// Try to acquire an exclusive OFD lock without blocking.
///
/// Returns `Ok(true)` if the lock was acquired, `Ok(false)` if another
/// file description already holds it.
pub(super) fn try_lock_exclusive(file: &File) -> Result<bool, std::io::Error> {
    match fcntl(file.as_fd(), FcntlArg::F_OFD_SETLK(&wrlck())) {
        Ok(_) => Ok(true),
        Err(Errno::EAGAIN | Errno::EACCES) => Ok(false),
        Err(e) => Err(std::io::Error::from(e)),
    }
}
