//! Platform-specific OS primitives behind a portable Rust API.
//!
//! # Primitives
//!
//! - [`FileLock`] — RAII exclusive file lock for mutual exclusion
//! - [`ProcessLease`] — kernel-mediated process liveness detection
//! - [`Liveness`] — result of probing a process lease
//! - [`MappedFile`] — RAII file-backed memory mapping
//! - [`SharedMemory`] — RAII POSIX shared memory mapping (`/dev/shm`)

pub mod file_lock;
pub mod lease;
mod mapped_file;
pub mod mapping;
mod shared_memory;

pub use file_lock::FileLock;
pub use lease::{Liveness, ProcessLease};
pub use mapped_file::{MappedFile, MappedFileOptions};
pub use mapping::{Advice, MapError, Mapping, Protection, Sharing};
pub use shared_memory::{SharedMemory, SharedMemoryOptions};

/// Mapping hints for segment creation and attachment.
///
/// These are best-effort: the platform backend documents what it
/// actually provides. Both default to `false`.
#[derive(Debug, Clone, Copy, Default)]
pub struct MapHints {
    /// Pre-fault pages into memory (`MAP_POPULATE`).
    pub pretouch: bool,
    /// Request huge-page backing (`MAP_HUGETLB`).
    pub huge_pages: bool,
}
