//! Platform-specific OS primitives behind a portable Rust API.
//!
//! # Primitives
//!
//! - [`FileLock`] — RAII exclusive file lock for mutual exclusion
//! - [`ProcessLease`] — kernel-mediated process liveness detection
//! - [`Liveness`] — result of probing a process lease
//! - [`MappedFile`] — RAII file-backed memory mapping

pub mod file_lock;
pub mod lease;
mod mapped_file;
pub mod mapping;

pub use file_lock::FileLock;
pub use lease::{Liveness, ProcessLease};
pub use mapped_file::{MappedFile, MappedFileOptions};
pub use mapping::{Advice, MapError, Mapping, Protection, Sharing};
