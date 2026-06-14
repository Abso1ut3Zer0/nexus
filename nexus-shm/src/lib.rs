//! Shared-memory IPC primitives for multi-process trading systems.
//!
//! Implements the foundation layer: the segment control block, the
//! mmap-backed [`Segment`], and two-tier liveness (atomic status + OFD lock).

pub(crate) mod control;
mod error;
mod segment;

pub use error::ShmError;
pub use nexus_platform::{Liveness, MapHints, MappedFile};
pub use segment::{Segment, Status};
