//! Shared-memory IPC primitives for multi-process trading systems.
//!
//! See `docs/design/nexus-shm.md`. This module tree currently implements the
//! foundation layer: the [`Pod`] boundary, the segment control block, the
//! mmap-backed [`Segment`], and two-tier liveness (atomic status + OFD lock).

pub(crate) mod control;
mod error;
mod journal;
mod pod;
mod seglog;
mod segment;

pub use error::ShmError;
pub use journal::{
    FixHeader, Journal, JournalConfig, JournalError, ReadRange, ReadRecord, Reader, RecordHeader,
    SeqHeader, WriteClaim, Writer,
};
pub use nexus_platform::Liveness;

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
pub use pod::Pod;
pub use seglog::{
    Conductor, ConductorBuilder, Frame, LogError, LogOffset, OpenError, SegmentedLog,
    SegmentedLogBuilder,
};
pub use segment::{Segment, Status};
