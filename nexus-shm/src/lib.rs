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
pub use nexus_platform::{Liveness, MapOptions};
pub use pod::Pod;
pub use seglog::{
    Conductor, ConductorBuilder, Frame, LogError, LogOffset, OpenError, SegmentedLog,
    SegmentedLogBuilder,
};
pub use segment::{Segment, Status};
