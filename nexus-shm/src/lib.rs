//! Shared-memory IPC primitives for multi-process trading systems.
//!
//! Implements the foundation layer: the segment control block, the
//! mmap-backed [`Segment`], and two-tier liveness (atomic status + OFD lock).
//! Also provides [`ShmSlotWriter`] / [`ShmSlotReader`] for cross-process
//! latest-value sharing via seqlock, and [`ShmRingWriter`] / [`ShmRingReader`]
//! for cross-process SPSC messaging.

pub(crate) mod control;
mod error;
pub mod pod;
mod ring;
mod segment;
mod slot;

pub use error::ShmError;
pub use nexus_platform::{Liveness, MapHints, MappedFile};
pub use pod::Pod;
pub use ring::{ShmRingReader, ShmRingWriter};
pub use segment::{Segment, Status};
pub use slot::{ShmSlotReader, ShmSlotWriter, SlotRead};
