//! Append-only and bounded-rotation mmap'd journals for trading systems.

pub mod append;
pub(crate) mod pod;
pub mod rotating;

pub use nexus_platform::MapHints;
pub use pod::Pod;

pub use append::{
    AppendOnlyJournal, AppendOnlyJournalConfig, AppendOnlyJournalError, FixHeader, ReadRange,
    ReadRecord, Reader, RecordHeader, SeqHeader, WriteClaim, Writer,
};

pub use rotating::{
    Conductor, ConductorBuilder, Frame, LogOffset, OpenError, RotatingJournal,
    RotatingJournalBuilder, WriteError,
};
