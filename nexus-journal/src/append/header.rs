use crate::pod::Pod;

/// Per-record metadata the journal frames but never interprets. Any [`Pod`] is a
/// valid header; `()` gives a position-only log at zero overhead.
pub trait RecordHeader: Pod {}

impl<T: Pod> RecordHeader for T {}

/// A header carrying a monotonic sequence number, enabling [`read_range`].
///
/// [`read_range`]: super::Reader::read_range
pub trait SeqHeader: RecordHeader {
    fn seq(&self) -> u64;
}

/// Reference header for FIX journaling: sequence number plus timestamp.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(C)]
pub struct FixHeader {
    pub seq: u64,
    pub timestamp: u64,
}

// SAFETY: repr(C) over two u64 — fixed layout, no pointers, no Drop, valid for
// every bit pattern.
unsafe impl Pod for FixHeader {}

impl SeqHeader for FixHeader {
    fn seq(&self) -> u64 {
        self.seq
    }
}
