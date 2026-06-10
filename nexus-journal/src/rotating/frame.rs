pub(crate) const FRAME_HDR: usize = 8;
pub(crate) const ALIGN: usize = 8;

#[inline]
pub(crate) const fn align_up(n: usize) -> usize {
    (n + ALIGN - 1) & !(ALIGN - 1)
}

#[inline]
pub(crate) const fn footprint(body: usize) -> usize {
    FRAME_HDR + align_up(body)
}

/// # Safety
/// `ptr` must be 4-byte-aligned and within the mapped region.
#[inline]
pub(crate) unsafe fn read_commit_len(ptr: *const u8) -> u32 {
    unsafe { ptr.cast::<u32>().read() }
}

/// # Safety
/// `ptr` must be 4-byte-aligned and within the mapped region.
#[inline]
pub(crate) unsafe fn write_commit_len(ptr: *mut u8, val: u32) {
    unsafe { ptr.cast::<u32>().write(val) }
}

#[inline]
pub(crate) fn session_id_ptr(ptr: *mut u8) -> *mut u32 {
    // SAFETY: ptr is frame-aligned (>= 4-byte), so ptr+4 is also 4-byte aligned.
    unsafe { ptr.add(4).cast() }
}

/// Zero-copy view of a committed record in the log.
///
/// Provides access to the session tag, global offset, and payload bytes
/// without copying from the underlying mmap'd segment.
#[repr(C)]
pub struct Frame<'buf> {
    payload: &'buf [u8],
    offset: u64,
    session_id: u32,
}

impl<'buf> Frame<'buf> {
    pub(crate) fn new(payload: &'buf [u8], offset: u64, session_id: u32) -> Self {
        Self {
            payload,
            offset,
            session_id,
        }
    }

    #[inline]
    pub fn session_id(&self) -> u32 {
        self.session_id
    }

    #[inline]
    pub fn offset(&self) -> u64 {
        self.offset
    }

    #[inline]
    pub fn payload(&self) -> &'buf [u8] {
        self.payload
    }
}

/// Opaque position handle for a record in the log.
///
/// Returned by [`RotatingJournal::append`](super::RotatingJournal::append), passed to [`RotatingJournal::read`](super::RotatingJournal::read).
/// Valid until the slot it references is rotated out (two rotations after
/// the write — one to move it to `prev`, one to evict).
///
/// # Bit layout
///
/// ```text
/// 63           34 33  32 31                    0
/// ┌──────────────┬──────┬──────────────────────┐
/// │    epoch     │ slot │     local_off        │
/// │   (30 bits)  │(2 b) │     (32 bits)        │
/// └──────────────┴──────┴──────────────────────┘
/// ```
///
/// - **`epoch`** (bits 63:34): rotation generation counter. Matched against
///   `slot_gen[slot]` to detect stale offsets — if the slot has been reused
///   since this offset was issued, the epoch won't match and `read()` returns
///   `None`.
///
/// - **`slot`** (bits 33:32): physical segment index (0, 1, or 2). Only
///   `current` and `prev` slots are readable; if the slot is `standby`,
///   `read()` returns `None`.
///
/// - **`local_off`** (bits 31:0): byte offset of the frame within the
///   segment. Points to the start of the frame header (`commit_len`), not
///   the payload.
///
/// # Default
///
/// `u64::MAX` encodes slot index 3 (no valid slot exists), so a default
/// `LogOffset` always returns `None` from `read()`.
///
/// # Global offset
///
/// A `LogOffset` can be converted to a monotonic global byte position via
/// `epoch * segment_size + local_off`. This is used by [`Frame::offset`] to
/// give each record a unique position across all segments.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LogOffset(u64);

impl Default for LogOffset {
    fn default() -> Self {
        Self(u64::MAX)
    }
}

impl LogOffset {
    #[inline]
    pub(crate) fn new(slot: u8, local_off: usize, epoch: u32) -> Self {
        Self((epoch as u64) << 34 | (slot as u64) << 32 | local_off as u64)
    }

    #[inline]
    pub(crate) fn global_offset(self, segment_size: usize) -> u64 {
        self.epoch() as u64 * segment_size as u64 + self.local_off() as u64
    }

    #[inline]
    pub(crate) fn slot(self) -> usize {
        ((self.0 >> 32) & 0x3) as usize
    }

    #[inline]
    pub(crate) fn local_off(self) -> usize {
        (self.0 & 0xFFFF_FFFF) as usize
    }

    #[inline]
    pub(crate) fn epoch(self) -> u32 {
        (self.0 >> 34) as u32
    }
}
