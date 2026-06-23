//! FIX message framing over a TCP byte stream.
//!
//! [`FrameReader`] buffers inbound bytes and yields complete FIX messages
//! as `&[u8]` slices. [`FrameWriter`] buffers outbound messages encoded by
//! the codec. Both are dictionary-independent — using only the structural
//! tags `8=` (BeginString), `9=` (BodyLength), and `10=` (CheckSum) that
//! are invariant across all FIX versions.

use nexus_fix_codec::validate_checksum;
use nexus_net::buf::{ReadBuf, WriteBuf};
use nexus_net::wire::ParserSink;

const SOH: u8 = 0x01;

/// Checksum trailer is always `10=XXX\x01` — 7 bytes.
const CHECKSUM_LEN: usize = 7;

/// Error from [`FrameReader::read`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReadError {
    /// ReadBuf cannot accept the incoming bytes.
    BufferFull {
        /// Bytes the caller tried to write.
        needed: usize,
        /// Bytes available in the spare region.
        available: usize,
    },
}

impl std::fmt::Display for ReadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BufferFull { needed, available } => {
                write!(f, "buffer full: need {needed} bytes, {available} available")
            }
        }
    }
}

impl std::error::Error for ReadError {}

/// Error from [`FrameReader::next`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FrameError {
    /// Invalid data was detected and discarded. `skipped` bytes were
    /// advanced past to reach the next `8=` boundary (or end of buffer).
    ///
    /// The reader is ready for the next [`next`](FrameReader::next) call —
    /// no manual recovery needed.
    Garbage { skipped: usize },
    /// Message exceeds the configured maximum size. The message was
    /// skipped entirely.
    MessageTooLarge { size: usize },
}

impl std::fmt::Display for FrameError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Garbage { skipped } => {
                write!(f, "discarded {skipped} bytes of invalid data")
            }
            Self::MessageTooLarge { size } => {
                write!(f, "message size {size} exceeds configured maximum")
            }
        }
    }
}

impl std::error::Error for FrameError {}

/// FIX message boundary detector.
///
/// Buffers inbound TCP bytes and yields complete FIX messages. Each call
/// to [`next`](Self::next) returns the next complete message as a raw
/// `&[u8]` borrowing from the internal buffer, or `None` if more bytes
/// are needed.
///
/// Invalid data is handled automatically: `next()` scans forward to
/// the next `8=` boundary and returns [`FrameError::Garbage`] with the
/// number of bytes discarded. The reader is always in a parseable state
/// after returning — no manual recovery needed.
///
/// # Usage
///
/// ```
/// use nexus_fix_engine::FrameReader;
///
/// let mut reader = FrameReader::builder()
///     .buffer_capacity(65_536)
///     .build();
///
/// // A complete Heartbeat message.
/// let msg = b"8=FIX.4.4\x019=5\x0135=0\x0110=163\x01";
/// reader.read(msg).unwrap();
///
/// let frame = reader.next().unwrap().unwrap();
/// assert_eq!(frame, msg.as_slice());
/// assert!(reader.next().unwrap().is_none());
/// ```
pub struct FrameReader {
    buf: ReadBuf,
    buf_compact_at: usize,
    max_message_size: usize,
    pending_advance: usize,
}

/// Builder for [`FrameReader`].
pub struct FrameReaderBuilder {
    buffer_capacity: usize,
    compact_at: f64,
    max_message_size: usize,
}

enum ParseResult {
    Complete(usize),
    Incomplete,
    Garbage,
    TooLarge { size: usize, end: usize },
}

impl FrameReader {
    /// Create a builder with sensible defaults.
    #[must_use]
    pub fn builder() -> FrameReaderBuilder {
        FrameReaderBuilder {
            buffer_capacity: 64 * 1024,
            compact_at: 0.5,
            max_message_size: 1024 * 1024,
        }
    }

    /// Buffer wire bytes from a source slice.
    pub fn read(&mut self, src: &[u8]) -> Result<(), ReadError> {
        let mut spare = self.buf.spare();
        if src.len() > spare.len() {
            self.buf.compact();
            spare = self.buf.spare();
            if src.len() > spare.len() {
                return Err(ReadError::BufferFull {
                    needed: src.len(),
                    available: spare.len(),
                });
            }
        }
        spare[..src.len()].copy_from_slice(src);
        self.buf.filled(src.len());
        Ok(())
    }

    /// Read bytes from a source directly into the internal buffer.
    ///
    /// Returns bytes read, or 0 on EOF.
    pub fn read_from<R: std::io::Read>(&mut self, src: &mut R) -> std::io::Result<usize> {
        let mut spare = self.buf.spare();
        if spare.is_empty() {
            self.buf.compact();
            spare = self.buf.spare();
            if spare.is_empty() {
                return Err(std::io::Error::other("frame reader buffer full"));
            }
        }
        let n = src.read(spare)?;
        self.buf.filled(n);
        Ok(n)
    }

    /// Writable region for direct socket reads.
    #[inline]
    pub fn spare(&mut self) -> &mut [u8] {
        self.buf.spare()
    }

    /// Commit bytes written into [`spare()`](Self::spare).
    #[inline]
    pub fn filled(&mut self, n: usize) {
        self.buf.filled(n);
    }

    /// Reclaim consumed buffer space.
    #[inline]
    pub fn compact(&mut self) {
        self.buf.compact();
    }

    /// Whether the buffer should be compacted based on the configured threshold.
    #[inline]
    pub fn should_compact(&self) -> bool {
        let consumed = self.buf.consumed();
        consumed > 0 && consumed >= self.buf_compact_at && !self.buf.is_empty()
    }

    /// Bytes of buffer space remaining.
    #[inline]
    pub fn remaining(&self) -> usize {
        self.buf.remaining()
    }

    /// Parse the next complete FIX message.
    ///
    /// Returns the full message bytes (`8=…` through `10=XXX\x01`) or
    /// `None` if more data is needed. Call in a loop after each
    /// [`read`](Self::read) to drain all complete messages from the buffer.
    ///
    /// On invalid data, scans forward to the next `8=` boundary and
    /// returns [`FrameError::Garbage`]. The reader always makes progress
    /// on error — the next call starts from the new position.
    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Result<Option<&[u8]>, FrameError> {
        if self.pending_advance > 0 {
            self.buf.advance(self.pending_advance);
            self.pending_advance = 0;
        }

        match self.try_parse() {
            ParseResult::Complete(end) => {
                self.pending_advance = end;
                Ok(Some(&self.buf.data()[..end]))
            }
            ParseResult::Incomplete => Ok(None),
            ParseResult::Garbage => {
                let skipped = self.skip_to_next_header();
                Err(FrameError::Garbage { skipped })
            }
            ParseResult::TooLarge { size, end } => {
                if self.buf.data().len() >= end {
                    self.buf.advance(end);
                } else {
                    self.skip_to_next_header();
                }
                Err(FrameError::MessageTooLarge { size })
            }
        }
    }

    /// Pure read-only parse: determines the message boundary or error
    /// without mutating any state.
    fn try_parse(&self) -> ParseResult {
        let data = self.buf.data();
        if data.len() < 2 {
            return ParseResult::Incomplete;
        }

        if data[0] != b'8' || data[1] != b'=' {
            return ParseResult::Garbage;
        }

        let Some(soh1) = find_soh(data, 2) else {
            return ParseResult::Incomplete;
        };

        let tag9 = soh1 + 1;
        if data.len() < tag9 + 3 {
            return ParseResult::Incomplete;
        }
        if data[tag9] != b'9' || data[tag9 + 1] != b'=' {
            return ParseResult::Garbage;
        }

        let digits_start = tag9 + 2;
        let Some(soh2) = find_soh(data, digits_start) else {
            return ParseResult::Incomplete;
        };
        let Ok(body_len) = parse_body_length(&data[digits_start..soh2]) else {
            return ParseResult::Garbage;
        };

        let body_start = soh2 + 1;
        let Some(message_end) = body_start
            .checked_add(body_len)
            .and_then(|n| n.checked_add(CHECKSUM_LEN))
        else {
            return ParseResult::Garbage;
        };

        if message_end > self.max_message_size {
            return ParseResult::TooLarge {
                size: message_end,
                end: message_end,
            };
        }

        if data.len() < message_end {
            return ParseResult::Incomplete;
        }

        if validate_checksum(&data[..message_end]).is_err() {
            return ParseResult::Garbage;
        }

        ParseResult::Complete(message_end)
    }

    /// Scan forward from byte 1 for the next `8=` and advance past
    /// everything before it. Returns bytes discarded.
    fn skip_to_next_header(&mut self) -> usize {
        let data = self.buf.data();
        for i in 1..data.len().saturating_sub(1) {
            if data[i] == b'8' && data[i + 1] == b'=' {
                self.buf.advance(i);
                return i;
            }
        }
        let len = data.len();
        self.buf.advance(len);
        len
    }
}

impl ParserSink for FrameReader {
    #[inline]
    fn spare(&mut self) -> &mut [u8] {
        self.buf.spare()
    }

    #[inline]
    fn filled(&mut self, n: usize) {
        self.buf.filled(n);
    }
}

impl FrameReaderBuilder {
    /// Internal buffer capacity in bytes.
    ///
    /// Default: 64 KiB. The buffer is fixed-size — it never reallocates.
    #[must_use]
    pub fn buffer_capacity(mut self, cap: usize) -> Self {
        self.buffer_capacity = cap;
        self
    }

    /// Fraction of buffer that must be consumed before [`should_compact`](FrameReader::should_compact)
    /// returns `true`. Default: 0.5 (50%).
    #[must_use]
    pub fn compact_at(mut self, ratio: f64) -> Self {
        assert!(
            (0.0..=1.0).contains(&ratio),
            "compact_at must be between 0.0 and 1.0, got {ratio}"
        );
        self.compact_at = ratio;
        self
    }

    /// Maximum message size in bytes. Messages exceeding this return
    /// [`FrameError::MessageTooLarge`]. Default: 1 MiB.
    #[must_use]
    pub fn max_message_size(mut self, max: usize) -> Self {
        self.max_message_size = max;
        self
    }

    /// Build the [`FrameReader`].
    #[must_use]
    pub fn build(self) -> FrameReader {
        let buf = ReadBuf::with_capacity(self.buffer_capacity);
        let buf_compact_at = (self.buffer_capacity as f64 * self.compact_at) as usize;
        FrameReader {
            buf,
            buf_compact_at,
            max_message_size: self.max_message_size,
            pending_advance: 0,
        }
    }
}

/// Find the next SOH byte (`\x01`) starting at `from`.
///
/// SWAR (SIMD Within A Register): processes 8 bytes per iteration
/// using u64 arithmetic. Sufficient for the short scans in header
/// parsing (~8-12 bytes to first SOH).
#[inline]
fn find_soh(data: &[u8], from: usize) -> Option<usize> {
    const HI: u64 = 0x8080_8080_8080_8080;
    const LO: u64 = 0x0101_0101_0101_0101;

    let bytes = data.get(from..)?;
    if bytes.is_empty() {
        return None;
    }

    let splat = LO; // LO * 0x01 == LO
    let mut i = 0;

    while i + 8 <= bytes.len() {
        // SAFETY: bounds checked by the while condition
        let chunk: [u8; 8] = unsafe { bytes.as_ptr().add(i).cast::<[u8; 8]>().read_unaligned() };
        let word = u64::from_ne_bytes(chunk);
        let xored = word ^ splat;
        let mask = xored.wrapping_sub(LO) & !xored & HI;
        if mask != 0 {
            let offset = (mask.trailing_zeros() / 8) as usize;
            return Some(from + i + offset);
        }
        i += 8;
    }

    while i < bytes.len() {
        if bytes[i] == SOH {
            return Some(from + i);
        }
        i += 1;
    }

    None
}

/// Parse an ASCII decimal integer from a byte slice.
fn parse_body_length(digits: &[u8]) -> Result<usize, ()> {
    if digits.is_empty() {
        return Err(());
    }
    let mut n: usize = 0;
    for &b in digits {
        if !b.is_ascii_digit() {
            return Err(());
        }
        n = n
            .checked_mul(10)
            .and_then(|n| n.checked_add((b - b'0') as usize))
            .ok_or(())?;
    }
    Ok(n)
}

// =============================================================================
// FrameWriter
// =============================================================================

/// Outbound FIX message buffer.
///
/// Thin wrapper around [`WriteBuf`](nexus_net::buf::WriteBuf) providing
/// symmetry with [`FrameReader`]. The codec (via
/// [`FrameFormatter`](nexus_fix_codec::FrameFormatter)) handles all message
/// encoding — FrameWriter just manages the write buffer.
///
/// # Usage
///
/// ```
/// use nexus_fix_engine::FrameWriter;
/// use nexus_fix_codec::FrameFormatter;
///
/// let mut writer = FrameWriter::builder().buffer_capacity(4096).build();
///
/// // Encode a Heartbeat into the writer's spare region.
/// let spare = writer.spare();
/// let mut fmt = FrameFormatter::new(spare, b"FIX.4.4", b"0");
/// let (start, len) = fmt.finish().unwrap();
///
/// // Commit the encoded message.
/// writer.commit(start, len);
///
/// // Data is ready for the socket.
/// assert!(!writer.is_empty());
/// assert!(writer.data().starts_with(b"8=FIX.4.4\x01"));
/// ```
pub struct FrameWriter(WriteBuf);

/// Builder for [`FrameWriter`].
pub struct FrameWriterBuilder {
    buffer_capacity: usize,
}

impl FrameWriter {
    /// Create a builder with sensible defaults.
    #[must_use]
    pub fn builder() -> FrameWriterBuilder {
        FrameWriterBuilder {
            buffer_capacity: 64 * 1024,
        }
    }

    /// Writable region for encoding a message via
    /// [`FrameFormatter`](nexus_fix_codec::FrameFormatter).
    #[inline]
    pub fn spare(&mut self) -> &mut [u8] {
        self.0.spare()
    }

    /// Commit a finished message into the write buffer.
    ///
    /// `start` and `len` come from
    /// [`FrameFormatter::finish()`](nexus_fix_codec::FrameFormatter::finish).
    /// Closes the right-alignment gap (if any) so the message is contiguous
    /// with any previously buffered data.
    #[inline]
    pub fn commit(&mut self, start: usize, len: usize) {
        if start > 0 {
            self.0.spare().copy_within(start..start + len, 0);
        }
        self.0.filled(len);
    }

    /// Pending bytes ready for socket write.
    #[inline]
    pub fn data(&self) -> &[u8] {
        self.0.data()
    }

    /// Consume `n` bytes after a successful socket write.
    ///
    /// Auto-resets the buffer when fully drained.
    #[inline]
    pub fn advance(&mut self, n: usize) {
        self.0.advance(n);
    }

    /// Whether there are pending bytes to write.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Bytes of spare capacity remaining.
    #[inline]
    pub fn remaining(&self) -> usize {
        self.0.tailroom()
    }
}

impl FrameWriterBuilder {
    /// Total buffer capacity in bytes. Default: 64 KiB.
    #[must_use]
    pub fn buffer_capacity(mut self, capacity: usize) -> Self {
        self.buffer_capacity = capacity;
        self
    }

    /// Build the [`FrameWriter`].
    #[must_use]
    pub fn build(self) -> FrameWriter {
        FrameWriter(WriteBuf::new(self.buffer_capacity, 0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn heartbeat() -> Vec<u8> {
        let mut buf = [0u8; 128];
        let (start, len) = nexus_fix_codec::FrameFormatter::new(&mut buf, b"FIX.4.4", b"0")
            .finish()
            .unwrap();
        buf[start..start + len].to_vec()
    }

    fn new_order(clord_id: &[u8]) -> Vec<u8> {
        let mut buf = [0u8; 256];
        let mut f = nexus_fix_codec::FrameFormatter::new(&mut buf, b"FIX.4.4", b"D");
        f.field(49, b"SENDER");
        f.field(56, b"TARGET");
        f.field(11, clord_id);
        let (start, len) = f.finish().unwrap();
        buf[start..start + len].to_vec()
    }

    // ---- happy path ----

    #[test]
    fn single_message() {
        let msg = heartbeat();
        let mut reader = FrameReader::builder().build();
        reader.read(&msg).unwrap();

        let frame = reader.next().unwrap().unwrap();
        assert_eq!(frame, msg.as_slice());
        assert!(reader.next().unwrap().is_none());
    }

    #[test]
    fn two_messages_in_one_read() {
        let mut data = heartbeat();
        let second = new_order(b"ORD-1");
        data.extend_from_slice(&second);

        let mut reader = FrameReader::builder().build();
        reader.read(&data).unwrap();

        let f1 = reader.next().unwrap().unwrap().to_vec();
        let f2 = reader.next().unwrap().unwrap().to_vec();
        assert!(reader.next().unwrap().is_none());

        assert_eq!(f1, heartbeat());
        assert_eq!(f2, second);
    }

    #[test]
    fn incomplete_then_complete() {
        let msg = heartbeat();
        let split = msg.len() / 2;

        let mut reader = FrameReader::builder().build();
        reader.read(&msg[..split]).unwrap();
        assert!(reader.next().unwrap().is_none());

        reader.read(&msg[split..]).unwrap();
        let frame = reader.next().unwrap().unwrap();
        assert_eq!(frame, msg.as_slice());
    }

    #[test]
    fn byte_at_a_time() {
        let msg = heartbeat();
        let mut reader = FrameReader::builder().build();

        for (i, &b) in msg.iter().enumerate() {
            reader.read(&[b]).unwrap();
            if i < msg.len() - 1 {
                assert!(reader.next().unwrap().is_none());
            }
        }
        let frame = reader.next().unwrap().unwrap();
        assert_eq!(frame, msg.as_slice());
    }

    #[test]
    fn three_messages_sequential() {
        let m1 = new_order(b"A");
        let m2 = new_order(b"BB");
        let m3 = heartbeat();

        let mut reader = FrameReader::builder().build();
        reader.read(&m1).unwrap();
        reader.read(&m2).unwrap();
        reader.read(&m3).unwrap();

        assert_eq!(reader.next().unwrap().unwrap(), m1.as_slice());
        assert_eq!(reader.next().unwrap().unwrap(), m2.as_slice());
        assert_eq!(reader.next().unwrap().unwrap(), m3.as_slice());
        assert!(reader.next().unwrap().is_none());
    }

    #[test]
    fn spare_and_filled() {
        let msg = heartbeat();
        let mut reader = FrameReader::builder().build();

        let spare = reader.spare();
        spare[..msg.len()].copy_from_slice(&msg);
        reader.filled(msg.len());

        let frame = reader.next().unwrap().unwrap();
        assert_eq!(frame, msg.as_slice());
    }

    #[test]
    fn read_from_io() {
        let msg = heartbeat();
        let mut cursor = std::io::Cursor::new(&msg);
        let mut reader = FrameReader::builder().build();

        let n = reader.read_from(&mut cursor).unwrap();
        assert_eq!(n, msg.len());

        let frame = reader.next().unwrap().unwrap();
        assert_eq!(frame, msg.as_slice());
    }

    // ---- garbage recovery ----

    #[test]
    fn garbage_prefix_skipped() {
        let msg = heartbeat();
        let mut data = b"GARBAGE".to_vec();
        data.extend_from_slice(&msg);

        let mut reader = FrameReader::builder().build();
        reader.read(&data).unwrap();

        // next() detects garbage, skips to 8=, returns error.
        let err = reader.next().unwrap_err();
        assert_eq!(err, FrameError::Garbage { skipped: 7 });

        // Next call picks up the valid message.
        let frame = reader.next().unwrap().unwrap();
        assert_eq!(frame, msg.as_slice());
    }

    #[test]
    fn garbage_missing_body_length() {
        // 8= present but 9= missing — entire malformed start is garbage.
        let garbage = b"8=FIX.4.4\x0135=0\x01";
        let msg = heartbeat();
        let mut data = garbage.to_vec();
        data.extend_from_slice(&msg);

        let mut reader = FrameReader::builder().build();
        reader.read(&data).unwrap();

        let err = reader.next().unwrap_err();
        assert_eq!(
            err,
            FrameError::Garbage {
                skipped: garbage.len()
            }
        );

        let frame = reader.next().unwrap().unwrap();
        assert_eq!(frame, msg.as_slice());
    }

    #[test]
    fn garbage_invalid_body_length() {
        let garbage = b"8=FIX.4.4\x019=abc\x01";
        let msg = heartbeat();
        let mut data = garbage.to_vec();
        data.extend_from_slice(&msg);

        let mut reader = FrameReader::builder().build();
        reader.read(&data).unwrap();

        let err = reader.next().unwrap_err();
        assert!(matches!(err, FrameError::Garbage { .. }));

        let frame = reader.next().unwrap().unwrap();
        assert_eq!(frame, msg.as_slice());
    }

    #[test]
    fn garbage_body_length_overflow() {
        let garbage = b"8=FIX.4.4\x019=99999999999999999999\x01";
        let msg = heartbeat();
        let mut data = garbage.to_vec();
        data.extend_from_slice(&msg);

        let mut reader = FrameReader::builder().build();
        reader.read(&data).unwrap();

        let err = reader.next().unwrap_err();
        assert!(matches!(err, FrameError::Garbage { .. }));

        let frame = reader.next().unwrap().unwrap();
        assert_eq!(frame, msg.as_slice());
    }

    #[test]
    fn garbage_body_length_addition_overflow() {
        // body_len parses successfully but body_start + body_len + CHECKSUM_LEN
        // overflows usize — must be treated as garbage, not wrap around.
        let val = (usize::MAX - 10).to_string();
        let mut garbage = format!("8=FIX.4.4\x019={val}\x01").into_bytes();
        let msg = heartbeat();
        garbage.extend_from_slice(&msg);

        let mut reader = FrameReader::builder().build();
        reader.read(&garbage).unwrap();

        let err = reader.next().unwrap_err();
        assert!(matches!(err, FrameError::Garbage { .. }));

        let frame = reader.next().unwrap().unwrap();
        assert_eq!(frame, msg.as_slice());
    }

    #[test]
    #[should_panic(expected = "compact_at must be between 0.0 and 1.0")]
    fn compact_at_rejects_invalid() {
        let _ = FrameReader::builder().compact_at(1.5).build();
    }

    #[test]
    fn garbage_all_discarded_when_no_header() {
        let mut reader = FrameReader::builder().build();
        reader.read(b"no valid message here at all").unwrap();

        let err = reader.next().unwrap_err();
        assert_eq!(err, FrameError::Garbage { skipped: 28 });

        assert!(reader.next().unwrap().is_none());
    }

    #[test]
    fn garbage_false_8_equals_keeps_scanning() {
        // `8=` in garbage but not a valid message start. next() will
        // land on it, detect garbage again, then find the real message.
        let msg = heartbeat();
        let mut data = b"XX8=junk\x01".to_vec();
        data.extend_from_slice(&msg);

        let mut reader = FrameReader::builder().build();
        reader.read(&data).unwrap();

        // First next(): skips XX, lands on false 8=.
        let err = reader.next().unwrap_err();
        assert_eq!(err, FrameError::Garbage { skipped: 2 });

        // Second next(): false 8= has no valid 9=, skips to real 8=.
        let err = reader.next().unwrap_err();
        assert!(matches!(err, FrameError::Garbage { .. }));

        // Third next(): real message.
        let frame = reader.next().unwrap().unwrap();
        assert_eq!(frame, msg.as_slice());
    }

    #[test]
    fn garbage_empty_body_length() {
        let garbage = b"8=FIX.4.4\x019=\x01";
        let msg = heartbeat();
        let mut data = garbage.to_vec();
        data.extend_from_slice(&msg);

        let mut reader = FrameReader::builder().build();
        reader.read(&data).unwrap();

        let err = reader.next().unwrap_err();
        assert!(matches!(err, FrameError::Garbage { .. }));

        let frame = reader.next().unwrap().unwrap();
        assert_eq!(frame, msg.as_slice());
    }

    // ---- message too large ----

    #[test]
    fn message_too_large() {
        let mut reader = FrameReader::builder().max_message_size(32).build();
        let msg = new_order(b"ORD-1");
        reader.read(&msg).unwrap();

        let err = reader.next().unwrap_err();
        assert!(matches!(err, FrameError::MessageTooLarge { .. }));

        // Reader advanced past the message.
        assert!(reader.next().unwrap().is_none());
    }

    #[test]
    fn message_too_large_followed_by_valid() {
        let mut data = new_order(b"VERY-LONG-ORDER-ID-THAT-IS-BIG");
        let small = heartbeat();
        data.extend_from_slice(&small);

        let mut reader = FrameReader::builder().max_message_size(50).build();
        reader.read(&data).unwrap();

        let err = reader.next().unwrap_err();
        assert!(matches!(err, FrameError::MessageTooLarge { .. }));

        let frame = reader.next().unwrap().unwrap();
        assert_eq!(frame, small.as_slice());
    }

    // ---- buffer management ----

    #[test]
    fn buffer_full() {
        let mut reader = FrameReader::builder().buffer_capacity(16).build();
        let msg = heartbeat();
        let err = reader.read(&msg).unwrap_err();
        assert!(matches!(err, ReadError::BufferFull { .. }));
    }

    #[test]
    fn compact_reclaims_space() {
        let msg = heartbeat();
        let mut reader = FrameReader::builder()
            .buffer_capacity(msg.len() + 8)
            .build();

        reader.read(&msg).unwrap();
        let _ = reader.next().unwrap().unwrap();

        assert!(reader.next().unwrap().is_none());
        reader.compact();

        reader.read(&msg).unwrap();
        let frame = reader.next().unwrap().unwrap();
        assert_eq!(frame, msg.as_slice());
    }

    #[test]
    fn should_compact_threshold() {
        let m1 = heartbeat();
        let m2 = new_order(b"A");
        let mut reader = FrameReader::builder()
            .buffer_capacity((m1.len() + m2.len()) * 2)
            .compact_at(0.1)
            .build();

        reader.read(&m1).unwrap();
        reader.read(&m2).unwrap();
        assert!(!reader.should_compact());

        let _ = reader.next().unwrap().unwrap();
        let _ = reader.next().unwrap().unwrap();
        assert!(reader.should_compact());
    }

    // ---- FrameWriter ----

    #[test]
    fn writer_encode_and_read_back() {
        let mut writer = FrameWriter::builder().buffer_capacity(4096).build();

        let spare = writer.spare();
        let fmt = nexus_fix_codec::FrameFormatter::new(spare, b"FIX.4.4", b"0");
        let (start, len) = fmt.finish().unwrap();
        writer.commit(start, len);

        assert!(!writer.is_empty());
        assert!(writer.data().starts_with(b"8=FIX.4.4\x01"));
        assert_eq!(writer.data().len(), len);
    }

    #[test]
    fn writer_multiple_messages() {
        let mut writer = FrameWriter::builder().buffer_capacity(4096).build();

        // First message.
        let spare = writer.spare();
        let fmt = nexus_fix_codec::FrameFormatter::new(spare, b"FIX.4.4", b"0");
        let (start, len1) = fmt.finish().unwrap();
        writer.commit(start, len1);

        // Second message.
        let spare = writer.spare();
        let mut fmt = nexus_fix_codec::FrameFormatter::new(spare, b"FIX.4.4", b"D");
        fmt.field(49, b"SENDER");
        fmt.field(11, b"ORD-1");
        let (start, len2) = fmt.finish().unwrap();
        writer.commit(start, len2);

        assert_eq!(writer.data().len(), len1 + len2);

        // Both messages should be valid FIX.
        let data = writer.data();
        assert!(nexus_fix_codec::validate_checksum(&data[..len1]).is_ok());
        assert!(nexus_fix_codec::validate_checksum(&data[len1..]).is_ok());
    }

    #[test]
    fn writer_advance_drains() {
        let mut writer = FrameWriter::builder().buffer_capacity(4096).build();

        let spare = writer.spare();
        let fmt = nexus_fix_codec::FrameFormatter::new(spare, b"FIX.4.4", b"0");
        let (start, len) = fmt.finish().unwrap();
        writer.commit(start, len);

        assert!(!writer.is_empty());
        writer.advance(len);
        assert!(writer.is_empty());
    }

    #[test]
    fn writer_partial_advance() {
        let mut writer = FrameWriter::builder().buffer_capacity(4096).build();

        let spare = writer.spare();
        let fmt = nexus_fix_codec::FrameFormatter::new(spare, b"FIX.4.4", b"0");
        let (start, len) = fmt.finish().unwrap();
        writer.commit(start, len);

        let half = len / 2;
        writer.advance(half);
        assert_eq!(writer.data().len(), len - half);
    }

    #[test]
    fn writer_remaining_decreases() {
        let mut writer = FrameWriter::builder().buffer_capacity(256).build();
        let before = writer.remaining();

        let spare = writer.spare();
        let fmt = nexus_fix_codec::FrameFormatter::new(spare, b"FIX.4.4", b"0");
        let (start, len) = fmt.finish().unwrap();
        writer.commit(start, len);

        assert_eq!(writer.remaining(), before - len);
    }

    #[test]
    fn writer_gap_is_closed() {
        // Use a large buffer so the reservation is wider than needed,
        // producing a nonzero start offset from finish().
        let mut writer = FrameWriter::builder().buffer_capacity(4096).build();

        let spare = writer.spare();
        let fmt = nexus_fix_codec::FrameFormatter::new(spare, b"FIX.4.4", b"0");
        let (start, len) = fmt.finish().unwrap();
        assert!(start > 0, "expected nonzero start from right-alignment");
        writer.commit(start, len);

        // data() should start right at the message — no gap.
        assert!(writer.data().starts_with(b"8=FIX.4.4\x01"));
        assert_eq!(writer.data().len(), len);
    }

    // ---- checksum validation ----

    #[test]
    fn corrupt_checksum_rejected() {
        let mut msg = heartbeat();
        let n = msg.len();
        msg[n - 2] ^= 1; // flip the last checksum digit

        let mut reader = FrameReader::builder().build();
        reader.read(&msg).unwrap();
        let err = reader.next().unwrap_err();
        assert!(
            matches!(err, FrameError::Garbage { .. }),
            "corrupt checksum must be treated as garbage"
        );
    }

    #[test]
    fn valid_checksum_accepted() {
        let msg = heartbeat();
        let mut reader = FrameReader::builder().build();
        reader.read(&msg).unwrap();
        assert!(reader.next().unwrap().is_some());
    }
}
