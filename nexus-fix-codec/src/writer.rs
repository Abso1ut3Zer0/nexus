//! FIX field writer for encoding `tag=value\x01` fields into a buffer.
//!
//! Provides [`FieldWriter`], a cursor that writes FIX fields into a
//! caller-provided `&mut [u8]`. Generated encoders (from `nexus-fix-codegen`)
//! compose this with framing logic for complete message construction.
//!
//! Also provides [`encode_field`] as a standalone function for cases
//! where the struct overhead isn't needed.
//!
//! # Buffer-too-small policy
//!
//! Two layers, two behaviors. [`FrameFormatter`] — the user-facing message builder
//! — **never panics** on a small buffer: an overflowing field poisons the formatter
//! and [`finish`](FrameFormatter::finish) returns [`EncodeError::BufferFull`], so
//! the caller owns the failure. The lower-level primitives ([`encode_field`] and
//! the value-type `encode` methods like [`FixDecimal::encode`](crate::FixDecimal::encode))
//! instead **assert** capacity up front — an internal contract that lets them
//! write without per-byte bounds checks. Generated encoders only ever hand those
//! primitives oversized scratch buffers (see
//! [`MAX_VALUE_ENCODE_LEN`](crate::MAX_VALUE_ENCODE_LEN)), so the asserts are
//! development tripwires, not a reachable failure mode on the happy path.

use crate::EncodeError;

/// FIX field writer.
///
/// Wraps a `&mut [u8]` buffer and tracks the write position as fields
/// are appended. Symmetric with [`FieldReader`](crate::FieldReader)
/// on the read side.
///
/// # Example
///
/// ```
/// use nexus_fix_codec::writer::FieldWriter;
///
/// let mut buf = [0u8; 64];
/// let mut w = FieldWriter::wrap(&mut buf);
/// w.field(35, b"D");
/// w.field(49, b"SENDER");
/// w.field(55, b"BTC-USD");
/// assert_eq!(w.data(), b"35=D\x0149=SENDER\x0155=BTC-USD\x01");
/// ```
pub struct FieldWriter<'a> {
    buf: &'a mut [u8],
    pos: usize,
}

impl<'a> FieldWriter<'a> {
    /// Wrap a mutable buffer for writing FIX fields.
    #[inline]
    pub fn wrap(buf: &'a mut [u8]) -> Self {
        Self { buf, pos: 0 }
    }

    /// Wrap a mutable buffer, starting writes at `offset`.
    #[inline]
    pub fn wrap_at(buf: &'a mut [u8], offset: usize) -> Self {
        Self { buf, pos: offset }
    }

    /// Write a `tag=value\x01` field. Advances position.
    #[inline]
    pub fn field(&mut self, tag: u32, value: &[u8]) {
        self.pos = encode_field(self.buf, self.pos, tag, value);
    }

    /// Current write position (bytes written so far).
    #[inline]
    pub fn pos(&self) -> usize {
        self.pos
    }

    /// The written portion of the buffer.
    #[inline]
    pub fn data(&self) -> &[u8] {
        &self.buf[..self.pos]
    }
}

/// Builds a complete, framed FIX message into a caller-provided buffer.
///
/// Owns the framing the wire mandates — `8=BeginString`, `9=BodyLength`,
/// `10=CheckSum` — so the caller only writes body fields and can never get
/// BodyLength or the checksum wrong. Body fields stream forward; the
/// `8=…9=…` prefix is filled in **right-aligned** at [`finish`](Self::finish)
/// once the body length is known, so the body never moves and BodyLength is
/// **canonical** (no leading zeros). The default reservation in [`new`](Self::new)
/// is sized so the right-aligned write never shifts; [`with_reserved`](Self::with_reserved)
/// trades that for a caller-chosen prefix size and shifts only if undersized.
///
/// On overflow the writer is poisoned (further writes are dropped) and
/// [`finish`](Self::finish) returns [`EncodeError::BufferFull`]
/// — encoding never panics on a too-small buffer.
///
/// # Example
///
/// ```
/// use nexus_fix_codec::FrameFormatter;
///
/// let mut buf = [0u8; 128];
/// let mut f = FrameFormatter::new(&mut buf, b"FIX.4.4", b"D"); // 8=, reserve 9=, 35=D
/// f.field(49, b"SENDER");
/// f.field(56, b"TARGET");
/// f.field(11, b"ORD-1");
/// let (start, len) = f.finish().unwrap();
/// let msg = &buf[start..start + len];
/// assert!(msg.starts_with(b"8=FIX.4.4\x019="));
/// assert!(nexus_fix_codec::validate_checksum(msg).is_ok());
/// ```
pub struct FrameFormatter<'buf> {
    buf: &'buf mut [u8],
    begin_string: &'static [u8],
    /// Start of the body-length-counted region (after the reserved prefix).
    content: usize,
    /// Write cursor within the content region.
    pos: usize,
    /// Sticky overflow flag — once set, writes are dropped and `finish` errors.
    full: bool,
}

impl<'buf> FrameFormatter<'buf> {
    /// Begin a message: reserve the front prefix and write `35=<msg_type>`.
    ///
    /// The reservation defaults to the widest the `8=…9=…` prefix could need
    /// for this buffer (BodyLength can't exceed the buffer), so the
    /// right-aligned write at [`finish`](Self::finish) never shifts the body.
    #[inline]
    pub fn new(buf: &'buf mut [u8], begin_string: &'static [u8], msg_type: &[u8]) -> Self {
        let reserved = prefix_capacity(begin_string.len(), buf.len());
        Self::with_reserved(buf, begin_string, msg_type, reserved)
    }

    /// As [`new`](Self::new) but with an explicit prefix reservation (bytes for
    /// the `8=…9=…` prefix). If the body grows past what the reservation can
    /// hold, [`finish`](Self::finish) shifts the content to make room; the
    /// default in [`new`](Self::new) is sized so that never happens.
    #[inline]
    pub fn with_reserved(
        buf: &'buf mut [u8],
        begin_string: &'static [u8],
        msg_type: &[u8],
        reserved: usize,
    ) -> Self {
        let full = reserved > buf.len();
        let mut f = Self {
            content: reserved,
            pos: reserved,
            begin_string,
            full,
            buf,
        };
        f.field(35, msg_type);
        f
    }

    /// Append a `tag=value` body field. Poisons the writer if it won't fit.
    #[inline]
    pub fn field(&mut self, tag: u32, value: &[u8]) {
        if self.full {
            return;
        }
        let need = tag_digits(tag) + 2 + value.len();
        if need > self.buf.len() - self.pos {
            self.full = true;
            return;
        }
        self.pos = encode_field(self.buf, self.pos, tag, value);
    }

    /// Whether a write has overflowed the buffer (so [`finish`](Self::finish)
    /// will return [`EncodeError::BufferFull`]).
    #[inline]
    pub fn is_full(&self) -> bool {
        self.full
    }

    /// Finish the message: write `8=…9=<canonical>` and append the checksum.
    ///
    /// Returns `(start, len)` — the byte offset and length of the finished
    /// message within the buffer. The message is at `buf[start..start + len]`.
    ///
    /// # Errors
    /// [`EncodeError::BufferFull`] if any field,
    /// the prefix, or the checksum did not fit.
    pub fn finish(mut self) -> Result<(usize, usize), EncodeError> {
        if self.full {
            return Err(EncodeError::BufferFull);
        }
        let body_len = self.pos - self.content;

        // Canonical BodyLength digits (no leading zeros).
        let mut bl = [0u8; 10];
        let bl_n = crate::encode_fix_uint(body_len as u32, &mut bl);

        // prefix = "8=" + begin_string + SOH + "9=" + <bodylen> + SOH
        let prefix_len = 2 + self.begin_string.len() + 1 + 2 + bl_n + 1;

        let start = if prefix_len <= self.content {
            // Default path: right-align into the reservation, nothing moves.
            self.content - prefix_len
        } else {
            // Under-reserved: shift the content right to make prefix room.
            let shift = prefix_len - self.content;
            if shift + self.pos > self.buf.len() {
                return Err(EncodeError::BufferFull);
            }
            self.buf.copy_within(self.content..self.pos, prefix_len);
            self.pos += shift;
            0
        };

        // Checksum trailer "10=" + 3 digits + SOH = 7 bytes.
        if 7 > self.buf.len() - self.pos {
            return Err(EncodeError::BufferFull);
        }

        // Write the prefix right before the content region.
        let p = encode_field(self.buf, start, 8, self.begin_string);
        let p = encode_field(self.buf, p, 9, &bl[..bl_n]);
        debug_assert_eq!(p, start + prefix_len, "prefix must abut the content");

        // Checksum covers everything from `8=` up to (not including) `10=`.
        let sum = crate::checksum(&self.buf[start..self.pos]);
        let end = encode_field(self.buf, self.pos, 10, &format_checksum(sum));
        Ok((start, end - start))
    }
}

/// Resume an encoder stage from an in-progress [`FrameFormatter`].
///
/// Generated message encoders implement this so the venue-shared header encoder
/// can return control to the per-message body stage when its `end()` is called,
/// without the header encoder needing to name the concrete message type. It's
/// the typestate handoff: header writer → message body writer, carrying the
/// buffer along.
pub trait FromFormatter<'buf> {
    /// Resume encoding from `frame`.
    fn from_formatter(frame: FrameFormatter<'buf>) -> Self;
}

/// Widest the `8=…9=…` prefix can be for a buffer of `buf_len` bytes: the `8=`
/// tag, the BeginString, an SOH, `9=`, the most BodyLength digits the buffer
/// could ever need (BodyLength < buf_len), and the trailing SOH.
#[inline]
fn prefix_capacity(begin_len: usize, buf_len: usize) -> usize {
    2 + begin_len + 1 + 2 + dec_digits(buf_len) + 1
}

/// Number of decimal digits in `n` (`0` → 1).
#[inline]
fn dec_digits(mut n: usize) -> usize {
    let mut d = 1;
    while n >= 10 {
        n /= 10;
        d += 1;
    }
    d
}

/// Write a `tag=value\x01` field into `buf` at `pos`. Returns new position.
///
/// This is the standalone version of [`FieldWriter::field`] for use
/// without the struct wrapper.
///
/// # Panics
///
/// Panics if `buf` is too small to hold the encoded field
/// (`pos + tag_digits + 1 + value.len() + 1` bytes). The capacity is
/// checked once up front; on success every byte is written without
/// further per-byte bounds checks.
#[inline]
pub fn encode_field(buf: &mut [u8], pos: usize, tag: u32, value: &[u8]) -> usize {
    let digits = tag_digits(tag);
    // Bytes this field needs: `digits` tag bytes + `=` + value + SOH. Computed
    // without overflow — `digits <= 10` and `value.len() <= isize::MAX`, so the
    // sum stays below `usize::MAX`. The `pos <= buf.len()` guard is checked
    // first so `buf.len() - pos` cannot underflow.
    let need = digits + 2 + value.len();
    assert!(
        pos <= buf.len() && need <= buf.len() - pos,
        "encode_field: buffer too small (need {need} at pos {pos}, have {})",
        buf.len()
    );

    // SAFETY: the assert guarantees `pos + need <= buf.len()`. Every write below
    // lands in `pos..pos + need`: `digits` tag bytes, the `=`, `value.len()`
    // value bytes, then the trailing SOH — so all indices are in bounds.
    // `value` is a `&[u8]` and `buf` a `&mut [u8]`; the borrow checker forbids
    // them from aliasing, so the copy is genuinely non-overlapping.
    unsafe {
        write_tag_unchecked(buf, pos, tag, digits);
        let mut p = pos + digits;
        *buf.get_unchecked_mut(p) = b'=';
        p += 1;
        core::ptr::copy_nonoverlapping(value.as_ptr(), buf.as_mut_ptr().add(p), value.len());
        p += value.len();
        *buf.get_unchecked_mut(p) = 0x01;
        p + 1
    }
}

/// Format a checksum value as 3 zero-padded ASCII digits.
///
/// FIX tag 10 is always a 3-character zero-padded decimal value.
///
/// # Example
///
/// ```
/// use nexus_fix_codec::writer::format_checksum;
///
/// assert_eq!(&format_checksum(42), b"042");
/// assert_eq!(&format_checksum(178), b"178");
/// ```
#[inline]
pub fn format_checksum(sum: u8) -> [u8; 3] {
    [sum / 100 + b'0', (sum / 10) % 10 + b'0', sum % 10 + b'0']
}

// =============================================================================
// Internal: tag number → ASCII digits
// =============================================================================

/// Number of ASCII digits needed to represent `tag`.
///
/// FIX tags are always `>= 1`; tag `0` still reports one digit so the
/// encoding round-trips. When `tag` is a compile-time constant (the
/// generated-encoder case), this folds to a constant and the caller's
/// length math and digit writes collapse to straight-line stores.
#[inline]
fn tag_digits(tag: u32) -> usize {
    match tag {
        0..=9 => 1,
        10..=99 => 2,
        100..=999 => 3,
        1_000..=9_999 => 4,
        10_000..=99_999 => 5,
        100_000..=999_999 => 6,
        1_000_000..=9_999_999 => 7,
        10_000_000..=99_999_999 => 8,
        100_000_000..=999_999_999 => 9,
        _ => 10,
    }
}

/// Write `tag` as exactly `digits` ASCII characters starting at `pos`.
///
/// # Safety
///
/// `buf[pos..pos + digits]` must be in bounds, and `digits` must equal
/// `tag_digits(tag)` so the value fits exactly in the written span.
#[inline]
unsafe fn write_tag_unchecked(buf: &mut [u8], pos: usize, tag: u32, digits: usize) {
    // Internal contract, guaranteed by construction in `encode_field` and
    // proven by its capacity assert. Debug-only: a development tripwire, not a
    // release-time guard (those would belong on external input, not here).
    debug_assert_eq!(digits, tag_digits(tag), "digit count must match tag width");
    debug_assert!(
        pos + digits <= buf.len(),
        "tag write span must be in bounds"
    );

    let mut t = tag;
    let mut i = pos + digits;
    // Least-significant digit first, walking back to `pos`. Trip count is
    // `digits` (constant when `tag` is constant), so no data-dependent exit.
    while i > pos {
        i -= 1;
        // SAFETY: `i` ranges over `pos..pos + digits`, in bounds by precondition.
        unsafe {
            *buf.get_unchecked_mut(i) = b'0' + (t % 10) as u8;
        }
        t /= 10;
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn single_field() {
        let mut buf = [0u8; 32];
        let end = encode_field(&mut buf, 0, 35, b"D");
        assert_eq!(&buf[..end], b"35=D\x01");
    }

    #[test]
    fn multiple_fields() {
        let mut buf = [0u8; 64];
        let mut pos = 0;
        pos = encode_field(&mut buf, pos, 8, b"FIX.4.4");
        pos = encode_field(&mut buf, pos, 35, b"D");
        pos = encode_field(&mut buf, pos, 49, b"SENDER");
        assert_eq!(&buf[..pos], b"8=FIX.4.4\x0135=D\x0149=SENDER\x01");
    }

    #[test]
    fn all_tag_widths() {
        let cases: &[(u32, &[u8])] = &[
            (8, b"8=v\x01"),
            (35, b"35=v\x01"),
            (150, b"150=v\x01"),
            (5592, b"5592=v\x01"),
            (10000, b"10000=v\x01"),
        ];
        for &(tag, expected) in cases {
            let mut buf = [0u8; 16];
            let end = encode_field(&mut buf, 0, tag, b"v");
            assert_eq!(&buf[..end], expected, "tag={}", tag);
        }
    }

    #[test]
    fn empty_value() {
        let mut buf = [0u8; 16];
        let end = encode_field(&mut buf, 0, 35, b"");
        assert_eq!(&buf[..end], b"35=\x01");
    }

    #[test]
    fn exact_fit_buffer() {
        // "35=D\x01" is exactly 5 bytes — no slack.
        let mut buf = [0u8; 5];
        let end = encode_field(&mut buf, 0, 35, b"D");
        assert_eq!(&buf[..end], b"35=D\x01");
    }

    #[test]
    #[should_panic(expected = "buffer too small")]
    fn panics_when_too_small() {
        let mut buf = [0u8; 4]; // needs 5 for "35=D\x01"
        encode_field(&mut buf, 0, 35, b"D");
    }

    #[test]
    #[should_panic(expected = "buffer too small")]
    fn panics_when_pos_past_end() {
        let mut buf = [0u8; 8];
        encode_field(&mut buf, 9, 35, b"D");
    }

    #[test]
    fn wide_tag_widths_roundtrip() {
        // tag_digits boundaries: every width writes the exact digit count.
        for &(tag, expected) in &[
            (9u32, "9"),
            (99, "99"),
            (999, "999"),
            (9_999, "9999"),
            (99_999, "99999"),
            (999_999, "999999"),
            (4_294_967_295, "4294967295"), // u32::MAX, 10 digits
        ] {
            let mut buf = [0u8; 32];
            let end = encode_field(&mut buf, 0, tag, b"v");
            let want = format!("{expected}=v\u{1}");
            assert_eq!(&buf[..end], want.as_bytes(), "tag={tag}");
        }
    }

    #[test]
    fn encode_from_offset() {
        let mut buf = [0u8; 32];
        buf[0..5].copy_from_slice(b"XXXXX");
        let end = encode_field(&mut buf, 5, 35, b"D");
        assert_eq!(&buf[5..end], b"35=D\x01");
    }

    #[test]
    fn format_checksum_values() {
        assert_eq!(&format_checksum(0), b"000");
        assert_eq!(&format_checksum(42), b"042");
        assert_eq!(&format_checksum(178), b"178");
        assert_eq!(&format_checksum(255), b"255");
    }

    #[test]
    fn writer_basic() {
        let mut buf = [0u8; 64];
        let mut w = FieldWriter::wrap(&mut buf);
        w.field(35, b"D");
        w.field(49, b"SENDER");
        assert_eq!(w.pos(), 15);
        assert_eq!(w.data(), b"35=D\x0149=SENDER\x01");
    }

    #[test]
    fn writer_wrap_at() {
        let mut buf = [0u8; 64];
        let mut w = FieldWriter::wrap_at(&mut buf, 10);
        w.field(35, b"D");
        assert_eq!(w.pos(), 15);
        assert_eq!(&buf[10..15], b"35=D\x01");
    }

    #[test]
    fn roundtrip_read_write() {
        let mut buf = [0u8; 128];
        let mut w = FieldWriter::wrap(&mut buf);
        w.field(8, b"FIX.4.4");
        w.field(35, b"D");
        w.field(49, b"SENDER");
        w.field(55, b"BTC-USD");
        let written = w.pos();

        let mut reader = crate::FieldReader::new(&buf[..written], 0);
        let fields: Vec<_> = reader.by_ref().collect();

        assert_eq!(fields.len(), 4);
        assert_eq!(fields[0].tag, 8);
        assert_eq!(fields[0].value.slice(&buf), b"FIX.4.4");
        assert_eq!(fields[1].tag, 35);
        assert_eq!(fields[1].value.slice(&buf), b"D");
        assert_eq!(fields[2].tag, 49);
        assert_eq!(fields[2].value.slice(&buf), b"SENDER");
        assert_eq!(fields[3].tag, 55);
        assert_eq!(fields[3].value.slice(&buf), b"BTC-USD");
    }

    #[test]
    fn long_value() {
        let value = "X".repeat(200);
        let mut buf = [0u8; 256];
        let end = encode_field(&mut buf, 0, 1, value.as_bytes());
        let expected = format!("1={}\x01", value);
        assert_eq!(&buf[..end], expected.as_bytes());
    }

    #[test]
    fn tag_zero() {
        let mut buf = [0u8; 16];
        let end = encode_field(&mut buf, 0, 0, b"v");
        assert_eq!(&buf[..end], b"0=v\x01");
    }

    #[test]
    fn roundtrip_with_checksum_validation() {
        let mut buf = [0u8; 128];
        let body_end;
        {
            let mut w = FieldWriter::wrap(&mut buf);
            w.field(8, b"FIX.4.4");
            w.field(9, b"42");
            w.field(35, b"D");
            w.field(49, b"SENDER");
            w.field(56, b"TARGET");
            body_end = w.pos();
        }

        let sum = crate::checksum(&buf[..body_end]);
        let msg_end = encode_field(&mut buf, body_end, 10, &crate::writer::format_checksum(sum));

        assert!(crate::validate_checksum(&buf[..msg_end]).is_ok());
    }

    #[test]
    fn writer_with_checksum() {
        let mut buf = [0u8; 128];
        let body_end;
        {
            let mut w = FieldWriter::wrap(&mut buf);
            w.field(35, b"D");
            w.field(49, b"SENDER");
            body_end = w.pos();
        }

        let sum = crate::checksum(&buf[..body_end]);
        let msg_end = encode_field(&mut buf, body_end, 10, &format_checksum(sum));

        assert!(buf[body_end..msg_end].starts_with(b"10="));
        assert_eq!(buf[msg_end - 1], 0x01);
    }

    // ---- FrameFormatter ----

    #[test]
    fn frame_basic_roundtrips() {
        let mut buf = [0u8; 128];
        let mut f = FrameFormatter::new(&mut buf, b"FIX.4.4", b"D");
        f.field(49, b"SENDER");
        f.field(56, b"TARGET");
        f.field(11, b"ORD-1");
        let (start, len) = f.finish().unwrap();
        let msg = &buf[start..start + len];

        assert!(msg.starts_with(b"8=FIX.4.4\x019="));
        assert!(crate::validate_checksum(msg).is_ok());

        let mut r = crate::FieldReader::new(msg, 0);
        let fields: Vec<_> = r.by_ref().collect();
        let tags: Vec<u32> = fields.iter().map(|f| f.tag).collect();
        assert_eq!(tags, vec![8, 9, 35, 49, 56, 11, 10]);

        // BodyLength = bytes of 35=…11=…  →  5 + 10 + 10 + 9 = 34, canonical.
        let nine = fields.iter().find(|f| f.tag == 9).unwrap();
        assert_eq!(nine.value.slice(msg), b"34");
    }

    #[test]
    fn frame_bodylength_is_canonical() {
        // Small body → BodyLength has fewer digits than the reservation;
        // the value must still be canonical (no leading zeros).
        let mut buf = [0u8; 4096];
        let mut f = FrameFormatter::new(&mut buf, b"FIX.4.4", b"0");
        f.field(112, b"HB");
        let (start, len) = f.finish().unwrap();
        let msg = &buf[start..start + len];

        let mut r = crate::FieldReader::new(msg, 0);
        let fields: Vec<_> = r.by_ref().collect();
        let nine = fields.iter().find(|f| f.tag == 9).unwrap().value.slice(msg);
        assert_ne!(nine[0], b'0', "BodyLength must not have leading zeros");
        assert!(crate::validate_checksum(msg).is_ok());
    }

    #[test]
    fn frame_starts_past_offset_zero() {
        // A wider buffer reserves a wider prefix; a small body right-aligns
        // into it, so the message starts a few bytes in (no shift, body never
        // moved). buf.len() has 4 digits, the body's BodyLength only 2.
        let mut buf = [0u8; 1024];
        let mut f = FrameFormatter::new(&mut buf, b"FIX.4.4", b"D");
        f.field(11, b"A");
        let (start, len) = f.finish().unwrap();
        assert!(start > 0, "right-aligned prefix should start past offset 0");
        let msg = &buf[start..start + len];
        assert!(crate::validate_checksum(msg).is_ok());
        assert!(msg.starts_with(b"8=FIX.4.4\x019="));
    }

    #[test]
    fn frame_formatter_checksum_is_last_field() {
        // The CheckSum (tag 10) must always be the final field — the invariant
        // `validate_checksum`'s positional lookup relies on.
        let mut buf = [0u8; 1024];
        let mut f = FrameFormatter::new(&mut buf, b"FIX.4.4", b"D");
        f.field(49, b"SENDER");
        f.field(56, b"TARGET");
        f.field(34, b"1");
        let (start, len) = f.finish().unwrap();
        let msg = &buf[start..start + len];

        // The trailing bytes are exactly `10=DDD\x01`, and our own reader agrees
        // the final field is tag 10.
        assert_eq!(&msg[len - 7..len - 4], b"10=");
        assert_eq!(msg[len - 1], b'\x01');
        assert_eq!(crate::FieldReader::new(msg, 0).last().unwrap().tag, 10);
        assert!(crate::validate_checksum(msg).is_ok());
    }

    #[test]
    fn frame_buffer_full_no_panic() {
        // Too small even for the prefix — must error, never panic.
        let mut buf = [0u8; 8];
        let mut f = FrameFormatter::new(&mut buf, b"FIX.4.4", b"D");
        f.field(49, b"SENDER");
        assert_eq!(f.finish(), Err(crate::EncodeError::BufferFull));
    }

    #[test]
    fn frame_field_overflow_poisons() {
        // The body overruns mid-write → poisoned → BufferFull at finish.
        let mut buf = [0u8; 32];
        let mut f = FrameFormatter::new(&mut buf, b"FIX.4.4", b"D");
        f.field(11, b"THIS-IS-A-VERY-LONG-CLORDID-THAT-WONT-FIT");
        assert!(f.is_full());
        assert_eq!(f.finish(), Err(crate::EncodeError::BufferFull));
    }

    #[test]
    fn frame_undersized_reservation_shifts_and_stays_valid() {
        // Reserve room for a 1-digit BodyLength, then write a body that needs
        // two digits → finish() shifts the content to make prefix room.
        let mut buf = [0u8; 128];
        let mut f = FrameFormatter::with_reserved(&mut buf, b"FIX.4.4", b"D", 14);
        f.field(49, b"SENDER");
        f.field(56, b"TARGET");
        let (start, len) = f.finish().unwrap();
        let msg = &buf[start..start + len];

        assert!(crate::validate_checksum(msg).is_ok());
        let mut r = crate::FieldReader::new(msg, 0);
        let fields: Vec<_> = r.by_ref().collect();
        let nine = fields.iter().find(|f| f.tag == 9).unwrap().value.slice(msg);
        assert_ne!(nine[0], b'0');
        // shifted to the front
        assert!(msg.starts_with(b"8=FIX.4.4\x01"));
    }
}
