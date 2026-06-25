//! FIX field reader with SIMD-accelerated SOH scanning.
//!
//! A pure SOH-delimiter scanner: each SIMD chunk load runs one `cmpeq` against
//! `\x01` to find field boundaries. The FIX checksum is a separate concern,
//! computed in a single contiguous pass at verification time, so a trusted feed
//! can skip it entirely and pay nothing.
//!
//! Dispatch cascade (widest first, remainder flows down):
//!
//! - AVX-512: 64 bytes/iter (`target_feature = "avx512bw"`)
//! - AVX2: 32 bytes/iter (`target_feature = "avx2"`)
//! - SSE2: 16 bytes/iter (baseline x86_64)
//! - SWAR: 8 bytes/iter (all platforms)
//! - Scalar: byte-by-byte tail

use crate::FieldSpan;
use crate::error::ChecksumError;

#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::*;

const HI: u64 = 0x8080_8080_8080_8080;
const LO: u64 = 0x0101_0101_0101_0101;

/// A parsed FIX field: tag number and value span.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct RawField {
    pub tag: u32,
    pub value: FieldSpan,
}

/// FIX field reader: a pure SOH-delimited field scanner.
///
/// Iterates over `tag=value\x01` fields, yielding [`RawField`] pairs. The reader
/// tracks position only; the FIX checksum is computed separately by a single
/// contiguous pass ([`checksum`] / [`verify_checksum`](Self::verify_checksum)),
/// so a caller that trusts its feed can skip verification entirely.
///
/// # Example
///
/// ```
/// use nexus_fix_codec::reader::FieldReader;
///
/// let msg = b"8=FIX.4.4\x0135=D\x0149=SENDER\x01";
/// let mut parser = FieldReader::new(msg, 0);
///
/// while let Some(field) = parser.next_field() {
///     // field.tag, field.value
/// }
/// ```
pub struct FieldReader<'a> {
    buf: &'a [u8],
    scan_pos: usize,
    field_start: usize,
    soh_mask: u64,
    mask_base: usize,
}

impl<'a> FieldReader<'a> {
    #[inline]
    pub fn new(buf: &'a [u8], start: usize) -> Self {
        Self {
            buf,
            scan_pos: start,
            field_start: start,
            soh_mask: 0,
            mask_base: 0,
        }
    }

    /// Consume a length-prefixed DATA field.
    ///
    /// `len` is the value byte count, excluding the terminating SOH. Returns
    /// `InvalidLength` if `len == 0`, `Truncated` if the SOH is absent or the
    /// buffer is too short.
    #[inline]
    pub fn next_data_field(&mut self, len: usize) -> Result<RawField, crate::DecodeError> {
        if len == 0 {
            return Err(crate::DecodeError::InvalidLength);
        }
        let field_start = self.field_start;
        let (tag, tag_len) = parse_tag(self.buf.get(field_start..).unwrap_or(b""));
        if tag_len == 0 {
            return Err(crate::DecodeError::InvalidTag);
        }
        if self.buf.get(field_start + tag_len) != Some(&b'=') {
            return Err(crate::DecodeError::MissingSeparator);
        }
        let value_start = field_start + tag_len + 1;
        let remaining = self.buf.len().saturating_sub(value_start);
        if len > remaining {
            return Err(crate::DecodeError::Truncated);
        }
        let data_end = value_start + len;
        if self.buf.get(data_end) != Some(&b'\x01') {
            return Err(crate::DecodeError::Truncated);
        }
        let span = FieldSpan::new(value_start as u32, len as u32);
        self.resync_after_data(data_end + 1);
        Ok(RawField { tag, value: span })
    }

    /// Resume scanning at `data_end`, having consumed a length-prefixed DATA
    /// field whose value may contain SOH bytes.
    ///
    /// A DATA field can't be SOH-scanned (its value contains SOH), so generated
    /// decoders compute its end from the preceding length and jump past it. The
    /// reader is a pure position tracker, so this is a plain reposition — no
    /// checksum bookkeeping. The DATA bytes are still covered by the standalone
    /// checksum pass ([`verify_checksum`](Self::verify_checksum)), which sums a
    /// contiguous range and is oblivious to embedded SOH.
    #[inline]
    pub fn resync_after_data(&mut self, data_end: usize) {
        let end = data_end.min(self.buf.len());
        self.field_start = end;
        self.scan_pos = end;
        self.soh_mask = 0;
        self.mask_base = 0;
    }

    /// The underlying message buffer.
    #[inline]
    pub fn buf(&self) -> &'a [u8] {
        self.buf
    }

    /// Where the next field would start (after the last SOH + 1).
    #[inline]
    pub fn pos(&self) -> usize {
        self.field_start
    }

    /// Verify the FIX checksum against the tag 10 (`CheckSum`) field value.
    ///
    /// Computes the checksum in a single contiguous pass over every byte before
    /// the `10=` field (the FIX checksum covers `8=…` through the byte before
    /// `10=`), parses the declared 3-digit value, and compares. `checksum_span`
    /// is the *value* span of tag 10, so the field begins three bytes earlier
    /// (`10=`).
    ///
    /// This is the verification half of the two-axis decode: a trusted feed can
    /// skip it (decode_unchecked) and pay nothing.
    pub fn verify_checksum(&self, checksum_span: FieldSpan) -> Result<(), ChecksumError> {
        let body_end = (checksum_span.offset as usize).saturating_sub(3);
        let computed = checksum(&self.buf[..body_end.min(self.buf.len())]);
        match parse_checksum_bytes(checksum_span.slice(self.buf)) {
            Some(expected) if expected == computed => Ok(()),
            Some(expected) => Err(ChecksumError { expected, computed }),
            // Malformed CheckSum field (not three digits): reject regardless of
            // `computed`. `expected` is a placeholder — there is no valid value.
            None => Err(ChecksumError {
                expected: 0,
                computed,
            }),
        }
    }

    /// Parse the next `tag=value\x01` field.
    ///
    /// Returns `None` at end of buffer or if the remaining bytes
    /// contain no valid `tag=value\x01` structure.
    #[inline]
    pub fn next_field(&mut self) -> Option<RawField> {
        let field_start = self.field_start;
        let soh_pos = self.next_soh()?;
        self.field_start = soh_pos + 1;

        let field_bytes = self.buf.get(field_start..soh_pos)?;
        let (tag, tag_len) = parse_tag(field_bytes);

        if tag_len == 0 || tag_len >= field_bytes.len() || field_bytes[tag_len] != b'=' {
            return None;
        }

        let value_start = field_start + tag_len + 1;
        let value_len = soh_pos - value_start;

        Some(RawField {
            tag,
            value: FieldSpan::new(value_start as u32, value_len as u32),
        })
    }

    /// Read the next field **only if** its tag satisfies `pred` — a forward-only
    /// boundary peek.
    ///
    /// The tag sits at the cursor (right after the previous SOH), so it is read
    /// locally — no scan to *this* field's terminating SOH. If `pred(tag)` is
    /// false the reader is left **completely untouched** (no scan, no advance),
    /// so the next consumer reads the same field. This is how the header→body
    /// and group boundaries hand off with no over-read, stash, or re-scan: the
    /// boundary field's SOH is scanned exactly once, by whoever keeps it.
    #[inline]
    pub fn next_field_if(&mut self, pred: impl Fn(u32) -> bool) -> Option<RawField> {
        let field_start = self.field_start;
        // Peek the tag locally (digits before `=`); does not touch the SOH scan.
        let (tag, tag_len) = parse_tag(self.buf.get(field_start..)?);
        if tag_len == 0 || !pred(tag) {
            return None;
        }
        // Kept: commit — now scan to the SOH, validate, and advance.
        let soh_pos = self.next_soh()?;
        self.field_start = soh_pos + 1;

        let field_bytes = self.buf.get(field_start..soh_pos)?;
        if tag_len >= field_bytes.len() || field_bytes[tag_len] != b'=' {
            return None;
        }

        let value_start = field_start + tag_len + 1;
        let value_len = soh_pos - value_start;

        Some(RawField {
            tag,
            value: FieldSpan::new(value_start as u32, value_len as u32),
        })
    }
}

impl Iterator for FieldReader<'_> {
    type Item = RawField;

    #[inline]
    fn next(&mut self) -> Option<RawField> {
        self.next_field()
    }
}

// =============================================================================
// Tag number parsing
// =============================================================================

/// Parse a FIX tag number from ASCII digits.
///
/// Reads sequential digits from the start of `buf` until a non-digit
/// byte or end of buffer. Returns `(tag_number, digits_consumed)`.
#[inline]
pub fn parse_tag(buf: &[u8]) -> (u32, usize) {
    let mut tag = 0u32;
    let mut i = 0;
    while i < buf.len() && buf[i] >= b'0' && buf[i] <= b'9' {
        tag = tag
            .saturating_mul(10)
            .saturating_add((buf[i] - b'0') as u32);
        i += 1;
    }
    (tag, i)
}

// =============================================================================
// Standalone helpers
// =============================================================================

/// Compute the FIX checksum: byte sum mod 256.
///
/// Simple scalar sum — useful for encoder checksum computation
/// and anywhere a standalone checksum is needed without a full parse.
///
/// Uses `wrapping_add` because only the low 8 bits matter (the
/// result is mod 256), so intermediate overflow is harmless and
/// the function accepts any input length without debug panics.
#[inline]
pub fn checksum(data: &[u8]) -> u8 {
    data.iter().fold(0u32, |acc, &b| acc.wrapping_add(b as u32)) as u8
}

/// Find the first field with a specific tag number.
///
/// Scans from `start` using [`FieldReader`], returning the value
/// [`FieldSpan`] of the first field with matching tag number.
#[inline]
pub fn find_tag(buf: &[u8], start: usize, tag: u32) -> Option<FieldSpan> {
    FieldReader::new(buf, start)
        .find(|f| f.tag == tag)
        .map(|f| f.value)
}

/// Validate a FIX message checksum against tag 10.
///
/// Scans for the tag 10 (`CheckSum`) field, then verifies via a single
/// contiguous checksum pass over the preceding bytes.
///
/// Returns `Ok(())` if valid, `Err(ChecksumError)` on mismatch.
/// Returns `Ok(())` if tag 10 is absent (nothing to validate
/// against — structural validation is the decoder's job).
pub fn validate_checksum(msg: &[u8]) -> Result<(), ChecksumError> {
    let mut parser = FieldReader::new(msg, 0);
    let mut expected_span = None;

    while let Some(field) = parser.next_field() {
        if field.tag == 10 {
            expected_span = Some(field.value);
        }
    }

    expected_span.map_or(Ok(()), |span| parser.verify_checksum(span))
}

/// Parse a FIX CheckSum (tag 10) value: exactly three ASCII digits.
///
/// Returns `None` for anything else. A malformed CheckSum must be rejected
/// deterministically — silently coercing it to `0` could collide with a
/// genuine `0` computed checksum and false-accept an invalid message.
fn parse_checksum_bytes(bytes: &[u8]) -> Option<u8> {
    if bytes.len() != 3 {
        return None;
    }
    let mut val = 0u32;
    for &b in bytes {
        let digit = b.wrapping_sub(b'0');
        if digit > 9 {
            return None;
        }
        val = val * 10 + digit as u32;
    }
    Some((val & 0xFF) as u8)
}

// =============================================================================
// SOH scanning
// =============================================================================

impl FieldReader<'_> {
    #[inline(always)]
    fn emit_soh_mask(&mut self, mask: u64, chunk_offset: usize, chunk_size: usize) -> usize {
        self.mask_base = self.scan_pos + chunk_offset;
        self.scan_pos = self.scan_pos + chunk_offset + chunk_size;
        self.soh_mask = mask;
        let bit = self.soh_mask.trailing_zeros() as usize;
        self.soh_mask &= self.soh_mask - 1;
        self.mask_base + bit
    }

    /// Yield the next SOH position.
    ///
    /// Fast path (the common case): drain a bit from the cached chunk mask —
    /// a handful of register-resident instructions when inlined into the
    /// caller, no `call`, no checksum touch. Slow path: a SIMD chunk needs
    /// (re)loading, delegated to the out-of-line [`scan_next_soh`].
    #[inline(always)]
    fn next_soh(&mut self) -> Option<usize> {
        if self.soh_mask != 0 {
            let bit = self.soh_mask.trailing_zeros() as usize;
            self.soh_mask &= self.soh_mask - 1;
            return Some(self.mask_base + bit);
        }
        self.scan_next_soh()
    }

    /// Cold path: load and scan SIMD chunks for the next SOH, caching the
    /// delimiter mask for [`next_soh`] to drain. Kept out-of-line and `#[cold]`
    /// so the per-field fast path above stays inlined and the reader's scan state
    /// stays in registers across cached-mask drains, instead of being spilled
    /// around a per-field `call`.
    #[cold]
    #[inline(never)]
    fn scan_next_soh(&mut self) -> Option<usize> {
        let bytes = self.buf.get(self.scan_pos..)?;
        if bytes.is_empty() {
            return None;
        }

        let mut i = 0;

        // ---- x86_64 SIMD tiers (widest first) ----
        #[cfg(target_arch = "x86_64")]
        {
            // SAFETY: target_feature cfgs guarantee SIMD instruction availability.
            // All pointer arithmetic is bounds-checked by the while conditions.
            unsafe {
                #[cfg(target_feature = "avx512bw")]
                {
                    let soh = _mm512_set1_epi8(0x01_i8);
                    while i + 64 <= bytes.len() {
                        let chunk = _mm512_loadu_si512(bytes.as_ptr().add(i).cast());
                        let m = _mm512_cmpeq_epi8_mask(chunk, soh);
                        if m != 0 {
                            return Some(self.emit_soh_mask(m, i, 64));
                        }
                        i += 64;
                    }
                }

                #[cfg(target_feature = "avx2")]
                {
                    let soh = _mm256_set1_epi8(0x01_i8);
                    while i + 32 <= bytes.len() {
                        let chunk = _mm256_loadu_si256(bytes.as_ptr().add(i).cast());
                        let m = _mm256_movemask_epi8(_mm256_cmpeq_epi8(chunk, soh)) as u32 as u64;
                        if m != 0 {
                            return Some(self.emit_soh_mask(m, i, 32));
                        }
                        i += 32;
                    }
                }

                // SSE2 — baseline on x86_64
                {
                    let soh = _mm_set1_epi8(0x01_i8);
                    while i + 16 <= bytes.len() {
                        let chunk = _mm_loadu_si128(bytes.as_ptr().add(i).cast());
                        let m = _mm_movemask_epi8(_mm_cmpeq_epi8(chunk, soh)) as u32 as u64;
                        if m != 0 {
                            return Some(self.emit_soh_mask(m, i, 16));
                        }
                        i += 16;
                    }
                }
            }
        }

        // ---- SWAR (8 bytes at a time) ----
        {
            let splat = LO;
            while i + 8 <= bytes.len() {
                // SAFETY: bounds checked by the while condition
                let chunk: [u8; 8] =
                    unsafe { bytes.as_ptr().add(i).cast::<[u8; 8]>().read_unaligned() };
                let word = u64::from_ne_bytes(chunk);
                let xored = word ^ splat;
                let swar_mask = xored.wrapping_sub(LO) & !xored & HI;
                if swar_mask != 0 {
                    let packed = swar_to_byte_mask(swar_mask);
                    return Some(self.emit_soh_mask(packed, i, 8));
                }
                i += 8;
            }
        }

        // ---- Scalar tail (< 8 bytes) ----
        while i < bytes.len() {
            if bytes[i] == 0x01 {
                let result = self.scan_pos + i;
                self.scan_pos = result + 1;
                return Some(result);
            }
            i += 1;
        }

        self.scan_pos = self.buf.len();
        None
    }
}

// =============================================================================
// SWAR mask conversion
// =============================================================================

/// Convert SWAR match mask to bit-per-byte mask.
///
/// SWAR sets the high bit of each matching byte (bits 7, 15, 23, ...).
/// This converts to one-bit-per-byte (bits 0, 1, 2, ...) for uniform
/// handling via `emit_soh_mask`.
///
/// A branchless multiply-shift gather (shift right 7, multiply by the
/// magic `0x0102_0408_1020_4080`, shift right 56) is correct and tempting
/// here, but measured slower on realistic decode and was rejected: this
/// result feeds `emit_soh_mask` on the critical path, so the multiply's
/// full latency lands on the returned position. For the common sparse case
/// (one SOH in the tail window) the loop runs a single cheap iteration and
/// wins by doing less work for the common input.
#[inline]
fn swar_to_byte_mask(swar_mask: u64) -> u64 {
    let mut packed = 0u64;
    let mut m = swar_mask;
    while m != 0 {
        let bit = m.trailing_zeros();
        packed |= 1u64 << (bit / 8);
        m &= m - 1;
    }
    packed
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_buffer() {
        let mut parser = FieldReader::new(b"", 0);
        assert!(parser.next_field().is_none());
    }

    #[test]
    fn single_field() {
        let msg = b"35=D\x01";
        let mut parser = FieldReader::new(msg, 0);
        let field = parser.next_field().unwrap();
        assert_eq!(field.tag, 35);
        assert_eq!(field.value.slice(msg), b"D");
        assert!(parser.next_field().is_none());
    }

    #[test]
    fn next_field_if_peeks_without_consuming() {
        // The header→body / group boundary primitive: consume while `pred` holds,
        // then stop *without* touching the first field that fails it.
        let msg = b"8=FIX.4.4\x0135=D\x0111=ORD\x0155=BTC\x01";
        let mut r = FieldReader::new(msg, 0);
        let hdr = |t: u32| matches!(t, 8 | 35);

        assert_eq!(r.next_field_if(hdr).unwrap().tag, 8);
        assert_eq!(r.next_field_if(hdr).unwrap().tag, 35);
        // Tag 11 fails the predicate → None, and the reader is left untouched.
        assert!(r.next_field_if(hdr).is_none());
        assert!(r.next_field_if(hdr).is_none()); // idempotent: still untouched
        // The next consumer reads tag 11 normally — no re-scan, no lost field.
        let f11 = r.next_field().unwrap();
        assert_eq!(f11.tag, 11);
        assert_eq!(f11.value.slice(msg), b"ORD");
        assert_eq!(r.next_field().unwrap().tag, 55);
        assert!(r.next_field().is_none());
    }

    #[test]
    fn multiple_fields() {
        let msg = b"8=FIX.4.4\x0135=D\x0149=SENDER\x01";
        let mut parser = FieldReader::new(msg, 0);

        let f1 = parser.next_field().unwrap();
        assert_eq!(f1.tag, 8);
        assert_eq!(f1.value.slice(msg), b"FIX.4.4");

        let f2 = parser.next_field().unwrap();
        assert_eq!(f2.tag, 35);
        assert_eq!(f2.value.slice(msg), b"D");

        let f3 = parser.next_field().unwrap();
        assert_eq!(f3.tag, 49);
        assert_eq!(f3.value.slice(msg), b"SENDER");

        assert!(parser.next_field().is_none());
    }

    #[test]
    fn from_offset() {
        let msg = b"8=FIX.4.4\x0135=D\x01";
        let mut parser = FieldReader::new(msg, 10);
        let field = parser.next_field().unwrap();
        assert_eq!(field.tag, 35);
        assert_eq!(field.value.slice(msg), b"D");
        assert!(parser.next_field().is_none());
    }

    #[test]
    fn tag_numbers() {
        let msg = b"8=v\x0135=v\x01150=v\x015592=v\x01";
        let tags: Vec<u32> = FieldReader::new(msg, 0).map(|f| f.tag).collect();
        assert_eq!(tags, vec![8, 35, 150, 5592]);
    }

    #[test]
    fn value_spans() {
        let msg = b"44=50000.00\x0155=BTC-USD\x01";
        let mut parser = FieldReader::new(msg, 0);

        let f1 = parser.next_field().unwrap();
        assert_eq!(f1.value.slice(msg), b"50000.00");

        let f2 = parser.next_field().unwrap();
        assert_eq!(f2.value.slice(msg), b"BTC-USD");
    }

    #[test]
    fn standalone_checksum_matches_byte_sum() {
        let msg = b"8=FIX.4.4\x0135=D\x0149=SENDER\x01";
        let expected: u8 = msg.iter().map(|&b| b as u32).sum::<u32>() as u8;
        assert_eq!(checksum(msg), expected);
    }

    #[test]
    fn standalone_checksum_various_lengths() {
        // Sweep every length so the standalone checksum's auto-vectorized tiers
        // (and tail) are all exercised.
        for len in 1..=300 {
            let value = "X".repeat(len);
            let msg = format!("1={}\x01", value);
            let msg = msg.as_bytes();
            let expected: u8 = msg.iter().map(|&b| b as u32).sum::<u32>() as u8;
            assert_eq!(checksum(msg), expected, "len={}", len);
        }
    }

    #[test]
    fn malformed_no_equals() {
        let msg = b"garbage\x01";
        let mut parser = FieldReader::new(msg, 0);
        assert!(parser.next_field().is_none());
    }

    #[test]
    fn iterator_count() {
        let msg = b"8=FIX.4.4\x019=65\x0135=D\x0149=SENDER\x0156=TARGET\x01\
                     34=1\x0152=20260530-12:00:00\x0111=order1\x0155=BTC-USD\x01\
                     54=1\x0138=100\x0140=2\x0144=50000.00\x0110=123\x01";
        let count = FieldReader::new(msg, 0).count();
        assert_eq!(count, 14);
    }

    #[test]
    fn realistic_fix_message() {
        let msg = b"8=FIX.4.4\x019=120\x0135=D\x0149=SENDER\x0156=TARGET\x01\
                     34=42\x0152=20260530-12:00:00.000\x0111=order-001\x01\
                     55=BTC-USD\x0154=1\x0138=1.50000000\x0140=2\x01\
                     44=67500.00\x0159=0\x0110=178\x01";

        let mut parser = FieldReader::new(msg, 0);
        let mut fields = Vec::new();
        while let Some(field) = parser.next_field() {
            fields.push(field);
        }

        assert_eq!(fields.len(), 15);
        assert_eq!(fields[0].tag, 8);
        assert_eq!(fields[0].value.slice(msg), b"FIX.4.4");
        assert_eq!(fields[2].tag, 35);
        assert_eq!(fields[2].value.slice(msg), b"D");
        assert_eq!(fields[14].tag, 10);
        assert_eq!(fields[14].value.slice(msg), b"178");

        // FIX checksum covers every byte before the "10=" field.
        let body = &msg[..msg.len() - b"10=178\x01".len()];
        let body_sum: u8 = body.iter().map(|&b| b as u32).sum::<u32>() as u8;
        assert_eq!(checksum(body), body_sum);
    }

    #[test]
    fn verify_checksum_excludes_tag_10() {
        // CheckSum covers only the bytes before "10=". Build the message with
        // the correct value and confirm verification passes.
        let body = b"35=D\x0149=SENDER\x01";
        let sum = checksum(body);
        let msg = format!("35=D\x0149=SENDER\x0110={sum:03}\x01");
        assert!(validate_checksum(msg.as_bytes()).is_ok());
    }

    #[test]
    fn long_value_exercises_simd() {
        let value = "X".repeat(300);
        let msg = format!("1={}\x01", value);
        let msg = msg.as_bytes();

        let mut parser = FieldReader::new(msg, 0);
        let field = parser.next_field().unwrap();
        assert_eq!(field.tag, 1);
        assert_eq!(field.value.len, 300);
        assert!(parser.next_field().is_none());

        let expected: u8 = msg.iter().map(|&b| b as u32).sum::<u32>() as u8;
        assert_eq!(checksum(msg), expected);
    }

    #[test]
    fn many_short_fields() {
        let mut msg = Vec::new();
        for i in 1..=50 {
            msg.extend_from_slice(format!("{}=v\x01", i).as_bytes());
        }

        let mut parser = FieldReader::new(&msg, 0);
        let mut count = 0;
        while parser.next_field().is_some() {
            count += 1;
        }
        assert_eq!(count, 50);

        let expected: u8 = msg.iter().map(|&b| b as u32).sum::<u32>() as u8;
        assert_eq!(checksum(&msg), expected);
    }

    #[test]
    fn dense_soh_in_swar_chunk() {
        // Multiple SOH bytes within a single 8-byte window
        let msg = b"1=A\x012=B\x013=C\x01";
        let fields: Vec<(u32, &[u8])> = FieldReader::new(msg, 0)
            .map(|f| (f.tag, f.value.slice(msg)))
            .collect();
        assert_eq!(
            fields,
            vec![(1, b"A" as &[u8]), (2, b"B" as &[u8]), (3, b"C" as &[u8])]
        );
    }

    #[test]
    fn pos_advances() {
        let msg = b"8=FIX.4.4\x0135=D\x01";
        let mut parser = FieldReader::new(msg, 0);
        assert_eq!(parser.pos(), 0);
        parser.next_field();
        assert_eq!(parser.pos(), 10);
        parser.next_field();
        assert_eq!(parser.pos(), 15);
    }

    #[test]
    fn parse_tag_standalone() {
        assert_eq!(parse_tag(b"8=FIX"), (8, 1));
        assert_eq!(parse_tag(b"35=D"), (35, 2));
        assert_eq!(parse_tag(b"150=2"), (150, 3));
        assert_eq!(parse_tag(b"5592=CUSTOM"), (5592, 4));
        assert_eq!(parse_tag(b"10000=X"), (10000, 5));
    }

    #[test]
    fn parse_tag_empty() {
        assert_eq!(parse_tag(b""), (0, 0));
        assert_eq!(parse_tag(b"=value"), (0, 0));
    }

    #[test]
    fn parse_tag_overflow_saturates() {
        // 11-digit tag overflows u32; saturates to MAX and consumes all digits.
        assert_eq!(parse_tag(b"99999999999=x"), (u32::MAX, 11));
        // Digits still consumed past the saturation point.
        assert_eq!(parse_tag(b"123456789012345=v"), (u32::MAX, 15));
    }

    #[test]
    fn swar_mask_conversion() {
        // Single match at byte 0: bit 7 set
        assert_eq!(swar_to_byte_mask(0x80), 0x01);
        // Single match at byte 3: bit 31 set
        assert_eq!(swar_to_byte_mask(0x80_00_00_00), 0x08);
        // Matches at bytes 0 and 7
        assert_eq!(swar_to_byte_mask(0x80_00_00_00_00_00_00_80), 0x81);
    }

    #[test]
    fn swar_mask_conversion_exhaustive() {
        // For every subset of matched bytes, build the SWAR mask (high bit
        // per matched byte) and check `swar_to_byte_mask` against the
        // reference mapping: matched byte k -> output bit k.
        for pattern in 0u32..256 {
            let mut swar = 0u64;
            let mut expected = 0u64;
            for k in 0..8 {
                if pattern & (1 << k) != 0 {
                    swar |= 0x80u64 << (k * 8);
                    expected |= 1u64 << k;
                }
            }
            assert_eq!(
                swar_to_byte_mask(swar),
                expected,
                "pattern={:#010b}",
                pattern
            );
        }
    }

    // =========================================================================
    // Standalone checksum
    // =========================================================================

    #[test]
    fn checksum_standalone() {
        assert_eq!(checksum(b""), 0);
        assert_eq!(checksum(b"\x01"), 1);
        let msg = b"8=FIX.4.4\x0135=D\x01";
        let expected: u8 = msg.iter().map(|&b| b as u32).sum::<u32>() as u8;
        assert_eq!(checksum(msg), expected);
    }

    // =========================================================================
    // find_tag
    // =========================================================================

    #[test]
    fn find_tag_present() {
        let msg = b"8=FIX.4.4\x0135=D\x0149=SENDER\x01";
        let span = find_tag(msg, 0, 35).unwrap();
        assert_eq!(span.slice(msg), b"D");
    }

    #[test]
    fn find_tag_absent() {
        let msg = b"8=FIX.4.4\x0135=D\x01";
        assert!(find_tag(msg, 0, 99).is_none());
    }

    #[test]
    fn find_tag_with_offset() {
        let msg = b"8=FIX.4.4\x0135=D\x0149=SENDER\x01";
        assert!(find_tag(msg, 10, 8).is_none());
        let span = find_tag(msg, 10, 35).unwrap();
        assert_eq!(span.slice(msg), b"D");
    }

    #[test]
    fn find_tag_first_match() {
        let msg = b"58=first\x0158=second\x01";
        let span = find_tag(msg, 0, 58).unwrap();
        assert_eq!(span.slice(msg), b"first");
    }

    // =========================================================================
    // validate_checksum
    // =========================================================================

    #[test]
    fn validate_checksum_valid() {
        let body = b"8=FIX.4.4\x0135=D\x0149=SENDER\x01";
        let sum = checksum(body);
        let msg = format!("8=FIX.4.4\x0135=D\x0149=SENDER\x0110={:03}\x01", sum);
        assert!(validate_checksum(msg.as_bytes()).is_ok());
    }

    #[test]
    fn validate_checksum_invalid() {
        let msg = b"8=FIX.4.4\x0135=D\x0149=SENDER\x0110=000\x01";
        let result = validate_checksum(msg);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert_eq!(err.expected, 0);
        assert_ne!(err.computed, 0);
    }

    #[test]
    fn validate_checksum_no_tag10() {
        let msg = b"8=FIX.4.4\x0135=D\x01";
        assert!(validate_checksum(msg).is_ok());
    }

    #[test]
    fn validate_checksum_realistic() {
        // Build a message, compute correct checksum, then validate
        let body = b"8=FIX.4.4\x019=65\x0135=D\x0149=SENDER\x0156=TARGET\x01";
        let sum = checksum(body);
        let mut msg = body.to_vec();
        msg.extend_from_slice(format!("10={:03}\x01", sum).as_bytes());
        assert!(validate_checksum(&msg).is_ok());
    }

    #[test]
    fn binary_value() {
        let msg = b"96=\x00\xFF\x80\x7F\x01";
        let mut parser = FieldReader::new(msg, 0);
        let field = parser.next_field().unwrap();
        assert_eq!(field.tag, 96);
        assert_eq!(field.value.slice(msg), b"\x00\xFF\x80\x7F");
        assert!(parser.next_field().is_none());

        let expected: u8 = msg.iter().map(|&b| b as u32).sum::<u32>() as u8;
        assert_eq!(checksum(msg), expected);
    }

    #[test]
    fn validate_checksum_malformed_tag10() {
        let msg = b"35=D\x0110=XYZ\x01";
        // A non-digit CheckSum is malformed → rejected deterministically.
        assert!(validate_checksum(msg).is_err());
    }

    #[test]
    fn parse_checksum_bytes_rejects_malformed() {
        // Malformed CheckSum is `None` — distinct from a genuine `Some(0)` — so
        // it can never false-accept by colliding with a `0` computed checksum.
        assert_eq!(parse_checksum_bytes(b"178"), Some(178));
        assert_eq!(parse_checksum_bytes(b"000"), Some(0));
        assert_eq!(parse_checksum_bytes(b"XYZ"), None); // non-digit
        assert_eq!(parse_checksum_bytes(b"12"), None); // too short
        assert_eq!(parse_checksum_bytes(b"1234"), None); // too long
    }

    #[test]
    fn next_data_field_embedded_soh() {
        let msg = b"95=5\x0196=AB\x01CD\x0155=X\x01";
        let mut r = FieldReader::new(msg, 0);
        r.next_field();
        let f = r.next_data_field(5).unwrap();
        assert_eq!(f.tag, 96);
        assert_eq!(f.value.slice(msg), b"AB\x01CD");
        let next = r.next_field().unwrap();
        assert_eq!(next.tag, 55);
        assert_eq!(next.value.slice(msg), b"X");
        assert!(r.next_field().is_none());
    }

    #[test]
    fn next_data_field_embedded_equals() {
        let msg = b"95=3\x0196=a=b\x0155=Y\x01";
        let mut r = FieldReader::new(msg, 0);
        r.next_field();
        let f = r.next_data_field(3).unwrap();
        assert_eq!(f.tag, 96);
        assert_eq!(f.value.slice(msg), b"a=b");
        assert_eq!(r.next_field().unwrap().tag, 55);
    }

    #[test]
    fn next_data_field_last_before_checksum() {
        let body = b"95=3\x0196=ABC\x01";
        let sum = checksum(body);
        let mut msg = body.to_vec();
        msg.extend_from_slice(format!("10={sum:03}\x01").as_bytes());
        let mut r = FieldReader::new(&msg, 0);
        r.next_field();
        let f = r.next_data_field(3).unwrap();
        assert_eq!(f.value.slice(&msg), b"ABC");
        let tag10 = r.next_field().unwrap();
        assert_eq!(tag10.tag, 10);
    }

    #[test]
    fn next_data_field_multiple_pairs() {
        let msg = b"95=2\x0196=AB\x01212=3\x01213=CDE\x0155=Z\x01";
        let mut r = FieldReader::new(msg, 0);
        r.next_field();
        let f1 = r.next_data_field(2).unwrap();
        assert_eq!(f1.tag, 96);
        assert_eq!(f1.value.slice(msg), b"AB");
        r.next_field();
        let f2 = r.next_data_field(3).unwrap();
        assert_eq!(f2.tag, 213);
        assert_eq!(f2.value.slice(msg), b"CDE");
        assert_eq!(r.next_field().unwrap().tag, 55);
    }

    #[test]
    fn next_data_field_inside_group() {
        let msg = b"268=1\x0196=AB\x01CD\x01";
        let mut r = FieldReader::new(msg, 0);
        r.next_field(); // 268=1
        let f = r.next_data_field(5).unwrap();
        assert_eq!(f.tag, 96);
        assert_eq!(f.value.slice(msg), b"AB\x01CD");
        assert!(r.next_field().is_none());
    }

    #[test]
    fn next_data_field_checksum_covers_embedded_soh() {
        let body = b"95=5\x0196=AB\x01CD\x01";
        let sum = checksum(body);
        let mut msg = body.to_vec();
        msg.extend_from_slice(format!("10={sum:03}\x01").as_bytes());
        let prefix = &msg[..msg.len() - b"10=000\x01".len()];
        assert_eq!(checksum(prefix), sum);
    }

    #[test]
    fn next_data_field_zero_len_errors() {
        let msg = b"95=0\x0196=\x0155=X\x01";
        let mut r = FieldReader::new(msg, 0);
        r.next_field();
        assert!(matches!(
            r.next_data_field(0),
            Err(crate::DecodeError::InvalidLength)
        ));
    }

    #[test]
    fn next_data_field_n_exceeds_remaining() {
        let msg = b"95=100\x0196=ABC\x01";
        let mut r = FieldReader::new(msg, 0);
        r.next_field();
        assert!(matches!(
            r.next_data_field(100),
            Err(crate::DecodeError::Truncated)
        ));
    }

    #[test]
    fn next_data_field_missing_terminator() {
        let msg = b"95=3\x0196=ABC";
        let mut r = FieldReader::new(msg, 0);
        r.next_field();
        assert!(matches!(
            r.next_data_field(3),
            Err(crate::DecodeError::Truncated)
        ));
    }

    #[test]
    fn resync_after_data_repositions() {
        // The generated DATA-field skip jumps the reader past a length-prefixed
        // value that may contain embedded SOH, then continues scanning. Verify
        // the reposition lands exactly on the next field.
        // value "a\x01b\x01c" — 5 bytes, two embedded SOH.
        let msg = b"8=FIX.4.4\x0195=5\x0196=a\x01b\x01c\x0155=X\x01";

        let mut r = FieldReader::new(msg, 0);
        r.next_field(); // 8=
        let f95 = r.next_field().unwrap();
        assert_eq!(f95.tag, 95);

        // Compute the DATA value end the way the generated code does, then skip.
        let dstart = r.pos();
        let (_, dtl) = parse_tag(&msg[dstart..]);
        let vstart = dstart + dtl + 1;
        let dend = vstart + 5 + 1; // value(5) + trailing SOH
        r.resync_after_data(dend);

        let f55 = r.next_field().unwrap();
        assert_eq!(f55.tag, 55);
        assert_eq!(f55.value.slice(msg), b"X");
        assert!(r.next_field().is_none());

        // The standalone checksum covers the DATA bytes (incl. embedded SOH)
        // with a flat contiguous sum — no special handling needed.
        assert_eq!(
            checksum(msg),
            msg.iter().map(|&b| b as u32).sum::<u32>() as u8
        );
    }

    // =========================================================================
    // Repeating group pattern (simulates codegen usage)
    // =========================================================================

    #[test]
    fn repeating_group_walk() {
        // MarketDataSnapshot with NoMDEntries (tag 268) = 3 entries.
        // Delimiter tag is 269 (MDEntryType). Entries have varying field counts.
        let msg = b"35=W\x01\
                     268=3\x01\
                     269=0\x01270=50000.00\x01271=1.5\x01\
                     269=1\x01270=49999.00\x01\
                     269=2\x01270=50001.00\x01271=0.8\x01272=XBTO\x01\
                     10=999\x01";

        let delimiter_tag = 269u32;
        let mut reader = FieldReader::new(msg, 0);

        // Walk to the count tag (268), simulating what the scanner does.
        let mut group_count = 0u16;
        let mut group_offset = 0u32;
        while let Some(field) = reader.next_field() {
            if field.tag == 268 {
                let count_bytes = field.value.slice(msg);
                group_count = core::str::from_utf8(count_bytes).unwrap().parse().unwrap();
                group_offset = reader.pos() as u32;
                break;
            }
        }

        let group = crate::GroupSpan::new(group_offset, group_count);
        assert_eq!(group.count, 3);

        // Now read the group: iterate from group.offset, using dictionary
        // knowledge of which tags belong to the group to detect boundaries.
        let group_tags: &[u32] = &[269, 270, 271, 272];
        let mut group_reader = FieldReader::new(msg, group.offset as usize);
        let mut entries: Vec<Vec<RawField>> = Vec::new();
        let mut current_entry: Vec<RawField> = Vec::new();

        while let Some(field) = group_reader.next_field() {
            if !group_tags.contains(&field.tag) {
                break;
            }
            if field.tag == delimiter_tag && !current_entry.is_empty() {
                entries.push(core::mem::take(&mut current_entry));
            }
            current_entry.push(field);
        }
        if !current_entry.is_empty() {
            entries.push(current_entry);
        }

        assert_eq!(entries.len(), 3);
        assert_eq!(entries[0].len(), 3); // 269, 270, 271
        assert_eq!(entries[1].len(), 2); // 269, 270
        assert_eq!(entries[2].len(), 4); // 269, 270, 271, 272

        assert_eq!(entries[0][0].value.slice(msg), b"0");
        assert_eq!(entries[0][1].value.slice(msg), b"50000.00");
        assert_eq!(entries[1][0].value.slice(msg), b"1");
        assert_eq!(entries[2][3].value.slice(msg), b"XBTO");
    }

    #[test]
    fn repeating_group_single_entry() {
        let msg = b"35=W\x01268=1\x01269=0\x01270=50000\x0110=999\x01";

        let group_tags: &[u32] = &[269, 270];
        let mut reader = FieldReader::new(msg, 0);
        while let Some(f) = reader.next_field() {
            if f.tag == 268 {
                break;
            }
        }
        let group = crate::GroupSpan::new(reader.pos() as u32, 1);

        let mut group_reader = FieldReader::new(msg, group.offset as usize);
        let mut entries: Vec<Vec<RawField>> = Vec::new();
        let mut current: Vec<RawField> = Vec::new();
        while let Some(f) = group_reader.next_field() {
            if !group_tags.contains(&f.tag) {
                break;
            }
            if f.tag == 269 && !current.is_empty() {
                entries.push(core::mem::take(&mut current));
            }
            current.push(f);
        }
        if !current.is_empty() {
            entries.push(current);
        }

        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].len(), 2);
        assert_eq!(entries[0][0].value.slice(msg), b"0");
        assert_eq!(entries[0][1].value.slice(msg), b"50000");
    }

    #[test]
    fn repeating_group_minimal_entries() {
        // Entries with only the delimiter tag (all optional fields absent).
        let msg = b"268=3\x01269=0\x01269=1\x01269=2\x0110=999\x01";

        let group_tags: &[u32] = &[269, 270, 271];
        let mut reader = FieldReader::new(msg, 0);
        reader.next_field(); // skip 268
        let group = crate::GroupSpan::new(reader.pos() as u32, 3);

        let mut group_reader = FieldReader::new(msg, group.offset as usize);
        let mut entries: Vec<Vec<RawField>> = Vec::new();
        let mut current: Vec<RawField> = Vec::new();
        while let Some(f) = group_reader.next_field() {
            if !group_tags.contains(&f.tag) {
                break;
            }
            if f.tag == 269 && !current.is_empty() {
                entries.push(core::mem::take(&mut current));
            }
            current.push(f);
        }
        if !current.is_empty() {
            entries.push(current);
        }

        assert_eq!(entries.len(), 3);
        assert_eq!(entries[0].len(), 1);
        assert_eq!(entries[1].len(), 1);
        assert_eq!(entries[2].len(), 1);
    }

    #[test]
    fn repeating_group_at_end_of_message() {
        // Group is the last thing in the buffer — no trailing non-group tag.
        let msg = b"268=2\x01269=0\x01270=100\x01269=1\x01270=200\x01";

        let group_tags: &[u32] = &[269, 270];
        let mut reader = FieldReader::new(msg, 0);
        reader.next_field(); // skip 268
        let group = crate::GroupSpan::new(reader.pos() as u32, 2);

        let mut group_reader = FieldReader::new(msg, group.offset as usize);
        let mut entries: Vec<Vec<RawField>> = Vec::new();
        let mut current: Vec<RawField> = Vec::new();
        while let Some(f) = group_reader.next_field() {
            if !group_tags.contains(&f.tag) {
                break;
            }
            if f.tag == 269 && !current.is_empty() {
                entries.push(core::mem::take(&mut current));
            }
            current.push(f);
        }
        if !current.is_empty() {
            entries.push(current);
        }

        assert_eq!(entries.len(), 2);
        assert_eq!(entries[0][1].value.slice(msg), b"100");
        assert_eq!(entries[1][1].value.slice(msg), b"200");
    }

    // =========================================================================
    // Repeating group error cases
    // =========================================================================

    #[test]
    fn repeating_group_truncated() {
        // Count says 3 but buffer only has 2 entries.
        let msg = b"268=3\x01269=0\x01270=100\x01269=1\x01270=200\x01";

        let group_tags: &[u32] = &[269, 270];
        let mut reader = FieldReader::new(msg, 0);
        reader.next_field();
        let group = crate::GroupSpan::new(reader.pos() as u32, 3);

        let mut group_reader = FieldReader::new(msg, group.offset as usize);
        let mut entry_count = 0u16;
        while let Some(f) = group_reader.next_field() {
            if !group_tags.contains(&f.tag) {
                break;
            }
            if f.tag == 269 {
                entry_count += 1;
            }
        }

        // Reader yields what's there without panicking.
        // Codegen detects the mismatch: found 2, expected 3.
        assert_eq!(entry_count, 2);
        assert!(entry_count < group.count);
    }

    #[test]
    fn repeating_group_no_delimiter() {
        // Count says 2 but the delimiter tag (269) never appears.
        let msg = b"268=2\x01270=100\x01271=200\x0110=999\x01";

        let group_tags: &[u32] = &[269, 270, 271];
        let mut reader = FieldReader::new(msg, 0);
        reader.next_field();
        let group = crate::GroupSpan::new(reader.pos() as u32, 2);

        let mut group_reader = FieldReader::new(msg, group.offset as usize);
        let mut entry_count = 0u16;
        while let Some(f) = group_reader.next_field() {
            if !group_tags.contains(&f.tag) {
                break;
            }
            if f.tag == 269 {
                entry_count += 1;
            }
        }

        // No delimiter seen — codegen would flag this as malformed.
        assert_eq!(entry_count, 0);
    }

    #[test]
    fn repeating_group_count_zero() {
        // Count is 0 — group has no entries.
        let msg = b"268=0\x0135=W\x01";

        let mut reader = FieldReader::new(msg, 0);
        reader.next_field();
        let group = crate::GroupSpan::new(reader.pos() as u32, 0);

        assert!(!group.is_present());

        // Reading from the offset just yields the next non-group field.
        let mut group_reader = FieldReader::new(msg, group.offset as usize);
        let next = group_reader.next_field().unwrap();
        assert_eq!(next.tag, 35);
    }

    // =========================================================================
    // Bogus / adversarial input
    // =========================================================================

    #[test]
    fn bogus_no_soh() {
        let mut reader = FieldReader::new(b"just random garbage", 0);
        assert!(reader.next_field().is_none());
    }

    #[test]
    fn bogus_adjacent_soh() {
        // Empty spans between SOH bytes.
        let mut reader = FieldReader::new(b"\x01\x01\x01", 0);
        assert!(reader.next_field().is_none());
    }

    #[test]
    fn bogus_equals_no_tag() {
        let mut reader = FieldReader::new(b"=value\x01", 0);
        assert!(reader.next_field().is_none());
    }

    #[test]
    fn bogus_non_digit_in_tag() {
        // parse_tag reads "1", stops at "a", then field_bytes[1] != '='.
        let mut reader = FieldReader::new(b"1a2=value\x01", 0);
        assert!(reader.next_field().is_none());
    }

    #[test]
    fn bogus_all_soh() {
        let buf = vec![0x01; 64];
        let mut reader = FieldReader::new(&buf, 0);
        assert!(reader.next_field().is_none());
    }

    #[test]
    fn bogus_before_valid_field() {
        // Garbage field stops the iterator; valid field after it is not reached.
        let msg = b"garbage\x0135=D\x01";
        let count = FieldReader::new(msg, 0).count();
        assert_eq!(count, 0);
    }

    #[test]
    fn bogus_only_equals_and_soh() {
        let mut reader = FieldReader::new(b"=\x01=\x01=\x01", 0);
        assert!(reader.next_field().is_none());
    }

    #[test]
    fn bogus_tag_no_value_no_equals() {
        let mut reader = FieldReader::new(b"35\x01", 0);
        assert!(reader.next_field().is_none());
    }
}
