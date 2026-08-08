//! Fixed-capacity ASCII string type.

use core::hash::{Hash, Hasher};

use crate::AsciiError;
use crate::char::AsciiChar;
use crate::hash;
use crate::simd;
use crate::str_ref::AsciiStr;

/// Extract length from header (stored in upper 16 bits).
#[inline(always)]
const fn unpack_len(header: u64) -> usize {
    (header >> 48) as usize
}

// =============================================================================
// Null Byte Detection & ASCII Validation
// =============================================================================

/// Detect if any byte in a u64 is zero.
/// Returns a mask with the high bit set in each byte position that contains zero.
#[allow(dead_code)]
#[inline(always)]
const fn has_null_byte(v: u64) -> u64 {
    const LO: u64 = 0x0101_0101_0101_0101;
    const HI: u64 = 0x8080_8080_8080_8080;
    (v.wrapping_sub(LO)) & !v & HI
}

/// Find the position of the first null byte using SWAR (8 bytes at a time).
#[allow(dead_code)]
#[inline]
fn find_null_byte_scalar(bytes: &[u8]) -> usize {
    let mut i = 0;

    // Process 8 bytes at a time
    while i + 8 <= bytes.len() {
        // SAFETY: We just checked that i + 8 <= bytes.len()
        let chunk: [u8; 8] = unsafe { bytes.as_ptr().add(i).cast::<[u8; 8]>().read_unaligned() };
        let word = u64::from_ne_bytes(chunk);
        let mask = has_null_byte(word);
        if mask != 0 {
            return i + (mask.trailing_zeros() / 8) as usize;
        }
        i += 8;
    }

    // Handle remainder byte by byte
    while i < bytes.len() {
        if bytes[i] == 0 {
            return i;
        }
        i += 1;
    }

    bytes.len()
}

/// Find the position of the first null byte using SSE2 (16 bytes at a time).
/// Falls back to scalar for remainder.
#[cfg(target_arch = "x86_64")]
#[inline]
fn find_null_byte_sse2(bytes: &[u8]) -> usize {
    use core::arch::x86_64::*;

    let len = bytes.len();
    let mut i = 0;

    // Process 16 bytes at a time
    // SAFETY: SSE2 is baseline for x86_64
    unsafe {
        let zero = _mm_setzero_si128();

        while i + 16 <= len {
            let chunk = _mm_loadu_si128(bytes.as_ptr().add(i).cast());
            let cmp = _mm_cmpeq_epi8(chunk, zero);
            let mask = _mm_movemask_epi8(cmp);
            if mask != 0 {
                return i + mask.trailing_zeros() as usize;
            }
            i += 16;
        }
    }

    // Handle remainder with scalar
    while i < len {
        if bytes[i] == 0 {
            return i;
        }
        i += 1;
    }

    len
}

/// Find the position of the first null byte in a slice.
/// Returns the slice length if no null byte is found.
///
/// Dispatches to SSE2 on x86_64 (16 bytes/iter), scalar SWAR elsewhere (8 bytes/iter).
#[inline]
pub(crate) fn find_null_byte(bytes: &[u8]) -> usize {
    #[cfg(target_arch = "x86_64")]
    {
        find_null_byte_sse2(bytes)
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        find_null_byte_scalar(bytes)
    }
}

/// Precomputed header for empty string (compile-time).
const EMPTY_HEADER: u64 = hash::pack_header(0, hash::hash_const::<0>(&[]));

/// Inline copy for bounded lengths. Avoids glibc memcpy call overhead for short copies.
///
/// Uses the overlap trick: reads two chunks whose combined span covers all bytes,
/// even if they overlap. Safe because destination is a freshly zeroed buffer.
///
/// For len > 32, falls through to memcpy where call overhead is negligible
/// relative to data volume.
///
/// # Safety
///
/// - `dst` must be writable for at least `len` bytes
/// - `src` must be readable for `len` bytes
/// - `dst` and `src` must not overlap
#[inline(always)]
pub(crate) unsafe fn copy_short(dst: *mut u8, src: *const u8, len: usize) {
    // SAFETY: caller guarantees dst/src validity, len, and non-overlap per function preconditions.
    unsafe {
        if len > 32 {
            core::ptr::copy_nonoverlapping(src, dst, len);
        } else if len >= 16 {
            let a = src.cast::<u128>().read_unaligned();
            let b = src.add(len - 16).cast::<u128>().read_unaligned();
            dst.cast::<u128>().write_unaligned(a);
            dst.add(len - 16).cast::<u128>().write_unaligned(b);
        } else if len >= 8 {
            let a = src.cast::<u64>().read_unaligned();
            let b = src.add(len - 8).cast::<u64>().read_unaligned();
            dst.cast::<u64>().write_unaligned(a);
            dst.add(len - 8).cast::<u64>().write_unaligned(b);
        } else if len >= 4 {
            let a = src.cast::<u32>().read_unaligned();
            let b = src.add(len - 4).cast::<u32>().read_unaligned();
            dst.cast::<u32>().write_unaligned(a);
            dst.add(len - 4).cast::<u32>().write_unaligned(b);
        } else if len > 0 {
            *dst = *src;
            *dst.add(len / 2) = *src.add(len / 2);
            *dst.add(len - 1) = *src.add(len - 1);
        }
    }
}

// =============================================================================
// AsciiString
// =============================================================================

/// A fixed-capacity, immutable ASCII string.
///
/// `AsciiString<CAP>` stores up to `CAP` ASCII bytes inline with a precomputed
/// hash. The hash and length are packed into a single `u64` header, enabling
/// fast equality checks (single 64-bit comparison rejects most non-equal strings).
///
/// # Design
///
/// - **Immutable**: Once created, the string cannot be modified. This guarantees
///   the hash is always valid.
/// - **Copy**: Always implements `Copy`. For move semantics, wrap in a newtype.
/// - **Full ASCII**: Accepts bytes 0x01-0x7F. For printable-only, use `AsciiText`.
///
/// # Example
///
/// ```
/// use nexus_ascii::AsciiString;
///
/// let s: AsciiString<32> = AsciiString::try_from("hello")?;
/// assert_eq!(s.len(), 5);
/// assert_eq!(s.as_str(), "hello");
/// # Ok::<(), nexus_ascii::AsciiError>(())
/// ```
#[derive(Clone, Copy)]
#[repr(C)]
pub struct AsciiString<const CAP: usize> {
    /// Packed header: bits 0-47 = hash (lower 48 bits), bits 48-63 = length.
    header: u64,
    /// Raw ASCII bytes. Only `len()` bytes are valid.
    data: [u8; CAP],
}

// =============================================================================
// Constructors
// =============================================================================

impl<const CAP: usize> AsciiString<CAP> {
    /// Compile-time assertion that CAP is a multiple of 8.
    /// Required for word-aligned SIMD operations.
    const _CAP_ASSERT: () = assert!(
        CAP.is_multiple_of(8),
        "AsciiString CAP must be a multiple of 8"
    );

    /// Creates an empty ASCII string.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let s: AsciiString<32> = AsciiString::empty();
    /// assert!(s.is_empty());
    /// assert_eq!(s.len(), 0);
    /// ```
    #[inline]
    pub const fn empty() -> Self {
        let () = Self::_CAP_ASSERT; // Force compile-time check
        Self {
            header: EMPTY_HEADER,
            data: [0u8; CAP],
        }
    }

    /// Creates an ASCII string from a static string literal at compile time.
    ///
    /// This is a `const fn` that validates the input and computes the hash
    /// at compile time. Invalid input (non-ASCII or too long) causes a
    /// compile-time panic.
    ///
    /// # Panics
    ///
    /// Panics at compile time if:
    /// - The string contains null bytes or non-ASCII bytes (> 127)
    /// - The string is longer than `CAP`
    /// - `CAP > 128` (const hash limitation)
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// // Compile-time construction
    /// const BTC: AsciiString<16> = AsciiString::from_static("BTC-USD");
    /// const ETH: AsciiString<16> = AsciiString::from_static("ETH-USD");
    ///
    /// assert_eq!(BTC.as_str(), "BTC-USD");
    /// assert_eq!(ETH.len(), 7);
    /// ```
    #[inline]
    pub const fn from_static(s: &'static str) -> Self {
        let () = Self::_CAP_ASSERT;
        assert!(CAP <= 128, "from_static only supports CAP <= 128");

        let bytes = s.as_bytes();
        let len = bytes.len();

        assert!(len <= CAP, "string exceeds capacity");

        // Validate non-null ASCII at compile time
        let mut i = 0;
        while i < len {
            assert!(bytes[i] != 0, "string contains null byte");
            assert!(bytes[i] <= 127, "string contains non-ASCII byte");
            i += 1;
        }

        // Compute hash at compile time
        let h = hash::hash_const::<CAP>(bytes);
        let header = hash::pack_header(len as u16, h);

        // Copy bytes into data array
        let mut data = [0u8; CAP];
        let mut j = 0;
        while j < len {
            data[j] = bytes[j];
            j += 1;
        }

        Self { header, data }
    }

    /// Creates an ASCII string from a static byte slice at compile time.
    ///
    /// This is a `const fn` that validates the input and computes the hash
    /// at compile time. Invalid input (non-ASCII, null, or too long) causes
    /// a compile-time panic.
    ///
    /// # Panics
    ///
    /// Panics at compile time if:
    /// - Any byte is null (0x00) or > 127 (non-ASCII)
    /// - The slice is longer than `CAP`
    /// - `CAP > 128` (const hash limitation)
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// // Compile-time construction from bytes
    /// const SYMBOL: AsciiString<16> = AsciiString::from_static_bytes(b"BTC-USD");
    /// const WITH_CTRL: AsciiString<16> = AsciiString::from_static_bytes(&[0x01, b'A', b'B']);
    ///
    /// assert_eq!(SYMBOL.as_str(), "BTC-USD");
    /// assert_eq!(WITH_CTRL.len(), 3);
    /// ```
    #[inline]
    pub const fn from_static_bytes(bytes: &'static [u8]) -> Self {
        let () = Self::_CAP_ASSERT;
        assert!(CAP <= 128, "from_static_bytes only supports CAP <= 128");

        let len = bytes.len();

        assert!(len <= CAP, "bytes exceed capacity");

        // Validate non-null ASCII at compile time
        let mut i = 0;
        while i < len {
            assert!(bytes[i] != 0, "bytes contain null byte");
            assert!(bytes[i] <= 127, "bytes contain non-ASCII byte");
            i += 1;
        }

        // Compute hash at compile time
        let h = hash::hash_const::<CAP>(bytes);
        let header = hash::pack_header(len as u16, h);

        // Copy bytes into data array
        let mut data = [0u8; CAP];
        let mut j = 0;
        while j < len {
            data[j] = bytes[j];
            j += 1;
        }

        Self { header, data }
    }

    /// Creates an ASCII string from a byte slice without validation.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - All bytes are valid ASCII (0x01-0x7F)
    /// - `bytes.len() <= CAP`
    ///
    /// Violating these invariants causes undefined behavior in downstream code
    /// that assumes ASCII validity.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let bytes = b"HELLO";
    /// // SAFETY: bytes are known ASCII and len <= 32
    /// let s: AsciiString<32> = unsafe { AsciiString::from_bytes_unchecked(bytes) };
    /// assert_eq!(s.as_str(), "HELLO");
    /// ```
    #[inline]
    pub unsafe fn from_bytes_unchecked(bytes: &[u8]) -> Self {
        let () = Self::_CAP_ASSERT;
        debug_assert!(bytes.len() <= CAP, "bytes exceed capacity");
        debug_assert!(
            bytes.iter().all(|&b| b > 0 && b <= 127),
            "bytes contain null or non-ASCII"
        );

        let len = bytes.len();
        let hash = hash::hash::<CAP>(bytes);
        let header = hash::pack_header(len as u16, hash);

        let mut data = [0u8; CAP];
        // SAFETY: len <= CAP guaranteed by caller, buffers don't overlap
        unsafe { copy_short(data.as_mut_ptr(), bytes.as_ptr(), len) };

        Self { header, data }
    }

    /// Creates an ASCII string from pre-validated parts.
    ///
    /// This is an internal constructor used by `AsciiStringBuilder`. The caller
    /// must guarantee that:
    /// - `len <= CAP`
    /// - `data[..len]` contains only valid ASCII bytes (0x01-0x7F)
    ///
    /// The hash is computed from `data[..len]`.
    #[inline]
    pub(crate) fn from_parts_unchecked(len: usize, mut data: [u8; CAP]) -> Self {
        let () = Self::_CAP_ASSERT;
        debug_assert!(len <= CAP, "len exceeds capacity");
        debug_assert!(
            data[..len].iter().all(|&b| b > 0 && b <= 127),
            "data contains null or non-ASCII"
        );

        // Zero-pad beyond content for word-aligned processing invariant
        data[len..].fill(0);

        let hash = hash::hash::<CAP>(&data[..len]);
        let header = hash::pack_header(len as u16, hash);
        Self { header, data }
    }

    /// Attempts to create an ASCII string from a byte slice.
    ///
    /// Returns an error if:
    /// - The slice is longer than `CAP` ([`AsciiError::TooLong`])
    /// - Any byte is null (0x00) or > 127 ([`AsciiError::InvalidByte`])
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::{AsciiString, AsciiError};
    ///
    /// let s: AsciiString<8> = AsciiString::try_from_bytes(b"hello")?;
    /// assert_eq!(s.as_str(), "hello");
    ///
    /// // Too long
    /// let err = AsciiString::<8>::try_from_bytes(b"hello world").unwrap_err();
    /// assert!(matches!(err, AsciiError::TooLong { .. }));
    ///
    /// // Invalid ASCII
    /// let err = AsciiString::<8>::try_from_bytes(&[0xFF]).unwrap_err();
    /// assert!(matches!(err, AsciiError::InvalidByte { .. }));
    /// # Ok::<(), AsciiError>(())
    /// ```
    #[inline]
    pub fn try_from_bytes(bytes: &[u8]) -> Result<Self, AsciiError> {
        if bytes.len() > CAP {
            return Err(AsciiError::TooLong {
                len: bytes.len(),
                cap: CAP,
            });
        }

        // Fast ASCII validation using word-at-a-time checking
        // Use bounded version since we know len <= CAP
        if let Err((byte, pos)) = simd::validate_ascii_bounded::<CAP>(bytes) {
            return Err(AsciiError::InvalidByte { byte, pos });
        }

        // SAFETY: We just validated all bytes are ASCII and len <= CAP
        Ok(unsafe { Self::from_bytes_unchecked(bytes) })
    }

    /// Attempts to create an ASCII string from a string slice.
    ///
    /// This is equivalent to `try_from_bytes(s.as_bytes())`.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let s: AsciiString<32> = AsciiString::try_from_str("BTC-USD")?;
    /// assert_eq!(s.as_str(), "BTC-USD");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn try_from_str(s: &str) -> Result<Self, AsciiError> {
        Self::try_from_bytes(s.as_bytes())
    }

    /// Creates an ASCII string from a `&str` without validation.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - All bytes are valid ASCII (0x01-0x7F)
    /// - The string length does not exceed `CAP`
    ///
    /// Violating these invariants causes undefined behavior.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// // SAFETY: "hello" is valid ASCII and fits in capacity
    /// let s: AsciiString<16> = unsafe { AsciiString::from_str_unchecked("hello") };
    /// assert_eq!(s.as_str(), "hello");
    /// ```
    #[inline]
    #[must_use]
    pub unsafe fn from_str_unchecked(s: &str) -> Self {
        // SAFETY: Caller guarantees valid ASCII and length
        unsafe { Self::from_bytes_unchecked(s.as_bytes()) }
    }

    /// Creates an ASCII string from a null-terminated byte slice.
    ///
    /// Finds the first null byte (0x00) and uses content before it.
    /// If no null byte is found, uses the entire slice (up to `CAP`).
    ///
    /// This is useful when you have a reference to a fixed-size buffer
    /// (e.g., `&[u8; 40]`) and don't want to copy to an owned array.
    ///
    /// # Errors
    ///
    /// - [`AsciiError::InvalidByte`] if any byte before the null is not ASCII
    /// - [`AsciiError::TooLong`] if content length exceeds `CAP`
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// // Reference to a fixed-size buffer (like from a wire format)
    /// let buffer: &[u8; 16] = b"BTC-USD\0\0\0\0\0\0\0\0\0";
    /// let s: AsciiString<16> = AsciiString::try_from_null_terminated(buffer)?;
    /// assert_eq!(s.as_str(), "BTC-USD");
    /// assert_eq!(s.len(), 7);
    ///
    /// // Also works with regular slices
    /// let slice: &[u8] = b"ETH-USD\0padding";
    /// let s: AsciiString<16> = AsciiString::try_from_null_terminated(slice)?;
    /// assert_eq!(s.as_str(), "ETH-USD");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn try_from_null_terminated(bytes: &[u8]) -> Result<Self, AsciiError> {
        let () = Self::_CAP_ASSERT;

        // Find null terminator using SIMD-optimized search
        let null_pos = find_null_byte(bytes);
        let content = &bytes[..null_pos];

        if content.len() > CAP {
            return Err(AsciiError::TooLong {
                len: content.len(),
                cap: CAP,
            });
        }

        // Validate ASCII
        if let Err((byte, pos)) = simd::validate_ascii_bounded::<CAP>(content) {
            return Err(AsciiError::InvalidByte { byte, pos });
        }

        // Build the string
        let mut data = [0u8; CAP];
        data[..content.len()].copy_from_slice(content);

        let hash = hash::hash::<CAP>(content);
        let header = hash::pack_header(content.len() as u16, hash);

        Ok(Self { header, data })
    }

    /// Creates an ASCII string from a reference to a fixed-size buffer.
    ///
    /// Similar to [`try_from_null_terminated`](Self::try_from_null_terminated),
    /// but takes `&[u8; CAP]` instead of `&[u8]`. This allows the compiler to
    /// skip bounds checking since the buffer size matches the capacity.
    ///
    /// The string length is determined by the position of the first null byte
    /// (0x00). If no null byte is found, the entire buffer is used.
    ///
    /// # Errors
    ///
    /// Returns [`AsciiError::InvalidByte`] if any byte before the first null
    /// is not valid ASCII (null or > 127).
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// // Reference to a fixed-size buffer (zero-copy from wire format)
    /// let buffer: &[u8; 16] = b"BTC-USD\0\0\0\0\0\0\0\0\0";
    /// let s: AsciiString<16> = AsciiString::try_from_raw_ref(buffer)?;
    /// assert_eq!(s.as_str(), "BTC-USD");
    /// assert_eq!(s.len(), 7);
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn try_from_raw_ref(buffer: &[u8; CAP]) -> Result<Self, AsciiError> {
        let () = Self::_CAP_ASSERT;

        // Find null terminator - buffer is exactly CAP bytes
        let len = find_null_byte(buffer);

        // Validate ASCII (no bounds check needed - len <= CAP guaranteed)
        if let Err((byte, pos)) = simd::validate_ascii_bounded::<CAP>(&buffer[..len]) {
            return Err(AsciiError::InvalidByte { byte, pos });
        }

        // Copy to internal buffer
        let mut data = [0u8; CAP];
        data[..len].copy_from_slice(&buffer[..len]);

        let hash = hash::hash::<CAP>(&buffer[..len]);
        let header = hash::pack_header(len as u16, hash);

        Ok(Self { header, data })
    }

    /// Creates an ASCII string from a fixed-size raw buffer.
    ///
    /// The string length is determined by the position of the first null byte
    /// (0x00). If no null byte is found, the entire buffer is used.
    ///
    /// This is useful when reading from fixed-size fields in binary protocols
    /// (e.g., SBE) where unused bytes are null-padded.
    ///
    /// # Errors
    ///
    /// Returns [`AsciiError::InvalidByte`] if any byte before the first null
    /// is not valid ASCII (null or > 127).
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// // Null-terminated buffer (like from SBE or C strings)
    /// let buffer: [u8; 16] = *b"BTC-USD\0\0\0\0\0\0\0\0\0";
    /// let s: AsciiString<16> = AsciiString::try_from_raw(buffer)?;
    /// assert_eq!(s.as_str(), "BTC-USD");
    /// assert_eq!(s.len(), 7);
    ///
    /// // No null terminator - uses full buffer
    /// let full: [u8; 8] = *b"BTCUSDT!";
    /// let s: AsciiString<8> = AsciiString::try_from_raw(full)?;
    /// assert_eq!(s.len(), 8);
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn try_from_raw(mut buffer: [u8; CAP]) -> Result<Self, AsciiError> {
        let () = Self::_CAP_ASSERT;
        let len = find_null_byte(&buffer);

        // Fast ASCII validation for bytes before the null terminator
        // Use bounded version since len <= CAP
        if let Err((byte, pos)) = simd::validate_ascii_bounded::<CAP>(&buffer[..len]) {
            return Err(AsciiError::InvalidByte { byte, pos });
        }

        // Zero-pad beyond content for word-aligned processing invariant
        buffer[len..].fill(0);

        let hash = hash::hash::<CAP>(&buffer[..len]);
        let header = hash::pack_header(len as u16, hash);

        Ok(Self {
            header,
            data: buffer,
        })
    }

    /// Creates an ASCII string from a fixed-size raw buffer without validation.
    ///
    /// The string length is determined by the position of the first null byte
    /// (0x00). If no null byte is found, the entire buffer is used.
    ///
    /// # Safety
    ///
    /// The caller must ensure that all bytes before the first null byte are
    /// valid ASCII (0x01-0x7F). Violating this causes undefined behavior in
    /// code that assumes ASCII validity.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let buffer: [u8; 16] = *b"BTC-USD\0\0\0\0\0\0\0\0\0";
    /// // SAFETY: bytes before null are valid ASCII
    /// let s: AsciiString<16> = unsafe { AsciiString::from_raw_unchecked(buffer) };
    /// assert_eq!(s.as_str(), "BTC-USD");
    /// ```
    #[inline]
    pub unsafe fn from_raw_unchecked(mut buffer: [u8; CAP]) -> Self {
        let () = Self::_CAP_ASSERT;
        let len = find_null_byte(&buffer);

        debug_assert!(
            buffer[..len].iter().all(|&b| b > 0 && b <= 127),
            "buffer contains null or non-ASCII before terminator"
        );

        // Zero-pad beyond content for word-aligned processing invariant
        buffer[len..].fill(0);

        let hash = hash::hash::<CAP>(&buffer[..len]);
        let header = hash::pack_header(len as u16, hash);

        Self {
            header,
            data: buffer,
        }
    }

    /// Creates an ASCII string from a right-padded fixed-size buffer.
    ///
    /// Strips trailing bytes that match the specified `pad` value to determine
    /// the string length. Useful for space-padded fields common in some protocols.
    ///
    /// # Errors
    ///
    /// Returns [`AsciiError::InvalidByte`] if any non-padding byte is not valid
    /// ASCII (null or > 127).
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// // Space-padded buffer
    /// let buffer: [u8; 16] = *b"BTC-USD         ";
    /// let s: AsciiString<16> = AsciiString::try_from_right_padded(buffer, b' ')?;
    /// assert_eq!(s.as_str(), "BTC-USD");
    /// assert_eq!(s.len(), 7);
    ///
    /// // All padding - results in empty string
    /// let empty: [u8; 8] = [b' '; 8];
    /// let s: AsciiString<8> = AsciiString::try_from_right_padded(empty, b' ')?;
    /// assert!(s.is_empty());
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn try_from_right_padded(mut buffer: [u8; CAP], pad: u8) -> Result<Self, AsciiError> {
        let () = Self::_CAP_ASSERT;
        // Find length by stripping trailing pad bytes
        let len = buffer.iter().rposition(|&b| b != pad).map_or(0, |i| i + 1);

        // Fast ASCII validation
        // Use bounded version since len <= CAP
        if let Err((byte, pos)) = simd::validate_ascii_bounded::<CAP>(&buffer[..len]) {
            return Err(AsciiError::InvalidByte { byte, pos });
        }

        // Zero-pad beyond content for word-aligned processing invariant
        buffer[len..].fill(0);

        let hash = hash::hash::<CAP>(&buffer[..len]);
        let header = hash::pack_header(len as u16, hash);

        Ok(Self {
            header,
            data: buffer,
        })
    }
}

// =============================================================================
// Accessors
// =============================================================================

impl<const CAP: usize> AsciiString<CAP> {
    /// Returns the length of the string in bytes.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("hello")?;
    /// assert_eq!(s.len(), 5);
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline(always)]
    pub const fn len(&self) -> usize {
        unpack_len(self.header)
    }

    /// Returns `true` if the string is empty.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let empty: AsciiString<32> = AsciiString::empty();
    /// assert!(empty.is_empty());
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("x")?;
    /// assert!(!s.is_empty());
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline(always)]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the maximum capacity of the string.
    ///
    /// This is always equal to the const generic `CAP`.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let s: AsciiString<32> = AsciiString::empty();
    /// assert_eq!(s.capacity(), 32);
    /// ```
    #[inline(always)]
    pub const fn capacity(&self) -> usize {
        CAP
    }

    /// Returns the string as a byte slice.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("hello")?;
    /// assert_eq!(s.as_bytes(), b"hello");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline(always)]
    pub fn as_bytes(&self) -> &[u8] {
        // SAFETY: len is always <= CAP and data[..len] contains valid ASCII
        unsafe { self.data.get_unchecked(..self.len()) }
    }

    /// Returns the string as a `&str`.
    ///
    /// This is a zero-cost conversion since ASCII is valid UTF-8.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("hello")?;
    /// assert_eq!(s.as_str(), "hello");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline(always)]
    pub fn as_str(&self) -> &str {
        // SAFETY: ASCII is always valid UTF-8
        unsafe { core::str::from_utf8_unchecked(self.as_bytes()) }
    }

    /// Returns a borrowed `&AsciiStr` view of this string.
    ///
    /// This is a zero-cost conversion that provides access to the `AsciiStr`
    /// API without copying.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::{AsciiString, AsciiStr};
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("hello")?;
    /// let ascii_str: &AsciiStr = s.as_ascii_str();
    /// assert_eq!(ascii_str.len(), 5);
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline(always)]
    pub fn as_ascii_str(&self) -> &AsciiStr {
        // SAFETY: AsciiString data is valid ASCII
        unsafe { AsciiStr::from_bytes_unchecked(self.as_bytes()) }
    }

    /// Returns the packed header (for advanced use).
    ///
    /// The header contains both hash (bits 0-47) and length (bits 48-63).
    /// This is primarily useful for debugging or low-level operations.
    #[inline(always)]
    pub const fn header(&self) -> u64 {
        self.header
    }

    /// Returns the full fixed-size buffer.
    ///
    /// The first `self.len()` bytes contain the string content.
    /// Remaining bytes are zero-padded. Useful for wire formats that
    /// require fixed-size fields.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let s: AsciiString<16> = AsciiString::try_from("hello")?;
    /// let raw: [u8; 16] = s.into_raw();
    /// assert_eq!(&raw[..5], b"hello");
    /// assert_eq!(&raw[5..], &[0u8; 11]); // zero-padded
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    #[must_use]
    pub const fn into_raw(self) -> [u8; CAP] {
        self.data
    }

    /// Returns a reference to the full fixed-size buffer.
    ///
    /// This provides direct access to the underlying `[u8; CAP]` array,
    /// which is useful for wire formats (like SBE) that expect fixed-size
    /// byte arrays.
    ///
    /// The first `self.len()` bytes contain the string content.
    /// Remaining bytes are zero-padded.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let s: AsciiString<16> = AsciiString::try_from("Hello")?;
    /// let raw: &[u8; 16] = s.as_raw();
    /// assert_eq!(&raw[..5], b"Hello");
    /// assert_eq!(&raw[5..], &[0u8; 11]);
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    #[must_use]
    pub const fn as_raw(&self) -> &[u8; CAP] {
        &self.data
    }

    /// Returns the character at the given index, or `None` if out of bounds.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::{AsciiString, AsciiChar};
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("hello")?;
    /// assert_eq!(s.get(0), Some(AsciiChar::h));
    /// assert_eq!(s.get(4), Some(AsciiChar::o));
    /// assert_eq!(s.get(5), None);
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn get(&self, index: usize) -> Option<AsciiChar> {
        if index < self.len() {
            // SAFETY: index is within bounds and data contains valid ASCII
            Some(unsafe { AsciiChar::new_unchecked(self.data[index]) })
        } else {
            None
        }
    }

    /// Returns the character at the given index without bounds checking.
    ///
    /// # Safety
    ///
    /// The index must be less than `self.len()`.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::{AsciiString, AsciiChar};
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("hello")?;
    /// // SAFETY: 0 < 5
    /// let ch = unsafe { s.get_unchecked(0) };
    /// assert_eq!(ch, AsciiChar::h);
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub unsafe fn get_unchecked(&self, index: usize) -> AsciiChar {
        debug_assert!(index < self.len());
        // SAFETY: caller guarantees index < len, data contains valid ASCII
        unsafe { AsciiChar::new_unchecked(*self.data.get_unchecked(index)) }
    }

    /// Returns an iterator over the characters in the string.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::{AsciiString, AsciiChar};
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("ABC")?;
    /// let chars: Vec<_> = s.chars().collect();
    /// assert_eq!(chars, vec![AsciiChar::A, AsciiChar::B, AsciiChar::C]);
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn chars(&self) -> impl Iterator<Item = AsciiChar> + '_ {
        self.as_bytes().iter().map(|&b| {
            // SAFETY: all bytes in the string are valid ASCII
            unsafe { AsciiChar::new_unchecked(b) }
        })
    }

    /// Returns an iterator over the bytes in the string.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("ABC")?;
    /// let bytes: Vec<_> = s.bytes().collect();
    /// assert_eq!(bytes, vec![b'A', b'B', b'C']);
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn bytes(&self) -> impl Iterator<Item = u8> + '_ {
        self.as_bytes().iter().copied()
    }

    /// Returns the first character, or `None` if the string is empty.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::{AsciiString, AsciiChar};
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("hello")?;
    /// assert_eq!(s.first(), Some(AsciiChar::h));
    ///
    /// let empty: AsciiString<32> = AsciiString::empty();
    /// assert_eq!(empty.first(), None);
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn first(&self) -> Option<AsciiChar> {
        self.get(0)
    }

    /// Returns the last character, or `None` if the string is empty.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::{AsciiString, AsciiChar};
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("hello")?;
    /// assert_eq!(s.last(), Some(AsciiChar::o));
    ///
    /// let empty: AsciiString<32> = AsciiString::empty();
    /// assert_eq!(empty.last(), None);
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn last(&self) -> Option<AsciiChar> {
        if self.is_empty() {
            None
        } else {
            self.get(self.len() - 1)
        }
    }
}

// =============================================================================
// Capacity Conversion
// =============================================================================

impl<const CAP: usize> AsciiString<CAP> {
    /// Converts to a larger capacity `AsciiString`.
    ///
    /// The hash is preserved since it's computed from content, not capacity.
    /// This is a data copy, not a reference.
    ///
    /// # Compile-time Checks
    ///
    /// - `NEW_CAP >= CAP` (must be widening, not narrowing)
    /// - `NEW_CAP.is_multiple_of(8)` (alignment requirement)
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let small: AsciiString<16> = AsciiString::try_from("hello")?;
    /// let large: AsciiString<32> = small.widen();
    /// assert_eq!(small.as_str(), large.as_str());
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn widen<const NEW_CAP: usize>(self) -> AsciiString<NEW_CAP> {
        const { assert!(NEW_CAP.is_multiple_of(8), "NEW_CAP must be a multiple of 8") }
        const {
            assert!(
                NEW_CAP >= CAP,
                "widen requires NEW_CAP >= CAP; use tighten for smaller"
            );
        }

        let mut data = [0u8; NEW_CAP];
        // Copy content bytes (rest is already zeroed)
        data[..CAP].copy_from_slice(&self.data);

        AsciiString {
            header: self.header, // hash + len unchanged
            data,
        }
    }

    /// Converts to a smaller capacity `AsciiString`.
    ///
    /// Returns `Err(AsciiError::TooLong)` if the content doesn't fit.
    /// The hash is preserved since it's computed from content.
    ///
    /// # Compile-time Checks
    ///
    /// - `NEW_CAP <= CAP` (must be tightening, not widening)
    /// - `NEW_CAP.is_multiple_of(8)` (alignment requirement)
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::{AsciiString, AsciiError};
    ///
    /// let large: AsciiString<32> = AsciiString::try_from("hello")?;
    /// let small: AsciiString<16> = large.tighten()?;
    /// assert_eq!(large.as_str(), small.as_str());
    ///
    /// // Content too long for target capacity
    /// let long: AsciiString<32> = AsciiString::try_from("this is a longer string")?;
    /// assert!(matches!(long.tighten::<16>(), Err(AsciiError::TooLong { .. })));
    /// # Ok::<(), AsciiError>(())
    /// ```
    #[inline]
    pub fn tighten<const NEW_CAP: usize>(self) -> Result<AsciiString<NEW_CAP>, crate::AsciiError> {
        const { assert!(NEW_CAP.is_multiple_of(8), "NEW_CAP must be a multiple of 8") }
        const {
            assert!(
                NEW_CAP <= CAP,
                "tighten requires NEW_CAP <= CAP; use widen for larger"
            );
        }

        if self.len() > NEW_CAP {
            return Err(crate::AsciiError::TooLong {
                len: self.len(),
                cap: NEW_CAP,
            });
        }

        let mut data = [0u8; NEW_CAP];
        data.copy_from_slice(&self.data[..NEW_CAP]);

        Ok(AsciiString {
            header: self.header, // hash + len unchanged
            data,
        })
    }
}

// =============================================================================
// Comparison Methods
// =============================================================================

impl<const CAP: usize> AsciiString<CAP> {
    /// Compares two ASCII strings for equality, ignoring ASCII case.
    ///
    /// This performs a case-insensitive comparison where 'A'-'Z' are considered
    /// equal to 'a'-'z'.
    ///
    /// # Fast Path
    ///
    /// If the lengths differ, returns `false` immediately without comparing bytes.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let s1: AsciiString<32> = AsciiString::try_from("Hello")?;
    /// let s2: AsciiString<32> = AsciiString::try_from("HELLO")?;
    /// let s3: AsciiString<32> = AsciiString::try_from("hello")?;
    /// let s4: AsciiString<32> = AsciiString::try_from("world")?;
    ///
    /// assert!(s1.eq_ignore_ascii_case(&s2));
    /// assert!(s1.eq_ignore_ascii_case(&s3));
    /// assert!(!s1.eq_ignore_ascii_case(&s4));
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn eq_ignore_ascii_case(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }
        // Full-buffer processing: with same-length strings, padding regions
        // are identical (both zero). The compiler sees CAP as the length,
        // enabling full unrolling with no remainder loops.
        crate::simd::eq_ignore_ascii_case(&self.data, &other.data)
    }

    /// Returns `true` if the string starts with the given prefix.
    ///
    /// Accepts `&[u8]`, `&str`, or anything that implements `AsRef<[u8]>`.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("BTC-USD")?;
    ///
    /// assert!(s.starts_with(b"BTC"));
    /// assert!(s.starts_with("BTC-"));
    /// assert!(!s.starts_with("ETH"));
    /// assert!(s.starts_with("")); // Empty prefix always matches
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn starts_with<P: AsRef<[u8]>>(&self, prefix: P) -> bool {
        self.as_bytes().starts_with(prefix.as_ref())
    }

    /// Returns `true` if the string ends with the given suffix.
    ///
    /// Accepts `&[u8]`, `&str`, or anything that implements `AsRef<[u8]>`.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("BTC-USD")?;
    ///
    /// assert!(s.ends_with(b"USD"));
    /// assert!(s.ends_with("-USD"));
    /// assert!(!s.ends_with("EUR"));
    /// assert!(s.ends_with("")); // Empty suffix always matches
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn ends_with<S: AsRef<[u8]>>(&self, suffix: S) -> bool {
        self.as_bytes().ends_with(suffix.as_ref())
    }

    /// Returns the string with the given prefix removed.
    ///
    /// Returns `Some(stripped)` if the string starts with the prefix,
    /// or `None` if it doesn't.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("USD-BTC")?;
    ///
    /// let stripped = s.strip_prefix("USD-").unwrap();
    /// assert_eq!(stripped.as_str(), "BTC");
    ///
    /// // Prefix not found
    /// assert!(s.strip_prefix("EUR-").is_none());
    ///
    /// // Empty prefix always matches
    /// let same = s.strip_prefix("").unwrap();
    /// assert_eq!(same.as_str(), "USD-BTC");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn strip_prefix<P: AsRef<[u8]>>(&self, prefix: P) -> Option<&AsciiStr> {
        let prefix = prefix.as_ref();
        if self.as_bytes().starts_with(prefix) {
            // SAFETY: Prefix is within bounds, remaining bytes are valid ASCII
            Some(unsafe { AsciiStr::from_bytes_unchecked(&self.as_bytes()[prefix.len()..]) })
        } else {
            None
        }
    }

    /// Returns the string with the given suffix removed.
    ///
    /// Returns `Some(stripped)` if the string ends with the suffix,
    /// or `None` if it doesn't.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("BTC-USD")?;
    ///
    /// let stripped = s.strip_suffix("-USD").unwrap();
    /// assert_eq!(stripped.as_str(), "BTC");
    ///
    /// // Suffix not found
    /// assert!(s.strip_suffix("-EUR").is_none());
    ///
    /// // Empty suffix always matches
    /// let same = s.strip_suffix("").unwrap();
    /// assert_eq!(same.as_str(), "BTC-USD");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn strip_suffix<S: AsRef<[u8]>>(&self, suffix: S) -> Option<&AsciiStr> {
        let suffix = suffix.as_ref();
        if self.as_bytes().ends_with(suffix) {
            let new_len = self.len() - suffix.len();
            // SAFETY: new_len is within bounds, bytes are valid ASCII
            Some(unsafe { AsciiStr::from_bytes_unchecked(&self.as_bytes()[..new_len]) })
        } else {
            None
        }
    }

    /// Returns `true` if the string contains the given substring.
    ///
    /// Accepts `&[u8]`, `&str`, or anything that implements `AsRef<[u8]>`.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("BTC-USD")?;
    ///
    /// assert!(s.contains(b"-"));
    /// assert!(s.contains("TC-US"));
    /// assert!(!s.contains("ETH"));
    /// assert!(s.contains("")); // Empty needle always found
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn contains<N: AsRef<[u8]>>(&self, needle: N) -> bool {
        let needle = needle.as_ref();
        if needle.is_empty() {
            return true;
        }
        // Use the standard library's optimized substring search
        self.as_bytes()
            .windows(needle.len())
            .any(|window| window == needle)
    }

    // =========================================================================
    // Find Methods
    // =========================================================================

    /// Returns the byte index of the first occurrence of a byte.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("BTC-USD")?;
    /// assert_eq!(s.find_byte(b'-'), Some(3));
    /// assert_eq!(s.find_byte(b'X'), None);
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn find_byte(&self, byte: u8) -> Option<usize> {
        self.as_bytes().iter().position(|&b| b == byte)
    }

    /// Returns the byte index of the first occurrence of an ASCII character.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::{AsciiString, AsciiChar};
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("BTC-USD")?;
    /// assert_eq!(s.find_char(AsciiChar::MINUS), Some(3));
    /// assert_eq!(s.find_char(AsciiChar::X), None);
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn find_char(&self, ch: AsciiChar) -> Option<usize> {
        self.find_byte(ch.as_u8())
    }

    /// Returns the byte index of the first occurrence of a byte pattern.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("BTC-USD-PERP")?;
    /// assert_eq!(s.find(b"-USD"), Some(3));
    /// assert_eq!(s.find(b"ETH"), None);
    /// assert_eq!(s.find(b""), Some(0)); // Empty pattern always matches at start
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn find(&self, needle: &[u8]) -> Option<usize> {
        if needle.is_empty() {
            return Some(0);
        }
        self.as_bytes()
            .windows(needle.len())
            .position(|window| window == needle)
    }

    /// Returns the byte index of the last occurrence of a byte.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("BTC-USD-PERP")?;
    /// assert_eq!(s.rfind_byte(b'-'), Some(7));
    /// assert_eq!(s.rfind_byte(b'X'), None);
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn rfind_byte(&self, byte: u8) -> Option<usize> {
        self.as_bytes().iter().rposition(|&b| b == byte)
    }

    /// Returns the byte index of the last occurrence of an ASCII character.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::{AsciiString, AsciiChar};
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("BTC-USD-PERP")?;
    /// assert_eq!(s.rfind_char(AsciiChar::MINUS), Some(7));
    /// assert_eq!(s.rfind_char(AsciiChar::X), None);
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn rfind_char(&self, ch: AsciiChar) -> Option<usize> {
        self.rfind_byte(ch.as_u8())
    }

    /// Returns the byte index of the last occurrence of a byte pattern.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("BTC-USD-PERP")?;
    /// assert_eq!(s.rfind(b"-"), Some(7));
    /// assert_eq!(s.rfind(b"USD"), Some(4));
    /// assert_eq!(s.rfind(b"ETH"), None);
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn rfind(&self, needle: &[u8]) -> Option<usize> {
        if needle.is_empty() {
            return Some(self.len());
        }
        if needle.len() > self.len() {
            return None;
        }
        self.as_bytes()
            .windows(needle.len())
            .rposition(|window| window == needle)
    }

    // =========================================================================
    // Trim Methods (return borrowed &AsciiStr)
    // =========================================================================

    /// Returns a string slice with leading and trailing ASCII whitespace removed.
    ///
    /// ASCII whitespace is defined as: space (0x20), tab (0x09), newline (0x0A),
    /// carriage return (0x0D), form feed (0x0C), and vertical tab (0x0B).
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("  hello  ")?;
    /// assert_eq!(s.trim().as_str(), "hello");
    ///
    /// let tabs: AsciiString<32> = AsciiString::try_from("\t\nworld\r\n")?;
    /// assert_eq!(tabs.trim().as_str(), "world");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn trim(&self) -> &AsciiStr {
        self.trim_start().trim_end()
    }

    /// Returns a string slice with leading ASCII whitespace removed.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("  hello  ")?;
    /// assert_eq!(s.trim_start().as_str(), "hello  ");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn trim_start(&self) -> &AsciiStr {
        let bytes = self.as_bytes();
        let start = bytes
            .iter()
            .position(|&b| !b.is_ascii_whitespace())
            .unwrap_or(bytes.len());
        // SAFETY: trimmed slice is still valid ASCII
        unsafe { AsciiStr::from_bytes_unchecked(&bytes[start..]) }
    }

    /// Returns a string slice with trailing ASCII whitespace removed.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("  hello  ")?;
    /// assert_eq!(s.trim_end().as_str(), "  hello");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn trim_end(&self) -> &AsciiStr {
        let bytes = self.as_bytes();
        let end = bytes
            .iter()
            .rposition(|&b| !b.is_ascii_whitespace())
            .map_or(0, |i| i + 1);
        // SAFETY: trimmed slice is still valid ASCII
        unsafe { AsciiStr::from_bytes_unchecked(&bytes[..end]) }
    }

    // =========================================================================
    // Split Methods
    // =========================================================================

    /// Returns an iterator over substrings separated by the given delimiter.
    ///
    /// The iterator yields `&AsciiStr` slices that do not include the delimiter.
    /// If the string starts or ends with the delimiter, or contains consecutive
    /// delimiters, empty slices are yielded.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::{AsciiString, AsciiChar};
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("BTC-USD-PERP")?;
    /// let parts: Vec<_> = s.split(AsciiChar::MINUS).map(|s| s.as_str()).collect();
    /// assert_eq!(parts, vec!["BTC", "USD", "PERP"]);
    ///
    /// // Empty parts from consecutive or edge delimiters
    /// let s2: AsciiString<32> = AsciiString::try_from("-a--b-")?;
    /// let parts2: Vec<_> = s2.split(AsciiChar::MINUS).map(|s| s.as_str()).collect();
    /// assert_eq!(parts2, vec!["", "a", "", "b", ""]);
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn split(&self, delimiter: AsciiChar) -> Split<'_> {
        Split {
            remainder: self.as_bytes(),
            delimiter: delimiter.as_u8(),
            finished: false,
        }
    }

    /// Splits the string on the first occurrence of the delimiter.
    ///
    /// Returns `Some((before, after))` if the delimiter is found, where
    /// `before` is the substring before the delimiter and `after` is the
    /// substring after it. The delimiter itself is not included in either part.
    ///
    /// Returns `None` if the delimiter is not found.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::{AsciiString, AsciiChar};
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("BTC-USD")?;
    /// let (base, quote) = s.split_once(AsciiChar::MINUS).unwrap();
    /// assert_eq!(base.as_str(), "BTC");
    /// assert_eq!(quote.as_str(), "USD");
    ///
    /// // No delimiter found
    /// let s2: AsciiString<32> = AsciiString::try_from("BTCUSD")?;
    /// assert!(s2.split_once(AsciiChar::MINUS).is_none());
    ///
    /// // Delimiter at start
    /// let s3: AsciiString<32> = AsciiString::try_from("-USD")?;
    /// let (before, after) = s3.split_once(AsciiChar::MINUS).unwrap();
    /// assert_eq!(before.as_str(), "");
    /// assert_eq!(after.as_str(), "USD");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn split_once(&self, delimiter: AsciiChar) -> Option<(&AsciiStr, &AsciiStr)> {
        let bytes = self.as_bytes();
        let pos = bytes.iter().position(|&b| b == delimiter.as_u8())?;
        // SAFETY: pos is within bounds, and bytes contain valid ASCII
        let before = unsafe { AsciiStr::from_bytes_unchecked(&bytes[..pos]) };
        // SAFETY: pos is within bounds, and bytes contain valid ASCII
        let after = unsafe { AsciiStr::from_bytes_unchecked(&bytes[pos + 1..]) };
        Some((before, after))
    }
}

/// An iterator over substrings of an ASCII string, separated by a delimiter.
///
/// Created by the [`AsciiString::split`] method.
#[derive(Debug, Clone)]
pub struct Split<'a> {
    pub(crate) remainder: &'a [u8],
    pub(crate) delimiter: u8,
    pub(crate) finished: bool,
}

impl<'a> Iterator for Split<'a> {
    type Item = &'a AsciiStr;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            return None;
        }

        if let Some(pos) = self.remainder.iter().position(|&b| b == self.delimiter) {
            let part = &self.remainder[..pos];
            self.remainder = &self.remainder[pos + 1..];
            // SAFETY: part is a slice of valid ASCII bytes
            Some(unsafe { AsciiStr::from_bytes_unchecked(part) })
        } else {
            self.finished = true;
            // SAFETY: remainder is valid ASCII bytes
            Some(unsafe { AsciiStr::from_bytes_unchecked(self.remainder) })
        }
    }
}

// =============================================================================
// Transformations
// =============================================================================

impl<const CAP: usize> AsciiString<CAP> {
    /// Returns a new string with all ASCII letters converted to uppercase.
    ///
    /// This consumes `self` and returns a new `AsciiString` with the
    /// transformation applied. The hash is recomputed for the new content.
    ///
    /// Non-alphabetic characters are unchanged.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("Hello, World!")?;
    /// let upper = s.to_ascii_uppercase();
    /// assert_eq!(upper.as_str(), "HELLO, WORLD!");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn to_ascii_uppercase(self) -> Self {
        let len = self.len();
        let mut data = self.data;

        // Full-buffer processing: zeros are not letters, so case conversion
        // leaves them unchanged. The compiler sees CAP as the length, enabling
        // full unrolling with no remainder loops.
        crate::simd::make_uppercase(&mut data);

        let hash = hash::hash::<CAP>(&data[..len]);
        let header = hash::pack_header(len as u16, hash);

        Self { header, data }
    }

    /// Returns a new string with all ASCII letters converted to lowercase.
    ///
    /// This consumes `self` and returns a new `AsciiString` with the
    /// transformation applied. The hash is recomputed for the new content.
    ///
    /// Non-alphabetic characters are unchanged.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("Hello, World!")?;
    /// let lower = s.to_ascii_lowercase();
    /// assert_eq!(lower.as_str(), "hello, world!");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn to_ascii_lowercase(self) -> Self {
        let len = self.len();
        let mut data = self.data;

        // Full-buffer processing: zeros are not letters, so case conversion
        // leaves them unchanged. The compiler sees CAP as the length, enabling
        // full unrolling with no remainder loops.
        crate::simd::make_lowercase(&mut data);

        let hash = hash::hash::<CAP>(&data[..len]);
        let header = hash::pack_header(len as u16, hash);

        Self { header, data }
    }

    /// Returns a new string truncated to the specified length.
    ///
    /// This consumes `self` and returns a new `AsciiString` with at most
    /// `new_len` bytes. The hash is recomputed for the new content.
    ///
    /// # Panics
    ///
    /// Panics if `new_len > self.len()`.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("Hello, World!")?;
    /// let truncated = s.truncated(5);
    /// assert_eq!(truncated.as_str(), "Hello");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn truncated(self, new_len: usize) -> Self {
        assert!(
            new_len <= self.len(),
            "new_len ({}) exceeds current length ({})",
            new_len,
            self.len()
        );

        let mut data = self.data;
        data[new_len..].fill(0);

        let hash = hash::hash::<CAP>(&data[..new_len]);
        let header = hash::pack_header(new_len as u16, hash);

        Self { header, data }
    }

    /// Returns a new string truncated to the specified length, or `None` if
    /// `new_len` exceeds the current length.
    ///
    /// This is the non-panicking version of [`truncated`](Self::truncated).
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("Hello")?;
    ///
    /// assert_eq!(s.try_truncated(3).map(|t| t.as_str().to_owned()), Some("Hel".to_owned()));
    /// assert_eq!(s.try_truncated(5).map(|t| t.as_str().to_owned()), Some("Hello".to_owned()));
    /// assert_eq!(s.try_truncated(10), None); // Exceeds length
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn try_truncated(self, new_len: usize) -> Option<Self> {
        if new_len > self.len() {
            return None;
        }

        let mut data = self.data;
        data[new_len..].fill(0);

        let hash = hash::hash::<CAP>(&data[..new_len]);
        let header = hash::pack_header(new_len as u16, hash);

        Some(Self { header, data })
    }

    // =========================================================================
    // Trimmed Methods (return owned Self with recomputed hash)
    // =========================================================================

    /// Returns a new string with leading and trailing ASCII whitespace removed.
    ///
    /// This consumes `self` and returns a new `AsciiString` with the whitespace
    /// removed. The hash is recomputed for the new content.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("  hello  ")?;
    /// let trimmed = s.trimmed();
    /// assert_eq!(trimmed.as_str(), "hello");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn trimmed(self) -> Self {
        let bytes = self.as_bytes();
        let start = bytes
            .iter()
            .position(|&b| !b.is_ascii_whitespace())
            .unwrap_or(bytes.len());
        let end = bytes
            .iter()
            .rposition(|&b| !b.is_ascii_whitespace())
            .map_or(0, |i| i + 1);

        let new_len = end.saturating_sub(start);
        let mut data = [0u8; CAP];
        data[..new_len].copy_from_slice(&bytes[start..end]);

        let hash = hash::hash::<CAP>(&data[..new_len]);
        let header = hash::pack_header(new_len as u16, hash);

        Self { header, data }
    }

    /// Returns a new string with leading ASCII whitespace removed.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("  hello  ")?;
    /// let trimmed = s.trimmed_start();
    /// assert_eq!(trimmed.as_str(), "hello  ");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn trimmed_start(self) -> Self {
        let bytes = self.as_bytes();
        let start = bytes
            .iter()
            .position(|&b| !b.is_ascii_whitespace())
            .unwrap_or(bytes.len());

        let new_len = bytes.len() - start;
        let mut data = [0u8; CAP];
        data[..new_len].copy_from_slice(&bytes[start..]);

        let hash = hash::hash::<CAP>(&data[..new_len]);
        let header = hash::pack_header(new_len as u16, hash);

        Self { header, data }
    }

    /// Returns a new string with trailing ASCII whitespace removed.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("  hello  ")?;
    /// let trimmed = s.trimmed_end();
    /// assert_eq!(trimmed.as_str(), "  hello");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn trimmed_end(self) -> Self {
        let bytes = self.as_bytes();
        let new_len = bytes
            .iter()
            .rposition(|&b| !b.is_ascii_whitespace())
            .map_or(0, |i| i + 1);

        let mut data = self.data;
        data[new_len..].fill(0);

        let hash = hash::hash::<CAP>(&data[..new_len]);
        let header = hash::pack_header(new_len as u16, hash);

        Self { header, data }
    }

    // =========================================================================
    // Replace Methods
    // =========================================================================

    /// Returns a new string with all occurrences of a character replaced.
    ///
    /// Since this is a character-for-character replacement, the length remains
    /// the same and this operation is infallible.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::{AsciiString, AsciiChar};
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("BTC-USD-PERP")?;
    /// let replaced = s.replaced_char(AsciiChar::MINUS, AsciiChar::UNDERSCORE);
    /// assert_eq!(replaced.as_str(), "BTC_USD_PERP");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn replaced_char(self, from: AsciiChar, to: AsciiChar) -> Self {
        debug_assert!(to.as_u8() != 0, "cannot replace with null byte");
        let len = self.len();
        let mut data = self.data;
        let from_byte = from.as_u8();
        let to_byte = to.as_u8();

        for byte in &mut data[..len] {
            if *byte == from_byte {
                *byte = to_byte;
            }
        }

        let hash = hash::hash::<CAP>(&data[..len]);
        let header = hash::pack_header(len as u16, hash);

        Self { header, data }
    }

    /// Returns a new string with the first occurrence of a character replaced.
    ///
    /// Since this is a character-for-character replacement, the length remains
    /// the same and this operation is infallible.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::{AsciiString, AsciiChar};
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("BTC-USD-PERP")?;
    /// let replaced = s.replace_first_char(AsciiChar::MINUS, AsciiChar::UNDERSCORE);
    /// assert_eq!(replaced.as_str(), "BTC_USD-PERP");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn replace_first_char(self, from: AsciiChar, to: AsciiChar) -> Self {
        debug_assert!(to.as_u8() != 0, "cannot replace with null byte");
        let len = self.len();
        let mut data = self.data;
        let from_byte = from.as_u8();
        let to_byte = to.as_u8();

        for byte in &mut data[..len] {
            if *byte == from_byte {
                *byte = to_byte;
                break;
            }
        }

        let hash = hash::hash::<CAP>(&data[..len]);
        let header = hash::pack_header(len as u16, hash);

        Self { header, data }
    }

    /// Returns a new string with all occurrences of a pattern replaced.
    ///
    /// # Errors
    ///
    /// Returns [`AsciiError::TooLong`] if the result exceeds capacity.
    /// Returns [`AsciiError::InvalidByte`] if `to` contains non-ASCII bytes.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("foo bar foo")?;
    /// let replaced = s.replaced(b"foo", b"baz")?;
    /// assert_eq!(replaced.as_str(), "baz bar baz");
    ///
    /// // Length change
    /// let s2: AsciiString<32> = AsciiString::try_from("aaa")?;
    /// let replaced2 = s2.replaced(b"a", b"bb")?;
    /// assert_eq!(replaced2.as_str(), "bbbbbb");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    pub fn replaced(&self, from: &[u8], to: &[u8]) -> Result<Self, AsciiError> {
        // Validate replacement is ASCII
        if let Err((byte, pos)) = simd::validate_ascii(to) {
            return Err(AsciiError::InvalidByte { byte, pos });
        }

        // Empty pattern - nothing to replace
        if from.is_empty() {
            return Ok(*self);
        }

        let src = self.as_bytes();
        let mut result = [0u8; CAP];
        let mut result_len = 0;
        let mut i = 0;

        while i < src.len() {
            if i + from.len() <= src.len() && &src[i..i + from.len()] == from {
                // Found a match, insert replacement
                if result_len + to.len() > CAP {
                    return Err(AsciiError::TooLong {
                        len: result_len + to.len(),
                        cap: CAP,
                    });
                }
                result[result_len..result_len + to.len()].copy_from_slice(to);
                result_len += to.len();
                i += from.len();
            } else {
                // No match, copy byte
                if result_len >= CAP {
                    return Err(AsciiError::TooLong {
                        len: result_len + 1,
                        cap: CAP,
                    });
                }
                result[result_len] = src[i];
                result_len += 1;
                i += 1;
            }
        }

        let hash = hash::hash::<CAP>(&result[..result_len]);
        let header = hash::pack_header(result_len as u16, hash);

        Ok(Self {
            header,
            data: result,
        })
    }

    /// Returns a new string with the first occurrence of a pattern replaced.
    ///
    /// # Errors
    ///
    /// Returns [`AsciiError::TooLong`] if the result exceeds capacity.
    /// Returns [`AsciiError::InvalidByte`] if `to` contains non-ASCII bytes.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("foo bar foo")?;
    /// let replaced = s.replace_first(b"foo", b"baz")?;
    /// assert_eq!(replaced.as_str(), "baz bar foo");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    pub fn replace_first(&self, from: &[u8], to: &[u8]) -> Result<Self, AsciiError> {
        // Validate replacement is ASCII
        if let Err((byte, pos)) = simd::validate_ascii(to) {
            return Err(AsciiError::InvalidByte { byte, pos });
        }

        // Empty pattern or no match - return copy
        if from.is_empty() {
            return Ok(*self);
        }

        let src = self.as_bytes();

        // Find first occurrence
        let Some(pos) = src.windows(from.len()).position(|w| w == from) else {
            return Ok(*self);
        };

        // Calculate new length
        let new_len = src.len() - from.len() + to.len();
        if new_len > CAP {
            return Err(AsciiError::TooLong {
                len: new_len,
                cap: CAP,
            });
        }

        let mut result = [0u8; CAP];
        result[..pos].copy_from_slice(&src[..pos]);
        result[pos..pos + to.len()].copy_from_slice(to);
        result[pos + to.len()..new_len].copy_from_slice(&src[pos + from.len()..]);

        let hash = hash::hash::<CAP>(&result[..new_len]);
        let header = hash::pack_header(new_len as u16, hash);

        Ok(Self {
            header,
            data: result,
        })
    }

    // =========================================================================
    // Classification Helpers
    // =========================================================================

    /// Returns `true` if all characters in the string are printable ASCII.
    ///
    /// Printable ASCII is defined as bytes in the range 0x20 (space) to 0x7E (tilde),
    /// inclusive. This excludes control characters (0x00-0x1F) and DEL (0x7F).
    ///
    /// An empty string returns `true`.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let printable: AsciiString<32> = AsciiString::try_from("Hello, World!").unwrap();
    /// assert!(printable.is_all_printable());
    ///
    /// let with_tab: AsciiString<32> = AsciiString::try_from_bytes(b"Hello\tWorld").unwrap();
    /// assert!(!with_tab.is_all_printable());
    /// ```
    #[inline]
    pub fn is_all_printable(&self) -> bool {
        crate::simd::is_all_printable(self.as_bytes())
    }

    /// Returns `true` if the string contains any control characters.
    ///
    /// Control characters are bytes in the ranges 0x00-0x1F and 0x7F (DEL).
    /// This is the inverse of printable characters.
    ///
    /// An empty string returns `false`.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let normal: AsciiString<32> = AsciiString::try_from("Hello").unwrap();
    /// assert!(!normal.contains_control_chars());
    ///
    /// // FIX protocol uses SOH (0x01) as delimiter
    /// let fix_msg: AsciiString<32> = AsciiString::try_from_bytes(b"8=FIX\x019=5").unwrap();
    /// assert!(fix_msg.contains_control_chars());
    /// ```
    #[inline]
    pub fn contains_control_chars(&self) -> bool {
        crate::simd::contains_control_chars(self.as_bytes())
    }

    /// Returns `true` if all characters are ASCII digits (0-9).
    ///
    /// An empty string returns `true`.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let digits: AsciiString<32> = AsciiString::try_from("12345").unwrap();
    /// assert!(digits.is_numeric());
    ///
    /// let mixed: AsciiString<32> = AsciiString::try_from("123abc").unwrap();
    /// assert!(!mixed.is_numeric());
    ///
    /// let empty: AsciiString<32> = AsciiString::empty();
    /// assert!(empty.is_numeric());
    /// ```
    #[inline]
    pub fn is_numeric(&self) -> bool {
        crate::simd::is_all_numeric(self.as_bytes())
    }

    /// Returns `true` if all characters are ASCII alphanumeric (A-Z, a-z, 0-9).
    ///
    /// An empty string returns `true`.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let alphanum: AsciiString<32> = AsciiString::try_from("ABC123").unwrap();
    /// assert!(alphanum.is_alphanumeric());
    ///
    /// let with_dash: AsciiString<32> = AsciiString::try_from("BTC-USD").unwrap();
    /// assert!(!with_dash.is_alphanumeric());
    ///
    /// let empty: AsciiString<32> = AsciiString::empty();
    /// assert!(empty.is_alphanumeric());
    /// ```
    #[inline]
    pub fn is_alphanumeric(&self) -> bool {
        crate::simd::is_all_alphanumeric(self.as_bytes())
    }

    /// Attempts to convert this string into an `AsciiText`.
    ///
    /// `AsciiText` only allows printable ASCII (0x20-0x7E). This method
    /// validates the content and returns an error if any non-printable
    /// characters are found.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::{AsciiString, AsciiText, AsciiError};
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("Hello").unwrap();
    /// let text: AsciiText<32> = s.try_into_text().unwrap();
    /// assert_eq!(text.as_str(), "Hello");
    ///
    /// let with_ctrl: AsciiString<32> = AsciiString::try_from_bytes(b"Hello\x01").unwrap();
    /// assert!(with_ctrl.try_into_text().is_err());
    /// ```
    #[inline]
    pub fn try_into_text(self) -> Result<crate::AsciiText<CAP>, crate::AsciiError> {
        crate::AsciiText::try_from_ascii_string(self)
    }
}

// =============================================================================
// Integer Parsing
// =============================================================================

crate::parse::impl_parse_int_generic!(AsciiString, as_str);

// =============================================================================
// Integer Formatting
// =============================================================================

crate::format::impl_format_int_generic!(AsciiString, from_bytes_unchecked);

// =============================================================================
// Trait Implementations
// =============================================================================

impl<const CAP: usize> Default for AsciiString<CAP> {
    #[inline]
    fn default() -> Self {
        Self::empty()
    }
}

impl<const CAP: usize> PartialEq for AsciiString<CAP> {
    /// Compares two ASCII strings for equality.
    ///
    /// This uses a fast path: first compare the 64-bit headers (which include
    /// both length and hash). If headers differ, the strings are definitely
    /// not equal. If headers match, fall back to byte comparison.
    ///
    /// The fast path rejects most non-equal strings with a single comparison.
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        // Fast path: header includes length + hash
        // Different headers = definitely different strings
        if self.header != other.header {
            return false;
        }

        // Headers match (same length + same hash)
        // Must verify actual content (rare to reach here for non-equal strings)
        self.as_bytes() == other.as_bytes()
    }
}

impl<const CAP: usize> Eq for AsciiString<CAP> {}

impl<const CAP: usize> core::ops::Deref for AsciiString<CAP> {
    type Target = AsciiStr;

    /// Dereferences to `&AsciiStr`, enabling method coercion.
    ///
    /// This allows `AsciiString` to be used anywhere `&AsciiStr` is expected,
    /// and provides access to all `AsciiStr` methods.
    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_ascii_str()
    }
}

// Cross-type equality with AsciiStr
impl<const CAP: usize> PartialEq<AsciiStr> for AsciiString<CAP> {
    #[inline]
    fn eq(&self, other: &AsciiStr) -> bool {
        self.as_bytes() == other.as_bytes()
    }
}

impl<const CAP: usize> PartialEq<AsciiString<CAP>> for AsciiStr {
    #[inline]
    fn eq(&self, other: &AsciiString<CAP>) -> bool {
        self.as_bytes() == other.as_bytes()
    }
}

impl<const CAP: usize> PartialEq<&AsciiStr> for AsciiString<CAP> {
    #[inline]
    fn eq(&self, other: &&AsciiStr) -> bool {
        self.as_bytes() == other.as_bytes()
    }
}

impl<const CAP: usize> PartialOrd for AsciiString<CAP> {
    /// Lexicographic ordering based on byte values.
    ///
    /// ASCII ordering is the same as raw byte ordering:
    /// `'0'-'9'` (48-57) < `'A'-'Z'` (65-90) < `'a'-'z'` (97-122)
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<const CAP: usize> Ord for AsciiString<CAP> {
    /// Lexicographic ordering using word-at-a-time comparison.
    ///
    /// Compares all CAP bytes as u64 words using `from_be_bytes` for correct
    /// lexicographic ordering (compiles to `bswap` on little-endian x86).
    /// Zero-padding means shorter content naturally sorts before longer content
    /// (0x00 < any ASCII byte). The loop is fully unrolled by the compiler
    /// since CAP is a const generic.
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        let mut i = 0;
        while i < CAP {
            // SAFETY: CAP.is_multiple_of(8) guarantees i + 8 <= CAP
            let a =
                u64::from_be_bytes(unsafe { self.data.as_ptr().add(i).cast::<[u8; 8]>().read() });
            // SAFETY: CAP.is_multiple_of(8) guarantees i + 8 <= CAP
            let b =
                u64::from_be_bytes(unsafe { other.data.as_ptr().add(i).cast::<[u8; 8]>().read() });
            match a.cmp(&b) {
                core::cmp::Ordering::Equal => {}
                ord => return ord,
            }
            i += 8;
        }
        // Tiebreaker: handles edge case where content contains 0x00
        // and two strings with different lengths have identical data.
        self.len().cmp(&other.len())
    }
}

impl<const CAP: usize> Hash for AsciiString<CAP> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(hash::finalize(self.header));
    }
}

impl<const CAP: usize> core::fmt::Debug for AsciiString<CAP> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("AsciiString")
            .field("value", &self.as_str())
            .field("len", &self.len())
            .field("cap", &CAP)
            .finish()
    }
}

impl<const CAP: usize> core::fmt::Display for AsciiString<CAP> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.as_str())
    }
}

impl<const CAP: usize> core::ops::Index<usize> for AsciiString<CAP> {
    type Output = AsciiChar;

    /// Returns the character at the given index.
    ///
    /// # Panics
    ///
    /// Panics if `index >= self.len()`.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::{AsciiString, AsciiChar};
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("hello")?;
    /// assert_eq!(s[0], AsciiChar::h);
    /// assert_eq!(s[4], AsciiChar::o);
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        assert!(index < self.len(), "index out of bounds");
        // SAFETY: index is within bounds, data contains valid ASCII.
        // We need to return a reference, so we transmute the byte reference.
        // This is safe because AsciiChar is #[repr(transparent)] over u8.
        unsafe { &*(self.data.get_unchecked(index) as *const u8 as *const AsciiChar) }
    }
}

impl<const CAP: usize> core::ops::Index<core::ops::Range<usize>> for AsciiString<CAP> {
    type Output = AsciiStr;

    /// Returns a slice of the string.
    ///
    /// # Panics
    ///
    /// Panics if the range is out of bounds.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiString;
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("BTC-USD")?;
    /// assert_eq!(&s[0..3], "BTC");
    /// assert_eq!(&s[4..7], "USD");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    fn index(&self, range: core::ops::Range<usize>) -> &Self::Output {
        assert!(range.start <= range.end, "range start > end");
        assert!(range.end <= self.len(), "range end out of bounds");
        // SAFETY: range is within bounds, data contains valid ASCII
        unsafe { AsciiStr::from_bytes_unchecked(&self.data[range]) }
    }
}

impl<const CAP: usize> core::ops::Index<core::ops::RangeFrom<usize>> for AsciiString<CAP> {
    type Output = AsciiStr;

    #[inline]
    fn index(&self, range: core::ops::RangeFrom<usize>) -> &Self::Output {
        assert!(range.start <= self.len(), "range start out of bounds");
        // SAFETY: range is within bounds, data contains valid ASCII
        unsafe { AsciiStr::from_bytes_unchecked(&self.data[range.start..self.len()]) }
    }
}

impl<const CAP: usize> core::ops::Index<core::ops::RangeTo<usize>> for AsciiString<CAP> {
    type Output = AsciiStr;

    #[inline]
    fn index(&self, range: core::ops::RangeTo<usize>) -> &Self::Output {
        assert!(range.end <= self.len(), "range end out of bounds");
        // SAFETY: range is within bounds, data contains valid ASCII
        unsafe { AsciiStr::from_bytes_unchecked(&self.data[range]) }
    }
}

impl<const CAP: usize> core::ops::Index<core::ops::RangeFull> for AsciiString<CAP> {
    type Output = AsciiStr;

    #[inline]
    fn index(&self, _range: core::ops::RangeFull) -> &Self::Output {
        self.as_ascii_str()
    }
}

impl<const CAP: usize> core::ops::Index<core::ops::RangeInclusive<usize>> for AsciiString<CAP> {
    type Output = AsciiStr;

    #[inline]
    fn index(&self, range: core::ops::RangeInclusive<usize>) -> &Self::Output {
        let start = *range.start();
        let end = *range.end();
        assert!(start <= end, "range start > end");
        assert!(end < self.len(), "range end out of bounds");
        // SAFETY: range is within bounds, data contains valid ASCII
        unsafe { AsciiStr::from_bytes_unchecked(&self.data[start..=end]) }
    }
}

impl<const CAP: usize> core::ops::Index<core::ops::RangeToInclusive<usize>> for AsciiString<CAP> {
    type Output = AsciiStr;

    #[inline]
    fn index(&self, range: core::ops::RangeToInclusive<usize>) -> &Self::Output {
        assert!(range.end < self.len(), "range end out of bounds");
        // SAFETY: range is within bounds, data contains valid ASCII
        unsafe { AsciiStr::from_bytes_unchecked(&self.data[range]) }
    }
}

// =============================================================================
// TryFrom Implementations
// =============================================================================

impl<const CAP: usize> TryFrom<&str> for AsciiString<CAP> {
    type Error = AsciiError;

    #[inline]
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        Self::try_from_str(s)
    }
}

impl<const CAP: usize> TryFrom<&[u8]> for AsciiString<CAP> {
    type Error = AsciiError;

    #[inline]
    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        Self::try_from_bytes(bytes)
    }
}

#[cfg(feature = "std")]
impl<const CAP: usize> TryFrom<std::string::String> for AsciiString<CAP> {
    type Error = AsciiError;

    #[inline]
    fn try_from(s: std::string::String) -> Result<Self, Self::Error> {
        Self::try_from_str(&s)
    }
}

#[cfg(feature = "std")]
impl<const CAP: usize> TryFrom<&std::string::String> for AsciiString<CAP> {
    type Error = AsciiError;

    #[inline]
    fn try_from(s: &std::string::String) -> Result<Self, Self::Error> {
        Self::try_from_str(s)
    }
}

// =============================================================================
// FromStr
// =============================================================================

impl<const CAP: usize> core::str::FromStr for AsciiString<CAP> {
    type Err = AsciiError;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::try_from(s)
    }
}

// =============================================================================
// AsRef Implementations
// =============================================================================

impl<const CAP: usize> AsRef<str> for AsciiString<CAP> {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl<const CAP: usize> AsRef<[u8]> for AsciiString<CAP> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<const CAP: usize> AsRef<AsciiStr> for AsciiString<CAP> {
    #[inline]
    fn as_ref(&self) -> &AsciiStr {
        self.as_ascii_str()
    }
}

impl<const CAP: usize> AsRef<[u8; CAP]> for AsciiString<CAP> {
    #[inline]
    fn as_ref(&self) -> &[u8; CAP] {
        self.as_raw()
    }
}

// =============================================================================
// Borrow Implementation
// =============================================================================

impl<const CAP: usize> core::borrow::Borrow<AsciiStr> for AsciiString<CAP> {
    /// Borrows the string as an `&AsciiStr`.
    ///
    /// This enables using `AsciiString` as a key in `HashMap`/`HashSet` while
    /// looking up with `&AsciiStr`.
    ///
    /// # Example
    ///
    /// ```
    /// use std::collections::HashMap;
    /// use nexus_ascii::{AsciiString, AsciiStr};
    ///
    /// let mut map: HashMap<AsciiString<32>, i32> = HashMap::new();
    /// let key: AsciiString<32> = AsciiString::try_from("BTC-USD").unwrap();
    /// map.insert(key, 42);
    ///
    /// // Look up with &AsciiStr
    /// let lookup: &AsciiStr = AsciiStr::try_from_str("BTC-USD").unwrap();
    /// assert_eq!(map.get(lookup), Some(&42));
    /// ```
    #[inline]
    fn borrow(&self) -> &AsciiStr {
        self.as_ascii_str()
    }
}

// =============================================================================
// Serde Support (feature-gated)
// =============================================================================

#[cfg(feature = "serde")]
impl<const CAP: usize> serde::Serialize for AsciiString<CAP> {
    /// Serializes the ASCII string as a string.
    ///
    /// This is a zero-cost serialization since ASCII is valid UTF-8.
    #[inline]
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(self.as_str())
    }
}

#[cfg(feature = "serde")]
impl<'de, const CAP: usize> serde::Deserialize<'de> for AsciiString<CAP> {
    /// Deserializes a string into an ASCII string.
    ///
    /// Returns an error if:
    /// - The string is longer than `CAP`
    /// - The string contains non-ASCII bytes
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct AsciiStringVisitor<const CAP: usize>;

        impl<const CAP: usize> serde::de::Visitor<'_> for AsciiStringVisitor<CAP> {
            type Value = AsciiString<CAP>;

            fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                write!(formatter, "an ASCII string with at most {} bytes", CAP)
            }

            #[inline]
            fn visit_str<E: serde::de::Error>(self, v: &str) -> Result<Self::Value, E> {
                AsciiString::try_from_str(v).map_err(|e| match e {
                    AsciiError::TooLong { len, cap } => E::custom(format_args!(
                        "string length {} exceeds capacity {}",
                        len, cap
                    )),
                    AsciiError::InvalidByte { byte, pos } => E::custom(format_args!(
                        "invalid ASCII byte 0x{:02X} at position {}",
                        byte, pos
                    )),
                    AsciiError::NonPrintable { byte, pos } => E::custom(format_args!(
                        "non-printable byte 0x{:02X} at position {}",
                        byte, pos
                    )),
                })
            }

            #[inline]
            fn visit_bytes<E: serde::de::Error>(self, v: &[u8]) -> Result<Self::Value, E> {
                AsciiString::try_from_bytes(v).map_err(|e| match e {
                    AsciiError::TooLong { len, cap } => E::custom(format_args!(
                        "byte slice length {} exceeds capacity {}",
                        len, cap
                    )),
                    AsciiError::InvalidByte { byte, pos } => E::custom(format_args!(
                        "invalid ASCII byte 0x{:02X} at position {}",
                        byte, pos
                    )),
                    AsciiError::NonPrintable { byte, pos } => E::custom(format_args!(
                        "non-printable byte 0x{:02X} at position {}",
                        byte, pos
                    )),
                })
            }
        }

        deserializer.deserialize_str(AsciiStringVisitor)
    }
}

// =============================================================================
// Bytes Crate Support (feature-gated)
// =============================================================================

#[cfg(feature = "bytes")]
impl<const CAP: usize> From<AsciiString<CAP>> for bytes::Bytes {
    /// Converts an ASCII string into `Bytes`.
    ///
    /// This copies the string data into a new `Bytes` buffer.
    #[inline]
    fn from(s: AsciiString<CAP>) -> Self {
        bytes::Bytes::copy_from_slice(s.as_bytes())
    }
}

#[cfg(feature = "bytes")]
impl<const CAP: usize> From<&AsciiString<CAP>> for bytes::Bytes {
    /// Converts a reference to an ASCII string into `Bytes`.
    ///
    /// This copies the string data into a new `Bytes` buffer.
    #[inline]
    fn from(s: &AsciiString<CAP>) -> Self {
        bytes::Bytes::copy_from_slice(s.as_bytes())
    }
}

#[cfg(feature = "bytes")]
impl<const CAP: usize> TryFrom<bytes::Bytes> for AsciiString<CAP> {
    type Error = AsciiError;

    /// Attempts to create an ASCII string from `Bytes`.
    ///
    /// # Errors
    ///
    /// Returns [`AsciiError::TooLong`] if the bytes exceed capacity.
    /// Returns [`AsciiError::InvalidByte`] if any byte is null or > 127.
    #[inline]
    fn try_from(bytes: bytes::Bytes) -> Result<Self, Self::Error> {
        Self::try_from_bytes(&bytes)
    }
}

#[cfg(feature = "bytes")]
impl<const CAP: usize> TryFrom<&bytes::Bytes> for AsciiString<CAP> {
    type Error = AsciiError;

    /// Attempts to create an ASCII string from a `Bytes` reference.
    ///
    /// # Errors
    ///
    /// Returns [`AsciiError::TooLong`] if the bytes exceed capacity.
    /// Returns [`AsciiError::InvalidByte`] if any byte is null or > 127.
    #[inline]
    fn try_from(bytes: &bytes::Bytes) -> Result<Self, Self::Error> {
        Self::try_from_bytes(bytes.as_ref())
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_string() {
        let s: AsciiString<32> = AsciiString::empty();
        assert!(s.is_empty());
        assert_eq!(s.len(), 0);
        assert_eq!(s.as_str(), "");
        assert_eq!(s.as_bytes(), b"");
    }

    #[test]
    fn from_str() {
        let s: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        assert_eq!(s.len(), 5);
        assert_eq!(s.as_str(), "hello");
    }

    #[test]
    fn from_bytes() {
        let s: AsciiString<32> = AsciiString::try_from_bytes(b"world").unwrap();
        assert_eq!(s.len(), 5);
        assert_eq!(s.as_str(), "world");
    }

    #[test]
    fn too_long() {
        let result = AsciiString::<8>::try_from("hello world");
        assert!(matches!(
            result,
            Err(AsciiError::TooLong { len: 11, cap: 8 })
        ));
    }

    #[test]
    fn invalid_ascii() {
        let result = AsciiString::<32>::try_from_bytes(&[0x80]);
        assert!(matches!(
            result,
            Err(AsciiError::InvalidByte { byte: 0x80, pos: 0 })
        ));

        let result = AsciiString::<32>::try_from_bytes(&[b'a', b'b', 0xFF]);
        assert!(matches!(
            result,
            Err(AsciiError::InvalidByte { byte: 0xFF, pos: 2 })
        ));
    }

    #[test]
    fn equality_same() {
        let s1: AsciiString<32> = AsciiString::try_from("test").unwrap();
        let s2: AsciiString<32> = AsciiString::try_from("test").unwrap();
        assert_eq!(s1, s2);
    }

    #[test]
    fn equality_different() {
        let s1: AsciiString<32> = AsciiString::try_from("test").unwrap();
        let s2: AsciiString<32> = AsciiString::try_from("other").unwrap();
        assert_ne!(s1, s2);
    }

    #[test]
    fn equality_different_length() {
        let s1: AsciiString<32> = AsciiString::try_from("test").unwrap();
        let s2: AsciiString<32> = AsciiString::try_from("testing").unwrap();
        assert_ne!(s1, s2);
    }

    #[test]
    fn hash_consistency() {
        use std::collections::hash_map::DefaultHasher;

        let s1: AsciiString<32> = AsciiString::try_from("test").unwrap();
        let s2: AsciiString<32> = AsciiString::try_from("test").unwrap();

        let mut h1 = DefaultHasher::new();
        let mut h2 = DefaultHasher::new();
        s1.hash(&mut h1);
        s2.hash(&mut h2);

        assert_eq!(h1.finish(), h2.finish());
    }

    #[test]
    fn hash_in_hashmap() {
        use std::collections::HashMap;

        let mut map: HashMap<AsciiString<32>, i32> = HashMap::new();

        let key: AsciiString<32> = AsciiString::try_from("BTC-USD").unwrap();
        map.insert(key, 42);

        let lookup: AsciiString<32> = AsciiString::try_from("BTC-USD").unwrap();
        assert_eq!(map.get(&lookup), Some(&42));
    }

    #[test]
    fn default_is_empty() {
        let s: AsciiString<32> = AsciiString::default();
        assert!(s.is_empty());
    }

    #[test]
    fn display() {
        let s: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        assert_eq!(format!("{}", s), "hello");
    }

    #[test]
    fn debug() {
        let s: AsciiString<32> = AsciiString::try_from("hi").unwrap();
        let debug = format!("{:?}", s);
        assert!(debug.contains("AsciiString"));
        assert!(debug.contains("hi"));
    }

    #[test]
    fn copy_semantics() {
        let s1: AsciiString<32> = AsciiString::try_from("copy").unwrap();
        let s2 = s1; // Copy
        assert_eq!(s1, s2); // s1 still valid
    }

    #[test]
    fn capacity() {
        let s: AsciiString<64> = AsciiString::empty();
        assert_eq!(s.capacity(), 64);
    }

    #[test]
    fn as_ref_str() {
        let s: AsciiString<32> = AsciiString::try_from("test").unwrap();
        let r: &str = s.as_ref();
        assert_eq!(r, "test");
    }

    #[test]
    fn as_ref_bytes() {
        let s: AsciiString<32> = AsciiString::try_from("test").unwrap();
        let r: &[u8] = s.as_ref();
        assert_eq!(r, b"test");
    }

    #[test]
    fn full_capacity() {
        let input = "12345678";
        let s: AsciiString<8> = AsciiString::try_from(input).unwrap();
        assert_eq!(s.len(), 8);
        assert_eq!(s.as_str(), input);
    }

    #[test]
    fn control_characters_allowed() {
        // Full ASCII includes control characters
        let s: AsciiString<8> = AsciiString::try_from_bytes(&[0x01, 0x02, 0x03]).unwrap();
        assert_eq!(s.len(), 3);
    }

    // =========================================================================
    // from_static tests
    // =========================================================================

    #[test]
    fn from_static_basic() {
        const S: AsciiString<32> = AsciiString::from_static("hello");
        assert_eq!(S.len(), 5);
        assert_eq!(S.as_str(), "hello");
    }

    #[test]
    fn from_static_empty() {
        const S: AsciiString<32> = AsciiString::from_static("");
        assert!(S.is_empty());
        assert_eq!(S.len(), 0);
    }

    #[test]
    fn from_static_full_capacity() {
        const S: AsciiString<8> = AsciiString::from_static("12345678");
        assert_eq!(S.len(), 8);
        assert_eq!(S.as_str(), "12345678");
    }

    #[test]
    fn from_static_matches_runtime() {
        // Verify const construction produces same result as runtime
        const CONST_S: AsciiString<32> = AsciiString::from_static("BTC-USD");
        let runtime_s: AsciiString<32> = AsciiString::try_from("BTC-USD").unwrap();

        assert_eq!(CONST_S, runtime_s);
        assert_eq!(CONST_S.header(), runtime_s.header());
        assert_eq!(CONST_S.as_str(), runtime_s.as_str());
    }

    #[test]
    fn from_static_hash_matches_runtime() {
        // Critical: const hash must match runtime hash
        const CONST_S: AsciiString<32> = AsciiString::from_static("ETH-USDT");
        let runtime_s: AsciiString<32> = AsciiString::try_from("ETH-USDT").unwrap();

        // Headers must be identical (same length + same hash)
        assert_eq!(CONST_S.header(), runtime_s.header());
    }

    #[test]
    fn from_static_various_lengths() {
        // Test various lengths to cover different hash paths
        const L1: AsciiString<128> = AsciiString::from_static("a");
        const L3: AsciiString<128> = AsciiString::from_static("abc");
        const L4: AsciiString<128> = AsciiString::from_static("abcd");
        const L8: AsciiString<128> = AsciiString::from_static("abcdefgh");
        const L9: AsciiString<128> = AsciiString::from_static("abcdefghi");
        const L16: AsciiString<128> = AsciiString::from_static("abcdefghijklmnop");
        const L17: AsciiString<128> = AsciiString::from_static("abcdefghijklmnopq");
        const L32: AsciiString<128> = AsciiString::from_static("abcdefghijklmnopqrstuvwxyz012345");

        // Verify they match runtime
        assert_eq!(L1, AsciiString::try_from("a").unwrap());
        assert_eq!(L3, AsciiString::try_from("abc").unwrap());
        assert_eq!(L4, AsciiString::try_from("abcd").unwrap());
        assert_eq!(L8, AsciiString::try_from("abcdefgh").unwrap());
        assert_eq!(L9, AsciiString::try_from("abcdefghi").unwrap());
        assert_eq!(L16, AsciiString::try_from("abcdefghijklmnop").unwrap());
        assert_eq!(L17, AsciiString::try_from("abcdefghijklmnopq").unwrap());
        assert_eq!(
            L32,
            AsciiString::try_from("abcdefghijklmnopqrstuvwxyz012345").unwrap()
        );
    }

    #[test]
    fn from_static_in_hashmap() {
        use std::collections::HashMap;

        const KEY: AsciiString<16> = AsciiString::from_static("BTC-USD");

        let mut map: HashMap<AsciiString<16>, i32> = HashMap::new();
        map.insert(KEY, 100);

        // Lookup with runtime-constructed key
        let lookup: AsciiString<16> = AsciiString::try_from("BTC-USD").unwrap();
        assert_eq!(map.get(&lookup), Some(&100));

        // Lookup with the const key itself
        assert_eq!(map.get(&KEY), Some(&100));
    }

    #[test]
    fn from_static_equality_with_runtime() {
        const BTC: AsciiString<16> = AsciiString::from_static("BTC-USD");
        const ETH: AsciiString<16> = AsciiString::from_static("ETH-USD");

        let btc_runtime: AsciiString<16> = AsciiString::try_from("BTC-USD").unwrap();
        let eth_runtime: AsciiString<16> = AsciiString::try_from("ETH-USD").unwrap();

        // Const == Runtime
        assert_eq!(BTC, btc_runtime);
        assert_eq!(ETH, eth_runtime);

        // Const != Different Runtime
        assert_ne!(BTC, eth_runtime);
        assert_ne!(ETH, btc_runtime);

        // Const != Const
        assert_ne!(BTC, ETH);
    }

    #[test]
    fn from_static_with_symbols() {
        const S: AsciiString<64> = AsciiString::from_static("!@#$%^&*()_+-=[]{}|;':\",./<>?");
        assert_eq!(S.as_str(), "!@#$%^&*()_+-=[]{}|;':\",./<>?");
    }

    #[test]
    fn from_static_with_digits() {
        const S: AsciiString<32> = AsciiString::from_static("0123456789");
        assert_eq!(S.as_str(), "0123456789");
    }

    #[test]
    fn from_static_realistic_identifiers() {
        const ORDER_ID: AsciiString<64> = AsciiString::from_static("ORD-2024-01-20-001-ABC123");
        const SYMBOL: AsciiString<16> = AsciiString::from_static("BTCUSDT");
        const EXCHANGE: AsciiString<16> = AsciiString::from_static("BINANCE");

        assert_eq!(ORDER_ID.as_str(), "ORD-2024-01-20-001-ABC123");
        assert_eq!(SYMBOL.as_str(), "BTCUSDT");
        assert_eq!(EXCHANGE.as_str(), "BINANCE");

        // Verify they work in lookups
        let runtime_symbol: AsciiString<16> = AsciiString::try_from("BTCUSDT").unwrap();
        assert_eq!(SYMBOL, runtime_symbol);
    }

    // =========================================================================
    // from_static_bytes tests
    // =========================================================================

    #[test]
    fn from_static_bytes_basic() {
        const S: AsciiString<32> = AsciiString::from_static_bytes(b"hello");
        assert_eq!(S.len(), 5);
        assert_eq!(S.as_str(), "hello");
    }

    #[test]
    fn from_static_bytes_empty() {
        const S: AsciiString<32> = AsciiString::from_static_bytes(b"");
        assert!(S.is_empty());
        assert_eq!(S.len(), 0);
    }

    #[test]
    fn from_static_bytes_with_control_chars() {
        // This is a key use case - control characters that can't be in str literals easily
        const S: AsciiString<16> = AsciiString::from_static_bytes(&[0x01, 0x02, b'A', b'B']);
        assert_eq!(S.len(), 4);
        assert_eq!(S.as_bytes(), &[0x01, 0x02, b'A', b'B']);
    }

    #[test]
    fn from_static_bytes_fix_delimiter() {
        // FIX protocol uses SOH (0x01) as delimiter
        const FIX_FIELD: AsciiString<32> =
            AsciiString::from_static_bytes(b"8=FIX.4.4\x019=123\x01");
        assert_eq!(FIX_FIELD.len(), 16);
        assert_eq!(FIX_FIELD.as_bytes()[9], 0x01); // SOH delimiter
    }

    #[test]
    fn from_static_bytes_matches_from_static_str() {
        // When content is the same, both should produce identical results
        const FROM_STR: AsciiString<32> = AsciiString::from_static("BTC-USD");
        const FROM_BYTES: AsciiString<32> = AsciiString::from_static_bytes(b"BTC-USD");

        assert_eq!(FROM_STR, FROM_BYTES);
        assert_eq!(FROM_STR.header(), FROM_BYTES.header());
    }

    #[test]
    fn from_static_bytes_matches_runtime() {
        const CONST_S: AsciiString<32> = AsciiString::from_static_bytes(b"ETH-USDT");
        let runtime_s: AsciiString<32> = AsciiString::try_from_bytes(b"ETH-USDT").unwrap();

        assert_eq!(CONST_S, runtime_s);
        assert_eq!(CONST_S.header(), runtime_s.header());
    }

    #[test]
    fn from_static_bytes_various_lengths() {
        const L1: AsciiString<128> = AsciiString::from_static_bytes(b"a");
        const L8: AsciiString<128> = AsciiString::from_static_bytes(b"abcdefgh");
        const L16: AsciiString<128> = AsciiString::from_static_bytes(b"abcdefghijklmnop");
        const L32: AsciiString<128> =
            AsciiString::from_static_bytes(b"abcdefghijklmnopqrstuvwxyz012345");

        assert_eq!(L1, AsciiString::try_from_bytes(b"a").unwrap());
        assert_eq!(L8, AsciiString::try_from_bytes(b"abcdefgh").unwrap());
        assert_eq!(
            L16,
            AsciiString::try_from_bytes(b"abcdefghijklmnop").unwrap()
        );
        assert_eq!(
            L32,
            AsciiString::try_from_bytes(b"abcdefghijklmnopqrstuvwxyz012345").unwrap()
        );
    }

    #[test]
    fn from_static_bytes_in_hashmap() {
        use std::collections::HashMap;

        const KEY: AsciiString<16> = AsciiString::from_static_bytes(b"BTC-USD");

        let mut map: HashMap<AsciiString<16>, i32> = HashMap::new();
        map.insert(KEY, 100);

        // Lookup with runtime-constructed key
        let lookup: AsciiString<16> = AsciiString::try_from_bytes(b"BTC-USD").unwrap();
        assert_eq!(map.get(&lookup), Some(&100));

        // Lookup with str-constructed key (should also match)
        let lookup_str: AsciiString<16> = AsciiString::try_from("BTC-USD").unwrap();
        assert_eq!(map.get(&lookup_str), Some(&100));
    }

    #[test]
    fn from_static_bytes_all_ascii_values() {
        // Test with bytes spanning the full non-null ASCII range
        const LOW: AsciiString<32> = AsciiString::from_static_bytes(&[0x01, 0x02, 0x03, 0x04]);
        const HIGH: AsciiString<32> = AsciiString::from_static_bytes(&[0x7C, 0x7D, 0x7E, 0x7F]);

        assert_eq!(LOW.len(), 4);
        assert_eq!(HIGH.len(), 4);
        assert_eq!(HIGH.as_bytes()[3], 0x7F); // DEL character
    }

    // =========================================================================
    // Character access tests
    // =========================================================================

    #[test]
    fn get_valid_index() {
        let s: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        assert_eq!(s.get(0), Some(AsciiChar::h));
        assert_eq!(s.get(1), Some(AsciiChar::e));
        assert_eq!(s.get(2), Some(AsciiChar::l));
        assert_eq!(s.get(3), Some(AsciiChar::l));
        assert_eq!(s.get(4), Some(AsciiChar::o));
    }

    #[test]
    fn get_out_of_bounds() {
        let s: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        assert_eq!(s.get(5), None);
        assert_eq!(s.get(100), None);
    }

    #[test]
    fn get_empty_string() {
        let s: AsciiString<32> = AsciiString::empty();
        assert_eq!(s.get(0), None);
    }

    #[test]
    fn get_unchecked_valid() {
        let s: AsciiString<32> = AsciiString::try_from("ABC").unwrap();
        // SAFETY: indices 0, 1, 2 are within bounds of "ABC" (len = 3).
        unsafe {
            assert_eq!(s.get_unchecked(0), AsciiChar::A);
            assert_eq!(s.get_unchecked(1), AsciiChar::B);
            assert_eq!(s.get_unchecked(2), AsciiChar::C);
        }
    }

    #[test]
    fn chars_iterator() {
        let s: AsciiString<32> = AsciiString::try_from("ABC").unwrap();
        let chars: Vec<_> = s.chars().collect();
        assert_eq!(chars, vec![AsciiChar::A, AsciiChar::B, AsciiChar::C]);
    }

    #[test]
    fn chars_empty() {
        let s: AsciiString<32> = AsciiString::empty();
        assert_eq!(s.chars().count(), 0);
    }

    #[test]
    fn chars_with_digits() {
        let s: AsciiString<32> = AsciiString::try_from("a1b2").unwrap();
        let chars: Vec<_> = s.chars().collect();
        assert_eq!(
            chars,
            vec![
                AsciiChar::a,
                AsciiChar::DIGIT_1,
                AsciiChar::b,
                AsciiChar::DIGIT_2
            ]
        );
    }

    #[test]
    fn chars_iterate_and_transform() {
        let s: AsciiString<32> = AsciiString::try_from("abc").unwrap();
        let upper: Vec<_> = s.chars().map(AsciiChar::to_uppercase).collect();
        assert_eq!(upper, vec![AsciiChar::A, AsciiChar::B, AsciiChar::C]);
    }

    #[test]
    fn chars_count_alphabetic() {
        let s: AsciiString<32> = AsciiString::try_from("ab12cd").unwrap();
        let alpha_count = s.chars().filter(|c| c.is_alphabetic()).count();
        assert_eq!(alpha_count, 4);
    }

    // =========================================================================
    // bytes() iterator tests
    // =========================================================================

    #[test]
    fn bytes_iterator() {
        let s: AsciiString<32> = AsciiString::try_from("ABC").unwrap();
        let bytes: Vec<_> = s.bytes().collect();
        assert_eq!(bytes, vec![b'A', b'B', b'C']);
    }

    #[test]
    fn bytes_empty() {
        let s: AsciiString<32> = AsciiString::empty();
        assert_eq!(s.bytes().count(), 0);
    }

    #[test]
    fn bytes_matches_as_bytes() {
        let s: AsciiString<32> = AsciiString::try_from("hello world").unwrap();
        let from_iter: Vec<_> = s.bytes().collect();
        let from_slice: Vec<_> = s.as_bytes().to_vec();
        assert_eq!(from_iter, from_slice);
    }

    // =========================================================================
    // first() and last() tests
    // =========================================================================

    #[test]
    fn first_non_empty() {
        let s: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        assert_eq!(s.first(), Some(AsciiChar::h));
    }

    #[test]
    fn first_empty() {
        let s: AsciiString<32> = AsciiString::empty();
        assert_eq!(s.first(), None);
    }

    #[test]
    fn first_single_char() {
        let s: AsciiString<32> = AsciiString::try_from("X").unwrap();
        assert_eq!(s.first(), Some(AsciiChar::X));
    }

    #[test]
    fn last_non_empty() {
        let s: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        assert_eq!(s.last(), Some(AsciiChar::o));
    }

    #[test]
    fn last_empty() {
        let s: AsciiString<32> = AsciiString::empty();
        assert_eq!(s.last(), None);
    }

    #[test]
    fn last_single_char() {
        let s: AsciiString<32> = AsciiString::try_from("X").unwrap();
        assert_eq!(s.last(), Some(AsciiChar::X));
    }

    #[test]
    fn first_last_same_for_single() {
        let s: AsciiString<32> = AsciiString::try_from("Z").unwrap();
        assert_eq!(s.first(), s.last());
    }

    // =========================================================================
    // Index<usize> tests
    // =========================================================================

    #[test]
    fn index_valid() {
        let s: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        assert_eq!(s[0], AsciiChar::h);
        assert_eq!(s[1], AsciiChar::e);
        assert_eq!(s[2], AsciiChar::l);
        assert_eq!(s[3], AsciiChar::l);
        assert_eq!(s[4], AsciiChar::o);
    }

    #[test]
    #[should_panic(expected = "index out of bounds")]
    fn index_out_of_bounds() {
        let s: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        let _ = s[5];
    }

    #[test]
    #[should_panic(expected = "index out of bounds")]
    fn index_empty_string() {
        let s: AsciiString<32> = AsciiString::empty();
        let _ = s[0];
    }

    #[test]
    fn index_matches_get() {
        let s: AsciiString<32> = AsciiString::try_from("test").unwrap();
        for i in 0..s.len() {
            assert_eq!(s[i], s.get(i).unwrap());
        }
    }

    // =========================================================================
    // Ordering tests
    // =========================================================================

    #[test]
    fn ord_equal_strings() {
        let s1: AsciiString<32> = AsciiString::try_from("abc").unwrap();
        let s2: AsciiString<32> = AsciiString::try_from("abc").unwrap();
        assert_eq!(s1.cmp(&s2), core::cmp::Ordering::Equal);
    }

    #[test]
    fn ord_less_than() {
        let s1: AsciiString<32> = AsciiString::try_from("abc").unwrap();
        let s2: AsciiString<32> = AsciiString::try_from("abd").unwrap();
        assert_eq!(s1.cmp(&s2), core::cmp::Ordering::Less);
    }

    #[test]
    fn ord_greater_than() {
        let s1: AsciiString<32> = AsciiString::try_from("abd").unwrap();
        let s2: AsciiString<32> = AsciiString::try_from("abc").unwrap();
        assert_eq!(s1.cmp(&s2), core::cmp::Ordering::Greater);
    }

    #[test]
    fn ord_prefix_is_less() {
        // Shorter string that's a prefix is less
        let s1: AsciiString<32> = AsciiString::try_from("abc").unwrap();
        let s2: AsciiString<32> = AsciiString::try_from("abcd").unwrap();
        assert_eq!(s1.cmp(&s2), core::cmp::Ordering::Less);
    }

    #[test]
    fn ord_case_sensitive() {
        // Uppercase comes before lowercase in ASCII
        let upper: AsciiString<32> = AsciiString::try_from("ABC").unwrap();
        let lower: AsciiString<32> = AsciiString::try_from("abc").unwrap();
        assert_eq!(upper.cmp(&lower), core::cmp::Ordering::Less);
    }

    #[test]
    fn ord_digits_before_letters() {
        // Digits come before letters in ASCII
        let digits: AsciiString<32> = AsciiString::try_from("123").unwrap();
        let letters: AsciiString<32> = AsciiString::try_from("ABC").unwrap();
        assert_eq!(digits.cmp(&letters), core::cmp::Ordering::Less);
    }

    #[test]
    fn ord_sortable() {
        let mut strings: Vec<AsciiString<32>> = vec![
            AsciiString::try_from("zebra").unwrap(),
            AsciiString::try_from("apple").unwrap(),
            AsciiString::try_from("banana").unwrap(),
        ];
        strings.sort();
        assert_eq!(strings[0].as_str(), "apple");
        assert_eq!(strings[1].as_str(), "banana");
        assert_eq!(strings[2].as_str(), "zebra");
    }

    #[test]
    fn partial_ord_consistent() {
        let s1: AsciiString<32> = AsciiString::try_from("abc").unwrap();
        let s2: AsciiString<32> = AsciiString::try_from("abd").unwrap();
        assert_eq!(s1.partial_cmp(&s2), Some(core::cmp::Ordering::Less));
    }

    // =========================================================================
    // eq_ignore_ascii_case tests
    // =========================================================================

    #[test]
    fn eq_ignore_case_same_case() {
        let s1: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        let s2: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        assert!(s1.eq_ignore_ascii_case(&s2));
    }

    #[test]
    fn eq_ignore_case_different_case() {
        let s1: AsciiString<32> = AsciiString::try_from("Hello").unwrap();
        let s2: AsciiString<32> = AsciiString::try_from("HELLO").unwrap();
        let s3: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        assert!(s1.eq_ignore_ascii_case(&s2));
        assert!(s1.eq_ignore_ascii_case(&s3));
        assert!(s2.eq_ignore_ascii_case(&s3));
    }

    #[test]
    fn eq_ignore_case_different_strings() {
        let s1: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        let s2: AsciiString<32> = AsciiString::try_from("world").unwrap();
        assert!(!s1.eq_ignore_ascii_case(&s2));
    }

    #[test]
    fn eq_ignore_case_different_lengths() {
        let s1: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        let s2: AsciiString<32> = AsciiString::try_from("hell").unwrap();
        assert!(!s1.eq_ignore_ascii_case(&s2));
    }

    #[test]
    fn eq_ignore_case_empty() {
        let s1: AsciiString<32> = AsciiString::empty();
        let s2: AsciiString<32> = AsciiString::empty();
        assert!(s1.eq_ignore_ascii_case(&s2));
    }

    #[test]
    fn eq_ignore_case_with_digits() {
        // Digits should match exactly (no case)
        let s1: AsciiString<32> = AsciiString::try_from("ABC123").unwrap();
        let s2: AsciiString<32> = AsciiString::try_from("abc123").unwrap();
        assert!(s1.eq_ignore_ascii_case(&s2));
    }

    #[test]
    fn eq_ignore_case_with_symbols() {
        // Symbols should match exactly
        let s1: AsciiString<32> = AsciiString::try_from("BTC-USD").unwrap();
        let s2: AsciiString<32> = AsciiString::try_from("btc-usd").unwrap();
        assert!(s1.eq_ignore_ascii_case(&s2));
    }

    // =========================================================================
    // starts_with tests
    // =========================================================================

    #[test]
    fn starts_with_bytes() {
        let s: AsciiString<32> = AsciiString::try_from("BTC-USD").unwrap();
        assert!(s.starts_with(b"BTC"));
        assert!(s.starts_with(b"BTC-"));
        assert!(s.starts_with(b"BTC-USD"));
        assert!(!s.starts_with(b"ETH"));
    }

    #[test]
    fn starts_with_str() {
        let s: AsciiString<32> = AsciiString::try_from("BTC-USD").unwrap();
        assert!(s.starts_with("BTC"));
        assert!(s.starts_with("BTC-"));
        assert!(!s.starts_with("USD"));
    }

    #[test]
    fn starts_with_empty() {
        let s: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        assert!(s.starts_with("")); // Empty prefix matches everything
        assert!(s.starts_with(b""));
    }

    #[test]
    fn starts_with_full_string() {
        let s: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        assert!(s.starts_with("hello"));
    }

    #[test]
    fn starts_with_longer_prefix() {
        let s: AsciiString<32> = AsciiString::try_from("hi").unwrap();
        assert!(!s.starts_with("hello"));
    }

    #[test]
    fn starts_with_empty_string() {
        let s: AsciiString<32> = AsciiString::empty();
        assert!(s.starts_with("")); // Empty matches empty
        assert!(!s.starts_with("a")); // Non-empty doesn't match
    }

    // =========================================================================
    // ends_with tests
    // =========================================================================

    #[test]
    fn ends_with_bytes() {
        let s: AsciiString<32> = AsciiString::try_from("BTC-USD").unwrap();
        assert!(s.ends_with(b"USD"));
        assert!(s.ends_with(b"-USD"));
        assert!(s.ends_with(b"BTC-USD"));
        assert!(!s.ends_with(b"EUR"));
    }

    #[test]
    fn ends_with_str() {
        let s: AsciiString<32> = AsciiString::try_from("BTC-USD").unwrap();
        assert!(s.ends_with("USD"));
        assert!(s.ends_with("-USD"));
        assert!(!s.ends_with("BTC"));
    }

    #[test]
    fn ends_with_empty() {
        let s: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        assert!(s.ends_with("")); // Empty suffix matches everything
        assert!(s.ends_with(b""));
    }

    #[test]
    fn ends_with_full_string() {
        let s: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        assert!(s.ends_with("hello"));
    }

    #[test]
    fn ends_with_longer_suffix() {
        let s: AsciiString<32> = AsciiString::try_from("lo").unwrap();
        assert!(!s.ends_with("hello"));
    }

    #[test]
    fn ends_with_empty_string() {
        let s: AsciiString<32> = AsciiString::empty();
        assert!(s.ends_with("")); // Empty matches empty
        assert!(!s.ends_with("a")); // Non-empty doesn't match
    }

    // =========================================================================
    // contains tests
    // =========================================================================

    #[test]
    fn contains_bytes() {
        let s: AsciiString<32> = AsciiString::try_from("BTC-USD").unwrap();
        assert!(s.contains(b"-"));
        assert!(s.contains(b"TC-US"));
        assert!(s.contains(b"BTC"));
        assert!(s.contains(b"USD"));
        assert!(!s.contains(b"ETH"));
    }

    #[test]
    fn contains_str() {
        let s: AsciiString<32> = AsciiString::try_from("BTC-USD").unwrap();
        assert!(s.contains("-"));
        assert!(s.contains("TC-US"));
        assert!(!s.contains("ETH"));
    }

    #[test]
    fn contains_empty() {
        let s: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        assert!(s.contains("")); // Empty needle always found
        assert!(s.contains(b""));
    }

    #[test]
    fn contains_full_string() {
        let s: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        assert!(s.contains("hello"));
    }

    #[test]
    fn contains_at_start() {
        let s: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        assert!(s.contains("hel"));
    }

    #[test]
    fn contains_at_end() {
        let s: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        assert!(s.contains("llo"));
    }

    #[test]
    fn contains_in_middle() {
        let s: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        assert!(s.contains("ell"));
    }

    #[test]
    fn contains_longer_needle() {
        let s: AsciiString<32> = AsciiString::try_from("hi").unwrap();
        assert!(!s.contains("hello"));
    }

    #[test]
    fn contains_empty_string() {
        let s: AsciiString<32> = AsciiString::empty();
        assert!(s.contains("")); // Empty contains empty
        assert!(!s.contains("a")); // Empty doesn't contain non-empty
    }

    #[test]
    fn contains_single_char() {
        let s: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        assert!(s.contains("h"));
        assert!(s.contains("e"));
        assert!(s.contains("l"));
        assert!(s.contains("o"));
        assert!(!s.contains("x"));
    }

    // =========================================================================
    // AsciiStr integration tests
    // =========================================================================

    #[test]
    fn as_ascii_str() {
        let s: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        let ascii_str = s.as_ascii_str();
        assert_eq!(ascii_str.len(), 5);
        assert_eq!(ascii_str.as_str(), "hello");
    }

    #[test]
    fn deref_to_ascii_str() {
        let s: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        // Deref coercion should work
        let ascii_str: &AsciiStr = &s;
        assert_eq!(ascii_str.len(), 5);
    }

    #[test]
    fn deref_method_access() {
        let s: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        // Should be able to call AsciiStr methods directly via Deref
        // (these are also on AsciiString, but this tests the coercion)
        let first = s.first();
        assert_eq!(first, Some(AsciiChar::h));
    }

    #[test]
    fn cross_type_equality_ascii_str() {
        let s: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        let ascii_str = AsciiStr::try_from_bytes(b"hello").unwrap();

        assert!(s == *ascii_str);
        assert!(*ascii_str == s);
    }

    #[test]
    fn function_accepting_ascii_str() {
        fn takes_ascii_str(s: &AsciiStr) -> usize {
            s.len()
        }

        let s: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        // Should work via Deref coercion
        assert_eq!(takes_ascii_str(&s), 5);
    }

    // =========================================================================
    // try_from_raw tests
    // =========================================================================

    #[test]
    fn try_from_raw_null_terminated() {
        let buffer: [u8; 16] = *b"BTC-USD\0\0\0\0\0\0\0\0\0";
        let s: AsciiString<16> = AsciiString::try_from_raw(buffer).unwrap();
        assert_eq!(s.as_str(), "BTC-USD");
        assert_eq!(s.len(), 7);
    }

    #[test]
    fn try_from_raw_no_null() {
        // No null terminator - uses full buffer
        let buffer: [u8; 8] = *b"BTCUSDT!";
        let s: AsciiString<8> = AsciiString::try_from_raw(buffer).unwrap();
        assert_eq!(s.as_str(), "BTCUSDT!");
        assert_eq!(s.len(), 8);
    }

    #[test]
    fn try_from_raw_immediate_null() {
        // Null at start - empty string
        let buffer: [u8; 8] = [0u8; 8];
        let s: AsciiString<8> = AsciiString::try_from_raw(buffer).unwrap();
        assert!(s.is_empty());
        assert_eq!(s.len(), 0);
    }

    #[test]
    fn try_from_raw_null_in_middle() {
        let buffer: [u8; 16] = *b"ABC\0DEF\0\0\0\0\0\0\0\0\0";
        let s: AsciiString<16> = AsciiString::try_from_raw(buffer).unwrap();
        assert_eq!(s.as_str(), "ABC");
        assert_eq!(s.len(), 3);
    }

    #[test]
    fn try_from_raw_invalid_ascii_before_null() {
        let mut buffer: [u8; 16] = *b"BTC\0\0\0\0\0\0\0\0\0\0\0\0\0";
        buffer[1] = 0xFF; // Invalid ASCII
        let result = AsciiString::<16>::try_from_raw(buffer);
        assert!(matches!(
            result,
            Err(AsciiError::InvalidByte { byte: 0xFF, pos: 1 })
        ));
    }

    #[test]
    fn try_from_raw_invalid_ascii_after_null_ok() {
        // Invalid byte AFTER null should be fine (not read)
        let mut buffer: [u8; 16] = *b"BTC\0\0\0\0\0\0\0\0\0\0\0\0\0";
        buffer[10] = 0xFF; // After null - should not matter
        let s: AsciiString<16> = AsciiString::try_from_raw(buffer).unwrap();
        assert_eq!(s.as_str(), "BTC");
    }

    #[test]
    fn try_from_raw_matches_try_from_bytes() {
        // Results should be equal
        let buffer: [u8; 16] = *b"BTC-USD\0\0\0\0\0\0\0\0\0";
        let from_raw: AsciiString<16> = AsciiString::try_from_raw(buffer).unwrap();
        let from_bytes: AsciiString<16> = AsciiString::try_from_bytes(b"BTC-USD").unwrap();

        assert_eq!(from_raw, from_bytes);
        assert_eq!(from_raw.header(), from_bytes.header());
    }

    #[test]
    fn try_from_raw_various_positions() {
        // Test null at various positions to exercise the 8-byte chunking
        for len in 0..=16 {
            let mut buffer = [b'A'; 16];
            if len < 16 {
                buffer[len] = 0;
            }
            let s: AsciiString<16> = AsciiString::try_from_raw(buffer).unwrap();
            assert_eq!(s.len(), len);
        }
    }

    #[test]
    fn try_from_raw_32_bytes() {
        // Test with larger buffer
        let mut buffer = [b'X'; 32];
        buffer[20] = 0;
        let s: AsciiString<32> = AsciiString::try_from_raw(buffer).unwrap();
        assert_eq!(s.len(), 20);
        assert_eq!(s.as_bytes(), &[b'X'; 20]);
    }

    #[test]
    fn try_from_raw_hashmap_lookup() {
        use std::collections::HashMap;

        let mut map: HashMap<AsciiString<16>, i32> = HashMap::new();

        // Insert with try_from_bytes
        let key: AsciiString<16> = AsciiString::try_from_bytes(b"BTC-USD").unwrap();
        map.insert(key, 100);

        // Lookup with try_from_raw
        let buffer: [u8; 16] = *b"BTC-USD\0\0\0\0\0\0\0\0\0";
        let lookup: AsciiString<16> = AsciiString::try_from_raw(buffer).unwrap();
        assert_eq!(map.get(&lookup), Some(&100));
    }

    // =========================================================================
    // from_raw_unchecked tests
    // =========================================================================

    #[test]
    fn from_raw_unchecked_basic() {
        let buffer: [u8; 16] = *b"BTC-USD\0\0\0\0\0\0\0\0\0";
        // SAFETY: buffer contains valid ASCII bytes followed by null padding.
        let s: AsciiString<16> = unsafe { AsciiString::from_raw_unchecked(buffer) };
        assert_eq!(s.as_str(), "BTC-USD");
        assert_eq!(s.len(), 7);
    }

    #[test]
    fn from_raw_unchecked_no_null() {
        let buffer: [u8; 8] = *b"BTCUSDT!";
        // SAFETY: buffer is all valid ASCII, fully filled.
        let s: AsciiString<8> = unsafe { AsciiString::from_raw_unchecked(buffer) };
        assert_eq!(s.len(), 8);
    }

    #[test]
    fn from_raw_unchecked_empty() {
        let buffer: [u8; 8] = [0u8; 8];
        // SAFETY: buffer is all null bytes; represents an empty string.
        let s: AsciiString<8> = unsafe { AsciiString::from_raw_unchecked(buffer) };
        assert!(s.is_empty());
    }

    #[test]
    fn from_raw_unchecked_matches_checked() {
        let buffer: [u8; 16] = *b"ETH-USDT\0\0\0\0\0\0\0\0";
        let checked: AsciiString<16> = AsciiString::try_from_raw(buffer).unwrap();
        // SAFETY: buffer contains valid ASCII bytes followed by null padding.
        let unchecked: AsciiString<16> = unsafe { AsciiString::from_raw_unchecked(buffer) };

        assert_eq!(checked, unchecked);
        assert_eq!(checked.header(), unchecked.header());
    }

    // =========================================================================
    // try_from_right_padded tests
    // =========================================================================

    #[test]
    fn try_from_right_padded_space() {
        let buffer: [u8; 16] = *b"BTC-USD         ";
        let s: AsciiString<16> = AsciiString::try_from_right_padded(buffer, b' ').unwrap();
        assert_eq!(s.as_str(), "BTC-USD");
        assert_eq!(s.len(), 7);
    }

    #[test]
    fn try_from_right_padded_null() {
        // Can also strip null padding (but note: stops at first non-null from right)
        let buffer: [u8; 16] = *b"BTC-USD\0\0\0\0\0\0\0\0\0";
        let s: AsciiString<16> = AsciiString::try_from_right_padded(buffer, 0).unwrap();
        assert_eq!(s.as_str(), "BTC-USD");
        assert_eq!(s.len(), 7);
    }

    #[test]
    fn try_from_right_padded_all_padding() {
        let buffer: [u8; 8] = [b' '; 8];
        let s: AsciiString<8> = AsciiString::try_from_right_padded(buffer, b' ').unwrap();
        assert!(s.is_empty());
    }

    #[test]
    fn try_from_right_padded_no_padding() {
        let buffer: [u8; 8] = *b"BTCUSDT!";
        let s: AsciiString<8> = AsciiString::try_from_right_padded(buffer, b' ').unwrap();
        assert_eq!(s.len(), 8);
        assert_eq!(s.as_str(), "BTCUSDT!");
    }

    #[test]
    fn try_from_right_padded_internal_padding_preserved() {
        // Padding characters in the middle should be preserved
        let buffer: [u8; 16] = *b"A B C           ";
        let s: AsciiString<16> = AsciiString::try_from_right_padded(buffer, b' ').unwrap();
        assert_eq!(s.as_str(), "A B C");
        assert_eq!(s.len(), 5);
    }

    #[test]
    fn try_from_right_padded_custom_pad() {
        // Custom padding character
        let buffer: [u8; 8] = *b"ABC#####";
        let s: AsciiString<8> = AsciiString::try_from_right_padded(buffer, b'#').unwrap();
        assert_eq!(s.as_str(), "ABC");
    }

    #[test]
    fn try_from_right_padded_invalid_ascii() {
        let mut buffer: [u8; 16] = *b"BTC-USD         ";
        buffer[2] = 0xFF;
        let result = AsciiString::<16>::try_from_right_padded(buffer, b' ');
        assert!(matches!(
            result,
            Err(AsciiError::InvalidByte { byte: 0xFF, pos: 2 })
        ));
    }

    #[test]
    fn try_from_right_padded_matches_try_from_bytes() {
        let buffer: [u8; 16] = *b"ETH-USD         ";
        let from_padded: AsciiString<16> =
            AsciiString::try_from_right_padded(buffer, b' ').unwrap();
        let from_bytes: AsciiString<16> = AsciiString::try_from_bytes(b"ETH-USD").unwrap();

        assert_eq!(from_padded, from_bytes);
        assert_eq!(from_padded.header(), from_bytes.header());
    }

    // =========================================================================
    // find_null_byte helper tests
    // =========================================================================

    #[test]
    fn find_null_byte_unit_tests() {
        // Test the helper function directly
        assert_eq!(find_null_byte(b""), 0);
        assert_eq!(find_null_byte(b"\0"), 0);
        assert_eq!(find_null_byte(b"A"), 1);
        assert_eq!(find_null_byte(b"A\0"), 1);
        assert_eq!(find_null_byte(b"ABC\0DEF"), 3);
        assert_eq!(find_null_byte(b"ABCDEFGH"), 8); // No null
        assert_eq!(find_null_byte(b"ABCDEFGH\0"), 8);
        assert_eq!(find_null_byte(b"ABCDEFGHI\0"), 9); // Past 8-byte boundary

        // Test at 8-byte boundaries
        assert_eq!(find_null_byte(b"12345678\0"), 8);
        assert_eq!(find_null_byte(b"1234567\0X"), 7);
        assert_eq!(find_null_byte(b"123456\0XX"), 6);

        // Test larger buffers
        let large = b"0123456789ABCDEF\0rest";
        assert_eq!(find_null_byte(large), 16);
    }

    // =========================================================================
    // Transformation tests
    // =========================================================================

    #[test]
    fn to_ascii_uppercase_basic() {
        let s: AsciiString<32> = AsciiString::try_from("Hello, World!").unwrap();
        let upper = s.to_ascii_uppercase();
        assert_eq!(upper.as_str(), "HELLO, WORLD!");
    }

    #[test]
    fn to_ascii_uppercase_already_upper() {
        let s: AsciiString<32> = AsciiString::try_from("HELLO").unwrap();
        let upper = s.to_ascii_uppercase();
        assert_eq!(upper.as_str(), "HELLO");
    }

    #[test]
    fn to_ascii_uppercase_all_lower() {
        let s: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        let upper = s.to_ascii_uppercase();
        assert_eq!(upper.as_str(), "HELLO");
    }

    #[test]
    fn to_ascii_uppercase_mixed() {
        let s: AsciiString<32> = AsciiString::try_from("HeLLo WoRLd").unwrap();
        let upper = s.to_ascii_uppercase();
        assert_eq!(upper.as_str(), "HELLO WORLD");
    }

    #[test]
    fn to_ascii_uppercase_with_numbers() {
        let s: AsciiString<32> = AsciiString::try_from("abc123xyz").unwrap();
        let upper = s.to_ascii_uppercase();
        assert_eq!(upper.as_str(), "ABC123XYZ");
    }

    #[test]
    fn to_ascii_uppercase_empty() {
        let s: AsciiString<32> = AsciiString::empty();
        let upper = s.to_ascii_uppercase();
        assert!(upper.is_empty());
    }

    #[test]
    fn to_ascii_uppercase_hash_changes() {
        let s: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        let upper = s.to_ascii_uppercase();
        // Hash should be different since content changed
        assert_ne!(s.header(), upper.header());
    }

    #[test]
    fn to_ascii_lowercase_basic() {
        let s: AsciiString<32> = AsciiString::try_from("Hello, World!").unwrap();
        let lower = s.to_ascii_lowercase();
        assert_eq!(lower.as_str(), "hello, world!");
    }

    #[test]
    fn to_ascii_lowercase_already_lower() {
        let s: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        let lower = s.to_ascii_lowercase();
        assert_eq!(lower.as_str(), "hello");
    }

    #[test]
    fn to_ascii_lowercase_all_upper() {
        let s: AsciiString<32> = AsciiString::try_from("HELLO").unwrap();
        let lower = s.to_ascii_lowercase();
        assert_eq!(lower.as_str(), "hello");
    }

    #[test]
    fn to_ascii_lowercase_with_symbols() {
        let s: AsciiString<32> = AsciiString::try_from("BTC-USD").unwrap();
        let lower = s.to_ascii_lowercase();
        assert_eq!(lower.as_str(), "btc-usd");
    }

    #[test]
    fn to_ascii_lowercase_empty() {
        let s: AsciiString<32> = AsciiString::empty();
        let lower = s.to_ascii_lowercase();
        assert!(lower.is_empty());
    }

    #[test]
    fn to_ascii_lowercase_hash_changes() {
        let s: AsciiString<32> = AsciiString::try_from("HELLO").unwrap();
        let lower = s.to_ascii_lowercase();
        assert_ne!(s.header(), lower.header());
    }

    #[test]
    fn case_roundtrip() {
        // upper(lower(s)) should equal upper(s) for any ASCII string
        let s: AsciiString<32> = AsciiString::try_from("HeLLo WoRLd 123!").unwrap();
        let upper1 = s.to_ascii_uppercase();
        let lower = s.to_ascii_lowercase();
        let upper2 = lower.to_ascii_uppercase();
        assert_eq!(upper1, upper2);
    }

    #[test]
    fn truncated_basic() {
        let s: AsciiString<32> = AsciiString::try_from("Hello, World!").unwrap();
        let t = s.truncated(5);
        assert_eq!(t.as_str(), "Hello");
        assert_eq!(t.len(), 5);
    }

    #[test]
    fn truncated_to_zero() {
        let s: AsciiString<32> = AsciiString::try_from("Hello").unwrap();
        let t = s.truncated(0);
        assert!(t.is_empty());
    }

    #[test]
    fn truncated_to_same_length() {
        let s: AsciiString<32> = AsciiString::try_from("Hello").unwrap();
        let t = s.truncated(5);
        assert_eq!(t.as_str(), "Hello");
    }

    #[test]
    fn truncated_hash_changes() {
        let s: AsciiString<32> = AsciiString::try_from("Hello").unwrap();
        let t = s.truncated(3);
        // Hash should be different since content changed
        assert_ne!(s.header(), t.header());
    }

    #[test]
    fn truncated_hash_matches_direct() {
        // truncated result should have same hash as directly constructed
        let s: AsciiString<32> = AsciiString::try_from("Hello, World!").unwrap();
        let truncated = s.truncated(5);
        let direct: AsciiString<32> = AsciiString::try_from("Hello").unwrap();
        assert_eq!(truncated, direct);
        assert_eq!(truncated.header(), direct.header());
    }

    #[test]
    #[should_panic(expected = "exceeds current length")]
    fn truncated_panics_on_longer() {
        let s: AsciiString<32> = AsciiString::try_from("Hello").unwrap();
        let _ = s.truncated(10);
    }

    #[test]
    fn try_truncated_basic() {
        let s: AsciiString<32> = AsciiString::try_from("Hello").unwrap();
        let t = s.try_truncated(3);
        assert!(t.is_some());
        assert_eq!(t.unwrap().as_str(), "Hel");
    }

    #[test]
    fn try_truncated_exact_length() {
        let s: AsciiString<32> = AsciiString::try_from("Hello").unwrap();
        let t = s.try_truncated(5);
        assert!(t.is_some());
        assert_eq!(t.unwrap().as_str(), "Hello");
    }

    #[test]
    fn try_truncated_too_long() {
        let s: AsciiString<32> = AsciiString::try_from("Hello").unwrap();
        let t = s.try_truncated(10);
        assert!(t.is_none());
    }

    #[test]
    fn try_truncated_to_zero() {
        let s: AsciiString<32> = AsciiString::try_from("Hello").unwrap();
        let t = s.try_truncated(0);
        assert!(t.is_some());
        assert!(t.unwrap().is_empty());
    }

    #[test]
    fn transformations_preserve_capacity() {
        let s: AsciiString<64> = AsciiString::try_from("Hello").unwrap();
        let upper = s.to_ascii_uppercase();
        let lower = s.to_ascii_lowercase();
        let truncated = s.truncated(3);

        assert_eq!(upper.capacity(), 64);
        assert_eq!(lower.capacity(), 64);
        assert_eq!(truncated.capacity(), 64);
    }

    #[test]
    #[cfg(feature = "nohash")]
    fn nohash_hashmap_behavior() {
        use nohash_hasher::BuildNoHashHasher;
        use std::collections::HashMap;

        // Verify that nohash HashMap works correctly with AsciiString
        let mut map: HashMap<AsciiString<32>, i32, BuildNoHashHasher<u64>> = HashMap::default();

        let btc = AsciiString::try_from("BTC-USD").unwrap();
        let eth = AsciiString::try_from("ETH-USD").unwrap();
        let btc_copy = AsciiString::try_from("BTC-USD").unwrap();

        // Insert different keys
        map.insert(btc, 100);
        map.insert(eth, 200);

        // Verify both are stored separately
        assert_eq!(map.len(), 2);
        assert_eq!(map.get(&btc), Some(&100));
        assert_eq!(map.get(&eth), Some(&200));

        // Verify same content key retrieves correct value
        assert_eq!(map.get(&btc_copy), Some(&100));

        // Verify update works correctly (same key overwrites)
        map.insert(btc_copy, 300);
        assert_eq!(map.len(), 2); // Still 2, not 3
        assert_eq!(map.get(&btc), Some(&300)); // Updated value

        // Verify different strings never overwrite each other
        let sol = AsciiString::try_from("SOL-USD").unwrap();
        map.insert(sol, 400);
        assert_eq!(map.len(), 3);
        assert_eq!(map.get(&btc), Some(&300));
        assert_eq!(map.get(&eth), Some(&200));
        assert_eq!(map.get(&sol), Some(&400));
    }

    #[test]
    #[cfg(feature = "nohash")]
    fn nohash_bucket_distribution_good() {
        // Verify that strings of same length get different buckets (hash in lower bits)
        let a = AsciiString::<32>::try_from("AAAA").unwrap();
        let b = AsciiString::<32>::try_from("BBBB").unwrap();
        let c = AsciiString::<32>::try_from("AAAAA").unwrap(); // different length

        // New layout: lower 48 bits = hash, upper 16 bits = length
        let hash_a = a.header & 0x0000_FFFF_FFFF_FFFF;
        let hash_b = b.header & 0x0000_FFFF_FFFF_FFFF;
        let len_a = a.header >> 48;
        let len_b = b.header >> 48;

        println!("Header A (AAAA):  0x{:016X}", a.header);
        println!("Header B (BBBB):  0x{:016X}", b.header);
        println!("Header C (AAAAA): 0x{:016X}", c.header);
        println!();
        println!("Upper 16 bits (length): A={}, B={}", len_a, len_b);
        println!(
            "Lower 48 bits (hash):   A=0x{:012X}, B=0x{:012X}",
            hash_a, hash_b
        );
        println!();
        println!(
            "Bucket (& 1023): A={}, B={}, C={}",
            a.header & 1023,
            b.header & 1023,
            c.header & 1023
        );
        println!();

        // Now A and B should have different buckets despite same length
        assert_ne!(
            a.header & 1023,
            b.header & 1023,
            "Same-length strings should have different bucket assignments"
        );
    }

    #[test]
    #[cfg(feature = "nohash")]
    fn nohash_same_header_different_content() {
        use nohash_hasher::BuildNoHashHasher;
        use std::collections::HashMap;

        // Create two AsciiStrings with IDENTICAL headers but DIFFERENT content.
        // This proves HashMap uses eq() for correctness, not just the hash.

        let real = AsciiString::<8>::try_from("AAAA").unwrap();

        // Construct a fake string with same header but different bytes
        let fake: AsciiString<8> = {
            let mut data = [0u8; 8];
            data[0] = b'B';
            data[1] = b'B';
            data[2] = b'B';
            data[3] = b'B';

            // Use same header as `real` - same length, same hash bits
            let header = real.header;

            AsciiString { header, data }
        };

        // Sanity checks: same header, different content
        assert_eq!(real.len(), fake.len());
        assert_eq!(real.header, fake.header); // Headers are identical!
        assert_ne!(real.as_bytes(), fake.as_bytes()); // Content differs
        assert_ne!(real, fake); // eq() sees them as different

        // Now use in HashMap - if it only checked headers, this would fail
        let mut map: HashMap<AsciiString<8>, i32, BuildNoHashHasher<u64>> = HashMap::default();

        map.insert(real, 1);
        map.insert(fake, 2);

        // Both must be present as separate entries
        assert_eq!(map.len(), 2, "HashMap should have 2 entries, not 1");
        assert_eq!(map.get(&real), Some(&1));
        assert_eq!(map.get(&fake), Some(&2));
    }

    // =========================================================================
    // Serde tests
    // =========================================================================

    #[cfg(feature = "serde")]
    mod serde_tests {
        use super::*;

        #[test]
        fn serialize_json() {
            let s: AsciiString<32> = AsciiString::try_from("BTC-USD").unwrap();
            let json = serde_json::to_string(&s).unwrap();
            assert_eq!(json, "\"BTC-USD\"");
        }

        #[test]
        fn deserialize_json() {
            let s: AsciiString<32> = serde_json::from_str("\"BTC-USD\"").unwrap();
            assert_eq!(s.as_str(), "BTC-USD");
        }

        #[test]
        fn deserialize_json_empty() {
            let s: AsciiString<32> = serde_json::from_str("\"\"").unwrap();
            assert!(s.is_empty());
        }

        #[test]
        fn deserialize_json_too_long() {
            let result: Result<AsciiString<8>, _> = serde_json::from_str("\"hello world\"");
            assert!(result.is_err());
            let err = result.unwrap_err().to_string();
            assert!(err.contains("exceeds capacity"));
        }

        #[test]
        fn deserialize_json_non_ascii() {
            let result: Result<AsciiString<32>, _> = serde_json::from_str("\"héllo\"");
            assert!(result.is_err());
            let err = result.unwrap_err().to_string();
            assert!(err.contains("invalid ASCII"));
        }

        #[test]
        fn roundtrip_json() {
            let original: AsciiString<32> = AsciiString::try_from("test-123").unwrap();
            let json = serde_json::to_string(&original).unwrap();
            let restored: AsciiString<32> = serde_json::from_str(&json).unwrap();
            assert_eq!(original, restored);
        }
    }

    // =========================================================================
    // Capacity conversion tests
    // =========================================================================

    #[test]
    fn widen_basic() {
        let small: AsciiString<16> = AsciiString::try_from("hello").unwrap();
        let large: AsciiString<32> = small.widen();
        assert_eq!(small.as_str(), large.as_str());
        assert_eq!(small.len(), large.len());
    }

    #[test]
    fn widen_preserves_hash() {
        let small: AsciiString<16> = AsciiString::try_from("BTC-USD").unwrap();
        let large: AsciiString<64> = small.widen();
        // Header contains hash + len, both should be identical
        assert_eq!(small.header(), large.header());
    }

    #[test]
    fn widen_empty() {
        let small: AsciiString<8> = AsciiString::empty();
        let large: AsciiString<32> = small.widen();
        assert!(large.is_empty());
        assert_eq!(small.header(), large.header());
    }

    #[test]
    fn widen_same_size() {
        let s: AsciiString<16> = AsciiString::try_from("test").unwrap();
        let same: AsciiString<16> = s.widen();
        assert_eq!(s, same);
    }

    #[test]
    fn tighten_basic() {
        let large: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        let small: AsciiString<16> = large.tighten().unwrap();
        assert_eq!(large.as_str(), small.as_str());
        assert_eq!(large.len(), small.len());
    }

    #[test]
    fn tighten_preserves_hash() {
        let large: AsciiString<64> = AsciiString::try_from("BTC-USD").unwrap();
        let small: AsciiString<16> = large.tighten().unwrap();
        // Header contains hash + len, both should be identical
        assert_eq!(large.header(), small.header());
    }

    #[test]
    fn tighten_empty() {
        let large: AsciiString<32> = AsciiString::empty();
        let small: AsciiString<8> = large.tighten().unwrap();
        assert!(small.is_empty());
        assert_eq!(large.header(), small.header());
    }

    #[test]
    fn tighten_same_size() {
        let s: AsciiString<16> = AsciiString::try_from("test").unwrap();
        let same: AsciiString<16> = s.tighten().unwrap();
        assert_eq!(s, same);
    }

    #[test]
    fn tighten_too_long() {
        let large: AsciiString<32> = AsciiString::try_from("this is too long").unwrap();
        let result = large.tighten::<8>();
        assert!(matches!(
            result,
            Err(AsciiError::TooLong { len: 16, cap: 8 })
        ));
    }

    #[test]
    fn tighten_exact_fit() {
        // Content is exactly 8 bytes, should fit in AsciiString<8>
        let large: AsciiString<32> = AsciiString::try_from("12345678").unwrap();
        let small: AsciiString<8> = large.tighten().unwrap();
        assert_eq!(small.as_str(), "12345678");
    }

    #[test]
    fn widen_tighten_roundtrip() {
        let original: AsciiString<16> = AsciiString::try_from("roundtrip").unwrap();
        let widened: AsciiString<64> = original.widen();
        let tightened: AsciiString<16> = widened.tighten().unwrap();
        assert_eq!(original, tightened);
        assert_eq!(original.header(), tightened.header());
    }

    // =========================================================================
    // into_raw tests
    // =========================================================================

    #[test]
    fn into_raw_basic() {
        let s: AsciiString<16> = AsciiString::try_from("hello").unwrap();
        let raw: [u8; 16] = s.into_raw();
        assert_eq!(&raw[..5], b"hello");
        assert_eq!(&raw[5..], &[0u8; 11]);
    }

    #[test]
    fn into_raw_empty() {
        let s: AsciiString<16> = AsciiString::empty();
        let raw: [u8; 16] = s.into_raw();
        assert_eq!(raw, [0u8; 16]);
    }

    #[test]
    fn into_raw_full_capacity() {
        let s: AsciiString<8> = AsciiString::try_from("12345678").unwrap();
        let raw: [u8; 8] = s.into_raw();
        assert_eq!(&raw, b"12345678");
    }

    #[test]
    fn into_raw_roundtrip() {
        let original: AsciiString<16> = AsciiString::try_from("test").unwrap();
        let raw: [u8; 16] = original.into_raw();
        let recovered: AsciiString<16> = AsciiString::try_from_raw(raw).unwrap();
        assert_eq!(original, recovered);
    }

    // =========================================================================
    // from_str_unchecked tests
    // =========================================================================

    #[test]
    fn from_str_unchecked_basic() {
        // SAFETY: "hello" is valid ASCII.
        let s: AsciiString<16> = unsafe { AsciiString::from_str_unchecked("hello") };
        assert_eq!(s.as_str(), "hello");
        assert_eq!(s.len(), 5);
    }

    #[test]
    fn from_str_unchecked_empty() {
        // SAFETY: "" is valid ASCII.
        let s: AsciiString<16> = unsafe { AsciiString::from_str_unchecked("") };
        assert!(s.is_empty());
    }

    #[test]
    fn from_str_unchecked_matches_checked() {
        // SAFETY: "test123" is valid ASCII.
        let unchecked: AsciiString<16> = unsafe { AsciiString::from_str_unchecked("test123") };
        let checked: AsciiString<16> = AsciiString::try_from_str("test123").unwrap();
        assert_eq!(unchecked, checked);
        assert_eq!(unchecked.header(), checked.header());
    }

    // =========================================================================
    // try_from_null_terminated tests
    // =========================================================================

    #[test]
    fn try_from_null_terminated_basic() {
        let buffer: &[u8; 16] = b"BTC-USD\0\0\0\0\0\0\0\0\0";
        let s: AsciiString<16> = AsciiString::try_from_null_terminated(buffer).unwrap();
        assert_eq!(s.as_str(), "BTC-USD");
        assert_eq!(s.len(), 7);
    }

    #[test]
    fn try_from_null_terminated_slice() {
        let slice: &[u8] = b"ETH-USD\0garbage";
        let s: AsciiString<16> = AsciiString::try_from_null_terminated(slice).unwrap();
        assert_eq!(s.as_str(), "ETH-USD");
    }

    #[test]
    fn try_from_null_terminated_no_null() {
        let buffer: &[u8] = b"BTCUSDT";
        let s: AsciiString<16> = AsciiString::try_from_null_terminated(buffer).unwrap();
        assert_eq!(s.as_str(), "BTCUSDT");
        assert_eq!(s.len(), 7);
    }

    #[test]
    fn try_from_null_terminated_empty() {
        let buffer: &[u8] = b"\0garbage";
        let s: AsciiString<16> = AsciiString::try_from_null_terminated(buffer).unwrap();
        assert!(s.is_empty());
    }

    #[test]
    fn try_from_null_terminated_too_long() {
        let buffer: &[u8] = b"this is way too long for the capacity";
        let result = AsciiString::<8>::try_from_null_terminated(buffer);
        assert!(matches!(result, Err(AsciiError::TooLong { .. })));
    }

    #[test]
    fn try_from_null_terminated_invalid_ascii() {
        let buffer: &[u8] = b"hello\xFF\0";
        let result = AsciiString::<16>::try_from_null_terminated(buffer);
        assert!(matches!(
            result,
            Err(AsciiError::InvalidByte { byte: 0xFF, .. })
        ));
    }

    #[test]
    fn try_from_null_terminated_roundtrip() {
        let original: AsciiString<16> = AsciiString::try_from("test").unwrap();
        let raw = original.into_raw();
        let recovered: AsciiString<16> = AsciiString::try_from_null_terminated(&raw).unwrap();
        assert_eq!(original, recovered);
    }

    // =========================================================================
    // try_from_raw_ref tests
    // =========================================================================

    #[test]
    fn try_from_raw_ref_basic() {
        let buffer: &[u8; 16] = b"BTC-USD\0\0\0\0\0\0\0\0\0";
        let s: AsciiString<16> = AsciiString::try_from_raw_ref(buffer).unwrap();
        assert_eq!(s.as_str(), "BTC-USD");
        assert_eq!(s.len(), 7);
    }

    #[test]
    fn try_from_raw_ref_no_null() {
        let buffer: &[u8; 8] = b"BTCUSDT!";
        let s: AsciiString<8> = AsciiString::try_from_raw_ref(buffer).unwrap();
        assert_eq!(s.as_str(), "BTCUSDT!");
        assert_eq!(s.len(), 8);
    }

    #[test]
    fn try_from_raw_ref_empty() {
        let buffer: &[u8; 16] = b"\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0";
        let s: AsciiString<16> = AsciiString::try_from_raw_ref(buffer).unwrap();
        assert!(s.is_empty());
    }

    #[test]
    fn try_from_raw_ref_invalid_ascii() {
        let buffer: &[u8; 16] = b"hello\xFF\0\0\0\0\0\0\0\0\0\0";
        let result = AsciiString::<16>::try_from_raw_ref(buffer);
        assert!(matches!(
            result,
            Err(AsciiError::InvalidByte { byte: 0xFF, .. })
        ));
    }

    #[test]
    fn try_from_raw_ref_matches_try_from_null_terminated() {
        let buffer: &[u8; 16] = b"test123\0\0\0\0\0\0\0\0\0";
        let from_ref: AsciiString<16> = AsciiString::try_from_raw_ref(buffer).unwrap();
        let from_slice: AsciiString<16> = AsciiString::try_from_null_terminated(buffer).unwrap();
        assert_eq!(from_ref, from_slice);
        assert_eq!(from_ref.header(), from_slice.header());
    }

    #[test]
    fn try_from_raw_ref_roundtrip() {
        let original: AsciiString<16> = AsciiString::try_from("test").unwrap();
        let raw = original.into_raw();
        let recovered: AsciiString<16> = AsciiString::try_from_raw_ref(&raw).unwrap();
        assert_eq!(original, recovered);
    }

    // =========================================================================
    // Bytes crate tests
    // =========================================================================

    #[cfg(feature = "bytes")]
    mod bytes_tests {
        use super::*;
        use bytes::Bytes;

        #[test]
        fn into_bytes() {
            let s: AsciiString<32> = AsciiString::try_from("hello").unwrap();
            let b: Bytes = s.into();
            assert_eq!(&b[..], b"hello");
        }

        #[test]
        fn ref_into_bytes() {
            let s: AsciiString<32> = AsciiString::try_from("hello").unwrap();
            let b: Bytes = (&s).into();
            assert_eq!(&b[..], b"hello");
        }

        #[test]
        fn try_from_bytes() {
            let b = Bytes::from_static(b"hello");
            let s: AsciiString<32> = AsciiString::try_from(b).unwrap();
            assert_eq!(s.as_str(), "hello");
        }

        #[test]
        fn try_from_bytes_ref() {
            let b = Bytes::from_static(b"hello");
            let s: AsciiString<32> = AsciiString::try_from(&b).unwrap();
            assert_eq!(s.as_str(), "hello");
        }

        #[test]
        fn try_from_bytes_too_long() {
            let b = Bytes::from_static(b"hello world");
            let result: Result<AsciiString<8>, _> = AsciiString::try_from(b);
            assert!(matches!(result, Err(AsciiError::TooLong { .. })));
        }

        #[test]
        fn try_from_bytes_non_ascii() {
            let b = Bytes::from_static(&[0xFF, 0x80]);
            let result: Result<AsciiString<32>, _> = AsciiString::try_from(b);
            assert!(matches!(result, Err(AsciiError::InvalidByte { .. })));
        }
    }

    // =========================================================================
    // as_raw tests
    // =========================================================================

    #[test]
    fn as_raw_returns_full_buffer() {
        let s: AsciiString<8> = AsciiString::try_from("hello").unwrap();
        let raw: &[u8; 8] = s.as_raw();
        // First 5 bytes are "hello", rest are zero-padded
        assert_eq!(&raw[..5], b"hello");
        assert_eq!(&raw[5..], &[0, 0, 0]);
    }

    #[test]
    fn as_raw_empty() {
        let s: AsciiString<8> = AsciiString::empty();
        let raw: &[u8; 8] = s.as_raw();
        assert_eq!(raw, &[0; 8]);
    }

    #[test]
    fn as_raw_full_capacity() {
        let s: AsciiString<8> = AsciiString::try_from("12345678").unwrap();
        let raw: &[u8; 8] = s.as_raw();
        assert_eq!(raw, b"12345678");
    }

    #[test]
    fn as_ref_array() {
        let s: AsciiString<8> = AsciiString::try_from("test").unwrap();
        let arr: &[u8; 8] = s.as_ref();
        assert_eq!(&arr[..4], b"test");
    }

    // =========================================================================
    // split_once tests
    // =========================================================================

    #[test]
    fn split_once_found() {
        let s: AsciiString<32> = AsciiString::try_from("BTC-USD").unwrap();
        let (before, after) = s.split_once(AsciiChar::MINUS).unwrap();
        assert_eq!(before.as_str(), "BTC");
        assert_eq!(after.as_str(), "USD");
    }

    #[test]
    fn split_once_not_found() {
        let s: AsciiString<32> = AsciiString::try_from("BTCUSD").unwrap();
        assert!(s.split_once(AsciiChar::MINUS).is_none());
    }

    #[test]
    fn split_once_at_start() {
        let s: AsciiString<32> = AsciiString::try_from("-USD").unwrap();
        let (before, after) = s.split_once(AsciiChar::MINUS).unwrap();
        assert_eq!(before.as_str(), "");
        assert_eq!(after.as_str(), "USD");
    }

    #[test]
    fn split_once_at_end() {
        let s: AsciiString<32> = AsciiString::try_from("BTC-").unwrap();
        let (before, after) = s.split_once(AsciiChar::MINUS).unwrap();
        assert_eq!(before.as_str(), "BTC");
        assert_eq!(after.as_str(), "");
    }

    #[test]
    fn split_once_multiple_delimiters() {
        let s: AsciiString<32> = AsciiString::try_from("A-B-C").unwrap();
        let (before, after) = s.split_once(AsciiChar::MINUS).unwrap();
        assert_eq!(before.as_str(), "A");
        assert_eq!(after.as_str(), "B-C"); // Only splits on first
    }

    // =========================================================================
    // strip_prefix and strip_suffix tests
    // =========================================================================

    #[test]
    fn strip_prefix_found() {
        let s: AsciiString<32> = AsciiString::try_from("hello world").unwrap();
        let stripped = s.strip_prefix("hello ").unwrap();
        assert_eq!(stripped.as_str(), "world");
    }

    #[test]
    fn strip_prefix_not_found() {
        let s: AsciiString<32> = AsciiString::try_from("hello world").unwrap();
        assert!(s.strip_prefix("goodbye").is_none());
    }

    #[test]
    fn strip_prefix_entire_string() {
        let s: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        let stripped = s.strip_prefix("hello").unwrap();
        assert_eq!(stripped.as_str(), "");
    }

    #[test]
    fn strip_suffix_found() {
        let s: AsciiString<32> = AsciiString::try_from("hello world").unwrap();
        let stripped = s.strip_suffix(" world").unwrap();
        assert_eq!(stripped.as_str(), "hello");
    }

    #[test]
    fn strip_suffix_not_found() {
        let s: AsciiString<32> = AsciiString::try_from("hello world").unwrap();
        assert!(s.strip_suffix("universe").is_none());
    }

    #[test]
    fn strip_suffix_entire_string() {
        let s: AsciiString<32> = AsciiString::try_from("hello").unwrap();
        let stripped = s.strip_suffix("hello").unwrap();
        assert_eq!(stripped.as_str(), "");
    }

    // =========================================================================
    // is_numeric and is_alphanumeric tests
    // =========================================================================

    #[test]
    fn is_numeric_true() {
        let s: AsciiString<32> = AsciiString::try_from("12345").unwrap();
        assert!(s.is_numeric());
    }

    #[test]
    fn is_numeric_false() {
        let s: AsciiString<32> = AsciiString::try_from("123a5").unwrap();
        assert!(!s.is_numeric());
    }

    #[test]
    fn is_numeric_empty() {
        let s: AsciiString<32> = AsciiString::empty();
        assert!(s.is_numeric()); // Empty string has no non-numeric chars
    }

    #[test]
    fn is_alphanumeric_true() {
        let s: AsciiString<32> = AsciiString::try_from("Hello123").unwrap();
        assert!(s.is_alphanumeric());
    }

    #[test]
    fn is_alphanumeric_false() {
        let s: AsciiString<32> = AsciiString::try_from("Hello-123").unwrap();
        assert!(!s.is_alphanumeric());
    }

    #[test]
    fn is_alphanumeric_empty() {
        let s: AsciiString<32> = AsciiString::empty();
        assert!(s.is_alphanumeric());
    }

    // =========================================================================
    // Integer parsing tests
    // =========================================================================

    #[test]
    fn parse_u8_valid() {
        let s: AsciiString<8> = AsciiString::try_from("255").unwrap();
        assert_eq!(s.parse_u8().unwrap(), 255);
    }

    #[test]
    fn parse_u8_overflow() {
        let s: AsciiString<8> = AsciiString::try_from("256").unwrap();
        assert!(s.parse_u8().is_err());
    }

    #[test]
    fn parse_u64_valid() {
        let s: AsciiString<32> = AsciiString::try_from("18446744073709551615").unwrap();
        assert_eq!(s.parse_u64().unwrap(), u64::MAX);
    }

    #[test]
    fn parse_i8_negative() {
        let s: AsciiString<8> = AsciiString::try_from("-128").unwrap();
        assert_eq!(s.parse_i8().unwrap(), -128);
    }

    #[test]
    fn parse_i64_negative() {
        let s: AsciiString<32> = AsciiString::try_from("-9223372036854775808").unwrap();
        assert_eq!(s.parse_i64().unwrap(), i64::MIN);
    }

    #[test]
    fn parse_invalid_format() {
        let s: AsciiString<8> = AsciiString::try_from("abc").unwrap();
        assert!(s.parse_u64().is_err());
    }

    // =========================================================================
    // Integer formatting tests
    // =========================================================================

    #[test]
    fn from_u8_basic() {
        let s: AsciiString<8> = AsciiString::from_u8(255).unwrap();
        assert_eq!(s.as_str(), "255");
    }

    #[test]
    fn from_u8_zero() {
        let s: AsciiString<8> = AsciiString::from_u8(0).unwrap();
        assert_eq!(s.as_str(), "0");
    }

    #[test]
    fn from_u64_large() {
        let s: AsciiString<32> = AsciiString::from_u64(u64::MAX).unwrap();
        assert_eq!(s.as_str(), "18446744073709551615");
    }

    #[test]
    fn from_i8_negative() {
        let s: AsciiString<8> = AsciiString::from_i8(-128).unwrap();
        assert_eq!(s.as_str(), "-128");
    }

    #[test]
    fn from_i64_min() {
        let s: AsciiString<32> = AsciiString::from_i64(i64::MIN).unwrap();
        assert_eq!(s.as_str(), "-9223372036854775808");
    }

    #[test]
    fn from_int_too_small_capacity() {
        // u64::MAX needs 20 characters, won't fit in 8
        let result: Result<AsciiString<8>, _> = AsciiString::from_u64(u64::MAX);
        assert!(result.is_err());
    }

    #[test]
    fn format_then_parse_roundtrip() {
        let original: u64 = 12_345_678_901_234;
        let s: AsciiString<32> = AsciiString::from_u64(original).unwrap();
        let parsed = s.parse_u64().unwrap();
        assert_eq!(original, parsed);
    }

    #[test]
    fn format_then_parse_roundtrip_negative() {
        let original: i64 = -98_765_432_109_876;
        let s: AsciiString<32> = AsciiString::from_i64(original).unwrap();
        let parsed = s.parse_i64().unwrap();
        assert_eq!(original, parsed);
    }

    #[test]
    fn from_str_parse() {
        let s: AsciiString<32> = "BTC-USD".parse().unwrap();
        assert_eq!(s.as_str(), "BTC-USD");
    }

    #[test]
    fn from_str_invalid() {
        let result = "héllo".parse::<AsciiString<32>>();
        assert!(result.is_err());
    }

    #[test]
    fn from_str_too_long() {
        let result = "ABCDEFGHI".parse::<AsciiString<8>>();
        assert!(result.is_err());
    }
}
