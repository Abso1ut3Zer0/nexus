//! Newtype wrappers for ID values.
//!
//! These types provide type safety and encapsulation for generated IDs.
//! Each type wraps an internal representation and provides methods for
//! conversion, parsing, and access to the underlying data.
//!
//! All types support configurable capacity via const generic `CAP` for
//! fixed-size wire formats. The default capacity is the minimum required.
//!
//! # Example
//!
//! ```rust
//! use nexus_id::Base62Id;
//!
//! // Default capacity (16 bytes)
//! let id: Base62Id = Base62Id::encode(12345);
//!
//! // Custom capacity for 32-byte wire format
//! let id: Base62Id<32> = Base62Id::encode(12345);
//! ```

use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::ops::Deref;
use core::str::FromStr;

use nexus_ascii::AsciiString;

use crate::parse::{self, DecodeError, ParseError, UuidParseError};

// ============================================================================
// UUID Types
// ============================================================================

/// UUID in standard dashed format.
///
/// Format: `xxxxxxxx-xxxx-xxxx-xxxx-xxxxxxxxxxxx` (36 characters)
///
/// This type wraps the string representation of a UUID. It implements
/// `Copy`, `Hash`, `Eq`, and `Deref<Target = str>` for ergonomic usage.
///
/// # Capacity
///
/// The default capacity is 40 bytes (minimum required). Use a larger capacity
/// for fixed-size wire formats: `Uuid<64>`.
///
/// # Example
///
/// ```rust
/// use nexus_id::uuid::UuidV4;
///
/// let mut generator = UuidV4::new(12345);
/// let id = generator.next();
///
/// // Use as &str via Deref
/// println!("{}", &*id);
///
/// // Or explicitly
/// println!("{}", id.as_str());
/// ```
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct Uuid<const CAP: usize = 40>(pub(crate) AsciiString<CAP>);

impl<const CAP: usize> Uuid<CAP> {
    /// Create a Uuid from raw (hi, lo) 64-bit components.
    ///
    /// The `hi` value contains the upper 64 bits and `lo` the lower 64 bits
    /// of the 128-bit UUID. This is the inverse of [`decode()`](Self::decode).
    ///
    /// Any (hi, lo) pair produces a valid UUID string. No validation is needed.
    #[inline]
    pub fn from_raw(hi: u64, lo: u64) -> Self {
        Self(crate::encode::uuid_dashed(hi, lo))
    }

    /// Construct from a 16-byte big-endian binary representation.
    ///
    /// This is the inverse of [`to_bytes()`](Self::to_bytes).
    ///
    /// # Errors
    ///
    /// Returns [`ParseError::InvalidLength`] if `bytes.len() != 16`.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, ParseError> {
        if bytes.len() != 16 {
            return Err(ParseError::InvalidLength {
                expected: 16,
                got: bytes.len(),
            });
        }
        let hi = u64::from_be_bytes(bytes[0..8].try_into().expect("8-byte slice"));
        let lo = u64::from_be_bytes(bytes[8..16].try_into().expect("8-byte slice"));
        Ok(Self::from_raw(hi, lo))
    }

    /// Construct from a byte slice without length validation.
    ///
    /// # Safety
    ///
    /// The caller must guarantee that `bytes.len() >= 16`. Reads the first
    /// 16 bytes as a big-endian UUID.
    #[inline]
    pub unsafe fn from_bytes_unchecked(bytes: &[u8]) -> Self {
        debug_assert!(bytes.len() >= 16);
        // SAFETY: caller guarantees bytes.len() >= 16
        unsafe {
            let hi = u64::from_be_bytes(bytes.get_unchecked(0..8).try_into().unwrap_unchecked());
            let lo = u64::from_be_bytes(bytes.get_unchecked(8..16).try_into().unwrap_unchecked());
            Self::from_raw(hi, lo)
        }
    }

    /// Returns the UUID as a string slice.
    #[inline]
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }

    /// Returns the UUID as a byte slice.
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        self.0.as_bytes()
    }

    /// Decode the UUID back to raw (hi, lo) bytes.
    ///
    /// Uses SIMD (SSSE3) hex decoding when available, falling back to
    /// scalar on other architectures.
    #[inline]
    pub fn decode(&self) -> (u64, u64) {
        let bytes: &[u8; 36] = self.0.as_bytes().try_into().unwrap();
        // SAFETY: self.0 was validated at construction — always valid hex+dashes.
        // Uuid is always 36 bytes. try_into is infallible here.
        unsafe { crate::simd::uuid_parse_dashed(bytes).unwrap_unchecked() }
    }

    /// Extract the UUID version (4 bits).
    #[inline]
    pub fn version(&self) -> u8 {
        // Version is char at position 14
        hex_digit(self.0.as_bytes()[14])
    }

    /// Parse a UUID from a dashed string.
    ///
    /// Accepts format: `xxxxxxxx-xxxx-xxxx-xxxx-xxxxxxxxxxxx` (36 chars).
    /// Case-insensitive for hex digits.
    ///
    /// # Errors
    ///
    /// Returns [`UuidParseError`] if the input has wrong length, invalid hex
    /// characters, or missing/misplaced dashes.
    pub fn parse(s: &str) -> Result<Self, UuidParseError> {
        let bytes = s.as_bytes();
        if bytes.len() != 36 {
            return Err(UuidParseError::InvalidLength {
                expected: 36,
                got: bytes.len(),
            });
        }

        // Validate dashes at positions 8, 13, 18, 23
        if bytes[8] != b'-' || bytes[13] != b'-' || bytes[18] != b'-' || bytes[23] != b'-' {
            return Err(UuidParseError::InvalidFormat);
        }

        // SAFETY: We verified bytes.len() == 36.
        let input: &[u8; 36] = unsafe { &*(bytes.as_ptr().cast::<[u8; 36]>()) };

        // Decode via SIMD path: compacts dashes out, decodes 32 hex chars in parallel.
        let (hi, lo) = crate::simd::uuid_parse_dashed(input).map_err(|pos| {
            // Map compacted 32-byte position back to 36-byte input position.
            let input_pos = match pos {
                0..=7 => pos,       // segment 1: no offset
                8..=11 => pos + 1,  // segment 2: skip dash at 8
                12..=15 => pos + 2, // segment 3: skip dashes at 8, 13
                16..=19 => pos + 3, // segment 4: skip dashes at 8, 13, 18
                _ => pos + 4,       // segment 5: skip all 4 dashes
            };
            UuidParseError::InvalidChar {
                position: input_pos,
                byte: bytes[input_pos],
            }
        })?;

        Ok(Self::from_raw(hi, lo))
    }

    /// Convert to compact format (no dashes).
    ///
    /// Returns a `UuidCompact` with default capacity.
    #[inline]
    pub fn to_compact(&self) -> UuidCompact {
        let (hi, lo) = self.decode();
        UuidCompact::from_raw(hi, lo)
    }

    /// Check if this is the nil UUID (all zeros).
    ///
    /// Compares raw bytes directly — no hex decoding needed.
    #[inline]
    pub fn is_nil(&self) -> bool {
        self.0.as_bytes() == b"00000000-0000-0000-0000-000000000000"
    }

    /// Extract the timestamp for UUID v7 (milliseconds since Unix epoch).
    ///
    /// Returns `None` if this is not a v7 UUID.
    #[inline]
    pub fn timestamp_ms(&self) -> Option<u64> {
        if self.version() != 7 {
            return None;
        }
        let (hi, _) = self.decode();
        Some(hi >> 16)
    }

    /// Get the raw 128-bit value as big-endian bytes.
    pub fn to_bytes(&self) -> [u8; 16] {
        let (hi, lo) = self.decode();
        let mut out = [0u8; 16];
        out[..8].copy_from_slice(&hi.to_be_bytes());
        out[8..].copy_from_slice(&lo.to_be_bytes());
        out
    }
}

impl<const CAP: usize> Deref for Uuid<CAP> {
    type Target = str;

    #[inline]
    fn deref(&self) -> &str {
        self.0.as_str()
    }
}

impl<const CAP: usize> AsRef<str> for Uuid<CAP> {
    #[inline]
    fn as_ref(&self) -> &str {
        self.0.as_str()
    }
}

impl<const CAP: usize> fmt::Display for Uuid<CAP> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.0.as_str())
    }
}

impl<const CAP: usize> fmt::Debug for Uuid<CAP> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Uuid({})", self.0.as_str())
    }
}

impl<const CAP: usize> Hash for Uuid<CAP> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<const CAP: usize> Ord for Uuid<CAP> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        // Lexicographic order = time order for v7 UUIDs
        self.0.cmp(&other.0)
    }
}

impl<const CAP: usize> PartialOrd for Uuid<CAP> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const CAP: usize> FromStr for Uuid<CAP> {
    type Err = UuidParseError;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
    }
}

// ============================================================================
// UUID Compact (no dashes)
// ============================================================================

/// UUID in compact format (no dashes).
///
/// Format: `xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx` (32 characters)
///
/// # Capacity
///
/// The default capacity is 32 bytes (minimum required). Use a larger capacity
/// for fixed-size wire formats: `UuidCompact<64>`.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct UuidCompact<const CAP: usize = 32>(pub(crate) AsciiString<CAP>);

impl<const CAP: usize> UuidCompact<CAP> {
    /// Create a UuidCompact from raw (hi, lo) 64-bit components.
    ///
    /// The `hi` value contains the upper 64 bits and `lo` the lower 64 bits
    /// of the 128-bit UUID. This is the inverse of [`decode()`](Self::decode).
    #[inline]
    pub fn from_raw(hi: u64, lo: u64) -> Self {
        Self(crate::encode::hex_u128(hi, lo))
    }

    /// Construct from a 16-byte big-endian binary representation.
    ///
    /// This is the inverse of [`to_bytes()`](Self::to_bytes).
    ///
    /// # Errors
    ///
    /// Returns [`ParseError::InvalidLength`] if `bytes.len() != 16`.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, ParseError> {
        if bytes.len() != 16 {
            return Err(ParseError::InvalidLength {
                expected: 16,
                got: bytes.len(),
            });
        }
        let hi = u64::from_be_bytes(bytes[0..8].try_into().expect("8-byte slice"));
        let lo = u64::from_be_bytes(bytes[8..16].try_into().expect("8-byte slice"));
        Ok(Self::from_raw(hi, lo))
    }

    /// Construct from a byte slice without length validation.
    ///
    /// # Safety
    ///
    /// The caller must guarantee that `bytes.len() >= 16`.
    #[inline]
    pub unsafe fn from_bytes_unchecked(bytes: &[u8]) -> Self {
        debug_assert!(bytes.len() >= 16);
        // SAFETY: caller guarantees bytes.len() >= 16
        unsafe {
            let hi = u64::from_be_bytes(bytes.get_unchecked(0..8).try_into().unwrap_unchecked());
            let lo = u64::from_be_bytes(bytes.get_unchecked(8..16).try_into().unwrap_unchecked());
            Self::from_raw(hi, lo)
        }
    }

    /// Returns the UUID (no-dash hex) as a string slice.
    #[inline]
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }

    /// Returns the UUID (no-dash hex) as a byte slice.
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        self.0.as_bytes()
    }

    /// Decode back to raw (hi, lo) bytes.
    pub fn decode(&self) -> (u64, u64) {
        let bytes: &[u8; 32] = self.0.as_bytes().try_into().expect("32-byte hex string");
        // SAFETY: Data was validated at construction; decode cannot fail.
        unsafe { crate::simd::hex_decode_32(bytes).unwrap_unchecked() }
    }

    /// Parse a compact UUID from a hex string (no dashes).
    ///
    /// Accepts format: 32 hex characters. Case-insensitive.
    pub fn parse(s: &str) -> Result<Self, ParseError> {
        let bytes = s.as_bytes();
        if bytes.len() != 32 {
            return Err(ParseError::InvalidLength {
                expected: 32,
                got: bytes.len(),
            });
        }

        // SIMD path: validates and decodes in a single pass
        let hex_bytes: &[u8; 32] = bytes.try_into().expect("32-byte hex string");
        let (hi, lo) =
            crate::simd::hex_decode_32(hex_bytes).map_err(|pos| ParseError::InvalidChar {
                position: pos,
                byte: bytes[pos],
            })?;

        Ok(Self::from_raw(hi, lo))
    }

    /// Convert to dashed format.
    ///
    /// Returns a `Uuid` with default capacity.
    #[inline]
    pub fn to_dashed(&self) -> Uuid {
        let (hi, lo) = self.decode();
        Uuid::from_raw(hi, lo)
    }

    /// Check if this is the nil UUID.
    ///
    /// Compares raw bytes directly — no hex decoding needed.
    #[inline]
    pub fn is_nil(&self) -> bool {
        self.0.as_bytes() == b"00000000000000000000000000000000"
    }

    /// Get the raw 128-bit value as big-endian bytes.
    pub fn to_bytes(&self) -> [u8; 16] {
        let (hi, lo) = self.decode();
        let mut out = [0u8; 16];
        out[..8].copy_from_slice(&hi.to_be_bytes());
        out[8..].copy_from_slice(&lo.to_be_bytes());
        out
    }
}

impl<const CAP: usize> Deref for UuidCompact<CAP> {
    type Target = str;

    #[inline]
    fn deref(&self) -> &str {
        self.0.as_str()
    }
}

impl<const CAP: usize> AsRef<str> for UuidCompact<CAP> {
    #[inline]
    fn as_ref(&self) -> &str {
        self.0.as_str()
    }
}

impl<const CAP: usize> fmt::Display for UuidCompact<CAP> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.0.as_str())
    }
}

impl<const CAP: usize> fmt::Debug for UuidCompact<CAP> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "UuidCompact({})", self.0.as_str())
    }
}

impl<const CAP: usize> Hash for UuidCompact<CAP> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<const CAP: usize> Ord for UuidCompact<CAP> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl<const CAP: usize> PartialOrd for UuidCompact<CAP> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const CAP: usize> FromStr for UuidCompact<CAP> {
    type Err = ParseError;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
    }
}

// ============================================================================
// HexId64 - Hex-encoded u64
// ============================================================================

/// Hex-encoded 64-bit ID.
///
/// Format: 16 lowercase hex characters.
///
/// # Capacity
///
/// The default capacity is 16 bytes (minimum required). Use a larger capacity
/// for fixed-size wire formats: `HexId64<32>`.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct HexId64<const CAP: usize = 16>(pub(crate) AsciiString<CAP>);

impl<const CAP: usize> HexId64<CAP> {
    /// Encode a u64 as hex.
    #[inline]
    pub fn encode(value: u64) -> Self {
        Self(crate::encode::hex_u64(value))
    }

    /// Returns the encoded hex string.
    #[inline]
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }

    /// Returns the encoded hex string as a byte slice.
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        self.0.as_bytes()
    }

    /// Decode back to u64.
    #[inline]
    pub fn decode(&self) -> u64 {
        let bytes: &[u8; 16] = self.0.as_bytes().try_into().expect("16-byte hex string");
        // SAFETY: Data was validated at construction; decode cannot fail.
        unsafe { crate::simd::hex_decode_16(bytes).unwrap_unchecked() }
    }

    /// Parse a hex ID from a 16-character hex string. Case-insensitive.
    pub fn parse(s: &str) -> Result<Self, ParseError> {
        let bytes = s.as_bytes();
        if bytes.len() != 16 {
            return Err(ParseError::InvalidLength {
                expected: 16,
                got: bytes.len(),
            });
        }

        // SIMD path: validates and decodes in a single pass
        let hex_bytes: &[u8; 16] = bytes.try_into().expect("16-byte hex string");
        let value =
            crate::simd::hex_decode_16(hex_bytes).map_err(|pos| ParseError::InvalidChar {
                position: pos,
                byte: bytes[pos],
            })?;

        Ok(Self::encode(value))
    }
}

impl<const CAP: usize> Deref for HexId64<CAP> {
    type Target = str;

    #[inline]
    fn deref(&self) -> &str {
        self.0.as_str()
    }
}

impl<const CAP: usize> AsRef<str> for HexId64<CAP> {
    #[inline]
    fn as_ref(&self) -> &str {
        self.0.as_str()
    }
}

impl<const CAP: usize> fmt::Display for HexId64<CAP> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.0.as_str())
    }
}

impl<const CAP: usize> fmt::Debug for HexId64<CAP> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "HexId64({})", self.0.as_str())
    }
}

impl<const CAP: usize> Hash for HexId64<CAP> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<const CAP: usize> FromStr for HexId64<CAP> {
    type Err = ParseError;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
    }
}

// ============================================================================
// Base62Id - Base62-encoded u64
// ============================================================================

/// Base62-encoded 64-bit ID.
///
/// Format: 11 alphanumeric characters (0-9, A-Z, a-z).
///
/// # Capacity
///
/// The default capacity is 16 bytes (minimum required). Use a larger capacity
/// for fixed-size wire formats: `Base62Id<32>`.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct Base62Id<const CAP: usize = 16>(pub(crate) AsciiString<CAP>);

impl<const CAP: usize> Base62Id<CAP> {
    /// Encode a u64 as base62.
    #[inline]
    pub fn encode(value: u64) -> Self {
        Self(crate::encode::base62_u64(value))
    }

    /// Returns the encoded Base62 string.
    #[inline]
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }

    /// Returns the encoded Base62 string as a byte slice.
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        self.0.as_bytes()
    }

    /// Decode back to u64.
    #[inline]
    pub fn decode(&self) -> u64 {
        let bytes = self.0.as_bytes();
        let mut value: u64 = 0;
        for &b in bytes {
            value = value * 62 + base62_digit(b) as u64;
        }
        value
    }

    /// Parse a base62 ID from an 11-character string.
    pub fn parse(s: &str) -> Result<Self, DecodeError> {
        let bytes = s.as_bytes();
        if bytes.len() != 11 {
            return Err(DecodeError::InvalidLength {
                expected: 11,
                got: bytes.len(),
            });
        }

        let mut value: u64 = 0;
        let mut i = 0;
        while i < 11 {
            let d = parse::validate_base62(bytes[i], i)?;
            value = value
                .checked_mul(62)
                .and_then(|v| v.checked_add(d as u64))
                .ok_or(DecodeError::Overflow)?;
            i += 1;
        }

        Ok(Self::encode(value))
    }
}

impl<const CAP: usize> Deref for Base62Id<CAP> {
    type Target = str;

    #[inline]
    fn deref(&self) -> &str {
        self.0.as_str()
    }
}

impl<const CAP: usize> AsRef<str> for Base62Id<CAP> {
    #[inline]
    fn as_ref(&self) -> &str {
        self.0.as_str()
    }
}

impl<const CAP: usize> fmt::Display for Base62Id<CAP> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.0.as_str())
    }
}

impl<const CAP: usize> fmt::Debug for Base62Id<CAP> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Base62Id({})", self.0.as_str())
    }
}

impl<const CAP: usize> Hash for Base62Id<CAP> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<const CAP: usize> FromStr for Base62Id<CAP> {
    type Err = DecodeError;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
    }
}

// ============================================================================
// Base36Id - Base36-encoded u64
// ============================================================================

/// Base36-encoded 64-bit ID.
///
/// Format: 13 alphanumeric characters (0-9, a-z), case-insensitive.
///
/// # Capacity
///
/// The default capacity is 16 bytes (minimum required). Use a larger capacity
/// for fixed-size wire formats: `Base36Id<32>`.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct Base36Id<const CAP: usize = 16>(pub(crate) AsciiString<CAP>);

impl<const CAP: usize> Base36Id<CAP> {
    /// Encode a u64 as base36.
    #[inline]
    pub fn encode(value: u64) -> Self {
        Self(crate::encode::base36_u64(value))
    }

    /// Returns the encoded Base36 string.
    #[inline]
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }

    /// Returns the encoded Base36 string as a byte slice.
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        self.0.as_bytes()
    }

    /// Decode back to u64.
    #[inline]
    pub fn decode(&self) -> u64 {
        let bytes = self.0.as_bytes();
        let mut value: u64 = 0;
        for &b in bytes {
            value = value * 36 + base36_digit(b) as u64;
        }
        value
    }

    /// Parse a base36 ID from a 13-character string. Case-insensitive.
    pub fn parse(s: &str) -> Result<Self, DecodeError> {
        let bytes = s.as_bytes();
        if bytes.len() != 13 {
            return Err(DecodeError::InvalidLength {
                expected: 13,
                got: bytes.len(),
            });
        }

        let mut value: u64 = 0;
        let mut i = 0;
        while i < 13 {
            let d = parse::validate_base36(bytes[i], i)?;
            value = value
                .checked_mul(36)
                .and_then(|v| v.checked_add(d as u64))
                .ok_or(DecodeError::Overflow)?;
            i += 1;
        }

        Ok(Self::encode(value))
    }
}

impl<const CAP: usize> Deref for Base36Id<CAP> {
    type Target = str;

    #[inline]
    fn deref(&self) -> &str {
        self.0.as_str()
    }
}

impl<const CAP: usize> AsRef<str> for Base36Id<CAP> {
    #[inline]
    fn as_ref(&self) -> &str {
        self.0.as_str()
    }
}

impl<const CAP: usize> fmt::Display for Base36Id<CAP> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.0.as_str())
    }
}

impl<const CAP: usize> fmt::Debug for Base36Id<CAP> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Base36Id({})", self.0.as_str())
    }
}

impl<const CAP: usize> Hash for Base36Id<CAP> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<const CAP: usize> FromStr for Base36Id<CAP> {
    type Err = DecodeError;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
    }
}

// ============================================================================
// ULID
// ============================================================================

/// ULID (Universally Unique Lexicographically Sortable Identifier).
///
/// Format: 26 Crockford Base32 characters (128 bits total)
/// - First 10 chars: 48-bit timestamp (milliseconds since Unix epoch)
/// - Last 16 chars: 80 bits of randomness
///
/// ULIDs are lexicographically sortable and monotonically increasing.
///
/// # Capacity
///
/// The default capacity is 32 bytes (minimum required). Use a larger capacity
/// for fixed-size wire formats: `Ulid<64>`.
///
/// # Example
///
/// ```rust
/// use std::time::{Instant, SystemTime, UNIX_EPOCH};
/// use nexus_id::ulid::UlidGenerator;
///
/// let epoch = Instant::now();
/// let unix_base = SystemTime::now()
///     .duration_since(UNIX_EPOCH)
///     .unwrap()
///     .as_millis() as u64;
///
/// let mut generator = UlidGenerator::new(epoch, unix_base, 12345);
/// let id = generator.next(Instant::now());
/// assert_eq!(id.len(), 26);
/// ```
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct Ulid<const CAP: usize = 32>(pub(crate) AsciiString<CAP>);

impl<const CAP: usize> Ulid<CAP> {
    /// Create a ULID from raw components.
    ///
    /// - `timestamp_ms`: 48-bit millisecond timestamp (upper bits ignored)
    /// - `rand_hi`: upper 16 bits of the 80-bit random field
    /// - `rand_lo`: lower 64 bits of the 80-bit random field
    #[inline]
    pub fn from_raw(timestamp_ms: u64, rand_hi: u16, rand_lo: u64) -> Self {
        Self(crate::encode::ulid_encode(timestamp_ms, rand_hi, rand_lo))
    }

    /// Construct from a 16-byte big-endian binary representation.
    ///
    /// Layout: `[timestamp: 6 bytes][rand_hi: 2 bytes][rand_lo: 8 bytes]`
    ///
    /// This is the inverse of [`to_bytes()`](Self::to_bytes).
    ///
    /// # Errors
    ///
    /// Returns [`ParseError::InvalidLength`] if `bytes.len() != 16`.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, ParseError> {
        if bytes.len() != 16 {
            return Err(ParseError::InvalidLength {
                expected: 16,
                got: bytes.len(),
            });
        }
        // Timestamp: bytes 0-5 (48 bits, big-endian)
        let mut ts_buf = [0u8; 8];
        ts_buf[2..8].copy_from_slice(&bytes[0..6]);
        let timestamp_ms = u64::from_be_bytes(ts_buf);

        let rand_hi = u16::from_be_bytes(bytes[6..8].try_into().expect("2-byte slice"));
        let rand_lo = u64::from_be_bytes(bytes[8..16].try_into().expect("8-byte slice"));

        Ok(Self::from_raw(timestamp_ms, rand_hi, rand_lo))
    }

    /// Construct from a byte slice without length validation.
    ///
    /// # Safety
    ///
    /// The caller must guarantee that `bytes.len() >= 16`.
    #[inline]
    pub unsafe fn from_bytes_unchecked(bytes: &[u8]) -> Self {
        debug_assert!(bytes.len() >= 16);
        // SAFETY: caller guarantees bytes.len() >= 16
        unsafe {
            let mut ts_buf = [0u8; 8];
            core::ptr::copy_nonoverlapping(bytes.as_ptr(), ts_buf.as_mut_ptr().add(2), 6);
            let timestamp_ms = u64::from_be_bytes(ts_buf);

            let rand_hi =
                u16::from_be_bytes(bytes.get_unchecked(6..8).try_into().unwrap_unchecked());
            let rand_lo =
                u64::from_be_bytes(bytes.get_unchecked(8..16).try_into().unwrap_unchecked());

            Self::from_raw(timestamp_ms, rand_hi, rand_lo)
        }
    }

    /// Returns the encoded ULID (Crockford Base32) string.
    #[inline]
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }

    /// Returns the encoded ULID string as a byte slice.
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        self.0.as_bytes()
    }

    /// Extract the timestamp (milliseconds since Unix epoch).
    pub fn timestamp_ms(&self) -> u64 {
        let bytes = self.0.as_bytes();
        let mut ts: u64 = 0;

        // Decode first 10 characters (48 bits of timestamp)
        // Char 0: 3 bits, Chars 1-9: 5 bits each = 3 + 45 = 48 bits
        ts = (ts << 3) | crockford32_digit(bytes[0]) as u64;
        for &b in &bytes[1..10] {
            ts = (ts << 5) | crockford32_digit(b) as u64;
        }

        ts
    }

    /// Parse a ULID from a 26-character Crockford Base32 string.
    ///
    /// Case-insensitive. Accepts Crockford aliases (I/L → 1, O → 0).
    pub fn parse(s: &str) -> Result<Self, ParseError> {
        let bytes = s.as_bytes();
        if bytes.len() != 26 {
            return Err(ParseError::InvalidLength {
                expected: 26,
                got: bytes.len(),
            });
        }

        // Single-pass: validate and decode simultaneously via lookup table.
        // Decode timestamp (chars 0-9): 3 + 9×5 = 48 bits
        // First char encodes only 3 bits — values > 7 overflow the 48-bit timestamp.
        let first = parse::validate_crockford32(bytes[0], 0)?;
        if first > 7 {
            return Err(ParseError::InvalidChar {
                position: 0,
                byte: bytes[0],
            });
        }
        let mut ts: u64 = first as u64;
        let mut i = 1;
        while i < 10 {
            let d = parse::validate_crockford32(bytes[i], i)? as u64;
            ts = (ts << 5) | d;
            i += 1;
        }

        // Decode random (chars 10-25): 80 bits
        let c10 = parse::validate_crockford32(bytes[10], 10)? as u16;
        let c11 = parse::validate_crockford32(bytes[11], 11)? as u16;
        let c12 = parse::validate_crockford32(bytes[12], 12)? as u16;
        let c13 = parse::validate_crockford32(bytes[13], 13)? as u64;

        let rand_hi = (c10 << 11) | (c11 << 6) | (c12 << 1) | ((c13 >> 4) as u16);

        let mut rand_lo: u64 = c13 & 0x0F;
        i = 14;
        while i < 26 {
            let d = parse::validate_crockford32(bytes[i], i)? as u64;
            rand_lo = (rand_lo << 5) | d;
            i += 1;
        }

        Ok(Self::from_raw(ts, rand_hi, rand_lo))
    }

    /// Check if this is a nil ULID (all zeros).
    #[inline]
    pub fn is_nil(&self) -> bool {
        self.timestamp_ms() == 0 && {
            let (hi, lo) = self.random();
            hi == 0 && lo == 0
        }
    }

    /// Convert to a UUID v7-compatible format.
    ///
    /// Maps the ULID's 128-bit value into UUID v7 layout, setting version (7) and
    /// variant (RFC) bits.
    ///
    /// Returns a `Uuid` with default capacity.
    ///
    /// # Data Loss
    ///
    /// This conversion is **lossy**. ULID has 80 random bits, but UUID v7 reserves
    /// 6 bits for version+variant, leaving only 74 bits for randomness. The bottom
    /// 6 bits of `rand_lo` are discarded. The conversion is not reversible.
    pub fn to_uuid(&self) -> Uuid {
        let ts = self.timestamp_ms();
        let (rand_hi, rand_lo) = self.random();

        // Pack into UUID v7 layout
        // hi: [timestamp: 48][version=7: 4][rand_a: 12]
        let rand_a = (rand_hi >> 4) as u64; // top 12 bits of rand_hi
        let hi = (ts << 16) | (0x7 << 12) | (rand_a & 0xFFF);

        // lo: [variant=10: 2][rand_b: 62]
        // Use remaining bits from rand_hi (4 bits) + rand_lo (64 bits) → take 62 bits
        let remaining = ((rand_hi as u64 & 0x0F) << 58) | (rand_lo >> 6);
        let lo = (0b10u64 << 62) | (remaining & 0x3FFF_FFFF_FFFF_FFFF);

        Uuid::from_raw(hi, lo)
    }

    /// Get the raw 128-bit value as big-endian bytes.
    pub fn to_bytes(&self) -> [u8; 16] {
        let ts = self.timestamp_ms();
        let (rand_hi, rand_lo) = self.random();

        let mut out = [0u8; 16];
        // Timestamp in bytes 0-5 (48 bits, big-endian)
        let ts_bytes = ts.to_be_bytes();
        out[0..6].copy_from_slice(&ts_bytes[2..8]);
        // Random hi in bytes 6-7 (16 bits)
        out[6..8].copy_from_slice(&rand_hi.to_be_bytes());
        // Random lo in bytes 8-15 (64 bits)
        out[8..16].copy_from_slice(&rand_lo.to_be_bytes());
        out
    }

    /// Decode the random portion as (hi: u16, lo: u64).
    pub fn random(&self) -> (u16, u64) {
        let bytes = self.0.as_bytes();

        // Chars 10-13 contain rand_hi (16 bits) spread across boundaries
        // Char 10: bits 11-15 of rand_hi (5 bits)
        // Char 11: bits 6-10 of rand_hi (5 bits)
        // Char 12: bits 1-5 of rand_hi (5 bits)
        // Char 13: bit 0 of rand_hi (1 bit) + bits 60-63 of rand_lo (4 bits)

        let c10 = crockford32_digit(bytes[10]) as u16;
        let c11 = crockford32_digit(bytes[11]) as u16;
        let c12 = crockford32_digit(bytes[12]) as u16;
        let c13 = crockford32_digit(bytes[13]) as u64;

        let rand_hi = (c10 << 11) | (c11 << 6) | (c12 << 1) | ((c13 >> 4) as u16);

        // Chars 13-25 contain rand_lo (64 bits)
        // Char 13 contributes 4 bits (already extracted above for rand_hi)
        let mut rand_lo: u64 = c13 & 0x0F;
        for &b in &bytes[14..26] {
            rand_lo = (rand_lo << 5) | crockford32_digit(b) as u64;
        }

        (rand_hi, rand_lo)
    }
}

impl<const CAP: usize> Deref for Ulid<CAP> {
    type Target = str;

    #[inline]
    fn deref(&self) -> &str {
        self.0.as_str()
    }
}

impl<const CAP: usize> AsRef<str> for Ulid<CAP> {
    #[inline]
    fn as_ref(&self) -> &str {
        self.0.as_str()
    }
}

impl<const CAP: usize> fmt::Display for Ulid<CAP> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.0.as_str())
    }
}

impl<const CAP: usize> fmt::Debug for Ulid<CAP> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Ulid({})", self.0.as_str())
    }
}

impl<const CAP: usize> Hash for Ulid<CAP> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<const CAP: usize> Ord for Ulid<CAP> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        // Lexicographic order = time order (timestamp in MSB chars)
        self.0.cmp(&other.0)
    }
}

impl<const CAP: usize> PartialOrd for Ulid<CAP> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const CAP: usize> FromStr for Ulid<CAP> {
    type Err = ParseError;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
    }
}

// ============================================================================
// Cross-type From impls
// ============================================================================

impl<const CAP: usize> From<Uuid<CAP>> for UuidCompact {
    /// Lossless conversion: strip dashes.
    #[inline]
    fn from(u: Uuid<CAP>) -> Self {
        u.to_compact()
    }
}

impl<const CAP: usize> From<UuidCompact<CAP>> for Uuid {
    /// Lossless conversion: add dashes.
    #[inline]
    fn from(u: UuidCompact<CAP>) -> Self {
        u.to_dashed()
    }
}

impl<const CAP: usize> From<Ulid<CAP>> for Uuid {
    /// Convert ULID to UUID v7 format (sets version and variant bits).
    ///
    /// **Lossy**: 6 bits of randomness are discarded. See [`Ulid::to_uuid()`].
    #[inline]
    fn from(u: Ulid<CAP>) -> Self {
        u.to_uuid()
    }
}

// ============================================================================
// Helper functions
// ============================================================================

/// Convert Crockford Base32 character to value (0-31) via lookup table.
/// For already-validated data (from our own encode output).
#[inline]
fn crockford32_digit(b: u8) -> u8 {
    parse::CROCKFORD32_DECODE[b as usize]
}

/// Convert hex character to value (0-15).
#[inline]
const fn hex_digit(b: u8) -> u8 {
    match b {
        b'0'..=b'9' => b - b'0',
        b'a'..=b'f' => b - b'a' + 10,
        b'A'..=b'F' => b - b'A' + 10,
        _ => 0, // Should never happen for valid IDs
    }
}

/// Convert base62 character to value (0-61).
#[inline]
const fn base62_digit(b: u8) -> u8 {
    match b {
        b'0'..=b'9' => b - b'0',
        b'A'..=b'Z' => b - b'A' + 10,
        b'a'..=b'z' => b - b'a' + 36,
        _ => 0,
    }
}

/// Convert base36 character to value (0-35).
#[inline]
const fn base36_digit(b: u8) -> u8 {
    match b {
        b'0'..=b'9' => b - b'0',
        b'a'..=b'z' => b - b'a' + 10,
        b'A'..=b'Z' => b - b'A' + 10, // Case insensitive
        _ => 0,
    }
}

#[cfg(all(test, feature = "std"))]
mod tests {
    use super::*;

    #[test]
    fn uuid_decode_roundtrip() {
        let hi = 0x0123_4567_89AB_CDEF_u64;
        let lo = 0xFEDC_BA98_7654_3210_u64;

        let uuid: Uuid = Uuid::from_raw(hi, lo);
        let (decoded_hi, decoded_lo) = uuid.decode();

        assert_eq!(hi, decoded_hi);
        assert_eq!(lo, decoded_lo);
    }

    #[test]
    fn uuid_larger_cap() {
        let hi = 0x0123_4567_89AB_CDEF_u64;
        let lo = 0xFEDC_BA98_7654_3210_u64;

        let small: Uuid<40> = Uuid::from_raw(hi, lo);
        let large: Uuid<64> = Uuid::from_raw(hi, lo);

        assert_eq!(small.as_str(), large.as_str());
        assert_eq!(small.decode(), large.decode());
    }

    #[test]
    fn uuid_compact_decode_roundtrip() {
        let hi = 0x0123_4567_89AB_CDEF_u64;
        let lo = 0xFEDC_BA98_7654_3210_u64;

        let uuid: UuidCompact = UuidCompact::from_raw(hi, lo);
        let (decoded_hi, decoded_lo) = uuid.decode();

        assert_eq!(hi, decoded_hi);
        assert_eq!(lo, decoded_lo);
    }

    #[test]
    fn hex_id64_decode_roundtrip() {
        for value in [0, 1, 12345, u64::MAX, 0xDEAD_BEEF_CAFE_BABE] {
            let id: HexId64 = HexId64::encode(value);
            assert_eq!(id.decode(), value);
        }
    }

    #[test]
    fn hex_id64_larger_cap() {
        let id_small: HexId64<16> = HexId64::encode(12345);
        let id_large: HexId64<32> = HexId64::encode(12345);
        assert_eq!(id_small.as_str(), id_large.as_str());
    }

    #[test]
    fn base62_id_decode_roundtrip() {
        for value in [0, 1, 12345, u64::MAX] {
            let id: Base62Id = Base62Id::encode(value);
            assert_eq!(id.decode(), value);
        }
    }

    #[test]
    fn base62_id_larger_cap() {
        let id_small: Base62Id<16> = Base62Id::encode(12345);
        let id_large: Base62Id<32> = Base62Id::encode(12345);
        assert_eq!(id_small.as_str(), id_large.as_str());
    }

    #[test]
    fn base36_id_decode_roundtrip() {
        for value in [0, 1, 12345, u64::MAX] {
            let id: Base36Id = Base36Id::encode(value);
            assert_eq!(id.decode(), value);
        }
    }

    #[test]
    fn base36_id_larger_cap() {
        let id_small: Base36Id<16> = Base36Id::encode(12345);
        let id_large: Base36Id<32> = Base36Id::encode(12345);
        assert_eq!(id_small.as_str(), id_large.as_str());
    }

    #[test]
    fn ulid_larger_cap() {
        let small: Ulid<32> = Ulid::from_raw(1_700_000_000_000, 0x1234, 0xDEAD_BEEF);
        let large: Ulid<64> = Ulid::from_raw(1_700_000_000_000, 0x1234, 0xDEAD_BEEF);
        assert_eq!(small.as_str(), large.as_str());
        assert_eq!(small.timestamp_ms(), large.timestamp_ms());
    }

    #[test]
    fn uuid_version() {
        // V4 UUID
        let hi = 0x0123_4567_89AB_4DEF_u64; // version 4 at position
        let lo = 0x8EDC_BA98_7654_3210_u64;
        let uuid: Uuid = Uuid::from_raw(hi, lo);
        assert_eq!(uuid.version(), 4);

        // V7 UUID
        let hi = 0x0123_4567_89AB_7DEF_u64; // version 7 at position
        let uuid: Uuid = Uuid::from_raw(hi, lo);
        assert_eq!(uuid.version(), 7);
    }

    #[test]
    fn display_works() {
        let uuid: Uuid = Uuid::from_raw(0x0123_4567_89AB_CDEF, 0xFEDC_BA98_7654_3210);
        let s = format!("{}", uuid);
        assert_eq!(s, "01234567-89ab-cdef-fedc-ba9876543210");
    }

    #[test]
    fn deref_works() {
        let uuid: Uuid = Uuid::from_raw(0x0123_4567_89AB_CDEF, 0xFEDC_BA98_7654_3210);
        let s: &str = &uuid;
        assert_eq!(s, "01234567-89ab-cdef-fedc-ba9876543210");
    }

    #[test]
    fn uuid_from_bytes_roundtrip() {
        let original: Uuid = Uuid::from_raw(0x0123_4567_89AB_CDEF, 0xFEDC_BA98_7654_3210);
        let bytes = original.to_bytes();
        let recovered: Uuid = Uuid::from_bytes(&bytes).unwrap();
        assert_eq!(original, recovered);
    }

    #[test]
    fn uuid_from_bytes_wrong_length() {
        assert!(Uuid::<40>::from_bytes(&[0u8; 15]).is_err());
        assert!(Uuid::<40>::from_bytes(&[0u8; 17]).is_err());
        assert!(Uuid::<40>::from_bytes(&[]).is_err());
    }

    #[test]
    fn uuid_from_bytes_unchecked_roundtrip() {
        let original: Uuid = Uuid::from_raw(0xDEAD_BEEF_CAFE_BABE, 0x0123_4567_89AB_CDEF);
        let bytes = original.to_bytes();
        // SAFETY: bytes came from original.to_bytes(), so it encodes a valid Uuid.
        let recovered: Uuid = unsafe { Uuid::from_bytes_unchecked(&bytes) };
        assert_eq!(original, recovered);
    }

    #[test]
    fn uuid_compact_from_bytes_roundtrip() {
        let original: UuidCompact =
            UuidCompact::from_raw(0x0123_4567_89AB_CDEF, 0xFEDC_BA98_7654_3210);
        let bytes = original.to_bytes();
        let recovered: UuidCompact = UuidCompact::from_bytes(&bytes).unwrap();
        assert_eq!(original, recovered);
    }

    #[test]
    fn uuid_compact_from_bytes_wrong_length() {
        assert!(UuidCompact::<32>::from_bytes(&[0u8; 15]).is_err());
        assert!(UuidCompact::<32>::from_bytes(&[0u8; 17]).is_err());
    }

    #[test]
    fn ulid_from_bytes_roundtrip() {
        let original: Ulid = Ulid::from_raw(1_700_000_000_000, 0xABCD, 0xDEAD_BEEF_CAFE_BABE);
        let bytes = original.to_bytes();
        let recovered: Ulid = Ulid::from_bytes(&bytes).unwrap();
        assert_eq!(original.timestamp_ms(), recovered.timestamp_ms());
        assert_eq!(original.random(), recovered.random());
        assert_eq!(original, recovered);
    }

    #[test]
    fn ulid_from_bytes_wrong_length() {
        assert!(Ulid::<32>::from_bytes(&[0u8; 15]).is_err());
        assert!(Ulid::<32>::from_bytes(&[0u8; 17]).is_err());
    }

    #[test]
    fn ulid_from_bytes_unchecked_roundtrip() {
        let original: Ulid = Ulid::from_raw(1_700_000_000_000, 0x1234, 0x0123_4567_89AB_CDEF);
        let bytes = original.to_bytes();
        // SAFETY: bytes came from original.to_bytes(), so it encodes a valid Ulid.
        let recovered: Ulid = unsafe { Ulid::from_bytes_unchecked(&bytes) };
        assert_eq!(original, recovered);
    }

    #[test]
    fn ulid_parse_rejects_overflow_first_char() {
        // First char value > 7 overflows the 48-bit timestamp.
        // '8' decodes to value 8 in Crockford Base32.
        let overflow = "80000000000000000000000000";
        assert!(Ulid::<32>::parse(overflow).is_err());

        // 'Z' decodes to value 31 — also invalid.
        let z_first = "Z0000000000000000000000000";
        assert!(Ulid::<32>::parse(z_first).is_err());

        // '7' (value 7) is the max valid first char.
        let max_valid = "70000000000000000000000000";
        assert!(Ulid::<32>::parse(max_valid).is_ok());
    }

    // ====================================================================
    // Overflow detection
    // ====================================================================

    #[test]
    fn base62_parse_overflow() {
        use crate::parse::DecodeError;

        // "zzzzzzzzzzz" (11 z's) = 61*(62^10 + 62^9 + ... + 1) > u64::MAX
        let result = Base62Id::<16>::parse("zzzzzzzzzzz");
        assert_eq!(result, Err(DecodeError::Overflow));

        // u64::MAX encodes to "LygHa16AHYF" — should round-trip
        let max_id: Base62Id = Base62Id::encode(u64::MAX);
        let parsed = Base62Id::<16>::parse(max_id.as_str()).unwrap();
        assert_eq!(parsed.decode(), u64::MAX);
    }

    #[test]
    fn base36_parse_overflow() {
        use crate::parse::DecodeError;

        // "zzzzzzzzzzzzz" (13 z's) = 35*(36^12 + ...) > u64::MAX
        let result = Base36Id::<16>::parse("zzzzzzzzzzzzz");
        assert_eq!(result, Err(DecodeError::Overflow));

        // u64::MAX should round-trip
        let max_id: Base36Id = Base36Id::encode(u64::MAX);
        let parsed = Base36Id::<16>::parse(max_id.as_str()).unwrap();
        assert_eq!(parsed.decode(), u64::MAX);
    }

    // ====================================================================
    // Uuid::parse negative cases
    // ====================================================================

    #[test]
    fn uuid_parse_wrong_length() {
        use crate::parse::UuidParseError;

        let result = Uuid::<40>::parse("01234567-89ab-cdef-fedc-ba987654321"); // 35 chars
        assert!(matches!(result, Err(UuidParseError::InvalidLength { .. })));

        let result = Uuid::<40>::parse("01234567-89ab-cdef-fedc-ba98765432100"); // 37 chars
        assert!(matches!(result, Err(UuidParseError::InvalidLength { .. })));

        let result = Uuid::<40>::parse("");
        assert!(matches!(result, Err(UuidParseError::InvalidLength { .. })));
    }

    #[test]
    fn uuid_parse_bad_dashes() {
        use crate::parse::UuidParseError;

        // Missing dash at position 8
        let result = Uuid::<40>::parse("01234567089ab-cdef-fedc-ba9876543210");
        assert!(matches!(result, Err(UuidParseError::InvalidFormat)));

        // Missing dash at position 13
        let result = Uuid::<40>::parse("01234567-89ab0cdef-fedc-ba9876543210");
        assert!(matches!(result, Err(UuidParseError::InvalidFormat)));

        // Missing dash at position 18
        let result = Uuid::<40>::parse("01234567-89ab-cdef0fedc-ba9876543210");
        assert!(matches!(result, Err(UuidParseError::InvalidFormat)));

        // Missing dash at position 23
        let result = Uuid::<40>::parse("01234567-89ab-cdef-fedc0ba9876543210");
        assert!(matches!(result, Err(UuidParseError::InvalidFormat)));
    }

    #[test]
    fn uuid_parse_invalid_hex_char() {
        use crate::parse::UuidParseError;

        // 'g' is not a valid hex character
        let result = Uuid::<40>::parse("g1234567-89ab-cdef-fedc-ba9876543210");
        assert!(matches!(
            result,
            Err(UuidParseError::InvalidChar { position: 0, .. })
        ));

        // Invalid in the middle segment
        let result = Uuid::<40>::parse("01234567-89xb-cdef-fedc-ba9876543210");
        assert!(matches!(
            result,
            Err(UuidParseError::InvalidChar { position: 11, .. })
        ));
    }

    // ====================================================================
    // is_nil() tests
    // ====================================================================

    #[test]
    fn uuid_is_nil() {
        let nil: Uuid = Uuid::from_raw(0, 0);
        assert!(nil.is_nil());

        let not_nil: Uuid = Uuid::from_raw(0, 1);
        assert!(!not_nil.is_nil());

        let not_nil: Uuid = Uuid::from_raw(1, 0);
        assert!(!not_nil.is_nil());
    }

    #[test]
    fn uuid_compact_is_nil() {
        let nil: UuidCompact = UuidCompact::from_raw(0, 0);
        assert!(nil.is_nil());

        let not_nil: UuidCompact = UuidCompact::from_raw(0, 1);
        assert!(!not_nil.is_nil());
    }

    #[test]
    fn ulid_is_nil() {
        let nil: Ulid = Ulid::from_raw(0, 0, 0);
        assert!(nil.is_nil());

        // Non-zero timestamp
        let not_nil: Ulid = Ulid::from_raw(1, 0, 0);
        assert!(!not_nil.is_nil());

        // Non-zero rand_hi
        let not_nil: Ulid = Ulid::from_raw(0, 1, 0);
        assert!(!not_nil.is_nil());

        // Non-zero rand_lo
        let not_nil: Ulid = Ulid::from_raw(0, 0, 1);
        assert!(!not_nil.is_nil());
    }

    // ====================================================================
    // Crockford Base32 alias handling
    // ====================================================================

    #[test]
    fn ulid_parse_crockford_aliases() {
        // Crockford spec: I/i/L/l → 1, O/o → 0
        // "01" prefix with aliases should parse the same as canonical "01"
        let canonical: Ulid = Ulid::parse("01000000000000000000000000").unwrap();

        // 'O' → 0 (alias for zero)
        let with_o: Ulid = Ulid::parse("O1000000000000000000000000").unwrap();
        assert_eq!(canonical, with_o);

        // 'I' → 1
        let with_i: Ulid = Ulid::parse("0I000000000000000000000000").unwrap();
        assert_eq!(canonical, with_i);

        // 'L' → 1
        let with_l: Ulid = Ulid::parse("0L000000000000000000000000").unwrap();
        assert_eq!(canonical, with_l);

        // 'i' → 1 (lowercase)
        let with_i_lower: Ulid = Ulid::parse("0i000000000000000000000000").unwrap();
        assert_eq!(canonical, with_i_lower);

        // 'o' → 0 (lowercase)
        let with_o_lower: Ulid = Ulid::parse("o1000000000000000000000000").unwrap();
        assert_eq!(canonical, with_o_lower);

        // 'l' → 1 (lowercase)
        let with_l_lower: Ulid = Ulid::parse("0l000000000000000000000000").unwrap();
        assert_eq!(canonical, with_l_lower);
    }

    // ====================================================================
    // Ulid::to_uuid() lossy conversion
    // ====================================================================

    #[test]
    fn ulid_to_uuid_preserves_timestamp() {
        let ts = 1_700_000_000_000u64;
        let ulid: Ulid = Ulid::from_raw(ts, 0x1234, 0xDEAD_BEEF_CAFE_BABE);
        let uuid = ulid.to_uuid();

        // Version should be 7
        assert_eq!(uuid.version(), 7);

        // Timestamp should survive the conversion (top 48 bits of hi)
        let (hi, _) = uuid.decode();
        let extracted_ts = hi >> 16;
        assert_eq!(extracted_ts, ts);
    }

    #[test]
    fn ulid_to_uuid_is_lossy() {
        // Two ULIDs that differ only in the bottom 6 bits of rand_lo
        // should map to the same UUID (those bits are discarded).
        let ulid_a: Ulid = Ulid::from_raw(1_700_000_000_000, 0x1234, 0xDEAD_BEEF_CAFE_BA00);
        let ulid_b: Ulid = Ulid::from_raw(1_700_000_000_000, 0x1234, 0xDEAD_BEEF_CAFE_BA3F);

        // Different ULIDs
        assert_ne!(ulid_a, ulid_b);

        // Same UUID (bottom 6 bits lost)
        assert_eq!(ulid_a.to_uuid(), ulid_b.to_uuid());
    }

    #[test]
    fn ulid_to_uuid_sets_variant_bits() {
        let ulid: Ulid = Ulid::from_raw(1_700_000_000_000, 0xFFFF, u64::MAX);
        let uuid = ulid.to_uuid();
        let (_, lo) = uuid.decode();

        // Top 2 bits of lo must be 0b10 (RFC variant)
        assert_eq!(lo >> 62, 0b10);
    }
}
