//! TypeID: Type-prefixed sortable identifiers.
//!
//! A TypeID combines a lowercase ASCII prefix with a 26-character Crockford
//! Base32 suffix (compatible with ULID encoding). This provides domain-level
//! type safety at the string layer.
//!
//! Format: `{prefix}_{suffix}` (e.g., `user_01ARZ3NDEKTSV4RRFFQ69G5FAV`)
//!
//! # Type Parameter
//!
//! `CAP` is the total string capacity (prefix + `_` + 26 suffix).
//! Must be a multiple of 8 (AsciiString alignment requirement).
//! Choose based on your longest prefix:
//! - `TypeId<32>`: prefixes up to 5 chars
//! - `TypeId<40>`: prefixes up to 13 chars
//! - `TypeId<48>`: prefixes up to 21 chars

use core::fmt;
use core::hash::{Hash, Hasher};
use core::ops::Deref;
use core::str::FromStr;

use nexus_ascii::AsciiString;

use crate::parse::{CROCKFORD32_DECODE, TypeIdParseError};
use crate::types::Ulid;

/// Type-prefixed sortable identifier.
///
/// Stores the full string representation (`prefix_suffix`) in a fixed-capacity
/// `AsciiString<CAP>`. The suffix is a 26-character Crockford Base32 value
/// (ULID-compatible).
///
/// # Example
///
/// ```rust
/// use nexus_id::{TypeId, Ulid};
/// use nexus_id::ulid::UlidGenerator;
/// use std::time::{Instant, SystemTime, UNIX_EPOCH};
///
/// let epoch = Instant::now();
/// let unix_base = SystemTime::now()
///     .duration_since(UNIX_EPOCH)
///     .unwrap()
///     .as_millis() as u64;
/// let mut generator = UlidGenerator::new(epoch, unix_base, 42);
///
/// let ulid = generator.next(Instant::now()).unwrap();
/// let id: TypeId<32> = TypeId::new("user", ulid).unwrap();
/// assert!(id.as_str().starts_with("user_"));
/// assert_eq!(id.prefix(), "user");
/// ```
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct TypeId<const CAP: usize = 32> {
    inner: AsciiString<CAP>,
    prefix_len: u8,
}

impl<const CAP: usize> TypeId<CAP> {
    /// Minimum capacity: `_` + 26 suffix = 27 bytes (empty prefix allowed).
    const MIN_SUFFIX_LEN: usize = 27; // '_' + 26

    /// Create a new TypeId from a prefix and ULID suffix.
    ///
    /// # Errors
    ///
    /// Returns [`TypeIdParseError`] if:
    /// - Prefix contains non-lowercase-ASCII characters
    /// - Prefix + separator + suffix exceeds `CAP`
    /// - Prefix is empty (use ULID directly instead)
    pub fn new(prefix: &str, suffix: Ulid) -> Result<Self, TypeIdParseError> {
        let prefix_bytes = prefix.as_bytes();
        let total_len = prefix_bytes.len() + 1 + 26; // prefix + '_' + suffix

        if prefix_bytes.is_empty() {
            return Err(TypeIdParseError::InvalidPrefix);
        }

        if total_len > CAP {
            return Err(TypeIdParseError::InvalidLength {
                expected: CAP,
                got: total_len,
            });
        }

        // Validate prefix: lowercase ASCII only [a-z]
        for (i, &b) in prefix_bytes.iter().enumerate() {
            if !b.is_ascii_lowercase() {
                return Err(TypeIdParseError::InvalidChar {
                    position: i,
                    byte: b,
                });
            }
        }

        // Build the combined string
        let mut buf = [0u8; CAP];
        buf[..prefix_bytes.len()].copy_from_slice(prefix_bytes);
        buf[prefix_bytes.len()] = b'_';
        buf[prefix_bytes.len() + 1..total_len].copy_from_slice(suffix.as_bytes());

        // SAFETY: prefix is lowercase ASCII, separator is '_', suffix is Crockford base32
        let inner = unsafe { AsciiString::from_bytes_unchecked(&buf[..total_len]) };

        Ok(Self {
            inner,
            prefix_len: prefix_bytes.len() as u8,
        })
    }

    /// Parse a TypeId from a string.
    ///
    /// Expects format: `{prefix}_{suffix}` where prefix is lowercase ASCII
    /// and suffix is 26 Crockford Base32 characters.
    pub fn parse(s: &str) -> Result<Self, TypeIdParseError> {
        let bytes = s.as_bytes();

        if bytes.len() > CAP {
            return Err(TypeIdParseError::InvalidLength {
                expected: CAP,
                got: bytes.len(),
            });
        }

        if bytes.len() < Self::MIN_SUFFIX_LEN {
            return Err(TypeIdParseError::InvalidFormat);
        }

        // Find the underscore separator (must be at len - 27)
        let sep_pos = bytes.len() - 27;
        if bytes[sep_pos] != b'_' {
            return Err(TypeIdParseError::InvalidFormat);
        }

        let prefix_bytes = &bytes[..sep_pos];
        let suffix_bytes = &bytes[sep_pos + 1..];

        // Validate prefix
        if prefix_bytes.is_empty() {
            return Err(TypeIdParseError::InvalidPrefix);
        }
        for (i, &b) in prefix_bytes.iter().enumerate() {
            if !b.is_ascii_lowercase() {
                return Err(TypeIdParseError::InvalidChar {
                    position: i,
                    byte: b,
                });
            }
        }

        // Validate suffix (26 Crockford base32 chars)
        if suffix_bytes.len() != 26 {
            return Err(TypeIdParseError::InvalidFormat);
        }
        let suffix_str =
            core::str::from_utf8(suffix_bytes).map_err(|_| TypeIdParseError::InvalidFormat)?;
        let _: Ulid = Ulid::parse(suffix_str)?;

        // Build from validated input
        // SAFETY: all bytes validated as ASCII
        let inner = unsafe { AsciiString::from_bytes_unchecked(bytes) };

        Ok(Self {
            inner,
            prefix_len: prefix_bytes.len() as u8,
        })
    }

    /// The prefix portion (without underscore or suffix).
    #[inline]
    pub fn prefix(&self) -> &str {
        &self.inner.as_str()[..self.prefix_len as usize]
    }

    /// The suffix portion (26-char Crockford Base32).
    #[inline]
    pub fn suffix_str(&self) -> &str {
        &self.inner.as_str()[self.prefix_len as usize + 1..]
    }

    /// Extract the ULID suffix.
    ///
    /// Constructs the `Ulid` directly from the validated suffix bytes
    /// without re-parsing.
    #[inline]
    pub fn suffix(&self) -> Ulid {
        let suffix_bytes = self.suffix_str().as_bytes();
        // SAFETY: suffix was validated as 26-char Crockford Base32 at construction.
        let inner = unsafe { AsciiString::from_bytes_unchecked(suffix_bytes) };
        Ulid(inner)
    }

    /// The full string representation.
    #[inline]
    pub fn as_str(&self) -> &str {
        self.inner.as_str()
    }

    /// The full string as bytes.
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        self.inner.as_bytes()
    }

    /// Extract the timestamp from the ULID suffix.
    ///
    /// Decodes the first 10 Crockford Base32 characters directly without
    /// constructing an intermediate `Ulid`.
    #[inline]
    pub fn timestamp_millis(&self) -> u64 {
        let bytes = self.suffix_str().as_bytes();
        let mut ts: u64 = CROCKFORD32_DECODE[bytes[0] as usize] as u64;
        let mut i = 1;
        while i < 10 {
            ts = (ts << 5) | CROCKFORD32_DECODE[bytes[i] as usize] as u64;
            i += 1;
        }
        ts
    }
}

impl<const CAP: usize> Deref for TypeId<CAP> {
    type Target = str;

    #[inline]
    fn deref(&self) -> &str {
        self.inner.as_str()
    }
}

impl<const CAP: usize> AsRef<str> for TypeId<CAP> {
    #[inline]
    fn as_ref(&self) -> &str {
        self.inner.as_str()
    }
}

impl<const CAP: usize> Hash for TypeId<CAP> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.inner.hash(state);
    }
}

impl<const CAP: usize> Ord for TypeId<CAP> {
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.inner.cmp(&other.inner)
    }
}

impl<const CAP: usize> PartialOrd for TypeId<CAP> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<const CAP: usize> fmt::Display for TypeId<CAP> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.inner.as_str())
    }
}

impl<const CAP: usize> fmt::Debug for TypeId<CAP> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TypeId({})", self.inner.as_str())
    }
}

impl<const CAP: usize> FromStr for TypeId<CAP> {
    type Err = TypeIdParseError;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
    }
}

#[cfg(all(test, feature = "std"))]
mod tests {
    use super::*;
    use crate::ulid::UlidGenerator;
    use std::time::{Instant, SystemTime, UNIX_EPOCH};

    fn test_ulid() -> Ulid {
        let epoch = Instant::now();
        let unix_base = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_millis() as u64;
        let mut generator = UlidGenerator::new(epoch, unix_base, 42);
        generator.next(epoch).unwrap()
    }

    #[test]
    fn basic_construction() {
        let ulid = test_ulid();
        let id: TypeId<32> = TypeId::new("user", ulid).unwrap();

        assert!(id.as_str().starts_with("user_"));
        assert_eq!(id.prefix(), "user");
        assert_eq!(id.suffix_str(), ulid.as_str());
    }

    #[test]
    fn parse_roundtrip() {
        let ulid = test_ulid();
        let id: TypeId<40> = TypeId::new("order", ulid).unwrap();
        let s = id.as_str().to_string();

        let parsed: TypeId<40> = TypeId::parse(&s).unwrap();
        assert_eq!(id, parsed);
    }

    #[test]
    fn invalid_prefix_uppercase() {
        let ulid = test_ulid();
        let result: Result<TypeId<32>, _> = TypeId::new("User", ulid);
        assert!(result.is_err());
    }

    #[test]
    fn invalid_prefix_empty() {
        let ulid = test_ulid();
        let result: Result<TypeId<32>, _> = TypeId::new("", ulid);
        assert!(result.is_err());
    }

    #[test]
    fn capacity_overflow() {
        let ulid = test_ulid();
        // "longprefix" (10) + "_" (1) + 26 = 37, exceeds capacity 32
        let result: Result<TypeId<32>, _> = TypeId::new("longprefix", ulid);
        assert!(result.is_err());
    }

    #[test]
    fn ordering_works() {
        let epoch = Instant::now();
        let unix_base = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_millis() as u64;
        let mut generator = UlidGenerator::new(epoch, unix_base, 42);

        let ulid1 = generator.next(epoch).unwrap();
        let ulid2 = generator.next(epoch).unwrap();

        let id1: TypeId<32> = TypeId::new("user", ulid1).unwrap();
        let id2: TypeId<32> = TypeId::new("user", ulid2).unwrap();

        // Same prefix, different suffix → ordered by suffix (time-ordered)
        assert!(id1 < id2);
    }

    #[test]
    fn timestamp_extraction() {
        let ulid = test_ulid();
        let id: TypeId<32> = TypeId::new("user", ulid).unwrap();

        assert_eq!(id.timestamp_millis(), ulid.timestamp_millis());
    }

    #[test]
    fn fromstr_works() {
        let ulid = test_ulid();
        let id: TypeId<40> = TypeId::new("order", ulid).unwrap();
        let s = id.as_str().to_string();

        let parsed: TypeId<40> = s.parse().unwrap();
        assert_eq!(id, parsed);
    }
}
