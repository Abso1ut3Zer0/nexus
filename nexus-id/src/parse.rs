//! Error types for ID string parsing.
//!
//! Each error type contains only the variants reachable by the parse methods
//! that return it. Users never need unreachable match arms.
//!
//! | Error Type | Used By |
//! |---|---|
//! | [`ParseError`] | [`HexId64`], [`UuidCompact`], [`Ulid`] |
//! | [`UuidParseError`] | [`Uuid`] |
//! | [`DecodeError`] | [`Base62Id`], [`Base36Id`] |
//! | [`TypeIdParseError`] | [`TypeId`] |

use core::fmt;

// =============================================================================
// ParseError — InvalidLength + InvalidChar
// =============================================================================

/// Error parsing a fixed-format ID string.
///
/// Returned by [`HexId64`](crate::HexId64), [`UuidCompact`](crate::UuidCompact),
/// and [`Ulid`](crate::Ulid).
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ParseError {
    /// Input length doesn't match expected format length.
    InvalidLength {
        /// The length the format requires.
        expected: usize,
        /// The length of the input that was provided.
        got: usize,
    },
    /// Invalid character at the given position.
    InvalidChar {
        /// Byte index in the input where the invalid character was found.
        position: usize,
        /// The invalid byte value.
        byte: u8,
    },
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidLength { expected, got } => {
                write!(f, "invalid length: expected {}, got {}", expected, got)
            }
            Self::InvalidChar { position, byte } => {
                write!(
                    f,
                    "invalid character 0x{:02x} at position {}",
                    byte, position
                )
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ParseError {}

// =============================================================================
// UuidParseError — InvalidLength + InvalidChar + InvalidFormat
// =============================================================================

/// Error parsing a UUID string.
///
/// Returned by [`Uuid`](crate::Uuid).
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum UuidParseError {
    /// Input length doesn't match expected format length.
    InvalidLength {
        /// The length the format requires.
        expected: usize,
        /// The length of the input that was provided.
        got: usize,
    },
    /// Invalid character at the given position.
    InvalidChar {
        /// Byte index in the input where the invalid character was found.
        position: usize,
        /// The invalid byte value.
        byte: u8,
    },
    /// Structural format error (missing or misplaced dashes).
    InvalidFormat,
}

impl fmt::Display for UuidParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidLength { expected, got } => {
                write!(f, "invalid length: expected {}, got {}", expected, got)
            }
            Self::InvalidChar { position, byte } => {
                write!(
                    f,
                    "invalid character 0x{:02x} at position {}",
                    byte, position
                )
            }
            Self::InvalidFormat => write!(f, "invalid UUID format (expected dashes at 8-13-18-23)"),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for UuidParseError {}

impl From<ParseError> for UuidParseError {
    #[inline]
    fn from(e: ParseError) -> Self {
        match e {
            ParseError::InvalidLength { expected, got } => Self::InvalidLength { expected, got },
            ParseError::InvalidChar { position, byte } => Self::InvalidChar { position, byte },
        }
    }
}

// =============================================================================
// DecodeError — InvalidLength + InvalidChar + Overflow
// =============================================================================

/// Error parsing a base-N encoded ID string.
///
/// Returned by [`Base62Id`](crate::Base62Id) and [`Base36Id`](crate::Base36Id).
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum DecodeError {
    /// Input length doesn't match expected format length.
    InvalidLength {
        /// The length the format requires.
        expected: usize,
        /// The length of the input that was provided.
        got: usize,
    },
    /// Invalid character at the given position.
    InvalidChar {
        /// Byte index in the input where the invalid character was found.
        position: usize,
        /// The invalid byte value.
        byte: u8,
    },
    /// Value overflows the target integer type.
    Overflow,
}

impl fmt::Display for DecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidLength { expected, got } => {
                write!(f, "invalid length: expected {}, got {}", expected, got)
            }
            Self::InvalidChar { position, byte } => {
                write!(
                    f,
                    "invalid character 0x{:02x} at position {}",
                    byte, position
                )
            }
            Self::Overflow => write!(f, "value overflows target type"),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for DecodeError {}

impl From<ParseError> for DecodeError {
    #[inline]
    fn from(e: ParseError) -> Self {
        match e {
            ParseError::InvalidLength { expected, got } => Self::InvalidLength { expected, got },
            ParseError::InvalidChar { position, byte } => Self::InvalidChar { position, byte },
        }
    }
}

// =============================================================================
// TypeIdParseError — InvalidLength + InvalidChar + InvalidFormat + InvalidPrefix
// =============================================================================

/// Error parsing or constructing a TypeId.
///
/// Returned by [`TypeId`](crate::TypeId).
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum TypeIdParseError {
    /// Input length doesn't match expected capacity or format.
    InvalidLength {
        /// The length the format requires.
        expected: usize,
        /// The length of the input that was provided.
        got: usize,
    },
    /// Invalid character at the given position.
    InvalidChar {
        /// Byte index in the input where the invalid character was found.
        position: usize,
        /// The invalid byte value.
        byte: u8,
    },
    /// Structural format error (missing underscore separator).
    InvalidFormat,
    /// Prefix is empty or contains non-lowercase-ASCII characters.
    InvalidPrefix,
}

impl fmt::Display for TypeIdParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidLength { expected, got } => {
                write!(f, "invalid length: expected max {}, got {}", expected, got)
            }
            Self::InvalidChar { position, byte } => {
                write!(
                    f,
                    "invalid character 0x{:02x} at position {}",
                    byte, position
                )
            }
            Self::InvalidFormat => {
                write!(f, "invalid TypeId format (expected prefix_suffix)")
            }
            Self::InvalidPrefix => {
                write!(f, "invalid prefix: must be non-empty lowercase ASCII [a-z]")
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for TypeIdParseError {}

impl From<ParseError> for TypeIdParseError {
    #[inline]
    fn from(e: ParseError) -> Self {
        match e {
            ParseError::InvalidLength { expected, got } => Self::InvalidLength { expected, got },
            ParseError::InvalidChar { position, byte } => Self::InvalidChar { position, byte },
        }
    }
}

// =============================================================================
// Validation helpers
// =============================================================================

/// Validate and decode a hex character, returning value or error.
#[allow(dead_code)] // Utility available for future parse implementations
#[inline]
pub(crate) const fn validate_hex(b: u8, position: usize) -> Result<u8, ParseError> {
    match b {
        b'0'..=b'9' => Ok(b - b'0'),
        b'a'..=b'f' => Ok(b - b'a' + 10),
        b'A'..=b'F' => Ok(b - b'A' + 10),
        _ => Err(ParseError::InvalidChar { position, byte: b }),
    }
}

/// Sentinel value for invalid Crockford Base32 characters.
const CROCKFORD32_INVALID: u8 = 0xFF;

/// Lookup table: ASCII byte → Crockford Base32 value (0-31), or 0xFF if invalid.
/// 256 bytes = 4 cache lines. Stays warm after first use.
pub(crate) static CROCKFORD32_DECODE: [u8; 256] = {
    let mut table = [CROCKFORD32_INVALID; 256];

    // Digits 0-9
    table[b'0' as usize] = 0;
    table[b'1' as usize] = 1;
    table[b'2' as usize] = 2;
    table[b'3' as usize] = 3;
    table[b'4' as usize] = 4;
    table[b'5' as usize] = 5;
    table[b'6' as usize] = 6;
    table[b'7' as usize] = 7;
    table[b'8' as usize] = 8;
    table[b'9' as usize] = 9;

    // Letters (uppercase) — Crockford excludes I, L, O, U
    table[b'A' as usize] = 10;
    table[b'B' as usize] = 11;
    table[b'C' as usize] = 12;
    table[b'D' as usize] = 13;
    table[b'E' as usize] = 14;
    table[b'F' as usize] = 15;
    table[b'G' as usize] = 16;
    table[b'H' as usize] = 17;
    table[b'J' as usize] = 18;
    table[b'K' as usize] = 19;
    table[b'M' as usize] = 20;
    table[b'N' as usize] = 21;
    table[b'P' as usize] = 22;
    table[b'Q' as usize] = 23;
    table[b'R' as usize] = 24;
    table[b'S' as usize] = 25;
    table[b'T' as usize] = 26;
    table[b'V' as usize] = 27;
    table[b'W' as usize] = 28;
    table[b'X' as usize] = 29;
    table[b'Y' as usize] = 30;
    table[b'Z' as usize] = 31;

    // Letters (lowercase)
    table[b'a' as usize] = 10;
    table[b'b' as usize] = 11;
    table[b'c' as usize] = 12;
    table[b'd' as usize] = 13;
    table[b'e' as usize] = 14;
    table[b'f' as usize] = 15;
    table[b'g' as usize] = 16;
    table[b'h' as usize] = 17;
    table[b'j' as usize] = 18;
    table[b'k' as usize] = 19;
    table[b'm' as usize] = 20;
    table[b'n' as usize] = 21;
    table[b'p' as usize] = 22;
    table[b'q' as usize] = 23;
    table[b'r' as usize] = 24;
    table[b's' as usize] = 25;
    table[b't' as usize] = 26;
    table[b'v' as usize] = 27;
    table[b'w' as usize] = 28;
    table[b'x' as usize] = 29;
    table[b'y' as usize] = 30;
    table[b'z' as usize] = 31;

    // Crockford aliases
    table[b'O' as usize] = 0; // O → 0
    table[b'o' as usize] = 0;
    table[b'I' as usize] = 1; // I → 1
    table[b'i' as usize] = 1;
    table[b'L' as usize] = 1; // L → 1
    table[b'l' as usize] = 1;

    table
};

/// Validate and decode a Crockford Base32 character via lookup table.
#[inline]
pub(crate) fn validate_crockford32(b: u8, position: usize) -> Result<u8, ParseError> {
    let val = CROCKFORD32_DECODE[b as usize];
    if val == CROCKFORD32_INVALID {
        Err(ParseError::InvalidChar { position, byte: b })
    } else {
        Ok(val)
    }
}

/// Validate and decode a base62 character.
#[inline]
pub(crate) const fn validate_base62(b: u8, position: usize) -> Result<u8, ParseError> {
    match b {
        b'0'..=b'9' => Ok(b - b'0'),
        b'A'..=b'Z' => Ok(b - b'A' + 10),
        b'a'..=b'z' => Ok(b - b'a' + 36),
        _ => Err(ParseError::InvalidChar { position, byte: b }),
    }
}

/// Validate and decode a base36 character.
#[inline]
pub(crate) const fn validate_base36(b: u8, position: usize) -> Result<u8, ParseError> {
    match b {
        b'0'..=b'9' => Ok(b - b'0'),
        b'a'..=b'z' => Ok(b - b'a' + 10),
        b'A'..=b'Z' => Ok(b - b'A' + 10),
        _ => Err(ParseError::InvalidChar { position, byte: b }),
    }
}

#[cfg(all(test, feature = "std"))]
mod tests {
    use super::*;

    // ====================================================================
    // ParseError variants
    // ====================================================================

    #[test]
    fn parse_error_invalid_length() {
        let err = ParseError::InvalidLength {
            expected: 16,
            got: 10,
        };
        assert_eq!(
            err,
            ParseError::InvalidLength {
                expected: 16,
                got: 10
            }
        );
        assert_eq!(err.to_string(), "invalid length: expected 16, got 10");
    }

    #[test]
    fn parse_error_invalid_char() {
        let err = ParseError::InvalidChar {
            position: 3,
            byte: b'!',
        };
        assert_eq!(
            err,
            ParseError::InvalidChar {
                position: 3,
                byte: b'!'
            }
        );
        assert_eq!(err.to_string(), "invalid character 0x21 at position 3");
    }

    // ====================================================================
    // UuidParseError variants
    // ====================================================================

    #[test]
    fn uuid_parse_error_invalid_length() {
        let err = UuidParseError::InvalidLength {
            expected: 36,
            got: 35,
        };
        assert_eq!(err.to_string(), "invalid length: expected 36, got 35");
    }

    #[test]
    fn uuid_parse_error_invalid_char() {
        let err = UuidParseError::InvalidChar {
            position: 5,
            byte: b'z',
        };
        assert_eq!(err.to_string(), "invalid character 0x7a at position 5");
    }

    #[test]
    fn uuid_parse_error_invalid_format() {
        let err = UuidParseError::InvalidFormat;
        assert_eq!(
            err.to_string(),
            "invalid UUID format (expected dashes at 8-13-18-23)"
        );
    }

    // ====================================================================
    // DecodeError variants
    // ====================================================================

    #[test]
    fn decode_error_invalid_length() {
        let err = DecodeError::InvalidLength {
            expected: 11,
            got: 8,
        };
        assert_eq!(err.to_string(), "invalid length: expected 11, got 8");
    }

    #[test]
    fn decode_error_invalid_char() {
        let err = DecodeError::InvalidChar {
            position: 2,
            byte: b'#',
        };
        assert_eq!(err.to_string(), "invalid character 0x23 at position 2");
    }

    #[test]
    fn decode_error_overflow() {
        let err = DecodeError::Overflow;
        assert_eq!(err.to_string(), "value overflows target type");
    }

    // ====================================================================
    // TypeIdParseError variants
    // ====================================================================

    #[test]
    fn typeid_parse_error_invalid_length() {
        let err = TypeIdParseError::InvalidLength {
            expected: 32,
            got: 50,
        };
        assert_eq!(err.to_string(), "invalid length: expected max 32, got 50");
    }

    #[test]
    fn typeid_parse_error_invalid_char() {
        let err = TypeIdParseError::InvalidChar {
            position: 0,
            byte: b'A',
        };
        assert_eq!(err.to_string(), "invalid character 0x41 at position 0");
    }

    #[test]
    fn typeid_parse_error_invalid_format() {
        let err = TypeIdParseError::InvalidFormat;
        assert_eq!(
            err.to_string(),
            "invalid TypeId format (expected prefix_suffix)"
        );
    }

    #[test]
    fn typeid_parse_error_invalid_prefix() {
        let err = TypeIdParseError::InvalidPrefix;
        assert_eq!(
            err.to_string(),
            "invalid prefix: must be non-empty lowercase ASCII [a-z]"
        );
    }

    // ====================================================================
    // From conversions
    // ====================================================================

    #[test]
    fn parse_error_into_uuid_parse_error_length() {
        let parse_err = ParseError::InvalidLength {
            expected: 16,
            got: 10,
        };
        let uuid_err: UuidParseError = parse_err.into();
        assert_eq!(
            uuid_err,
            UuidParseError::InvalidLength {
                expected: 16,
                got: 10
            }
        );
    }

    #[test]
    fn parse_error_into_uuid_parse_error_char() {
        let parse_err = ParseError::InvalidChar {
            position: 7,
            byte: b'g',
        };
        let uuid_err: UuidParseError = parse_err.into();
        assert_eq!(
            uuid_err,
            UuidParseError::InvalidChar {
                position: 7,
                byte: b'g'
            }
        );
    }

    #[test]
    fn parse_error_into_decode_error_length() {
        let parse_err = ParseError::InvalidLength {
            expected: 11,
            got: 5,
        };
        let decode_err: DecodeError = parse_err.into();
        assert_eq!(
            decode_err,
            DecodeError::InvalidLength {
                expected: 11,
                got: 5
            }
        );
    }

    #[test]
    fn parse_error_into_decode_error_char() {
        let parse_err = ParseError::InvalidChar {
            position: 4,
            byte: b'@',
        };
        let decode_err: DecodeError = parse_err.into();
        assert_eq!(
            decode_err,
            DecodeError::InvalidChar {
                position: 4,
                byte: b'@'
            }
        );
    }

    #[test]
    fn parse_error_into_typeid_parse_error_length() {
        let parse_err = ParseError::InvalidLength {
            expected: 26,
            got: 20,
        };
        let typeid_err: TypeIdParseError = parse_err.into();
        assert_eq!(
            typeid_err,
            TypeIdParseError::InvalidLength {
                expected: 26,
                got: 20
            }
        );
    }

    #[test]
    fn parse_error_into_typeid_parse_error_char() {
        let parse_err = ParseError::InvalidChar {
            position: 12,
            byte: b'$',
        };
        let typeid_err: TypeIdParseError = parse_err.into();
        assert_eq!(
            typeid_err,
            TypeIdParseError::InvalidChar {
                position: 12,
                byte: b'$'
            }
        );
    }

    // ====================================================================
    // Validation helpers
    // ====================================================================

    #[test]
    fn validate_hex_valid_digits() {
        assert_eq!(validate_hex(b'0', 0), Ok(0));
        assert_eq!(validate_hex(b'9', 0), Ok(9));
        assert_eq!(validate_hex(b'a', 0), Ok(10));
        assert_eq!(validate_hex(b'f', 0), Ok(15));
        assert_eq!(validate_hex(b'A', 0), Ok(10));
        assert_eq!(validate_hex(b'F', 0), Ok(15));
    }

    #[test]
    fn validate_hex_invalid_char() {
        let err = validate_hex(b'g', 5).unwrap_err();
        assert_eq!(
            err,
            ParseError::InvalidChar {
                position: 5,
                byte: b'g'
            }
        );
    }

    #[test]
    fn validate_crockford32_valid_digits() {
        assert_eq!(validate_crockford32(b'0', 0), Ok(0));
        assert_eq!(validate_crockford32(b'9', 0), Ok(9));
        assert_eq!(validate_crockford32(b'A', 0), Ok(10));
        assert_eq!(validate_crockford32(b'Z', 0), Ok(31));
        assert_eq!(validate_crockford32(b'a', 0), Ok(10));
        assert_eq!(validate_crockford32(b'z', 0), Ok(31));
    }

    #[test]
    fn validate_crockford32_aliases() {
        // O/o -> 0, I/i -> 1, L/l -> 1
        assert_eq!(validate_crockford32(b'O', 0), Ok(0));
        assert_eq!(validate_crockford32(b'o', 0), Ok(0));
        assert_eq!(validate_crockford32(b'I', 0), Ok(1));
        assert_eq!(validate_crockford32(b'i', 0), Ok(1));
        assert_eq!(validate_crockford32(b'L', 0), Ok(1));
        assert_eq!(validate_crockford32(b'l', 0), Ok(1));
    }

    #[test]
    fn validate_crockford32_invalid_char() {
        // 'U' is excluded from Crockford Base32
        let err = validate_crockford32(b'U', 3).unwrap_err();
        assert_eq!(
            err,
            ParseError::InvalidChar {
                position: 3,
                byte: b'U'
            }
        );
    }

    #[test]
    fn validate_base62_valid_chars() {
        assert_eq!(validate_base62(b'0', 0), Ok(0));
        assert_eq!(validate_base62(b'9', 0), Ok(9));
        assert_eq!(validate_base62(b'A', 0), Ok(10));
        assert_eq!(validate_base62(b'Z', 0), Ok(35));
        assert_eq!(validate_base62(b'a', 0), Ok(36));
        assert_eq!(validate_base62(b'z', 0), Ok(61));
    }

    #[test]
    fn validate_base62_invalid_char() {
        let err = validate_base62(b'!', 7).unwrap_err();
        assert_eq!(
            err,
            ParseError::InvalidChar {
                position: 7,
                byte: b'!'
            }
        );
    }

    #[test]
    fn validate_base36_valid_chars() {
        assert_eq!(validate_base36(b'0', 0), Ok(0));
        assert_eq!(validate_base36(b'9', 0), Ok(9));
        assert_eq!(validate_base36(b'a', 0), Ok(10));
        assert_eq!(validate_base36(b'z', 0), Ok(35));
        // Case insensitive
        assert_eq!(validate_base36(b'A', 0), Ok(10));
        assert_eq!(validate_base36(b'Z', 0), Ok(35));
    }

    #[test]
    fn validate_base36_invalid_char() {
        let err = validate_base36(b'_', 9).unwrap_err();
        assert_eq!(
            err,
            ParseError::InvalidChar {
                position: 9,
                byte: b'_'
            }
        );
    }

    // ====================================================================
    // std::error::Error impls
    // ====================================================================

    #[test]
    fn parse_error_is_std_error() {
        let err: Box<dyn std::error::Error> = Box::new(ParseError::InvalidChar {
            position: 0,
            byte: b'x',
        });
        assert!(err.source().is_none());
    }

    #[test]
    fn uuid_parse_error_is_std_error() {
        let err: Box<dyn std::error::Error> = Box::new(UuidParseError::InvalidFormat);
        assert!(err.source().is_none());
    }

    #[test]
    fn decode_error_is_std_error() {
        let err: Box<dyn std::error::Error> = Box::new(DecodeError::Overflow);
        assert!(err.source().is_none());
    }

    // ====================================================================
    // Clone + Eq
    // ====================================================================

    #[test]
    fn error_types_clone_and_eq() {
        let a = ParseError::InvalidLength {
            expected: 16,
            got: 10,
        };
        let b = a.clone();
        assert_eq!(a, b);

        let a = UuidParseError::InvalidFormat;
        let b = a.clone();
        assert_eq!(a, b);

        let a = DecodeError::Overflow;
        let b = a.clone();
        assert_eq!(a, b);

        let a = TypeIdParseError::InvalidPrefix;
        let b = a.clone();
        assert_eq!(a, b);
    }
}
