//! Single ASCII character type.
//!
//! Provides a validated, zero-cost wrapper around `u8` for ASCII characters.

use core::fmt;

// =============================================================================
// Error Type
// =============================================================================

/// Error when creating an `AsciiChar` from an invalid value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InvalidAsciiChar {
    /// The invalid value (> 127).
    pub value: u32,
}

impl fmt::Display for InvalidAsciiChar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.value <= 255 {
            write!(f, "invalid ASCII: 0x{:02X} ({})", self.value, self.value)
        } else {
            write!(f, "invalid ASCII: U+{:04X} ({})", self.value, self.value)
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for InvalidAsciiChar {}

// =============================================================================
// AsciiChar
// =============================================================================

/// A single ASCII character (0x00-0x7F).
///
/// Zero-cost wrapper around `u8` with validation. All methods are const.
/// Note: `AsciiChar::NULL` (0x00) is a valid character value, but null cannot
/// appear as content in string types where it is structural (terminator/padding).
///
/// # Example
///
/// ```
/// use nexus_ascii::AsciiChar;
///
/// let ch = AsciiChar::try_new(b'A').unwrap();
/// assert_eq!(ch.as_char(), 'A');
/// assert!(ch.is_uppercase());
///
/// // Use named constants
/// assert_eq!(AsciiChar::A, ch);
/// assert_eq!(AsciiChar::SOH.as_u8(), 0x01); // FIX delimiter
/// ```
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct AsciiChar(u8);

// =============================================================================
// Constants - Control Characters (0x00-0x1F)
// =============================================================================

#[allow(non_upper_case_globals)]
impl AsciiChar {
    /// NUL - Null (0x00)
    pub const NULL: Self = Self(0x00);
    /// SOH - Start of Heading (0x01) - FIX protocol delimiter
    pub const SOH: Self = Self(0x01);
    /// STX - Start of Text (0x02)
    pub const STX: Self = Self(0x02);
    /// ETX - End of Text (0x03)
    pub const ETX: Self = Self(0x03);
    /// EOT - End of Transmission (0x04)
    pub const EOT: Self = Self(0x04);
    /// ENQ - Enquiry (0x05)
    pub const ENQ: Self = Self(0x05);
    /// ACK - Acknowledge (0x06)
    pub const ACK: Self = Self(0x06);
    /// BEL - Bell (0x07)
    pub const BEL: Self = Self(0x07);
    /// BS - Backspace (0x08)
    pub const BACKSPACE: Self = Self(0x08);
    /// HT - Horizontal Tab (0x09)
    pub const TAB: Self = Self(0x09);
    /// LF - Line Feed (0x0A)
    pub const NEWLINE: Self = Self(0x0A);
    /// VT - Vertical Tab (0x0B)
    pub const VERTICAL_TAB: Self = Self(0x0B);
    /// FF - Form Feed (0x0C)
    pub const FORM_FEED: Self = Self(0x0C);
    /// CR - Carriage Return (0x0D)
    pub const CARRIAGE_RETURN: Self = Self(0x0D);
    /// SO - Shift Out (0x0E)
    pub const SHIFT_OUT: Self = Self(0x0E);
    /// SI - Shift In (0x0F)
    pub const SHIFT_IN: Self = Self(0x0F);
    /// DLE - Data Link Escape (0x10)
    pub const DLE: Self = Self(0x10);
    /// DC1 - Device Control 1 / XON (0x11)
    pub const DC1: Self = Self(0x11);
    /// DC2 - Device Control 2 (0x12)
    pub const DC2: Self = Self(0x12);
    /// DC3 - Device Control 3 / XOFF (0x13)
    pub const DC3: Self = Self(0x13);
    /// DC4 - Device Control 4 (0x14)
    pub const DC4: Self = Self(0x14);
    /// NAK - Negative Acknowledge (0x15)
    pub const NAK: Self = Self(0x15);
    /// SYN - Synchronous Idle (0x16)
    pub const SYN: Self = Self(0x16);
    /// ETB - End of Transmission Block (0x17)
    pub const ETB: Self = Self(0x17);
    /// CAN - Cancel (0x18)
    pub const CAN: Self = Self(0x18);
    /// EM - End of Medium (0x19)
    pub const EM: Self = Self(0x19);
    /// SUB - Substitute (0x1A)
    pub const SUB: Self = Self(0x1A);
    /// ESC - Escape (0x1B)
    pub const ESCAPE: Self = Self(0x1B);
    /// FS - File Separator (0x1C)
    pub const FS: Self = Self(0x1C);
    /// GS - Group Separator (0x1D)
    pub const GS: Self = Self(0x1D);
    /// RS - Record Separator (0x1E)
    pub const RS: Self = Self(0x1E);
    /// US - Unit Separator (0x1F)
    pub const US: Self = Self(0x1F);

    // =========================================================================
    // Constants - Printable Characters (0x20-0x7E)
    // =========================================================================

    /// Space (0x20)
    pub const SPACE: Self = Self(0x20);
    /// ! - Exclamation mark (0x21)
    pub const EXCLAMATION: Self = Self(0x21);
    /// " - Double quote (0x22)
    pub const DOUBLE_QUOTE: Self = Self(0x22);
    /// # - Hash / Number sign (0x23)
    pub const HASH: Self = Self(0x23);
    /// $ - Dollar sign (0x24)
    pub const DOLLAR: Self = Self(0x24);
    /// % - Percent sign (0x25)
    pub const PERCENT: Self = Self(0x25);
    /// & - Ampersand (0x26)
    pub const AMPERSAND: Self = Self(0x26);
    /// ' - Single quote / Apostrophe (0x27)
    pub const SINGLE_QUOTE: Self = Self(0x27);
    /// ( - Left parenthesis (0x28)
    pub const LEFT_PAREN: Self = Self(0x28);
    /// ) - Right parenthesis (0x29)
    pub const RIGHT_PAREN: Self = Self(0x29);
    /// * - Asterisk (0x2A)
    pub const ASTERISK: Self = Self(0x2A);
    /// + - Plus sign (0x2B)
    pub const PLUS: Self = Self(0x2B);
    /// , - Comma (0x2C)
    pub const COMMA: Self = Self(0x2C);
    /// - - Hyphen / Minus (0x2D)
    pub const MINUS: Self = Self(0x2D);
    /// . - Period / Full stop (0x2E)
    pub const PERIOD: Self = Self(0x2E);
    /// / - Slash / Solidus (0x2F)
    pub const SLASH: Self = Self(0x2F);

    // Digits (0x30-0x39)
    /// 0 (0x30)
    pub const DIGIT_0: Self = Self(0x30);
    /// 1 (0x31)
    pub const DIGIT_1: Self = Self(0x31);
    /// 2 (0x32)
    pub const DIGIT_2: Self = Self(0x32);
    /// 3 (0x33)
    pub const DIGIT_3: Self = Self(0x33);
    /// 4 (0x34)
    pub const DIGIT_4: Self = Self(0x34);
    /// 5 (0x35)
    pub const DIGIT_5: Self = Self(0x35);
    /// 6 (0x36)
    pub const DIGIT_6: Self = Self(0x36);
    /// 7 (0x37)
    pub const DIGIT_7: Self = Self(0x37);
    /// 8 (0x38)
    pub const DIGIT_8: Self = Self(0x38);
    /// 9 (0x39)
    pub const DIGIT_9: Self = Self(0x39);

    /// : - Colon (0x3A)
    pub const COLON: Self = Self(0x3A);
    /// ; - Semicolon (0x3B)
    pub const SEMICOLON: Self = Self(0x3B);
    /// < - Less than (0x3C)
    pub const LESS_THAN: Self = Self(0x3C);
    /// = - Equals sign (0x3D)
    pub const EQUALS: Self = Self(0x3D);
    /// > - Greater than (0x3E)
    pub const GREATER_THAN: Self = Self(0x3E);
    /// ? - Question mark (0x3F)
    pub const QUESTION: Self = Self(0x3F);
    /// @ - At sign (0x40)
    pub const AT: Self = Self(0x40);

    // Uppercase letters (0x41-0x5A)
    /// A (0x41)
    pub const A: Self = Self(0x41);
    /// B (0x42)
    pub const B: Self = Self(0x42);
    /// C (0x43)
    pub const C: Self = Self(0x43);
    /// D (0x44)
    pub const D: Self = Self(0x44);
    /// E (0x45)
    pub const E: Self = Self(0x45);
    /// F (0x46)
    pub const F: Self = Self(0x46);
    /// G (0x47)
    pub const G: Self = Self(0x47);
    /// H (0x48)
    pub const H: Self = Self(0x48);
    /// I (0x49)
    pub const I: Self = Self(0x49);
    /// J (0x4A)
    pub const J: Self = Self(0x4A);
    /// K (0x4B)
    pub const K: Self = Self(0x4B);
    /// L (0x4C)
    pub const L: Self = Self(0x4C);
    /// M (0x4D)
    pub const M: Self = Self(0x4D);
    /// N (0x4E)
    pub const N: Self = Self(0x4E);
    /// O (0x4F)
    pub const O: Self = Self(0x4F);
    /// P (0x50)
    pub const P: Self = Self(0x50);
    /// Q (0x51)
    pub const Q: Self = Self(0x51);
    /// R (0x52)
    pub const R: Self = Self(0x52);
    /// S (0x53)
    pub const S: Self = Self(0x53);
    /// T (0x54)
    pub const T: Self = Self(0x54);
    /// U (0x55)
    pub const U: Self = Self(0x55);
    /// V (0x56)
    pub const V: Self = Self(0x56);
    /// W (0x57)
    pub const W: Self = Self(0x57);
    /// X (0x58)
    pub const X: Self = Self(0x58);
    /// Y (0x59)
    pub const Y: Self = Self(0x59);
    /// Z (0x5A)
    pub const Z: Self = Self(0x5A);

    /// [ - Left bracket (0x5B)
    pub const LEFT_BRACKET: Self = Self(0x5B);
    /// \ - Backslash (0x5C)
    pub const BACKSLASH: Self = Self(0x5C);
    /// ] - Right bracket (0x5D)
    pub const RIGHT_BRACKET: Self = Self(0x5D);
    /// ^ - Caret (0x5E)
    pub const CARET: Self = Self(0x5E);
    /// _ - Underscore (0x5F)
    pub const UNDERSCORE: Self = Self(0x5F);
    /// Backtick / Grave accent (0x60)
    pub const BACKTICK: Self = Self(0x60);

    // Lowercase letters (0x61-0x7A)
    /// a (0x61)
    pub const a: Self = Self(0x61);
    /// b (0x62)
    pub const b: Self = Self(0x62);
    /// c (0x63)
    pub const c: Self = Self(0x63);
    /// d (0x64)
    pub const d: Self = Self(0x64);
    /// e (0x65)
    pub const e: Self = Self(0x65);
    /// f (0x66)
    pub const f: Self = Self(0x66);
    /// g (0x67)
    pub const g: Self = Self(0x67);
    /// h (0x68)
    pub const h: Self = Self(0x68);
    /// i (0x69)
    pub const i: Self = Self(0x69);
    /// j (0x6A)
    pub const j: Self = Self(0x6A);
    /// k (0x6B)
    pub const k: Self = Self(0x6B);
    /// l (0x6C)
    pub const l: Self = Self(0x6C);
    /// m (0x6D)
    pub const m: Self = Self(0x6D);
    /// n (0x6E)
    pub const n: Self = Self(0x6E);
    /// o (0x6F)
    pub const o: Self = Self(0x6F);
    /// p (0x70)
    pub const p: Self = Self(0x70);
    /// q (0x71)
    pub const q: Self = Self(0x71);
    /// r (0x72)
    pub const r: Self = Self(0x72);
    /// s (0x73)
    pub const s: Self = Self(0x73);
    /// t (0x74)
    pub const t: Self = Self(0x74);
    /// u (0x75)
    pub const u: Self = Self(0x75);
    /// v (0x76)
    pub const v: Self = Self(0x76);
    /// w (0x77)
    pub const w: Self = Self(0x77);
    /// x (0x78)
    pub const x: Self = Self(0x78);
    /// y (0x79)
    pub const y: Self = Self(0x79);
    /// z (0x7A)
    pub const z: Self = Self(0x7A);

    /// { - Left brace (0x7B)
    pub const LEFT_BRACE: Self = Self(0x7B);
    /// | - Pipe / Vertical bar (0x7C)
    pub const PIPE: Self = Self(0x7C);
    /// } - Right brace (0x7D)
    pub const RIGHT_BRACE: Self = Self(0x7D);
    /// ~ - Tilde (0x7E)
    pub const TILDE: Self = Self(0x7E);
    /// DEL - Delete (0x7F)
    pub const DEL: Self = Self(0x7F);
}

// =============================================================================
// Constructors
// =============================================================================

impl AsciiChar {
    /// Try to create an `AsciiChar` from a byte.
    ///
    /// Returns `Err` if the byte is > 127.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiChar;
    ///
    /// assert!(AsciiChar::try_new(b'A').is_ok());
    /// assert!(AsciiChar::try_new(0x80).is_err());
    /// ```
    #[inline]
    pub const fn try_new(byte: u8) -> Result<Self, InvalidAsciiChar> {
        if byte > 127 {
            Err(InvalidAsciiChar { value: byte as u32 })
        } else {
            Ok(Self(byte))
        }
    }

    /// Create an `AsciiChar` from a byte without validation.
    ///
    /// # Safety
    ///
    /// The byte must be <= 127.
    #[inline]
    #[must_use]
    pub const unsafe fn new_unchecked(byte: u8) -> Self {
        debug_assert!(byte <= 127);
        Self(byte)
    }

    /// Try to create an `AsciiChar` from a `char`.
    ///
    /// Returns `Err` if the char is not ASCII (> 127).
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiChar;
    ///
    /// assert!(AsciiChar::from_char('A').is_ok());
    /// assert!(AsciiChar::from_char('é').is_err());
    /// ```
    #[inline]
    #[allow(clippy::cast_possible_truncation)] // value is validated <= 127
    pub const fn from_char(c: char) -> Result<Self, InvalidAsciiChar> {
        let value = c as u32;
        if value > 127 {
            Err(InvalidAsciiChar { value })
        } else {
            Ok(Self(value as u8))
        }
    }
}

// =============================================================================
// Accessors
// =============================================================================

impl AsciiChar {
    /// Returns the byte value of this character.
    #[inline]
    #[must_use]
    pub const fn as_u8(self) -> u8 {
        self.0
    }

    /// Returns this character as a `char`.
    #[inline]
    #[must_use]
    pub const fn as_char(self) -> char {
        self.0 as char
    }
}

// =============================================================================
// Classification
// =============================================================================

impl AsciiChar {
    /// Returns `true` if this is an alphabetic character ('A'-'Z' or 'a'-'z').
    #[inline]
    #[must_use]
    pub const fn is_alphabetic(self) -> bool {
        self.is_uppercase() || self.is_lowercase()
    }

    /// Returns `true` if this is an uppercase letter ('A'-'Z').
    #[inline]
    #[must_use]
    pub const fn is_uppercase(self) -> bool {
        self.0 >= b'A' && self.0 <= b'Z'
    }

    /// Returns `true` if this is a lowercase letter ('a'-'z').
    #[inline]
    #[must_use]
    pub const fn is_lowercase(self) -> bool {
        self.0 >= b'a' && self.0 <= b'z'
    }

    /// Returns `true` if this is a digit ('0'-'9').
    #[inline]
    #[must_use]
    pub const fn is_digit(self) -> bool {
        self.0 >= b'0' && self.0 <= b'9'
    }

    /// Returns `true` if this is alphanumeric (alphabetic or digit).
    #[inline]
    #[must_use]
    pub const fn is_alphanumeric(self) -> bool {
        self.is_alphabetic() || self.is_digit()
    }

    /// Returns `true` if this is ASCII whitespace.
    ///
    /// Whitespace characters: space (0x20), tab (0x09), newline (0x0A),
    /// carriage return (0x0D), vertical tab (0x0B), form feed (0x0C).
    #[inline]
    #[must_use]
    pub const fn is_whitespace(self) -> bool {
        matches!(self.0, b' ' | b'\t' | b'\n' | b'\r' | 0x0B | 0x0C)
    }

    /// Returns `true` if this is a printable character (0x20-0x7E).
    ///
    /// Printable characters are space through tilde.
    #[inline]
    #[must_use]
    pub const fn is_printable(self) -> bool {
        self.0 >= 0x20 && self.0 <= 0x7E
    }

    /// Returns `true` if this is a control character (0x00-0x1F or 0x7F).
    #[inline]
    #[must_use]
    pub const fn is_control(self) -> bool {
        self.0 < 0x20 || self.0 == 0x7F
    }

    /// Returns `true` if this is a hexadecimal digit ('0'-'9', 'A'-'F', 'a'-'f').
    #[inline]
    #[must_use]
    pub const fn is_hex_digit(self) -> bool {
        self.is_digit() || (self.0 >= b'A' && self.0 <= b'F') || (self.0 >= b'a' && self.0 <= b'f')
    }
}

// =============================================================================
// Transformations
// =============================================================================

impl AsciiChar {
    /// Converts this character to uppercase.
    ///
    /// Non-alphabetic characters are returned unchanged.
    #[inline]
    #[must_use]
    pub const fn to_uppercase(self) -> Self {
        if self.is_lowercase() {
            Self(self.0 - 32)
        } else {
            self
        }
    }

    /// Converts this character to lowercase.
    ///
    /// Non-alphabetic characters are returned unchanged.
    #[inline]
    #[must_use]
    pub const fn to_lowercase(self) -> Self {
        if self.is_uppercase() {
            Self(self.0 + 32)
        } else {
            self
        }
    }

    /// Compares two characters for equality, ignoring case.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiChar;
    ///
    /// assert!(AsciiChar::A.eq_ignore_case(AsciiChar::a));
    /// assert!(AsciiChar::DIGIT_1.eq_ignore_case(AsciiChar::DIGIT_1));
    /// assert!(!AsciiChar::A.eq_ignore_case(AsciiChar::B));
    /// ```
    #[inline]
    #[must_use]
    pub const fn eq_ignore_case(self, other: Self) -> bool {
        self.to_lowercase().0 == other.to_lowercase().0
    }
}

// =============================================================================
// Trait Implementations
// =============================================================================

impl Default for AsciiChar {
    /// Returns `AsciiChar::NULL` (0x00).
    #[inline]
    fn default() -> Self {
        Self::NULL
    }
}

impl fmt::Debug for AsciiChar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_printable() {
            write!(f, "AsciiChar('{}')", self.0 as char)
        } else {
            write!(f, "AsciiChar(0x{:02X})", self.0)
        }
    }
}

impl fmt::Display for AsciiChar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0 as char)
    }
}

impl From<AsciiChar> for u8 {
    #[inline]
    fn from(c: AsciiChar) -> Self {
        c.0
    }
}

impl From<AsciiChar> for char {
    #[inline]
    fn from(c: AsciiChar) -> Self {
        c.0 as char
    }
}

impl TryFrom<u8> for AsciiChar {
    type Error = InvalidAsciiChar;

    #[inline]
    fn try_from(byte: u8) -> Result<Self, Self::Error> {
        Self::try_new(byte)
    }
}

impl TryFrom<char> for AsciiChar {
    type Error = InvalidAsciiChar;

    #[inline]
    fn try_from(c: char) -> Result<Self, Self::Error> {
        Self::from_char(c)
    }
}

// =============================================================================
// Serde Support (feature-gated)
// =============================================================================

#[cfg(feature = "serde")]
impl serde::Serialize for AsciiChar {
    /// Serializes the ASCII character as a single-character string.
    #[inline]
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_char(self.as_char())
    }
}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for AsciiChar {
    /// Deserializes a character into an ASCII character.
    ///
    /// Returns an error if the character is not ASCII (> 127).
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct AsciiCharVisitor;

        impl serde::de::Visitor<'_> for AsciiCharVisitor {
            type Value = AsciiChar;

            fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                formatter.write_str("an ASCII character")
            }

            #[inline]
            fn visit_char<E: serde::de::Error>(self, v: char) -> Result<Self::Value, E> {
                AsciiChar::from_char(v)
                    .map_err(|_| E::custom(format_args!("character '{}' is not ASCII", v)))
            }

            #[inline]
            fn visit_str<E: serde::de::Error>(self, v: &str) -> Result<Self::Value, E> {
                let mut chars = v.chars();
                match (chars.next(), chars.next()) {
                    (Some(c), None) => self.visit_char(c),
                    _ => Err(E::custom("expected a single ASCII character")),
                }
            }

            #[inline]
            fn visit_u64<E: serde::de::Error>(self, v: u64) -> Result<Self::Value, E> {
                if v > 127 {
                    Err(E::custom(format_args!("byte value {} is not ASCII", v)))
                } else {
                    // SAFETY: We just verified v <= 127
                    Ok(unsafe { AsciiChar::new_unchecked(v as u8) })
                }
            }
        }

        deserializer.deserialize_char(AsciiCharVisitor)
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // =========================================================================
    // Constructor tests
    // =========================================================================

    #[test]
    fn try_new_valid() {
        for b in 0..=127 {
            assert!(AsciiChar::try_new(b).is_ok());
        }
    }

    #[test]
    fn try_new_invalid() {
        for b in 128..=255 {
            let err = AsciiChar::try_new(b).unwrap_err();
            assert_eq!(err.value, b as u32);
        }
    }

    #[test]
    fn from_char_valid() {
        for c in '\0'..='\x7F' {
            assert!(AsciiChar::from_char(c).is_ok());
        }
    }

    #[test]
    fn from_char_invalid() {
        assert!(AsciiChar::from_char('é').is_err());
        assert!(AsciiChar::from_char('中').is_err());

        let err = AsciiChar::from_char('中').unwrap_err();
        assert_eq!(err.value, '中' as u32);
    }

    #[test]
    fn new_unchecked_valid() {
        for b in 0..=127 {
            // SAFETY: b is in 0..=127, the valid ASCII range.
            let c = unsafe { AsciiChar::new_unchecked(b) };
            assert_eq!(c.as_u8(), b);
        }
    }

    // =========================================================================
    // Accessor tests
    // =========================================================================

    #[test]
    fn as_u8_roundtrip() {
        for b in 0..=127 {
            let c = AsciiChar::try_new(b).unwrap();
            assert_eq!(c.as_u8(), b);
        }
    }

    #[test]
    fn as_char_roundtrip() {
        for b in 0..=127u8 {
            let c = AsciiChar::try_new(b).unwrap();
            assert_eq!(c.as_char(), b as char);
        }
    }

    // =========================================================================
    // Classification tests
    // =========================================================================

    #[test]
    fn is_uppercase() {
        for b in b'A'..=b'Z' {
            assert!(AsciiChar::try_new(b).unwrap().is_uppercase());
        }
        assert!(!AsciiChar::a.is_uppercase());
        assert!(!AsciiChar::DIGIT_0.is_uppercase());
    }

    #[test]
    fn is_lowercase() {
        for b in b'a'..=b'z' {
            assert!(AsciiChar::try_new(b).unwrap().is_lowercase());
        }
        assert!(!AsciiChar::A.is_lowercase());
        assert!(!AsciiChar::DIGIT_0.is_lowercase());
    }

    #[test]
    fn is_alphabetic() {
        for b in b'A'..=b'Z' {
            assert!(AsciiChar::try_new(b).unwrap().is_alphabetic());
        }
        for b in b'a'..=b'z' {
            assert!(AsciiChar::try_new(b).unwrap().is_alphabetic());
        }
        assert!(!AsciiChar::DIGIT_0.is_alphabetic());
        assert!(!AsciiChar::SPACE.is_alphabetic());
    }

    #[test]
    fn is_digit() {
        for b in b'0'..=b'9' {
            assert!(AsciiChar::try_new(b).unwrap().is_digit());
        }
        assert!(!AsciiChar::A.is_digit());
        assert!(!AsciiChar::SPACE.is_digit());
    }

    #[test]
    fn is_alphanumeric() {
        assert!(AsciiChar::A.is_alphanumeric());
        assert!(AsciiChar::z.is_alphanumeric());
        assert!(AsciiChar::DIGIT_5.is_alphanumeric());
        assert!(!AsciiChar::SPACE.is_alphanumeric());
        assert!(!AsciiChar::MINUS.is_alphanumeric());
    }

    #[test]
    fn is_whitespace() {
        assert!(AsciiChar::SPACE.is_whitespace());
        assert!(AsciiChar::TAB.is_whitespace());
        assert!(AsciiChar::NEWLINE.is_whitespace());
        assert!(AsciiChar::CARRIAGE_RETURN.is_whitespace());
        assert!(AsciiChar::VERTICAL_TAB.is_whitespace());
        assert!(AsciiChar::FORM_FEED.is_whitespace());
        assert!(!AsciiChar::A.is_whitespace());
        assert!(!AsciiChar::NULL.is_whitespace());
    }

    #[test]
    fn is_printable() {
        // 0x20 (space) through 0x7E (tilde) are printable
        for b in 0x20..=0x7E {
            assert!(
                AsciiChar::try_new(b).unwrap().is_printable(),
                "0x{:02X} should be printable",
                b
            );
        }
        // Control characters are not printable
        for b in 0x00..0x20 {
            assert!(
                !AsciiChar::try_new(b).unwrap().is_printable(),
                "0x{:02X} should not be printable",
                b
            );
        }
        assert!(!AsciiChar::DEL.is_printable());
    }

    #[test]
    fn is_control() {
        // 0x00-0x1F and 0x7F are control characters
        for b in 0x00..0x20 {
            assert!(AsciiChar::try_new(b).unwrap().is_control());
        }
        assert!(AsciiChar::DEL.is_control());
        assert!(!AsciiChar::SPACE.is_control());
        assert!(!AsciiChar::A.is_control());
    }

    #[test]
    fn is_hex_digit() {
        for b in b'0'..=b'9' {
            assert!(AsciiChar::try_new(b).unwrap().is_hex_digit());
        }
        for b in b'A'..=b'F' {
            assert!(AsciiChar::try_new(b).unwrap().is_hex_digit());
        }
        for b in b'a'..=b'f' {
            assert!(AsciiChar::try_new(b).unwrap().is_hex_digit());
        }
        assert!(!AsciiChar::G.is_hex_digit());
        assert!(!AsciiChar::g.is_hex_digit());
        assert!(!AsciiChar::SPACE.is_hex_digit());
    }

    // =========================================================================
    // Transformation tests
    // =========================================================================

    #[test]
    fn to_uppercase() {
        for b in b'a'..=b'z' {
            let lower = AsciiChar::try_new(b).unwrap();
            let upper = lower.to_uppercase();
            assert_eq!(upper.as_u8(), b - 32);
        }
        // Non-letters unchanged
        assert_eq!(AsciiChar::DIGIT_5.to_uppercase(), AsciiChar::DIGIT_5);
        assert_eq!(AsciiChar::SPACE.to_uppercase(), AsciiChar::SPACE);
        assert_eq!(AsciiChar::A.to_uppercase(), AsciiChar::A);
    }

    #[test]
    fn to_lowercase() {
        for b in b'A'..=b'Z' {
            let upper = AsciiChar::try_new(b).unwrap();
            let lower = upper.to_lowercase();
            assert_eq!(lower.as_u8(), b + 32);
        }
        // Non-letters unchanged
        assert_eq!(AsciiChar::DIGIT_5.to_lowercase(), AsciiChar::DIGIT_5);
        assert_eq!(AsciiChar::SPACE.to_lowercase(), AsciiChar::SPACE);
        assert_eq!(AsciiChar::a.to_lowercase(), AsciiChar::a);
    }

    #[test]
    fn eq_ignore_case() {
        assert!(AsciiChar::A.eq_ignore_case(AsciiChar::a));
        assert!(AsciiChar::a.eq_ignore_case(AsciiChar::A));
        assert!(AsciiChar::Z.eq_ignore_case(AsciiChar::z));
        assert!(!AsciiChar::A.eq_ignore_case(AsciiChar::B));
        // Non-letters compare exactly
        assert!(AsciiChar::DIGIT_1.eq_ignore_case(AsciiChar::DIGIT_1));
        assert!(!AsciiChar::DIGIT_1.eq_ignore_case(AsciiChar::DIGIT_2));
    }

    // =========================================================================
    // Trait tests
    // =========================================================================

    #[test]
    fn default_is_null() {
        assert_eq!(AsciiChar::default(), AsciiChar::NULL);
    }

    #[test]
    fn debug_printable() {
        let s = format!("{:?}", AsciiChar::A);
        assert_eq!(s, "AsciiChar('A')");
    }

    #[test]
    fn debug_control() {
        let s = format!("{:?}", AsciiChar::NULL);
        assert_eq!(s, "AsciiChar(0x00)");
    }

    #[test]
    fn display() {
        assert_eq!(format!("{}", AsciiChar::A), "A");
        assert_eq!(format!("{}", AsciiChar::SPACE), " ");
    }

    #[test]
    fn from_traits() {
        let c = AsciiChar::A;
        let byte: u8 = c.into();
        let ch: char = c.into();
        assert_eq!(byte, b'A');
        assert_eq!(ch, 'A');
    }

    #[test]
    fn try_from_traits() {
        let c: AsciiChar = 65u8.try_into().unwrap();
        assert_eq!(c, AsciiChar::A);

        let c: AsciiChar = 'A'.try_into().unwrap();
        assert_eq!(c, AsciiChar::A);
    }

    #[test]
    fn ordering() {
        assert!(AsciiChar::A < AsciiChar::B);
        assert!(AsciiChar::a > AsciiChar::Z);
        assert!(AsciiChar::DIGIT_0 < AsciiChar::A);
    }

    #[test]
    fn hash_works() {
        use std::collections::HashSet;
        let mut set = HashSet::new();
        set.insert(AsciiChar::A);
        set.insert(AsciiChar::B);
        assert!(set.contains(&AsciiChar::A));
        assert!(!set.contains(&AsciiChar::C));
    }

    // =========================================================================
    // Constant tests
    // =========================================================================

    #[test]
    fn control_char_constants() {
        assert_eq!(AsciiChar::NULL.as_u8(), 0x00);
        assert_eq!(AsciiChar::SOH.as_u8(), 0x01);
        assert_eq!(AsciiChar::TAB.as_u8(), 0x09);
        assert_eq!(AsciiChar::NEWLINE.as_u8(), 0x0A);
        assert_eq!(AsciiChar::CARRIAGE_RETURN.as_u8(), 0x0D);
        assert_eq!(AsciiChar::ESCAPE.as_u8(), 0x1B);
        assert_eq!(AsciiChar::DEL.as_u8(), 0x7F);
    }

    #[test]
    fn printable_constants() {
        assert_eq!(AsciiChar::SPACE.as_u8(), 0x20);
        assert_eq!(AsciiChar::EXCLAMATION.as_u8(), b'!');
        assert_eq!(AsciiChar::AT.as_u8(), b'@');
        assert_eq!(AsciiChar::TILDE.as_u8(), b'~');
    }

    #[test]
    fn letter_constants() {
        assert_eq!(AsciiChar::A.as_u8(), b'A');
        assert_eq!(AsciiChar::Z.as_u8(), b'Z');
        assert_eq!(AsciiChar::a.as_u8(), b'a');
        assert_eq!(AsciiChar::z.as_u8(), b'z');
    }

    #[test]
    fn digit_constants() {
        assert_eq!(AsciiChar::DIGIT_0.as_u8(), b'0');
        assert_eq!(AsciiChar::DIGIT_9.as_u8(), b'9');
    }

    // =========================================================================
    // Error display tests
    // =========================================================================

    #[test]
    fn error_display_byte() {
        let err = InvalidAsciiChar { value: 0x80 };
        assert_eq!(format!("{}", err), "invalid ASCII: 0x80 (128)");
    }

    #[test]
    fn error_display_unicode() {
        let err = InvalidAsciiChar { value: 0x4E2D };
        assert_eq!(format!("{}", err), "invalid ASCII: U+4E2D (20013)");
    }
}
