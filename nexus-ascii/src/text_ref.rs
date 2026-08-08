//! Borrowed printable ASCII string slice type.
//!
//! `AsciiTextStr` is to `AsciiText` what `str` is to `String` — a borrowed,
//! dynamically-sized view into validated printable ASCII bytes.

use core::hash::{Hash, Hasher};

use crate::AsciiError;
use crate::char::AsciiChar;
use crate::hash;
use crate::simd;
use crate::str_ref::AsciiStr;

// =============================================================================
// AsciiTextStr
// =============================================================================

/// A borrowed slice of validated printable ASCII bytes.
///
/// `AsciiTextStr` is a dynamically-sized type (DST) that can only exist behind
/// a reference. It provides a zero-copy view into printable ASCII data (bytes
/// 0x20-0x7E only).
///
/// This is the borrowed equivalent of [`AsciiText`](crate::AsciiText), just as
/// [`AsciiStr`] is the borrowed equivalent of [`AsciiString`](crate::AsciiString).
///
/// # When to Use
///
/// - When you need to pass printable ASCII data without copying
/// - When working with substrings or slices of printable ASCII
/// - When deserializing with zero-copy (serde `borrow` feature)
///
/// # Example
///
/// ```
/// use nexus_ascii::{AsciiTextStr, AsciiText};
///
/// // From a validated text
/// let text: AsciiText<32> = AsciiText::try_from("hello")?;
/// let text_str: &AsciiTextStr = text.as_ascii_text_str();
///
/// // From bytes (with validation)
/// let from_bytes: &AsciiTextStr = AsciiTextStr::try_from_bytes(b"world")?;
///
/// assert_eq!(text_str.len(), 5);
/// assert_eq!(from_bytes.as_str(), "world");
/// # Ok::<(), nexus_ascii::AsciiError>(())
/// ```
#[repr(transparent)]
pub struct AsciiTextStr([u8]);

// =============================================================================
// Construction
// =============================================================================

impl AsciiTextStr {
    /// Creates an `&AsciiTextStr` from a byte slice after validating printable ASCII.
    ///
    /// Returns an error if any byte is not printable ASCII (< 0x20 or > 0x7E).
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::{AsciiTextStr, AsciiError};
    ///
    /// let valid: &AsciiTextStr = AsciiTextStr::try_from_bytes(b"hello")?;
    /// assert_eq!(valid.as_str(), "hello");
    ///
    /// // Control characters are rejected
    /// let invalid = AsciiTextStr::try_from_bytes(b"hello\t");
    /// assert!(matches!(invalid, Err(AsciiError::NonPrintable { .. })));
    /// # Ok::<(), AsciiError>(())
    /// ```
    #[inline]
    pub fn try_from_bytes(bytes: &[u8]) -> Result<&Self, AsciiError> {
        simd::validate_printable(bytes)
            .map_err(|(byte, pos)| AsciiError::NonPrintable { byte, pos })?;
        // SAFETY: We just validated all bytes are printable ASCII
        Ok(unsafe { Self::from_bytes_unchecked(bytes) })
    }

    /// Creates an `&AsciiTextStr` from a string slice after validating printable ASCII.
    ///
    /// Returns an error if any character is not printable ASCII.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::{AsciiTextStr, AsciiError};
    ///
    /// let valid: &AsciiTextStr = AsciiTextStr::try_from_str("hello")?;
    /// assert_eq!(valid.as_str(), "hello");
    /// # Ok::<(), AsciiError>(())
    /// ```
    #[inline]
    pub fn try_from_str(s: &str) -> Result<&Self, AsciiError> {
        Self::try_from_bytes(s.as_bytes())
    }

    /// Creates an `&AsciiTextStr` from a byte slice without validation.
    ///
    /// # Safety
    ///
    /// The caller must ensure all bytes are printable ASCII (0x20-0x7E).
    /// Violating this invariant may cause unexpected behavior in code that
    /// assumes printable content.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiTextStr;
    ///
    /// let bytes = b"HELLO";
    /// // SAFETY: bytes are known printable ASCII
    /// let s: &AsciiTextStr = unsafe { AsciiTextStr::from_bytes_unchecked(bytes) };
    /// assert_eq!(s.as_str(), "HELLO");
    /// ```
    #[inline]
    pub const unsafe fn from_bytes_unchecked(bytes: &[u8]) -> &Self {
        // SAFETY: AsciiTextStr is #[repr(transparent)] over [u8]
        unsafe { &*(bytes as *const [u8] as *const Self) }
    }

    /// Creates an `&AsciiTextStr` from a string slice without validation.
    ///
    /// # Safety
    ///
    /// The caller must ensure all characters are printable ASCII (0x20-0x7E).
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiTextStr;
    ///
    /// let s = "hello";
    /// // SAFETY: "hello" is known printable ASCII
    /// let text: &AsciiTextStr = unsafe { AsciiTextStr::from_str_unchecked(s) };
    /// assert_eq!(text.len(), 5);
    /// ```
    #[inline]
    pub const unsafe fn from_str_unchecked(s: &str) -> &Self {
        // SAFETY: Caller guarantees printable ASCII
        unsafe { Self::from_bytes_unchecked(s.as_bytes()) }
    }

    /// Returns an empty `&AsciiTextStr`.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiTextStr;
    ///
    /// let empty = AsciiTextStr::empty();
    /// assert!(empty.is_empty());
    /// assert_eq!(empty.len(), 0);
    /// ```
    #[inline]
    pub const fn empty() -> &'static Self {
        // SAFETY: Empty slice is trivially valid printable ASCII
        unsafe { Self::from_bytes_unchecked(&[]) }
    }

    /// Creates an `&AsciiTextStr` from an `&AsciiStr` after validating printable.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::{AsciiStr, AsciiTextStr};
    ///
    /// let ascii = AsciiStr::try_from_bytes(b"hello")?;
    /// let text = AsciiTextStr::try_from_ascii_str(ascii)?;
    /// assert_eq!(text.as_str(), "hello");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn try_from_ascii_str(s: &AsciiStr) -> Result<&Self, AsciiError> {
        Self::try_from_bytes(s.as_bytes())
    }
}

// =============================================================================
// Accessors
// =============================================================================

impl AsciiTextStr {
    /// Returns the length of the string in bytes.
    #[inline]
    pub const fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns `true` if the string is empty.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Returns the string as a byte slice.
    #[inline]
    pub const fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    /// Returns the string as a `&str`.
    ///
    /// This is a zero-cost conversion since printable ASCII is valid UTF-8.
    #[inline]
    pub const fn as_str(&self) -> &str {
        // SAFETY: Printable ASCII is always valid UTF-8
        unsafe { core::str::from_utf8_unchecked(&self.0) }
    }

    /// Returns this as an `&AsciiStr`.
    ///
    /// This is a zero-cost conversion since printable ASCII is a subset of ASCII.
    #[inline]
    pub const fn as_ascii_str(&self) -> &AsciiStr {
        // SAFETY: Printable ASCII is valid ASCII
        unsafe { AsciiStr::from_bytes_unchecked(&self.0) }
    }

    /// Returns the character at the given index, or `None` if out of bounds.
    #[inline]
    pub fn get(&self, index: usize) -> Option<AsciiChar> {
        if index < self.len() {
            // SAFETY: index is within bounds and data contains valid ASCII
            Some(unsafe { AsciiChar::new_unchecked(self.0[index]) })
        } else {
            None
        }
    }

    /// Returns the character at the given index without bounds checking.
    ///
    /// # Safety
    ///
    /// The index must be less than `self.len()`.
    #[inline]
    pub unsafe fn get_unchecked(&self, index: usize) -> AsciiChar {
        debug_assert!(index < self.len());
        // SAFETY: caller guarantees index < len, data contains valid ASCII
        unsafe { AsciiChar::new_unchecked(*self.0.get_unchecked(index)) }
    }

    /// Returns the first character, or `None` if the string is empty.
    #[inline]
    pub fn first(&self) -> Option<AsciiChar> {
        self.get(0)
    }

    /// Returns the last character, or `None` if the string is empty.
    #[inline]
    pub fn last(&self) -> Option<AsciiChar> {
        if self.is_empty() {
            None
        } else {
            self.get(self.len() - 1)
        }
    }

    /// Returns an iterator over the characters in the string.
    #[inline]
    pub fn chars(&self) -> impl Iterator<Item = AsciiChar> + '_ {
        self.0.iter().map(|&b| {
            // SAFETY: all bytes in the string are valid ASCII
            unsafe { AsciiChar::new_unchecked(b) }
        })
    }

    /// Returns an iterator over the bytes in the string.
    #[inline]
    pub fn bytes(&self) -> impl Iterator<Item = u8> + '_ {
        self.0.iter().copied()
    }
}

// =============================================================================
// Comparison Methods
// =============================================================================

impl AsciiTextStr {
    /// Compares two strings for equality, ignoring ASCII case.
    #[inline]
    pub fn eq_ignore_ascii_case(&self, other: &Self) -> bool {
        // Use SWAR-optimized comparison (8 bytes at a time)
        crate::simd::eq_ignore_ascii_case(&self.0, &other.0)
    }

    /// Returns `true` if the string starts with the given prefix.
    #[inline]
    pub fn starts_with<P: AsRef<[u8]>>(&self, prefix: P) -> bool {
        self.0.starts_with(prefix.as_ref())
    }

    /// Returns `true` if the string ends with the given suffix.
    #[inline]
    pub fn ends_with<S: AsRef<[u8]>>(&self, suffix: S) -> bool {
        self.0.ends_with(suffix.as_ref())
    }

    /// Returns the string with the given prefix removed.
    ///
    /// Returns `Some(stripped)` if the string starts with the prefix,
    /// or `None` if it doesn't.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiTextStr;
    ///
    /// let s = AsciiTextStr::try_from_bytes(b"USD-BTC")?;
    /// let stripped = s.strip_prefix("USD-").unwrap();
    /// assert_eq!(stripped.as_str(), "BTC");
    ///
    /// assert!(s.strip_prefix("EUR-").is_none());
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn strip_prefix<P: AsRef<[u8]>>(&self, prefix: P) -> Option<&AsciiTextStr> {
        let prefix = prefix.as_ref();
        if self.0.starts_with(prefix) {
            // SAFETY: Prefix is within bounds, remaining bytes are printable ASCII
            Some(unsafe { AsciiTextStr::from_bytes_unchecked(&self.0[prefix.len()..]) })
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
    /// use nexus_ascii::AsciiTextStr;
    ///
    /// let s = AsciiTextStr::try_from_bytes(b"BTC-USD")?;
    /// let stripped = s.strip_suffix("-USD").unwrap();
    /// assert_eq!(stripped.as_str(), "BTC");
    ///
    /// assert!(s.strip_suffix("-EUR").is_none());
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn strip_suffix<S: AsRef<[u8]>>(&self, suffix: S) -> Option<&AsciiTextStr> {
        let suffix = suffix.as_ref();
        if self.0.ends_with(suffix) {
            let new_len = self.len() - suffix.len();
            // SAFETY: new_len is within bounds, bytes are printable ASCII
            Some(unsafe { AsciiTextStr::from_bytes_unchecked(&self.0[..new_len]) })
        } else {
            None
        }
    }

    /// Returns `true` if the string contains the given substring.
    #[inline]
    pub fn contains<N: AsRef<[u8]>>(&self, needle: N) -> bool {
        let needle = needle.as_ref();
        if needle.is_empty() {
            return true;
        }
        self.0.windows(needle.len()).any(|window| window == needle)
    }

    // =========================================================================
    // Trim Methods
    // =========================================================================

    /// Returns a string slice with leading and trailing ASCII whitespace removed.
    ///
    /// Note: For `AsciiTextStr`, only space (0x20) is valid whitespace since
    /// other whitespace characters (tab, newline, etc.) are not printable.
    #[inline]
    pub fn trim(&self) -> &Self {
        self.trim_start().trim_end()
    }

    /// Returns a string slice with leading ASCII whitespace removed.
    #[inline]
    pub fn trim_start(&self) -> &Self {
        let start = self
            .0
            .iter()
            .position(|&b| b != b' ')
            .unwrap_or(self.0.len());
        // SAFETY: trimmed slice is still valid printable ASCII
        unsafe { Self::from_bytes_unchecked(&self.0[start..]) }
    }

    /// Returns a string slice with trailing ASCII whitespace removed.
    #[inline]
    pub fn trim_end(&self) -> &Self {
        let end = self.0.iter().rposition(|&b| b != b' ').map_or(0, |i| i + 1);
        // SAFETY: trimmed slice is still valid printable ASCII
        unsafe { Self::from_bytes_unchecked(&self.0[..end]) }
    }

    // =========================================================================
    // Find Methods
    // =========================================================================

    /// Returns the byte index of the first occurrence of a byte.
    #[inline]
    pub fn find_byte(&self, byte: u8) -> Option<usize> {
        self.0.iter().position(|&b| b == byte)
    }

    /// Returns the byte index of the first occurrence of an ASCII character.
    #[inline]
    pub fn find_char(&self, ch: AsciiChar) -> Option<usize> {
        self.find_byte(ch.as_u8())
    }

    /// Returns the byte index of the first occurrence of a byte pattern.
    #[inline]
    pub fn find(&self, needle: &[u8]) -> Option<usize> {
        if needle.is_empty() {
            return Some(0);
        }
        self.0
            .windows(needle.len())
            .position(|window| window == needle)
    }

    /// Returns the byte index of the last occurrence of a byte.
    #[inline]
    pub fn rfind_byte(&self, byte: u8) -> Option<usize> {
        self.0.iter().rposition(|&b| b == byte)
    }

    /// Returns the byte index of the last occurrence of an ASCII character.
    #[inline]
    pub fn rfind_char(&self, ch: AsciiChar) -> Option<usize> {
        self.rfind_byte(ch.as_u8())
    }

    /// Returns the byte index of the last occurrence of a byte pattern.
    #[inline]
    pub fn rfind(&self, needle: &[u8]) -> Option<usize> {
        if needle.is_empty() {
            return Some(self.len());
        }
        if needle.len() > self.len() {
            return None;
        }
        self.0
            .windows(needle.len())
            .rposition(|window| window == needle)
    }

    /// Splits the text on the first occurrence of the delimiter.
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
    /// use nexus_ascii::{AsciiTextStr, AsciiChar};
    ///
    /// let s = AsciiTextStr::try_from_bytes(b"BTC-USD")?;
    /// let (base, quote) = s.split_once(AsciiChar::MINUS).unwrap();
    /// assert_eq!(base.as_str(), "BTC");
    /// assert_eq!(quote.as_str(), "USD");
    ///
    /// // No delimiter found
    /// let s2 = AsciiTextStr::try_from_bytes(b"BTCUSD")?;
    /// assert!(s2.split_once(AsciiChar::MINUS).is_none());
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn split_once(&self, delimiter: AsciiChar) -> Option<(&AsciiTextStr, &AsciiTextStr)> {
        let pos = self.find_byte(delimiter.as_u8())?;
        // SAFETY: pos is within bounds, AsciiTextStr guarantees printable ASCII
        let before = unsafe { AsciiTextStr::from_bytes_unchecked(&self.0[..pos]) };
        // SAFETY: pos is within bounds, AsciiTextStr guarantees printable ASCII
        let after = unsafe { AsciiTextStr::from_bytes_unchecked(&self.0[pos + 1..]) };
        Some((before, after))
    }

    /// Returns `true` if all characters are ASCII digits (0-9).
    ///
    /// An empty string returns `true`.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiTextStr;
    ///
    /// let digits = AsciiTextStr::try_from_bytes(b"12345")?;
    /// assert!(digits.is_numeric());
    ///
    /// let mixed = AsciiTextStr::try_from_bytes(b"123abc")?;
    /// assert!(!mixed.is_numeric());
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn is_numeric(&self) -> bool {
        crate::simd::is_all_numeric(&self.0)
    }

    /// Returns `true` if all characters are ASCII alphanumeric (A-Z, a-z, 0-9).
    ///
    /// An empty string returns `true`.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiTextStr;
    ///
    /// let alphanum = AsciiTextStr::try_from_bytes(b"ABC123")?;
    /// assert!(alphanum.is_alphanumeric());
    ///
    /// let with_dash = AsciiTextStr::try_from_bytes(b"BTC-USD")?;
    /// assert!(!with_dash.is_alphanumeric());
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn is_alphanumeric(&self) -> bool {
        crate::simd::is_all_alphanumeric(&self.0)
    }
}

// =============================================================================
// Integer Parsing
// =============================================================================

crate::parse::impl_parse_int!(AsciiTextStr, as_str);

// =============================================================================
// Trait Implementations
// =============================================================================

impl PartialEq for AsciiTextStr {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for AsciiTextStr {}

impl PartialOrd for AsciiTextStr {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AsciiTextStr {
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

impl Hash for AsciiTextStr {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        let header = hash::pack_header(self.0.len() as u16, hash::hash_unbounded(&self.0));
        state.write_u64(hash::finalize(header));
    }
}

impl core::fmt::Debug for AsciiTextStr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("AsciiTextStr")
            .field("value", &self.as_str())
            .field("len", &self.len())
            .finish()
    }
}

impl core::fmt::Display for AsciiTextStr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.as_str())
    }
}

impl core::ops::Index<usize> for AsciiTextStr {
    type Output = AsciiChar;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        assert!(index < self.len(), "index out of bounds");
        // SAFETY: index is within bounds, data contains valid ASCII.
        // AsciiChar is #[repr(transparent)] over u8.
        unsafe { &*(self.0.get_unchecked(index) as *const u8 as *const AsciiChar) }
    }
}

impl core::ops::Index<core::ops::Range<usize>> for AsciiTextStr {
    type Output = Self;

    #[inline]
    fn index(&self, range: core::ops::Range<usize>) -> &Self::Output {
        assert!(range.start <= range.end, "range start > end");
        assert!(range.end <= self.len(), "range end out of bounds");
        // SAFETY: range is within bounds, data contains valid printable ASCII
        unsafe { Self::from_bytes_unchecked(&self.0[range]) }
    }
}

impl core::ops::Index<core::ops::RangeFrom<usize>> for AsciiTextStr {
    type Output = Self;

    #[inline]
    fn index(&self, range: core::ops::RangeFrom<usize>) -> &Self::Output {
        assert!(range.start <= self.len(), "range start out of bounds");
        // SAFETY: range is within bounds, data contains valid printable ASCII
        unsafe { Self::from_bytes_unchecked(&self.0[range]) }
    }
}

impl core::ops::Index<core::ops::RangeTo<usize>> for AsciiTextStr {
    type Output = Self;

    #[inline]
    fn index(&self, range: core::ops::RangeTo<usize>) -> &Self::Output {
        assert!(range.end <= self.len(), "range end out of bounds");
        // SAFETY: range is within bounds, data contains valid printable ASCII
        unsafe { Self::from_bytes_unchecked(&self.0[range]) }
    }
}

impl core::ops::Index<core::ops::RangeFull> for AsciiTextStr {
    type Output = Self;

    #[inline]
    fn index(&self, _range: core::ops::RangeFull) -> &Self::Output {
        self
    }
}

impl core::ops::Index<core::ops::RangeInclusive<usize>> for AsciiTextStr {
    type Output = Self;

    #[inline]
    fn index(&self, range: core::ops::RangeInclusive<usize>) -> &Self::Output {
        let start = *range.start();
        let end = *range.end();
        assert!(start <= end, "range start > end");
        assert!(end < self.len(), "range end out of bounds");
        // SAFETY: range is within bounds, data contains valid printable ASCII
        unsafe { Self::from_bytes_unchecked(&self.0[start..=end]) }
    }
}

impl core::ops::Index<core::ops::RangeToInclusive<usize>> for AsciiTextStr {
    type Output = Self;

    #[inline]
    fn index(&self, range: core::ops::RangeToInclusive<usize>) -> &Self::Output {
        assert!(range.end < self.len(), "range end out of bounds");
        // SAFETY: range is within bounds, data contains valid printable ASCII
        unsafe { Self::from_bytes_unchecked(&self.0[range]) }
    }
}

// =============================================================================
// Cross-type equality
// =============================================================================

impl PartialEq<str> for AsciiTextStr {
    #[inline]
    fn eq(&self, other: &str) -> bool {
        self.0 == *other.as_bytes()
    }
}

impl PartialEq<AsciiTextStr> for str {
    #[inline]
    fn eq(&self, other: &AsciiTextStr) -> bool {
        *self.as_bytes() == other.0
    }
}

impl PartialEq<[u8]> for AsciiTextStr {
    #[inline]
    fn eq(&self, other: &[u8]) -> bool {
        self.0 == *other
    }
}

impl PartialEq<AsciiTextStr> for [u8] {
    #[inline]
    fn eq(&self, other: &AsciiTextStr) -> bool {
        *self == other.0
    }
}

impl PartialEq<AsciiStr> for AsciiTextStr {
    #[inline]
    fn eq(&self, other: &AsciiStr) -> bool {
        self.0 == *other.as_bytes()
    }
}

impl PartialEq<AsciiTextStr> for AsciiStr {
    #[inline]
    fn eq(&self, other: &AsciiTextStr) -> bool {
        *self.as_bytes() == other.0
    }
}

// =============================================================================
// AsRef implementations
// =============================================================================

impl AsRef<[u8]> for AsciiTextStr {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl AsRef<str> for AsciiTextStr {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<AsciiStr> for AsciiTextStr {
    #[inline]
    fn as_ref(&self) -> &AsciiStr {
        self.as_ascii_str()
    }
}

// =============================================================================
// Serde Support (feature-gated)
// =============================================================================

#[cfg(feature = "serde")]
impl serde::Serialize for AsciiTextStr {
    #[inline]
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(self.as_str())
    }
}

/// Zero-copy deserialization for borrowed printable ASCII strings.
///
/// This implementation allows deserializing `&'de AsciiTextStr` directly from the
/// input data without copying, when the deserializer supports borrowing
/// (e.g., `serde_json` with `&str` input).
///
/// # Example
///
/// ```
/// use nexus_ascii::AsciiTextStr;
/// use serde::Deserialize;
///
/// #[derive(Deserialize)]
/// struct Message<'a> {
///     #[serde(borrow)]
///     text: &'a AsciiTextStr,
/// }
///
/// let json = r#"{"text": "Hello, World!"}"#;
/// let msg: Message = serde_json::from_str(json).unwrap();
/// assert_eq!(msg.text.as_str(), "Hello, World!");
/// ```
#[cfg(feature = "serde")]
impl<'de: 'a, 'a> serde::Deserialize<'de> for &'a AsciiTextStr {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct AsciiTextStrVisitor;

        impl<'de> serde::de::Visitor<'de> for AsciiTextStrVisitor {
            type Value = &'de AsciiTextStr;

            fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                formatter.write_str("a borrowed printable ASCII string")
            }

            #[inline]
            fn visit_borrowed_str<E: serde::de::Error>(
                self,
                v: &'de str,
            ) -> Result<Self::Value, E> {
                AsciiTextStr::try_from_str(v).map_err(|e| match e {
                    AsciiError::NonPrintable { byte, pos } => E::custom(format_args!(
                        "non-printable ASCII byte 0x{:02X} at position {}",
                        byte, pos
                    )),
                    AsciiError::InvalidByte { byte, pos } => E::custom(format_args!(
                        "invalid ASCII byte 0x{:02X} at position {}",
                        byte, pos
                    )),
                    AsciiError::TooLong { .. } => E::custom("invalid printable ASCII"),
                })
            }

            #[inline]
            fn visit_borrowed_bytes<E: serde::de::Error>(
                self,
                v: &'de [u8],
            ) -> Result<Self::Value, E> {
                AsciiTextStr::try_from_bytes(v).map_err(|e| match e {
                    AsciiError::NonPrintable { byte, pos } => E::custom(format_args!(
                        "non-printable ASCII byte 0x{:02X} at position {}",
                        byte, pos
                    )),
                    AsciiError::InvalidByte { byte, pos } => E::custom(format_args!(
                        "invalid ASCII byte 0x{:02X} at position {}",
                        byte, pos
                    )),
                    AsciiError::TooLong { .. } => E::custom("invalid printable ASCII"),
                })
            }
        }

        deserializer.deserialize_str(AsciiTextStrVisitor)
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn try_from_bytes_valid() {
        let s = AsciiTextStr::try_from_bytes(b"hello").unwrap();
        assert_eq!(s.as_str(), "hello");
        assert_eq!(s.len(), 5);
    }

    #[test]
    fn try_from_bytes_non_printable() {
        let result = AsciiTextStr::try_from_bytes(b"hello\t");
        assert!(matches!(result, Err(AsciiError::NonPrintable { .. })));
    }

    #[test]
    fn try_from_bytes_control_char() {
        let result = AsciiTextStr::try_from_bytes(&[0x01]);
        assert!(matches!(
            result,
            Err(AsciiError::NonPrintable { byte: 0x01, pos: 0 })
        ));
    }

    #[test]
    fn try_from_str_valid() {
        let s = AsciiTextStr::try_from_str("hello").unwrap();
        assert_eq!(s.as_str(), "hello");
    }

    #[test]
    fn empty() {
        let s = AsciiTextStr::empty();
        assert!(s.is_empty());
        assert_eq!(s.len(), 0);
        assert_eq!(s.as_str(), "");
    }

    #[test]
    fn from_bytes_unchecked() {
        // SAFETY: b"test" is valid printable ASCII.
        let s = unsafe { AsciiTextStr::from_bytes_unchecked(b"test") };
        assert_eq!(s.as_str(), "test");
    }

    #[test]
    fn as_ascii_str() {
        let text = AsciiTextStr::try_from_bytes(b"hello").unwrap();
        let ascii: &AsciiStr = text.as_ascii_str();
        assert_eq!(ascii.as_str(), "hello");
    }

    #[test]
    fn trim() {
        let s = AsciiTextStr::try_from_bytes(b"  hello  ").unwrap();
        assert_eq!(s.trim().as_str(), "hello");
        assert_eq!(s.trim_start().as_str(), "hello  ");
        assert_eq!(s.trim_end().as_str(), "  hello");
    }

    #[test]
    fn equality() {
        let s1 = AsciiTextStr::try_from_bytes(b"hello").unwrap();
        let s2 = AsciiTextStr::try_from_bytes(b"hello").unwrap();
        let s3 = AsciiTextStr::try_from_bytes(b"world").unwrap();

        assert_eq!(s1, s2);
        assert_ne!(s1, s3);
    }

    #[test]
    fn cross_type_equality() {
        let s = AsciiTextStr::try_from_bytes(b"hello").unwrap();
        assert!(s == "hello");
        assert!(*s == b"hello"[..]);
    }

    #[cfg(feature = "serde")]
    mod serde_tests {
        use super::*;
        use serde::Deserialize;

        #[test]
        fn serialize() {
            let s = AsciiTextStr::try_from_bytes(b"Hello, World!").unwrap();
            let json = serde_json::to_string(&s).unwrap();
            assert_eq!(json, "\"Hello, World!\"");
        }

        #[derive(Debug, Deserialize)]
        struct BorrowedMessage<'a> {
            #[serde(borrow)]
            text: &'a AsciiTextStr,
        }

        #[test]
        fn deserialize_borrowed() {
            let json = r#"{"text": "Hello, World!"}"#;
            let msg: BorrowedMessage = serde_json::from_str(json).unwrap();
            assert_eq!(msg.text.as_str(), "Hello, World!");
        }

        #[test]
        fn deserialize_borrowed_empty() {
            let json = r#"{"text": ""}"#;
            let msg: BorrowedMessage = serde_json::from_str(json).unwrap();
            assert!(msg.text.is_empty());
        }

        #[test]
        fn deserialize_borrowed_with_escapes_fails() {
            // JSON with escape sequences can't be borrowed (serde_json allocates)
            // so we get an error about invalid type rather than validation
            let json = r#"{"text": "hello\tthere"}"#;
            let result: Result<BorrowedMessage, _> = serde_json::from_str(json);
            assert!(result.is_err());
        }

        #[test]
        fn deserialize_borrowed_non_ascii() {
            let json = r#"{"text": "héllo"}"#;
            let result: Result<BorrowedMessage, _> = serde_json::from_str(json);
            assert!(result.is_err());
        }
    }
}
