//! Mutable builder for constructing ASCII strings.

use crate::AsciiError;
use crate::char::AsciiChar;
use crate::simd;
use crate::str_ref::AsciiStr;
use crate::string::{AsciiString, find_null_byte};
use crate::text::AsciiText;

// =============================================================================
// AsciiStringBuilder
// =============================================================================

/// A mutable builder for constructing [`AsciiString`] values.
///
/// `AsciiStringBuilder` allows incremental construction of ASCII strings by
/// pushing characters, bytes, slices, or other ASCII types. When complete,
/// call [`build()`](Self::build) to produce an immutable [`AsciiString`].
///
/// Unlike `AsciiString`, the builder does not store a precomputed hash. The
/// hash is computed only when `build()` is called.
///
/// # Example
///
/// ```
/// use nexus_ascii::{AsciiStringBuilder, AsciiString};
///
/// let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
/// builder.push_str("BTC")?;
/// builder.push_byte(b'-')?;
/// builder.push_str("USD")?;
///
/// let s: AsciiString<32> = builder.build();
/// assert_eq!(s.as_str(), "BTC-USD");
/// # Ok::<(), nexus_ascii::AsciiError>(())
/// ```
#[derive(Clone)]
pub struct AsciiStringBuilder<const CAP: usize> {
    /// Current length of the string being built.
    len: usize,
    /// Raw ASCII bytes. Only `len` bytes are valid.
    data: [u8; CAP],
}

// =============================================================================
// Constructors
// =============================================================================

impl<const CAP: usize> AsciiStringBuilder<CAP> {
    /// Creates an empty builder.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiStringBuilder;
    ///
    /// let builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
    /// assert!(builder.is_empty());
    /// assert_eq!(builder.remaining(), 32);
    /// ```
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            len: 0,
            data: [0u8; CAP],
        }
    }

    /// Creates a builder initialized with the contents of an [`AsciiString`].
    ///
    /// This allows converting an immutable string back to a mutable builder
    /// for further modification.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::{AsciiString, AsciiStringBuilder};
    ///
    /// let s: AsciiString<32> = AsciiString::try_from("Hello")?;
    /// let mut builder = AsciiStringBuilder::from_ascii_string(s);
    /// builder.push_str(", World!")?;
    ///
    /// let result = builder.build();
    /// assert_eq!(result.as_str(), "Hello, World!");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn from_ascii_string(s: AsciiString<CAP>) -> Self {
        let len = s.len();
        let mut data = [0u8; CAP];
        data[..len].copy_from_slice(s.as_bytes());
        Self { len, data }
    }
}

impl<const CAP: usize> Default for AsciiStringBuilder<CAP> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

// =============================================================================
// Accessors
// =============================================================================

impl<const CAP: usize> AsciiStringBuilder<CAP> {
    /// Returns the current length of the builder.
    #[inline]
    #[must_use]
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the builder is empty.
    #[inline]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns the maximum capacity of the builder.
    #[inline]
    #[must_use]
    pub const fn capacity(&self) -> usize {
        CAP
    }

    /// Returns the remaining capacity available for pushing.
    #[inline]
    #[must_use]
    pub const fn remaining(&self) -> usize {
        CAP - self.len
    }

    /// Returns the current contents as a string slice.
    #[inline]
    #[must_use]
    pub fn as_str(&self) -> &str {
        // SAFETY: We only accept ASCII bytes, which are always valid UTF-8
        unsafe { core::str::from_utf8_unchecked(&self.data[..self.len]) }
    }

    /// Returns the current contents as a byte slice.
    #[inline]
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        &self.data[..self.len]
    }
}

// =============================================================================
// Mutation
// =============================================================================

impl<const CAP: usize> AsciiStringBuilder<CAP> {
    /// Pushes an ASCII character onto the builder.
    ///
    /// # Errors
    ///
    /// Returns [`AsciiError::TooLong`] if the builder is at capacity.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::{AsciiStringBuilder, AsciiChar};
    ///
    /// let mut builder: AsciiStringBuilder<8> = AsciiStringBuilder::new();
    /// builder.push(AsciiChar::A)?;
    /// builder.push(AsciiChar::B)?;
    /// assert_eq!(builder.as_str(), "AB");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn push(&mut self, ch: AsciiChar) -> Result<(), AsciiError> {
        let byte = ch.as_u8();
        if byte == 0 {
            return Err(AsciiError::InvalidByte {
                byte: 0,
                pos: self.len,
            });
        }
        if self.len >= CAP {
            return Err(AsciiError::TooLong {
                len: 1,
                cap: self.remaining(),
            });
        }
        self.data[self.len] = byte;
        self.len += 1;
        Ok(())
    }

    /// Pushes a byte onto the builder.
    ///
    /// # Errors
    ///
    /// - [`AsciiError::InvalidByte`] if `byte` is null or `> 127`
    /// - [`AsciiError::TooLong`] if the builder is at capacity
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiStringBuilder;
    ///
    /// let mut builder: AsciiStringBuilder<8> = AsciiStringBuilder::new();
    /// builder.push_byte(b'H')?;
    /// builder.push_byte(b'i')?;
    /// assert_eq!(builder.as_str(), "Hi");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn push_byte(&mut self, byte: u8) -> Result<(), AsciiError> {
        if byte == 0 || byte > 127 {
            return Err(AsciiError::InvalidByte {
                byte,
                pos: self.len,
            });
        }
        if self.len >= CAP {
            return Err(AsciiError::TooLong {
                len: 1,
                cap: self.remaining(),
            });
        }
        self.data[self.len] = byte;
        self.len += 1;
        Ok(())
    }

    /// Pushes a string slice onto the builder.
    ///
    /// # Errors
    ///
    /// - [`AsciiError::InvalidByte`] if the string contains non-ASCII bytes
    /// - [`AsciiError::TooLong`] if the string exceeds remaining capacity
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiStringBuilder;
    ///
    /// let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
    /// builder.push_str("Hello, ")?;
    /// builder.push_str("World!")?;
    /// assert_eq!(builder.as_str(), "Hello, World!");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn push_str(&mut self, s: &str) -> Result<(), AsciiError> {
        self.push_bytes(s.as_bytes())
    }

    /// Pushes a byte slice onto the builder.
    ///
    /// # Errors
    ///
    /// - [`AsciiError::InvalidByte`] if any byte is null or > 127
    /// - [`AsciiError::TooLong`] if the slice exceeds remaining capacity
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiStringBuilder;
    ///
    /// let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
    /// builder.push_bytes(b"Hello")?;
    /// assert_eq!(builder.as_str(), "Hello");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn push_bytes(&mut self, bytes: &[u8]) -> Result<(), AsciiError> {
        if bytes.len() > self.remaining() {
            return Err(AsciiError::TooLong {
                len: bytes.len(),
                cap: self.remaining(),
            });
        }

        // Use bounded version since we know bytes.len() <= remaining() <= CAP
        if let Err((byte, pos)) = simd::validate_ascii_bounded::<CAP>(bytes) {
            return Err(AsciiError::InvalidByte { byte, pos });
        }

        // SAFETY: We verified the bytes fit and are ASCII
        unsafe { self.push_bytes_unchecked(bytes) };
        Ok(())
    }

    /// Pushes a byte slice onto the builder without validation.
    ///
    /// # Safety
    ///
    /// The caller must guarantee:
    /// - All bytes are valid ASCII (0x01-0x7F)
    /// - The slice length does not exceed `remaining()`
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiStringBuilder;
    ///
    /// let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
    /// // SAFETY: b"Hello" is ASCII and fits in remaining capacity
    /// unsafe { builder.push_bytes_unchecked(b"Hello") };
    /// assert_eq!(builder.as_str(), "Hello");
    /// ```
    #[inline]
    pub unsafe fn push_bytes_unchecked(&mut self, bytes: &[u8]) {
        debug_assert!(
            bytes.len() <= self.remaining(),
            "bytes exceed remaining capacity"
        );
        debug_assert!(
            bytes.iter().all(|&b| b > 0 && b <= 127),
            "bytes contain null or non-ASCII"
        );

        // SAFETY: Caller guarantees bytes fit
        unsafe {
            core::ptr::copy_nonoverlapping(
                bytes.as_ptr(),
                self.data.as_mut_ptr().add(self.len),
                bytes.len(),
            );
        }
        self.len += bytes.len();
    }

    /// Pushes an [`AsciiStr`] onto the builder.
    ///
    /// Since `AsciiStr` is already validated, this only checks capacity.
    ///
    /// # Errors
    ///
    /// Returns [`AsciiError::TooLong`] if the string exceeds remaining capacity.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::{AsciiStr, AsciiStringBuilder};
    ///
    /// let ascii_str = AsciiStr::try_from_bytes(b"World")?;
    /// let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
    /// builder.push_str("Hello, ")?;
    /// builder.push_ascii_str(ascii_str)?;
    /// assert_eq!(builder.as_str(), "Hello, World");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn push_ascii_str(&mut self, s: &AsciiStr) -> Result<(), AsciiError> {
        let bytes = s.as_bytes();
        if bytes.len() > self.remaining() {
            return Err(AsciiError::TooLong {
                len: bytes.len(),
                cap: self.remaining(),
            });
        }

        // SAFETY: AsciiStr is already validated ASCII and we checked capacity
        unsafe { self.push_bytes_unchecked(bytes) };
        Ok(())
    }

    /// Pushes an [`AsciiString`] onto the builder.
    ///
    /// The source string can have a different capacity than the builder.
    /// Since `AsciiString` is already validated, this only checks capacity.
    ///
    /// # Errors
    ///
    /// Returns [`AsciiError::TooLong`] if the string exceeds remaining capacity.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::{AsciiString, AsciiStringBuilder};
    ///
    /// let suffix: AsciiString<8> = AsciiString::try_from("USD")?;
    /// let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
    /// builder.push_str("BTC-")?;
    /// builder.push_ascii_string(&suffix)?;
    /// assert_eq!(builder.as_str(), "BTC-USD");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn push_ascii_string<const N: usize>(
        &mut self,
        s: &AsciiString<N>,
    ) -> Result<(), AsciiError> {
        let bytes = s.as_bytes();
        if bytes.len() > self.remaining() {
            return Err(AsciiError::TooLong {
                len: bytes.len(),
                cap: self.remaining(),
            });
        }

        // SAFETY: AsciiString is already validated ASCII and we checked capacity
        unsafe { self.push_bytes_unchecked(bytes) };
        Ok(())
    }

    /// Pushes content from a raw null-terminated buffer onto the builder.
    ///
    /// Reads bytes from the buffer until the first null byte (or end of buffer),
    /// validates them as ASCII, and appends them to the builder.
    ///
    /// # Errors
    ///
    /// - [`AsciiError::InvalidByte`] if any byte before the null is null or > 127
    /// - [`AsciiError::TooLong`] if the content exceeds remaining capacity
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiStringBuilder;
    ///
    /// let buffer: [u8; 16] = *b"USD\0\0\0\0\0\0\0\0\0\0\0\0\0";
    /// let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
    /// builder.push_str("BTC-")?;
    /// builder.push_raw(buffer)?;
    /// assert_eq!(builder.as_str(), "BTC-USD");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn push_raw<const N: usize>(&mut self, buffer: [u8; N]) -> Result<(), AsciiError> {
        let content_len = find_null_byte(&buffer);
        let content = &buffer[..content_len];

        if content_len > self.remaining() {
            return Err(AsciiError::TooLong {
                len: content_len,
                cap: self.remaining(),
            });
        }

        // Use bounded version since content_len <= remaining() <= CAP
        if let Err((byte, pos)) = simd::validate_ascii_bounded::<CAP>(content) {
            return Err(AsciiError::InvalidByte { byte, pos });
        }

        // SAFETY: We validated ASCII and checked capacity
        unsafe { self.push_bytes_unchecked(content) };
        Ok(())
    }

    /// Pushes content from a raw null-terminated buffer without ASCII validation.
    ///
    /// Reads bytes from the buffer until the first null byte (or end of buffer)
    /// and appends them to the builder.
    ///
    /// # Safety
    ///
    /// The caller must guarantee:
    /// - All bytes before the first null (or entire buffer) are valid ASCII (0x01-0x7F)
    /// - The content length does not exceed `remaining()`
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiStringBuilder;
    ///
    /// let buffer: [u8; 16] = *b"USD\0\0\0\0\0\0\0\0\0\0\0\0\0";
    /// let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
    /// builder.push_str("BTC-")?;
    /// // SAFETY: Buffer content is ASCII and fits
    /// unsafe { builder.push_raw_unchecked(buffer) };
    /// assert_eq!(builder.as_str(), "BTC-USD");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub unsafe fn push_raw_unchecked<const N: usize>(&mut self, buffer: [u8; N]) {
        let content_len = find_null_byte(&buffer);
        debug_assert!(
            content_len <= self.remaining(),
            "content exceeds remaining capacity"
        );
        debug_assert!(
            buffer[..content_len].iter().all(|&b| b > 0 && b <= 127),
            "buffer contains null or non-ASCII"
        );

        // SAFETY: Caller guarantees ASCII and capacity
        unsafe {
            core::ptr::copy_nonoverlapping(
                buffer.as_ptr(),
                self.data.as_mut_ptr().add(self.len),
                content_len,
            );
        }
        self.len += content_len;
    }

    /// Clears the builder, resetting it to empty.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiStringBuilder;
    ///
    /// let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
    /// builder.push_str("Hello")?;
    /// assert_eq!(builder.len(), 5);
    ///
    /// builder.clear();
    /// assert!(builder.is_empty());
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.len = 0;
    }

    /// Truncates the builder to the specified length.
    ///
    /// If `new_len` is greater than the current length, this has no effect.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::AsciiStringBuilder;
    ///
    /// let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
    /// builder.push_str("Hello, World!")?;
    /// builder.truncate(5);
    /// assert_eq!(builder.as_str(), "Hello");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn truncate(&mut self, new_len: usize) {
        if new_len < self.len {
            self.len = new_len;
        }
    }
}

// =============================================================================
// Finalization
// =============================================================================

impl<const CAP: usize> AsciiStringBuilder<CAP> {
    /// Consumes the builder and returns an immutable [`AsciiString`].
    ///
    /// This computes the hash for the final string content.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::{AsciiString, AsciiStringBuilder};
    ///
    /// let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
    /// builder.push_str("BTC-USD")?;
    ///
    /// let s: AsciiString<32> = builder.build();
    /// assert_eq!(s.as_str(), "BTC-USD");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn build(self) -> AsciiString<CAP> {
        AsciiString::from_parts_unchecked(self.len, self.data)
    }

    /// Consumes the builder and returns an immutable [`AsciiText`].
    ///
    /// This validates that all characters are printable (0x20-0x7E) and
    /// computes the hash for the final string content.
    ///
    /// # Errors
    ///
    /// Returns [`AsciiError::NonPrintable`] if any byte is < 0x20 or > 0x7E.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_ascii::{AsciiText, AsciiStringBuilder};
    ///
    /// let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
    /// builder.push_str("Hello, World!")?;
    ///
    /// let text: AsciiText<32> = builder.build_text()?;
    /// assert_eq!(text.as_str(), "Hello, World!");
    /// # Ok::<(), nexus_ascii::AsciiError>(())
    /// ```
    #[inline]
    pub fn build_text(self) -> Result<AsciiText<CAP>, AsciiError> {
        let s = self.build();
        AsciiText::try_from_ascii_string(s)
    }
}

// =============================================================================
// Trait Implementations
// =============================================================================

impl<const CAP: usize> core::fmt::Debug for AsciiStringBuilder<CAP> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("AsciiStringBuilder")
            .field("len", &self.len)
            .field("capacity", &CAP)
            .field("content", &self.as_str())
            .finish()
    }
}

impl<const CAP: usize> core::fmt::Display for AsciiStringBuilder<CAP> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.as_str())
    }
}

impl<const CAP: usize> core::fmt::Write for AsciiStringBuilder<CAP> {
    /// Writes a string slice into the builder.
    ///
    /// This enables using the `write!` macro to format directly into
    /// an `AsciiStringBuilder`.
    ///
    /// # Errors
    ///
    /// Returns [`core::fmt::Error`] if the string contains non-ASCII bytes
    /// or exceeds remaining capacity.
    ///
    /// # Example
    ///
    /// ```
    /// use core::fmt::Write;
    /// use nexus_ascii::AsciiStringBuilder;
    ///
    /// let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
    /// write!(builder, "order-{:08}", 12345)?;
    /// assert_eq!(builder.as_str(), "order-00012345");
    /// # Ok::<(), core::fmt::Error>(())
    /// ```
    #[inline]
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        self.push_str(s).map_err(|_| core::fmt::Error)
    }

    /// Writes a single character into the builder.
    ///
    /// # Errors
    ///
    /// Returns [`core::fmt::Error`] if the character is non-ASCII
    /// or exceeds remaining capacity.
    #[inline]
    fn write_char(&mut self, c: char) -> core::fmt::Result {
        if c.is_ascii() {
            self.push_byte(c as u8).map_err(|_| core::fmt::Error)
        } else {
            Err(core::fmt::Error)
        }
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_empty() {
        let builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        assert!(builder.is_empty());
        assert_eq!(builder.len(), 0);
        assert_eq!(builder.capacity(), 32);
        assert_eq!(builder.remaining(), 32);
    }

    #[test]
    fn test_default() {
        let builder: AsciiStringBuilder<16> = AsciiStringBuilder::default();
        assert!(builder.is_empty());
    }

    #[test]
    fn test_from_ascii_string() {
        let s: AsciiString<32> = AsciiString::try_from("Hello").unwrap();
        let builder = AsciiStringBuilder::from_ascii_string(s);
        assert_eq!(builder.len(), 5);
        assert_eq!(builder.as_str(), "Hello");
    }

    #[test]
    fn test_push_char() {
        let mut builder: AsciiStringBuilder<8> = AsciiStringBuilder::new();
        builder.push(AsciiChar::H).unwrap();
        builder.push(AsciiChar::i).unwrap();
        assert_eq!(builder.as_str(), "Hi");
    }

    #[test]
    fn test_push_byte() {
        let mut builder: AsciiStringBuilder<8> = AsciiStringBuilder::new();
        builder.push_byte(b'A').unwrap();
        builder.push_byte(b'B').unwrap();
        assert_eq!(builder.as_str(), "AB");
    }

    #[test]
    fn test_push_byte_invalid() {
        let mut builder: AsciiStringBuilder<8> = AsciiStringBuilder::new();
        let err = builder.push_byte(0xFF).unwrap_err();
        assert!(matches!(
            err,
            AsciiError::InvalidByte { byte: 0xFF, pos: 0 }
        ));
    }

    #[test]
    fn test_push_str() {
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        builder.push_str("Hello").unwrap();
        builder.push_str(", ").unwrap();
        builder.push_str("World!").unwrap();
        assert_eq!(builder.as_str(), "Hello, World!");
    }

    #[test]
    fn test_push_str_too_long() {
        let mut builder: AsciiStringBuilder<8> = AsciiStringBuilder::new();
        builder.push_str("Hello").unwrap();
        let err = builder.push_str("World!").unwrap_err();
        assert!(matches!(err, AsciiError::TooLong { .. }));
    }

    #[test]
    fn test_push_bytes() {
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        builder.push_bytes(b"Hello").unwrap();
        assert_eq!(builder.as_str(), "Hello");
    }

    #[test]
    fn test_push_bytes_unchecked() {
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        // SAFETY: b"Hello" is valid ASCII.
        unsafe { builder.push_bytes_unchecked(b"Hello") };
        assert_eq!(builder.as_str(), "Hello");
    }

    #[test]
    fn test_push_ascii_str() {
        let ascii_str = AsciiStr::try_from_bytes(b"World").unwrap();
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        builder.push_str("Hello, ").unwrap();
        builder.push_ascii_str(ascii_str).unwrap();
        assert_eq!(builder.as_str(), "Hello, World");
    }

    #[test]
    fn test_push_ascii_string() {
        let suffix: AsciiString<8> = AsciiString::try_from("USD").unwrap();
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        builder.push_str("BTC-").unwrap();
        builder.push_ascii_string(&suffix).unwrap();
        assert_eq!(builder.as_str(), "BTC-USD");
    }

    #[test]
    fn test_push_raw() {
        let buffer: [u8; 16] = *b"USD\0\0\0\0\0\0\0\0\0\0\0\0\0";
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        builder.push_str("BTC-").unwrap();
        builder.push_raw(buffer).unwrap();
        assert_eq!(builder.as_str(), "BTC-USD");
    }

    #[test]
    fn test_push_raw_full_buffer() {
        let buffer: [u8; 8] = *b"BTCUSDT!";
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        builder.push_raw(buffer).unwrap();
        assert_eq!(builder.as_str(), "BTCUSDT!");
    }

    #[test]
    fn test_push_raw_unchecked() {
        let buffer: [u8; 16] = *b"USD\0\0\0\0\0\0\0\0\0\0\0\0\0";
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        builder.push_str("BTC-").unwrap();
        // SAFETY: buffer contains valid ASCII bytes followed by null padding.
        unsafe { builder.push_raw_unchecked(buffer) };
        assert_eq!(builder.as_str(), "BTC-USD");
    }

    #[test]
    fn test_clear() {
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        builder.push_str("Hello").unwrap();
        assert_eq!(builder.len(), 5);
        builder.clear();
        assert!(builder.is_empty());
        assert_eq!(builder.remaining(), 32);
    }

    #[test]
    fn test_truncate() {
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        builder.push_str("Hello, World!").unwrap();
        builder.truncate(5);
        assert_eq!(builder.as_str(), "Hello");
    }

    #[test]
    fn test_truncate_noop() {
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        builder.push_str("Hi").unwrap();
        builder.truncate(100);
        assert_eq!(builder.as_str(), "Hi");
    }

    #[test]
    fn test_build() {
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        builder.push_str("BTC-USD").unwrap();
        let s = builder.build();
        assert_eq!(s.as_str(), "BTC-USD");
        assert_eq!(s.len(), 7);
    }

    #[test]
    fn test_build_empty() {
        let builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        let s = builder.build();
        assert!(s.is_empty());
    }

    #[test]
    fn test_build_hash_correct() {
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        builder.push_str("BTC-USD").unwrap();
        let built = builder.build();

        let direct: AsciiString<32> = AsciiString::try_from("BTC-USD").unwrap();

        // Hash should match
        assert_eq!(built.header(), direct.header());
        assert_eq!(built, direct);
    }

    #[test]
    fn test_debug() {
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        builder.push_str("Hello").unwrap();
        let debug = format!("{:?}", builder);
        assert!(debug.contains("AsciiStringBuilder"));
        assert!(debug.contains("Hello"));
    }

    #[test]
    fn test_display() {
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        builder.push_str("Hello").unwrap();
        assert_eq!(format!("{}", builder), "Hello");
    }

    #[test]
    fn test_clone() {
        let mut builder: AsciiStringBuilder<32> = AsciiStringBuilder::new();
        builder.push_str("Hello").unwrap();
        let cloned = builder.clone();
        assert_eq!(cloned.as_str(), "Hello");
    }

    #[test]
    fn test_capacity_exhausted() {
        let mut builder: AsciiStringBuilder<8> = AsciiStringBuilder::new();
        builder.push_str("HelloYo!").unwrap();
        assert_eq!(builder.remaining(), 0);

        let err = builder.push_byte(b'!').unwrap_err();
        assert!(matches!(err, AsciiError::TooLong { .. }));

        let err = builder.push(AsciiChar::EXCLAMATION).unwrap_err();
        assert!(matches!(err, AsciiError::TooLong { .. }));
    }
}
