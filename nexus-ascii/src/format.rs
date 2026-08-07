//! Integer formatting utilities for ASCII strings.
//!
//! This module provides macros and functions for formatting integers into ASCII strings.
//! Similar to the `itoa` crate but integrated with our ASCII string types.

/// Maximum buffer size needed for any integer type (i128 needs up to 40 chars)
const MAX_INT_LEN: usize = 40;

/// Formats an unsigned integer into a buffer, returning the slice containing the formatted number.
///
/// The buffer is written from the end backwards, and the returned slice starts at the
/// first digit.
#[inline]
pub(crate) fn format_unsigned<T: Into<u128>>(value: T, buf: &mut [u8; MAX_INT_LEN]) -> &[u8] {
    let mut value = value.into();
    let mut pos = MAX_INT_LEN;

    if value == 0 {
        pos -= 1;
        buf[pos] = b'0';
        return &buf[pos..];
    }

    while value > 0 {
        pos -= 1;
        buf[pos] = b'0' + (value % 10) as u8;
        value /= 10;
    }

    &buf[pos..]
}

/// Formats a signed integer into a buffer, returning the slice containing the formatted number.
#[inline]
pub(crate) fn format_signed<T: Into<i128>>(value: T, buf: &mut [u8; MAX_INT_LEN]) -> &[u8] {
    let value = value.into();

    if value >= 0 {
        format_unsigned(value as u128, buf)
    } else {
        // Handle negative numbers
        // Use unsigned_abs() which handles i128::MIN correctly
        let abs_value = value.unsigned_abs();

        let mut pos = MAX_INT_LEN;

        // Format the absolute value
        let mut v = abs_value;
        while v > 0 {
            pos -= 1;
            buf[pos] = b'0' + (v % 10) as u8;
            v /= 10;
        }

        // Add the minus sign
        pos -= 1;
        buf[pos] = b'-';

        &buf[pos..]
    }
}

/// Error returned when an integer is too large to fit in the target capacity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IntegerTooLarge {
    /// The number of characters needed to format the integer.
    pub needed: usize,
    /// The available capacity.
    pub capacity: usize,
}

impl core::fmt::Display for IntegerTooLarge {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "integer requires {} characters but capacity is {}",
            self.needed, self.capacity
        )
    }
}

#[cfg(feature = "std")]
impl std::error::Error for IntegerTooLarge {}

/// Macro to generate integer formatting methods for a generic type with const CAP.
macro_rules! impl_format_int_generic {
    ($ty:ident, $from_bytes:ident) => {
        impl<const CAP: usize> $ty<CAP> {
            /// Formats a `u8` into this string type.
            ///
            /// # Errors
            ///
            /// Returns an error if the formatted integer exceeds the capacity.
            ///
            /// # Example
            ///
            /// ```
            /// # use nexus_ascii::*;
            /// let s: AsciiString<8> = AsciiString::from_u8(255)?;
            /// assert_eq!(s.as_str(), "255");
            /// # Ok::<(), nexus_ascii::IntegerTooLarge>(())
            /// ```
            #[inline]
            pub fn from_u8(value: u8) -> Result<Self, crate::format::IntegerTooLarge> {
                let mut buf = [0u8; 40];
                let formatted = crate::format::format_unsigned(value, &mut buf);
                if formatted.len() > CAP {
                    return Err(crate::format::IntegerTooLarge {
                        needed: formatted.len(),
                        capacity: CAP,
                    });
                }
                // SAFETY: digits are always ASCII
                Ok(unsafe { Self::$from_bytes(formatted) })
            }

            /// Formats a `u16` into this string type.
            #[inline]
            pub fn from_u16(value: u16) -> Result<Self, crate::format::IntegerTooLarge> {
                let mut buf = [0u8; 40];
                let formatted = crate::format::format_unsigned(value, &mut buf);
                if formatted.len() > CAP {
                    return Err(crate::format::IntegerTooLarge {
                        needed: formatted.len(),
                        capacity: CAP,
                    });
                }
                // SAFETY: digits are always ASCII
                Ok(unsafe { Self::$from_bytes(formatted) })
            }

            /// Formats a `u32` into this string type.
            #[inline]
            pub fn from_u32(value: u32) -> Result<Self, crate::format::IntegerTooLarge> {
                let mut buf = [0u8; 40];
                let formatted = crate::format::format_unsigned(value, &mut buf);
                if formatted.len() > CAP {
                    return Err(crate::format::IntegerTooLarge {
                        needed: formatted.len(),
                        capacity: CAP,
                    });
                }
                // SAFETY: digits are always ASCII
                Ok(unsafe { Self::$from_bytes(formatted) })
            }

            /// Formats a `u64` into this string type.
            ///
            /// # Example
            ///
            /// ```
            /// # use nexus_ascii::*;
            /// let s: AsciiString<32> = AsciiString::from_u64(12345678901234)?;
            /// assert_eq!(s.as_str(), "12345678901234");
            /// # Ok::<(), nexus_ascii::IntegerTooLarge>(())
            /// ```
            #[inline]
            pub fn from_u64(value: u64) -> Result<Self, crate::format::IntegerTooLarge> {
                let mut buf = [0u8; 40];
                let formatted = crate::format::format_unsigned(value, &mut buf);
                if formatted.len() > CAP {
                    return Err(crate::format::IntegerTooLarge {
                        needed: formatted.len(),
                        capacity: CAP,
                    });
                }
                // SAFETY: digits are always ASCII
                Ok(unsafe { Self::$from_bytes(formatted) })
            }

            /// Formats a `u128` into this string type.
            #[inline]
            pub fn from_u128(value: u128) -> Result<Self, crate::format::IntegerTooLarge> {
                let mut buf = [0u8; 40];
                let formatted = crate::format::format_unsigned(value, &mut buf);
                if formatted.len() > CAP {
                    return Err(crate::format::IntegerTooLarge {
                        needed: formatted.len(),
                        capacity: CAP,
                    });
                }
                // SAFETY: digits are always ASCII
                Ok(unsafe { Self::$from_bytes(formatted) })
            }

            /// Formats a `usize` into this string type.
            #[inline]
            pub fn from_usize(value: usize) -> Result<Self, crate::format::IntegerTooLarge> {
                let mut buf = [0u8; 40];
                let formatted = crate::format::format_unsigned(value as u128, &mut buf);
                if formatted.len() > CAP {
                    return Err(crate::format::IntegerTooLarge {
                        needed: formatted.len(),
                        capacity: CAP,
                    });
                }
                // SAFETY: digits are always ASCII
                Ok(unsafe { Self::$from_bytes(formatted) })
            }

            /// Formats an `i8` into this string type.
            ///
            /// # Example
            ///
            /// ```
            /// # use nexus_ascii::*;
            /// let s: AsciiString<8> = AsciiString::from_i8(-128)?;
            /// assert_eq!(s.as_str(), "-128");
            /// # Ok::<(), nexus_ascii::IntegerTooLarge>(())
            /// ```
            #[inline]
            pub fn from_i8(value: i8) -> Result<Self, crate::format::IntegerTooLarge> {
                let mut buf = [0u8; 40];
                let formatted = crate::format::format_signed(value, &mut buf);
                if formatted.len() > CAP {
                    return Err(crate::format::IntegerTooLarge {
                        needed: formatted.len(),
                        capacity: CAP,
                    });
                }
                // SAFETY: digits are always ASCII
                Ok(unsafe { Self::$from_bytes(formatted) })
            }

            /// Formats an `i16` into this string type.
            #[inline]
            pub fn from_i16(value: i16) -> Result<Self, crate::format::IntegerTooLarge> {
                let mut buf = [0u8; 40];
                let formatted = crate::format::format_signed(value, &mut buf);
                if formatted.len() > CAP {
                    return Err(crate::format::IntegerTooLarge {
                        needed: formatted.len(),
                        capacity: CAP,
                    });
                }
                // SAFETY: digits are always ASCII
                Ok(unsafe { Self::$from_bytes(formatted) })
            }

            /// Formats an `i32` into this string type.
            #[inline]
            pub fn from_i32(value: i32) -> Result<Self, crate::format::IntegerTooLarge> {
                let mut buf = [0u8; 40];
                let formatted = crate::format::format_signed(value, &mut buf);
                if formatted.len() > CAP {
                    return Err(crate::format::IntegerTooLarge {
                        needed: formatted.len(),
                        capacity: CAP,
                    });
                }
                // SAFETY: digits are always ASCII
                Ok(unsafe { Self::$from_bytes(formatted) })
            }

            /// Formats an `i64` into this string type.
            ///
            /// # Example
            ///
            /// ```
            /// # use nexus_ascii::*;
            /// let s: AsciiString<32> = AsciiString::from_i64(-12345678901234)?;
            /// assert_eq!(s.as_str(), "-12345678901234");
            /// # Ok::<(), nexus_ascii::IntegerTooLarge>(())
            /// ```
            #[inline]
            pub fn from_i64(value: i64) -> Result<Self, crate::format::IntegerTooLarge> {
                let mut buf = [0u8; 40];
                let formatted = crate::format::format_signed(value, &mut buf);
                if formatted.len() > CAP {
                    return Err(crate::format::IntegerTooLarge {
                        needed: formatted.len(),
                        capacity: CAP,
                    });
                }
                // SAFETY: digits are always ASCII
                Ok(unsafe { Self::$from_bytes(formatted) })
            }

            /// Formats an `i128` into this string type.
            #[inline]
            pub fn from_i128(value: i128) -> Result<Self, crate::format::IntegerTooLarge> {
                let mut buf = [0u8; 40];
                let formatted = crate::format::format_signed(value, &mut buf);
                if formatted.len() > CAP {
                    return Err(crate::format::IntegerTooLarge {
                        needed: formatted.len(),
                        capacity: CAP,
                    });
                }
                // SAFETY: digits are always ASCII
                Ok(unsafe { Self::$from_bytes(formatted) })
            }

            /// Formats an `isize` into this string type.
            #[inline]
            pub fn from_isize(value: isize) -> Result<Self, crate::format::IntegerTooLarge> {
                let mut buf = [0u8; 40];
                let formatted = crate::format::format_signed(value as i128, &mut buf);
                if formatted.len() > CAP {
                    return Err(crate::format::IntegerTooLarge {
                        needed: formatted.len(),
                        capacity: CAP,
                    });
                }
                // SAFETY: digits are always ASCII
                Ok(unsafe { Self::$from_bytes(formatted) })
            }
        }
    };
}

pub(crate) use impl_format_int_generic;
