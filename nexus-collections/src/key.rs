//! Key trait for storage indices.
//!
//! The [`Key`] trait abstracts over index types used in storage.
//! It provides a sentinel value (`NONE`) and conversion to/from `usize`.

/// Trait for key/index types used in storage.
///
/// Provides a sentinel value (`NONE`) and conversion to/from `usize`.
/// Implemented for common integer types and can be implemented for
/// custom key types (e.g., strongly-typed order IDs).
///
/// # Example
///
/// ```
/// use nexus_collections::Key;
///
/// // u32 is a Key with NONE = u32::MAX
/// let key: u32 = 42;
/// assert!(!key.is_none());
/// assert!(u32::NONE.is_none());
/// ```
///
/// # Custom Key Types
///
/// ```
/// use nexus_collections::Key;
/// use std::hash::Hash;
///
/// #[derive(Copy, Clone, PartialEq, Eq, Hash)]
/// struct OrderId(u64);
///
/// impl Key for OrderId {
///     const NONE: Self = OrderId(u64::MAX);
///
///     fn from_usize(val: usize) -> Self {
///         OrderId(val as u64)
///     }
///
///     fn as_usize(&self) -> usize {
///         self.0 as usize
///     }
///
///     fn is_none(&self) -> bool {
///         self.0 == u64::MAX
///     }
/// }
/// ```
pub trait Key: Copy + Eq {
    /// Sentinel value representing "no key" / "null".
    ///
    /// Used internally to represent empty links in data structures.
    /// For integer types, this is typically `MAX` (e.g., `u32::MAX`).
    const NONE: Self;

    /// Creates a key from a `usize` value.
    ///
    /// Used when storage assigns sequential indices.
    fn from_usize(val: usize) -> Self;

    /// Returns the key as a `usize`.
    ///
    /// Used for indexing into arrays and bounds checking.
    fn as_usize(&self) -> usize;

    /// Returns `true` if this is the sentinel value.
    #[inline]
    fn is_none(&self) -> bool {
        *self == Self::NONE
    }

    /// Returns `true` if this is NOT the sentinel value.
    #[inline]
    fn is_some(&self) -> bool {
        !self.is_none()
    }
}

// =============================================================================
// Implementations for integer types
// =============================================================================

impl Key for u8 {
    const NONE: Self = u8::MAX;

    #[inline]
    fn from_usize(val: usize) -> Self {
        val as u8
    }

    #[inline]
    fn as_usize(&self) -> usize {
        *self as usize
    }
}

impl Key for u16 {
    const NONE: Self = u16::MAX;

    #[inline]
    fn from_usize(val: usize) -> Self {
        val as u16
    }

    #[inline]
    fn as_usize(&self) -> usize {
        *self as usize
    }
}

impl Key for u32 {
    const NONE: Self = u32::MAX;

    #[inline]
    fn from_usize(val: usize) -> Self {
        val as u32
    }

    #[inline]
    fn as_usize(&self) -> usize {
        *self as usize
    }
}

impl Key for u64 {
    const NONE: Self = u64::MAX;

    #[inline]
    fn from_usize(val: usize) -> Self {
        val as u64
    }

    #[inline]
    fn as_usize(&self) -> usize {
        *self as usize
    }
}

impl Key for usize {
    const NONE: Self = usize::MAX;

    #[inline]
    fn from_usize(val: usize) -> Self {
        val
    }

    #[inline]
    fn as_usize(&self) -> usize {
        *self
    }
}

#[cfg(feature = "nexus-slab")]
impl Key for nexus_slab::Key {
    const NONE: Self = unsafe { nexus_slab::Key::from_raw(u32::MAX) };

    #[inline]
    fn from_usize(val: usize) -> Self {
        unsafe { nexus_slab::Key::from_raw(val as u32) }
    }

    #[inline]
    fn as_usize(&self) -> usize {
        self.index() as usize
    }

    #[inline]
    fn is_none(&self) -> bool {
        self.index() == u32::MAX
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn u32_key_basics() {
        let key: u32 = 42;
        assert!(!key.is_none());
        assert!(key.is_some());
        assert_eq!(key.as_usize(), 42);

        assert!(u32::NONE.is_none());
        assert!(!u32::NONE.is_some());
    }

    #[test]
    fn from_usize_roundtrip() {
        for i in [0usize, 1, 100, 1000, u16::MAX as usize] {
            let key = u32::from_usize(i);
            assert_eq!(key.as_usize(), i);
        }
    }

    #[test]
    fn none_values() {
        assert_eq!(u8::NONE, u8::MAX);
        assert_eq!(u16::NONE, u16::MAX);
        assert_eq!(u32::NONE, u32::MAX);
        assert_eq!(u64::NONE, u64::MAX);
        assert_eq!(usize::NONE, usize::MAX);
    }
}
