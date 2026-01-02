//! Sentinel-based index trait for zero-cost optional indices.
//!
//! Uses a reserved sentinel value (e.g., `usize::MAX`) instead of `Option<Idx>`
//! to save space in node-based data structures.

/// A copyable index type with a sentinel "none" value.
///
/// # Example
///
/// ```
/// use nexus_collections::Index;
///
/// let idx: u32 = 5;
/// let none: u32 = u32::NONE;
///
/// assert!(idx.is_some());
/// assert!(none.is_none());
/// ```
pub trait Index: Copy + Eq {
    /// Sentinel value representing "no index" / null.
    const NONE: Self;

    /// Returns `true` if this is the sentinel value.
    #[inline]
    fn is_none(self) -> bool {
        self == Self::NONE
    }

    /// Returns `true` if this is not the sentinel value.
    #[inline]
    fn is_some(self) -> bool {
        !self.is_none()
    }

    fn as_usize(self) -> usize;

    fn from_usize(val: usize) -> Self;
}

macro_rules! impl_index_for_unsigned {
    ($($ty:ty),*) => {
        $(
            impl Index for $ty {
                const NONE: Self = <$ty>::MAX;

                #[inline]
                fn as_usize(self) -> usize {
                    self as usize
                }

                #[inline]
                fn from_usize(val: usize) -> Self {
                    val as Self
                }
            }
        )*
    };
}

impl_index_for_unsigned!(u8, u16, u32, u64, usize);

#[cfg(feature = "nexus-slab")]
impl Index for nexus_slab::Key {
    // SAFETY: u32::MAX is reserved as sentinel, never a valid slab index
    const NONE: Self = unsafe { nexus_slab::Key::from_raw(u32::MAX) };

    #[inline]
    fn as_usize(self) -> usize {
        self.index() as usize
    }

    #[inline]
    fn from_usize(val: usize) -> Self {
        unsafe { nexus_slab::Key::from_raw(val as u32) }
    }
}

#[cfg(all(test, feature = "nexus-slab"))]
mod nexus_slab_tests {
    use super::*;

    #[test]
    fn key_sentinel() {
        assert!(nexus_slab::Key::NONE.is_none());
        assert!(!nexus_slab::Key::NONE.is_some());

        let valid = unsafe { nexus_slab::Key::from_raw(0) };
        assert!(valid.is_some());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! test_index_sentinel {
        ($($ty:ty => $name:ident),*) => {
            $(
                #[test]
                fn $name() {
                    assert!(<$ty>::NONE.is_none());
                    assert!(!<$ty>::NONE.is_some());
                    assert!((0 as $ty).is_some());
                    assert!((<$ty>::MAX - 1).is_some());
                }
            )*
        };
    }

    test_index_sentinel!(
        u8 => u8_sentinel,
        u16 => u16_sentinel,
        u32 => u32_sentinel,
        u64 => u64_sentinel,
        usize => usize_sentinel
    );
}
