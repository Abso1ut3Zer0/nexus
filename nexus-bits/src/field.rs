//! Bit field extraction and packing.

use crate::error::Overflow;

/// A field within a packed integer.
///
/// Defines a contiguous range of bits by start position and length.
/// Precomputes mask for efficient get/set operations.
///
/// # Example
///
/// ```
/// use nexus_bits::BitField;
///
/// const EXCHANGE: BitField<u64> = BitField::<u64>::new(4, 8);  // bits 4-11
///
/// let packed = EXCHANGE.set(0, 42).unwrap();
/// assert_eq!(EXCHANGE.get(packed), 42);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BitField<T> {
    start: u32,
    len: u32,
    mask: T,
}

macro_rules! impl_bitfield {
    ($($ty:ty),*) => {
        $(
            impl BitField<$ty> {
                /// Creates a new field at bit position `start` with width `len`.
                ///
                /// # Panics
                ///
                /// Panics if `len` is 0 or `start + len` exceeds type's bit width.
                #[inline]
                pub const fn new(start: u32, len: u32) -> Self {
                    assert!(len > 0, "field length must be > 0");
                    assert!(start + len <= <$ty>::BITS, "field exceeds integer bounds");

                    let unshifted = if len == <$ty>::BITS {
                        !0
                    } else {
                        (1 << len) - 1
                    };
                    let mask = unshifted << start;

                    Self { start, len, mask }
                }

                /// Start bit position.
                #[inline]
                pub const fn start(self) -> u32 {
                    self.start
                }

                /// Field width in bits.
                #[inline]
                pub const fn len(self) -> u32 {
                    self.len
                }

                /// Mask with 1s in field position.
                #[inline]
                pub const fn mask(self) -> $ty {
                    self.mask
                }

                /// Maximum value this field can hold.
                #[inline]
                pub const fn max_value(self) -> $ty {
                    self.mask >> self.start
                }

                /// Extract field value from packed integer.
                #[inline]
                pub const fn get(self, val: $ty) -> $ty {
                    (val & self.mask) >> self.start
                }

                /// Set field value in packed integer.
                ///
                /// Clears existing bits in field, then sets new value.
                /// Returns error if `field_val` exceeds `max_value()`.
                #[inline]
                pub const fn set(self, val: $ty, field_val: $ty) -> Result<$ty, Overflow<$ty>> {
                    let max = self.max_value();
                    if field_val > max {
                        return Err(Overflow { value: field_val, max });
                    }
                    Ok(self.set_unchecked(val, field_val))
                }

                /// Set field value without bounds checking.
                ///
                /// # Safety
                ///
                /// Caller must ensure `field_val <= max_value()`.
                #[inline]
                pub const fn set_unchecked(self, val: $ty, field_val: $ty) -> $ty {
                    let cleared = val & !self.mask;
                    cleared | (field_val << self.start)
                }

                /// Clear field to zero.
                #[inline]
                pub const fn clear(self, val: $ty) -> $ty {
                    val & !self.mask
                }
            }
        )*
    };
}

impl_bitfield!(u8, u16, u32, u64, u128, i8, i16, i32, i64, i128);
