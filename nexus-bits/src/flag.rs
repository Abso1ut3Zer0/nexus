//! Single-bit flag extraction and packing.

/// A single-bit flag within a packed integer.
///
/// Simpler than `BitField` for boolean flags - no overflow checking needed.
///
/// # Example
///
/// ```
/// use nexus_bits::Flag;
///
/// const IS_BUY: Flag<u64> = Flag::<u64>::new(0);
/// const IS_IOC: Flag<u64> = Flag::<u64>::new(1);
///
/// let mut flags: u64 = 0;
/// flags = IS_BUY.set(flags);
/// flags = IS_IOC.set(flags);
///
/// assert!(IS_BUY.is_set(flags));
/// assert!(IS_IOC.is_set(flags));
///
/// flags = IS_IOC.clear(flags);
/// assert!(!IS_IOC.is_set(flags));
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Flag<T> {
    bit: u32,
    mask: T,
}

macro_rules! impl_flag {
    ($($ty:ty),*) => {
        $(
            impl Flag<$ty> {
                /// Creates a flag at bit position `bit`.
                ///
                /// # Panics
                ///
                /// Panics if `bit` >= type's bit width.
                #[inline]
                pub const fn new(bit: u32) -> Self {
                    assert!(bit < <$ty>::BITS, "bit position exceeds integer bounds");
                    let mask = 1 << bit;
                    Self { bit, mask }
                }

                /// Bit position.
                #[inline]
                pub const fn bit(self) -> u32 {
                    self.bit
                }

                /// Mask with 1 at flag position.
                #[inline]
                pub const fn mask(self) -> $ty {
                    self.mask
                }

                /// Returns true if flag is set.
                #[inline]
                pub const fn is_set(self, val: $ty) -> bool {
                    (val & self.mask) != 0
                }

                /// Set flag to 1.
                #[inline]
                pub const fn set(self, val: $ty) -> $ty {
                    val | self.mask
                }

                /// Set flag to 0.
                #[inline]
                pub const fn clear(self, val: $ty) -> $ty {
                    val & !self.mask
                }

                /// Flip flag.
                #[inline]
                pub const fn toggle(self, val: $ty) -> $ty {
                    val ^ self.mask
                }

                /// Set flag to given boolean value.
                #[inline]
                pub const fn set_to(self, val: $ty, enabled: bool) -> $ty {
                    if enabled {
                        self.set(val)
                    } else {
                        self.clear(val)
                    }
                }
            }
        )*
    };
}

impl_flag!(u8, u16, u32, u64, u128, i8, i16, i32, i64, i128);
