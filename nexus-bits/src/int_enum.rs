// nexus-bits/src/int_enum.rs

/// Trait for enums that can be packed into integers.
///
/// Derive this on `#[repr(u8)]` / `#[repr(u16)]` / etc enums:
///
/// TODO - remove ignore once we have macro
/// ```ignore
/// use nexus_bits::IntEnum;
///
/// #[derive(IntEnum, Clone, Copy)]
/// #[repr(u8)]
/// pub enum Exchange {
///     Nasdaq = 0,
///     Nyse = 1,
///     Cboe = 2,
/// }
///
/// let e = Exchange::Nyse;
/// assert_eq!(e.into_repr(), 1u8);
/// assert_eq!(Exchange::try_from_repr(1), Some(Exchange::Nyse));
/// assert_eq!(Exchange::try_from_repr(99), None);
/// ```
pub trait IntEnum: Copy {
    /// The integer representation type (u8, u16, u32, u64, i8, i16, i32, i64).
    type Repr;

    /// Convert to integer representation.
    fn into_repr(self) -> Self::Repr;

    /// Try to convert from integer representation.
    /// Returns `None` for values that don't map to a variant.
    fn try_from_repr(repr: Self::Repr) -> Option<Self>;
}
