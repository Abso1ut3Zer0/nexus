/// Marker trait for types safely transmutable from arbitrary byte patterns.
///
/// # Safety
/// The type must have a defined layout for every possible bit pattern
/// within its size. This rules out types with validity invariants such as
/// `bool`, `char`, `NonZero*`, enums with a niche, and references.
pub unsafe trait Pod: Copy + 'static {}

// SAFETY: Primitive integers and floats: no Drop, no heap pointers, no padding;
// every bit pattern within the type's width is a valid value.
unsafe impl Pod for u8 {}
// SAFETY: as above.
unsafe impl Pod for u16 {}
// SAFETY: as above.
unsafe impl Pod for u32 {}
// SAFETY: as above.
unsafe impl Pod for u64 {}
// SAFETY: as above.
unsafe impl Pod for u128 {}
// SAFETY: as above.
unsafe impl Pod for usize {}
// SAFETY: as above.
unsafe impl Pod for i8 {}
// SAFETY: as above.
unsafe impl Pod for i16 {}
// SAFETY: as above.
unsafe impl Pod for i32 {}
// SAFETY: as above.
unsafe impl Pod for i64 {}
// SAFETY: as above.
unsafe impl Pod for i128 {}
// SAFETY: as above.
unsafe impl Pod for isize {}
// SAFETY: as above.
unsafe impl Pod for f32 {}
// SAFETY: as above.
unsafe impl Pod for f64 {}

// SAFETY: [T; N] is N contiguous T values with no padding added by the compiler;
// T: Pod guarantees every bit pattern is valid.
unsafe impl<T: Pod, const N: usize> Pod for [T; N] {}
// SAFETY: () is zero-sized with no fields; trivially satisfies all Pod invariants.
unsafe impl Pod for () {}
