/// Marker trait for types safely transmutable from arbitrary byte patterns.
///
/// # Safety
/// The type must have a defined layout for every possible bit pattern
/// within its size. This rules out types with validity invariants such as
/// `bool`, `char`, `NonZero*`, enums with a niche, and references.
pub unsafe trait Pod: Copy + 'static {}

unsafe impl Pod for u8 {}
unsafe impl Pod for u16 {}
unsafe impl Pod for u32 {}
unsafe impl Pod for u64 {}
unsafe impl Pod for u128 {}
unsafe impl Pod for usize {}
unsafe impl Pod for i8 {}
unsafe impl Pod for i16 {}
unsafe impl Pod for i32 {}
unsafe impl Pod for i64 {}
unsafe impl Pod for i128 {}
unsafe impl Pod for isize {}
unsafe impl Pod for f32 {}
unsafe impl Pod for f64 {}

unsafe impl<T: Pod, const N: usize> Pod for [T; N] {}
unsafe impl Pod for () {}
