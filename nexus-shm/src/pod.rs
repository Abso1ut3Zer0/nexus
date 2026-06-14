/// Marker trait for types safe to place in shared memory.
///
/// # Safety
/// The type must have no heap pointers, no `Drop`, and a stable
/// binary representation (`repr(C)` or `repr(transparent)`).
/// Any bit pattern that fits in `size_of::<Self>()` bytes must be valid.
pub unsafe trait Pod: Sized + 'static {}

unsafe impl Pod for u8 {}
unsafe impl Pod for u16 {}
unsafe impl Pod for u32 {}
unsafe impl Pod for u64 {}
unsafe impl Pod for u128 {}
unsafe impl Pod for i8 {}
unsafe impl Pod for i16 {}
unsafe impl Pod for i32 {}
unsafe impl Pod for i64 {}
unsafe impl Pod for i128 {}
unsafe impl Pod for f32 {}
unsafe impl Pod for f64 {}
/// # Cross-process caveat
///
/// `usize` and `isize` are pointer-width integers. Both ends of an IPC channel
/// must run the same architecture (same pointer width); mixing a 32-bit writer
/// with a 64-bit reader produces wrong values.
unsafe impl Pod for usize {}
unsafe impl Pod for isize {}
unsafe impl<T: Pod, const N: usize> Pod for [T; N] {}
