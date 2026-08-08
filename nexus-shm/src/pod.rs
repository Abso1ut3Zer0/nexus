/// Marker trait for types safe to place in shared memory.
///
/// # Safety
/// The type must have no heap pointers, no `Drop`, and a stable
/// binary representation (`repr(C)` or `repr(transparent)`).
/// Any bit pattern that fits in `size_of::<Self>()` bytes must be valid.
pub unsafe trait Pod: Sized + 'static {}

// SAFETY: All primitive integer and float types are `Copy` (no `Drop`), contain
// no heap pointers, have a stable platform-defined representation with no
// padding, and every bit pattern within the type's width is a valid value.
unsafe impl Pod for u8 {}
// SAFETY: same as u8.
unsafe impl Pod for u16 {}
// SAFETY: same as u8.
unsafe impl Pod for u32 {}
// SAFETY: same as u8.
unsafe impl Pod for u64 {}
// SAFETY: same as u8.
unsafe impl Pod for u128 {}
// SAFETY: same as u8.
unsafe impl Pod for i8 {}
// SAFETY: same as u8.
unsafe impl Pod for i16 {}
// SAFETY: same as u8.
unsafe impl Pod for i32 {}
// SAFETY: same as u8.
unsafe impl Pod for i64 {}
// SAFETY: same as u8.
unsafe impl Pod for i128 {}
// SAFETY: same as u8.
unsafe impl Pod for f32 {}
// SAFETY: same as u8.
unsafe impl Pod for f64 {}
/// # Cross-process caveat
///
/// `usize` and `isize` are pointer-width integers. Both ends of an IPC channel
/// must run the same architecture (same pointer width); mixing a 32-bit writer
/// with a 64-bit reader produces wrong values.
// SAFETY: `usize`/`isize` satisfy all `Pod` requirements: `Copy`, no heap
// pointers, stable repr, every bit pattern valid. The cross-process caveat
// above is a correctness concern for callers, not a soundness issue for `Pod`.
unsafe impl Pod for usize {}
// SAFETY: same as usize; Copy, no heap pointers, stable repr, all bit patterns valid.
unsafe impl Pod for isize {}
// SAFETY: `T: Pod` guarantees T has no heap pointers, no `Drop`, a stable
// repr, and every bit pattern is valid. A fixed-size array `[T; N]` inherits
// all these properties; its layout is N contiguous copies of T with no padding
// added by the compiler.
unsafe impl<T: Pod, const N: usize> Pod for [T; N] {}
