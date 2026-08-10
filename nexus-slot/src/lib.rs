//! High-performance conflation slots for latest-value-wins scenarios.
//!
//! Two variants based on reader topology:
//!
//! - [`spsc`] — Single producer, single consumer. Lowest overhead.
//! - [`spmc`] — Single producer, multiple consumers. [`SharedReader`](spmc::SharedReader) is `Clone`.
//!
//! Both use a seqlock internally: the writer increments a sequence counter,
//! copies data via word-at-a-time atomics, and increments again. Readers
//! speculatively copy and retry if the sequence changed.
//!
//! # The `Pod` Trait
//!
//! Types must implement [`Pod`] (Plain Old Data). Every bit pattern within
//! `size_of::<T>()` bytes must be a valid value of the type, and the type
//! must have no padding bytes. This rules out types with validity invariants
//! (`NonZero*`, `char`, `bool`) and padded structs. The no-padding rule is
//! not cosmetic: atomic stores cannot carry uninit bytes, so a padded type
//! cannot be stored through the seqlock without UB no matter how the store
//! is written. The restriction lives at the type level so the store code
//! stays simple and correct.
//!
//! Primitive integers and floats implement [`Pod`] automatically. Arrays of
//! `Pod` types implement [`Pod`] automatically. Other types require a manual
//! `unsafe impl Pod`.
//!
//! ```rust
//! use nexus_slot::Pod;
//!
//! #[repr(C)]
//! struct OrderBook {
//!     bids: [f64; 20],
//!     asks: [f64; 20],
//!     sequence: u64,
//! }
//!
//! // SAFETY: All fields are f64/u64 (8-byte aligned); repr(C) layout adds no
//! // padding between them; every bit pattern is a valid value for each field.
//! unsafe impl Pod for OrderBook {}
//! ```
//!
//! # Examples
//!
//! ```rust
//! #[derive(Clone)]
//! #[repr(C)]
//! struct Quote { bid: f64, ask: f64, seq: u64 }
//!
//! // SAFETY: All fields are f64/u64; repr(C) adds no padding; every bit
//! // pattern is valid for each field.
//! unsafe impl nexus_slot::Pod for Quote {}
//!
//! // SPSC — single reader
//! let (mut writer, mut reader) = nexus_slot::spsc::slot::<Quote>();
//! writer.write(Quote { bid: 100.0, ask: 100.05, seq: 1 });
//! assert_eq!(reader.read().unwrap().seq, 1);
//! ```
//!
//! ```rust
//! #[derive(Clone)]
//! #[repr(C)]
//! struct Quote { bid: f64, ask: f64, seq: u64 }
//!
//! // SAFETY: All fields are f64/u64; repr(C) adds no padding; every bit
//! // pattern is valid for each field.
//! unsafe impl nexus_slot::Pod for Quote {}
//!
//! // SPMC — multiple readers
//! let (mut writer, mut reader1) = nexus_slot::spmc::shared_slot::<Quote>();
//! let mut reader2 = reader1.clone();
//!
//! writer.write(Quote { bid: 100.0, ask: 100.05, seq: 1 });
//! assert!(reader1.read().is_some());
//! assert!(reader2.read().is_some()); // independent consumption
//! ```

#![warn(missing_docs)]

pub(crate) mod loom_impl;
pub mod spmc;
pub mod spsc;

#[cfg(not(loom))]
use std::mem::{MaybeUninit, align_of, size_of};
#[cfg(not(loom))]
use std::sync::atomic::{AtomicU8, AtomicUsize, Ordering};

/// Marker trait for types safe to use in a conflated slot.
///
/// # Safety
///
/// Every bit pattern within `size_of::<Self>()` bytes must be a valid value
/// of this type. This rules out types with validity invariants such as `bool`,
/// `char`, `NonZero*`, and enums with a niche, as well as any type with
/// uninitialised padding bytes.
///
/// The no-padding requirement is not cosmetic: the seqlock stores values
/// word-at-a-time by reading source bytes as `usize` integers. If any of
/// those bytes are uninit padding, reading them as an integer is undefined
/// behaviour. There is no UB-free way to atomically store a type with
/// implicit padding regardless of how the store is implemented, so the
/// constraint belongs at the type level.
///
/// `Copy` alone is not sufficient: a padded `#[repr(C)]` struct is `Copy`
/// but reading its padding bytes as a typed value is undefined behaviour.
/// A `Pod` type must have no padding. Use `#[repr(C)]` and verify that
/// the field layout introduces no gaps.
///
/// Additional requirement (checked at slot creation):
/// `std::mem::needs_drop::<Self>()` must return false.
///
/// # Example
///
/// ```rust
/// use nexus_slot::Pod;
///
/// #[repr(C)]
/// struct Tick {
///     price: f64,
///     qty: f64,
///     seq: u64,
/// }
///
/// // SAFETY: All fields are f64/u64 (8-byte aligned, no padding between
/// // them under repr(C)); every bit pattern is a valid value for each field.
/// unsafe impl Pod for Tick {}
/// ```
pub unsafe trait Pod: Sized {}

// SAFETY: All primitive integer and float types: no Drop, no heap pointers,
// no padding, and every bit pattern within the type's width is a valid value.
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
// SAFETY: [T; N] inherits T's properties; its layout is N contiguous copies
// of T with no padding added by the compiler, so every bit pattern is valid.
unsafe impl<T: Pod, const N: usize> Pod for [T; N] {}

#[cfg(not(loom))]
/// Atomically stores `size_of::<T>()` bytes into shared memory.
///
/// Word-at-a-time `AtomicUsize` stores when alignment permits,
/// `AtomicU8` fallback for tail bytes or poorly-aligned types.
/// All stores use `Relaxed` ordering — caller provides fences.
///
/// # Safety
///
/// - `dst` must be valid for `size_of::<T>()` bytes
/// - `dst` must be aligned to `align_of::<T>()`
/// - `dst` must be derived from `UnsafeCell` (shared-mutable provenance)
#[inline]
pub(crate) unsafe fn atomic_store<T: Pod>(dst: *mut T, src: &T) {
    // SAFETY: Caller guarantees dst is valid, aligned, and from UnsafeCell.
    // Pod bound ensures T has no padding, so reading src bytes as usize
    // values is sound; all bytes are initialised and every bit pattern valid.
    unsafe {
        let dst = dst.cast::<u8>();
        let src = (src as *const T).cast::<u8>();
        let size = size_of::<T>();

        if align_of::<T>() >= align_of::<usize>() {
            let words = size / size_of::<usize>();
            let tail = size % size_of::<usize>();

            for i in 0..words {
                let atom = &*(dst.add(i * size_of::<usize>()) as *const AtomicUsize);
                let val = src.add(i * size_of::<usize>()).cast::<usize>().read();
                atom.store(val, Ordering::Relaxed);
            }

            let base = words * size_of::<usize>();
            for i in 0..tail {
                let atom = &*(dst.add(base + i) as *const AtomicU8);
                atom.store(*src.add(base + i), Ordering::Relaxed);
            }
        } else {
            for i in 0..size {
                let atom = &*(dst.add(i) as *const AtomicU8);
                atom.store(*src.add(i), Ordering::Relaxed);
            }
        }
    }
}

#[cfg(not(loom))]
/// Atomically loads `size_of::<T>()` bytes from shared memory.
///
/// Word-at-a-time `AtomicUsize` loads when alignment permits,
/// `AtomicU8` fallback for tail bytes or poorly-aligned types.
/// All loads use `Relaxed` ordering — caller provides fences.
///
/// Returns `MaybeUninit<T>`. The caller must call `assume_init` only after
/// the seqlock confirms seq1 == seq2, ensuring the bytes form a complete,
/// coherent value written by the writer.
///
/// # Safety
///
/// - `src` must be valid for `size_of::<T>()` bytes
/// - `src` must be aligned to `align_of::<T>()`
/// - `src` must be derived from `UnsafeCell` (shared-mutable provenance)
#[inline]
pub(crate) unsafe fn atomic_load<T: Pod>(src: *const T) -> MaybeUninit<T> {
    // SAFETY: Caller guarantees src is valid, aligned, and from UnsafeCell.
    // All size_of::<T>() bytes of buf are written before returning.
    // Callers must call assume_init only after the seqlock confirms seq1==seq2,
    // which guarantees the bytes form a valid T written by the writer.
    unsafe {
        let mut buf = MaybeUninit::<T>::uninit();
        let dst = buf.as_mut_ptr().cast::<u8>();
        let src = src.cast::<u8>();
        let size = size_of::<T>();

        if align_of::<T>() >= align_of::<usize>() {
            let words = size / size_of::<usize>();
            let tail = size % size_of::<usize>();

            for i in 0..words {
                let atom = &*(src.add(i * size_of::<usize>()) as *const AtomicUsize);
                let val = atom.load(Ordering::Relaxed);
                dst.add(i * size_of::<usize>()).cast::<usize>().write(val);
            }

            let base = words * size_of::<usize>();
            for i in 0..tail {
                let atom = &*(src.add(base + i) as *const AtomicU8);
                *dst.add(base + i) = atom.load(Ordering::Relaxed);
            }
        } else {
            for i in 0..size {
                let atom = &*(src.add(i) as *const AtomicU8);
                *dst.add(i) = atom.load(Ordering::Relaxed);
            }
        }

        buf
    }
}
