//! Pointer metadata decomposition.
//!
//! All pointer surgery in this crate is isolated here. Handles both:
//! - **Fat pointers** (`dyn Trait`, `[T]`): `(data_ptr, vtable/len)` — extract
//!   and reconstruct the metadata word.
//! - **Thin pointers** (`Sized` types): no metadata, just the data pointer.
//!
//! Read/write pointer words directly via `ptr::read`/`ptr::write` to preserve
//! provenance. Never round-trips through `usize`.
//!
//! Note: relies on the de facto stable fat pointer layout `(data, metadata)`.
//! `core::ptr::metadata` / `from_raw_parts` would be preferable but remain
//! unstable (`ptr_metadata`, tracking issue #81513). Migrate when stabilized.

use core::mem::{self, size_of};

// Compile-time assertion (runs for the target): fat pointers must be exactly
// two pointer-sized words. If this fails, the target has an unexpected pointer
// layout and the decomposition logic is unsound.
const _: () = assert!(
    size_of::<*const dyn core::fmt::Display>() == 2 * size_of::<usize>(),
    "nexus-smartptr: fat pointers must be exactly 2 words (data + metadata)"
);

/// Opaque pointer metadata.
///
/// For fat pointers: stores the vtable pointer (trait objects) or length (slices).
/// For thin pointers: null (unused but harmless).
/// Preserves pointer provenance.
#[derive(Clone, Copy)]
pub(crate) struct Metadata(pub(crate) *const ());

impl Metadata {
    /// Null metadata for Sized types (no vtable/length).
    pub(crate) const NULL: Self = Metadata(core::ptr::null());
}

/// Returns `true` if `*const T` is a fat pointer (2 words).
#[inline(always)]
pub(crate) const fn is_fat_ptr<T: ?Sized>() -> bool {
    size_of::<*const T>() > size_of::<usize>()
}

/// Extracts the metadata from a fat pointer.
///
/// For thin pointers (Sized types), returns [`Metadata::NULL`].
/// For fat pointers (?Sized types), returns the vtable/length word.
#[inline]
pub(crate) fn extract_metadata<T: ?Sized>(ptr: *const T) -> Metadata {
    if !is_fat_ptr::<T>() {
        return Metadata::NULL;
    }
    // SAFETY: T is ?Sized and we verified it's a fat pointer, laid out as
    // [data_ptr, metadata_ptr]. We read the second word as a pointer to
    // preserve provenance.
    let words = core::ptr::addr_of!(ptr).cast::<*const ()>();
    // SAFETY: verified fat pointer above; second word is the metadata pointer.
    let metadata = unsafe { words.add(1).read() };
    Metadata(metadata)
}

/// Reconstructs a `*const T` from a data address and metadata.
///
/// For Sized T: returns `data` cast to `*const T` (metadata ignored).
/// For ?Sized T: builds a fat pointer from `data` + `meta`.
///
/// # Safety
///
/// - `data` must be a valid pointer for the intended operation.
/// - For ?Sized T: `meta` must have been extracted from a pointer to the
///   same concrete type that will be accessed through the returned pointer.
#[inline(always)]
pub(crate) unsafe fn make_ptr<T: ?Sized>(data: *const (), meta: Metadata) -> *const T {
    let mut result: mem::MaybeUninit<*const T> = mem::MaybeUninit::uninit();
    let words = result.as_mut_ptr().cast::<*const ()>();
    // SAFETY: MaybeUninit<*const T> is written word-by-word; caller upholds data/meta validity.
    unsafe {
        words.write(data);
        if is_fat_ptr::<T>() {
            // SAFETY: Fat pointer — write metadata as second word.
            // Caller guarantees data and meta are compatible.
            words.add(1).write(meta.0);
        }
        result.assume_init()
    }
}

/// Reconstructs a `*mut T` from a data address and metadata.
///
/// # Safety
///
/// Same requirements as [`make_ptr`], plus `data` must be valid for writes.
#[inline(always)]
pub(crate) unsafe fn make_ptr_mut<T: ?Sized>(data: *mut (), meta: Metadata) -> *mut T {
    // SAFETY: *const T and *mut T have identical layout.
    unsafe { make_ptr::<T>(data.cast_const(), meta).cast_mut() }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::fmt::Display;

    #[test]
    fn roundtrip_trait_object() {
        let val: u64 = 42;
        let trait_ptr: *const dyn Display = &val as &dyn Display;

        let meta = extract_metadata(trait_ptr);
        let data = &raw const val as *const ();

        // SAFETY: data points to val, meta extracted from same concrete type.
        let reconstructed: *const dyn Display = unsafe { make_ptr(data, meta) };

        // SAFETY: trait_ptr is a valid reference to val.
        let original = unsafe { &*trait_ptr };
        // SAFETY: reconstructed points to val with the correct vtable.
        let recovered = unsafe { &*reconstructed };
        assert_eq!(format!("{original}"), format!("{recovered}"));
    }

    #[test]
    fn roundtrip_mut_trait_object() {
        use core::fmt::Debug;

        let mut val: Vec<u8> = vec![1, 2, 3];
        let trait_ptr: *mut dyn Debug = &mut val as &mut dyn Debug;

        let meta = extract_metadata(trait_ptr as *const dyn Debug);
        let data = &raw mut val as *mut ();

        // SAFETY: data points to val, meta from same concrete type.
        let reconstructed: *mut dyn Debug = unsafe { make_ptr_mut(data, meta) };
        // SAFETY: reconstructed points to val with the correct vtable.
        let recovered = unsafe { &*reconstructed };
        assert_eq!(format!("{recovered:?}"), "[1, 2, 3]");
    }

    #[test]
    fn thin_pointer_roundtrip() {
        let val: u64 = 99;
        let meta = extract_metadata(&raw const val);
        let data = &raw const val as *const ();

        // SAFETY: data points to val. For Sized T, meta is ignored.
        let reconstructed: *const u64 = unsafe { make_ptr(data, meta) };
        // SAFETY: reconstructed points to val, a valid u64.
        assert_eq!(unsafe { *reconstructed }, 99);
    }

    #[test]
    fn thin_pointer_null_metadata() {
        let val: u32 = 7;
        let meta = extract_metadata(&raw const val);
        assert!(meta.0.is_null());
    }

    #[test]
    fn metadata_is_copy() {
        let val: u32 = 7;
        let ptr: *const dyn Display = &val as &dyn Display;
        let meta = extract_metadata(ptr);
        let copy = meta;
        let another = meta;
        assert_eq!(copy.0, another.0);
    }

    #[test]
    fn different_data_same_vtable() {
        let a: u64 = 100;
        let b: u64 = 200;
        let meta = extract_metadata(&a as &dyn Display as *const dyn Display);

        // SAFETY: both a and b are u64, meta extracted from u64's Display vtable.
        let ptr_a: *const dyn Display = unsafe { make_ptr(&raw const a as *const (), meta) };
        // SAFETY: b is u64; meta extracted from u64's Display vtable, compatible.
        let ptr_b: *const dyn Display = unsafe { make_ptr(&raw const b as *const (), meta) };

        // SAFETY: ptr_a points to a, a valid u64.
        assert_eq!(format!("{}", unsafe { &*ptr_a }), "100");
        // SAFETY: ptr_b points to b, a valid u64.
        assert_eq!(format!("{}", unsafe { &*ptr_b }), "200");
    }

    #[test]
    fn roundtrip_slice() {
        let val: [u32; 4] = [10, 20, 30, 40];
        let slice: &[u32] = &val;
        let slice_ptr: *const [u32] = slice as *const [u32];

        let meta = extract_metadata(slice_ptr);
        let data = val.as_ptr() as *const ();

        // SAFETY: data points to val, meta carries the slice length.
        let reconstructed: *const [u32] = unsafe { make_ptr(data, meta) };
        // SAFETY: reconstructed points to val with the correct length metadata.
        let recovered = unsafe { &*reconstructed };
        assert_eq!(recovered.len(), 4);
        assert_eq!(recovered, &[10, 20, 30, 40]);
    }

    #[test]
    fn is_fat_ptr_correct() {
        assert!(!is_fat_ptr::<u64>());
        assert!(!is_fat_ptr::<String>());
        assert!(is_fat_ptr::<dyn Display>());
        assert!(is_fat_ptr::<[u8]>());
    }
}
