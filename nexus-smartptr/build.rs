//! Build-time validation of fat pointer layout.
//!
//! Asserts that rustc lays out fat pointers as `(data, metadata)`.
//! This is a compiler property, not a target property — the same rustc
//! uses the same ordering for all targets. Safe to run on host even
//! when cross-compiling.
//!
//! Approach borrowed from [smallbox](https://github.com/andylokandy/smallbox).

use std::ptr;

#[allow(dead_code)]
trait Probe {
    fn probe(&self);
}

struct ProbeImpl;
impl Probe for ProbeImpl {
    fn probe(&self) {}
}

#[repr(C)]
struct FatPtr {
    data: *const u8,
    meta: *const u8,
}

#[repr(C)]
struct SlicePtr {
    data: *const u8,
    len: usize,
}

fn main() {
    // Trait object: data pointer must be the first word.
    let val = ProbeImpl;
    let data_ptr: *const u8 = &raw const val as *const u8;
    let trait_ptr: *const dyn Probe = &val as &dyn Probe;

    // SAFETY: trait_ptr is a valid local reference; ptr::read copies its bytes to inspect fat pointer layout.
    let decomposed: FatPtr = unsafe { ptr::read(ptr::addr_of!(trait_ptr).cast::<FatPtr>()) };

    assert!(
        decomposed.data == data_ptr,
        "nexus-smartptr: trait object layout is not (data, vtable). \
         This compiler is not supported."
    );

    // Slice: data pointer first, length second.
    let array = [1_u8, 2, 3];
    let slice: &[u8] = &array;
    // SAFETY: slice is a valid local reference; ptr::read copies its bytes to inspect fat pointer layout.
    let slice_repr: SlicePtr = unsafe { ptr::read(ptr::addr_of!(slice).cast::<SlicePtr>()) };

    assert!(
        slice_repr.data == slice.as_ptr() && slice_repr.len == slice.len(),
        "nexus-smartptr: slice layout is not (data, len). \
         This compiler is not supported."
    );
}
