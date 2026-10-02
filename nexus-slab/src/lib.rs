//! # nexus-slab
//!
//! Pre-allocated slab allocators with pointer-based slot handles.
//!
//! # What Is This?
//!
//! `nexus-slab` provides **bounded** (fixed-capacity) and **unbounded** (growable)
//! slab allocators with 8-byte pointer handles ([`Slot<T>`]). Each allocation
//! returns a raw pointer wrapper that must be explicitly freed — no RAII, no
//! reference counting, just a pointer and a freelist.
//!
//! Use this when you need:
//! - **Stable memory addresses** — pointers remain valid until explicitly freed
//! - **Predictable tail latency** — no reallocation spikes, no allocator contention
//! - **8-byte handles** — half the size of `Box`
//! - **O(1) alloc/free** — freelist-based, no search
//! - **Pinned storage**: [`Slot::into_pinned`] for `!Unpin` values (futures, self-referential structs)
//!
//! If you need a general-purpose slab data structure (insert, get by key, iterate),
//! use the [`slab`](https://crates.io/crates/slab) crate instead.
//!
//! # Quick Start
//!
//! ```
//! use nexus_slab::bounded::Slab;
//!
//! // SAFETY: caller guarantees slab contract (see struct docs)
//! let slab = unsafe { Slab::with_capacity(1024) };
//! let slot = slab.alloc(42u64);
//! assert_eq!(*slot, 42);
//! slab.free(slot);
//! ```
//!
//! # Bounded vs Unbounded
//!
//! - **[`bounded::Slab`]**: Fixed capacity, returns `Err(Full)` when full.
//!   ~20-24 cycle operations, zero allocation after init.
//! - **[`unbounded::Slab`]**: Grows via independent chunks (no copying).
//!   ~40 cycle p999 during growth.
//!
//! # Architecture
//!
//! ## Slot State (SLUB-style union)
//!
//! Each slot is a `repr(C)` union — either a freelist pointer or a value:
//!
//! - **Occupied**: `value` field is active — contains the user's `T`
//! - **Vacant**: `next_free` field is active — points to next free slot (or null)
//!
//! Writing a value implicitly transitions the slot from vacant to occupied
//! (overwrites the freelist pointer). Writing a freelist link transitions it
//! back. There is no tag, no sentinel — the [`Slot`] handle is the proof
//! of occupancy. Zero bookkeeping on the hot path.

#![warn(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(not(any(feature = "std", feature = "alloc")))]
compile_error!("nexus-slab requires either the `std` or `alloc` feature");

#[cfg(feature = "alloc")]
extern crate alloc;

pub mod bounded;
pub mod byte;
#[cfg(feature = "rc")]
pub mod rc;
#[doc(hidden)]
pub mod shared;
pub mod unbounded;

#[cfg(feature = "rc")]
pub use rc::{RcSlot, Ref, RefMut};
pub use shared::{Full, PinnedSlot, Slot, SlotCell};
