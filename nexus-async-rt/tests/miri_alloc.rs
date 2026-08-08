#![allow(
    unused_must_use,
    unused_imports,
    dead_code,
    unknown_lints,
    clippy::float_cmp,
    clippy::ref_option,
    clippy::used_underscore_binding,
    clippy::redundant_locals,
    clippy::semicolon_if_nothing_returned,
    clippy::let_underscore_future,
    clippy::while_let_loop,
    clippy::needless_continue,
    clippy::match_wild_err_arm,
    clippy::collection_is_never_read,
    clippy::async_yields_async,
    clippy::match_same_arms
)]
//! Miri tests for slab task allocation.
//!
//! Exercises slab_spawn copy_nonoverlapping, slab_free_fn, and
//! bounded slab exhaustion paths under miri.
//!
//! **Requires tree borrows.** The slab's Cell<*mut SlotCell<T>> freelist
//! triggers a known stacked borrows false positive when accessed through
//! a type-erased TLS pointer round-trip (*const u8 → *const Slab → &Slab).
//! Tree borrows handles the Cell/UnsafeCell interaction correctly.
//!
//! Run: `MIRIFLAGS="-Zmiri-tree-borrows -Zmiri-ignore-leaks" cargo +nightly miri test -p nexus-async-rt --test miri_alloc`

use std::cell::Cell;
use std::rc::Rc;

use nexus_async_rt::{Runtime, spawn_slab};
use nexus_rt::WorldBuilder;

// =============================================================================
// Tests
// =============================================================================

#[test]
fn slab_spawn_and_free() {
    // Configure unbounded slab, spawn 10 tasks via spawn_slab, complete all.
    // Tasks are detached (handle dropped) so free_task fires inline during
    // poll — before the slab TLS guard drops.
    // SAFETY: single-threaded runtime.
    let slab = unsafe { nexus_slab::byte::unbounded::Slab::<256>::with_chunk_capacity(16) };
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::builder(&mut world).slab_unbounded(slab).build();

    let done = Rc::new(Cell::new(0u32));
    let d = done.clone();
    rt.block_on(async move {
        for i in 0..10u64 {
            let d = d.clone();
            // Drop handle immediately — task is detached/fire-and-forget.
            // complete_task frees inline (no deferred path).
            drop(spawn_slab(async move {
                let _ = i * 2;
                d.set(d.get() + 1);
            }));
        }

        // Yield to let all tasks run and get freed.
        nexus_async_rt::yield_now().await;
    });
    assert_eq!(done.get(), 10);
}

#[test]
fn slab_spawn_with_drop_tracker() {
    // Verify slab-spawned tasks drop their captures.
    let count = Rc::new(Cell::new(0u32));
    // SAFETY: single-threaded runtime.
    let slab = unsafe { nexus_slab::byte::unbounded::Slab::<256>::with_chunk_capacity(8) };
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::builder(&mut world).slab_unbounded(slab).build();

    struct DropCounter(Rc<Cell<u32>>);
    impl Drop for DropCounter {
        fn drop(&mut self) {
            self.0.set(self.0.get() + 1);
        }
    }

    let cnt = count.clone();
    rt.block_on(async move {
        for _ in 0..5 {
            let c = DropCounter(cnt.clone());
            drop(spawn_slab(async move {
                let _keep = c;
            }));
        }
        nexus_async_rt::yield_now().await;
    });

    assert_eq!(count.get(), 5, "5 slab tasks = 5 drops");
}

#[test]
fn slab_claim_and_spawn() {
    // Use claim_slab() → SlabClaim → .spawn(future).
    // Detach the handle so free fires inline.
    // SAFETY: single-threaded runtime.
    let slab = unsafe { nexus_slab::byte::unbounded::Slab::<256>::with_chunk_capacity(8) };
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::builder(&mut world).slab_unbounded(slab).build();

    let done = Rc::new(Cell::new(false));
    let d = done.clone();
    rt.block_on(async move {
        let claim = nexus_async_rt::claim_slab();
        let handle = claim.spawn(async move {
            d.set(true);
        });
        drop(handle); // detach
        nexus_async_rt::yield_now().await;
    });
    assert!(done.get());
}

// Bounded slab variant — same provenance fix applied.
#[test]
fn slab_bounded_reuse_after_free() {
    // Configure bounded slab with 4 slots. Spawn 4 tasks, complete them,
    // then spawn 4 more (reusing freed slots).
    // SAFETY: single-threaded runtime.
    let slab = unsafe { nexus_slab::byte::bounded::Slab::<256>::with_capacity(4) };
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::builder(&mut world).slab_bounded(slab).build();

    let done = Rc::new(Cell::new(0u32));
    let d = done.clone();
    rt.block_on(async move {
        // First batch — fill all 4 slots.
        for i in 0..4u64 {
            let d = d.clone();
            drop(spawn_slab(async move {
                let _ = i;
                d.set(d.get() + 1);
            }));
        }
        // Yield to let tasks run and free slots.
        nexus_async_rt::yield_now().await;

        // Second batch — reuse freed slots.
        for i in 0..4u64 {
            let d = d.clone();
            drop(spawn_slab(async move {
                let _ = i + 100;
                d.set(d.get() + 1);
            }));
        }
        nexus_async_rt::yield_now().await;
    });
    assert_eq!(done.get(), 8);
}
