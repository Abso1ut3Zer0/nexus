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
//! Regression tests for BUG-1 (#167): slab tasks surviving past
//! `block_on` are freed cleanly when the `Runtime` is dropped.
//!
//! Before the architectural fix, these tests panicked with
//! "slab free called without a slab configured" because slab TLS was
//! scoped to `run_loop` and cleared before `Executor::drop` could free
//! surviving slab tasks via the TLS dispatch path.
//!
//! After the fix (slab TLS installed at Runtime construction, restored
//! when the Runtime drops via field-order RAII on `_slab_guard`),
//! surviving slab tasks free cleanly during the normal drop sequence.

use nexus_async_rt::{Runtime, spawn_slab};
use nexus_rt::WorldBuilder;

#[test]
fn slab_task_uncompleted_at_runtime_drop_no_panic() {
    // SAFETY: single-threaded runtime.
    let slab = unsafe { nexus_slab::byte::unbounded::Slab::<256>::with_chunk_capacity(8) };
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::builder(&mut world).slab_unbounded(slab).build();

    // Spawn a slab task that never completes, drop handle immediately.
    // Root future returns right away — the slab task is in executor.all_tasks
    // but never ran.
    rt.block_on(async {
        drop(spawn_slab(async move {
            std::future::pending::<()>().await;
        }));
    });

    // Pre-fix: this panicked. Post-fix: clean — TLS still installed
    // when Executor::drop frees the surviving slab task.
    drop(rt);
}

#[test]
#[allow(clippy::async_yields_async)] // Intentional: returning the unawaited
// JoinHandle so we can drop it outside block_on and exercise BUG-1's path.
fn slab_handle_dropped_outside_block_on_no_panic() {
    // SAFETY: single-threaded runtime.
    let slab = unsafe { nexus_slab::byte::unbounded::Slab::<256>::with_chunk_capacity(8) };
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::builder(&mut world).slab_unbounded(slab).build();

    // Return the JoinHandle from block_on — task hasn't completed.
    let handle = rt.block_on(async { spawn_slab(async { 42u32 }) });

    // JoinHandle::Drop: task not completed → don't drop output.
    // clear_has_join, ref_dec → refcount 1, Retain. Task still in all_tasks.
    drop(handle);

    // Pre-fix: Executor::drop frees the task → free_task → TLS null → PANIC.
    // Post-fix: TLS still installed → frees correctly into the slab.
    drop(rt);
}

#[test]
fn many_slab_tasks_at_varying_lifecycle_states() {
    // SAFETY: single-threaded runtime.
    let slab = unsafe { nexus_slab::byte::unbounded::Slab::<256>::with_chunk_capacity(64) };
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::builder(&mut world).slab_unbounded(slab).build();

    let held = rt.block_on(async {
        // Group 1: completes during block_on.
        for i in 0..16i32 {
            let h = spawn_slab(async move { i });
            assert_eq!(h.await, i);
        }
        // Group 2: handle dropped, never completes.
        for _i in 0..16 {
            drop(spawn_slab(async {
                std::future::pending::<()>().await;
            }));
        }
        // Group 3: handle held outside block_on. Returned out of the
        // async block so it borrows nothing from the surrounding scope
        // (block_on requires F: 'static).
        let mut held = Vec::new();
        for i in 0..8i32 {
            held.push(spawn_slab(async move {
                std::future::pending::<i32>().await;
                i
            }));
        }
        held
    });

    // Drop handles after block_on — must not panic.
    drop(held);
    // Final drop — must not panic.
    drop(rt);
}

#[test]
fn no_slab_no_panic() {
    // Regression: ensure the no-slab path (Box-only tasks) still works.
    // _slab_guard is None, no TLS install, no Drop side effect.
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::builder(&mut world).build();

    rt.block_on(async {});
    drop(rt);
}

#[test]
fn slab_task_completed_during_block_on() {
    // Path where the bug never fired (TLS held during free during run_loop).
    // Confirm the new lifecycle doesn't break it.
    // SAFETY: single-threaded runtime.
    let slab = unsafe { nexus_slab::byte::unbounded::Slab::<256>::with_chunk_capacity(8) };
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::builder(&mut world).slab_unbounded(slab).build();

    let result = rt.block_on(async { spawn_slab(async { 100u32 }).await });
    assert_eq!(result, 100);

    drop(rt);
}

#[test]
fn multiple_block_on_with_slab_tasks() {
    // Multiple block_on calls on the same Runtime. TLS is installed
    // once at construction; block_on no longer manages it, so calls
    // across separate block_on invocations all see the same slab.
    // SAFETY: single-threaded runtime.
    let slab = unsafe { nexus_slab::byte::unbounded::Slab::<256>::with_chunk_capacity(8) };
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let mut rt = Runtime::builder(&mut world).slab_unbounded(slab).build();

    let r1 = rt.block_on(async { spawn_slab(async { 1u32 }).await });
    let r2 = rt.block_on(async { spawn_slab(async { 2u32 }).await });
    assert_eq!(r1, 1);
    assert_eq!(r2, 2);

    drop(rt);
}

#[test]
#[should_panic(expected = "another Runtime is already alive on this thread")]
fn second_runtime_on_same_thread_panics() {
    // Runtime presence guard: only one Runtime per thread allowed.
    // Constructing a second one with the first still alive must panic.
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    let _rt1 = Runtime::builder(&mut world).build();
    let _rt2 = Runtime::builder(&mut world).build(); // panics here
}

#[test]
fn runtime_construct_drop_construct_works() {
    // After dropping the first Runtime, constructing another on the
    // same thread must succeed — the presence flag is cleared on drop.
    let wb = WorldBuilder::new();
    let mut world = wb.build();
    {
        let _rt1 = Runtime::builder(&mut world).build();
    } // _rt1 dropped here, presence flag cleared
    let _rt2 = Runtime::builder(&mut world).build(); // must NOT panic
}
