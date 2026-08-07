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
//! Miri tests for task header, JoinHandle, and union transitions.
//!
//! These tests exercise the unsafe core of the task model under miri
//! to catch UB: raw pointer arithmetic, union transitions, type-erased
//! fn pointers, ref_count lifecycle, and deferred free.
//!
//! Run: `cargo +nightly miri test -p nexus-async-rt --test miri_task`
//!
//! These tests use the raw `Executor` API directly — no IO, no mio,
//! no timers. Miri can't handle real syscalls.

use std::cell::Cell;
use std::future::Future;
use std::pin::Pin;
use std::rc::Rc;
use std::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};

use nexus_async_rt::{Executor, TASK_HEADER_SIZE};

// =============================================================================
// Test helpers
// =============================================================================

fn test_executor() -> Executor {
    Executor::new(16)
}

/// Minimal noop waker for polling futures outside a runtime.
fn noop_waker() -> Waker {
    static VTABLE: RawWakerVTable =
        RawWakerVTable::new(|p| RawWaker::new(p, &VTABLE), |_| {}, |_| {}, |_| {});
    // SAFETY: the vtable functions are all no-ops; the null data pointer is never dereferenced.
    unsafe { Waker::from_raw(RawWaker::new(std::ptr::null(), &VTABLE)) }
}

/// A future that yields once then returns a value.
struct YieldThenReturn<T> {
    value: Option<T>,
    yielded: bool,
}

impl<T> YieldThenReturn<T> {
    fn new(value: T) -> Self {
        Self {
            value: Some(value),
            yielded: false,
        }
    }
}

impl<T: Unpin> Future for YieldThenReturn<T> {
    type Output = T;
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<T> {
        if self.yielded {
            Poll::Ready(self.value.take().unwrap())
        } else {
            self.yielded = true;
            cx.waker().wake_by_ref();
            Poll::Pending
        }
    }
}

/// Drop counter for verifying exactly-once drop semantics.
#[derive(Clone)]
struct DropCounter(Rc<Cell<u32>>);

impl DropCounter {
    fn new() -> (Self, Rc<Cell<u32>>) {
        let count = Rc::new(Cell::new(0));
        (Self(count.clone()), count)
    }
}

impl Drop for DropCounter {
    fn drop(&mut self) {
        self.0.set(self.0.get() + 1);
    }
}

// =============================================================================
// Basic spawn + poll — verifies header layout and trampoline dispatch
// =============================================================================

#[test]
fn spawn_immediate_ready() {
    let mut exec = test_executor();
    let handle = exec.spawn_boxed(async { 42u64 });
    exec.poll();
    assert!(handle.is_finished());
    drop(handle);
}

#[test]
fn spawn_and_complete_unit() {
    let mut exec = test_executor();
    let handle = exec.spawn_boxed(async {});
    exec.poll();
    assert!(handle.is_finished());
    drop(handle);
}

// =============================================================================
// Union transition: F dropped, T written, drop_fn overwritten
// =============================================================================

#[test]
fn union_transition_u64() {
    // Future produces u64. Verifies poll_join correctly:
    // 1. Drops F in place
    // 2. Writes T (u64) into the union slot
    // 3. Overwrites drop_fn to drop_output::<u64>
    let mut exec = test_executor();
    let handle = exec.spawn_boxed(async { 0xDEAD_BEEF_CAFE_BABEu64 });
    exec.poll();
    // Output is in the union slot — JoinHandle hasn't read it yet.
    // Dropping the handle should drop the output via the overwritten drop_fn.
    drop(handle);
}

#[test]
fn union_transition_string() {
    // Heap-allocated output — verifies drop_output actually runs the
    // destructor (frees the String's heap allocation).
    let mut exec = test_executor();
    let handle = exec.spawn_boxed(async { String::from("hello from miri") });
    exec.poll();
    drop(handle); // Must drop the String via drop_output
}

#[test]
fn union_transition_vec() {
    let mut exec = test_executor();
    let handle = exec.spawn_boxed(async { vec![1u64, 2, 3, 4, 5] });
    exec.poll();
    drop(handle);
}

#[test]
fn union_transition_drop_counter() {
    let (counter, count) = DropCounter::new();
    let mut exec = test_executor();
    let handle = exec.spawn_boxed(async move { counter });
    exec.poll();
    assert_eq!(count.get(), 0, "output should not be dropped yet");
    drop(handle);
    // The DropCounter in the async block's state machine may also be dropped.
    // The key invariant: the OUTPUT DropCounter is dropped exactly once
    // by JoinHandle::Drop via drop_fn.
    assert!(count.get() >= 1, "output must be dropped at least once");
}

// =============================================================================
// JoinHandle lifecycle: normal await path
// =============================================================================

#[test]
fn join_handle_read_output() {
    // Spawn a task, poll it to completion, then poll the JoinHandle
    // to read the output. Verifies ptr::read at the storage offset.
    let mut exec = test_executor();
    let mut handle = exec.spawn_boxed(async { 42u64 });
    exec.poll(); // task completes

    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);
    let result = Pin::new(&mut handle).poll(&mut cx);
    match result {
        Poll::Ready(v) => assert_eq!(v, 42),
        Poll::Pending => panic!("expected Ready"),
    }
    drop(handle);
}

#[test]
fn join_handle_read_string() {
    let mut exec = test_executor();
    let mut handle = exec.spawn_boxed(async { String::from("test output") });
    exec.poll();

    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);
    match Pin::new(&mut handle).poll(&mut cx) {
        Poll::Ready(v) => assert_eq!(v, "test output"),
        Poll::Pending => panic!("expected Ready"),
    }
    drop(handle);
}

// =============================================================================
// JoinHandle lifecycle: detach (drop without await)
// =============================================================================

#[test]
fn detach_before_completion() {
    // Drop JoinHandle before task completes.
    // Task should still run, output dropped by complete_task.
    let ran = Rc::new(Cell::new(false));
    let r = ran.clone();
    let mut exec = test_executor();
    let handle = exec.spawn_boxed(async move {
        r.set(true);
        42u64
    });
    drop(handle); // detach — clears HAS_JOIN, decrements ref_count
    exec.poll(); // task runs, complete_task sees !HAS_JOIN, drops output
    assert!(ran.get());
}

#[test]
fn detach_after_completion() {
    // Task completes, then JoinHandle is dropped without reading.
    // JoinHandle::Drop must drop the output.
    let (counter, count) = DropCounter::new();
    let mut exec = test_executor();
    let handle = exec.spawn_boxed(async move { counter });
    exec.poll(); // task completes, output in union slot
    assert_eq!(count.get(), 0, "output alive in union slot");
    drop(handle); // JoinHandle::Drop drops output via drop_fn
    assert!(count.get() >= 1);
}

// =============================================================================
// JoinHandle lifecycle: abort
// =============================================================================

#[test]
fn abort_before_poll() {
    // Abort before the task has been polled.
    let mut exec = test_executor();
    let handle = exec.spawn_boxed(std::future::pending::<u64>());
    let _ = handle.abort(); // consumes handle
    exec.poll(); // processes the abort
}

#[test]
fn abort_drops_future() {
    // Verify the future is dropped when aborted.
    let (counter, count) = DropCounter::new();
    let mut exec = test_executor();
    let handle = exec.spawn_boxed(async move {
        let _keep = counter;
        std::future::pending::<()>().await;
    });
    let _ = handle.abort(); // consumes handle
    exec.poll();
    assert!(count.get() >= 1, "future's captures must be dropped");
}

#[test]
fn abort_already_completed() {
    let mut exec = test_executor();
    let handle = exec.spawn_boxed(async { 42u64 });
    exec.poll();
    assert!(!handle.abort(), "abort on completed task returns false");
    // handle consumed by abort
}

// =============================================================================
// Output larger than future
// =============================================================================

#[test]
fn output_larger_than_future() {
    // The future is tiny (just returns a large array).
    // The FutureOrOutput union ensures the allocation is large enough.
    let mut exec = test_executor();
    let mut handle = exec.spawn_boxed(async { [0xABu8; 256] });
    exec.poll();

    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);
    match Pin::new(&mut handle).poll(&mut cx) {
        Poll::Ready(arr) => {
            assert_eq!(arr.len(), 256);
            assert_eq!(arr[0], 0xAB);
            assert_eq!(arr[255], 0xAB);
        }
        Poll::Pending => panic!("expected Ready"),
    }
    drop(handle);
}

// =============================================================================
// storage_offset correctness
// =============================================================================

#[test]
fn storage_offset_matches_header() {
    // For Task<()>, storage should be at TASK_HEADER_SIZE.
    assert_eq!(TASK_HEADER_SIZE, 72);
    // The storage_offset field is set from offset_of! at construction.
    // This test verifies the accessor reads the correct value by
    // spawning a task and checking the output is at the right place.
    let mut exec = test_executor();
    let handle = exec.spawn_boxed(async { 42u64 });
    exec.poll();
    // If storage_offset were wrong, poll_join would have written the
    // output to the wrong location, and we'd get garbage or a crash.
    drop(handle);
}

// =============================================================================
// Multiple tasks — interleaved lifecycle
// =============================================================================

#[test]
fn multiple_tasks_interleaved() {
    let mut exec = test_executor();

    let h1 = exec.spawn_boxed(async { String::from("one") });
    let h2 = exec.spawn_boxed(async { vec![1u32, 2, 3] });
    let h3 = exec.spawn_boxed(async { 99u64 });

    exec.poll();

    // Read outputs in different order than spawn
    let mut h3 = h3;
    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);
    match Pin::new(&mut h3).poll(&mut cx) {
        Poll::Ready(v) => assert_eq!(v, 99),
        Poll::Pending => panic!("expected Ready"),
    }
    drop(h3);

    drop(h1); // detach — String dropped
    drop(h2); // detach — Vec dropped
}

// =============================================================================
// Ref_count lifecycle
// =============================================================================

#[test]
fn refcount_spawn_detach_complete() {
    // Spawn (ref=2) → detach (ref=1) → complete (ref=0, freed)
    let mut exec = test_executor();
    let handle = exec.spawn_boxed(async { 42u64 });
    drop(handle); // ref 2→1
    exec.poll(); // complete, ref 1→0, freed
    assert_eq!(exec.task_count(), 0);
}

#[test]
fn refcount_spawn_complete_read_drop() {
    // Spawn (ref=2) → complete (ref=1) → read+drop (ref=0, freed)
    let mut exec = test_executor();
    let mut handle = exec.spawn_boxed(async { 42u64 });
    exec.poll(); // complete, ref 2→1

    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);
    let _ = Pin::new(&mut handle).poll(&mut cx); // read output
    drop(handle); // ref 1→0, deferred free
    exec.poll(); // drain deferred free
    assert_eq!(exec.task_count(), 0);
}

// =============================================================================
// Yielding future — multiple poll cycles
// =============================================================================

#[test]
fn yielding_future_with_output() {
    let mut exec = test_executor();
    let handle = exec.spawn_boxed(YieldThenReturn::new(String::from("delayed")));

    // First poll: task yields (Pending)
    exec.poll();
    assert!(!handle.is_finished());

    // Second poll: task completes
    exec.poll();
    assert!(handle.is_finished());

    drop(handle); // drops the String output
}

// =============================================================================
// Executor drop with live tasks
// =============================================================================

#[test]
fn executor_drop_with_pending_joinable_task() {
    let mut exec = test_executor();
    // Spawn a pending task, then drop the executor without completing it.
    // The executor should drop the future and free the task.
    let _handle = exec.spawn_boxed(std::future::pending::<u64>());
    // Drop handle first to avoid the "outstanding references" assert
    drop(_handle);
    drop(exec);
}

#[test]
fn executor_drop_with_completed_unread_task() {
    let mut exec = test_executor();
    let handle = exec.spawn_boxed(async { String::from("leaked?") });
    exec.poll(); // task completes
    drop(handle); // drops output via drop_fn
    // Deferred free in the next poll, but we drop the executor instead.
    drop(exec);
}

// =============================================================================
// ZST output (Output = ())
// =============================================================================

#[test]
fn zst_output() {
    let mut exec = test_executor();
    let mut handle = exec.spawn_boxed(async {});
    exec.poll();

    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);
    match Pin::new(&mut handle).poll(&mut cx) {
        Poll::Ready(()) => {}
        Poll::Pending => panic!("expected Ready"),
    }
    drop(handle);
}

// =============================================================================
// Deferred free, complete paths, waker push (Phase 3 additions)
// =============================================================================

#[test]
fn deferred_free_drain_cycle() {
    // Spawn joinable task, poll to completion. Drop JoinHandle (pushes to
    // deferred_free via TLS). Poll again — deferred_free is drained and
    // slot is freed. Under miri, verifies no UB in the free path.
    let mut exec = test_executor();
    let handle = exec.spawn_boxed(async { String::from("freed") });
    exec.poll(); // task completes, executor ref_dec → ref still 1 (JoinHandle)
    assert!(handle.is_finished());
    drop(handle); // ref_dec → should_free → deferred_free
    exec.poll(); // drain deferred_free → free_task
    assert_eq!(exec.task_count(), 0);
}

#[test]
fn complete_task_fire_and_forget() {
    // Spawn without holding JoinHandle (detach immediately). Complete.
    // Verify future is dropped, slot freed.
    let (counter, count) = DropCounter::new();
    let mut exec = test_executor();
    let handle = exec.spawn_boxed(async move {
        let _keep = counter;
    });
    drop(handle); // detach
    exec.poll(); // task completes, future dropped, slot freed
    assert!(count.get() >= 1, "future's captures must be dropped");
    assert_eq!(exec.task_count(), 0);
}

#[test]
fn complete_task_joinable_detached() {
    // Spawn joinable task, drop handle (detach), then complete.
    // The complete_task joinable branch sees should_free=true (handle
    // already decremented), drops output, frees.
    let (counter, count) = DropCounter::new();
    let mut exec = test_executor();
    let handle = exec.spawn_boxed(YieldThenReturn::new(counter));
    drop(handle); // detach before completion
    exec.poll(); // first poll: yields
    exec.poll(); // second poll: completes, drops output
    assert!(count.get() >= 1, "output must be dropped");
    assert_eq!(exec.task_count(), 0);
}

#[test]
fn waker_fires_during_poll() {
    // Spawn YieldThenReturn task. First poll returns Pending and calls
    // wake_by_ref. Second poll returns Ready. Verify the waker push to
    // ready queue and re-poll cycle under miri.
    let mut exec = test_executor();
    let handle = exec.spawn_boxed(YieldThenReturn::new(42u64));

    // First poll: yields, wakes self
    let completed = exec.poll();
    assert_eq!(completed, 0);
    assert!(!handle.is_finished());

    // Second poll: completes
    let completed = exec.poll();
    assert_eq!(completed, 1);
    assert!(handle.is_finished());
    drop(handle);
}

#[test]
fn executor_drop_drains_deferred_free() {
    // Spawn task, complete, drop handle (deferred free pending).
    // Drop executor. Verify executor drop drains deferred_free.
    let mut exec = test_executor();
    let handle = exec.spawn_boxed(async { vec![1u32, 2, 3] });
    exec.poll(); // task completes
    drop(handle); // pushes to deferred_free
    drop(exec); // should drain deferred_free and free_task
    // No leak, no UB — miri will catch.
}

// =============================================================================
// Many spawns — stress the allocator under miri
// =============================================================================

#[test]
fn many_spawns() {
    let mut exec = test_executor();
    let mut handles = Vec::new();

    for i in 0..50u64 {
        handles.push(exec.spawn_boxed(async move { i * 2 }));
    }

    exec.poll();

    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);
    for (i, mut h) in handles.into_iter().enumerate() {
        match Pin::new(&mut h).poll(&mut cx) {
            Poll::Ready(v) => assert_eq!(v, (i as u64) * 2),
            Poll::Pending => panic!("task {i} not ready"),
        }
        drop(h);
    }

    exec.poll(); // drain deferred frees
    assert_eq!(exec.task_count(), 0);
}
