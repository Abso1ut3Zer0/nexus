//! Refcounted single-threaded waker.
//!
//! The waker stores the task's raw pointer directly in the `RawWaker` data
//! field. No `Box`, no `Arc` — the waker is two pointers (vtable + data).
//!
//! **Clone** increments the task's `ref_count` (AtomicU16) and copies the pointer.
//! **Drop** decrements `ref_count`; if it hits 0 on a completed task, the slot
//! is pushed to the deferred free list. **Wake** pushes the task pointer to the
//! TLS ready queue (with `is_queued` dedup) and then decrements `ref_count`
//! (consuming the waker).
//!
//! # Safety
//!
//! Single-threaded only. The ready queue and deferred free list pointers in TLS
//! must be valid during the entire poll cycle.
//!
//! # Waker Lifetime
//!
//! Wakers hold a ref to the task via `ref_count`. The task slot stays alive as
//! long as any waker, JoinHandle, or the executor holds a reference. When the
//! last ref drops (refcount hits 0), the slot is deferred for freeing.

use std::task::{RawWaker, RawWakerVTable, Waker};

use crate::task::{self, TaskRef};

// =============================================================================
// Thread-local ready queue for wakers
// =============================================================================

std::thread_local! {
    /// Raw pointer to the executor's ready queue. Set before polling,
    /// cleared after. Wakers read this to push their task pointer.
    static READY_QUEUE: std::cell::Cell<*mut Vec<*mut u8>> =
        const { std::cell::Cell::new(std::ptr::null_mut()) };

    /// Deferred free list: task pointers whose refcount hit 0 after
    /// completion. The executor drains this on each poll cycle.
    static DEFERRED_FREE: std::cell::Cell<*mut Vec<*mut u8>> =
        const { std::cell::Cell::new(std::ptr::null_mut()) };
}

/// Install TLS pointers for the duration of a poll cycle.
/// Returns an RAII guard that restores previous values on drop.
///
/// # Safety
///
/// `ready` and `deferred_free` must be valid pointers to `Vec<*mut u8>`
/// that outlive the returned guard. Typically derived from
/// `UnsafeCell::get()` on the Executor's fields.
#[inline]
pub(crate) fn set_poll_context(
    ready: *mut Vec<*mut u8>,
    deferred_free: *mut Vec<*mut u8>,
) -> PollContextGuard {
    let prev_ready = READY_QUEUE.with(|cell| cell.replace(ready));
    let prev_free = DEFERRED_FREE.with(|cell| cell.replace(deferred_free));
    PollContextGuard {
        prev_ready,
        prev_free,
    }
}

pub(crate) struct PollContextGuard {
    prev_ready: *mut Vec<*mut u8>,
    prev_free: *mut Vec<*mut u8>,
}

impl Drop for PollContextGuard {
    #[inline]
    fn drop(&mut self) {
        READY_QUEUE.with(|cell| cell.set(self.prev_ready));
        DEFERRED_FREE.with(|cell| cell.set(self.prev_free));
    }
}

// =============================================================================
// RawWaker vtable
// =============================================================================

pub(crate) static VTABLE: RawWakerVTable =
    RawWakerVTable::new(clone_fn, wake_fn, wake_by_ref_fn, drop_fn);

/// Create a `Waker` for a task. Increments `ref_count` to account for
/// the waker's reference. The waker's `drop_fn` will decrement it.
///
/// # Safety
///
/// `ptr` must point to a live task with `ref_count >= 1`.
#[inline]
pub(crate) unsafe fn task_waker(ptr: *mut u8) -> Waker {
    // Acquire a TaskRef (ref_inc), then forget it — the RawWaker now
    // owns the ref. drop_fn calls TaskRef::from_owned + drop to release.
    // SAFETY: caller guarantees ptr points to a live task with ref_count >= 1.
    let task_ref = unsafe { TaskRef::acquire(ptr) };
    let raw = RawWaker::new(task_ref.as_ptr().cast(), &VTABLE);
    std::mem::forget(task_ref);
    // SAFETY: raw uses VTABLE with correct vtable functions; data ptr is a live task ref.
    unsafe { Waker::from_raw(raw) }
}

/// Extract the task pointer from a waker if it belongs to this runtime.
///
/// Returns the task `*mut u8` if the waker uses our local vtable.
/// Returns `None` if it's a different waker (cross-thread, root, etc.).
pub(crate) fn task_ptr_from_local_waker(waker: &Waker) -> Option<*mut u8> {
    if waker.vtable() == &VTABLE {
        Some(waker.data() as *mut u8)
    } else {
        None
    }
}

/// Clone: increment refcount, copy the pointer. The new RawWaker owns
/// the new ref; its drop_fn will release it.
unsafe fn clone_fn(data: *const ()) -> RawWaker {
    // SAFETY: data points to a live (or completed) task with refcount >= 1
    // (the original waker holds a ref).
    let task_ref = unsafe { TaskRef::acquire(data as *mut u8) };
    let raw = RawWaker::new(task_ref.as_ptr().cast(), &VTABLE);
    std::mem::forget(task_ref);
    raw
}

/// Wake (by value): push to ready queue, decrement refcount (consumes
/// waker). TaskRef::Drop routes terminal state through dispose_terminal,
/// which defers to DEFERRED_FREE on the executor thread.
unsafe fn wake_fn(data: *const ()) {
    // SAFETY: data is a valid task pointer.
    unsafe { wake_impl(data) };
    // Consume the ref via TaskRef::Drop.
    // SAFETY: data was given to wake_fn by the RawWaker; we own the ref and are consuming it.
    drop(unsafe { TaskRef::from_owned(data as *mut u8) });
}

/// Wake (by ref): push to ready queue. Does NOT decrement refcount
/// (the waker is borrowed, not consumed).
unsafe fn wake_by_ref_fn(data: *const ()) {
    // SAFETY: data is a valid task pointer.
    unsafe { wake_impl(data) };
}

/// Drop (without waking): decrement refcount via TaskRef::Drop.
unsafe fn drop_fn(data: *const ()) {
    // SAFETY: data was given to drop_fn by the RawWaker; we own the ref and are releasing it.
    drop(unsafe { TaskRef::from_owned(data as *mut u8) });
}

/// Push a terminal task pointer onto the executor's `DEFERRED_FREE`
/// list. Returns `true` if the push succeeded, `false` if the TLS is
/// null (called outside a poll cycle).
///
/// On `false`, the caller's task slot is not enqueued for cleanup —
/// `Executor::drop` will eventually iterate `all_tasks` and reclaim it.
/// This is the established "leak until shutdown" fallback for
/// terminal frees that fire outside `block_on`.
///
/// Used by `crate::cross_wake::dispose_terminal` for the on-executor
/// branch (TaskRef::Drop on the runtime's owning thread). The deferred
/// path keeps `Executor::all_tasks` bookkeeping consistent — the next
/// poll cycle's drain reads `tracker_key` then frees + removes from
/// `all_tasks` in the right order (see `Executor::poll`).
///
/// # Safety
///
/// `ptr` must point to a terminal task slot (refcount 0, COMPLETED set,
/// lifecycle flags clear).
#[cold]
#[inline(never)]
pub(crate) unsafe fn try_defer_free(ptr: *mut u8) -> bool {
    DEFERRED_FREE.with(|cell| {
        let list_ptr = cell.get();
        if list_ptr.is_null() {
            return false;
        }
        // SAFETY: list_ptr valid — set by set_poll_context.
        let list = unsafe { &mut *list_ptr };
        list.push(ptr);
        true
    })
}

/// Shared wake implementation.
///
/// # Safety
///
/// `data` must be a valid task pointer from the byte slab.
/// The ready queue TLS must be set (we're inside a poll cycle).
unsafe fn wake_impl(data: *const ()) {
    let task_ptr = data as *mut u8;

    // Don't wake completed tasks — the future is already dropped.
    // SAFETY: task_ptr points to a (possibly completed) task.
    if unsafe { task::is_completed(task_ptr) } {
        return;
    }

    // Check dedup flag — don't queue twice.
    // SAFETY: task_ptr is a valid task pointer; is_queued reads the queued flag from packed task state.
    if unsafe { task::is_queued(task_ptr) } {
        return;
    }
    // SAFETY: task_ptr is a valid task pointer; set_queued writes the queued flag atomically.
    unsafe { task::set_queued(task_ptr, true) };

    // Push to ready queue.
    READY_QUEUE.with(|cell| {
        let queue_ptr = cell.get();
        debug_assert!(
            !queue_ptr.is_null(),
            "waker fired outside poll cycle — task will be lost. \
             Ensure wakers are only used within Runtime::block_on or \
             Executor::poll scope."
        );
        if !queue_ptr.is_null() {
            // SAFETY: queue_ptr is valid — set by set_poll_context before
            // polling. Single-threaded, no concurrent access.
            let queue = unsafe { &mut *queue_ptr };
            queue.push(task_ptr);
        }
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::task::{RawWaker, Waker};

    #[test]
    fn task_ptr_from_local_waker_roundtrip() {
        let sentinel = 0xDEAD_BEEF_usize as *mut u8;
        // SAFETY: sentinel is not a real task pointer but we wrap it in
        // ManuallyDrop so vtable functions (which would deref it) are never called.
        let waker = unsafe { Waker::from_raw(RawWaker::new(sentinel.cast(), &VTABLE)) };
        let waker = std::mem::ManuallyDrop::new(waker);

        let ptr = task_ptr_from_local_waker(&waker);
        assert_eq!(ptr, Some(sentinel));
    }

    #[test]
    fn task_ptr_from_foreign_waker_returns_none() {
        static OTHER: RawWakerVTable =
            RawWakerVTable::new(|p| RawWaker::new(p, &OTHER), |_| {}, |_| {}, |_| {});
        // SAFETY: all vtable functions are no-ops; null data is never dereferenced.
        let waker = unsafe { Waker::from_raw(RawWaker::new(std::ptr::null(), &OTHER)) };
        let waker = std::mem::ManuallyDrop::new(waker);

        assert!(task_ptr_from_local_waker(&waker).is_none());
    }
}
