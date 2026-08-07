//! Task storage: header + future/output union in a contiguous allocation.
//!
//! Each task is a `Task<F>` struct. The raw pointer to the allocation
//! IS the task handle — no index layer, no separate metadata store.
//!
//! The waker holds the raw pointer directly. `wake()` sets `QUEUED`
//! and pushes the pointer to the ready queue. Zero allocations.
//!
//! Tasks can be allocated via Box (default) or slab (power user).
//! The `free_fn` in the header knows how to deallocate regardless
//! of which allocator was used.
//!
//! ## Packed state word
//!
//! All task state (flags + refcount) is packed into a single `AtomicUsize`:
//!
//! ```text
//! bits 0-5:   flags (COMPLETED, QUEUED, HAS_JOIN, ABORTED, OUTPUT_TAKEN, SLAB_ALLOCATED)
//! bits 6+:    refcount (shifted by 6)
//! ```
//!
//! This eliminates the SIGABRT race where `Executor::drop` reads
//! `ref_count` and `is_completed` as separate atomics and a cross-thread
//! waker can decrement the refcount between those reads.
//!
//! The state word naturally converges to `TERMINAL = COMPLETED = 1`
//! when all refs are decremented and all transient flags are cleared.
//! The free check is one comparison: `state == TERMINAL`.
//!
//! ## Union storage
//!
//! The slot at `storage_offset` holds either `F` (the future) or `T` (the output),
//! never both. While running, `F` is live. When the future completes,
//! `poll_join` drops `F` in place and writes `T` to the same bytes.
//! `drop_fn` is overwritten from `drop_fn::<F>` to `drop_output::<T>`
//! so subsequent cleanup targets the correct type.
//!
//! ## `TaskRef` ownership rule
//!
//! [`TaskRef`] covers every refcount holder EXCEPT the executor's own
//! `all_tasks` ref. That single ref uses [`complete_and_unref`] directly
//! (atomic COMPLETED-set + decrement), bypassing TaskRef's Drop-time
//! `dispose_terminal` routing. Wrapping `all_tasks` ownership in TaskRef
//! would route terminal frees through `dispose_terminal` →
//! `try_defer_free`, double-handling tasks the executor is already
//! tracking. Subtle regression — don't do it.
//!
//! Everything else (local wakers, cross-thread wakers, channel slots,
//! `JoinHandle`) IS a `TaskRef`.

use std::cell::UnsafeCell;
use std::future::Future;
use std::marker::PhantomData;
use std::pin::Pin;
use std::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};
use std::task::{Context, Poll, Waker};

use crate::cross_wake::CrossWakeContext;

// =============================================================================
// Packed state word — constants
// =============================================================================

/// Task has completed (future returned Ready or was aborted).
const COMPLETED: usize = 1 << 0;
/// Task is in a ready queue (dedup flag).
const QUEUED: usize = 1 << 1;
/// JoinHandle exists for this task.
const HAS_JOIN: usize = 1 << 2;
/// abort() was called.
const ABORTED: usize = 1 << 3;
/// JoinHandle consumed the output via poll.
const OUTPUT_TAKEN: usize = 1 << 4;
/// Task was allocated from the slab (permanent flag, set at spawn).
const SLAB_ALLOCATED: usize = 1 << 5;
/// Mask for all flag bits (0-5).
const FLAG_MASK: usize = 0b11_1111;
/// One reference count unit (bit 6).
const REF_ONE: usize = 1 << 6;
/// Mask for refcount bits (6+).
const REF_MASK: usize = !FLAG_MASK;

/// Lifecycle flags: must be cleared before a task can reach terminal.
/// QUEUED: someone needs to pop this task from a queue.
/// HAS_JOIN: a JoinHandle still exists and must be dropped.
const LIFECYCLE_MASK: usize = QUEUED | HAS_JOIN;

/// Inert flags: permanent metadata or historical — don't block terminal.
/// SLAB_ALLOCATED: permanent, set at spawn.
/// ABORTED: historical, set on abort — no cleanup gated on clearing it.
/// OUTPUT_TAKEN: historical, set when output read — same.
const INERT_MASK: usize = SLAB_ALLOCATED | ABORTED | OUTPUT_TAKEN;

/// What to do when a ref_dec or complete_and_unref produces a terminal state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum FreeAction {
    /// Task still has outstanding refs or unchecked flags. No action.
    Retain,
    /// Box-allocated terminal. Free from any thread via free_task.
    FreeBox,
    /// Slab-allocated terminal. Route to executor thread for slab free.
    FreeSlab,
}

// =============================================================================
// TaskRef — RAII smart pointer pairing ref_inc with ref_dec
// =============================================================================

/// Refcounted handle to a task. Pairs `ref_inc` with `ref_dec` at
/// compile time — Drop calls `ref_dec` and routes terminal results
/// through `dispose_terminal`.
///
/// `TaskRef` is the canonical refcount holder for everything except the
/// executor's `all_tasks` ref (see the module-level doc-block). Local
/// wakers, cross-thread wakers, channel slots, and `JoinHandle` all
/// hold a `TaskRef`.
///
/// # Invariants
///
/// - Each `TaskRef` owns exactly one refcount unit on the underlying task.
/// - `Drop` decrements; if terminal, the task is routed via
///   `crate::cross_wake::dispose_terminal` (defer via `try_defer_free`
///   on the owning executor thread or for null-ctx test tasks; queue
///   via the cross-wake queue off-thread).
pub(crate) struct TaskRef {
    ptr: *mut u8,
}

impl TaskRef {
    /// Acquire a reference. Increments the task's refcount.
    ///
    /// # Safety
    ///
    /// `ptr` must point to a live task with refcount >= 1 at the time of call.
    #[inline]
    pub(crate) unsafe fn acquire(ptr: *mut u8) -> Self {
        // SAFETY: acquire's safety contract requires ptr points to a live task with refcount >= 1.
        unsafe { ref_inc(ptr) };
        Self { ptr }
    }

    /// Wrap a pre-incremented pointer (no `ref_inc` here).
    ///
    /// Use when the caller has already accounted for the ref (e.g., on
    /// the boundary of a vtable handoff like `RawWaker::data` →
    /// `wake_fn` consuming the ref).
    ///
    /// # Safety
    ///
    /// `ptr` owns one ref. The caller must not also drop it.
    #[inline]
    pub(crate) unsafe fn from_owned(ptr: *mut u8) -> Self {
        Self { ptr }
    }

    /// The raw task pointer this handle holds.
    #[inline]
    pub(crate) fn as_ptr(&self) -> *mut u8 {
        self.ptr
    }
}

impl Drop for TaskRef {
    #[inline]
    fn drop(&mut self) {
        // SAFETY: self.ptr is a valid task pointer; TaskRef owns exactly one refcount unit.
        match unsafe { ref_dec(self.ptr) } {
            FreeAction::Retain => {}
            FreeAction::FreeBox | FreeAction::FreeSlab => {
                // SAFETY: terminal state — ref just dropped to 0 with
                // all lifecycle flags clear. dispose_terminal routes
                // per the task's header context and current thread:
                //
                //   - On-thread (or null-ctx test task): try_defer_free
                //     pushes to DEFERRED_FREE TLS if a poll cycle is
                //     active; otherwise the slot leaks until
                //     Executor::drop reclaims via its all_tasks scan.
                //   - Off-thread: queues via the cross-wake queue +
                //     conditional eventfd poke.
                //
                // Direct-free is never used — would race
                // Executor::all_tasks bookkeeping. See dispose_terminal's
                // doc-comment in `cross_wake.rs` for the full rationale.
                unsafe { crate::cross_wake::dispose_terminal(self.ptr) };
            }
        }
    }
}

// SAFETY: TaskRef is a raw pointer + refcount discipline. The underlying
// task allocation is Send-safe (atomic state, no thread-affine fields
// in the header). Cross-thread holders (tokio_compat, channel slots)
// store TaskRef across threads, so it must be Send.
unsafe impl Send for TaskRef {}
// Not Sync — only the holder may drop. Cloning a TaskRef means a new
// ref_inc; aliasing through &TaskRef would let two holders ref_dec
// the same logical ref.

// =============================================================================
// Task layout
// =============================================================================

/// Header size in bytes. Must match the layout of `Task<F>` before the
/// `storage` field.
pub const TASK_HEADER_SIZE: usize = 72;

/// Task header + storage in a contiguous allocation. `repr(C)` for
/// deterministic layout.
///
/// `S` is the storage type — either just `F` (fire-and-forget) or a union
/// of `F` and `T` (joinable). The header is always 72 bytes regardless of `S`.
///
/// Layout (64-bit):
/// ```text
/// offset  0: poll_fn        (8B, fn pointer — polls the future)
/// offset  8: drop_fn        (8B, fn pointer — drops F or T in place)
/// offset 16: free_fn        (8B, fn pointer — deallocates the task storage)
/// offset 24: state          (8B, AtomicUsize — packed flags + refcount)
/// offset 32: cross_next     (8B, AtomicPtr — intrusive cross-thread wake queue)
/// offset 40: join_waker     (16B, UnsafeCell<Option<Waker>>)
/// offset 56: storage_offset (2B, u16 — byte offset to storage field)
/// offset 58: _pad           (2B)
/// offset 60: tracker_key    (4B, u32 — index in Executor::all_tasks slab)
/// offset 64: cross_wake_ctx (8B, *const CrossWakeContext — cold; read by dispose_terminal)
/// offset 72: storage        (S bytes — future F or union { F, T })
/// ```
///
/// `cross_wake_ctx` lives at the end of the header because it's only
/// touched on terminal Drop (cold path); hot-path reads (state, drop_fn,
/// poll_fn, free_fn) stay near the cache-line head.
#[repr(C)]
pub(crate) struct Task<S> {
    /// Polls the future. Receives the task base pointer.
    poll_fn: unsafe fn(*mut u8, &mut Context<'_>) -> Poll<()>,
    /// Drops the value at `storage_offset` (future F or output T). Receives base pointer.
    drop_fn: unsafe fn(*mut u8),
    /// Deallocates the task storage.
    free_fn: unsafe fn(*mut u8),
    /// Packed state word: flags (bits 0-5) + refcount (bits 6+).
    state: AtomicUsize,
    /// Intrusive next pointer for the cross-thread wake queue.
    cross_next: AtomicPtr<u8>,
    /// Waker for the task awaiting this JoinHandle.
    join_waker: UnsafeCell<Option<Waker>>,
    /// Byte offset from task base to the storage field.
    /// Set at construction from `offset_of!(Task<S>, storage)`.
    storage_offset: u16,
    /// Padding for alignment.
    _pad: [u8; 2],
    /// Index into the Executor's `all_tasks` slab.
    tracker_key: u32,
    /// Pointer to the runtime's [`CrossWakeContext`] (Arc-backed, heap-stable).
    /// Set at spawn time. Read by `dispose_terminal` on terminal Drop to
    /// route the task through the owning executor (defer locally) or its
    /// cross-thread queue (off-thread). Null for tasks not associated
    /// with any runtime (test-only `Task::new_boxed` path).
    cross_wake_ctx: *const CrossWakeContext,
    storage: S,
}

/// Union storage for joinable tasks. Sized to fit both the future F
/// and the output T in the same allocation.
#[repr(C)]
pub(crate) union FutureOrOutput<F, T> {
    pub(crate) future: std::mem::ManuallyDrop<F>,
    pub(crate) output: std::mem::ManuallyDrop<T>,
}

// Static assertion: header layout matches TASK_HEADER_SIZE.
const _: () = {
    assert!(std::mem::size_of::<Task<()>>() == TASK_HEADER_SIZE);
};

impl<F: Future<Output = ()> + 'static> Task<F> {
    /// Construct a fire-and-forget task (no JoinHandle) with Box-based free.
    ///
    /// Used internally for tests and low-level task construction.
    /// `ref_count = 1` (executor only), `HAS_JOIN` not set.
    /// `cross_wake_ctx` is null — test tasks aren't registered with any
    /// runtime. Terminal frees go through `dispose_terminal`'s on-thread
    /// defer path (`try_defer_free` if a poll cycle is active, otherwise
    /// leak until `Executor::drop`'s `all_tasks` scan reclaims them).
    /// Direct-free is unsafe even for null-ctx tasks because
    /// `dispose_terminal` doesn't own `all_tasks` bookkeeping — see
    /// `dispose_terminal`'s doc-comment in `cross_wake.rs` for the full
    /// rationale.
    ///
    /// # Why `Output = ()` is required
    ///
    /// This uses `poll_join::<F>` which writes T at the storage offset
    /// after dropping F. The storage is `F` (not `FutureOrOutput<F, T>`),
    /// so it's only sized for F. With `T = ()` (ZST), the write is
    /// zero-size and the `drop_fn` overwrite to `drop_output::<()>` is a
    /// no-op. Relaxing this bound to non-ZST T would write T into
    /// storage not sized for it — UB.
    #[cfg(test)]
    #[inline]
    pub(crate) fn new_boxed(future: F, tracker_key: u32) -> Self {
        Self {
            poll_fn: poll_join::<F>,
            drop_fn: drop_future::<F>,
            free_fn: box_free::<F>,
            state: AtomicUsize::new(REF_ONE),
            cross_next: AtomicPtr::new(std::ptr::null_mut()),
            join_waker: UnsafeCell::new(None),
            storage_offset: std::mem::offset_of!(Task<F>, storage) as u16,
            tracker_key,
            _pad: [0; 2],
            cross_wake_ctx: std::ptr::null(),
            storage: future,
        }
    }
}

/// Allocate a joinable Box task and return the raw pointer.
///
/// The task has `ref_count = 2` (executor + JoinHandle) and `HAS_JOIN` set.
/// The allocation is sized for `max(size_of::<F>(), size_of::<T>())` via
/// the `FutureOrOutput<F, T>` union.
///
/// `cross_wake_ctx` should be `Arc::as_ptr(&runtime.cross_wake)` for
/// real spawns (Arc-backed, heap-stable), or `std::ptr::null()` for
/// tasks not associated with any runtime (test paths only). Read by
/// `dispose_terminal` on terminal Drop.
pub(crate) fn box_spawn_joinable<F>(
    future: F,
    tracker_key: u32,
    cross_wake_ctx: *const CrossWakeContext,
) -> *mut u8
where
    F: Future + 'static,
    F::Output: 'static,
{
    type Storage<F> = FutureOrOutput<F, <F as Future>::Output>;

    let task: Task<Storage<F>> = Task {
        poll_fn: poll_join::<F>,
        drop_fn: drop_future_in_union::<F>,
        free_fn: box_free::<Storage<F>>,
        state: AtomicUsize::new(HAS_JOIN | (2 * REF_ONE)),
        cross_next: AtomicPtr::new(std::ptr::null_mut()),
        join_waker: UnsafeCell::new(None),
        storage_offset: std::mem::offset_of!(Task<Storage<F>>, storage) as u16,
        tracker_key,
        _pad: [0; 2],
        cross_wake_ctx,
        storage: FutureOrOutput {
            future: std::mem::ManuallyDrop::new(future),
        },
    };
    Box::into_raw(Box::new(task)) as *mut u8
}

/// Construct a joinable task for slab allocation.
///
/// Returns the task struct to be copied into a slab slot. Uses the
/// `FutureOrOutput<F, T>` union so the allocation fits both.
///
/// See `box_spawn_joinable` for the `cross_wake_ctx` contract.
pub(crate) fn new_joinable_slab<F>(
    future: F,
    tracker_key: u32,
    free_fn: unsafe fn(*mut u8),
    cross_wake_ctx: *const CrossWakeContext,
) -> Task<FutureOrOutput<F, F::Output>>
where
    F: Future + 'static,
    F::Output: 'static,
{
    Task {
        poll_fn: poll_join::<F>,
        drop_fn: drop_future_in_union::<F>,
        free_fn,
        state: AtomicUsize::new(HAS_JOIN | SLAB_ALLOCATED | (2 * REF_ONE)),
        cross_next: AtomicPtr::new(std::ptr::null_mut()),
        join_waker: UnsafeCell::new(None),
        storage_offset: std::mem::offset_of!(Task<FutureOrOutput<F, F::Output>>, storage) as u16,
        tracker_key,
        _pad: [0; 2],
        cross_wake_ctx,
        storage: FutureOrOutput {
            future: std::mem::ManuallyDrop::new(future),
        },
    }
}

// =============================================================================
// Task handle — raw pointer operations
// =============================================================================

/// Opaque task identifier. Wraps the raw pointer to the task.
/// The pointer is stable for the task's lifetime.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct TaskId(pub(crate) *mut u8);

// =============================================================================
// JoinHandle
// =============================================================================

/// Handle to a spawned task. Await to get the result.
///
/// Dropping the handle detaches the task — it continues running but the
/// output is dropped when the task completes. Use [`abort()`](Self::abort)
/// to cancel the task.
///
/// `JoinHandle` is `!Send` and `!Sync` — it must stay on the executor thread.
#[must_use = "dropping a JoinHandle detaches the task — await it or call .abort()"]
pub struct JoinHandle<T> {
    ptr: *mut u8,
    _marker: PhantomData<T>,
    _not_send: PhantomData<*const ()>, // !Send + !Sync
}

impl<T: 'static> Future for JoinHandle<T> {
    type Output = T;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<T> {
        let ptr = self.ptr;

        // SAFETY: ptr is valid — JoinHandle holds a ref (refcount >= 1).
        if unsafe { is_completed(ptr) } {
            // SAFETY: ptr is valid — JoinHandle holds a ref (refcount >= 1).
            let s = unsafe { state_load(ptr) };
            assert!(s & ABORTED == 0, "polled JoinHandle after task was aborted");
            // SAFETY: Task completed, so poll_join already transitioned the union
            // from F to T. The output is live at storage_offset. ptr::read moves
            // it out (bitwise copy). OUTPUT_TAKEN prevents double-read.
            let output_ptr = unsafe { ptr.add(storage_offset(ptr)) };
            // SAFETY: output_ptr points to a live T at storage_offset; task is completed.
            let value = unsafe { std::ptr::read(output_ptr.cast::<T>()) };
            // SAFETY: ptr is valid — setting OUTPUT_TAKEN on a completed task.
            unsafe { set_output_taken(ptr) };
            Poll::Ready(value)
        } else {
            // SAFETY: Task still running, single-threaded — safe to write waker.
            unsafe { set_join_waker(ptr, cx.waker().clone()) };
            Poll::Pending
        }
    }
}

impl<T> JoinHandle<T> {
    pub(crate) fn new(ptr: *mut u8) -> Self {
        Self {
            ptr,
            _marker: PhantomData,
            _not_send: PhantomData,
        }
    }

    /// Returns `true` if the task has completed (output is ready).
    pub fn is_finished(&self) -> bool {
        // SAFETY: self.ptr is valid — JoinHandle holds a ref (refcount >= 1).
        unsafe { is_completed(self.ptr) }
    }

    /// Abort the task and consume the handle.
    ///
    /// The future is dropped on the next poll cycle. Consumes the handle
    /// so it cannot be awaited after abort — this is enforced at the type
    /// level rather than via a runtime panic.
    ///
    /// Returns `true` if the task was still running, `false` if it had
    /// already completed (output is dropped by `JoinHandle::drop`).
    #[must_use = "returns whether the task was still running"]
    pub fn abort(self) -> bool {
        let ptr = self.ptr;
        // SAFETY: ptr is valid — JoinHandle holds a ref (refcount >= 1).
        let was_running = !unsafe { is_completed(ptr) };
        if was_running {
            // SAFETY: ptr is valid — setting ABORTED on a live task.
            unsafe { set_aborted(ptr) };
        }
        // self is consumed — Drop runs, which clears HAS_JOIN,
        // takes the join waker, and decrements refcount.
        was_running
    }

    /// Test-only raw pointer accessor for white-box scenarios that
    /// need to drive the underlying task allocation directly (e.g.,
    /// the cross_wake UAF regression test in PR 2). Avoids the
    /// `repr(Rust)` layout assumption that `mem::transmute_copy`
    /// would otherwise rely on.
    #[cfg(test)]
    pub(crate) fn raw_ptr(&self) -> *mut u8 {
        self.ptr
    }
}

impl<T> Drop for JoinHandle<T> {
    fn drop(&mut self) {
        let ptr = self.ptr;
        // SAFETY: ptr is valid — JoinHandle holds a ref (refcount >= 1).
        let s = unsafe { state_load(ptr) };

        if (s & COMPLETED != 0) && (s & OUTPUT_TAKEN == 0) && (s & ABORTED == 0) {
            // Task completed but output was never read — drop it.
            // SAFETY: poll_join overwrote drop_fn to drop_output::<T>,
            // so this drops the output T (not the future F).
            unsafe { drop_task_future(ptr) };
        }

        // Clear HAS_JOIN so complete_task knows nobody is waiting.
        // Take the join waker to release the parent task's refcount.
        // SAFETY: ptr is valid — JoinHandle holds a ref (refcount >= 1).
        unsafe { clear_has_join(ptr) };
        // SAFETY: ptr is valid — taking the join waker under single-threaded access.
        let _ = unsafe { take_join_waker(ptr) };

        // Release our reference via TaskRef. Drop routes terminal state
        // through dispose_terminal — defers via DEFERRED_FREE TLS on the
        // executor thread (so all_tasks bookkeeping stays consistent),
        // queues cross-thread otherwise, frees directly for null-ctx
        // (test) tasks. JoinHandle is !Send so we're always on the
        // executor thread here, but the routing handles all cases.
        // SAFETY: JoinHandle owned exactly one ref on `ptr`; we hand
        // it off to TaskRef which will ref_dec on Drop.
        drop(unsafe { TaskRef::from_owned(ptr) });
    }
}

// =============================================================================
// Packed state accessor functions
// =============================================================================

/// Get the raw state value.
///
/// # Safety
///
/// `ptr` must point to a live `Task<F>`.
#[inline]
unsafe fn state_load(ptr: *mut u8) -> usize {
    // SAFETY: state is AtomicUsize at offset 24 in repr(C) Task.
    unsafe { &*ptr.add(24).cast::<AtomicUsize>() }.load(Ordering::Acquire)
}

/// Get a reference to the state atomic.
///
/// # Safety
///
/// `ptr` must point to a live `Task<F>`.
#[inline]
unsafe fn state_ref(ptr: *mut u8) -> &'static AtomicUsize {
    // SAFETY: state is AtomicUsize at offset 24 in repr(C) Task.
    // 'static is a lie — the caller must not outlive the task.
    unsafe { &*ptr.add(24).cast::<AtomicUsize>() }
}

/// Read the `tracker_key` from a task pointer.
///
/// # Safety
///
/// `ptr` must point to a live `Task<F>`.
#[inline]
pub(crate) unsafe fn tracker_key(ptr: *mut u8) -> u32 {
    // SAFETY: tracker_key is at offset 60 in repr(C) Task.
    unsafe { *(ptr.add(60).cast::<u32>()) }
}

/// Increment the waker refcount. Called on waker clone.
///
/// # Safety
///
/// `ptr` must point to a live `Task<F>`.
#[inline]
pub(crate) unsafe fn ref_inc(ptr: *mut u8) {
    // SAFETY: caller upholds ptr validity; state is at offset 24 in repr(C) Task.
    let state = unsafe { state_ref(ptr) };
    let prev = state.fetch_add(REF_ONE, Ordering::Relaxed);
    debug_assert!((prev & REF_MASK) > 0, "ref_inc on zero refcount");
}

/// Decrement the refcount. Returns `FreeAction` indicating whether
/// a terminal state was produced and what kind of allocation it is.
///
/// # Safety
///
/// `ptr` must point to a live (or completed) `Task<F>`.
#[inline]
pub(crate) unsafe fn ref_dec(ptr: *mut u8) -> FreeAction {
    // SAFETY: caller upholds ptr validity; state is at offset 24 in repr(C) Task.
    let state = unsafe { state_ref(ptr) };
    let prev = state.fetch_sub(REF_ONE, Ordering::AcqRel);
    debug_assert!((prev & REF_MASK) >= REF_ONE, "ref_dec on zero refcount");

    // Was this the last ref?
    if (prev & REF_MASK) != REF_ONE {
        return FreeAction::Retain;
    }

    // Last ref. Check: COMPLETED must be set, lifecycle flags must be clear.
    // ABORTED, OUTPUT_TAKEN, SLAB_ALLOCATED are inert — don't block terminal.
    let flags = prev & FLAG_MASK;
    if (flags & COMPLETED == 0) || (flags & LIFECYCLE_MASK != 0) {
        return FreeAction::Retain;
    }
    if flags & SLAB_ALLOCATED != 0 {
        FreeAction::FreeSlab
    } else {
        FreeAction::FreeBox
    }
}

/// Read the refcount.
///
/// # Safety
///
/// `ptr` must point to a live `Task<F>`.
#[inline]
pub(crate) unsafe fn ref_count(ptr: *mut u8) -> usize {
    // SAFETY: caller upholds ptr validity; state is at offset 24 in repr(C) Task.
    (unsafe { state_load(ptr) } & REF_MASK) >> 6
}

/// Atomically set COMPLETED and decrement the executor's reference.
/// Returns `FreeAction` indicating whether a terminal state was produced.
///
/// This is the key atomic operation that eliminates the race between
/// `set_completed` and `ref_dec` that caused the SIGABRT.
///
/// # Safety
///
/// `ptr` must point to a live, not-yet-completed `Task<F>`.
#[inline]
pub(crate) unsafe fn complete_and_unref(ptr: *mut u8) -> FreeAction {
    // SAFETY: caller upholds ptr validity; state is at offset 24 in repr(C) Task.
    let state = unsafe { state_ref(ptr) };
    // Atomically: set COMPLETED (add 1 to bit 0) + dec refcount (sub REF_ONE)
    // Net subtraction = REF_ONE - COMPLETED.
    let prev = state.fetch_sub(REF_ONE - COMPLETED, Ordering::AcqRel);
    debug_assert!(prev & COMPLETED == 0, "double complete");
    debug_assert!(
        (prev & REF_MASK) >= REF_ONE,
        "complete_and_unref on zero refcount"
    );
    // prev had COMPLETED=0. Last ref if prev had exactly REF_ONE.
    // Lifecycle flags (QUEUED, HAS_JOIN) must be clear.
    // Inert flags (ABORTED, OUTPUT_TAKEN, SLAB_ALLOCATED) don't matter.
    if (prev & REF_MASK) != REF_ONE {
        return FreeAction::Retain;
    }
    let flags = prev & FLAG_MASK;
    if flags & LIFECYCLE_MASK != 0 {
        return FreeAction::Retain;
    }
    if flags & SLAB_ALLOCATED != 0 {
        FreeAction::FreeSlab
    } else {
        FreeAction::FreeBox
    }
}

/// Check if the state is TERMINAL (safe to free).
///
/// # Safety
///
/// `ptr` must point to a live `Task<F>`.
#[inline]
pub(crate) unsafe fn is_terminal(ptr: *mut u8) -> bool {
    // SAFETY: caller upholds ptr validity; state is at offset 24 in repr(C) Task.
    let s = unsafe { state_load(ptr) };
    // Strip inert flags (SLAB_ALLOCATED, ABORTED, OUTPUT_TAKEN).
    // What remains must be exactly COMPLETED with zero refcount.
    (s & !INERT_MASK) == COMPLETED
}

/// Read the is_completed flag.
///
/// # Safety
///
/// `ptr` must point to a (possibly completed) `Task<F>`.
#[inline]
pub(crate) unsafe fn is_completed(ptr: *mut u8) -> bool {
    // SAFETY: caller upholds ptr validity; state is at offset 24 in repr(C) Task.
    (unsafe { state_load(ptr) }) & COMPLETED != 0
}

/// Read the SLAB_ALLOCATED flag.
///
/// Used by `Executor::drop` to differentiate cleanup behavior between
/// slab- and box-allocated tasks during unwinding.
///
/// # Safety
///
/// `ptr` must point to a live `Task<F>`.
#[inline]
pub(crate) unsafe fn is_slab_allocated(ptr: *mut u8) -> bool {
    // SAFETY: caller upholds ptr validity; state is at offset 24 in repr(C) Task.
    (unsafe { state_load(ptr) }) & SLAB_ALLOCATED != 0
}

/// Read the is_queued flag.
///
/// # Safety
///
/// `ptr` must point to a live `Task<F>`.
#[inline]
pub(crate) unsafe fn is_queued(ptr: *mut u8) -> bool {
    // SAFETY: caller upholds ptr validity; state is at offset 24 in repr(C) Task.
    (unsafe { state_load(ptr) }) & QUEUED != 0
}

/// Set the `is_queued` flag.
///
/// # Safety
///
/// `ptr` must point to a live `Task<F>`.
#[inline]
pub(crate) unsafe fn set_queued(ptr: *mut u8, queued: bool) {
    // SAFETY: caller upholds ptr validity; state is at offset 24 in repr(C) Task.
    let state = unsafe { state_ref(ptr) };
    if queued {
        state.fetch_or(QUEUED, Ordering::Release);
    } else {
        state.fetch_and(!QUEUED, Ordering::Release);
    }
}

/// Atomically try to set QUEUED from false to true. Returns true if
/// successful (was not queued). Used by cross-thread wakers.
///
/// # Safety
///
/// `ptr` must point to a live `Task<F>`.
#[inline]
pub(crate) unsafe fn try_set_queued(ptr: *mut u8) -> bool {
    // SAFETY: caller upholds ptr validity; state is at offset 24 in repr(C) Task.
    let state = unsafe { state_ref(ptr) };
    // fetch_or always sets the bit. Check if it was already set.
    let prev = state.fetch_or(QUEUED, Ordering::AcqRel);
    (prev & QUEUED) == 0
}

/// Clear the QUEUED flag.
///
/// # Safety
///
/// `ptr` must point to a live `Task<F>`.
#[inline]
pub(crate) unsafe fn clear_queued(ptr: *mut u8) {
    // SAFETY: caller upholds ptr validity; state is at offset 24 in repr(C) Task.
    let state = unsafe { state_ref(ptr) };
    state.fetch_and(!QUEUED, Ordering::Release);
}

/// Check if ABORTED flag is set.
///
/// # Safety
///
/// `ptr` must point to a live `Task<F>`.
#[inline]
pub(crate) unsafe fn is_aborted(ptr: *mut u8) -> bool {
    // SAFETY: caller upholds ptr validity; state is at offset 24 in repr(C) Task.
    (unsafe { state_load(ptr) }) & ABORTED != 0
}

/// Set the ABORTED flag.
///
/// # Safety
///
/// `ptr` must point to a live `Task<F>`.
#[inline]
pub(crate) unsafe fn set_aborted(ptr: *mut u8) {
    // SAFETY: caller upholds ptr validity; state is at offset 24 in repr(C) Task.
    let state = unsafe { state_ref(ptr) };
    state.fetch_or(ABORTED, Ordering::Release);
}

/// Check if HAS_JOIN flag is set.
///
/// # Safety
///
/// `ptr` must point to a live `Task<F>`.
#[inline]
pub(crate) unsafe fn has_join(ptr: *mut u8) -> bool {
    // SAFETY: caller upholds ptr validity; state is at offset 24 in repr(C) Task.
    (unsafe { state_load(ptr) }) & HAS_JOIN != 0
}

/// Clear the HAS_JOIN flag.
///
/// # Safety
///
/// `ptr` must point to a live `Task<F>`.
#[inline]
pub(crate) unsafe fn clear_has_join(ptr: *mut u8) {
    // SAFETY: caller upholds ptr validity; state is at offset 24 in repr(C) Task.
    let state = unsafe { state_ref(ptr) };
    state.fetch_and(!HAS_JOIN, Ordering::Release);
}

/// Set the OUTPUT_TAKEN flag.
///
/// # Safety
///
/// `ptr` must point to a live, completed `Task<F>`. Single-threaded.
#[inline]
unsafe fn set_output_taken(ptr: *mut u8) {
    // SAFETY: caller upholds ptr validity; state is at offset 24 in repr(C) Task.
    let state = unsafe { state_ref(ptr) };
    state.fetch_or(OUTPUT_TAKEN, Ordering::Release);
}

/// Get a raw pointer to the `cross_next` atomic pointer.
///
/// # Safety
///
/// `ptr` must point to a live `Task<F>`.
#[inline]
pub(crate) unsafe fn cross_next(ptr: *mut u8) -> *const AtomicPtr<u8> {
    // SAFETY: cross_next is at offset 32 in repr(C) Task.
    unsafe { ptr.add(32).cast::<AtomicPtr<u8>>() }
}

/// Read the storage offset from the task header.
///
/// # Safety
///
/// `ptr` must point to a live `Task<S>`.
#[inline]
pub(crate) unsafe fn storage_offset(ptr: *mut u8) -> usize {
    // SAFETY: storage_offset is u16 at offset 56 in repr(C) Task.
    unsafe { *(ptr.add(56).cast::<u16>()) as usize }
}

/// Read the `cross_wake_ctx` pointer from the task header.
///
/// Returns the runtime's [`CrossWakeContext`] pointer (Arc-backed,
/// heap-stable) set at spawn time, or null for tasks not associated
/// with any runtime (test path).
///
/// # Safety
///
/// `ptr` must point to a live `Task<S>` (header still valid).
#[inline]
pub(crate) unsafe fn header_cross_wake_ctx(ptr: *mut u8) -> *const CrossWakeContext {
    // SAFETY: `cross_wake_ctx` is `*const CrossWakeContext` at offset 64
    // in `repr(C) Task`. The field is initialized exactly once at spawn
    // time under the spawning thread's exclusive ownership, then made
    // visible to other threads via Arc/refcount publication (any TaskRef
    // holder transitively keeps the owning runtime's Arc alive, and the
    // Arc's atomic-counter publication establishes happens-before for the
    // read). Immutable after init — concurrent reads from any thread are
    // sound. dispose_terminal explicitly reads this from foreign threads
    // when routing terminal drops from cross-thread waker holders.
    unsafe { *(ptr.add(64).cast::<*const CrossWakeContext>()) }
}

/// Store a waker for the JoinHandle awaiter.
///
/// # Safety
///
/// `ptr` must point to a live `Task<F>`. Single-threaded access only.
#[inline]
unsafe fn set_join_waker(ptr: *mut u8, waker: Waker) {
    // SAFETY: join_waker is UnsafeCell<Option<Waker>> at offset 40.
    let cell = unsafe { &*ptr.add(40).cast::<UnsafeCell<Option<Waker>>>() };
    // SAFETY: task state is accessed only under the executor's single-thread invariant.
    unsafe { *cell.get() = Some(waker) };
}

/// Take the join waker (if any).
///
/// # Safety
///
/// `ptr` must point to a live `Task<F>`. Single-threaded access only.
#[inline]
pub(crate) unsafe fn take_join_waker(ptr: *mut u8) -> Option<Waker> {
    // SAFETY: caller upholds ptr validity; join_waker is UnsafeCell<Option<Waker>> at offset 40.
    let cell = unsafe { &*ptr.add(40).cast::<UnsafeCell<Option<Waker>>>() };
    // SAFETY: task state is accessed only under the executor's single-thread invariant.
    unsafe { (*cell.get()).take() }
}

/// Poll the task's future.
///
/// # Safety
///
/// `ptr` must point to a live `Task<F>`.
/// The future must not have been dropped.
#[inline]
pub(crate) unsafe fn poll_task(ptr: *mut u8, cx: &mut Context<'_>) -> Poll<()> {
    // SAFETY: poll_fn is at offset 0 in repr(C) Task.
    let poll_fn: unsafe fn(*mut u8, &mut Context<'_>) -> Poll<()> =
        unsafe { *(ptr as *const unsafe fn(*mut u8, &mut Context<'_>) -> Poll<()>) };
    // Pass the task base pointer — the trampoline reads storage_offset.
    // SAFETY: poll_fn is a valid function pointer for this task type; ptr is a live task.
    unsafe { poll_fn(ptr, cx) }
}

/// Drop the task's future (or output) in place.
///
/// # Safety
///
/// `ptr` must point to a live `Task<F>`. Must only be called once.
#[inline]
pub(crate) unsafe fn drop_task_future(ptr: *mut u8) {
    // SAFETY: drop_fn is at offset 8 in repr(C) Task.
    let drop_fn: unsafe fn(*mut u8) = unsafe { *(ptr.add(8) as *const unsafe fn(*mut u8)) };
    // Pass base pointer — the trampoline reads storage_offset.
    // SAFETY: drop_fn is a valid function pointer for this task; ptr is a live task.
    unsafe { drop_fn(ptr) }
}

/// Call the task's free function to deallocate its storage.
///
/// # Safety
///
/// `ptr` must point to a `Task<F>` whose future has already been dropped.
/// Must only be called once (after state reaches TERMINAL).
#[inline]
pub(crate) unsafe fn free_task(ptr: *mut u8) {
    // SAFETY: free_fn is at offset 16 in repr(C) Task.
    let free_fn: unsafe fn(*mut u8) = unsafe { *(ptr.add(16) as *const unsafe fn(*mut u8)) };
    // SAFETY: free_fn is a valid function pointer; the future has already been dropped.
    unsafe { free_fn(ptr) }
}

// =============================================================================
// Type-erased vtable functions
// =============================================================================

/// Poll trampoline for joinable tasks (Output = T).
///
/// On completion: drops F, writes T into the same location, overwrites
/// drop_fn to target T instead of F.
///
/// # Safety
///
/// `ptr` must point to a live `Task<F>`. The future must not have been dropped.
unsafe fn poll_join<F: Future>(ptr: *mut u8, cx: &mut Context<'_>) -> Poll<()>
where
    F::Output: 'static,
{
    // Check if aborted
    // SAFETY: caller upholds ptr validity; reading ABORTED flag atomically.
    if unsafe { is_aborted(ptr) } {
        return Poll::Ready(());
    }

    // SAFETY: caller upholds ptr validity; storage_offset is initialized at construction.
    let future_ptr = unsafe { ptr.add(storage_offset(ptr)) };
    // SAFETY: the task future is pinned in place; we never move it.
    let future = unsafe { Pin::new_unchecked(&mut *future_ptr.cast::<F>()) };
    match future.poll(cx) {
        Poll::Pending => Poll::Pending,
        Poll::Ready(value) => {
            // SAFETY: drop_fn is at offset 8 in repr(C) Task; ptr is a live task.
            let drop_fn_slot = unsafe { ptr.add(8).cast::<unsafe fn(*mut u8)>() };
            // 1. Overwrite drop_fn to no-op BEFORE dropping F.
            //    If F::drop() panics, this prevents double-drop —
            //    subsequent cleanup calls the no-op instead of
            //    drop_future_in_union on a partially-dropped F.
            //    The output (value) is dropped during unwind (stack-owned).
            // SAFETY: drop_fn_slot points to the drop_fn field; written before F is dropped to prevent double-drop.
            unsafe { *drop_fn_slot = drop_noop };
            // 2. Drop the future in place (panic-safe now)
            // SAFETY: future_ptr points to a live F at storage_offset; drop_fn overwritten to drop_noop first.
            unsafe { std::ptr::drop_in_place(future_ptr.cast::<F>()) };
            // 3. Write output T into the same location
            // SAFETY: future_ptr storage is sized for F::Output via FutureOrOutput<F, T> union; F has been dropped.
            unsafe { std::ptr::write(future_ptr.cast::<F::Output>(), value) };
            // 4. Overwrite drop_fn: now drops T instead of F
            // SAFETY: drop_fn_slot points to the drop_fn field; T is now live at storage_offset.
            unsafe { *drop_fn_slot = drop_output::<F::Output> };
            Poll::Ready(())
        }
    }
}

/// Drop trampoline for futures stored directly (fire-and-forget tasks).
///
/// # Safety
///
/// `ptr` must point to a live `Task<F>` with a live future at `storage_offset`.
#[cfg(test)]
unsafe fn drop_future<F>(ptr: *mut u8) {
    // SAFETY: caller upholds ptr validity; storage_offset is initialized at construction.
    let future_ptr = unsafe { ptr.add(storage_offset(ptr)) };
    // SAFETY: future_ptr points to a live F at storage_offset; caller ensures this is called once.
    unsafe { std::ptr::drop_in_place(future_ptr.cast::<F>()) }
}

/// Drop trampoline for futures stored in FutureOrOutput union.
///
/// # Safety
///
/// `ptr` must point to a `Task<FutureOrOutput<F, T>>` with a live future.
unsafe fn drop_future_in_union<F: Future>(ptr: *mut u8) {
    // SAFETY: caller upholds ptr validity; storage_offset is initialized at construction.
    let storage_ptr = unsafe { ptr.add(storage_offset(ptr)) };
    // The future is at the start of the union (same offset as the union itself).
    // SAFETY: storage_ptr points to a live F at the union's start; caller ensures this is called once.
    unsafe { std::ptr::drop_in_place(storage_ptr.cast::<F>()) }
}

/// No-op drop trampoline. Installed temporarily during the F→T transition
/// in `poll_join` to prevent double-drop if `F::drop()` panics.
///
/// # Safety
///
/// Always safe — does nothing.
unsafe fn drop_noop(_ptr: *mut u8) {}

/// Drop trampoline for output values. Receives the task base pointer.
///
/// Installed by `poll_join` after the future completes, replacing `drop_future`.
///
/// # Safety
///
/// `ptr` must point to a `Task` with a live `T` at `storage_offset`.
unsafe fn drop_output<T>(ptr: *mut u8) {
    // SAFETY: caller upholds ptr validity; storage_offset is initialized at construction.
    let output_ptr = unsafe { ptr.add(storage_offset(ptr)) };
    // SAFETY: output_ptr points to a live T at storage_offset; caller ensures this is called once.
    unsafe { std::ptr::drop_in_place(output_ptr.cast::<T>()) }
}

/// Free function for Box-allocated tasks.
///
/// Deallocates the memory without running destructors — the future/output
/// was already dropped via `drop_task_future`, and the header fields
/// are all trivial. Only the heap allocation needs to be freed.
///
/// # Safety
///
/// `ptr` must have been produced by `Box::into_raw(Box::new(Task<F>))`.
/// The value at offset 64 must already be dropped.
unsafe fn box_free<F>(ptr: *mut u8) {
    // SAFETY: Layout matches what Box::new(Task<F>) allocated.
    let layout = std::alloc::Layout::new::<Task<F>>();
    // SAFETY: ptr was produced by Box::into_raw(Box::new(Task<F>)); layout matches the allocation.
    unsafe { std::alloc::dealloc(ptr, layout) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn task_header_size() {
        assert_eq!(TASK_HEADER_SIZE, 72);
        assert_eq!(std::mem::size_of::<Task<()>>(), 72);
    }

    #[test]
    fn task_layout_offsets() {
        assert_eq!(std::mem::offset_of!(Task<()>, poll_fn), 0);
        assert_eq!(std::mem::offset_of!(Task<()>, drop_fn), 8);
        assert_eq!(std::mem::offset_of!(Task<()>, free_fn), 16);
        assert_eq!(std::mem::offset_of!(Task<()>, state), 24);
        assert_eq!(std::mem::offset_of!(Task<()>, cross_next), 32);
        assert_eq!(std::mem::offset_of!(Task<()>, join_waker), 40);
        assert_eq!(std::mem::offset_of!(Task<()>, storage_offset), 56);
        assert_eq!(std::mem::offset_of!(Task<()>, _pad), 58);
        assert_eq!(std::mem::offset_of!(Task<()>, tracker_key), 60);
        assert_eq!(std::mem::offset_of!(Task<()>, cross_wake_ctx), 64);
        assert_eq!(std::mem::offset_of!(Task<()>, storage), 72);
    }

    #[test]
    fn task_size_with_future() {
        #[allow(dead_code)]
        struct SmallFuture([u8; 24]);
        impl Future for SmallFuture {
            type Output = ();
            fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<()> {
                Poll::Ready(())
            }
        }

        // 72 byte header + 24 byte future = 96 bytes
        assert_eq!(
            std::mem::size_of::<Task<SmallFuture>>(),
            TASK_HEADER_SIZE + 24
        );
    }

    #[test]
    fn packed_state_fire_and_forget() {
        struct Noop;
        impl Future for Noop {
            type Output = ();
            fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<()> {
                Poll::Ready(())
            }
        }

        let task = Box::new(Task::new_boxed(Noop, 0));
        let ptr = Box::into_raw(task) as *mut u8;

        // SAFETY: ptr is a valid task created above via Box::into_raw.
        // All task:: functions are called on this live task pointer.
        unsafe {
            // Initial state: 1 ref, no flags
            assert_eq!(ref_count(ptr), 1);
            assert!(!is_completed(ptr));
            assert!(!is_queued(ptr));
            assert!(!has_join(ptr));
            assert!(!is_terminal(ptr));

            // Set and clear queued
            set_queued(ptr, true);
            assert!(is_queued(ptr));
            set_queued(ptr, false);
            assert!(!is_queued(ptr));

            // complete_and_unref with 1 ref → TERMINAL
            drop_task_future(ptr);
            assert!(matches!(complete_and_unref(ptr), FreeAction::FreeBox));
            assert!(is_terminal(ptr));

            free_task(ptr);
        }
    }

    #[test]
    fn packed_state_joinable() {
        struct Noop;
        impl Future for Noop {
            type Output = u64;
            fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<u64> {
                Poll::Ready(42)
            }
        }

        let ptr = box_spawn_joinable(Noop, 7, std::ptr::null());
        // SAFETY: ptr is a valid joinable task. All task:: functions are
        // called on this live task pointer through its lifecycle.
        unsafe {
            assert!(has_join(ptr));
            assert!(!is_aborted(ptr));
            assert_eq!(ref_count(ptr), 2); // executor + JoinHandle
            assert_eq!(tracker_key(ptr), 7);

            // Simulate: handle drops before completion
            clear_has_join(ptr);
            assert!(!has_join(ptr));
            assert!(matches!(ref_dec(ptr), FreeAction::Retain)); // still 1 ref, not completed

            // complete_and_unref → TERMINAL
            drop_task_future(ptr);
            assert!(matches!(complete_and_unref(ptr), FreeAction::FreeBox));
            assert!(is_terminal(ptr));

            free_task(ptr);
        }
    }

    #[test]
    fn packed_state_joinable_completion_before_handle_drop() {
        struct Noop;
        impl Future for Noop {
            type Output = u64;
            fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<u64> {
                Poll::Ready(42)
            }
        }

        let ptr = box_spawn_joinable(Noop, 0, std::ptr::null());
        // SAFETY: ptr is a valid joinable task. All task:: functions are
        // called on this live task pointer through its lifecycle.
        unsafe {
            // complete_and_unref with 2 refs → not terminal
            drop_task_future(ptr);
            assert!(matches!(complete_and_unref(ptr), FreeAction::Retain));
            assert!(is_completed(ptr));
            assert_eq!(ref_count(ptr), 1);

            // Handle drop: clear HAS_JOIN, ref_dec → TERMINAL
            clear_has_join(ptr);
            assert!(matches!(ref_dec(ptr), FreeAction::FreeBox));
            assert!(is_terminal(ptr));

            free_task(ptr);
        }
    }

    #[test]
    fn packed_state_cross_thread_waker_scenario() {
        struct Noop;
        impl Future for Noop {
            type Output = u64;
            fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<u64> {
                Poll::Ready(42)
            }
        }

        let ptr = box_spawn_joinable(Noop, 0, std::ptr::null());
        // SAFETY: ptr is a valid joinable task. Simulating the cross-thread
        // waker lifecycle: ref_inc for waker clone, complete_and_unref for
        // executor, ref_dec for handle and waker drops.
        unsafe {
            // Waker clone: ref_inc
            ref_inc(ptr);
            assert_eq!(ref_count(ptr), 3);

            // complete_and_unref: executor releases its ref
            drop_task_future(ptr);
            assert!(matches!(complete_and_unref(ptr), FreeAction::Retain));

            // Handle drop: clear HAS_JOIN, ref_dec
            clear_has_join(ptr);
            assert!(matches!(ref_dec(ptr), FreeAction::Retain)); // still 1 ref (waker)

            // Waker drop: ref_dec → TERMINAL
            assert!(matches!(ref_dec(ptr), FreeAction::FreeBox));
            assert!(is_terminal(ptr));

            free_task(ptr);
        }
    }

    // =========================================================================
    // Panic safety — drop_fn transitions
    // =========================================================================

    /// Future whose Drop impl panics. Used to verify the drop_noop guard
    /// in poll_join prevents double-drop.
    struct PanickingDrop {
        drop_count: *mut u32,
    }

    impl Future for PanickingDrop {
        type Output = u64;
        fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<u64> {
            Poll::Ready(42)
        }
    }

    impl Drop for PanickingDrop {
        fn drop(&mut self) {
            // SAFETY: drop_count is a valid pointer to a u32 on the test's stack; exclusive access during drop.
            unsafe { *self.drop_count += 1 };
            panic!("intentional drop panic");
        }
    }

    #[test]
    fn poll_join_panic_in_drop_prevents_double_drop() {
        use std::task::{RawWaker, RawWakerVTable, Waker};

        static NOOP_VTABLE: RawWakerVTable =
            RawWakerVTable::new(|p| RawWaker::new(p, &NOOP_VTABLE), |_| {}, |_| {}, |_| {});
        // SAFETY: all vtable functions are no-ops; null data is never dereferenced.
        let waker = unsafe { Waker::from_raw(RawWaker::new(std::ptr::null(), &NOOP_VTABLE)) };
        let mut cx = Context::from_waker(&waker);

        let mut drop_count: u32 = 0;
        let ptr = box_spawn_joinable(
            PanickingDrop {
                drop_count: &raw mut drop_count,
            },
            0,
            std::ptr::null(),
        );

        // poll_join completes the future, then drops F — which panics.
        // SAFETY: ptr is a valid task; poll_task's safety contract is upheld for the test task.
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| unsafe {
            poll_task(ptr, &mut cx)
        }));

        // The panic should have been caught.
        assert!(result.is_err(), "expected panic from PanickingDrop");
        // F was dropped exactly once (by poll_join, before the panic propagated).
        assert_eq!(drop_count, 1, "future should be dropped exactly once");

        // drop_fn should now be drop_noop — calling it must NOT double-drop F.
        // SAFETY: ptr is a valid task; drop_fn was transitioned to drop_noop
        // after the panic in poll_join.
        unsafe { drop_task_future(ptr) };
        assert_eq!(
            drop_count, 1,
            "drop_task_future after panic must be a no-op (drop_noop)"
        );

        // Clean up: dec both refs (executor + JoinHandle), then free.
        // SAFETY: ptr is a valid task; decrementing both refs to reach terminal.
        unsafe {
            ref_dec(ptr);
            ref_dec(ptr);
            free_task(ptr);
        }
    }

    #[test]
    fn drop_fn_transitions_correctly_on_normal_completion() {
        use std::task::{RawWaker, RawWakerVTable, Waker};

        static NOOP_VTABLE: RawWakerVTable =
            RawWakerVTable::new(|p| RawWaker::new(p, &NOOP_VTABLE), |_| {}, |_| {}, |_| {});
        // SAFETY: all vtable functions are no-ops; null data is never dereferenced.
        let waker = unsafe { Waker::from_raw(RawWaker::new(std::ptr::null(), &NOOP_VTABLE)) };
        let mut cx = Context::from_waker(&waker);

        static mut OUTPUT_DROP_COUNT: u32 = 0;
        struct TrackedOutput;
        impl Drop for TrackedOutput {
            fn drop(&mut self) {
                // SAFETY: single-threaded test; no other references to OUTPUT_DROP_COUNT.
                unsafe { OUTPUT_DROP_COUNT += 1 };
            }
        }

        struct ProduceTracked;
        impl Future for ProduceTracked {
            type Output = TrackedOutput;
            fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<TrackedOutput> {
                Poll::Ready(TrackedOutput)
            }
        }

        let ptr = box_spawn_joinable(ProduceTracked, 0, std::ptr::null());

        // Poll to completion — F dropped, T written, drop_fn → drop_output.
        // SAFETY: ptr is a valid task; poll_task's safety contract is upheld for the test task.
        let result = unsafe { poll_task(ptr, &mut cx) };
        assert!(result.is_ready());

        // drop_fn should now target T (TrackedOutput).
        // SAFETY: static mut access in single-threaded test.
        unsafe { OUTPUT_DROP_COUNT = 0 };
        // SAFETY: ptr is a valid completed task; drop_fn now targets the output T.
        unsafe { drop_task_future(ptr) };
        assert_eq!(
            // SAFETY: static mut access in single-threaded test.
            unsafe { OUTPUT_DROP_COUNT },
            1,
            "drop_fn should drop the output exactly once"
        );

        // Clean up.
        // SAFETY: ptr is a valid task; decrementing both refs to reach terminal.
        unsafe {
            ref_dec(ptr);
            ref_dec(ptr);
            free_task(ptr);
        }
    }

    // =========================================================================
    // Packed state word — SIGABRT root cause regression tests
    // =========================================================================

    #[test]
    fn packed_state_fire_and_forget_terminal() {
        // Box task with 1 ref (no JoinHandle). complete_and_unref → FreeBox.
        // Verify terminal state is exactly TERMINAL_BOX (1).
        struct Noop;
        impl Future for Noop {
            type Output = ();
            fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<()> {
                Poll::Ready(())
            }
        }

        let task = Box::new(Task::new_boxed(Noop, 0));
        let ptr = Box::into_raw(task) as *mut u8;

        // SAFETY: ptr is a valid fire-and-forget task created above.
        // Exercising the full lifecycle: drop future, complete, free.
        unsafe {
            assert_eq!(ref_count(ptr), 1);
            assert!(!has_join(ptr));

            drop_task_future(ptr);
            let action = complete_and_unref(ptr);
            assert_eq!(action, FreeAction::FreeBox);

            let s = state_load(ptr);
            assert_eq!(s, COMPLETED, "terminal state must have COMPLETED set");
            assert_eq!(s, 1);
            assert!(is_terminal(ptr));

            free_task(ptr);
        }
    }

    #[test]
    fn packed_state_slab_flag_terminal() {
        // Task with SLAB_ALLOCATED set. complete_and_unref → FreeSlab.
        // Verify terminal state is exactly TERMINAL_SLAB (33).
        struct Noop;
        impl Future for Noop {
            type Output = u64;
            fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<u64> {
                Poll::Ready(42)
            }
        }

        // Use new_joinable_slab to get SLAB_ALLOCATED flag set at construction.
        // Provide a free_fn that does Box dealloc (we box it manually below).
        type Storage = FutureOrOutput<Noop, u64>;
        unsafe fn slab_free(ptr: *mut u8) {
            // SAFETY: ptr was produced by Box::into_raw(Box::new(Task<Storage>)); layout matches the allocation.
            unsafe {
                let layout = std::alloc::Layout::new::<Task<Storage>>();
                std::alloc::dealloc(ptr, layout);
            }
        }

        let task = new_joinable_slab(Noop, 0, slab_free, std::ptr::null());
        let ptr = Box::into_raw(Box::new(task)) as *mut u8;

        // SAFETY: ptr is a valid slab-flagged joinable task. Exercising the
        // full lifecycle: handle detach, executor completion, free.
        unsafe {
            assert_eq!(ref_count(ptr), 2); // executor + JoinHandle
            assert!(has_join(ptr));

            // Simulate handle detach: clear HAS_JOIN + ref_dec
            clear_has_join(ptr);
            assert_eq!(ref_dec(ptr), FreeAction::Retain);
            assert_eq!(ref_count(ptr), 1);

            // Executor completes task
            drop_task_future(ptr);
            let action = complete_and_unref(ptr);
            assert_eq!(action, FreeAction::FreeSlab);

            let s = state_load(ptr);
            assert_eq!(
                s,
                COMPLETED | SLAB_ALLOCATED,
                "terminal state must be COMPLETED | SLAB_ALLOCATED"
            );
            assert_eq!(s, 33);
            assert!(is_terminal(ptr));

            slab_free(ptr);
        }
    }

    #[test]
    fn packed_state_joinable_handle_drops_first() {
        // Joinable task (2 refs + HAS_JOIN). Handle drops first:
        // clear HAS_JOIN → ref_dec → 1 ref remaining.
        // Then complete_and_unref → terminal.
        struct Noop;
        impl Future for Noop {
            type Output = u64;
            fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<u64> {
                Poll::Ready(42)
            }
        }

        let ptr = box_spawn_joinable(Noop, 0, std::ptr::null());
        // SAFETY: ptr is a valid joinable task. Exercising handle-drops-first lifecycle.
        unsafe {
            assert_eq!(ref_count(ptr), 2);
            assert!(has_join(ptr));

            // Handle drops: clear HAS_JOIN, ref_dec
            clear_has_join(ptr);
            assert!(!has_join(ptr));
            assert_eq!(ref_dec(ptr), FreeAction::Retain);
            assert_eq!(ref_count(ptr), 1);
            assert!(!is_terminal(ptr));

            // Executor completes
            drop_task_future(ptr);
            assert_eq!(complete_and_unref(ptr), FreeAction::FreeBox);
            assert!(is_terminal(ptr));

            free_task(ptr);
        }
    }

    #[test]
    fn packed_state_joinable_completion_first_then_handle() {
        // Joinable task. Completion fires first (Retain because 2 refs).
        // Then handle clears HAS_JOIN + ref_dec → FreeBox.
        struct Noop;
        impl Future for Noop {
            type Output = u64;
            fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<u64> {
                Poll::Ready(42)
            }
        }

        let ptr = box_spawn_joinable(Noop, 0, std::ptr::null());
        // SAFETY: ptr is a valid joinable task. Exercising completion-first lifecycle.
        unsafe {
            // complete_and_unref: sets COMPLETED, dec ref → 1 ref remains
            drop_task_future(ptr);
            assert_eq!(complete_and_unref(ptr), FreeAction::Retain);
            assert!(is_completed(ptr));
            assert_eq!(ref_count(ptr), 1);

            // Handle drops: clear HAS_JOIN, ref_dec → terminal
            clear_has_join(ptr);
            assert_eq!(ref_dec(ptr), FreeAction::FreeBox);
            assert!(is_terminal(ptr));

            free_task(ptr);
        }
    }

    #[test]
    fn packed_state_waker_clone_lifecycle() {
        // Joinable task (2 refs). Waker clone adds 3rd ref.
        // complete_and_unref → Retain (2 refs remain, HAS_JOIN still set).
        // Handle drops (clear HAS_JOIN + ref_dec) → Retain (1 ref from waker).
        // Waker drops (ref_dec) → FreeBox.
        struct Noop;
        impl Future for Noop {
            type Output = u64;
            fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<u64> {
                Poll::Ready(42)
            }
        }

        let ptr = box_spawn_joinable(Noop, 0, std::ptr::null());
        // SAFETY: ptr is a valid joinable task. Exercising waker-clone lifecycle:
        // 3 refs (executor + handle + waker), completion, handle drop, waker drop.
        unsafe {
            // Waker clone: ref_inc
            ref_inc(ptr);
            assert_eq!(ref_count(ptr), 3);

            // Executor completes: complete_and_unref
            drop_task_future(ptr);
            assert_eq!(complete_and_unref(ptr), FreeAction::Retain);
            assert_eq!(ref_count(ptr), 2);

            // Handle drops: clear HAS_JOIN, ref_dec
            clear_has_join(ptr);
            assert_eq!(ref_dec(ptr), FreeAction::Retain);
            assert_eq!(ref_count(ptr), 1);

            // Waker drops: ref_dec → terminal
            assert_eq!(ref_dec(ptr), FreeAction::FreeBox);
            assert!(is_terminal(ptr));

            free_task(ptr);
        }
    }

    #[test]
    fn packed_state_leaked_flag_prevents_terminal() {
        // If HAS_JOIN is NOT cleared before the final ref_dec, the state
        // won't reach terminal (HAS_JOIN is a lifecycle flag that blocks it).
        // Result: Retain. This is safe — the lifecycle flag prevents
        // premature free.
        struct Noop;
        impl Future for Noop {
            type Output = u64;
            fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<u64> {
                Poll::Ready(42)
            }
        }

        let ptr = box_spawn_joinable(Noop, 0, std::ptr::null());
        // SAFETY: ptr is a valid joinable task. Testing that a leaked
        // HAS_JOIN flag prevents terminal state (safety net against misuse).
        unsafe {
            // complete_and_unref with 2 refs → Retain
            drop_task_future(ptr);
            assert_eq!(complete_and_unref(ptr), FreeAction::Retain);

            // ref_dec WITHOUT clearing HAS_JOIN → still not terminal
            // because HAS_JOIN is a lifecycle flag that blocks terminal.
            assert_eq!(ref_dec(ptr), FreeAction::Retain);
            assert!(!is_terminal(ptr));

            // State is COMPLETED | HAS_JOIN | 0 refs — leaked but safe.
            // In real code this can't happen (JoinHandle::Drop always
            // clears HAS_JOIN), but the packed state correctly prevents
            // a free even if it did.
            let s = state_load(ptr);
            assert_eq!(s & COMPLETED, COMPLETED);
            assert_eq!(s & HAS_JOIN, HAS_JOIN);
            assert_eq!(ref_count(ptr), 0);

            // Clean up: manually clear HAS_JOIN to reach terminal, then free.
            clear_has_join(ptr);
            assert!(is_terminal(ptr));
            free_task(ptr);
        }
    }

    // =========================================================================
    // TaskRef — RAII inc/dec discipline
    // =========================================================================

    #[test]
    fn taskref_acquire_drop_balances_refcount() {
        // Acquire a TaskRef on a task with rc=1; rc goes to 2. Drop the
        // TaskRef; rc goes back to 1. Verifies acquire(ref_inc) is paired
        // with Drop(ref_dec).
        let task = Box::new(Task::new_boxed(async {}, 0));
        let ptr = Box::into_raw(task) as *mut u8;

        // SAFETY: ptr is a valid task. Testing acquire/drop refcount balance.
        unsafe {
            assert_eq!(ref_count(ptr), 1);
            let task_ref = TaskRef::acquire(ptr);
            assert_eq!(ref_count(ptr), 2);
            drop(task_ref); // Not terminal — rc 2 → 1
            assert_eq!(ref_count(ptr), 1);

            // Cleanup: complete and free directly (no TaskRef path).
            drop_task_future(ptr);
            assert!(matches!(complete_and_unref(ptr), FreeAction::FreeBox));
            free_task(ptr);
        }
    }

    #[test]
    fn taskref_from_owned_drop_balances_refcount() {
        // Manually ref_inc, then wrap with from_owned (no extra inc).
        // Drop releases the manual ref. Verifies from_owned's "wrap a
        // pre-incremented pointer" contract.
        let task = Box::new(Task::new_boxed(async {}, 0));
        let ptr = Box::into_raw(task) as *mut u8;

        // SAFETY: ptr is a valid task. Testing from_owned wraps a
        // pre-incremented pointer without extra ref_inc.
        unsafe {
            assert_eq!(ref_count(ptr), 1);
            ref_inc(ptr); // simulate handoff (e.g. RawWaker::data ownership)
            assert_eq!(ref_count(ptr), 2);
            let task_ref = TaskRef::from_owned(ptr);
            // No additional ref_inc — TaskRef takes the existing ref.
            assert_eq!(ref_count(ptr), 2);
            drop(task_ref); // releases the manual ref
            assert_eq!(ref_count(ptr), 1);

            // Cleanup.
            drop_task_future(ptr);
            assert!(matches!(complete_and_unref(ptr), FreeAction::FreeBox));
            free_task(ptr);
        }
    }

    #[test]
    fn taskref_drop_non_terminal_no_dispose() {
        // Drop a TaskRef when refcount > 1 — should NOT invoke
        // dispose_terminal. Verifies Drop's terminal gate (Retain branch
        // returns immediately).
        let task = Box::new(Task::new_boxed(async {}, 0));
        let ptr = Box::into_raw(task) as *mut u8;

        // SAFETY: ptr is a valid task. Verifying that dropping a TaskRef
        // when refcount > 1 does NOT invoke dispose_terminal.
        unsafe {
            // rc=1, acquire to rc=2, drop to rc=1. Not terminal (no
            // COMPLETED, lifecycle flags clear). Drop hits the Retain
            // branch — no dispose_terminal call. If dispose_terminal
            // were called with a non-terminal task it would assert (or
            // worse, free a live task).
            let task_ref = TaskRef::acquire(ptr);
            assert_eq!(ref_count(ptr), 2);
            drop(task_ref);
            assert_eq!(ref_count(ptr), 1);
            assert!(!is_completed(ptr));

            // Cleanup.
            drop_task_future(ptr);
            assert!(matches!(complete_and_unref(ptr), FreeAction::FreeBox));
            free_task(ptr);
        }
    }

    #[test]
    fn packed_state_many_refs_converge() {
        // Clone waker 10 times (ref_inc 10x), complete, then ref_dec 10x.
        // Only the last ref_dec returns FreeBox. All others Retain.
        struct Noop;
        impl Future for Noop {
            type Output = u64;
            fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<u64> {
                Poll::Ready(42)
            }
        }

        let ptr = box_spawn_joinable(Noop, 0, std::ptr::null());
        // SAFETY: ptr is a valid joinable task. Stress-testing convergence
        // of 10 waker refs to terminal state.
        unsafe {
            // 10 waker clones: ref 2 → 12
            for _ in 0..10 {
                ref_inc(ptr);
            }
            assert_eq!(ref_count(ptr), 12);

            // Executor completes: ref 12 → 11
            drop_task_future(ptr);
            assert_eq!(complete_and_unref(ptr), FreeAction::Retain);
            assert_eq!(ref_count(ptr), 11);

            // Handle drops: clear HAS_JOIN, ref_dec → 10
            clear_has_join(ptr);
            assert_eq!(ref_dec(ptr), FreeAction::Retain);
            assert_eq!(ref_count(ptr), 10);

            // Drop 9 waker refs — all Retain
            for i in 0..9 {
                assert_eq!(
                    ref_dec(ptr),
                    FreeAction::Retain,
                    "ref_dec #{i} should Retain"
                );
            }
            assert_eq!(ref_count(ptr), 1);

            // Last waker drop → FreeBox
            assert_eq!(ref_dec(ptr), FreeAction::FreeBox);
            assert!(is_terminal(ptr));

            free_task(ptr);
        }
    }
}
