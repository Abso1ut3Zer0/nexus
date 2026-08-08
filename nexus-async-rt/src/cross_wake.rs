//! Cross-thread wake infrastructure.
//!
//! An intrusive MPSC queue (Vyukov style) for waking tasks from other
//! threads. Each task's header contains an `AtomicPtr<u8>` (`cross_next`)
//! used as the intrusive link — zero allocation per wake.
//!
//! The queue is paired with a `mio::Waker` (eventfd) to interrupt the
//! runtime's epoll when a cross-thread wake arrives.
//!
//! Local wakes (same thread) continue using the fast TLS Vec path.
//! Cross-thread wakes use this queue + eventfd. The executor drains
//! both on each poll cycle.

use std::cell::{Cell, UnsafeCell};
use std::sync::Arc;
use std::sync::atomic::{AtomicPtr, Ordering};

use crate::task;

// =============================================================================
// TLS — cross-wake context accessible during block_on
// =============================================================================
//
// Two slots, separate scopes, separate consumers:
//
// - `CTX_CROSS_WAKE: *const Arc<CrossWakeContext>`
//   Pointer to the Runtime's `cross_wake` Arc field. Installed at
//   `run_loop` entry, cleared on exit. Used by `cross_wake_context()`
//   to clone the Arc for new cross-thread waker construction (channel
//   slots, tokio_compat). Scope is `block_on` because that's when
//   user task code runs and needs to construct cross-thread wakers.
//   Pointer-to-field — safe under `&mut self` during run_loop.
//
// - `CURRENT_RUNTIME_CTX: *const CrossWakeContext`
//   `Arc::as_ptr` value pointing into the Arc allocation (heap-stable,
//   doesn't dangle if the Runtime moves). Installed at
//   `RuntimeBuilder::build`, cleared via a guard field on Runtime.
//   Used by `dispose_terminal::on_owning_executor` to decide whether
//   a TaskRef::Drop is on the executor thread (defer) or a foreign
//   thread (queue). Scope is the Runtime's full lifetime because
//   TaskRef::Drop can fire post-`block_on` (e.g., JoinHandle dropped
//   between block_on calls, channel slots torn down during Runtime
//   drop) and during `Executor::drop` itself.

thread_local! {
    static CTX_CROSS_WAKE: Cell<*const Arc<CrossWakeContext>> =
        const { Cell::new(std::ptr::null()) };

    static CURRENT_RUNTIME_CTX: Cell<*const CrossWakeContext> =
        const { Cell::new(std::ptr::null()) };
}

/// Install the cross-wake context in TLS. Returns a guard that clears
/// it on drop.
pub(crate) fn install_cross_wake(ctx: &Arc<CrossWakeContext>) -> CrossWakeGuard {
    let prev = CTX_CROSS_WAKE.with(|c| c.replace(std::ptr::from_ref(ctx)));
    CrossWakeGuard { prev }
}

pub(crate) struct CrossWakeGuard {
    prev: *const Arc<CrossWakeContext>,
}

impl Drop for CrossWakeGuard {
    fn drop(&mut self) {
        CTX_CROSS_WAKE.with(|c| c.set(self.prev));
    }
}

/// Get the current runtime's cross-wake context. Returns None if
/// called outside `block_on`.
pub(crate) fn cross_wake_context() -> Option<Arc<CrossWakeContext>> {
    CTX_CROSS_WAKE.with(|c| {
        let ptr = c.get();
        if ptr.is_null() {
            None
        } else {
            // SAFETY: ptr was set by install_cross_wake and is valid
            // for the duration of block_on.
            Some(unsafe { (*ptr).clone() })
        }
    })
}

// =============================================================================
// Runtime-lifetime TLS install for `dispose_terminal`
// =============================================================================

/// Install the Runtime's cross-wake context as the current-thread
/// "owning executor" identity. Returns a guard that restores the
/// previous value on drop.
///
/// Stores `Arc::as_ptr(arc)` — the inner allocation address, stable
/// for the lifetime of the Arc. Doesn't dangle if the Runtime struct
/// moves (the inner stays put).
pub(crate) fn install_runtime_cross_wake(arc: &Arc<CrossWakeContext>) -> RuntimeCrossWakeGuard {
    let ptr = Arc::as_ptr(arc);
    let prev = CURRENT_RUNTIME_CTX.with(|c| c.replace(ptr));
    RuntimeCrossWakeGuard { prev }
}

/// RAII guard restoring the previous `CURRENT_RUNTIME_CTX` on drop.
///
/// Lives as a field on `Runtime`, placed after `executor` so it drops
/// after the executor finishes its task-freeing work (which may invoke
/// `dispose_terminal`).
pub(crate) struct RuntimeCrossWakeGuard {
    prev: *const CrossWakeContext,
}

impl Drop for RuntimeCrossWakeGuard {
    fn drop(&mut self) {
        CURRENT_RUNTIME_CTX.with(|c| c.set(self.prev));
    }
}

/// Read the currently-installed runtime cross-wake context pointer for
/// this thread, if any. Returns null when no Runtime is alive on the
/// thread.
///
/// Used by spawn paths (`Executor::spawn_boxed`, `alloc::slab_spawn`,
/// `SlabClaim::spawn`) to write the value into each new task's header.
#[inline]
pub(crate) fn current_runtime_ctx() -> *const CrossWakeContext {
    CURRENT_RUNTIME_CTX.with(Cell::get)
}

/// True if `ctx` matches the runtime currently installed on this thread.
///
/// False when no Runtime is alive here, or when a different runtime's
/// ctx is installed (which can't actually happen given
/// `RuntimePresenceGuard` — at most one Runtime per thread).
#[inline]
fn on_owning_executor(ctx: &CrossWakeContext) -> bool {
    let installed = CURRENT_RUNTIME_CTX.with(Cell::get);
    !installed.is_null() && std::ptr::eq(installed, ctx)
}

// =============================================================================
// dispose_terminal — unified terminal-drop routing
// =============================================================================

/// Dispose of a task whose final ref was just dropped (FreeBox / FreeSlab).
///
/// Routes to one of two on-thread paths and one off-thread path,
/// chosen by `task_ptr`'s header context and the current thread:
///
/// 1. **On-thread (null ctx OR ctx matches the current Runtime's TLS).**
///    Defer to end of the current poll cycle via
///    `crate::waker::try_defer_free` so `Executor::all_tasks`
///    bookkeeping stays consistent (the executor's drain frees the
///    task and removes the slab key in the right order). If the
///    `DEFERRED_FREE` TLS is null (called outside any poll cycle —
///    e.g., `JoinHandle` dropped after `block_on` returns, or a bare
///    `Executor` test where the handle outlives the poll), the slot
///    leaks until `Executor::drop` iterates `all_tasks` and reclaims
///    it. **Direct-freeing here is unsafe** because it would race
///    `Executor::drop`'s `all_tasks` iteration → double free. This is
///    the established pre-refactor behavior of `free_completed_slot`.
///
/// 2. **Off-thread (ctx non-null, doesn't match TLS).** Push to the
///    Runtime's cross-thread queue via `try_set_queued + push +
///    parked check`. The Runtime's `drain_cross_thread` recognizes
///    terminal entries and pushes them to `deferred_free`, which
///    updates `all_tasks` on the next poll cycle.
///
/// This is the ONE place that does terminal-drop routing for off-thread
/// holders. All other code (`TaskRef::Drop`, channel slot release
/// paths, `tokio_compat` terminal branches) goes through here.
///
/// # Safety
///
/// `task_ptr` must reference a task whose final ref was just dropped
/// (i.e., `ref_dec` returned `FreeBox` or `FreeSlab`). The header's
/// `cross_wake_ctx` must be either null or a valid Arc-backed pointer
/// (set at spawn time, kept alive transitively by any holder of a
/// TaskRef on this task).
pub(crate) unsafe fn dispose_terminal(task_ptr: *mut u8) {
    // SAFETY: caller guarantees task_ptr is a valid task; header_cross_wake_ctx reads the fixed-offset header field.
    let ctx_ptr = unsafe { task::header_cross_wake_ctx(task_ptr) };

    // Null ctx (bare Executor or test-only Task::new_boxed): same
    // defer-or-leak fallback as the on-owning-executor branch. Direct
    // free is unsafe — see doc-comment.
    let on_executor = ctx_ptr.is_null() || {
        // SAFETY: ctx_ptr is Arc-backed and kept alive transitively
        // by whoever held the ref we just dropped.
        let ctx = unsafe { &*ctx_ptr };
        on_owning_executor(ctx)
    };

    if on_executor {
        // SAFETY: caller guarantees terminal state.
        let _ = unsafe { crate::waker::try_defer_free(task_ptr) };
        return;
    }

    // Off-thread: route via cross-queue. The executor's
    // drain_cross_thread recognizes terminal entries and pushes them
    // to deferred_free, which updates all_tasks on the next poll cycle.
    //
    // SAFETY: ctx_ptr non-null (bypassed the on_executor branch via
    // the && short-circuit above), Arc-backed and alive. try_set_queued
    // is an atomic on the task header (still alive — we own no ref but
    // the task header isn't freed because no one else has freed it
    // yet, and dispose_terminal is the path that would). queue.push
    // uses the cross_next field and is thread-safe.
    let ctx = unsafe { &*ctx_ptr };
    // SAFETY: task_ptr is alive and non-null; try_set_queued is an atomic CAS on the task header.
    if unsafe { task::try_set_queued(task_ptr) } {
        // SAFETY: task_ptr is valid and not already queued; try_set_queued succeeded above.
        unsafe { ctx.queue.push(task_ptr) };
        if ctx.parked.load(Ordering::Acquire) {
            let _ = ctx.mio_waker.wake();
        }
    }
}

// =============================================================================
// Intrusive MPSC queue (Vyukov)
// =============================================================================

/// Lock-free MPSC queue for cross-thread task wake notifications.
///
/// Producers (any thread) push task pointers via atomic swap on the tail.
/// The single consumer (runtime thread) drains via the head.
///
/// Each task's `cross_next` field (offset 32 in the header) serves as
/// the intrusive link pointer. No heap allocation per push.
///
/// Uses a stub node to avoid the empty-queue edge case. The stub is
/// just an `AtomicPtr` — not a real task.
pub(crate) struct CrossWakeQueue {
    /// Consumer reads from here. Only touched by the runtime thread.
    /// Wrapped in UnsafeCell so pop() can take &self (interior mutability).
    head: UnsafeCell<*mut u8>,
    /// Producers CAS here. Shared across threads.
    tail: AtomicPtr<u8>,
    /// Heap-allocated stub node. Stable address across moves.
    /// The stub is just an `AtomicPtr<u8>` (the "next" pointer).
    stub: *mut AtomicPtr<u8>,
}

// SAFETY: The queue is designed for cross-thread use.
// Producers push from any thread (atomic tail swap).
// Consumer pops from one thread (head is non-atomic).
unsafe impl Send for CrossWakeQueue {}
// SAFETY: CrossWakeQueue is designed for cross-thread use; producers use atomic ops, consumer owns head exclusively.
unsafe impl Sync for CrossWakeQueue {}

impl CrossWakeQueue {
    /// Create a new empty queue.
    pub(crate) fn new() -> Self {
        // Heap-allocate the stub so its address is stable after moves.
        let stub = Box::into_raw(Box::new(AtomicPtr::new(std::ptr::null_mut())));
        let stub_as_node = stub.cast::<u8>();
        Self {
            head: UnsafeCell::new(stub_as_node),
            tail: AtomicPtr::new(stub_as_node),
            stub,
        }
    }

    /// The stub's "task pointer" — the heap-allocated AtomicPtr.
    #[inline]
    fn stub_ptr(&self) -> *mut u8 {
        self.stub.cast::<u8>()
    }

    /// Get the `cross_next` pointer for a node. For real tasks this is
    /// the AtomicPtr at offset 32. For the stub it IS the stub allocation.
    #[inline]
    unsafe fn next_of(&self, node: *mut u8) -> &AtomicPtr<u8> {
        if node == self.stub_ptr() {
            // SAFETY: stub is a valid heap-allocated AtomicPtr.
            unsafe { &*self.stub }
        } else {
            // SAFETY: caller guarantees `node` is a valid task pointer.
            // cross_next returns a raw pointer; we dereference explicitly.
            unsafe { &*task::cross_next(node) }
        }
    }
}

impl Drop for CrossWakeQueue {
    fn drop(&mut self) {
        // SAFETY: stub was allocated via Box::into_raw in new().
        unsafe { drop(Box::from_raw(self.stub)) };
    }
}

impl CrossWakeQueue {
    /// Push a task pointer into the queue. Thread-safe (any thread).
    ///
    /// # Safety
    ///
    /// `task_ptr` must point to a live task with a valid `cross_next` field,
    /// OR must be the stub pointer (internal re-insertion).
    /// The task must not already be in this queue.
    pub(crate) unsafe fn push(&self, task_ptr: *mut u8) {
        // Clear next pointer on the node we're pushing.
        // SAFETY: task_ptr is either a valid task or the stub.
        unsafe { self.next_of(task_ptr) }.store(std::ptr::null_mut(), Ordering::Relaxed);

        // Atomically swap ourselves into the tail position.
        let prev = self.tail.swap(task_ptr, Ordering::AcqRel);

        // Link the previous tail to us. The consumer will see this
        // once the Release from our swap is visible.
        // SAFETY: prev is either the stub or a previously pushed task.
        unsafe { self.next_of(prev) }.store(task_ptr, Ordering::Release);
    }

    /// Pop a task pointer from the queue. Single-consumer only.
    ///
    /// Takes `&self` using interior mutability for `head` (UnsafeCell).
    /// The single-consumer guarantee ensures no concurrent access to `head`.
    ///
    /// Returns `None` if the queue is empty (or a producer hasn't
    /// finished linking yet — transient inconsistency).
    pub(crate) fn pop(&self) -> Option<*mut u8> {
        // SAFETY: single-consumer guarantee — only the runtime thread
        // calls pop(), never concurrently.
        let head_ref = unsafe { &mut *self.head.get() };
        let mut head = *head_ref;
        // SAFETY: head is either the stub or a previously pushed task.
        let mut next = unsafe { self.next_of(head) }.load(Ordering::Acquire);

        let stub = self.stub_ptr();

        // Skip the stub node.
        if head == stub {
            if next.is_null() {
                return None; // Queue is empty.
            }
            *head_ref = next;
            head = next;
            // SAFETY: head was advanced to next, which is a valid task or stub pointer from the queue.
            next = unsafe { self.next_of(head) }.load(Ordering::Acquire);
        }

        // Normal case: head has a next -> pop head, advance.
        if !next.is_null() {
            *head_ref = next;
            return Some(head);
        }

        // head is the last node. Check if tail == head.
        let tail = self.tail.load(Ordering::Acquire);
        if head != tail {
            // A producer swapped tail but hasn't linked next yet.
            // Transient inconsistency — return None, retry later.
            return None;
        }

        // Re-insert stub so we don't lose the tail reference.
        // SAFETY: stub is always valid.
        unsafe { self.push(stub) };

        // Now check if head got a next pointer (the stub push linked it).
        // SAFETY: head is a valid task or stub pointer that was in the queue before the stub re-insertion.
        next = unsafe { self.next_of(head) }.load(Ordering::Acquire);
        if !next.is_null() {
            *head_ref = next;
            return Some(head);
        }

        None
    }
}

// =============================================================================
// Cross-thread waker data
// =============================================================================

/// Shared context for all cross-thread wakers in a runtime instance.
/// Created once per runtime, `Arc`-shared across all cross-thread wakers.
pub(crate) struct CrossWakeContext {
    /// The intrusive MPSC queue for cross-thread wake pushes.
    pub(crate) queue: CrossWakeQueue,
    /// The mio waker to interrupt epoll after pushing.
    pub(crate) mio_waker: Arc<mio::Waker>,
    /// Whether the runtime is currently parked in epoll_wait.
    /// Cross-thread senders read this to decide whether to poke
    /// the eventfd — skip the syscall when the runtime is actively
    /// polling (it will drain the inbox on the next iteration).
    pub(crate) parked: std::sync::atomic::AtomicBool,
}

// SAFETY: CrossWakeQueue is Send + Sync, Arc<mio::Waker> is Send + Sync.
unsafe impl Send for CrossWakeContext {}
// SAFETY: CrossWakeContext fields are Send + Sync; queue uses atomic tail, mio::Waker is thread-safe.
unsafe impl Sync for CrossWakeContext {}

/// Wake a task via the cross-thread path: push to intrusive inbox,
/// conditionally poke eventfd. Zero allocation.
///
/// # Safety
///
/// `task_ptr` must point to a live task. `ctx` must be a valid
/// `CrossWakeContext` (guaranteed by channel lifetime).
pub(crate) unsafe fn wake_task_cross_thread(task_ptr: *mut u8, ctx: &CrossWakeContext) {
    // Don't wake completed tasks.
    // SAFETY: caller guarantees task_ptr is a valid live task; is_completed reads an atomic flag.
    if unsafe { task::is_completed(task_ptr) } {
        return;
    }

    // Dedup: atomic CAS on is_queued for thread safety.
    // SAFETY: task_ptr is a valid task.
    if !unsafe { task::try_set_queued(task_ptr) } {
        return;
    }

    // SAFETY: task_ptr valid, not already queued.
    unsafe { ctx.queue.push(task_ptr) };

    if ctx.parked.load(Ordering::Acquire) {
        let _ = ctx.mio_waker.wake();
    }
}

// =============================================================================
// Shared waker slots — used by all channel modules
// =============================================================================
//
// `TaskWakerSlot`: cross-thread receiver waker slot. Holds one refcount
// unit on the registered task (TaskRef-equivalent semantics — the slot's
// `task_ptr` field semantically owns one ref). Used by the receiver side
// of every channel (`mpsc`, `spsc`, `mpsc_bytes`, `spsc_bytes`).
//
// `FallbackWaker`: storage for non-runtime wakers (root future, foreign
// wakers). Used when `TaskWakerSlot::try_register_local` returns false.
//
// Pre-PR-1b these were duplicated across the four channel modules. PR
// 1b consolidates to one definition each, shared via `pub(crate)` from
// this module.
//
// **CRITICAL invariants** (any future change to these types must
// preserve them — see PR 1a + PR 1b plans for context):
//
// 1. `TaskWakerSlot::register` ALWAYS releases `prev_ptr` when non-null,
//    regardless of `state` value. A sender's `wake()` CAS may have
//    transitioned state STORED→EMPTY without yet taking `task_ptr` (the
//    swap is the second step). In that race window `prev_ptr` is
//    non-null even though state was EMPTY when register observed it.
//    Skipping the release leaks the ref. (BUG-2 follow-up — found by
//    John in PR 1a review. The
//    `register_during_wake_does_not_leak_ref` test orchestrates exactly
//    this race.)
//
// 2. `TaskWakerSlot::wake` dispatches BEFORE releasing the ref:
//    (a) CAS state STORED→EMPTY,
//    (b) swap `task_ptr` to null (slot transfers ownership to caller),
//    (c) call `wake_task_cross_thread` — uses the ref but doesn't
//        consume it,
//    (d) drop the TaskRef (via `from_owned`).
//    Steps (c) and (d) MUST stay in this order. `wake_task_cross_thread`
//    derefs `task_ptr` (`is_completed`); releasing first risks the deref
//    hitting freed memory if our release was the terminal ref.

/// Shared wakeslot state values. Private to this module — both
/// `TaskWakerSlot` and `FallbackWaker` (defined below) use them.
const EMPTY: u8 = 0;
const STORED: u8 = 1;
const REGISTERING: u8 = 2;

/// Cross-thread receiver waker slot. Zero-alloc, lives in each channel's
/// `Inner`, pointed to by `RawWaker::data`.
///
/// Holds one refcount unit on the registered task. Senders observe
/// `task_ptr` and atomically swap it during `wake()`; the receiver
/// registers/clears it during `RecvFut::poll`/`RecvFut::Drop`.
pub(crate) struct TaskWakerSlot {
    /// Task pointer to wake. Written by receiver, read by senders.
    task_ptr: AtomicPtr<u8>,
    /// Raw pointer to the `CrossWakeContext`. Set once at channel
    /// creation. Used by `wake()` to enqueue the cross-thread wake.
    /// NOT used for terminal-drop routing — the dropped TaskRef reads
    /// ctx from the task header instead.
    cross_ctx: *const CrossWakeContext,
    /// State: EMPTY / STORED / REGISTERING. Coordinates concurrent
    /// register/wake/clear access.
    state: std::sync::atomic::AtomicU8,
}

// SAFETY: All fields are atomic or immutable after creation.
unsafe impl Send for TaskWakerSlot {}
// SAFETY: TaskWakerSlot fields are atomic or immutable after creation; UnsafeCell access is guarded by state.
unsafe impl Sync for TaskWakerSlot {}

impl TaskWakerSlot {
    pub(crate) fn new(cross_ctx: *const CrossWakeContext) -> Self {
        Self {
            task_ptr: AtomicPtr::new(std::ptr::null_mut()),
            cross_ctx,
            state: std::sync::atomic::AtomicU8::new(EMPTY),
        }
    }

    /// Register the receiver's task pointer. Called by `RecvFut::poll`.
    /// Single-registerer only.
    pub(crate) fn register(&self, task_ptr: *mut u8) {
        debug_assert!(
            !task_ptr.is_null(),
            "TaskWakerSlot::register called with null task_ptr — \
             contract violation by caller (typically RecvFut::poll)"
        );
        let prev = self.state.swap(REGISTERING, Ordering::Acquire);
        debug_assert_ne!(prev, REGISTERING, "concurrent register on TaskWakerSlot");

        // BUG-2 (#168) fix: hold a refcount on the task while registered
        // so a sender that captures the pointer mid-`wake()` can't have
        // it freed underneath. The matching `ref_dec` happens in `wake`
        // (after `wake_task_cross_thread` returns), `clear`, or `Drop`.
        // SAFETY: caller (RecvFut::poll) just received task_ptr from the
        // active receiver task whose refcount is >= 1; the debug_assert
        // above catches the null case in development.
        let task_ref = unsafe { crate::task::TaskRef::acquire(task_ptr) };
        let ptr = task_ref.as_ptr();
        std::mem::forget(task_ref); // slot's AtomicPtr now owns the ref

        // Release any prior registration's ref. Always check prev_ptr —
        // not gated on `prev == STORED` — because a sender's `wake()`
        // CAS may have transitioned state STORED→EMPTY without yet
        // taking the task_ptr (the swap is the second step). In that
        // race window, prev_ptr is still non-null even though state was
        // EMPTY when we observed it. Skipping the release leaks the
        // ref. (BUG-2 follow-up — found by John in PR review.)
        //
        // SAFETY: prev_ptr (if non-null) was registered with a ref_inc;
        // we own that ref now and must release it via TaskRef::Drop →
        // dispose_terminal. wake/clear/Drop operate on the new pointer
        // we just stored — both refs are tracked correctly in all
        // interleavings.
        let prev_ptr = self.task_ptr.swap(ptr, Ordering::AcqRel);
        if !prev_ptr.is_null() {
            // SAFETY: prev_ptr (non-null) was registered with a ref_inc; we own that ref and must release it.
            drop(unsafe { crate::task::TaskRef::from_owned(prev_ptr) });
        }

        self.state.store(STORED, Ordering::Release);
    }

    /// Try to register a local runtime waker. Returns true if the waker
    /// is a local-runtime waker and was registered via the zero-alloc
    /// slot. Returns false for foreign wakers (caller should fall back
    /// to the `FallbackWaker` slot on Inner).
    pub(crate) fn try_register_local(&self, waker: &std::task::Waker) -> bool {
        crate::waker::task_ptr_from_local_waker(waker).is_some_and(|task_ptr| {
            self.register(task_ptr);
            true
        })
    }

    /// Wake the receiver if registered. Called by senders from any
    /// thread. Returns true if a wake was actually delivered.
    ///
    /// PRESERVES dispatch-before-release ordering — see CRITICAL
    /// invariant 2 at the top of this section.
    pub(crate) fn wake(&self) -> bool {
        if self
            .state
            .compare_exchange(STORED, EMPTY, Ordering::AcqRel, Ordering::Relaxed)
            .is_ok()
        {
            let task_ptr = self.task_ptr.swap(std::ptr::null_mut(), Ordering::Acquire);
            if !task_ptr.is_null() {
                // Push to cross-thread inbox + conditional eventfd poke.
                // SAFETY: cross_ctx is valid for the lifetime of the
                // channel. task_ptr is alive because `register`
                // ref_inc'd before storing — that ref keeps the task
                // allocated through the dispatch (see BUG-2 #168).
                let ctx = unsafe { &*self.cross_ctx };
                // SAFETY: task_ptr is alive (kept by register's ref_inc) and ctx is valid for the channel lifetime.
                unsafe { wake_task_cross_thread(task_ptr, ctx) };

                // BUG-2 fix: release the ref `register` acquired. Must
                // happen AFTER `wake_task_cross_thread` returns so the
                // task is alive for the deref inside it.
                // SAFETY: we own the ref from `register`.
                drop(unsafe { crate::task::TaskRef::from_owned(task_ptr) });
                return true;
            }
        }
        false
    }

    pub(crate) fn has_waker(&self) -> bool {
        self.state.load(Ordering::Acquire) == STORED
    }

    /// Clear the stored waker if one exists. Used by `RecvFut::Drop` to
    /// prevent use-after-free when the recv task completes while a
    /// sender on another thread may try to wake through the stale ptr.
    pub(crate) fn clear(&self) {
        if self
            .state
            .compare_exchange(STORED, EMPTY, Ordering::AcqRel, Ordering::Relaxed)
            .is_ok()
        {
            let task_ptr = self.task_ptr.swap(std::ptr::null_mut(), Ordering::Acquire);
            if !task_ptr.is_null() {
                // BUG-2 fix: release the ref `register` acquired.
                // SAFETY: we own the ref from `register`.
                drop(unsafe { crate::task::TaskRef::from_owned(task_ptr) });
            }
        }
    }
}

impl Drop for TaskWakerSlot {
    fn drop(&mut self) {
        // BUG-2 (#168) fix: if still registered when dropped, release
        // our ref. Slot drops when channel `Inner` drops — both sides
        // of the channel are gone, so any registered receiver task can
        // no longer be woken via this slot. Releasing the ref here
        // matches the wake/clear release paths.
        //
        // &mut self gives exclusive access; no concurrent mutator.
        if *self.state.get_mut() == STORED {
            let task_ptr = *self.task_ptr.get_mut();
            if !task_ptr.is_null() {
                // SAFETY: we own the ref from `register`.
                drop(unsafe { crate::task::TaskRef::from_owned(task_ptr) });
            }
        }
    }
}

/// Fallback waker storage for non-runtime wakers (root future, foreign).
/// Used when `TaskWakerSlot::try_register_local` returns false.
pub(crate) struct FallbackWaker {
    state: std::sync::atomic::AtomicU8,
    waker: UnsafeCell<Option<std::task::Waker>>,
}

// SAFETY: Access to the UnsafeCell<Option<Waker>> is coordinated by
// the atomic state field (REGISTERING excludes concurrent writes,
// CAS STORED→EMPTY excludes concurrent reads).
unsafe impl Send for FallbackWaker {}
// SAFETY: FallbackWaker UnsafeCell access is coordinated by the atomic state field.
unsafe impl Sync for FallbackWaker {}

impl FallbackWaker {
    pub(crate) fn new() -> Self {
        Self {
            state: std::sync::atomic::AtomicU8::new(EMPTY),
            waker: UnsafeCell::new(None),
        }
    }

    pub(crate) fn register(&self, waker: &std::task::Waker) {
        let prev = self.state.swap(REGISTERING, Ordering::Acquire);
        debug_assert_ne!(prev, REGISTERING);
        // SAFETY: REGISTERING state excludes concurrent access to the
        // UnsafeCell. Only one thread can pass the swap-to-REGISTERING
        // gate (single-registerer contract), and wake() CAS only succeeds
        // from STORED, not REGISTERING.
        unsafe { *self.waker.get() = Some(waker.clone()) };
        self.state.store(STORED, Ordering::Release);
    }

    pub(crate) fn wake(&self) -> bool {
        if self
            .state
            .compare_exchange(STORED, EMPTY, Ordering::AcqRel, Ordering::Relaxed)
            .is_ok()
        {
            // SAFETY: CAS STORED→EMPTY succeeded, giving us exclusive
            // access to the UnsafeCell. No other thread can CAS from
            // STORED (it's now EMPTY), and register swaps to REGISTERING
            // first.
            let waker = unsafe { (*self.waker.get()).take() };
            if let Some(w) = waker {
                w.wake();
                return true;
            }
        }
        false
    }

    pub(crate) fn has_waker(&self) -> bool {
        self.state.load(Ordering::Acquire) == STORED
    }
}

impl Drop for FallbackWaker {
    fn drop(&mut self) {
        *self.waker.get_mut() = None;
    }
}

/// Sender waker slot — single-sender, single-receiver, no intrusive list
/// needed. Used by SPSC channels (typed and bytes) for the sender side
/// of the wake handshake. Same EMPTY/STORED/REGISTERING coordination
/// as `TaskWakerSlot` and `FallbackWaker`.
///
/// Single-registerer (the lone sender), single-waker (the lone
/// receiver) — coordination is simpler than `TaskWakerSlot` which
/// fields multi-thread access on the wake side.
pub(crate) struct TxWakerSlot {
    state: std::sync::atomic::AtomicU8,
    waker: UnsafeCell<Option<std::task::Waker>>,
}

// SAFETY: Access to the UnsafeCell<Option<Waker>> is coordinated by
// the atomic state field. Single-sender register, single-receiver wake.
unsafe impl Send for TxWakerSlot {}
// SAFETY: TxWakerSlot UnsafeCell access is coordinated by the atomic state; single-sender, single-receiver.
unsafe impl Sync for TxWakerSlot {}

impl TxWakerSlot {
    pub(crate) fn new() -> Self {
        Self {
            state: std::sync::atomic::AtomicU8::new(EMPTY),
            waker: UnsafeCell::new(None),
        }
    }

    /// Register. Called by the single sender — no concurrent register.
    pub(crate) fn register(&self, waker: &std::task::Waker) {
        let prev = self.state.swap(REGISTERING, Ordering::Acquire);
        debug_assert_ne!(prev, REGISTERING);
        // SAFETY: REGISTERING state excludes concurrent access to the
        // UnsafeCell. Single-sender contract means no concurrent register,
        // and wake() CAS only succeeds from STORED, not REGISTERING.
        unsafe { *self.waker.get() = Some(waker.clone()) };
        self.state.store(STORED, Ordering::Release);
    }

    /// Wake. Called by receiver (single thread).
    pub(crate) fn wake(&self) -> bool {
        if self
            .state
            .compare_exchange(STORED, EMPTY, Ordering::AcqRel, Ordering::Relaxed)
            .is_ok()
        {
            // SAFETY: CAS STORED→EMPTY succeeded, giving exclusive access
            // to the UnsafeCell. No concurrent register (state is EMPTY,
            // not STORED or REGISTERING) and no concurrent wake (single
            // receiver thread).
            if let Some(w) = unsafe { (*self.waker.get()).take() } {
                w.wake();
                return true;
            }
        }
        false
    }

    pub(crate) fn has_waker(&self) -> bool {
        self.state.load(Ordering::Acquire) == STORED
    }
}

impl Drop for TxWakerSlot {
    fn drop(&mut self) {
        *self.waker.get_mut() = None;
    }
}

// =============================================================================
// Cross-thread waker test scenarios — shared by all four channels' uaf_tests
// =============================================================================
//
// Pre-PR-1b: the 3 scenarios below were duplicated 4x (once per channel)
// with channel-specific `RxWakerSlot` types. After consolidation to the
// shared `TaskWakerSlot`, the bodies become identical — they all call
// the same `TaskWakerSlot` API. This module owns the canonical bodies;
// each channel's `mod uaf_tests` becomes 3 thin `#[test] fn` wrappers
// calling these scenarios.
//
// Why in-crate (`#[cfg(test)] pub(crate) mod`) instead of an integration
// test in `tests/cross_thread_harness.rs` (per PR 1b plan): the
// scenarios poke `TaskWakerSlot` internal fields (`state`,
// `task_ptr`) and call private helpers. Integration tests can only see
// `pub` items, which would force unacceptable test-only public API
// surface on `TaskWakerSlot`. The plan acknowledged this alternative
// ("a shared `#[cfg(test)] mod` inside `cross_wake.rs`") — taking it
// for the surface-leak reason.
#[cfg(test)]
pub(crate) mod uaf_scenarios {
    use super::*;
    use crate::task::{self, FreeAction, Task, TaskRef};
    use std::future::Future;
    use std::pin::Pin;
    use std::sync::atomic::AtomicBool;
    use std::task::{Context, Poll};

    struct UafNoop;
    impl Future for UafNoop {
        type Output = ();
        fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<()> {
            Poll::Ready(())
        }
    }

    fn make_uaf_task() -> *mut u8 {
        // Refcount = 1 (single executor-style ref) per Task::new_boxed.
        let task = Box::new(Task::new_boxed(UafNoop, 0));
        Box::into_raw(task) as *mut u8
    }

    fn make_uaf_cross_ctx() -> Arc<CrossWakeContext> {
        let poll = mio::Poll::new().unwrap();
        let mio_waker = Arc::new(mio::Waker::new(poll.registry(), mio::Token(usize::MAX)).unwrap());
        Arc::new(CrossWakeContext {
            queue: CrossWakeQueue::new(),
            mio_waker,
            parked: AtomicBool::new(false),
        })
    }

    /// Reproduces BUG-2: sender derefs the task pointer after the
    /// receiver task has been freed.
    ///
    /// Pre-fix: the call to `wake_task_cross_thread(captured, ...)`
    /// reads task state from freed memory. Tree-borrows miri flags
    /// this. The exact failure surface depends on which read miri
    /// trips on first (`is_completed` is the first deref).
    ///
    /// Post-fix: `register` ref_incs (refcount goes 1→2), so
    /// `complete_and_unref` returns `Retain` instead of `FreeBox`. The
    /// task allocation is alive when the sender derefs it; the deref
    /// reads `COMPLETED` and the function returns early. The slot's
    /// `Drop` then releases the final ref, freeing the task cleanly.
    pub(crate) fn waker_slot_uaf_when_task_freed_mid_dispatch() {
        let cross_ctx = make_uaf_cross_ctx();
        let task_ptr = make_uaf_task();

        // Sanity: starting refcount is 1 (Task::new_boxed initial state).
        assert_eq!(
            // SAFETY: task_ptr was just created by make_uaf_task; valid task.
            unsafe { task::ref_count(task_ptr) },
            1,
            "make_uaf_task should produce refcount=1"
        );

        // Construct the slot pointing at the cross-wake context, then
        // register the task pointer — this is the operation under test.
        let slot = TaskWakerSlot::new(Arc::as_ptr(&cross_ctx));
        slot.register(task_ptr);

        // Mirror the sender's first half of `slot.wake()`: CAS state
        // STORED→EMPTY, swap the pointer out. After this, the sender
        // owns the captured pointer and is about to call
        // `wake_task_cross_thread`.
        assert!(
            slot.state
                .compare_exchange(STORED, EMPTY, Ordering::AcqRel, Ordering::Relaxed)
                .is_ok(),
            "slot was registered; CAS STORED→EMPTY must succeed"
        );
        let captured = slot.task_ptr.swap(std::ptr::null_mut(), Ordering::Acquire);
        assert_eq!(captured, task_ptr);

        // Simulate "select resolved on the other arm during the
        // dispatch window": the executor calls `complete_and_unref` on
        // the task, which atomically sets COMPLETED and decrements the
        // executor's ref. Pre-fix this is the last ref → FreeBox.
        // Post-fix the slot still holds a ref → Retain.
        // SAFETY: task_ptr is a valid task created by make_uaf_task. The
        // executor-style ref (rc=1 or 2 depending on fix) is being
        // decremented as part of the simulated completion path.
        let action = unsafe { task::complete_and_unref(task_ptr) };

        // Track which path we're on — the test must clean up differently
        // pre-fix vs post-fix. Pre-fix: task is already freed below.
        // Post-fix: task is still alive (slot's ref); we must release it
        // ourselves at the end since the slot's `state` is EMPTY (we
        // CAS'd it above), so any future `Drop`-time release won't fire.
        let pre_fix = match action {
            FreeAction::FreeBox => {
                #[cfg(not(miri))]
                panic!(
                    "BUG-2 regression detected: register skipped ref_inc, \
                     so complete_and_unref produced FreeBox instead of \
                     Retain. Run under miri for the full UAF trace."
                );
                #[cfg(miri)]
                {
                    // SAFETY: FreeBox indicates rc=0 and task is terminal;
                    // free_task reclaims the Box allocation.
                    unsafe { task::free_task(task_ptr) };
                    true
                }
            }
            FreeAction::Retain => false,
            FreeAction::FreeSlab => {
                panic!("box-allocated test task must not produce FreeSlab");
            }
        };

        // Sender continues with the captured pointer.
        // PRE-FIX: derefs freed memory → tree-borrows UAF.
        // POST-FIX: derefs alive task, observes COMPLETED, returns early.
        // SAFETY: captured is a valid task pointer (post-fix: kept alive
        // by the slot's ref_inc; pre-fix: freed — UAF under miri).
        unsafe { wake_task_cross_thread(captured, &cross_ctx) };

        if !pre_fix {
            // POST-FIX cleanup: release the slot's captured ref via
            // TaskRef. In real code this is `wake()`'s drop after
            // wake_task_cross_thread returns.
            // SAFETY: captured is a valid task with rc >= 1 (the slot's
            // ref). from_owned reconstructs the TaskRef for the drop.
            drop(unsafe { TaskRef::from_owned(captured) });
            // captured was the only remaining ref; now freed. Don't
            // touch task_ptr again.
            drop(slot);
            return;
        }

        // PRE-FIX cleanup path (reachable only under miri).
        drop(slot);
    }

    /// Companion: a registered slot dropped without wake/clear must
    /// release its ref via Drop. Otherwise the task allocation leaks.
    ///
    /// **Sensitive to the fix via explicit refcount assertions.** Pre-fix
    /// this FAILS because no `Drop` impl exists on `TaskWakerSlot`,
    /// so `register` doesn't take a ref and Drop doesn't release one.
    /// PASSES post-fix because `register` ref_incs and Drop ref_decs.
    pub(crate) fn slot_drop_releases_ref_when_still_registered() {
        let cross_ctx = make_uaf_cross_ctx();
        let task_ptr = make_uaf_task();

        // Mark the task COMPLETED first via complete_and_unref. Bump the
        // ref to 2 so complete_and_unref returns Retain (rather than
        // freeing). After: refcount = 1, COMPLETED set.
        // SAFETY: task_ptr is a valid task from make_uaf_task with rc=1.
        // ref_inc brings rc to 2; complete_and_unref sets COMPLETED and
        // decrements rc back to 1, returning Retain.
        unsafe { task::ref_inc(task_ptr) };
        // SAFETY: task_ptr is valid with rc=2; complete_and_unref sets COMPLETED and decrements rc.
        let action = unsafe { task::complete_and_unref(task_ptr) };
        assert!(matches!(action, FreeAction::Retain));
        // SAFETY: task_ptr is still valid (Retain means no free).
        let baseline_refcount = unsafe { task::ref_count(task_ptr) };
        assert_eq!(baseline_refcount, 1, "after complete_and_unref, refcount=1");

        let slot = TaskWakerSlot::new(Arc::as_ptr(&cross_ctx));
        slot.register(task_ptr);
        // Post-fix: register ref_inc → refcount = 2.
        // Pre-fix: register did NOT ref_inc → refcount = 1.
        // SAFETY: task_ptr valid; reading refcount for assertion.
        let after_register = unsafe { task::ref_count(task_ptr) };

        // Drop the slot WITHOUT calling wake() or clear().
        // Post-fix: Drop sees state == STORED, ref_dec → refcount = 1, returns Retain.
        // Pre-fix: no Drop impl → refcount unchanged.
        drop(slot);
        // SAFETY: task_ptr valid (rc >= 1 in both pre/post-fix paths).
        let after_drop = unsafe { task::ref_count(task_ptr) };

        // The strengthened assertion: register-then-drop must net to
        // zero change in refcount. Pre-fix register doesn't take a ref AND
        // Drop doesn't release one, so this ALSO nets to zero — but the
        // explicit `register-took-a-ref` check below catches the regression.
        assert_eq!(
            after_register,
            after_drop + 1,
            "Post-fix Drop must release the ref that register acquired. \
             If this fires pre-fix (register skipped ref_inc), there's no \
             Drop ref_dec to compensate, so the net is 0 instead of -1."
        );
        assert_eq!(
            after_register,
            baseline_refcount + 1,
            "Post-fix register must bump refcount by 1. If this fires \
             pre-fix, register skipped ref_inc — that's BUG-2's root cause."
        );

        // Cleanup: refcount is 1 (post-fix or pre-fix), COMPLETED set.
        // Final ref_dec should return FreeBox; free the allocation.
        // SAFETY: task_ptr valid with rc=1, COMPLETED. ref_dec brings
        // rc to 0 → FreeBox. free_task reclaims the Box allocation.
        let action = unsafe { task::ref_dec(task_ptr) };
        match action {
            // SAFETY: FreeBox guarantees rc=0 and task is terminal; free_task reclaims the Box allocation.
            FreeAction::FreeBox => unsafe { task::free_task(task_ptr) },
            other => panic!("expected FreeBox on final ref_dec, got {other:?}"),
        }
    }

    /// Race regression for the BUG-2 follow-up.
    ///
    /// `register()` previously gated the prev-ref release on
    /// `prev == STORED && !prev_ptr.is_null()`. That gate was wrong:
    /// a sender's `wake()` first CAS's state STORED→EMPTY, THEN swaps
    /// `task_ptr`. If a re-register interleaves between those two
    /// steps it observes `prev == EMPTY` (CAS happened) but
    /// `prev_ptr` is still non-null (swap hasn't happened) — the gate
    /// skipped releasing the old ref, leaking it.
    ///
    /// The fix removes the `prev == STORED` part of the gate; we now
    /// always release a non-null prev_ptr.
    ///
    /// This test drives the interleave manually and asserts refcount
    /// returns to baseline. Pre-fix it lands at baseline+1 (leak).
    pub(crate) fn register_during_wake_does_not_leak_ref() {
        let cross_ctx = make_uaf_cross_ctx();
        let task_ptr = make_uaf_task();

        // Bump the ref so the test's manual ref_decs don't trigger
        // free mid-test. After complete_and_unref, refcount = 1 with
        // COMPLETED set — this is our baseline.
        // SAFETY: task_ptr valid from make_uaf_task (rc=1). ref_inc
        // brings rc to 2; complete_and_unref sets COMPLETED, rc → 1.
        unsafe { task::ref_inc(task_ptr) };
        // SAFETY: task_ptr is valid with rc=2; complete_and_unref sets COMPLETED and decrements rc.
        let action = unsafe { task::complete_and_unref(task_ptr) };
        assert!(matches!(action, FreeAction::Retain));
        // SAFETY: task_ptr valid (Retain, rc=1).
        let baseline = unsafe { task::ref_count(task_ptr) };
        assert_eq!(baseline, 1, "baseline must be 1 (executor-style ref)");

        let slot = TaskWakerSlot::new(Arc::as_ptr(&cross_ctx));

        // ---- T0: initial register ----
        slot.register(task_ptr);
        assert_eq!(
            // SAFETY: task_ptr valid; reading refcount for assertion.
            unsafe { task::ref_count(task_ptr) },
            baseline + 1,
            "initial register must take a ref (slot owns +1)"
        );

        // ---- T1 wake (first half): CAS only, do NOT swap task_ptr yet ----
        // Mirrors the entry of `wake()` paused mid-function. After
        // this, state is EMPTY but task_ptr still points at task_ptr.
        let cas_ok = slot
            .state
            .compare_exchange(STORED, EMPTY, Ordering::AcqRel, Ordering::Relaxed)
            .is_ok();
        assert!(cas_ok, "wake's CAS must succeed when state is STORED");

        // ---- T2: re-register (the race) ----
        // Mirrors RecvFut::poll re-registering after a wake from
        // another source (timer, parent select arm fired). Same task
        // — same task_ptr. Pre-fix: register's gate sees prev==EMPTY,
        // skips the release, leaks the old ref. Post-fix: release fires.
        slot.register(task_ptr);
        assert_eq!(
            // SAFETY: task_ptr valid; reading refcount for assertion.
            unsafe { task::ref_count(task_ptr) },
            baseline + 1,
            "race register must NET to baseline+1 (slot still owns one ref). \
             Pre-fix the gate skipped the release of the original; this \
             assertion would fire baseline+2 — the leak."
        );

        // ---- T1 wake (second half): swap task_ptr, release ----
        // Skip wake_task_cross_thread — we're testing refcount balance,
        // not the dispatch path. Drop the captured TaskRef (matches
        // wake's release-after-dispatch semantics).
        let captured = slot.task_ptr.swap(std::ptr::null_mut(), Ordering::Acquire);
        assert_eq!(captured, task_ptr);
        // SAFETY: captured is a valid task pointer with the ref that
        // register acquired. from_owned + drop releases that ref.
        drop(unsafe { TaskRef::from_owned(captured) });

        assert_eq!(
            // SAFETY: task_ptr valid; reading refcount for assertion.
            unsafe { task::ref_count(task_ptr) },
            baseline,
            "after wake's release, slot owes 0 refs to task. Pre-fix \
             this is baseline+1 (the leaked original)."
        );

        // ---- Cleanup ----
        // After the race, slot is in (state=STORED, task_ptr=null).
        // Drop sees state=STORED but task_ptr is null, so it releases
        // nothing — confirms the Drop impl correctly handles this
        // benign "post-race" inconsistency.
        drop(slot);
        assert_eq!(
            // SAFETY: task_ptr valid; reading refcount for assertion.
            unsafe { task::ref_count(task_ptr) },
            baseline,
            "Drop on a STORED-but-null-task_ptr slot must be a no-op for refcount"
        );

        // SAFETY: task_ptr valid with rc=baseline (1), COMPLETED.
        // ref_dec → rc=0 → FreeBox. free_task reclaims the allocation.
        match unsafe { task::ref_dec(task_ptr) } {
            // SAFETY: FreeBox guarantees rc=0 and task is terminal; free_task reclaims the allocation.
            FreeAction::FreeBox => unsafe { task::free_task(task_ptr) },
            other => panic!("expected FreeBox on final ref_dec, got {other:?}"),
        }
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::task::Task;
    use std::future::Future;
    use std::pin::Pin;
    use std::task::{Context, Poll};

    struct Noop;
    impl Future for Noop {
        type Output = ();
        fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<()> {
            Poll::Ready(())
        }
    }

    fn make_task() -> *mut u8 {
        let task = Box::new(Task::new_boxed(Noop, 0));
        Box::into_raw(task) as *mut u8
    }

    unsafe fn free(ptr: *mut u8) {
        // SAFETY: caller guarantees ptr is a valid task pointer from make_task; free_task reclaims the Box.
        unsafe { task::free_task(ptr) };
    }

    #[test]
    fn queue_push_pop_single() {
        let q = CrossWakeQueue::new();
        let t1 = make_task();

        // SAFETY: t1 is a valid task pointer from make_task with a
        // valid cross_next field. Not already in the queue.
        unsafe { q.push(t1) };
        assert_eq!(q.pop(), Some(t1));
        assert_eq!(q.pop(), None);

        // SAFETY: t1 was popped from the queue; free reclaims the Box.
        unsafe { free(t1) };
    }

    #[test]
    fn queue_push_pop_multiple() {
        let q = CrossWakeQueue::new();
        let t1 = make_task();
        let t2 = make_task();
        let t3 = make_task();

        // SAFETY: t1, t2, t3 are valid task pointers with valid
        // cross_next fields. Each pushed once, not already in queue.
        unsafe { q.push(t1) };
        // SAFETY: t2 is a valid task pointer, not already in queue.
        unsafe { q.push(t2) };
        // SAFETY: t3 is a valid task pointer, not already in queue.
        unsafe { q.push(t3) };

        assert_eq!(q.pop(), Some(t1));
        assert_eq!(q.pop(), Some(t2));
        assert_eq!(q.pop(), Some(t3));
        assert_eq!(q.pop(), None);

        // SAFETY: all popped from queue; free reclaims each Box.
        unsafe { free(t1) };
        // SAFETY: t2 was popped from queue; free reclaims the Box.
        unsafe { free(t2) };
        // SAFETY: t3 was popped from queue; free reclaims the Box.
        unsafe { free(t3) };
    }

    #[test]
    fn queue_interleaved_push_pop() {
        let q = CrossWakeQueue::new();
        let t1 = make_task();
        let t2 = make_task();

        // SAFETY: valid task pointers, not already in queue.
        unsafe { q.push(t1) };
        assert_eq!(q.pop(), Some(t1));

        // SAFETY: valid task pointer, not already in queue.
        unsafe { q.push(t2) };
        assert_eq!(q.pop(), Some(t2));
        assert_eq!(q.pop(), None);

        // SAFETY: both popped; free reclaims each Box.
        unsafe { free(t1) };
        // SAFETY: t2 was popped; free reclaims the Box.
        unsafe { free(t2) };
    }

    #[test]
    fn queue_empty() {
        let q = CrossWakeQueue::new();
        assert_eq!(q.pop(), None);
        assert_eq!(q.pop(), None);
    }

    #[test]
    fn queue_reuse_after_drain() {
        let q = CrossWakeQueue::new();
        let t1 = make_task();

        for _ in 0..100 {
            // SAFETY: t1 is a valid task, popped before each re-push
            // so it's never double-queued.
            unsafe { q.push(t1) };
            assert_eq!(q.pop(), Some(t1));
        }
        assert_eq!(q.pop(), None);

        // SAFETY: t1 was popped on the last iteration; free reclaims it.
        unsafe { free(t1) };
    }

    // =========================================================================
    // dispose_terminal — routing under different ctx + thread states
    // =========================================================================

    fn make_ctx() -> Arc<CrossWakeContext> {
        // Real mio Poll + Waker. mio 1.x exposes no public Waker
        // constructor that bypasses Poll (no `from_raw_fd`, no
        // `with_eventfd`), so a syscall-free test ctx would require
        // changing CrossWakeContext to hold `Option<Arc<mio::Waker>>`
        // — production-code churn whose only motivation is test
        // ergonomics. Keep the real mio construction here; the tests
        // never set `parked = true` so `mio_waker.wake()` is never
        // called.
        //
        // Tests pass under `-Zmiri-tree-borrows -Zmiri-ignore-leaks`
        // today. If a future miri tightens its epoll/eventfd shim and
        // breaks these tests, revisit by either (a) wrapping mio_waker
        // in an Option behind a trait abstraction, or (b) skipping
        // these tests under miri via #[cfg_attr(miri, ignore)].
        let poll = mio::Poll::new().expect("mio::Poll");
        let waker = mio::Waker::new(poll.registry(), mio::Token(0)).expect("mio::Waker");
        Arc::new(CrossWakeContext {
            queue: CrossWakeQueue::new(),
            mio_waker: Arc::new(waker),
            parked: std::sync::atomic::AtomicBool::new(false),
        })
    }

    /// Build a real spawn-shaped task (refcount=2, HAS_JOIN, ctx in
    /// header) so dispose_terminal sees a production-like header.
    fn make_spawned_task(ctx: &Arc<CrossWakeContext>) -> *mut u8 {
        struct Noop;
        impl std::future::Future for Noop {
            type Output = u64;
            fn poll(self: std::pin::Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<u64> {
                Poll::Ready(0)
            }
        }
        crate::task::box_spawn_joinable(Noop, 0, Arc::as_ptr(ctx))
    }

    /// Walk a freshly-spawned joinable task to terminal-eligible state:
    /// drop future, complete, clear HAS_JOIN, ref_dec the JoinHandle's
    /// ref. Final state: rc=0, COMPLETED, no lifecycle flags. Caller
    /// then invokes `dispose_terminal(ptr)` directly to exercise the
    /// routing — no re-acquire (would violate ref_inc's >=1 contract).
    unsafe fn drive_to_terminal(ptr: *mut u8) {
        // SAFETY: caller guarantees ptr is a freshly-spawned joinable
        // task (rc=2, HAS_JOIN set). Each step is valid given the
        // preceding state transitions documented inline.
        unsafe {
            crate::task::drop_task_future(ptr);
            assert!(matches!(
                crate::task::complete_and_unref(ptr),
                crate::task::FreeAction::Retain
            )); // 2 refs → 1 (HAS_JOIN still set, rc=1)
            crate::task::clear_has_join(ptr);
            assert!(matches!(
                crate::task::ref_dec(ptr),
                crate::task::FreeAction::FreeBox
            )); // rc 1 → 0, COMPLETED, no lifecycle → terminal
            assert!(crate::task::is_terminal(ptr));
        }
    }

    #[test]
    fn dispose_terminal_null_ctx_no_tls_leaks() {
        // Null ctx + no DEFERRED_FREE TLS → leak. dispose_terminal must
        // NOT free directly (would race Executor::drop's all_tasks scan
        // for tasks registered with a bare Executor).
        struct Noop;
        impl std::future::Future for Noop {
            type Output = ();
            fn poll(self: std::pin::Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<()> {
                Poll::Ready(())
            }
        }
        // Task::new_boxed: cross_wake_ctx is null, rc=1, no HAS_JOIN.
        let task = Box::new(crate::task::Task::new_boxed(Noop, 0));
        let ptr = Box::into_raw(task) as *mut u8;

        // SAFETY: ptr is a valid box-allocated task (rc=1, no HAS_JOIN).
        // drop_task_future drops the inner future. complete_and_unref
        // sets COMPLETED + rc → 0 → FreeBox (terminal). dispose_terminal
        // with null ctx + no TLS leaks intentionally. free_task reclaims.
        unsafe {
            // Walk to terminal: rc 1 → 0, COMPLETED, no lifecycle.
            crate::task::drop_task_future(ptr);
            assert!(matches!(
                crate::task::complete_and_unref(ptr),
                crate::task::FreeAction::FreeBox
            ));
            assert!(crate::task::is_terminal(ptr));

            // No TLS installed. dispose_terminal: null ctx → on_executor
            // branch → try_defer_free returns false (no DEFERRED_FREE
            // TLS) → leak. Task header stays valid for our final free.
            dispose_terminal(ptr);
            assert!(crate::task::is_terminal(ptr));
            crate::task::free_task(ptr);
        }
    }

    #[test]
    fn dispose_terminal_on_executor_defers_when_tls_set() {
        // ctx matches CURRENT_RUNTIME_CTX TLS + DEFERRED_FREE TLS set
        // → push to deferred_free list. Real-world case: JoinHandle
        // dropped during a poll cycle.
        let ctx = make_ctx();
        let _guard = install_runtime_cross_wake(&ctx);
        let ptr = make_spawned_task(&ctx);

        // Set up DEFERRED_FREE TLS pointing at a local Vec.
        let mut deferred: Vec<*mut u8> = Vec::new();
        let mut ready: Vec<*mut u8> = Vec::new();
        let _poll_guard = crate::waker::set_poll_context(&raw mut ready, &raw mut deferred);

        // SAFETY: ptr is a valid spawned task (rc=2, HAS_JOIN).
        // drive_to_terminal walks to terminal state. dispose_terminal
        // defers to the deferred_free Vec via TLS.
        unsafe {
            drive_to_terminal(ptr);
            dispose_terminal(ptr);
        }

        // Verify push to deferred_free.
        assert_eq!(deferred.len(), 1);
        assert_eq!(deferred[0], ptr);

        // SAFETY: ptr was deferred (not freed); free_task reclaims it.
        unsafe { crate::task::free_task(ptr) };
    }

    #[test]
    fn dispose_terminal_on_executor_leaks_when_tls_null() {
        // ctx matches TLS but DEFERRED_FREE TLS is null (e.g.,
        // JoinHandle dropped between block_on calls). dispose_terminal
        // leaves the task for Executor::drop to reclaim — we verify
        // "no double free" by freeing manually afterwards.
        let ctx = make_ctx();
        let _guard = install_runtime_cross_wake(&ctx);
        let ptr = make_spawned_task(&ctx);

        // SAFETY: ptr is a valid spawned task. drive_to_terminal walks
        // to terminal. dispose_terminal with matching TLS but null
        // DEFERRED_FREE leaks intentionally.
        unsafe {
            drive_to_terminal(ptr);
            // No poll context installed → DEFERRED_FREE TLS stays null.
            dispose_terminal(ptr);
        }

        // Task header still valid (we leaked, didn't free).
        // SAFETY: ptr was leaked, not freed; header is readable.
        assert!(unsafe { crate::task::is_terminal(ptr) });

        // SAFETY: ptr leaked above; free_task reclaims the Box.
        unsafe { crate::task::free_task(ptr) };
    }

    #[test]
    fn dispose_terminal_off_thread_queues() {
        // ctx non-null, but CURRENT_RUNTIME_CTX TLS NOT installed →
        // on_owning_executor returns false → off-thread branch →
        // push to ctx.queue + parked check.
        let ctx = make_ctx();
        let ptr = make_spawned_task(&ctx);

        // SAFETY: ptr is a valid spawned task. drive_to_terminal walks
        // to terminal. dispose_terminal with non-null ctx but no
        // matching TLS takes the off-thread path → cross-queue push.
        unsafe {
            drive_to_terminal(ptr);
            // No install_runtime_cross_wake → TLS null.
            dispose_terminal(ptr);
        }

        // Verify push to cross-queue.
        let popped = ctx.queue.pop();
        assert_eq!(popped, Some(ptr));
        // SAFETY: ptr was pushed to cross-queue, still valid.
        assert!(unsafe { crate::task::is_queued(ptr) });

        // SAFETY: ptr popped from queue; clear queued flag and free.
        unsafe {
            crate::task::clear_queued(ptr);
            crate::task::free_task(ptr);
        }
    }

    /// PR2-John-review item 1 regression test.
    ///
    /// Reproduces the race that caused a UAF in `Executor::drop` step
    /// 3:
    ///
    /// 1. A task with rc=1 is registered with the executor (in
    ///    `all_tasks`). State is COMPLETED — set up to mirror
    ///    "task ran to completion, off-thread waker holds the last
    ///    ref."
    /// 2. The off-thread waker drops terminal AFTER the runtime's
    ///    last `drain_cross_thread` call but BEFORE `Executor::drop`
    ///    starts: `dispose_terminal` does
    ///    `try_set_queued(T) + ctx.queue.push(T)`. T's rc is now 0,
    ///    QUEUED is set, allocation is alive.
    /// 3. `Executor::drop` runs. Pre-fix step 2 (all_tasks walk)
    ///    would see `is_terminal(T) = false` (QUEUED set blocks
    ///    terminal), fall to the rc=0 branch, free T's allocation.
    ///    Then pre-fix step 3's `cross_queue.pop()` would deref
    ///    `cross_next` at offset 32 of freed memory. **UAF.**
    ///
    /// This test orchestrates exactly that ordering and verifies no
    /// UAF under tree-borrows miri. Post-fix `Executor::drop` step 1
    /// drains cross_queue first, routing T to deferred_free; step 2
    /// frees T cleanly + removes from all_tasks; step 3's walk sees
    /// nothing.
    ///
    /// Run pre-fix (UAF expected):
    ///   MIRIFLAGS="-Zmiri-tree-borrows -Zmiri-ignore-leaks" \
    ///     cargo +nightly miri test -p nexus-async-rt --lib \
    ///     cross_wake::tests::executor_drop_handles_terminal_in_cross_queue
    #[test]
    fn executor_drop_handles_terminal_in_cross_queue() {
        use crate::Executor;

        let ctx = make_ctx();
        let mut exec = Executor::new(8);
        exec.install_cross_wake_for_drop(Arc::clone(&ctx));

        // Spawn a Box task — registered in all_tasks. The future
        // returns Ready immediately so the next poll completes it.
        struct OnceFuture;
        impl std::future::Future for OnceFuture {
            type Output = ();
            fn poll(self: std::pin::Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<()> {
                Poll::Ready(())
            }
        }

        let handle = exec.spawn_boxed(OnceFuture);
        // Immediately drop the JoinHandle — task becomes detached
        // (HAS_JOIN cleared, rc → 1: just executor's ref).
        drop(handle);

        // Poll once → task completes via the joinable-but-detached
        // path: drop_future + complete_and_unref. With no JoinHandle
        // the executor's ref is the LAST ref, so complete_and_unref
        // returns FreeBox and the task is freed + removed from
        // all_tasks immediately. To set up the UAF scenario we need
        // a task that survives completion in all_tasks with a
        // cross-thread holder. Easier path: use a JoinHandle that
        // we keep alive past completion to pin the task in
        // all_tasks, then simulate the cross-queue race directly.
        exec.poll();

        // Fresh setup: spawn another task and keep its handle.
        let kept_handle = exec.spawn_boxed(OnceFuture);
        exec.poll();
        // Task is now COMPLETED with rc=1 (just the JoinHandle).

        let task_ptr = kept_handle.raw_ptr();

        // Simulate "off-thread holder dropped TaskRef terminal": we
        // emulate by manually dropping the JoinHandle's ref + setting
        // QUEUED + pushing to cross_queue. The drop sequence:
        //   - clear HAS_JOIN, take_join_waker (no waker), ref_dec
        //     → rc 1 → 0, COMPLETED, no lifecycle → terminal.
        //   - On a real off-thread holder, dispose_terminal would push
        //     to cross_queue. We bypass JoinHandle::Drop's TaskRef
        //     route (which goes through dispose_terminal locally) and
        //     manually push to simulate the off-thread case.
        std::mem::forget(kept_handle);
        // SAFETY: task_ptr is the raw pointer from the forgotten
        // JoinHandle. Task is COMPLETED with rc=1. clear_has_join
        // clears the lifecycle flag; ref_dec brings rc → 0 → terminal.
        unsafe {
            crate::task::clear_has_join(task_ptr);
            let action = crate::task::ref_dec(task_ptr);
            assert!(matches!(action, crate::task::FreeAction::FreeBox));
        }
        // Task is now in TERMINAL state, allocation alive, in all_tasks.
        // Set QUEUED + push to cross_queue to mirror the off-thread
        // dispose_terminal scenario.
        // SAFETY: task_ptr is terminal but allocation is alive (no one
        // freed it). try_set_queued is an atomic on the header. push
        // uses the cross_next intrusive link.
        unsafe {
            assert!(crate::task::try_set_queued(task_ptr));
            ctx.queue.push(task_ptr);
        }

        // Drop the executor. Pre-fix this UAFs. Post-fix it cleans
        // up via step 1's pre-walk drain.
        drop(exec);
    }
}
