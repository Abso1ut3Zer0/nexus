//! Single-threaded async runtime.
//!
//! Two spawn strategies:
//! - **`spawn_boxed()`** — Box-allocated. Default. No setup needed.
//! - **`spawn_slab()`** — Slab-allocated. Pre-allocated, zero-alloc
//!   hot path. Requires slab configured via [`RuntimeBuilder::slab_unbounded`] or [`RuntimeBuilder::slab_bounded`].
//!
//! ```ignore
//! use nexus_async_rt::*;
//! use nexus_slab::byte::unbounded::Slab;
//! use nexus_rt::WorldBuilder;
//!
//! let mut world = WorldBuilder::new().build();
//!
//! // Simple — Box-allocated tasks, no slab setup
//! let mut rt = Runtime::new(&mut world);
//! rt.block_on(async {
//!     spawn_boxed(async { /* Box-allocated */ });
//! });
//!
//! // Power user — with slab for hot-path tasks
//! // SAFETY: single-threaded runtime.
//! let slab = unsafe { Slab::<256>::with_chunk_capacity(64) };
//! let mut rt = Runtime::builder(&mut world)
//!     .slab_unbounded(slab)
//!     .build();
//! rt.block_on(async {
//!     spawn_boxed(async { /* Box-allocated, long-lived */ });
//!     spawn_slab(async { /* slab-allocated, hot path */ });
//! });
//! ```

// Single-threaded runtime — futures are intentionally !Send.
#![allow(clippy::future_not_send)]
#![cfg(unix)]
#![warn(missing_docs)]

mod alloc;
mod backoff;
mod cancel;
pub mod channel;
mod context;
pub(crate) mod cross_wake;
mod io;
pub mod net;
mod runtime;
mod shutdown;
mod task;
mod timer;
#[cfg(feature = "tokio-compat")]
pub mod tokio_compat;
#[cfg(feature = "tokio-compat")]
pub use tokio_compat::{TokioJoinError, TokioJoinHandle, spawn_on_tokio};
mod waker;
mod world_ctx;

// Re-export slab type for convenience — users create the slab and hand it to the builder.
pub use alloc::SlabClaim;
pub use backoff::{Backoff, BackoffBuilder, Exhausted};
pub use cancel::{CancellationToken, DropGuard};
pub use context::{
    after, after_delay, event_time, interval, interval_at, sleep, sleep_until, timeout, timeout_at,
    yield_now,
};
pub use io::IoHandle;
pub use net::{
    AsyncRead, AsyncWrite, OwnedReadHalf, OwnedWriteHalf, ReadHalf, TcpListener, TcpSocket,
    TcpStream, UdpSocket, WriteHalf,
};
pub use nexus_slab::byte::unbounded::Slab as ByteSlab;
pub use runtime::{
    QuiesceTimeout, Runtime, RuntimeBuilder, claim_slab, spawn_boxed, spawn_slab, try_claim_slab,
};
// `ShutdownStats` is the snapshot type users match on. `ShutdownStatsAtomics`
// is the Arc-shared inner that survives Runtime drop — `Runtime::shutdown_stats`
// returns `Arc<ShutdownStatsAtomics>` and users call `.snapshot()` to get a
// plain `ShutdownStats`.
pub use shutdown::{ShutdownHandle, ShutdownSignal};
pub use task::{JoinHandle, TASK_HEADER_SIZE};
pub use timer::{Elapsed, Interval, MissedTickBehavior, Sleep, Timeout, TimerHandle, YieldNow};
pub use world_ctx::WorldCtx;

use std::future::Future;
use std::task::{Context, Poll};

use waker::set_poll_context;

/// Recommended minimum slab slot size.
///
/// The actual minimum depends on the task: header (72 bytes) + `max(size_of::<F>(),
/// size_of::<T>())`. ZST futures need only 72 bytes. 128 is a conservative default
/// that covers most small futures.
pub const MIN_SLOT_SIZE: usize = 128;

// =============================================================================
// Executor
// =============================================================================

/// Single-threaded async executor.
///
/// Manages task lifecycle: spawn, poll, complete, free. Tasks are
/// allocated via Box (default) or slab (via `spawn_slab`). Each
/// task's header contains a `free_fn` that knows how to deallocate
/// its own storage — the executor doesn't know or care which
/// allocator was used.
/// # UnsafeCell on `incoming` and `deferred_free`
///
/// These fields are wrapped in `UnsafeCell` to prevent a provenance
/// aliasing violation. During `poll()`, raw pointers to these Vecs are
/// stored in TLS for wakers to push into. Later in the same `poll()`,
/// `complete_task(&mut self)` takes `&mut self` — which under Rust's
/// aliasing rules asserts exclusive access to ALL fields. Without
/// `UnsafeCell`, this invalidates the TLS pointers because two `&mut`
/// paths to the same memory exist. `UnsafeCell` opts these fields out
/// of `&mut`'s exclusivity guarantee, telling the compiler they may be
/// accessed through other paths (the TLS raw pointers).
///
/// This is NOT a performance concern — `UnsafeCell` is zero-sized and
/// `get()` compiles to a no-op pointer cast. The only effect is that
/// the compiler won't optimize based on exclusive access to these fields.
pub struct Executor {
    /// Incoming ready tasks. Wakers and spawn push here.
    /// Swapped with `draining` at the start of each poll cycle.
    ///
    /// Wrapped in `UnsafeCell` because raw pointers to this Vec are stored
    /// in TLS during `poll()`. Without `UnsafeCell`, `&mut self` on methods
    /// like `complete_task` would invalidate the TLS pointer's provenance
    /// (exclusive `&mut` covers all non-UnsafeCell fields).
    incoming: std::cell::UnsafeCell<Vec<*mut u8>>,

    /// Tasks being drained this cycle. Iterated linearly.
    /// Does NOT need UnsafeCell — only accessed through `&mut self` in poll().
    draining: Vec<*mut u8>,

    /// All live task pointers. Slab-indexed for O(1) removal.
    all_tasks: slab::Slab<*mut u8>,

    /// Number of live tasks.
    live_count: usize,

    /// Maximum tasks to poll per cycle before yielding to IO.
    tasks_per_cycle: usize,

    /// Completed task slots awaiting deferred free.
    ///
    /// Same UnsafeCell rationale as `incoming` — TLS pointer stored during poll.
    deferred_free: std::cell::UnsafeCell<Vec<*mut u8>>,

    /// Atomic counters for abnormal-shutdown paths. Surfaced via
    /// [`Runtime::shutdown_stats`](crate::Runtime::shutdown_stats),
    /// which returns an `Arc` clone so users can read AFTER Runtime
    /// drop (the counters fire DURING `Executor::drop`; pre-drop
    /// snapshots always read zero). Per CALLOUT 5 of PR 2's plan,
    /// these paths increment counters ONLY — no `eprintln!`/`tracing`
    /// in new paths. PR 1a's existing eprintlns in the
    /// slab-unwinding-abort path stay (only signal at moment of
    /// process abort).
    shutdown_stats: std::sync::Arc<ShutdownStatsAtomics>,

    /// Cross-wake context, set by Runtime via [`Executor::install_cross_wake_for_drop`]
    /// after construction. `Executor::drop` uses it to drain the
    /// cross-thread queue at shutdown end and tally
    /// `cross_queue_undrained`. `None` for bare `Executor` use in
    /// tests (no Runtime, no cross-queue inspection at drop).
    cross_wake_for_drop: Option<std::sync::Arc<crate::cross_wake::CrossWakeContext>>,
}

/// Atomic counters backing [`ShutdownStats`]. Written by `Executor`,
/// readable via the handle returned by
/// [`Runtime::shutdown_stats`](crate::Runtime::shutdown_stats).
///
/// Atomics are used (not `Cell`) so the user-facing handle can survive
/// `Runtime::drop` and be read on the same thread post-drop. All
/// updates use `Relaxed` ordering — the counters are observability,
/// not synchronization.
#[derive(Default, Debug)]
pub struct ShutdownStatsAtomics {
    aborted_unwinds: std::sync::atomic::AtomicU64,
    leaked_box_tasks: std::sync::atomic::AtomicU64,
    unbalanced_normal_shutdowns: std::sync::atomic::AtomicU64,
    cross_queue_undrained: std::sync::atomic::AtomicU64,
}

impl ShutdownStatsAtomics {
    /// Snapshot the current counter values into a plain
    /// [`ShutdownStats`]. Loads are `Relaxed` — observability, not
    /// synchronization.
    pub fn snapshot(&self) -> ShutdownStats {
        use std::sync::atomic::Ordering;
        ShutdownStats {
            aborted_unwinds: self.aborted_unwinds.load(Ordering::Relaxed),
            leaked_box_tasks: self.leaked_box_tasks.load(Ordering::Relaxed),
            unbalanced_normal_shutdowns: self.unbalanced_normal_shutdowns.load(Ordering::Relaxed),
            cross_queue_undrained: self.cross_queue_undrained.load(Ordering::Relaxed),
        }
    }
}

/// Counters for abnormal-shutdown paths. Snapshot returned by
/// [`Runtime::shutdown_stats`](crate::Runtime::shutdown_stats).
///
/// All counters are `0` for a clean shutdown. Any non-zero counter is a
/// signal to investigate — the runtime hit a defensive code path that
/// should be unreachable in normal operation. Users own their
/// observability stack; the runtime emits no logs of its own (per
/// PR 2's design — see `ShutdownStats` doc-comment for the user
/// pattern).
///
/// # Example
///
/// ```ignore
/// let handle = runtime.shutdown_stats();   // Arc<ShutdownStatsAtomics>
/// drop(runtime);                            // counters fire during drop
/// let stats = handle.snapshot();            // plain ShutdownStats for matching
/// if stats.aborted_unwinds != 0
///     || stats.leaked_box_tasks != 0
///     || stats.unbalanced_normal_shutdowns != 0
///     || stats.cross_queue_undrained != 0
/// {
///     // user's own observability — log to wherever they want
///     my_logger::warn!("nexus runtime shutdown: {stats:?}");
/// }
/// ```
#[derive(Default, Debug, Clone, Copy)]
pub struct ShutdownStats {
    /// `Executor::drop` hit the slab-unwinding 100ms-wait-then-abort
    /// path. Indicates a producer thread held a slab task ref past
    /// Runtime drop during a panic. **The process aborted before this
    /// counter could be read** — non-zero means a previous run aborted
    /// (the counter is preserved across the abort by being stored in
    /// the executor's state, but reading it requires the runtime to
    /// have survived; in practice this counter is set just before
    /// abort and serves as a guarantee the abort path was hit if the
    /// runtime somehow survived).
    pub aborted_unwinds: u64,
    /// Box-allocated tasks the executor couldn't free during shutdown
    /// unwinding (outstanding cross-thread refs, leaked to avoid
    /// double-panic). Memory leak, not UAF. Box memory is reclaimed
    /// at process exit.
    pub leaked_box_tasks: u64,
    /// Normal shutdown (no panic in flight) found an `all_tasks` entry
    /// with `rc > 0`. Debug builds panic. Release builds eprintln +
    /// leak. Indicates a producer didn't release refs before Runtime
    /// drop — call [`Runtime::shutdown_quiesce`](crate::Runtime::shutdown_quiesce)
    /// before drop to surface this as an `Err` instead.
    pub unbalanced_normal_shutdowns: u64,
    /// Cross-thread queue entries that landed after Runtime drop and
    /// were never drained (the leak path inherited from PR 1a's
    /// dispose_terminal off-thread branch). Pure memory leak.
    pub cross_queue_undrained: u64,
}

/// Default poll limit.
const DEFAULT_TASKS_PER_CYCLE: usize = 64;

impl Executor {
    /// Create an executor.
    pub fn new(initial_capacity: usize) -> Self {
        Self {
            incoming: std::cell::UnsafeCell::new(Vec::with_capacity(initial_capacity)),
            draining: Vec::with_capacity(initial_capacity),
            all_tasks: slab::Slab::with_capacity(initial_capacity),
            live_count: 0,
            tasks_per_cycle: DEFAULT_TASKS_PER_CYCLE,
            shutdown_stats: std::sync::Arc::new(ShutdownStatsAtomics::default()),
            cross_wake_for_drop: None,
            deferred_free: std::cell::UnsafeCell::new(Vec::new()),
        }
    }

    /// Reserve a tracker key for external allocation (slab spawn).
    pub(crate) fn next_tracker_key(&self) -> u32 {
        let key = self.all_tasks.vacant_key();
        debug_assert!(
            u32::try_from(key).is_ok(),
            "more than 4 billion concurrent tasks — tracker_key overflow"
        );
        key as u32
    }

    /// Spawn an async task via Box allocation. Returns a [`JoinHandle`]
    /// that can be awaited for the task's output.
    pub fn spawn_boxed<F>(&mut self, future: F) -> task::JoinHandle<F::Output>
    where
        F: Future + 'static,
        F::Output: 'static,
    {
        let tracker_key = self.all_tasks.vacant_key();
        debug_assert!(
            u32::try_from(tracker_key).is_ok(),
            "more than 4 billion concurrent tasks — tracker_key overflow"
        );
        // Read the runtime's cross-wake context from TLS — installed at
        // RuntimeBuilder::build, lifetime of Runtime. Null when no
        // Runtime is alive (e.g., direct Executor use in tests); the
        // task header's cross_wake_ctx becomes null and dispose_terminal
        // routes those tasks via its null-ctx fallback.
        let cross_wake_ctx = crate::cross_wake::current_runtime_ctx();
        let ptr = task::box_spawn_joinable(future, tracker_key as u32, cross_wake_ctx);

        self.enqueue(ptr);
        task::JoinHandle::new(ptr)
    }

    /// Spawn a task with a pre-allocated pointer (from slab).
    ///
    /// The task at `ptr` must have been constructed with joinable or
    /// fire-and-forget constructors and a valid `free_fn`.
    pub(crate) fn spawn_raw(&mut self, ptr: *mut u8) {
        self.enqueue(ptr);
    }

    /// Common enqueue logic for spawn and spawn_raw.
    fn enqueue(&mut self, ptr: *mut u8) {
        self.all_tasks.insert(ptr);
        // SAFETY: ptr is a freshly constructed task. set_queued marks the
        // dedup flag so the task isn't double-queued by a concurrent wake.
        unsafe { task::set_queued(ptr, true) };
        // SAFETY: single-threaded, no concurrent access during enqueue.
        // UnsafeCell grants interior mutability for TLS pointer aliasing.
        unsafe { &mut *self.incoming.get() }.push(ptr);
        self.live_count += 1;
    }

    /// Drain the cross-thread wake inbox into the local ready queue.
    ///
    /// Called at the start of each poll cycle. Tasks pushed from other
    /// threads via `CrossWakeQueue::push` are moved into `incoming`.
    /// Completed tasks are routed to `deferred_free` instead — they
    /// were pushed for cleanup (not re-polling) by `cross_task_drop`.
    /// Drains at most `limit` tasks (remaining are picked up next cycle).
    pub(crate) fn drain_cross_thread(
        &mut self,
        inbox: &crate::cross_wake::CrossWakeQueue,
        limit: usize,
    ) -> usize {
        let mut drained = 0;
        while drained < limit {
            match inbox.pop() {
                Some(task_ptr) => {
                    // SAFETY: task_ptr is a live task pushed by a cross-thread waker.
                    // clear_queued clears the QUEUED dedup flag so the task can be re-queued.
                    unsafe { task::clear_queued(task_ptr) };

                    // Check if TERMINAL was reached (e.g., cross-thread waker
                    // produced TERMINAL via ref_dec while the task was queued).
                    // Only TERMINAL tasks go to deferred_free. Completed tasks
                    // with outstanding refs must NOT be freed prematurely.
                    // SAFETY: task_ptr is a live task; is_terminal reads the packed state.
                    if unsafe { task::is_terminal(task_ptr) } {
                        // SAFETY: UnsafeCell interior mutability; single-threaded.
                        unsafe { &mut *self.deferred_free.get() }.push(task_ptr);
                    } else {
                        // SAFETY: UnsafeCell interior mutability; single-threaded.
                        unsafe { &mut *self.incoming.get() }.push(task_ptr);
                    }
                    drained += 1;
                }
                None => break,
            }
        }
        drained
    }

    /// Poll all ready tasks once.
    pub fn poll(&mut self) -> usize {
        let mut completed = 0;

        // Drain deferred frees from last cycle.
        // SAFETY: single-threaded, TLS not yet set for this cycle.
        // UnsafeCell grants interior mutability.
        for ptr in unsafe { &mut *self.deferred_free.get() }.drain(..) {
            // SAFETY: ptr is a terminal task; tracker_key reads offset 60 of the header.
            let key = unsafe { task::tracker_key(ptr) } as usize;
            // SAFETY: ptr is terminal (refcount 0, COMPLETED set). free_fn was
            // set at spawn time and dispatches to Box::dealloc or slab free.
            unsafe { task::free_task(ptr) };
            if self.all_tasks.contains(key) {
                self.all_tasks.remove(key);
            }
        }

        // SAFETY: single-threaded, swapping before TLS is set.
        // UnsafeCell grants interior mutability for incoming.
        std::mem::swap(unsafe { &mut *self.incoming.get() }, &mut self.draining);

        // Derive TLS pointers from UnsafeCell — NOT from &mut self field borrows.
        // This is critical: complete_task(&mut self) later in this function must
        // not invalidate the TLS pointers. UnsafeCell fields are excluded from
        // &mut self's exclusivity guarantee.
        let _guard = set_poll_context(self.incoming.get(), self.deferred_free.get());

        let limit = self.tasks_per_cycle.min(self.draining.len());
        let draining_ptr: *const Vec<*mut u8> = &raw const self.draining;
        // SAFETY: draining_ptr is derived from &raw const on a field we own.
        // Slicing to limit avoids out-of-bounds.
        let drain_slice = unsafe { &(&*draining_ptr)[..limit] };

        for &ptr in drain_slice {
            // SAFETY: ptr is a live task in all_tasks. is_completed reads
            // the packed state word at offset 24.
            if unsafe { task::is_completed(ptr) } {
                continue;
            }

            // SAFETY: ptr is a live, non-completed task. Clearing the QUEUED
            // dedup flag allows future wakes to re-queue it.
            unsafe { task::set_queued(ptr, false) };

            // SAFETY: ptr is a live task, ref_count >= 1 (executor holds a ref).
            // task_waker increments ref_count; drop after poll decrements it.
            let waker = unsafe { crate::waker::task_waker(ptr) };
            let mut cx = Context::from_waker(&waker);

            // SAFETY: ptr points to a live, non-completed task. poll_task
            // pins the future and polls it with the provided context.
            let poll_result = unsafe { task::poll_task(ptr, &mut cx) };

            drop(waker);

            match poll_result {
                Poll::Pending => {}
                Poll::Ready(()) => {
                    self.complete_task(ptr);
                    completed += 1;
                }
            }
        }

        if limit < self.draining.len() {
            // SAFETY: single-threaded, UnsafeCell interior mutability.
            // TLS guard is about to drop; remaining un-polled tasks are
            // moved back to incoming for the next cycle.
            unsafe { &mut *self.incoming.get() }.extend_from_slice(&self.draining[limit..]);
        }
        self.draining.clear();

        completed
    }

    /// Number of live tasks.
    pub fn task_count(&self) -> usize {
        self.live_count
    }

    /// Number of tasks tracked in the executor's `all_tasks` slab.
    /// Includes COMPLETED-but-still-referenced tasks (a `JoinHandle`
    /// or cross-thread waker holds a ref) — distinguishing it from
    /// `task_count()` which decrements `live_count` unconditionally on
    /// completion.
    ///
    /// `shutdown_quiesce` uses this for its quiesce check: a task that
    /// completed but has outstanding refs WILL fire one of the
    /// abnormal-shutdown branches in `Executor::drop` (debug-panic
    /// "outstanding references" or release-eprintln + counter
    /// increment). Quiesce-as-`Ok` requires `all_tasks` to be empty,
    /// not just `live_count == 0`. (PR2-John-review item 2.)
    pub(crate) fn outstanding_tasks(&self) -> usize {
        self.all_tasks.len()
    }

    /// Number of completed task slots awaiting deferred free.
    #[cfg(test)]
    pub fn deferred_free_count(&self) -> usize {
        // SAFETY: single-threaded, read-only snapshot.
        unsafe { &*self.deferred_free.get() }.len()
    }

    /// Returns an Arc handle to the shutdown counters. Callers can
    /// hold it past Runtime drop to read final values via
    /// [`ShutdownStatsAtomics::snapshot`].
    pub(crate) fn shutdown_stats(&self) -> std::sync::Arc<ShutdownStatsAtomics> {
        std::sync::Arc::clone(&self.shutdown_stats)
    }

    /// Counter increments for the abnormal-shutdown branches.
    /// Per CALLOUT 5 of PR 2's plan: counter-only — no eprintln,
    /// no tracing, no log calls. Users own their observability.
    fn record_aborted_unwind(&self) {
        self.shutdown_stats
            .aborted_unwinds
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }

    fn record_leaked_box(&self) {
        self.shutdown_stats
            .leaked_box_tasks
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }

    fn record_unbalanced_normal(&self) {
        self.shutdown_stats
            .unbalanced_normal_shutdowns
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }

    /// Add `count` to the `cross_queue_undrained` counter. Called from
    /// `Executor::drop` after the all_tasks loop, when the cross-thread
    /// queue's tail-end is drained for the diagnostic count.
    fn record_cross_queue_undrained(&self, count: u64) {
        self.shutdown_stats
            .cross_queue_undrained
            .fetch_add(count, std::sync::atomic::Ordering::Relaxed);
    }

    /// Wire the runtime's cross-wake context into the executor so
    /// `Executor::drop` can drain + count the cross-thread queue at
    /// shutdown end. Called by `RuntimeBuilder::build` after both
    /// `Executor::new` and `Arc::new(CrossWakeContext { ... })`.
    pub(crate) fn install_cross_wake_for_drop(
        &mut self,
        cross_wake: std::sync::Arc<crate::cross_wake::CrossWakeContext>,
    ) {
        self.cross_wake_for_drop = Some(cross_wake);
    }

    /// Returns `true` if any tasks are queued for polling.
    pub fn has_ready(&self) -> bool {
        // SAFETY: single-threaded, read-only snapshot.
        !unsafe { &*self.incoming.get() }.is_empty()
    }

    /// Set the maximum tasks to poll per cycle.
    pub fn set_tasks_per_cycle(&mut self, limit: usize) {
        self.tasks_per_cycle = limit;
    }

    /// Complete a task: handle joinable vs fire-and-forget paths.
    ///
    /// Uses `complete_and_unref` to atomically set COMPLETED and decrement
    /// the executor's reference in a single atomic operation — eliminating
    /// the race window that caused SIGABRT with cross-thread wakers.
    ///
    /// Three branches based on task state:
    /// - **Aborted:** drop F (still live — poll_join short-circuited), notify joiner
    /// - **Joinable (HAS_JOIN):** T is live in the union, don't touch it — JoinHandle owns it
    /// - **Fire-and-forget / detached:** drop the value (F or T) and free
    ///
    /// # Safety invariants
    ///
    /// `ptr` must point to a task that just returned `Poll::Ready(())` from poll_task.
    fn complete_task(&mut self, ptr: *mut u8) {
        // SAFETY: ptr just returned Poll::Ready from poll_task; the task is
        // live and all header fields are valid for the state reads below.
        let aborted = unsafe { task::is_aborted(ptr) };

        if aborted {
            // Aborted: poll_join saw ABORTED and returned Ready without polling F.
            // F is still live in the union. drop_fn still targets F.
            // SAFETY: F is live in the FutureOrOutput union; drop_fn targets F.
            unsafe { task::drop_task_future(ptr) };
            self.live_count -= 1;

            // SAFETY: has_join reads a flag in the packed state word.
            if unsafe { task::has_join(ptr) } {
                // SAFETY: take_join_waker reads the join waker slot at offset 40.
                let waker = unsafe { task::take_join_waker(ptr) };
                if let Some(w) = waker {
                    w.wake();
                }
            }

            // SAFETY: complete_and_unref atomically sets COMPLETED and
            // decrements the executor's reference in one CAS.
            match unsafe { task::complete_and_unref(ptr) } {
                task::FreeAction::Retain => {}
                task::FreeAction::FreeBox | task::FreeAction::FreeSlab => {
                    // SAFETY: terminal state; tracker_key at offset 60, free_task
                    // dispatches through the header's free_fn.
                    let key = unsafe { task::tracker_key(ptr) } as usize;
                    // SAFETY: terminal state confirmed; free_task dispatches through the header's free_fn.
                    unsafe { task::free_task(ptr) };
                    self.all_tasks.remove(key);
                }
            }
        // SAFETY: has_join reads the HAS_JOIN flag from the packed task state word.
        } else if unsafe { task::has_join(ptr) } {
            // Joinable: poll_join dropped F and wrote T. drop_fn = drop_output::<T>.
            // Don't drop T — JoinHandle will read it or drop it on handle drop.
            self.live_count -= 1;

            // Wake the joiner so it can poll the JoinHandle and read T.
            // SAFETY: take_join_waker reads the join waker slot at offset 40.
            let waker = unsafe { task::take_join_waker(ptr) };
            if let Some(w) = waker {
                w.wake();
            }

            // SAFETY: see above -- complete_and_unref CAS on the packed state.
            match unsafe { task::complete_and_unref(ptr) } {
                task::FreeAction::Retain => {}
                task::FreeAction::FreeBox | task::FreeAction::FreeSlab => {
                    // Terminal — JoinHandle already dropped (detached). Drop output.
                    // SAFETY: T is live in the union; drop_fn now targets T.
                    unsafe { task::drop_task_future(ptr) };
                    // SAFETY: terminal state; read tracker_key then free.
                    let key = unsafe { task::tracker_key(ptr) } as usize;
                    // SAFETY: terminal state confirmed; free_task dispatches through the header's free_fn.
                    unsafe { task::free_task(ptr) };
                    self.all_tasks.remove(key);
                }
            }
        } else {
            // Fire-and-forget or detached (HAS_JOIN cleared by JoinHandle::Drop).
            // SAFETY: the value (F or T) in the union must be dropped.
            unsafe { task::drop_task_future(ptr) };
            self.live_count -= 1;

            // SAFETY: see above -- complete_and_unref CAS on the packed state.
            match unsafe { task::complete_and_unref(ptr) } {
                task::FreeAction::Retain => {}
                task::FreeAction::FreeBox | task::FreeAction::FreeSlab => {
                    // SAFETY: terminal state; read tracker_key then free.
                    let key = unsafe { task::tracker_key(ptr) } as usize;
                    // SAFETY: terminal state confirmed; free_task dispatches through the header's free_fn.
                    unsafe { task::free_task(ptr) };
                    self.all_tasks.remove(key);
                }
            }
        }
    }

    /// Returns raw pointers for TLS setup.
    ///
    /// Takes `&self` because `UnsafeCell::get()` only needs a shared reference.
    /// The raw pointers carry write provenance from the `UnsafeCell`.
    pub(crate) fn poll_context_ptrs(&self) -> (*mut Vec<*mut u8>, *mut Vec<*mut u8>) {
        (self.incoming.get(), self.deferred_free.get())
    }

    /// Cancel a task by ID.
    #[allow(dead_code)]
    pub(crate) fn cancel(&mut self, id: task::TaskId) {
        let ptr = id.0;
        // SAFETY: ptr is a task pointer; is_completed reads the packed state.
        if unsafe { task::is_completed(ptr) } {
            return;
        }
        // SAFETY: single-threaded, no TLS active during cancel.
        // UnsafeCell grants interior mutability.
        unsafe { &mut *self.incoming.get() }.retain(|p| *p != ptr);
        self.draining.retain(|p| *p != ptr);
        self.complete_task(ptr);
    }
}

impl Drop for Executor {
    fn drop(&mut self) {
        // Step 1 (PR 2 §2.3, fixed in PR2-John-review item 1): drain
        // the cross-thread queue FIRST, before walking `all_tasks`.
        //
        // **Why first.** An off-thread holder dropping a TaskRef
        // terminal between the runtime's last drain and `Executor::drop`
        // start enqueues a TERMINAL task pointer in `cross_queue`
        // (`try_set_queued + push`). The task allocation is alive (we
        // haven't freed it yet) but rc=0, COMPLETED set, QUEUED set.
        //
        // If we walked `all_tasks` BEFORE draining cross_queue:
        //   - `is_terminal` returns false (QUEUED bit is set, mask
        //     `INERT_MASK` doesn't clear it).
        //   - Falls through to the rc=0 branch → `free_task(ptr)`.
        //   - Step 3's pop then derefs `cross_next` at offset 32 of
        //     the freed allocation. **UAF.**
        //
        // By draining cross_queue first, `drain_cross_thread` clears
        // QUEUED and routes the terminal entry to `deferred_free`
        // (state is now just COMPLETED → `is_terminal` returns true
        // there). Step 2's deferred_free drain frees + removes from
        // `all_tasks`. Step 3's all_tasks walk no longer sees it.
        //
        // Entries that arrive AFTER step 1 (off-thread holder pushes
        // mid-drop) leave a stale pointer in cross_queue. No one pops
        // it post-drop (no executor) so no UAF; the leak is bounded
        // by the lifetime of `Arc<CrossWakeContext>` and the entry
        // is freed-then-pointer-leaked when the last Arc clone drops.
        let undrained = self.cross_wake_for_drop.take().map_or(0u64, |ctx| {
            self.drain_cross_thread(&ctx.queue, usize::MAX) as u64
        });
        if undrained > 0 {
            self.record_cross_queue_undrained(undrained);
        }

        // Step 2: drain deferred-free (now includes any terminals
        // routed by step 1's cross-queue drain). Updates `all_tasks`
        // bookkeeping in the right order (read tracker_key BEFORE
        // free_task).
        self.drop_drain_deferred_free();

        // Step 3: walk surviving tasks. Each task hits one of four
        // branches: TERMINAL (free directly), not-completed (try to
        // complete + maybe free), outstanding-refs (route to unwinding
        // or normal-shutdown handlers), or zero-refs (free).
        for (_, &ptr) in &self.all_tasks {
            // SAFETY: ptr is a live task pointer tracked in all_tasks.
            // is_terminal reads the packed state word.
            if unsafe { task::is_terminal(ptr) } {
                // TERMINAL: completed, zero refs, all flags cleared.
                // SAFETY: terminal state — safe to free via the header's free_fn.
                unsafe { task::free_task(ptr) };
                continue;
            }

            // SAFETY: is_completed reads the packed state word.
            if !unsafe { task::is_completed(ptr) } && Self::drop_complete_and_maybe_free(ptr) {
                continue;
            }

            // SAFETY: ref_count reads bits 6+ of the packed state word.
            let rc = unsafe { task::ref_count(ptr) };
            if rc > 0 {
                if std::thread::panicking() {
                    self.drop_outstanding_unwinding(ptr, rc);
                } else {
                    self.drop_outstanding_normal(ptr, rc);
                }
                continue;
            }

            // SAFETY: completed with zero refs — terminal. Free via header's free_fn.
            unsafe { task::free_task(ptr) };
        }
    }
}

impl Executor {
    /// Drop step 1: drain deferred-free entries from the last poll
    /// cycle (or accumulated since one). Each entry is a completed
    /// task whose final ref dropped after the last poll cycle's drain
    /// ran; we own them and must free the storage + remove from
    /// `all_tasks`. The order (read tracker_key, then free_task, then
    /// remove key) matters because tracker_key reads from the task
    /// header — must happen before the allocation is freed.
    ///
    /// SAFETY: `&mut self` in Drop, no concurrent access.
    fn drop_drain_deferred_free(&mut self) {
        // SAFETY: &mut self in Drop, single-threaded. UnsafeCell interior mutability.
        for ptr in unsafe { &mut *self.deferred_free.get() }.drain(..) {
            // SAFETY: ptr is a terminal task. Read tracker_key (offset 60)
            // before freeing the allocation.
            let key = unsafe { task::tracker_key(ptr) } as usize;
            // SAFETY: terminal state — free via the header's free_fn.
            unsafe { task::free_task(ptr) };
            if self.all_tasks.contains(key) {
                self.all_tasks.remove(key);
            }
        }
    }

    /// Drop step 2 / branch B: task hasn't completed yet. Drop its
    /// future (running its destructors — Aeron publishers, sockets,
    /// file handles all release here), then atomically set COMPLETED +
    /// decrement the executor's ref. Returns true if the resulting
    /// state is terminal (we freed the slot) — caller `continue`s.
    /// Returns false when the task still has cross-thread refs and
    /// the caller falls through to the rc-check.
    ///
    /// SAFETY: caller guarantees `ptr` references a not-yet-completed
    /// task with the executor's ref still held.
    fn drop_complete_and_maybe_free(ptr: *mut u8) -> bool {
        // SAFETY: ptr is a live, not-yet-completed task. drop_task_future
        // drops F (the future) via the header's drop_fn.
        unsafe { task::drop_task_future(ptr) };
        // SAFETY: complete_and_unref atomically sets COMPLETED and decrements
        // the executor's reference.
        match unsafe { task::complete_and_unref(ptr) } {
            task::FreeAction::Retain => false,
            task::FreeAction::FreeBox | task::FreeAction::FreeSlab => {
                // SAFETY: terminal state — free via header's free_fn.
                unsafe { task::free_task(ptr) };
                true
            }
        }
    }

    /// Drop step 2 / branch C+D: task completed but has outstanding
    /// cross-thread refs, and we're mid-unwind. Behavior splits by
    /// allocation type:
    ///
    /// - **Slab task**: wait up to 100ms for refs to settle (producer
    ///   threads may be racing to release). If settled, free cleanly.
    ///   If not, abort — leaking would UAF when `_slab_guard` releases
    ///   the slab backing storage after `Executor::drop` returns.
    /// - **Box task**: leak. The Box sits in process memory until
    ///   process exit; outstanding cross-thread refs that later run
    ///   `ref_dec` see valid memory.
    ///
    /// The eprintln!s in this branch are PR 1a's existing signals —
    /// they stay (per CALLOUT 5 of PR 2's plan, removable post-§2.4
    /// once `shutdown_quiesce` makes this branch unreachable in
    /// normal operation). The slab and box helpers each increment
    /// the relevant `ShutdownStats` counter (`aborted_unwinds` /
    /// `leaked_box_tasks`).
    ///
    /// SAFETY: caller guarantees `ptr` references a completed task
    /// with rc > 0, called during unwind.
    fn drop_outstanding_unwinding(&self, ptr: *mut u8, rc: usize) {
        // SAFETY: ptr is a completed task with outstanding refs.
        // is_slab_allocated reads the SLAB_ALLOCATED flag in the packed state.
        if unsafe { task::is_slab_allocated(ptr) } {
            self.drop_outstanding_slab_unwinding(ptr);
        } else {
            self.drop_outstanding_box_unwinding(ptr, rc);
        }
    }

    /// Slab branch of the unwinding path. See `drop_outstanding_unwinding`
    /// for context. Increments `aborted_unwinds` counter on the
    /// abort path (PR 2 §2.3) BEFORE calling `std::process::abort()`
    /// so a parent process inspecting the runtime's state can see
    /// the counter via shared memory or memory-mapped logging.
    fn drop_outstanding_slab_unwinding(&self, ptr: *mut u8) {
        let deadline = std::time::Instant::now() + std::time::Duration::from_millis(100);
        // SAFETY: ref_count reads bits 6+ of the packed state word. The
        // task allocation is alive (we haven't freed it). Spinning waits
        // for cross-thread holders to release their refs.
        while unsafe { task::ref_count(ptr) } > 0 && std::time::Instant::now() < deadline {
            std::thread::yield_now();
        }
        // SAFETY: task allocation is alive; ref_count reads bits from the packed state word.
        if unsafe { task::ref_count(ptr) } > 0 {
            // Record before the abort — the eprintln stays per CALLOUT 5
            // (only signal at moment of process abort).
            self.record_aborted_unwind();
            eprintln!(
                "nexus-async-rt: slab task {ptr:p} has \
                 outstanding refs after 100ms during unwinding \
                 — aborting to avoid UAF on slab memory \
                 release. Cross-thread waker producer thread \
                 may be deadlocked or starved."
            );
            std::process::abort();
        }
        // Refs settled — free cleanly. Avoid the panic path.
        // SAFETY: refcount settled to 0; terminal state. Free via header's free_fn.
        unsafe { task::free_task(ptr) };
    }

    /// Box branch of the unwinding path. See `drop_outstanding_unwinding`
    /// for context. Leaks the box; safe — outstanding refs see valid
    /// memory until process exit. Increments `leaked_box_tasks` (PR 2 §2.3).
    fn drop_outstanding_box_unwinding(&self, _ptr: *mut u8, rc: usize) {
        self.record_leaked_box();
        eprintln!(
            "nexus-async-rt: executor dropped with {rc} outstanding \
             reference(s) during unwinding — suppressing panic to \
             avoid abort. Task resources were released via \
             drop_task_future; leaking box task allocation + waker \
             bookkeeping memory."
        );
    }

    /// Drop step 2 / branch E: task completed but has outstanding
    /// cross-thread refs, normal shutdown (no panic in flight). This
    /// indicates a user-side lifetime discipline violation — wakers
    /// or JoinHandles weren't dropped before the Runtime. Debug builds
    /// panic to surface the bug; release builds eprintln + leak to
    /// avoid UB. Increments `unbalanced_normal_shutdowns` (PR 2 §2.3)
    /// before either path.
    ///
    /// SAFETY: caller guarantees `ptr` references a completed task
    /// with rc > 0, called outside any panic.
    fn drop_outstanding_normal(&self, _ptr: *mut u8, rc: usize) {
        self.record_unbalanced_normal();
        #[cfg(debug_assertions)]
        panic!(
            "executor dropped with {rc} outstanding reference(s) — \
             all wakers and JoinHandles must be dropped before the Runtime"
        );
        #[cfg(not(debug_assertions))]
        eprintln!(
            "nexus-async-rt: executor dropped with {rc} outstanding task \
             reference(s) — leaking to avoid UB"
        );
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
#[allow(
    unused_must_use,
    clippy::float_cmp,
    dead_code,
    clippy::ref_option,
    clippy::redundant_closure_for_method_calls,
    clippy::let_underscore_future,
    clippy::semicolon_if_nothing_returned
)]
mod tests {
    use super::*;
    use std::hint::black_box;
    use std::pin::Pin;
    use task::Task;

    fn test_executor() -> Executor {
        Executor::new(16)
    }

    // =========================================================================
    // Basic spawn + poll
    // =========================================================================

    #[test]
    fn spawn_and_poll_single_task() {
        let mut exec = test_executor();
        let mut done = false;
        let flag = &raw mut done;

        exec.spawn_boxed(async move {
            // SAFETY: single-threaded, flag lives on stack.
            unsafe { *flag = true };
        });

        assert_eq!(exec.task_count(), 1);
        let completed = exec.poll();
        assert_eq!(completed, 1);
        assert!(done);
        assert_eq!(exec.task_count(), 0);
    }

    #[test]
    fn spawn_multiple_tasks() {
        let mut exec = test_executor();

        for _ in 0..8 {
            exec.spawn_boxed(async {});
        }

        assert_eq!(exec.task_count(), 8);
        let completed = exec.poll();
        assert_eq!(completed, 8);
        assert_eq!(exec.task_count(), 0);
    }

    // =========================================================================
    // Pending tasks
    // =========================================================================

    #[test]
    fn pending_task_not_completed() {
        let mut exec = test_executor();

        // A future that is always pending.
        exec.spawn_boxed(std::future::pending::<()>());

        let completed = exec.poll();
        assert_eq!(completed, 0);
        assert_eq!(exec.task_count(), 1);
    }

    // =========================================================================
    // Waker: re-queue via wake_by_ref
    // =========================================================================

    #[test]
    fn immediate_task_completes() {
        let mut exec = test_executor();

        exec.spawn_boxed(async {
            // Immediately ready.
        });

        let completed = exec.poll();
        assert_eq!(completed, 1);
        assert_eq!(exec.task_count(), 0);
    }

    // =========================================================================
    // Self-waking task
    // =========================================================================

    #[test]
    fn self_waking_task_polled_again() {
        use std::cell::Cell;
        use std::rc::Rc;

        let mut exec = test_executor();

        let counter = Rc::new(Cell::new(0u32));
        let c = counter.clone();

        exec.spawn_boxed(async move {
            struct SelfWake {
                counter: Rc<Cell<u32>>,
            }
            impl Future for SelfWake {
                type Output = ();
                fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
                    let n = self.counter.get();
                    self.counter.set(n + 1);
                    if n < 3 {
                        cx.waker().wake_by_ref();
                        Poll::Pending
                    } else {
                        Poll::Ready(())
                    }
                }
            }
            SelfWake { counter: c }.await;
        });

        // Drain all polls.
        let mut total = 0;
        for _ in 0..10 {
            total += exec.poll();
            if exec.task_count() == 0 {
                break;
            }
        }
        assert_eq!(total, 1); // completed once
        assert_eq!(counter.get(), 4); // polled 4 times
    }

    // =========================================================================
    // Cancel
    // =========================================================================

    #[test]
    fn abort_task() {
        let mut exec = test_executor();
        let handle = exec.spawn_boxed(std::future::pending::<()>());

        assert_eq!(exec.task_count(), 1);
        assert!(handle.abort()); // was running, handle consumed
        exec.poll(); // abort takes effect on next poll
        assert_eq!(exec.task_count(), 0);
    }

    #[test]
    fn abort_frees_slot_for_reuse() {
        let mut exec = test_executor();
        let handle = exec.spawn_boxed(std::future::pending::<()>());
        handle.abort(); // consumes handle

        exec.poll(); // process abort + deferred free

        // Should be able to spawn again.
        exec.spawn_boxed(async {});
        assert_eq!(exec.task_count(), 1);
        exec.poll();
        assert_eq!(exec.task_count(), 0);
    }

    // =========================================================================
    // Poll limit (tasks_per_cycle)
    // =========================================================================

    #[test]
    fn poll_limit_respected() {
        let mut exec = test_executor();
        exec.set_tasks_per_cycle(2);

        for _ in 0..5 {
            exec.spawn_boxed(async {});
        }

        // Only 2 polled per cycle.
        let completed = exec.poll();
        assert_eq!(completed, 2);
        assert_eq!(exec.task_count(), 3);

        let completed = exec.poll();
        assert_eq!(completed, 2);
        assert_eq!(exec.task_count(), 1);

        let completed = exec.poll();
        assert_eq!(completed, 1);
        assert_eq!(exec.task_count(), 0);
    }

    // =========================================================================
    // Stale ready entries after cancel
    // =========================================================================

    #[test]
    fn cancel_with_stale_ready_entry() {
        use std::cell::Cell;
        use std::rc::Rc;

        let mut exec = test_executor();

        let polled = Rc::new(Cell::new(false));
        let p = polled.clone();

        // Spawn a self-waking task.
        struct WakeOnce(bool);
        impl Future for WakeOnce {
            type Output = ();
            fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
                if self.0 {
                    Poll::Ready(())
                } else {
                    self.0 = true;
                    cx.waker().wake_by_ref();
                    Poll::Pending
                }
            }
        }

        let handle = exec.spawn_boxed(WakeOnce(false));

        // First poll: sets is_queued again via wake_by_ref.
        exec.poll();

        // Abort while the task is in the ready queue (consumes handle).
        handle.abort();

        // Spawn a new task to prove we don't crash on the stale pointer.
        exec.spawn_boxed(async move {
            p.set(true);
        });

        exec.poll(); // processes abort + new task
        assert!(polled.get());
    }

    // =========================================================================
    // Refcount behavior
    // =========================================================================

    #[test]
    fn refcount_starts_at_one() {
        let task = Box::new(Task::new_boxed(async {}, 0));
        let ptr = Box::into_raw(task) as *mut u8;
        // SAFETY: ptr is a valid task just created above.
        assert_eq!(unsafe { task::ref_count(ptr) }, 1);
        // SAFETY: freeing the only reference; terminal state.
        unsafe { task::free_task(ptr) };
    }

    #[test]
    fn executor_drop_cleans_up_queued_tasks() {
        let mut exec = test_executor();
        exec.spawn_boxed(std::future::pending::<()>());
        exec.spawn_boxed(std::future::pending::<()>());
        exec.poll(); // poll them once
        // Drop executor — should free all tasks without panic.
        drop(exec);
    }

    // =========================================================================
    // Dispatch latency (rough, not controlled)
    // =========================================================================

    #[test]
    #[ignore]
    fn dispatch_latency() {
        use std::time::Instant;

        struct Noop;
        impl Future for Noop {
            type Output = ();
            fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
                cx.waker().wake_by_ref();
                Poll::Pending
            }
        }

        let mut exec = test_executor();
        exec.spawn_boxed(Noop);

        // Warmup.
        for _ in 0..10_000 {
            exec.poll();
        }

        let iters = 100_000;
        let start = Instant::now();
        for _ in 0..iters {
            exec.poll();
        }
        let elapsed = start.elapsed();
        let ns_per = elapsed.as_nanos() / iters;
        println!("dispatch: {ns_per} ns/poll (Box-allocated)");
        black_box(ns_per);
    }
}
