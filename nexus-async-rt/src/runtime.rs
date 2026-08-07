//! Single-threaded async runtime.
//!
//! [`Runtime`] owns an [`Executor`](crate::Executor) for spawned tasks, a
//! boxed root future, and an event-cycle timestamp. The root future is
//! driven to completion by [`block_on`](Runtime::block_on) or
//! [`block_on_busy`](Runtime::block_on_busy).
//!
//! Two spawn strategies:
//! - **`spawn_boxed()`** — Box-allocated. Default. No setup needed.
//! - **`spawn_slab()`** — Slab-allocated. Zero-alloc hot path.
//!   Requires slab configured via [`RuntimeBuilder::slab`].
//!
//! # Thread-local spawn
//!
//! [`spawn`] and [`spawn_slab`] are free functions that push tasks into
//! the current runtime via thread-local pointers set during `block_on`.
//! Calling them outside `block_on` panics.

use std::cell::Cell;
use std::future::Future;
use std::marker::PhantomData;
use std::pin::Pin;
use std::task::{Context, Poll, Wake, Waker};
use std::time::{Duration, Instant};

use crate::io::IoDriver;
use crate::task::JoinHandle;
use crate::timer::TimerDriver;
use crate::{Executor, WorldCtx};

/// Default number of loop iterations between non-blocking IO polls.
/// Matches tokio's heuristic (61, originally from Go's scheduler).
const DEFAULT_EVENT_INTERVAL: u32 = 61;

// =============================================================================
// Thread-local spawn context
// =============================================================================

thread_local! {
    /// Raw pointer to the active runtime's executor.
    /// Set on `block_on` entry, cleared on exit.
    static CURRENT: Cell<*mut Executor> = const { Cell::new(std::ptr::null_mut()) };
}

/// Spawn a Box-allocated task into the current runtime.
///
/// Returns a [`JoinHandle`] that can be awaited for the task's output.
/// Drop the handle to detach the task.
///
/// Must be called from within [`Runtime::block_on`] or
/// [`Runtime::block_on_busy`]. Panics otherwise.
///
/// # Panics
///
/// - If called outside a runtime context.
pub fn spawn_boxed<F>(future: F) -> JoinHandle<F::Output>
where
    F: Future + 'static,
    F::Output: 'static,
{
    CURRENT.with(|cell| {
        let ptr = cell.get();
        assert!(
            !ptr.is_null(),
            "spawn_boxed() called outside of Runtime::block_on"
        );
        // SAFETY: pointer was set by RuntimeGuard::enter at the start of
        // block_on and is valid for the duration of block_on. Single-threaded.
        let executor = unsafe { &mut *ptr };
        executor.spawn_boxed(future)
    })
}

/// Spawn a slab-allocated task into the current runtime.
///
/// Returns a [`JoinHandle`] that can be awaited for the task's output.
/// Zero allocation — the task is placed directly into a pre-allocated
/// slab slot via TLS.
///
/// # Panics
///
/// - If called outside a runtime context.
/// - If no slab is configured.
/// - If the slab is full (bounded slab).
/// - If the task future exceeds the slab's slot capacity.
pub fn spawn_slab<F>(future: F) -> JoinHandle<F::Output>
where
    F: Future + 'static,
    F::Output: 'static,
{
    CURRENT.with(|cell| {
        let ptr = cell.get();
        assert!(
            !ptr.is_null(),
            "spawn_slab() called outside of Runtime::block_on"
        );
        // SAFETY: pointer valid for duration of block_on. Single-threaded.
        let executor = unsafe { &mut *ptr };
        let tracker_key = executor.next_tracker_key();
        let task_ptr = crate::alloc::slab_spawn(future, tracker_key);
        executor.spawn_raw(task_ptr);
        JoinHandle::new(task_ptr)
    })
}

/// Access the current executor via TLS. Panics if outside `block_on`.
pub(crate) fn with_executor<R>(f: impl FnOnce(&mut Executor) -> R) -> R {
    CURRENT.with(|cell| {
        let ptr = cell.get();
        assert!(!ptr.is_null(), "called outside of Runtime::block_on");
        // SAFETY: pointer valid for duration of block_on. Single-threaded.
        let executor = unsafe { &mut *ptr };
        f(executor)
    })
}

/// Try to reserve a slab slot. Returns `None` if the slab is full.
///
/// Call `.spawn(future)` on the returned [`SlabClaim`](crate::alloc::SlabClaim)
/// to write a task and enqueue it. If dropped without spawning, the
/// slot is returned to the freelist automatically.
///
/// # Panics
///
/// - If called outside a runtime context.
/// - If no slab is configured.
pub fn try_claim_slab() -> Option<crate::alloc::SlabClaim> {
    CURRENT.with(|cell| {
        assert!(
            !cell.get().is_null(),
            "try_claim_slab() called outside of Runtime::block_on"
        );
    });
    crate::alloc::try_claim()
}

/// Reserve a slab slot. Panics if full or no slab configured.
///
/// Call `.spawn(future)` on the returned [`SlabClaim`](crate::alloc::SlabClaim)
/// to write a task and enqueue it. If dropped without spawning, the
/// slot is returned to the freelist automatically.
///
/// # Panics
///
/// - If called outside a runtime context.
/// - If no slab is configured.
/// - If the slab is full (bounded slab).
pub fn claim_slab() -> crate::alloc::SlabClaim {
    CURRENT.with(|cell| {
        assert!(
            !cell.get().is_null(),
            "claim_slab() called outside of Runtime::block_on"
        );
    });
    crate::alloc::claim()
}

// =============================================================================
// Runtime
// =============================================================================

/// Single-threaded async runtime.
///
/// `Runtime` is intrinsically thread-bound — its slab TLS state is
/// per-thread, so moving it to another thread would silently
/// desynchronize allocation dispatch. The type is therefore both
/// `!Send` and `!Sync`, enforced by a `PhantomData<*const ()>` marker.
///
/// ```compile_fail
/// use nexus_async_rt::Runtime;
/// fn assert_send<T: Send>() {}
/// assert_send::<Runtime>();
/// ```
///
/// ```compile_fail
/// use nexus_async_rt::Runtime;
/// fn assert_sync<T: Sync>() {}
/// assert_sync::<Runtime>();
/// ```
///
/// # Examples
///
/// ```ignore
/// use nexus_async_rt::{Runtime, spawn_boxed, spawn_slab};
/// use nexus_slab::byte::unbounded::Slab;
/// use nexus_rt::WorldBuilder;
///
/// let mut world = WorldBuilder::new().build();
///
/// // Simple — Box-allocated tasks
/// let mut rt = Runtime::new(&mut world);
/// rt.block_on(async {
///     spawn_boxed(async { /* Box-allocated */ });
/// });
///
/// // With slab for hot-path tasks
/// let slab = unsafe { Slab::<256>::with_chunk_capacity(64) };
/// let mut rt = Runtime::builder(&mut world)
///     .slab_unbounded(slab)
///     .build();
/// rt.block_on(async {
///     spawn_boxed(async { /* Box-allocated */ });
///     spawn_slab(async { /* slab-allocated */ });
/// });
/// ```
//
// `#[repr(C)]` is required for the `offset_of` assertion below to be
// sound. Under `repr(Rust)` (the default), the compiler is free to
// reorder fields for layout optimization, which would let an accidental
// declaration-order swap silently re-introduce BUG-1 (#167) while the
// offset comparison still happened to pass. `#[repr(C)]` guarantees
// field offsets follow declaration order modulo alignment padding,
// making the assertion enforce what it claims.
//
// This is NOT for FFI — `Runtime` has no foreign caller. It's purely
// to back the BUG-1 invariant with a language-spec guarantee instead
// of empirical rustc behavior.
#[repr(C)]
pub struct Runtime {
    /// Spawned task storage.
    ///
    /// Drops first (declaration order). `Executor::drop` walks
    /// `all_tasks` and frees any survivors via the slab TLS dispatch
    /// path, which requires `_slab_guard` to still be alive — see the
    /// field-order invariant on `_slab_guard`. Surviving tasks may
    /// also trigger `TaskRef::Drop → dispose_terminal`, which reads
    /// the runtime's cross-wake context from TLS — see the field-order
    /// invariant on `_cross_wake_tls_guard` below.
    executor: Executor,

    /// Clears the runtime's `CURRENT_RUNTIME_CTX` TLS slot on drop.
    ///
    /// **MUST drop AFTER `executor`**: when `Executor::drop` walks
    /// `all_tasks` and frees terminal tasks, any TaskRef::Drop fired
    /// from cross-thread holders (or local wakers cleaned up during
    /// teardown) reads `CURRENT_RUNTIME_CTX` via
    /// `crate::cross_wake::on_owning_executor` to decide whether to
    /// defer locally or queue cross-thread. If this guard drops before
    /// `executor`, the on-thread fast path silently misroutes terminal
    /// frees to the cross-queue. The `const _: ()` block below this
    /// struct enforces the ordering at compile time.
    ///
    /// **FAILURE MODE: silent UAF in production for slab tasks.** If
    /// this guard drops before `executor`, the on-thread fast path in
    /// `dispose_terminal::on_owning_executor` silently misroutes
    /// terminal `TaskRef::Drop` calls to the cross-queue. Nothing
    /// drains the cross-queue at this point in shutdown. `_slab_guard`
    /// then releases the slab backing storage. Any off-thread holder
    /// still pointing into the freed slab memory dereferences a
    /// dangling pointer. Do NOT modify the field declaration order
    /// without re-running miri tree-borrows on the full test suite AND
    /// the BUG-4 unwind regression tests.
    _cross_wake_tls_guard: crate::cross_wake::RuntimeCrossWakeGuard,

    /// IO driver (mio). Wrapped in `UnsafeCell` because a raw pointer
    /// is stored in TLS during `block_on`. Task futures access the IO
    /// driver through TLS (e.g., `TcpStream::poll_read`), while the
    /// run loop accesses it through `&mut self` (e.g., `poll_io()`).
    /// Without `UnsafeCell`, `&mut self` would invalidate the TLS
    /// pointer's provenance — see `Executor` docs for the full
    /// explanation.
    io: std::cell::UnsafeCell<IoDriver>,

    /// Timer driver. Same `UnsafeCell` rationale — `Sleep::poll` accesses
    /// through a stored raw pointer, `run_loop` accesses through `&mut self`.
    timers: std::cell::UnsafeCell<TimerDriver>,

    /// World access handle.
    ctx: WorldCtx,

    /// Event-cycle timestamp.
    event_time: Cell<Instant>,

    /// Graceful shutdown handle.
    shutdown: crate::ShutdownHandle,

    /// Cross-thread wake context. Shared with cross-thread wakers via Arc.
    /// Contains the intrusive MPSC inbox + mio::Waker for eventfd.
    cross_wake: std::sync::Arc<crate::cross_wake::CrossWakeContext>,

    /// Max cross-thread wakes drained per poll cycle.
    cross_thread_drain_limit: usize,

    /// Loop iterations between non-blocking IO polls.
    event_interval: u32,

    /// Slab allocator + TLS install. Owned via a single guard so that
    /// TLS dispatch stays valid for the Runtime's entire lifetime.
    ///
    /// **MUST drop AFTER `executor`**: when `Executor::drop` frees
    /// surviving slab tasks via TLS dispatch, the slab and its install
    /// must still be alive. Reordering re-introduces BUG-1 (#167) — a
    /// panic at `Runtime::drop` from surviving slab tasks calling into
    /// a cleared TLS dispatch path. The `const _: ()` block below this
    /// struct enforces the ordering at compile time.
    _slab_guard: Option<crate::alloc::SlabGuard>,

    /// Tracks Runtime presence on the thread. Installed at construction
    /// (panics if another Runtime is already alive), cleared on drop.
    /// Declared after `_slab_guard` so the "Runtime alive" flag stays
    /// set throughout the entire drop sequence — defensive against any
    /// inner Drop impl trying to construct another Runtime mid-teardown.
    _runtime_presence: RuntimePresenceGuard,

    /// Marker — `Runtime` is intrinsically thread-bound (per-thread TLS
    /// state). `*const ()` is `!Send + !Sync`; the `PhantomData`
    /// propagates that at the type level regardless of other field
    /// changes. See the `compile_fail` doc-tests on `Runtime`.
    _not_thread_safe: PhantomData<*const ()>,
}

// =============================================================================
// Runtime field ordering — invariants
// =============================================================================
//
// Field declaration order in `struct Runtime` is load-bearing. Each
// field has a position relative to others enforced by the requirements
// below. Rust's default layout doesn't guarantee declaration order,
// but `#[repr(C)]` + the `const _: ()` asserts below catch any
// reordering at compile time regardless of layout.
//
// Order (top → bottom = first → last drop):
//
//   executor              ← drops first; frees tasks
//   _cross_wake_tls_guard ← drops second; clears CURRENT_RUNTIME_CTX TLS
//   io                    ← UnsafeCell, no Drop concerns
//   timers                ← UnsafeCell, no Drop concerns
//   ctx                   ← WorldCtx, holds raw pointer to user's World
//   event_time            ← Cell<Instant>, trivial
//   shutdown              ← clone of ShutdownHandle, has Arc inside
//   cross_wake            ← Arc<CrossWakeContext>; off-thread holders may
//                           still exist; Arc keeps it alive past Runtime drop
//   cross_thread_drain_limit, event_interval ← trivial
//   _slab_guard           ← MUST drop AFTER executor (invariant 1)
//   _runtime_presence     ← MUST drop AFTER everything (invariant 3)
//   _not_thread_safe      ← PhantomData, no Drop
//
// Invariants:
//
// 1. `_slab_guard` after `executor`
//    Reason: BUG-1 (#167). When `Executor::drop` walks `all_tasks`
//    and encounters slab-allocated survivors, it dispatches their
//    `free_fn` through TLS. The TLS install lives on `_slab_guard`.
//    If `_slab_guard` drops first, slab tasks see the no-slab panic
//    stub.
//    Enforced: `const _:` offset assert below (added pre-PR-1a).
//
// 2. `_cross_wake_tls_guard` after `executor`
//    Reason: PR 1a. When `Executor::drop` walks `all_tasks` and
//    triggers `TaskRef::Drop`, the terminal-drop routing in
//    `dispose_terminal` reads `CURRENT_RUNTIME_CTX` to decide
//    on-thread (defer) vs off-thread (queue). If `_cross_wake_tls_guard`
//    drops first, the on-thread fast path silently misroutes terminal
//    frees to the cross-queue, where nothing drains them — leak,
//    OR for slab tasks, eventual UAF when `_slab_guard` releases
//    the slab backing storage.
//    FAILURE MODE: silent UAF in production for slab tasks.
//    Enforced: `const _:` offset assert below (added in PR 1a).
//
// 3. `_runtime_presence` after everything else
//    Reason: defensive. Some inner Drop impl might attempt to construct
//    another Runtime mid-teardown. With `_runtime_presence` dropping
//    last, the "Runtime alive" flag remains set, and that nested
//    construction panics rather than silently corrupting TLS.
//    Enforced: convention. No const_assert because there are too many
//    fields to assert against; relies on the doc-block + code review.
//
// 4. `cross_wake` outlives off-thread holders implicitly via Arc
//    Reason: cross-thread wakers (channel slots, tokio_compat) hold an
//    Arc<CrossWakeContext>. The Arc keeps the queue alive after Runtime
//    drops. When the LAST off-thread waker drops its Arc, the queue is
//    finally freed. Off-thread `dispose_terminal` calling
//    `try_set_queued + push` on a queue whose Runtime has been dropped
//    is safe: the queue is alive, we push to it, but no consumer
//    drains. The terminal task pointer leaks (memory, not UAF). PR 2
//    §2.3's `ShutdownStats` will surface this as a counter.
//
// Adding new fields:
// - Place trivial fields anywhere; non-trivial fields go to the
//   bottom of the appropriate group.
// - If your field has a Drop with cross-thread implications, document
//   the invariant here AND add an `offset_of` assert next to the
//   existing ones.
// - When in doubt, add to the bottom and document.

// BUG-1 (#167) invariant: `_slab_guard` MUST drop after `executor`.
// Field drop order is declaration order, and offset is a proxy: a
// later-declared field has a higher offset (modulo alignment padding,
// which preserves order). If anyone reorders the fields above, this
// fires at compile time.
const _: () = assert!(
    std::mem::offset_of!(Runtime, _slab_guard) > std::mem::offset_of!(Runtime, executor),
    "BUG-1 (#167) invariant violated: Runtime::_slab_guard MUST be \
     declared after Runtime::executor so it drops after the executor \
     frees surviving slab tasks. Restore the declaration order or BUG-1 \
     reappears as a panic at Runtime::drop."
);

// PR 1a (TaskRef + dispose_terminal) invariant: `_cross_wake_tls_guard`
// MUST drop after `executor`. The executor's drop path runs TaskRef::Drop
// for any cross-thread holder ref that lands during teardown; those
// drops route through `dispose_terminal` which checks
// `CURRENT_RUNTIME_CTX` to pick the on-thread (defer) vs off-thread
// (queue) branch. If this guard clears the TLS before `executor`
// finishes, the comparison silently fails and on-thread terminal frees
// get misrouted to the cross-queue (where nothing drains them — leak,
// or for slab tasks, eventual UAF when the slab backing storage drops
// behind `_slab_guard`).
const _: () = assert!(
    std::mem::offset_of!(Runtime, _cross_wake_tls_guard) > std::mem::offset_of!(Runtime, executor),
    "PR 1a invariant violated: Runtime::_cross_wake_tls_guard MUST be \
     declared after Runtime::executor so the runtime's CURRENT_RUNTIME_CTX \
     TLS stays installed while Executor::drop runs. Reordering \
     misroutes terminal TaskRef::Drop calls during teardown."
);

impl Runtime {
    /// Create a runtime with default settings. Box-allocated tasks only.
    ///
    /// For slab allocation or custom configuration, use [`Runtime::builder`].
    pub fn new(world: &mut nexus_rt::World) -> Self {
        RuntimeBuilder::new(world).build()
    }

    /// Create a runtime via the builder pattern.
    pub fn builder(world: &mut nexus_rt::World) -> RuntimeBuilder<'_> {
        RuntimeBuilder::new(world)
    }

    /// Returns a [`ShutdownHandle`](crate::ShutdownHandle) for triggering or observing shutdown.
    pub fn shutdown_handle(&self) -> crate::ShutdownHandle {
        self.shutdown.clone()
    }

    /// Install signal handlers for SIGTERM and SIGINT.
    pub fn install_signal_handlers(&self) {
        // SAFETY: single-threaded, called during setup before block_on.
        // UnsafeCell deref is safe because no TLS aliases exist yet.
        crate::shutdown::install_signal_handlers(
            &self.shutdown.flag_ptr(),
            &unsafe { &*self.io.get() }.mio_waker(),
        );
    }

    /// Number of live spawned tasks.
    pub fn task_count(&self) -> usize {
        self.executor.task_count()
    }

    /// Returns a handle to the abnormal-shutdown counter atomics.
    /// **Hold the handle past `drop(runtime)`** to inspect final
    /// values — the counters fire DURING `Executor::drop`, so a
    /// snapshot taken before drop will show all zeros for the
    /// shutdown-only counters.
    ///
    /// Useful as a signal — if any counter is non-zero, the shutdown
    /// hit a defensive path that should be investigated.
    ///
    /// ```ignore
    /// let stats_handle = runtime.shutdown_stats();
    /// drop(runtime);
    /// let stats = stats_handle.snapshot();
    /// if stats.aborted_unwinds != 0
    ///     || stats.leaked_box_tasks != 0
    ///     || stats.unbalanced_normal_shutdowns != 0
    ///     || stats.cross_queue_undrained != 0
    /// {
    ///     // user's own observability — log to wherever they want
    ///     my_logger::warn!("nexus runtime shutdown: {stats:?}");
    /// }
    /// ```
    ///
    /// Per PR 2's design (CALLOUT 5 of the plan), the runtime emits no
    /// log events of its own when these counters fire — users own
    /// their observability stack. The PR 1a `eprintln!` calls in the
    /// slab-unwinding-abort path remain (the only signal at the
    /// moment of process abort) but new abnormal paths added in PR 2
    /// are pure counter increments.
    ///
    /// # Counters
    ///
    /// See [`ShutdownStats`](crate::ShutdownStats) for what each
    /// counter signifies, and [`ShutdownStatsAtomics::snapshot`] for
    /// the read API on the returned handle.
    pub fn shutdown_stats(&self) -> std::sync::Arc<crate::ShutdownStatsAtomics> {
        self.executor.shutdown_stats()
    }
}

// =============================================================================
// RuntimeBuilder
// =============================================================================

/// Type-erased closure that boxes the slab and returns (ownership, TLS config).
type SlabInstaller = Box<dyn FnOnce() -> (Box<dyn std::any::Any>, crate::alloc::SlabTlsConfig)>;

/// Builder for configuring a [`Runtime`].
///
/// # Examples
///
/// ```ignore
/// use nexus_async_rt::*;
/// use nexus_slab::byte::unbounded::Slab;
///
/// let mut world = nexus_rt::WorldBuilder::new().build();
/// let slab = unsafe { Slab::<256>::with_chunk_capacity(64) };
///
/// let mut rt = Runtime::builder(&mut world)
///     .tasks_per_cycle(128)
///     .slab_unbounded(slab)
///     .signal_handlers(true)
///     .build();
/// ```
pub struct RuntimeBuilder<'w> {
    world: &'w mut nexus_rt::World,
    tasks_per_cycle: usize,
    cross_thread_drain_limit: usize,
    event_interval: u32,
    queue_capacity: usize,
    event_capacity: usize,
    token_capacity: usize,
    signal_handlers: bool,
    /// Type-erased slab + guard installer. None = no slab (Box-only).
    slab_installer: Option<SlabInstaller>,
}

impl<'w> RuntimeBuilder<'w> {
    fn new(world: &'w mut nexus_rt::World) -> Self {
        Self {
            world,
            tasks_per_cycle: crate::DEFAULT_TASKS_PER_CYCLE,
            cross_thread_drain_limit: usize::MAX,
            event_interval: DEFAULT_EVENT_INTERVAL,
            queue_capacity: 64,
            event_capacity: 1024,
            token_capacity: 64,
            signal_handlers: false,
            slab_installer: None,
        }
    }

    /// Maximum tasks polled per cycle before yielding to check IO.
    /// Default: 64.
    #[must_use]
    pub fn tasks_per_cycle(mut self, limit: usize) -> Self {
        self.tasks_per_cycle = limit;
        self
    }

    /// Number of loop iterations between non-blocking IO driver polls.
    /// Default: 61 (matches tokio's heuristic).
    ///
    /// Every `event_interval` iterations the runtime does a non-blocking
    /// `epoll_wait(0)` to check for socket events, even if tasks are
    /// ready. Lower values improve IO responsiveness at the cost of
    /// more syscalls; higher values favor task throughput.
    #[must_use]
    pub fn event_interval(mut self, n: u32) -> Self {
        assert!(n > 0, "event_interval must be > 0");
        self.event_interval = n;
        self
    }

    /// Maximum cross-thread wakes drained per poll cycle.
    /// Default: unlimited.
    ///
    /// Caps how many tasks woken from other threads are moved into the
    /// local ready queue per iteration. Prevents a firehose of
    /// cross-thread wakes from starving local tasks and IO. Remaining
    /// wakes are drained on the next iteration.
    #[must_use]
    pub fn cross_thread_drain_limit(mut self, limit: usize) -> Self {
        self.cross_thread_drain_limit = limit;
        self
    }

    /// Pre-allocated capacity for internal queues. Default: 64.
    #[must_use]
    pub fn queue_capacity(mut self, cap: usize) -> Self {
        self.queue_capacity = cap;
        self
    }

    /// Maximum IO events processed per epoll cycle. Default: 1024.
    #[must_use]
    pub fn event_capacity(mut self, cap: usize) -> Self {
        self.event_capacity = cap;
        self
    }

    /// Initial number of IO source slots. Default: 64.
    #[must_use]
    pub fn token_capacity(mut self, cap: usize) -> Self {
        self.token_capacity = cap;
        self
    }

    /// Install SIGTERM/SIGINT signal handlers. Default: false.
    #[must_use]
    pub fn signal_handlers(mut self, enable: bool) -> Self {
        self.signal_handlers = enable;
        self
    }

    /// Hand off a growable (unbounded) slab for [`spawn_slab`].
    ///
    /// `S` is the total slot size in bytes. The task header uses 72 bytes,
    /// so `Slab<256>` gives 184 bytes for the future. Most async IO
    /// futures are 128–256 bytes — `Slab<256>` or `Slab<512>` covers
    /// the common cases.
    ///
    /// The slab grows by allocating new chunks when full. No task spawn
    /// will ever fail due to capacity.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use nexus_slab::byte::unbounded::Slab;
    ///
    /// // SAFETY: single-threaded runtime.
    /// let slab = unsafe { Slab::<256>::with_chunk_capacity(64) };
    ///
    /// let mut rt = Runtime::builder(&mut world)
    ///     .slab_unbounded(slab)
    ///     .build();
    /// ```
    pub fn slab_unbounded<const S: usize>(
        mut self,
        slab: nexus_slab::byte::unbounded::Slab<S>,
    ) -> Self {
        const {
            assert!(
                S >= 72,
                "slab slot size must be at least 72 bytes (TASK_HEADER_SIZE)"
            );
        }
        self.slab_installer = Some(Box::new(move || {
            let mut slab = Box::new(slab);
            // Derive pointer via &mut to get write provenance. Using &ref
            // gives read-only provenance under stacked borrows, but the
            // allocator writes through this pointer.
            let slab_ptr = std::ptr::from_mut(slab.as_mut()).cast::<u8>();
            let config = crate::alloc::make_unbounded_config::<S>(slab_ptr);
            (slab as Box<dyn std::any::Any>, config)
        }));
        self
    }

    /// Hand off a fixed-capacity (bounded) slab for [`spawn_slab`].
    ///
    /// `S` is the total slot size in bytes. The slab has a fixed number
    /// of slots — `spawn_slab` panics if the slab is full. Use this
    /// when you want deterministic memory usage and know the maximum
    /// number of concurrent hot-path tasks.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use nexus_slab::byte::bounded::Slab;
    ///
    /// // SAFETY: single-threaded runtime.
    /// let slab = unsafe { Slab::<256>::with_capacity(64) };
    ///
    /// let mut rt = Runtime::builder(&mut world)
    ///     .slab_bounded(slab)
    ///     .build();
    /// ```
    pub fn slab_bounded<const S: usize>(
        mut self,
        slab: nexus_slab::byte::bounded::Slab<S>,
    ) -> Self {
        const {
            assert!(
                S >= 72,
                "slab slot size must be at least 72 bytes (TASK_HEADER_SIZE)"
            );
        }
        self.slab_installer = Some(Box::new(move || {
            let mut slab = Box::new(slab);
            // Derive pointer via &mut to get write provenance. Using &ref
            // gives read-only provenance under stacked borrows, but the
            // allocator writes through this pointer.
            let slab_ptr = std::ptr::from_mut(slab.as_mut()).cast::<u8>();
            let config = crate::alloc::make_bounded_config::<S>(slab_ptr);
            (slab as Box<dyn std::any::Any>, config)
        }));
        self
    }

    /// Build the runtime.
    pub fn build(self) -> Runtime {
        // Fail-fast if another Runtime is already alive on this thread.
        // Done before any resource allocation so we don't leak IoDriver,
        // mio::Poll, etc. on the panic path.
        let runtime_presence = RuntimePresenceGuard::install();

        let io = IoDriver::new(self.event_capacity, self.token_capacity)
            .expect("failed to create mio::Poll");
        let mut shutdown = crate::ShutdownHandle::new();
        shutdown.set_mio_waker(io.mio_waker());

        let mut executor = Executor::new(self.queue_capacity);
        executor.set_tasks_per_cycle(self.tasks_per_cycle);

        let ctx = WorldCtx::new(self.world);
        let event_time = Cell::new(Instant::now());

        // Create slab if configured and install TLS immediately. The
        // returned guard owns the slab and the TLS install; it lives
        // on Runtime so it drops AFTER `executor` (which frees surviving
        // slab tasks via TLS dispatch). This is the architectural fix
        // for BUG-1 (#167) — TLS scope now matches Runtime lifetime
        // instead of run_loop scope.
        let slab_guard = self.slab_installer.map(|install| {
            let (slab, config) = install();
            crate::alloc::install_slab(slab, &config)
        });

        let cross_wake = std::sync::Arc::new(crate::cross_wake::CrossWakeContext {
            queue: crate::cross_wake::CrossWakeQueue::new(),
            mio_waker: io.mio_waker(),
            parked: std::sync::atomic::AtomicBool::new(false),
        });

        // Wire the cross-wake context into the executor for the
        // shutdown-time `cross_queue_undrained` tally (PR 2 §2.3).
        // Bare Executor use in tests has no Runtime, no cross-wake
        // context, no tally — we install it here for the Runtime
        // path only.
        executor.install_cross_wake_for_drop(std::sync::Arc::clone(&cross_wake));

        // Install the runtime's cross-wake context as the current-thread
        // owning-executor identity. Lives lifetime-of-Runtime via the
        // guard field below — `dispose_terminal::on_owning_executor`
        // reads this slot to decide local-defer vs cross-queue routing
        // for TaskRef terminal drops.
        let cross_wake_tls_guard = crate::cross_wake::install_runtime_cross_wake(&cross_wake);

        let rt = Runtime {
            executor,
            _cross_wake_tls_guard: cross_wake_tls_guard,
            io: std::cell::UnsafeCell::new(io),
            timers: std::cell::UnsafeCell::new(TimerDriver::new(64)),
            ctx,
            event_time,
            shutdown,
            cross_wake,
            cross_thread_drain_limit: self.cross_thread_drain_limit,
            event_interval: self.event_interval,
            _slab_guard: slab_guard,
            _runtime_presence: runtime_presence,
            _not_thread_safe: PhantomData,
        };

        if self.signal_handlers {
            rt.install_signal_handlers();
        }

        rt
    }
}

// =============================================================================
// block_on / run_loop
// =============================================================================

impl Runtime {
    /// Drive the root future to completion. CPU-friendly.
    ///
    /// Parks the thread when no work is available.
    pub fn block_on<F>(&mut self, future: F) -> F::Output
    where
        F: Future + 'static,
    {
        self.run_loop(future, ParkMode::Park)
    }

    /// Drive the root future to completion. Busy-wait.
    ///
    /// Never parks. Minimum wake latency at 100% CPU.
    pub fn block_on_busy<F>(&mut self, future: F) -> F::Output
    where
        F: Future + 'static,
    {
        self.run_loop(future, ParkMode::Spin)
    }

    /// Drive the executor until pending cross-thread work has settled,
    /// before shutdown. The canonical "quiesce" step before
    /// `drop(runtime)` — see `docs/SHUTDOWN.md` for the full pattern.
    ///
    /// Loops while:
    /// 1. The cross-thread queue has entries (drains them).
    /// 2. The local ready queue has entries (polls them).
    ///
    /// Returns `Ok(())` once both are empty (or detected to no longer
    /// receive new entries). Returns `Err(QuiesceTimeout)` if `timeout`
    /// elapses first; the error contains diagnostic counts useful for
    /// determining which producer didn't release its refs.
    ///
    /// **This is for clean shutdown, not panic-during-shutdown.** The
    /// 100ms unwinding-wait in `Executor::drop` remains as
    /// defense-in-depth for the panic case (where this method can't
    /// be called).
    ///
    /// **The `timeout` parameter has no default — callers must pick a
    /// budget deliberately.** PR 2 §2.4 open-item 4 evaluated `100ms`
    /// (matches the unwinding defense), `500ms` (forgiving), and
    /// "parameter-only" — chose parameter-only to force the user to
    /// pick a budget appropriate for their producer landscape (a
    /// trading-system shutdown sequence with multiple Aeron drivers
    /// plus tokio futures plus channel senders has very different
    /// settling characteristics than a unit test).
    ///
    /// # Canonical shutdown sequence
    ///
    /// ```ignore
    /// // 1. Stop producers of cross-thread refs:
    /// //    - Drop tokio runtime (or shutdown_timeout)
    /// //    - Stop Aeron driver thread
    /// //    - Drop external channel senders
    ///
    /// // 2. Quiesce.
    /// runtime.shutdown_quiesce(Duration::from_millis(500))?;
    ///
    /// // 3. Drop the Runtime. Outstanding-ref panic paths in
    /// //    Executor::drop should be unreachable in normal operation.
    /// drop(runtime);
    /// ```
    ///
    /// If step 2 returns `QuiesceTimeout`, a producer hasn't released
    /// its refs. Investigate before letting Runtime drop — the
    /// unwind-abort path in `Executor::drop` is defensive, not
    /// desired.
    pub fn shutdown_quiesce(&mut self, timeout: Duration) -> Result<(), QuiesceTimeout> {
        // Install the same TLS context block_on uses, so any cross-thread
        // wakes that fire during quiesce still find a runtime.
        let _ctx_guard = crate::context::install(
            self.ctx.as_ptr(),
            self.io.get(),
            self.timers.get(),
            &raw const self.event_time,
            std::sync::Arc::as_ptr(&self.shutdown.flag_ptr()),
            std::ptr::from_ref(&self.shutdown.task_waker),
        );
        let _cross_wake_guard = crate::cross_wake::install_cross_wake(&self.cross_wake);
        let _spawn_guard = RuntimeGuard::enter(&raw mut self.executor);
        let (ready, deferred) = self.executor.poll_context_ptrs();
        let _ready_guard = crate::waker::set_poll_context(ready, deferred);

        let cross_queue = &*self.cross_wake;
        let start = Instant::now();

        loop {
            // Drain whatever's in the cross-thread queue. The returned
            // count tells us if anything was pending (a non-consuming
            // "is empty" check on the Vyukov queue would race the
            // producer; drain-and-count is the right primitive).
            let drained_this_pass = self
                .executor
                .drain_cross_thread(&cross_queue.queue, self.cross_thread_drain_limit);

            // Poll any ready tasks (drains the local ready queue).
            self.executor.poll();

            // Quiesced means: `all_tasks` is empty (no tasks with
            // outstanding refs — completed-but-held tasks would still
            // fire the abnormal-shutdown branches in `Executor::drop`),
            // no ready work pending, no cross-queue entries drained
            // THIS pass. Live or parked tasks that are still in
            // `all_tasks` count as not-quiesced — they're holding
            // refs that prevent a clean Runtime drop, even if they're
            // not making progress.
            //
            // Use `outstanding_tasks` (`all_tasks.len()`), NOT
            // `task_count` (`live_count`). `live_count` decrements
            // unconditionally on completion; `all_tasks` only loses an
            // entry when its refcount actually hits zero. A completed
            // task with a held `JoinHandle` has `live_count -= 1` but
            // is still in `all_tasks` — quiesce-as-Ok with
            // `task_count == 0` would mis-claim quiesced and the
            // user's subsequent drop would fire the
            // `unbalanced_normal_shutdowns` branch
            // (PR2-John-review item 2).
            let has_ready = self.executor.has_ready();
            let all_tasks_empty = self.executor.outstanding_tasks() == 0;
            if !has_ready && drained_this_pass == 0 && all_tasks_empty {
                return Ok(());
            }

            if start.elapsed() >= timeout {
                // Final drain to count what's left in the cross-queue
                // for the diagnostic. Anything after this drain is a
                // post-timeout race — not counted (and at this point
                // the user is about to investigate or drop).
                let remaining_cross_queue = self
                    .executor
                    .drain_cross_thread(&cross_queue.queue, usize::MAX)
                    as u64;
                return Err(QuiesceTimeout {
                    remaining_cross_queue,
                    remaining_outstanding_refs: self.executor.outstanding_tasks() as u64,
                    elapsed: start.elapsed(),
                });
            }

            // Avoid a tight spin on transient "queue popped a stub"
            // states. yield_now is a hint to the scheduler.
            std::thread::yield_now();
        }
    }

    fn run_loop<F>(&mut self, future: F, mode: ParkMode) -> F::Output
    where
        F: Future + 'static,
    {
        // Install TLS context.
        let _ctx_guard = crate::context::install(
            self.ctx.as_ptr(),
            self.io.get(),
            self.timers.get(),
            &raw const self.event_time,
            std::sync::Arc::as_ptr(&self.shutdown.flag_ptr()),
            std::ptr::from_ref(&self.shutdown.task_waker),
        );

        // Slab TLS is installed at Runtime construction (BUG-1 #167 fix)
        // and torn down when the Runtime drops — no longer scoped to
        // run_loop, so nothing to install here.

        // Install cross-thread wake context in TLS.
        let _cross_wake_guard = crate::cross_wake::install_cross_wake(&self.cross_wake);

        let mut root: Pin<Box<dyn Future<Output = F::Output>>> = Box::pin(future);

        let woken = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(true));
        let root_waker = Waker::from(std::sync::Arc::new(RootWake {
            woken: std::sync::Arc::clone(&woken),
            // SAFETY: single-threaded runtime; UnsafeCell deref is safe because
            // we have exclusive access during setup (TLS not yet installed).
            mio_waker: unsafe { &*self.io.get() }.mio_waker(),
        }));
        let mut root_cx = Context::from_waker(&root_waker);

        // Install spawn TLS.
        let _spawn_guard = RuntimeGuard::enter(&raw mut self.executor);

        // Install waker TLS: ready queue + deferred free list.
        // Uses UnsafeCell::get() to derive pointers that survive &mut self reborrows.
        let (ready, deferred) = self.executor.poll_context_ptrs();
        let _ready_guard = crate::waker::set_poll_context(ready, deferred);

        self.event_time.set(Instant::now());

        // The cross-thread queue uses interior mutability (UnsafeCell)
        // for the consumer head. pop() takes &self, so a shared ref
        // from the Arc is sufficient. No unsafe cast needed.
        let cross_queue = &*self.cross_wake;

        let mut tick: u32 = 0;

        loop {
            // 1. Poll root future if woken or shutdown requested.
            if woken.swap(false, std::sync::atomic::Ordering::Acquire)
                || self.shutdown.is_shutdown()
            {
                match root.as_mut().poll(&mut root_cx) {
                    Poll::Ready(output) => return output,
                    Poll::Pending => {}
                }
            }

            // 2. Drain cross-thread inbox.
            self.executor
                .drain_cross_thread(&cross_queue.queue, self.cross_thread_drain_limit);

            // 3. Poll ready tasks (up to tasks_per_cycle).
            self.executor.poll();

            // 4. Fire expired timers.
            // SAFETY: single-threaded runtime, no concurrent access.
            // UnsafeCell deref for interior mutability (TLS pointer aliasing).
            unsafe { &mut *self.timers.get() }.fire_expired(Instant::now());

            // 4.5. Set parked early (park mode only) so cross-thread
            // wakers arriving from here on will poke the eventfd.
            if matches!(mode, ParkMode::Park) {
                cross_queue
                    .parked
                    .store(true, std::sync::atomic::Ordering::Release);
            }

            // 5. Drain cross-thread inbox again (wakes during step 3/4).
            self.executor
                .drain_cross_thread(&cross_queue.queue, self.cross_thread_drain_limit);

            tick = tick.wrapping_add(1);

            // 6. Periodic non-blocking IO check every event_interval ticks.
            //    Prevents IO starvation under sustained task load.
            if tick.is_multiple_of(self.event_interval) {
                // SAFETY: single-threaded; UnsafeCell deref for interior mutability.
                if let Err(e) = unsafe { &mut *self.io.get() }.poll_io(Some(Duration::ZERO)) {
                    assert!(
                        e.kind() == std::io::ErrorKind::Interrupted,
                        "mio::Poll::poll failed: {e}"
                    );
                }
                self.event_time.set(Instant::now());
            }

            // 7. If work remains, loop immediately.
            let has_work =
                self.executor.has_ready() || woken.load(std::sync::atomic::Ordering::Acquire);

            if has_work {
                if matches!(mode, ParkMode::Park) {
                    cross_queue
                        .parked
                        .store(false, std::sync::atomic::Ordering::Release);
                }
                continue;
            }

            // 8. No work. Spin mode loops; park mode sleeps in epoll.
            match mode {
                ParkMode::Spin => {
                    // Non-blocking IO check before spinning again.
                    // SAFETY: single-threaded; UnsafeCell deref for interior mutability.
                    if let Err(e) = unsafe { &mut *self.io.get() }.poll_io(Some(Duration::ZERO)) {
                        assert!(
                            e.kind() == std::io::ErrorKind::Interrupted,
                            "mio::Poll::poll failed: {e}"
                        );
                    }
                    self.event_time.set(Instant::now());
                }
                ParkMode::Park => {
                    // parked is already true (set at step 4.5).
                    // Park in epoll_wait until IO, timer, or cross-thread
                    // eventfd wakes us.
                    // SAFETY: single-threaded, no concurrent timer access.
                    // UnsafeCell deref for interior mutability (shared ref for read).
                    let timeout = unsafe { &*self.timers.get() }
                        .next_deadline()
                        .map(|d| d.saturating_duration_since(Instant::now()));

                    // SAFETY: single-threaded; UnsafeCell deref for interior mutability.
                    if let Err(e) = unsafe { &mut *self.io.get() }.poll_io(timeout) {
                        assert!(
                            e.kind() == std::io::ErrorKind::Interrupted,
                            "mio::Poll::poll failed: {e}"
                        );
                    }

                    cross_queue
                        .parked
                        .store(false, std::sync::atomic::Ordering::Release);
                    self.event_time.set(Instant::now());
                }
            }
        }
    }
}

// =============================================================================
// QuiesceTimeout — error type for `Runtime::shutdown_quiesce`
// =============================================================================

/// Returned by [`Runtime::shutdown_quiesce`] when the timeout elapses
/// before the executor reaches a quiesced state.
///
/// The diagnostic fields help identify which producer didn't release
/// its refs:
///
/// - `remaining_cross_queue`: number of cross-thread queue entries
///   still pending at the moment of timeout. Non-zero indicates a
///   producer thread is still pushing wakes faster than quiesce can
///   drain them, OR a final-drain wake landed after the last drain
///   pass — investigate which off-thread producer is still active.
/// - `remaining_outstanding_refs`: number of tasks still in
///   `Executor::all_tasks` at the moment of timeout. Each represents a
///   task with outstanding cross-thread refs (or a held JoinHandle).
/// - `elapsed`: how long quiesce ran before timing out.
///
/// PR 2 §2.4 open-item 5 noted that finer-grained diagnostics
/// ("which task ID had the outstanding ref") could be added if
/// implementation revealed them as cheap to surface. The implementation
/// uses `Executor::task_count()` which doesn't enumerate tasks; adding
/// per-task data here would require new accessors. Out of scope for
/// initial PR 2; future enhancement.
#[derive(Debug)]
pub struct QuiesceTimeout {
    /// Number of cross-thread queue entries still pending at timeout.
    /// Non-zero means a producer is racing the drain loop.
    pub remaining_cross_queue: u64,
    /// Number of tasks still alive at the moment of timeout. Each is
    /// a candidate for "producer hasn't released its refs."
    pub remaining_outstanding_refs: u64,
    /// Time elapsed inside `shutdown_quiesce` before returning timeout.
    /// Approximately equal to the input `timeout`.
    pub elapsed: Duration,
}

impl std::fmt::Display for QuiesceTimeout {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Runtime::shutdown_quiesce timed out after {:?} with {} outstanding tasks, \
             {} cross-queue entries pending",
            self.elapsed, self.remaining_outstanding_refs, self.remaining_cross_queue
        )
    }
}

impl std::error::Error for QuiesceTimeout {}

// =============================================================================
// Park mode
// =============================================================================

#[derive(Clone, Copy)]
enum ParkMode {
    Park,
    Spin,
}

// =============================================================================
// Root future waker
// =============================================================================

struct RootWake {
    woken: std::sync::Arc<std::sync::atomic::AtomicBool>,
    mio_waker: std::sync::Arc<mio::Waker>,
}

impl Wake for RootWake {
    fn wake(self: std::sync::Arc<Self>) {
        self.wake_by_ref();
    }

    fn wake_by_ref(self: &std::sync::Arc<Self>) {
        let was_woken = self.woken.swap(true, std::sync::atomic::Ordering::Release);
        if !was_woken {
            let _ = self.mio_waker.wake();
        }
    }
}

// =============================================================================
// RAII guard for spawn TLS
// =============================================================================

struct RuntimeGuard {
    prev: *mut Executor,
}

impl RuntimeGuard {
    fn enter(executor: *mut Executor) -> Self {
        let prev = CURRENT.with(|cell| cell.replace(executor));
        Self { prev }
    }
}

impl Drop for RuntimeGuard {
    fn drop(&mut self) {
        CURRENT.with(|cell| cell.set(self.prev));
    }
}

// =============================================================================
// RAII guard for Runtime presence on this thread
// =============================================================================
//
// Enforces "at most one Runtime alive per thread" at construction time. This
// is the right scope because:
//
//  - Slab TLS is installed at construction (post BUG-1 fix). A second
//    construction would silently overwrite the first's slab dispatch state,
//    corrupting allocator routing for the first Runtime's surviving tasks.
//  - !Send + !Sync prevents cross-thread coexistence at the type level.
//    This guard prevents same-thread coexistence at runtime.
//
// Different from `RuntimeGuard` above: that one is per-`block_on` for spawn
// TLS, this one is per-Runtime for existence tracking.

thread_local! {
    static RUNTIME_PRESENT: Cell<bool> = const { Cell::new(false) };
}

pub(crate) struct RuntimePresenceGuard;

impl RuntimePresenceGuard {
    /// Install the Runtime-presence flag. Panics if another Runtime is
    /// already alive on this thread.
    fn install() -> Self {
        assert!(
            !RUNTIME_PRESENT.with(Cell::get),
            "nexus-async-rt: another Runtime is already alive on this \
             thread. Only one Runtime is supported per thread because \
             thread-local state (slab dispatch, IO/timer drivers, \
             cross-thread wake context) cannot be shared between \
             Runtimes. Drop the existing Runtime first."
        );
        RUNTIME_PRESENT.with(|c| c.set(true));
        Self
    }
}

impl Drop for RuntimePresenceGuard {
    fn drop(&mut self) {
        RUNTIME_PRESENT.with(|c| c.set(false));
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
    use nexus_rt::{Handler, IntoHandler, Res, ResMut, WorldBuilder};

    nexus_rt::new_resource!(Val(u64));
    nexus_rt::new_resource!(Out(u64));

    #[test]
    fn block_on_returns_value() {
        let mut wb = WorldBuilder::new();
        wb.register(Val(42));
        let mut world = wb.build();

        let mut rt = Runtime::new(&mut world);
        let result = rt.block_on(async { 42u64 });
        assert_eq!(result, 42);
    }

    #[test]
    fn block_on_with_world_access() {
        let mut wb = WorldBuilder::new();
        wb.register(Val(42));
        wb.register(Out(0));
        let mut world = wb.build();

        let mut rt = Runtime::new(&mut world);

        let result = rt.block_on(async move {
            crate::WorldCtx::current().with_world(|world| {
                let v = world.resource::<Val>().0;
                world.resource_mut::<Out>().0 = v + 10;
            });
            crate::WorldCtx::current().with_world_ref(|world| world.resource::<Out>().0)
        });

        assert_eq!(result, 52);
    }

    #[test]
    fn block_on_with_pre_resolved_handler() {
        let mut wb = WorldBuilder::new();
        wb.register(Val(42));
        wb.register(Out(0));
        let mut world = wb.build();

        let mut rt = Runtime::new(&mut world);

        let mut h = (|val: Res<Val>, mut out: ResMut<Out>, event: u64| {
            out.0 = val.0 + event;
        })
        .into_handler(world.registry());

        let result = rt.block_on(async move {
            crate::WorldCtx::current().with_world(|world| h.run(world, 10));
            crate::WorldCtx::current().with_world_ref(|world| world.resource::<Out>().0)
        });

        assert_eq!(result, 52);
    }

    #[test]
    fn spawn_from_root_future() {
        let mut wb = WorldBuilder::new();
        wb.register(Out(0));
        let mut world = wb.build();

        let mut rt = Runtime::new(&mut world);

        rt.block_on(async move {
            for i in 1..=3u64 {
                spawn_boxed(async move {
                    crate::WorldCtx::current().with_world(|world| {
                        world.resource_mut::<Out>().0 += i;
                    });
                });
            }

            YieldOnce(false).await;
        });

        assert_eq!(world.resource::<Out>().0, 6);
    }

    #[test]
    fn block_on_busy_returns_value() {
        let mut wb = WorldBuilder::new();
        wb.register(Val(7));
        let mut world = wb.build();

        let mut rt = Runtime::new(&mut world);
        let result = rt.block_on_busy(async { 6 * 7 });
        assert_eq!(result, 42);
    }

    #[test]
    fn block_on_busy_with_spawned_tasks() {
        let mut wb = WorldBuilder::new();
        wb.register(Out(0));
        let mut world = wb.build();

        let mut rt = Runtime::new(&mut world);

        rt.block_on_busy(async move {
            spawn_boxed(async move {
                crate::WorldCtx::current().with_world(|world| {
                    world.resource_mut::<Out>().0 = 99;
                });
            });

            YieldOnce(false).await;
        });

        assert_eq!(world.resource::<Out>().0, 99);
    }

    #[test]
    fn event_time_is_set() {
        let mut wb = WorldBuilder::new();
        wb.register(Val(0));
        let mut world = wb.build();

        let mut rt = Runtime::new(&mut world);

        let before = Instant::now();
        rt.block_on(async move {
            let t = crate::context::event_time();
            assert!(t >= before);
        });
    }

    #[test]
    #[should_panic(expected = "spawn_boxed() called outside of Runtime::block_on")]
    fn spawn_outside_runtime_panics() {
        spawn_boxed(async {});
    }

    fn test_slab() -> nexus_slab::byte::unbounded::Slab<256> {
        // SAFETY: single-threaded test.
        unsafe { nexus_slab::byte::unbounded::Slab::with_chunk_capacity(16) }
    }

    #[test]
    #[should_panic(expected = "spawn_slab() called without a slab")]
    fn spawn_slab_without_slab_panics() {
        let wb = WorldBuilder::new();
        let mut world = wb.build();
        let mut rt = Runtime::new(&mut world);

        rt.block_on(async {
            spawn_slab(async {});
        });
    }

    #[test]
    fn spawn_slab_with_slab() {
        let mut wb = WorldBuilder::new();
        wb.register(Out(0));
        let mut world = wb.build();

        let mut rt = Runtime::builder(&mut world)
            .slab_unbounded(test_slab())
            .build();

        rt.block_on(async move {
            spawn_slab(async move {
                crate::WorldCtx::current().with_world(|world| {
                    world.resource_mut::<Out>().0 = 77;
                });
            });

            YieldOnce(false).await;
        });

        assert_eq!(world.resource::<Out>().0, 77);
    }

    #[test]
    fn mixed_spawn_and_spawn_slab() {
        let mut wb = WorldBuilder::new();
        wb.register(Out(0));
        let mut world = wb.build();

        let mut rt = Runtime::builder(&mut world)
            .slab_unbounded(test_slab())
            .build();

        rt.block_on(async move {
            // Box-allocated
            spawn_boxed(async move {
                crate::WorldCtx::current().with_world(|world| {
                    world.resource_mut::<Out>().0 += 10;
                });
            });
            // Slab-allocated
            spawn_slab(async move {
                crate::WorldCtx::current().with_world(|world| {
                    world.resource_mut::<Out>().0 += 20;
                });
            });

            YieldOnce(false).await;
        });

        assert_eq!(world.resource::<Out>().0, 30);
    }

    // =========================================================================
    // Claim API tests
    // =========================================================================

    #[test]
    fn claim_slab_spawn_executes() {
        let mut wb = WorldBuilder::new();
        wb.register(Out(0));
        let mut world = wb.build();

        let mut rt = Runtime::builder(&mut world)
            .slab_unbounded(test_slab())
            .build();

        rt.block_on(async move {
            let claim = claim_slab();
            claim.spawn(async move {
                crate::WorldCtx::current().with_world(|world| {
                    world.resource_mut::<Out>().0 = 55;
                });
            });

            YieldOnce(false).await;
        });

        assert_eq!(world.resource::<Out>().0, 55);
    }

    #[test]
    fn claim_slab_drop_returns_slot() {
        let wb = WorldBuilder::new();
        let mut world = wb.build();

        // SAFETY: capacity 1 is a valid non-zero capacity for the bounded slab allocator.
        let bounded = unsafe { nexus_slab::byte::bounded::Slab::<256>::with_capacity(1) };
        let mut rt = Runtime::builder(&mut world).slab_bounded(bounded).build();

        rt.block_on(async {
            // Claim the only slot, then drop without spawning.
            let claim = claim_slab();
            drop(claim);

            // Slot should be back — can claim again.
            let claim = claim_slab();
            claim.spawn(async {});

            YieldOnce(false).await;
        });
    }

    #[test]
    fn try_claim_slab_returns_none_when_full() {
        let wb = WorldBuilder::new();
        let mut world = wb.build();

        // SAFETY: capacity 1 is a valid non-zero capacity for the bounded slab allocator.
        let bounded = unsafe { nexus_slab::byte::bounded::Slab::<256>::with_capacity(1) };
        let mut rt = Runtime::builder(&mut world).slab_bounded(bounded).build();

        rt.block_on(async {
            let _held = claim_slab(); // hold the only slot
            assert!(try_claim_slab().is_none());
        });
    }

    #[test]
    fn mixed_spawn_boxed_and_claim_slab() {
        let mut wb = WorldBuilder::new();
        wb.register(Out(0));
        let mut world = wb.build();

        let mut rt = Runtime::builder(&mut world)
            .slab_unbounded(test_slab())
            .build();

        rt.block_on(async move {
            spawn_boxed(async move {
                crate::WorldCtx::current().with_world(|world| {
                    world.resource_mut::<Out>().0 += 10;
                });
            });

            let claim = claim_slab();
            claim.spawn(async move {
                crate::WorldCtx::current().with_world(|world| {
                    world.resource_mut::<Out>().0 += 20;
                });
            });

            YieldOnce(false).await;
        });

        assert_eq!(world.resource::<Out>().0, 30);
    }

    // =========================================================================
    // Timer tests
    // =========================================================================

    #[test]
    fn sleep_completes() {
        let mut wb = WorldBuilder::new();
        wb.register(Out(0));
        let mut world = wb.build();

        let mut rt = Runtime::new(&mut world);

        let before = Instant::now();
        rt.block_on(async move {
            crate::context::sleep(Duration::from_millis(50)).await;
        });
        let elapsed = before.elapsed();

        assert!(
            elapsed >= Duration::from_millis(40),
            "elapsed {elapsed:?} too short"
        );
        assert!(
            elapsed < Duration::from_millis(200),
            "elapsed {elapsed:?} too long"
        );
    }

    #[test]
    fn sleep_in_spawned_task() {
        let mut wb = WorldBuilder::new();
        wb.register(Out(0));
        let mut world = wb.build();

        let mut rt = Runtime::new(&mut world);

        let before = Instant::now();
        rt.block_on(async move {
            spawn_boxed(async move {
                crate::context::sleep(Duration::from_millis(50)).await;
                crate::WorldCtx::current().with_world(|world| {
                    world.resource_mut::<Out>().0 = 42;
                });
            });

            crate::context::sleep(Duration::from_millis(100)).await;
        });

        let elapsed = before.elapsed();
        assert!(elapsed >= Duration::from_millis(80));
        assert_eq!(world.resource::<Out>().0, 42);
    }

    #[test]
    fn sleep_zero_duration_ready_immediately() {
        let wb = WorldBuilder::new();
        let mut world = wb.build();
        let mut rt = Runtime::new(&mut world);

        let before = Instant::now();
        rt.block_on(async move {
            crate::context::sleep(Duration::ZERO).await;
        });
        assert!(before.elapsed() < Duration::from_millis(10));
    }

    #[test]
    fn sleep_past_deadline_ready_immediately() {
        let wb = WorldBuilder::new();
        let mut world = wb.build();
        let mut rt = Runtime::new(&mut world);

        let past = Instant::now().checked_sub(Duration::from_secs(1)).unwrap();
        let before = Instant::now();
        rt.block_on(async move {
            crate::context::sleep_until(past).await;
        });
        assert!(before.elapsed() < Duration::from_millis(10));
    }

    // =========================================================================
    // Timeout tests
    // =========================================================================

    #[test]
    fn timeout_completes_before_deadline() {
        let wb = WorldBuilder::new();
        let mut world = wb.build();
        let mut rt = Runtime::new(&mut world);

        let result = rt.block_on(async {
            crate::context::timeout(Duration::from_millis(500), async { 42u64 }).await
        });

        assert_eq!(result.unwrap(), 42);
    }

    #[test]
    fn timeout_expires() {
        let wb = WorldBuilder::new();
        let mut world = wb.build();
        let mut rt = Runtime::new(&mut world);

        let result = rt.block_on(async {
            crate::context::timeout(
                Duration::from_millis(10),
                crate::context::sleep(Duration::from_secs(10)),
            )
            .await
        });

        assert!(result.is_err());
    }

    // =========================================================================
    // Interval tests
    // =========================================================================

    #[test]
    fn interval_ticks() {
        let mut wb = WorldBuilder::new();
        wb.register(Out(0));
        let mut world = wb.build();
        let mut rt = Runtime::new(&mut world);

        let before = Instant::now();
        rt.block_on(async move {
            let mut iv = crate::context::interval(Duration::from_millis(20));
            iv.tick().await; // ~20ms
            iv.tick().await; // ~40ms
            iv.tick().await; // ~60ms
        });
        let elapsed = before.elapsed();

        assert!(
            elapsed >= Duration::from_millis(50),
            "too fast: {elapsed:?}"
        );
        assert!(
            elapsed < Duration::from_millis(200),
            "too slow: {elapsed:?}"
        );
    }

    // =========================================================================
    // yield_now tests
    // =========================================================================

    #[test]
    fn yield_now_lets_other_tasks_run() {
        let mut wb = WorldBuilder::new();
        wb.register(Out(0));
        let mut world = wb.build();
        let mut rt = Runtime::new(&mut world);

        rt.block_on(async move {
            spawn_boxed(async move {
                crate::WorldCtx::current().with_world(|world| {
                    world.resource_mut::<Out>().0 = 99;
                });
            });

            // Yield so the spawned task gets a turn.
            crate::context::yield_now().await;

            let val = crate::WorldCtx::current().with_world_ref(|world| world.resource::<Out>().0);
            assert_eq!(val, 99);
        });
    }

    // =========================================================================
    // Test helpers
    // =========================================================================

    struct YieldOnce(bool);

    impl Future for YieldOnce {
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

    // =========================================================================
    // JoinHandle tests
    // =========================================================================

    #[test]
    fn join_handle_await_gets_value() {
        let wb = WorldBuilder::new();
        let mut world = wb.build();
        let mut rt = Runtime::new(&mut world);

        rt.block_on(async {
            let handle = spawn_boxed(async { 42u64 });
            let result = handle.await;
            assert_eq!(result, 42);
        });
    }

    #[test]
    fn join_handle_await_string() {
        let wb = WorldBuilder::new();
        let mut world = wb.build();
        let mut rt = Runtime::new(&mut world);

        rt.block_on(async {
            let handle = spawn_boxed(async { String::from("hello world") });
            let result = handle.await;
            assert_eq!(result, "hello world");
        });
    }

    #[test]
    fn join_handle_detach() {
        use std::cell::Cell;
        use std::rc::Rc;

        let wb = WorldBuilder::new();
        let mut world = wb.build();
        let mut rt = Runtime::new(&mut world);

        let ran = Rc::new(Cell::new(false));
        let r = ran.clone();

        rt.block_on(async move {
            // Spawn and immediately drop handle (detach).
            drop(spawn_boxed(async move {
                r.set(true);
            }));
            // Yield to let the spawned task run.
            crate::context::yield_now().await;
        });

        assert!(ran.get());
    }

    #[test]
    fn join_handle_is_finished() {
        let wb = WorldBuilder::new();
        let mut world = wb.build();
        let mut rt = Runtime::new(&mut world);

        rt.block_on(async {
            let handle = spawn_boxed(async { 1 });
            // The task hasn't been polled yet.
            assert!(!handle.is_finished());
            // Yield to let the task run.
            crate::context::yield_now().await;
            assert!(handle.is_finished());
            let val = handle.await;
            assert_eq!(val, 1);
        });
    }

    #[test]
    fn join_handle_abort_returns_true() {
        let wb = WorldBuilder::new();
        let mut world = wb.build();
        let mut rt = Runtime::new(&mut world);

        rt.block_on(async {
            let handle = spawn_boxed(std::future::pending::<()>());
            assert!(handle.abort()); // was running, handle consumed
        });
    }

    #[test]
    fn join_handle_abort_completed_returns_false() {
        let wb = WorldBuilder::new();
        let mut world = wb.build();
        let mut rt = Runtime::new(&mut world);

        rt.block_on(async {
            let handle = spawn_boxed(async { 42 });
            crate::context::yield_now().await;
            assert!(handle.is_finished());
            assert!(!handle.abort()); // already done, handle consumed
        });
    }

    #[test]
    fn join_handle_drop_after_completion_drops_output() {
        use std::cell::Cell;
        use std::rc::Rc;

        let wb = WorldBuilder::new();
        let mut world = wb.build();
        let mut rt = Runtime::new(&mut world);

        let drop_count = Rc::new(Cell::new(0u32));
        let dc = drop_count.clone();

        struct DropCounter(Rc<Cell<u32>>);
        impl Drop for DropCounter {
            fn drop(&mut self) {
                self.0.set(self.0.get() + 1);
            }
        }

        rt.block_on(async move {
            let handle = spawn_boxed(async move { DropCounter(dc) });
            // Let it complete.
            crate::context::yield_now().await;
            assert!(handle.is_finished());
            // Drop handle without reading — output should be dropped.
            drop(handle);
        });

        assert_eq!(drop_count.get(), 1, "output should be dropped exactly once");
    }

    #[test]
    fn join_handle_multiple_concurrent() {
        let wb = WorldBuilder::new();
        let mut world = wb.build();
        let mut rt = Runtime::new(&mut world);

        rt.block_on(async {
            let h1 = spawn_boxed(async { 10u64 });
            let h2 = spawn_boxed(async { 20u64 });
            let h3 = spawn_boxed(async { 30u64 });

            let r3 = h3.await;
            let r1 = h1.await;
            let r2 = h2.await;

            assert_eq!(r1, 10);
            assert_eq!(r2, 20);
            assert_eq!(r3, 30);
        });
    }

    #[test]
    fn join_handle_output_larger_than_future() {
        let wb = WorldBuilder::new();
        let mut world = wb.build();
        let mut rt = Runtime::new(&mut world);

        rt.block_on(async {
            // The future is tiny, the output is large.
            let handle = spawn_boxed(async { [42u64; 32] });
            let result = handle.await;
            assert_eq!(result[0], 42);
            assert_eq!(result[31], 42);
        });
    }
}
