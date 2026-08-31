//! Tokio compatibility layer.
//!
//! Allows polling tokio-based futures from the nexus-async-rt executor.
//! Tokio's background reactor watches file descriptors; our executor
//! owns and polls the futures. Cross-thread wakers bridge the gap.
//!
//! A lazy tokio runtime (single worker thread) is created on first use.
//!
//! # Two modes
//!
//! **`with_tokio(|| future_expr)`** — poll a tokio future on our executor.
//! Tokio provides the reactor (epoll) and timers; our executor polls the
//! future. Tokio never polls it — it just fires wakers.
//!
//! **`spawn_on_tokio(future)`** — run a future on tokio's thread pool.
//! The future is scheduled and polled by tokio. The result is delivered
//! back to our executor via the cross-thread waker bridge. Use this for
//! cold-path I/O (reqwest, database drivers, AWS SDK) that needs the
//! full tokio ecosystem.
//!
//! # How `with_tokio` works
//!
//! 1. `with_tokio(|| future_expr)` installs tokio's runtime context on
//!    the current thread via `Handle::enter()`. The closure runs with
//!    tokio context available so tokio types can be constructed.
//! 2. When polled, the tokio future registers its fds with tokio's
//!    reactor and stores a waker.
//! 3. That waker is our cross-thread waker — it pushes to the
//!    intrusive inbox + conditionally pokes the eventfd.
//! 4. When tokio's reactor detects IO readiness, it fires our waker.
//! 5. Our executor wakes up, re-polls the task, the future reads data.
//!
//! # Performance
//!
//! The waker bridge adds ~76ns per waker hop (measured with tokio
//! oneshot channel, pinned to separate physical cores):
//!
//! | Percentile | Busy spin | Park mode |
//! |-----------|-----------|-----------|
//! | p50       | 76 ns     | 75 ns     |
//! | p90       | 89 ns     | 92 ns     |
//! | p99       | 110 ns    | 117 ns    |
//! | p99.9     | 299 ns    | 2.0 µs   |
//!
//! TCP echo loopback (write + read, two bridge hops): ~8µs p50.
//!
//! # Usage
//!
//! ```ignore
//! use nexus_async_rt::tokio_compat::with_tokio;
//!
//! rt.block_on(async {
//!     // Single operation:
//!     let stream = with_tokio(|| TcpStream::connect(addr)).await?;
//!
//!     // Multiple awaits in one block:
//!     let data = with_tokio(|| async {
//!         let mut stream = TcpStream::connect(addr).await?;
//!         stream.write_all(b"hello").await?;
//!         let mut buf = [0u8; 64];
//!         let n = stream.read(&mut buf).await?;
//!         Ok::<_, io::Error>(buf[..n].to_vec())
//!     }).await?;
//!
//!     // Tokio ecosystem crates (e.g., databento):
//!     let client = with_tokio(|| databento::LiveClient::connect(key)).await?;
//!     loop {
//!         let record = with_tokio(|| client.next_record()).await?;
//!         process(record);  // runs on our executor, no wrapper needed
//!     }
//! });
//! ```

use std::future::Future;
use std::pin::Pin;
use std::sync::OnceLock;
use std::task::{Context, Poll, Waker};

/// Global lazy tokio runtime. Single worker thread for the IO reactor.
static TOKIO_RT: OnceLock<tokio::runtime::Runtime> = OnceLock::new();

fn tokio_runtime() -> &'static tokio::runtime::Runtime {
    TOKIO_RT.get_or_init(|| {
        tokio::runtime::Builder::new_multi_thread()
            .worker_threads(1)
            .enable_io()
            .enable_time()
            .build()
            .expect("failed to create tokio compatibility runtime")
    })
}

// Thread-local flag: tokio context installed on this thread.
// Set once, shared across all `with_tokio` calls. Avoids the
// "guards dropped out of order" panic from nested EnterGuards.
thread_local! {
    static TOKIO_ENTERED: Cell<bool> = const { Cell::new(false) };
}

use std::cell::Cell;

fn ensure_tokio_context() {
    TOKIO_ENTERED.with(|entered| {
        if !entered.get() {
            // Leak the guard — it lives for the thread's lifetime.
            // This is fine: the tokio runtime is 'static, and the
            // guard just sets TLS on this thread.
            std::mem::forget(tokio_runtime().enter());
            entered.set(true);
        }
    });
}

/// Run a closure with tokio context installed, returning a future
/// that can be polled from nexus-async-rt.
///
/// The closure runs immediately with tokio's runtime context available,
/// so tokio types can be constructed (e.g., `tokio::time::sleep()`).
/// The returned future is then polled by our executor with cross-thread
/// wakers bridging tokio's reactor back to us.
///
/// The returned [`TokioCompat`] future must be polled from within
/// [`Runtime::block_on`](crate::Runtime::block_on). If polled without
/// the runtime's cross-wake context installed, it will panic when
/// a local runtime waker is used.
pub fn with_tokio<F, Fut>(f: F) -> TokioCompat<Fut>
where
    F: FnOnce() -> Fut,
    Fut: Future,
{
    ensure_tokio_context();
    let future = f();
    TokioCompat { future }
}

/// Future wrapper that polls an inner future with tokio context installed.
///
/// Created by [`with_tokio()`].
pub struct TokioCompat<F> {
    future: F,
}

impl<F: Future> Future for TokioCompat<F> {
    type Output = F::Output;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // SAFETY: structural pin projection to `future`. We never move
        // `future` out of the struct.
        let this = unsafe { self.get_unchecked_mut() };

        // Build a cross-thread waker for this task.
        let cross_waker = make_cross_waker(cx);
        let mut cross_cx = Context::from_waker(&cross_waker);

        // Poll the inner future with cross-thread waker.
        // Tokio context installed via TLS (ensure_tokio_context).
        // SAFETY: `this.future` is structurally pinned — self is pinned
        // and we never move future out.
        let future = unsafe { Pin::new_unchecked(&mut this.future) };
        future.poll(&mut cross_cx)
    }
}

/// Build a cross-thread waker from the current context.
///
/// If the waker is our local runtime waker, extract the task pointer
/// and build a cross-thread waker. If it's already cross-thread safe
/// (e.g., root future waker), clone it directly.
fn make_cross_waker(cx: &Context<'_>) -> Waker {
    crate::waker::task_ptr_from_local_waker(cx.waker()).map_or_else(
        || cx.waker().clone(),
        |task_ptr| {
            let ctx = crate::cross_wake::cross_wake_context()
                .expect("with_tokio() requires runtime context");
            make_cross_task_waker(task_ptr, ctx)
        },
    )
}

/// Cross-thread waker inner. Arc-allocated, shared across all
/// `Waker::clone`s. `RawWaker::data` is `Arc::into_raw(Arc<Self>)`.
///
/// Uses a custom vtable (not the `Wake` trait) so that the clone path
/// is `Arc::clone` (one atomic increment) instead of allocating a fresh
/// per-clone struct. Tokio clones wakers freely (e.g. on every IO
/// register); per-clone malloc was the hot-path cost PR 2 §2.1
/// eliminated.
///
/// **Field order matters.** `task_ref` is declared BEFORE `ctx` so it
/// drops first. When the last `Arc` drops, `Inner::drop` runs the
/// fields in declaration order: `task_ref` first → `TaskRef::Drop` →
/// `ref_dec` → if terminal, `dispose_terminal` reads the
/// `CrossWakeContext` pointer from the task header (heap-allocated,
/// kept alive transitively by our still-alive `ctx: Arc<...>`). Then
/// `ctx` drops, decrementing the `CrossWakeContext` Arc's refcount.
struct CrossTaskWakerInner {
    /// Drops FIRST. See the type doc-comment for why.
    task_ref: crate::task::TaskRef,
    /// Drops SECOND. Keeps `CrossWakeContext` alive while `task_ref`
    /// drops, so `dispose_terminal` can read the ctx pointer from the
    /// task header without it dangling.
    ctx: std::sync::Arc<crate::cross_wake::CrossWakeContext>,
}

// SAFETY: TaskRef is Send (see task.rs). Arc<CrossWakeContext> is Send
// + Sync. Sync is required because tokio's RawWaker passes &Self to
// `wake_by_ref` and may share clones across threads.
unsafe impl Send for CrossTaskWakerInner {}
unsafe impl Sync for CrossTaskWakerInner {}

use std::task::RawWaker;
use std::task::RawWakerVTable;

static CROSS_TASK_VTABLE: RawWakerVTable = RawWakerVTable::new(
    cross_task_clone,
    cross_task_wake,
    cross_task_wake_by_ref,
    cross_task_drop,
);

fn make_cross_task_waker(
    task_ptr: *mut u8,
    ctx: std::sync::Arc<crate::cross_wake::CrossWakeContext>,
) -> Waker {
    // SAFETY: caller (make_cross_waker -> task_ptr_from_local_waker)
    // returned task_ptr from a live local waker, refcount >= 1.
    // TaskRef::acquire increments the task's refcount.
    let task_ref = unsafe { crate::task::TaskRef::acquire(task_ptr) };
    let inner = std::sync::Arc::new(CrossTaskWakerInner { task_ref, ctx });
    let raw = RawWaker::new(
        std::sync::Arc::into_raw(inner).cast::<()>(),
        &CROSS_TASK_VTABLE,
    );
    // SAFETY: raw was constructed from a valid Arc and our CROSS_TASK_VTABLE.
    // The vtable functions correctly manage the Arc's refcount.
    unsafe { Waker::from_raw(raw) }
}

/// Clone: bump the Arc refcount. No allocation, no task-level ref_inc
/// (the inner already holds one TaskRef shared by all clones).
unsafe fn cross_task_clone(data: *const ()) -> RawWaker {
    // SAFETY: data was produced by Arc::into_raw in make_cross_task_waker
    // or a previous clone. Reconstruct the Arc to clone it, then
    // immediately into_raw the original to avoid dropping it (the source
    // RawWaker still owns that ref).
    let arc = unsafe { std::sync::Arc::from_raw(data.cast::<CrossTaskWakerInner>()) };
    let cloned = std::sync::Arc::clone(&arc);
    // Hand the original Arc back to its owner (the source RawWaker).
    let _ = std::sync::Arc::into_raw(arc);
    RawWaker::new(
        std::sync::Arc::into_raw(cloned).cast::<()>(),
        &CROSS_TASK_VTABLE,
    )
}

/// Wake by value: dispatch the wake, then drop our Arc. If we held the
/// last ref, `Inner::drop` runs — `task_ref` drops first (releasing the
/// task ref via `dispose_terminal` if terminal), then `ctx` drops.
unsafe fn cross_task_wake(data: *const ()) {
    // SAFETY: data was produced by Arc::into_raw. Reconstruct the Arc
    // to consume it (wake by value).
    let arc = unsafe { std::sync::Arc::from_raw(data.cast::<CrossTaskWakerInner>()) };
    // SAFETY: arc.task_ref holds one ref on the task — alive across
    // this call. Same for arc.ctx (Arc).
    unsafe {
        crate::cross_wake::wake_task_cross_thread(arc.task_ref.as_ptr(), &arc.ctx);
    }
    // Drop arc here. If last ref, inner drops → task_ref drops →
    // ref_dec → dispose_terminal (if terminal) → ctx drops.
}

/// Wake by ref: dispatch only. No Arc takeover, no ref change.
unsafe fn cross_task_wake_by_ref(data: *const ()) {
    // SAFETY: data was produced by Arc::into_raw. The Arc is still alive
    // (wake_by_ref borrows, doesn't consume). Reading through the raw
    // pointer is valid because Arc guarantees the allocation is live while
    // any strong ref exists.
    let inner = unsafe { &*data.cast::<CrossTaskWakerInner>() };
    // SAFETY: inner.task_ref holds a ref on the task; inner.ctx is an Arc.
    unsafe {
        crate::cross_wake::wake_task_cross_thread(inner.task_ref.as_ptr(), &inner.ctx);
    }
}

/// Drop: drop our Arc. If we held the last ref, `Inner::drop` runs —
/// see `cross_task_wake` for the cascade.
unsafe fn cross_task_drop(data: *const ()) {
    // SAFETY: data was produced by Arc::into_raw. Reconstruct the Arc
    // to drop it. If this is the last Arc, Inner::drop runs: task_ref
    // drops first (ref_dec), then ctx drops.
    let _arc = unsafe { std::sync::Arc::from_raw(data.cast::<CrossTaskWakerInner>()) };
    // _arc drops at end of scope.
}

// =============================================================================
// spawn_on_tokio — run a future on tokio's thread pool
// =============================================================================

/// Spawn a future onto the tokio thread pool. Returns a handle
/// that can be awaited from nexus-async-rt.
///
/// The future runs on tokio's worker thread — it must be `Send + 'static`.
/// The result is delivered back to our executor via the cross-thread
/// waker bridge.
///
/// Use this for cold-path operations that need the tokio ecosystem
/// (reqwest, database drivers, AWS SDK, databento) without blocking
/// the hot-path executor.
///
/// # Requirements
///
/// The returned handle must be awaited from within
/// [`Runtime::block_on`](crate::Runtime::block_on) so the cross-thread
/// waker bridge can deliver the result. Spawning itself works from any
/// context with a tokio runtime installed.
///
/// # Example
///
/// ```ignore
/// use nexus_async_rt::tokio_compat::spawn_on_tokio;
///
/// rt.block_on(async {
///     let data = spawn_on_tokio(async {
///         reqwest::get("https://api.exchange.com/ticker")
///             .await
///             .unwrap()
///             .text()
///             .await
///             .unwrap()
///     }).await.unwrap();
///
///     // Back on our executor — process the result
///     process(data);
/// });
/// ```
pub fn spawn_on_tokio<F, T>(future: F) -> TokioJoinHandle<T>
where
    F: Future<Output = T> + Send + 'static,
    T: Send + 'static,
{
    let handle = tokio_runtime().handle().spawn(future);
    TokioJoinHandle {
        inner: handle,
        _not_send: std::marker::PhantomData,
    }
}

// =============================================================================
// TokioJoinHandle
// =============================================================================

/// Handle to a future running on the tokio thread pool.
///
/// Await to get the result. Dropping aborts the tokio task.
///
/// Unlike [`JoinHandle`](crate::JoinHandle) (which detaches on drop),
/// `TokioJoinHandle` aborts on drop — tokio tasks may hold remote
/// resources that should be released promptly.
///
/// `!Send` — must be awaited from the nexus-async-rt executor thread.
#[must_use = "dropping a TokioJoinHandle aborts the tokio task"]
pub struct TokioJoinHandle<T> {
    inner: tokio::task::JoinHandle<T>,
    _not_send: std::marker::PhantomData<*const ()>,
}

impl<T> Future for TokioJoinHandle<T> {
    type Output = Result<T, TokioJoinError>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // Build cross-thread waker so tokio can wake our executor.
        let cross_waker = make_cross_waker(cx);
        let mut cross_cx = Context::from_waker(&cross_waker);

        // Poll tokio's JoinHandle with the cross-thread waker.
        // tokio::JoinHandle is Unpin — safe pin projection.
        let inner = Pin::new(&mut self.get_mut().inner);
        match inner.poll(&mut cross_cx) {
            Poll::Pending => Poll::Pending,
            Poll::Ready(Ok(val)) => Poll::Ready(Ok(val)),
            Poll::Ready(Err(e)) => Poll::Ready(Err(TokioJoinError(e))),
        }
    }
}

impl<T> TokioJoinHandle<T> {
    /// Returns `true` if the tokio task has completed.
    pub fn is_finished(&self) -> bool {
        self.inner.is_finished()
    }

    /// Abort the tokio task.
    pub fn abort(&self) {
        self.inner.abort();
    }
}

impl<T> Drop for TokioJoinHandle<T> {
    fn drop(&mut self) {
        // Abort the tokio task — we can't observe the result, and
        // the task may hold connections or file handles on tokio's side.
        self.inner.abort();
    }
}

// =============================================================================
// TokioJoinError
// =============================================================================

/// Error returned when a tokio-spawned task fails.
///
/// Wraps `tokio::task::JoinError`. The task either panicked or was
/// cancelled (via [`TokioJoinHandle::abort`] or handle drop).
pub struct TokioJoinError(tokio::task::JoinError);

impl TokioJoinError {
    /// Returns `true` if the task was cancelled.
    pub fn is_cancelled(&self) -> bool {
        self.0.is_cancelled()
    }

    /// Returns `true` if the task panicked.
    pub fn is_panic(&self) -> bool {
        self.0.is_panic()
    }
}

impl std::fmt::Display for TokioJoinError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl std::fmt::Debug for TokioJoinError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl std::error::Error for TokioJoinError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.0.source()
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod arc_tests {
    //! White-box tests for §2.1's `Arc<CrossTaskWakerInner>` semantics.
    //!
    //! Pre-§2.1 each per-clone `Box<CrossTaskWakerData>` carried its own
    //! task-level `ref_inc` and matching `ref_dec`. Under Arc, the
    //! single `TaskRef` lives in `Inner` — N Arc clones share it,
    //! producing exactly one task-level `ref_inc` (at construction) and
    //! one task-level `ref_dec` (at last-Arc drop, via `Inner::drop`
    //! → `TaskRef::Drop`). These tests pin that contract.

    use super::*;
    use crate::cross_wake::{CrossWakeContext, CrossWakeQueue};
    use crate::task::{self, Task};
    use std::future::Future;
    use std::pin::Pin;
    use std::sync::Arc as StdArc;
    use std::sync::atomic::AtomicBool;
    use std::task::{Context, Poll};

    struct ArcNoop;
    impl Future for ArcNoop {
        type Output = ();
        fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<()> {
            Poll::Ready(())
        }
    }

    fn make_test_task() -> *mut u8 {
        let task = Box::new(Task::new_boxed(ArcNoop, 0));
        Box::into_raw(task) as *mut u8
    }

    fn make_test_ctx() -> StdArc<CrossWakeContext> {
        let poll = mio::Poll::new().expect("mio::Poll");
        let waker = StdArc::new(
            mio::Waker::new(poll.registry(), mio::Token(usize::MAX)).expect("mio::Waker"),
        );
        StdArc::new(CrossWakeContext {
            queue: CrossWakeQueue::new(),
            mio_waker: waker,
            parked: AtomicBool::new(false),
        })
    }

    /// CALLOUT 1: N Arc clones produce ONE task-level `ref_inc` (at
    /// construction) and ONE `ref_dec` (at last-Arc drop).
    #[test]
    fn multi_clone_arc_terminal_ref_count() {
        let ctx = make_test_ctx();
        let task_ptr = make_test_task();

        // Baseline: rc = 1 (Task::new_boxed initial executor-style ref).
        // SAFETY: task_ptr valid from make_test_task; reading refcount.
        assert_eq!(unsafe { task::ref_count(task_ptr) }, 1);

        // Construct the cross-task waker. ONE task-level ref_inc fires
        // here (TaskRef::acquire inside make_cross_task_waker).
        let waker0 = make_cross_task_waker(task_ptr, StdArc::clone(&ctx));
        assert_eq!(
            // SAFETY: task_ptr valid; reading refcount for assertion.
            unsafe { task::ref_count(task_ptr) },
            2,
            "make_cross_task_waker must take exactly one task-level ref"
        );

        // Clone N times via tokio's Waker::clone path → vtable
        // cross_task_clone → Arc::clone (atomic only, no task-level
        // ref_inc).
        let waker1 = waker0.clone();
        let waker2 = waker0.clone();
        let waker3 = waker0.clone();
        let waker4 = waker0.clone();
        assert_eq!(
            // SAFETY: task_ptr valid; reading refcount for assertion.
            unsafe { task::ref_count(task_ptr) },
            2,
            "Arc::clone must NOT bump task-level refcount"
        );

        // Drop in arbitrary order. Each drop is Arc::from_raw + drop —
        // atomic decrement only — until the LAST drop runs Inner::drop.
        drop(waker2);
        drop(waker4);
        drop(waker0);
        drop(waker1);
        assert_eq!(
            // SAFETY: task_ptr valid; reading refcount for assertion.
            unsafe { task::ref_count(task_ptr) },
            2,
            "intermediate Arc drops must NOT decrement task-level refcount"
        );

        // Final Arc drop → Inner::drop → task_ref drops → ref_dec
        // → if terminal, dispose_terminal (here: not terminal because
        // the original executor-style ref still exists, so rc 2 → 1).
        drop(waker3);
        assert_eq!(
            // SAFETY: task_ptr valid; reading refcount for assertion.
            unsafe { task::ref_count(task_ptr) },
            1,
            "last Arc drop must produce exactly ONE task-level ref_dec"
        );

        // Cleanup: drop the executor-style ref via complete_and_unref →
        // terminal → free.
        // SAFETY: task_ptr valid with rc=1. drop_task_future drops the
        // inner future. complete_and_unref sets COMPLETED + rc → 0 →
        // FreeBox. free_task reclaims the Box allocation.
        unsafe {
            task::drop_task_future(task_ptr);
            assert!(matches!(
                task::complete_and_unref(task_ptr),
                task::FreeAction::FreeBox
            ));
            task::free_task(task_ptr);
        }
    }

    /// Wake-by-value also produces the right ref count: it consumes the
    /// Waker (one Arc drop) but does not extra-decrement.
    #[test]
    fn wake_by_value_consumes_one_arc_only() {
        let ctx = make_test_ctx();
        let task_ptr = make_test_task();

        let waker0 = make_cross_task_waker(task_ptr, StdArc::clone(&ctx));
        let waker1 = waker0.clone();

        // After construction + clone: task rc=2, Arc strong=2.
        // SAFETY: task_ptr valid; reading refcount for assertion.
        assert_eq!(unsafe { task::ref_count(task_ptr) }, 2);

        // wake() consumes waker0 → cross_task_wake → Arc::from_raw +
        // wake_task_cross_thread + Arc drop. Since waker1 still holds
        // an Arc, Inner::drop does NOT run; task ref_count unchanged.
        waker0.wake();
        assert_eq!(
            // SAFETY: task_ptr valid; reading refcount for assertion.
            unsafe { task::ref_count(task_ptr) },
            2,
            "wake-by-value with surviving sibling Arc must not ref_dec the task"
        );

        // Drop the survivor → last Arc → Inner::drop → ref_dec.
        drop(waker1);
        // SAFETY: task_ptr valid; reading refcount for assertion.
        assert_eq!(unsafe { task::ref_count(task_ptr) }, 1);

        // After wake(), the task is in the cross-queue. Drain it so
        // Drop on ctx doesn't leak the entry. (Stub-aware pop.)
        let _ = ctx.queue.pop();
        // Clear queued so cleanup works.
        // SAFETY: task_ptr valid; reading and clearing atomic flag.
        if unsafe { task::is_queued(task_ptr) } {
            // SAFETY: task_ptr valid; clearing queued flag after is_queued check.
            unsafe { task::clear_queued(task_ptr) };
        }

        // SAFETY: task_ptr valid with rc=1. drop_task_future +
        // complete_and_unref → FreeBox. free_task reclaims.
        unsafe {
            task::drop_task_future(task_ptr);
            assert!(matches!(
                task::complete_and_unref(task_ptr),
                task::FreeAction::FreeBox
            ));
            task::free_task(task_ptr);
        }
    }

    /// Performance benchmark for §2.1's per-clone improvement. Run with:
    ///
    /// ```bash
    /// cargo test -p nexus-async-rt --features tokio-compat --release \
    ///     --lib tokio_compat::arc_tests::bench_cross_task_clone \
    ///     -- --ignored --nocapture
    /// ```
    ///
    /// Pre-§2.1 (per-clone Box): ~50ns under glibc malloc.
    /// Post-§2.1 (Arc::clone): ~5ns atomic.
    ///
    /// Same convention as `lib.rs::tests::dispatch_latency`. Not a
    /// criterion bench because the existing `benches/` files are stale
    /// and don't build (pre-existing breakage; out of scope for PR 2).
    #[test]
    #[ignore = "performance benchmark, run with --release --nocapture"]
    fn bench_cross_task_clone() {
        use std::time::Instant;

        let ctx = make_test_ctx();
        let task_ptr = make_test_task();
        let waker = make_cross_task_waker(task_ptr, StdArc::clone(&ctx));

        // Warmup.
        let warmup: Vec<Waker> = (0..10_000).map(|_| waker.clone()).collect();
        drop(warmup);

        // Measure: clone N times into a Vec, then drop the Vec.
        const ITERS: usize = 1_000_000;
        let mut clones = Vec::with_capacity(ITERS);
        let start = Instant::now();
        for _ in 0..ITERS {
            clones.push(waker.clone());
        }
        let clone_elapsed = start.elapsed();

        let drop_start = Instant::now();
        drop(clones);
        let drop_elapsed = drop_start.elapsed();

        let ns_per_clone = clone_elapsed.as_nanos() / ITERS as u128;
        let ns_per_drop = drop_elapsed.as_nanos() / ITERS as u128;
        println!("cross_task_waker: clone={ns_per_clone}ns, drop={ns_per_drop}ns ({ITERS} iters)");

        // Cleanup.
        drop(waker);
        // SAFETY: task_ptr valid with rc=1 after last waker dropped.
        // drop_task_future + complete_and_unref → free_task reclaims.
        unsafe {
            task::drop_task_future(task_ptr);
            let _ = task::complete_and_unref(task_ptr);
            task::free_task(task_ptr);
        }
    }
}
