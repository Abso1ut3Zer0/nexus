//! Cancellation tokens for cooperative task shutdown.
//!
//! Adapted from tokio-util's `CancellationToken` design, built for
//! the nexus-async-rt runtime. `Clone + Send + Sync`. Hierarchical —
//! cancelling a parent cancels all children.
//!
//! Any holder can cancel or await cancellation — no separate sender/
//! receiver roles. This allows any task in a group to trigger shutdown.
//!
//! # Architecture
//!
//! `is_cancelled()` is a single atomic load (lock-free).
//!
//! Awaiter registration uses an **intrusive doubly-linked list** of
//! [`WaiterNode`]s embedded directly in [`Cancelled`] futures. No
//! per-poll heap allocation. The list is protected by a tiny per-token
//! spinlock (~30ns under-lock for the hot poll path; ~1µs to drain
//! N=50 waiters on cancel). The lock is per-`Inner`, never contended
//! across tokens — a process with hundreds of tokens never sees one
//! token's cancel block another.
//!
//! Children of a token use a **lock-free Treiber stack** of
//! `ChildNode`s. Children don't have the "drop while in list" lifetime
//! problem the waiter list had pre-PR3, so the simpler design works.
//!
//! # `Cancelled` is `!Unpin`
//!
//! The intrusive design requires the embedded `WaiterNode`'s address
//! to be stable from first poll until Drop. [`Cancelled`] therefore
//! carries `PhantomPinned` — `.await` auto-pins, but for hot loops
//! that re-poll the same future, **pin once outside the loop**:
//!
//! ```ignore
//! use std::pin::pin;
//!
//! let cancelled = token.cancelled();
//! let mut cancelled = pin!(cancelled);
//! loop {
//!     // poll cancelled.as_mut() — no per-iteration heap traffic
//! }
//! ```
//!
//! ```ignore
//! use nexus_async_rt::CancellationToken;
//!
//! let token = CancellationToken::new();
//!
//! // Any clone can cancel or await:
//! let t = token.clone();
//! spawn_boxed(async move {
//!     match do_work().await {
//!         Ok(()) => t.cancelled().await,  // wait
//!         Err(_) => t.cancel(),           // or trigger
//!     }
//! });
//!
//! // Hierarchical:
//! let child = token.child();  // cancelled when parent is
//!
//! // Drop guard — cancels on scope exit:
//! let _guard = token.drop_guard();
//! ```

use std::cell::UnsafeCell;
use std::future::Future;
use std::marker::PhantomPinned;
use std::pin::Pin;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicPtr, Ordering};
use std::task::{Context, Poll, Waker};

// =============================================================================
// Per-token spinlock — private to cancel.rs
// =============================================================================
//
// Why hand-rolled and not `crate::Backoff`: `Backoff` is the async
// retry primitive (deadline + jitter + sleep); it's for waiting on a
// *runtime* schedule, not for spinning under a contended atomic. The
// spinlock here is exponential `spin_loop` (1, 2, 4, 8, 16, 32 hints)
// then fall back to `thread::yield_now` if a holder is preempted on a
// non-isolated core. That's it; no deps. Confirmed during PR 3
// scoping (open-item 5).

#[inline]
fn spin_lock(lock: &AtomicBool) {
    if lock
        .compare_exchange_weak(false, true, Ordering::AcqRel, Ordering::Acquire)
        .is_ok()
    {
        return; // fast path: uncontended
    }
    spin_lock_slow(lock);
}

#[cold]
#[inline(never)]
fn spin_lock_slow(lock: &AtomicBool) {
    let mut spins: u32 = 0;
    loop {
        if lock
            .compare_exchange_weak(false, true, Ordering::AcqRel, Ordering::Acquire)
            .is_ok()
        {
            return;
        }
        if spins < 6 {
            // Exponential PAUSE: 1, 2, 4, 8, 16, 32 hints.
            for _ in 0..(1u32 << spins) {
                std::hint::spin_loop();
            }
            spins += 1;
        } else {
            // Holder may be preempted on a non-isolated core.
            std::thread::yield_now();
        }
    }
}

#[inline]
fn spin_unlock(lock: &AtomicBool) {
    lock.store(false, Ordering::Release);
}

/// RAII guard for the per-token spinlock. Acquires on construction,
/// releases on drop (including unwind paths).
///
/// Defense-in-depth (PR3-John-review item 3): pre-PR3-cleanup the
/// four lock sites used bare `spin_lock`/`spin_unlock` pairs. None of
/// nexus's wakers panic in production paths, so the panic-leak-deadlock
/// concern is theoretical for the actual workload — but a future
/// `?` operator, `debug_assert!`, or method call inside a critical
/// section would silently re-introduce the leak. RAII handles unwind
/// by construction; the next contributor adding a critical section
/// reaches for the guard naturally.
///
/// Also handles early returns. The subsequent-poll branch in
/// `Cancelled::poll` has an early `return Poll::Ready(())` when the
/// post-lock `in_list` recheck observes false. The bare-call version
/// had to remember to `spin_unlock` before the return; the guard
/// drops correctly in both paths.
///
/// Zero cost in the happy path: the Drop is a single Release store
/// that the compiler folds into the unlock site.
struct SpinGuard<'a> {
    lock: &'a AtomicBool,
}

impl<'a> SpinGuard<'a> {
    #[inline]
    fn new(lock: &'a AtomicBool) -> Self {
        spin_lock(lock);
        Self { lock }
    }
}

impl Drop for SpinGuard<'_> {
    #[inline]
    fn drop(&mut self) {
        spin_unlock(self.lock);
    }
}

// =============================================================================
// Inner state
// =============================================================================

struct Inner {
    cancelled: AtomicBool,
    /// Spinlock guarding `head`, every `WaiterNode::next`/`prev`, and
    /// every `WaiterNode::waker`. See [`spin_lock`]/[`spin_unlock`].
    list_lock: AtomicBool,
    /// Head of the intrusive doubly-linked list of `WaiterNode`s
    /// embedded in `Cancelled` futures. Protected by `list_lock`.
    head: UnsafeCell<*mut WaiterNode>,
    /// Head of the child Treiber stack. Each node is a heap-allocated
    /// `ChildNode`. Lock-free push (CAS), drain on cancel via swap.
    /// (Children don't have the "drop while in list" lifetime problem
    /// — `cancel()` owns the drain atomically — so the simpler
    /// lock-free design is fine here.)
    child_head: AtomicPtr<ChildNode>,
    /// Test-only race-window widener (PR3-John-review item 2,
    /// PR3-Copilot-review item 3). When `true`, `cancel()`'s drain
    /// yields right after each `in_list=false` Release store. That
    /// widens the item-1 race window from a few cycles to a scheduler
    /// quantum, letting a concurrent `Cancelled::Drop` fast path
    /// observe the store and free the WaiterNode in time to UAF the
    /// drain's next access (pre-fix). Per-`Inner` so test parallelism
    /// doesn't cross-contaminate: only the regression test's specific
    /// token has this enabled. Production builds compile the field
    /// (and the load) out entirely.
    #[cfg(test)]
    race_yield: AtomicBool,
}

/// Intrusive waiter node. Lives EMBEDDED inside a [`Cancelled`]
/// future — no Box, no per-poll allocation. The `Cancelled` future is
/// `!Unpin` so the address stays stable from first poll through Drop.
///
/// All mutable fields except `in_list` are protected by
/// `Inner::list_lock`. `in_list` is an `AtomicBool` so Drop's fast
/// path can skip the lock when the node was already unlinked (e.g.
/// `cancel()` already drained it).
struct WaiterNode {
    /// Doubly-linked list pointers. Protected by `Inner::list_lock`.
    next: UnsafeCell<*mut WaiterNode>,
    prev: UnsafeCell<*mut WaiterNode>,
    /// Stored waker. Protected by `Inner::list_lock`. Reading or
    /// writing without the lock would race `Inner::cancel`'s
    /// `Option<Waker>::take()` — UB regardless of hardware behavior.
    waker: UnsafeCell<Option<Waker>>,
    /// Fast-path skip on Drop. `false` initially. Set to `true` by
    /// `Cancelled::poll` after inserting into the list (under lock).
    /// Cleared by `Inner::cancel`'s drain (under lock) and by
    /// `Cancelled::Drop` after unlinking (under lock). Drop's fast
    /// path loads this WITHOUT the lock — if `false`, the node is
    /// already unlinked, no work needed.
    in_list: AtomicBool,
}

impl WaiterNode {
    const fn new() -> Self {
        Self {
            next: UnsafeCell::new(std::ptr::null_mut()),
            prev: UnsafeCell::new(std::ptr::null_mut()),
            waker: UnsafeCell::new(None),
            in_list: AtomicBool::new(false),
        }
    }
}

// SAFETY: WaiterNode is accessed under Inner::list_lock for all
// mutable fields except in_list (which is itself atomic). The Waker
// inside Option<Waker> is Send+Sync. The list pointers are managed
// under the lock. Send is required because Cancelled is Send +
// holds a WaiterNode.
unsafe impl Send for WaiterNode {}
// Sync is required because Inner::cancel reads/writes node fields
// from a different thread than Cancelled::poll. All such access is
// under list_lock.
// SAFETY: Sync is safe; WaiterNode fields are accessed only under Inner::list_lock.
unsafe impl Sync for WaiterNode {}

struct ChildNode {
    inner: Arc<Inner>,
    next: *mut ChildNode,
}

// SAFETY: ChildNode owns an Arc<Inner> (Send) and a raw pointer managed under exclusive ownership.
unsafe impl Send for ChildNode {}

// SAFETY: Inner contains UnsafeCell<*mut WaiterNode> (head pointer)
// which is mutated under list_lock. Send + Sync because all access
// to mutable state is gated by the lock.
unsafe impl Send for Inner {}
// SAFETY: Inner's mutable state is fully guarded by list_lock; shared access is safe across threads.
unsafe impl Sync for Inner {}

impl Inner {
    fn new() -> Arc<Self> {
        Arc::new(Self {
            cancelled: AtomicBool::new(false),
            list_lock: AtomicBool::new(false),
            head: UnsafeCell::new(std::ptr::null_mut()),
            child_head: AtomicPtr::new(std::ptr::null_mut()),
            #[cfg(test)]
            race_yield: AtomicBool::new(false),
        })
    }

    /// O(1) — single atomic load.
    fn is_cancelled(&self) -> bool {
        self.cancelled.load(Ordering::Acquire)
    }

    /// Cancel: set flag, drain waiters and collect their wakers (under
    /// lock), release lock, fire wakers, then drain and cancel all
    /// children (lock-free Treiber stack swap).
    ///
    /// Idempotent. Wakers fire OUTSIDE the critical section — collect-
    /// then-wake pattern (PR3-Copilot-review item 2 — supersedes the
    /// original CALLOUT 4 trade-off). Releasing the lock before
    /// `wake()` defends against:
    ///   - User-provided wakers that re-enter `cancel()` on the same
    ///     token (would deadlock if `wake()` ran under the lock).
    ///   - Long-running `wake()` implementations that hold the lock
    ///     for unbounded time, blocking concurrent ops on this token.
    ///   - Panicking wakers leaking the lock (SpinGuard handles this
    ///     on the unwind path; collecting first means a panicking
    ///     `wake()` can't even reach the critical section).
    ///
    /// Cost: one `Vec<Waker>` allocation per `cancel()` call, bounded
    /// by waiter count (typically <50 in trading patterns). `cancel()`
    /// runs once per token lifetime, so the allocation is rare and small.
    fn cancel(&self) {
        // Set the flag BEFORE draining so `Cancelled::poll`'s
        // post-registration recheck (and Drop's fast path) sees a
        // consistent "I'm cancelled" view.
        self.cancelled.store(true, Ordering::Release);

        // Drain waiters under the lock, collecting their wakers. O(N)
        // where N is the number of currently-registered awaiters of
        // THIS token. Wakers are fired AFTER the guard drops.
        let mut wakers: Vec<Waker> = Vec::new();
        {
            let _guard = SpinGuard::new(&self.list_lock);
            // SAFETY: list_lock held — exclusive access to head + node fields.
            let mut cur = unsafe { *self.head.get() };
            // SAFETY: list_lock held — exclusive access to the head pointer.
            unsafe { *self.head.get() = std::ptr::null_mut() };
            while !cur.is_null() {
                // SAFETY: `cur` was pushed under the lock by Cancelled::poll;
                // its lifetime is bounded by the Cancelled future's Pin (the
                // future cannot move while we hold a raw ptr to its inner
                // node because !Unpin enforces the drop-before-move
                // guarantee). The Cancelled holds an Arc<Inner>, so Inner
                // can't drop while a Cancelled exists.
                //
                // **Race-fix invariant (PR3-John-review item 1):** read all
                // node fields BEFORE the `in_list.store(false, Release)`
                // below. The Release store synchronizes-with the Acquire
                // load in `Cancelled::Drop`'s fast path; once a concurrent
                // Drop observes `in_list=false`, it returns immediately
                // and frees the WaiterNode memory. After our Release store
                // we MUST NOT touch `*cur` again — UAF on the freed
                // allocation. No `let node = &*cur;` binding, because the
                // borrow's lifetime would extend past the invalidation
                // point under stacked-/tree-borrows rules.
                //
                // The intermediate-test stress hook (yield_now) widens
                // this race window to make the regression test deterministic
                // — see `cancel_race_regression`. In production builds the
                // hook is compiled out.
                // SAFETY: list_lock held; cur is non-null and points to a live WaiterNode
                // (in_list not yet cleared); next field read before the Release store below.
                let next = unsafe { *(*cur).next.get() };
                // SAFETY: list_lock held; waker field accessed under lock while cur node is still alive.
                let waker = unsafe { (*(*cur).waker.get()).take() };
                // After this Release store, *cur may be invalidated by a
                // concurrent Cancelled::Drop fast-path. Do not access
                // *cur below this line.
                // SAFETY: list_lock held; all node fields read above before this Release store.
                unsafe { (*cur).in_list.store(false, Ordering::Release) };
                #[cfg(test)]
                if self.race_yield.load(Ordering::Relaxed) {
                    std::thread::yield_now();
                }
                cur = next;
                if let Some(w) = waker {
                    wakers.push(w);
                }
            }
        } // SpinGuard drops here, lock released BEFORE wake calls.

        // Fire wakers outside the critical section. A re-entrant or
        // long-running waker can no longer block other ops on this
        // token's lock.
        for w in wakers {
            w.wake();
        }

        // Drain children — lock-free Treiber stack swap.
        let mut child = self.child_head.swap(std::ptr::null_mut(), Ordering::AcqRel);
        while !child.is_null() {
            // SAFETY: ChildNode allocated by Box::into_raw in add_child.
            let node = unsafe { Box::from_raw(child) };
            child = node.next;
            node.inner.cancel();
        }
    }

    /// Register a child. If already cancelled, cancels the child
    /// immediately. Lock-free CAS push onto the child Treiber stack.
    fn add_child(&self, child: &Arc<Inner>) {
        let node = Box::into_raw(Box::new(ChildNode {
            inner: child.clone(),
            next: std::ptr::null_mut(),
        }));

        loop {
            // Check cancelled before pushing — avoid leaking the node.
            if self.is_cancelled() {
                // SAFETY: we just allocated this node.
                let node = unsafe { Box::from_raw(node) };
                node.inner.cancel();
                return;
            }

            let head = self.child_head.load(Ordering::Acquire);
            // SAFETY: node was just allocated via Box::into_raw above.
            // Writing next before CAS is safe — no one else can see the
            // node until the CAS succeeds.
            unsafe { (*node).next = head };
            if self
                .child_head
                .compare_exchange_weak(head, node, Ordering::AcqRel, Ordering::Relaxed)
                .is_ok()
            {
                // Race check: cancelled between our load and the CAS.
                if self.is_cancelled() {
                    // Re-cancel to drain our node (idempotent).
                    self.cancel();
                }
                return;
            }
        }
    }
}

impl Drop for Inner {
    fn drop(&mut self) {
        // Waiter list discipline: all `Cancelled` futures hold an
        // `Arc<Inner>`. The Inner cannot drop while any Cancelled
        // exists. Cancelled::Drop unlinks under the lock. So at this
        // point, no waiter nodes can possibly still be in the list.
        #[cfg(debug_assertions)]
        {
            // SAFETY: &mut self in Drop — exclusive access, no lock needed.
            let head = unsafe { *self.head.get() };
            debug_assert!(
                head.is_null(),
                "Inner::Drop with waiter list non-empty — Cancelled futures \
                 must outlive their Inner via Arc<Inner>; if you see this, \
                 the list-discipline invariant has been violated"
            );
        }

        // Drain leftover children — happens when a token is dropped
        // without ever being cancelled.
        let mut child = *self.child_head.get_mut();
        while !child.is_null() {
            // SAFETY: each ChildNode was allocated via Box::into_raw in add_child.
            // We own them exclusively (&mut self in Drop).
            let node = unsafe { Box::from_raw(child) };
            child = node.next;
        }
    }
}

// =============================================================================
// CancellationToken
// =============================================================================

/// A token for cooperative cancellation.
///
/// `Clone + Send + Sync`. Cloning shares the same cancellation state.
/// Use [`child()`](CancellationToken::child) for hierarchical cancellation.
///
/// # Example
///
/// ```ignore
/// let token = CancellationToken::new();
///
/// spawn_boxed(async move {
///     token.cancelled().await;
///     println!("shutting down");
/// });
///
/// token.cancel();
/// ```
#[derive(Clone)]
pub struct CancellationToken {
    inner: Arc<Inner>,
}

impl CancellationToken {
    /// Create a new cancellation token.
    pub fn new() -> Self {
        Self {
            inner: Inner::new(),
        }
    }

    /// Create a child token. Cancelling this token (or any ancestor)
    /// also cancels the child and wakes its waiters. Cancelling the
    /// child does NOT cancel the parent.
    pub fn child(&self) -> Self {
        let child = Self {
            inner: Inner::new(),
        };
        self.inner.add_child(&child.inner);
        child
    }

    /// Cancel this token. All futures awaiting [`cancelled()`](Self::cancelled)
    /// will resolve. Child tokens are also cancelled.
    pub fn cancel(&self) {
        self.inner.cancel();
    }

    /// Whether this token has been cancelled.
    /// O(1) — single atomic load. Parent cancellation propagates
    /// eagerly (sets the child's flag), so no chain traversal needed.
    pub fn is_cancelled(&self) -> bool {
        self.inner.is_cancelled()
    }

    /// Returns a guard that cancels this token when dropped.
    ///
    /// Useful for ensuring cancellation on scope exit or panic.
    pub fn drop_guard(self) -> DropGuard {
        DropGuard { token: Some(self) }
    }

    /// Returns a future that resolves when this token is cancelled.
    ///
    /// The returned `Cancelled` is `!Unpin`. `.await` auto-pins; for
    /// hot loops re-polling the same future, pin once outside:
    ///
    /// ```ignore
    /// let cancelled = token.cancelled();
    /// let mut cancelled = std::pin::pin!(cancelled);
    /// loop { /* poll cancelled.as_mut() */ }
    /// ```
    pub fn cancelled(&self) -> Cancelled {
        Cancelled {
            inner: self.inner.clone(),
            node: WaiterNode::new(),
            _pin: PhantomPinned,
        }
    }

    /// Test-only: enable the race-window-widening yield in this
    /// token's `cancel()` drain. Per-token (not process-global) so
    /// parallel test execution doesn't cross-contaminate scheduling
    /// — only this token's drain yields. See `Inner::race_yield`
    /// for the rationale (PR3-Copilot-review item 3).
    #[cfg(test)]
    pub(crate) fn enable_race_yield(&self) {
        self.inner.race_yield.store(true, Ordering::Relaxed);
    }
}

impl Default for CancellationToken {
    fn default() -> Self {
        Self::new()
    }
}

impl std::fmt::Debug for CancellationToken {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CancellationToken")
            .field("cancelled", &self.is_cancelled())
            .finish()
    }
}

// =============================================================================
// Cancelled future
// =============================================================================

/// Future that resolves when a [`CancellationToken`] is cancelled.
///
/// Created by [`CancellationToken::cancelled()`]. The embedded
/// [`WaiterNode`] is registered in the token's intrusive doubly-linked
/// list on first poll. Subsequent polls re-register the waker if it
/// changed (under the per-token spinlock — see CALLOUT 2 of PR 3's
/// plan). Drop unlinks the node (fast path: skip the lock if already
/// unlinked by `cancel()`'s drain).
///
/// `!Unpin` — `.await` auto-pins, but for hot loops that re-poll the
/// same future, pin once outside:
///
/// ```ignore
/// use std::pin::pin;
///
/// let cancelled = token.cancelled();
/// let mut cancelled = pin!(cancelled);
/// loop { /* poll cancelled.as_mut() */ }
/// ```
pub struct Cancelled {
    inner: Arc<Inner>,
    node: WaiterNode,
    _pin: PhantomPinned,
}

impl Future for Cancelled {
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        // Lock-free fast-out: token already cancelled. Resolves any
        // already-cancelled awaiter in ~3 cycles, no lock.
        if self.inner.is_cancelled() {
            return Poll::Ready(());
        }

        // SAFETY: structural projection — node is part of the future,
        // and we're !Unpin so the address stays stable. We don't move
        // out of `self`.
        let this = unsafe { self.get_unchecked_mut() };
        let node = &this.node;

        // First poll? Insert under the lock + write the waker.
        if !node.in_list.load(Ordering::Acquire) {
            {
                let _guard = SpinGuard::new(&this.inner.list_lock);
                // SAFETY: list_lock held.
                unsafe { *node.waker.get() = Some(cx.waker().clone()) };
                // SAFETY: list_lock held; node not currently linked
                // (in_list was false above). Insert at head.
                unsafe {
                    let head_slot = this.inner.head.get();
                    let old_head = *head_slot;
                    let node_ptr = std::ptr::from_ref(node).cast_mut();
                    *node.next.get() = old_head;
                    *node.prev.get() = std::ptr::null_mut();
                    if !old_head.is_null() {
                        *(*old_head).prev.get() = node_ptr;
                    }
                    *head_slot = node_ptr;
                }
                node.in_list.store(true, Ordering::Release);
            }

            // Re-check cancelled AFTER registration. cancel() sets
            // the flag BEFORE draining; if it ran between our flag
            // check at the top and our insert, the flag is now true
            // and we either:
            //  (a) inserted before cancel's drain — drain woke our
            //      waker and we'll be polled again; OR
            //  (b) inserted after cancel's drain — our node sits in
            //      the list, no one will wake it; the recheck here
            //      catches that and we resolve immediately. Drop
            //      will unlink under the slow path.
            if this.inner.is_cancelled() {
                return Poll::Ready(());
            }
            return Poll::Pending;
        }

        // Subsequent poll: take the lock to safely read/update the
        // waker. The lock-free `will_wake` snapshot is UB
        // (`Option<Waker>` is non-atomic; cancel() takes() under the
        // lock). Critical section is one comparison + maybe one
        // clone — ~30ns uncontended.
        let _guard = SpinGuard::new(&this.inner.list_lock);
        // Re-check in_list under the lock: cancel() may have drained
        // between the in_list check above and our lock acquisition.
        if !node.in_list.load(Ordering::Relaxed) {
            // _guard's Drop releases the lock on the early return.
            // cancel() set self.cancelled BEFORE draining (Release
            // ordering pairs with the Acquire load below).
            return Poll::Ready(());
        }
        // SAFETY: list_lock held.
        let needs_update = unsafe {
            (*node.waker.get())
                .as_ref()
                .is_none_or(|w| !w.will_wake(cx.waker()))
        };
        if needs_update {
            // SAFETY: list_lock held. Drops the previous waker
            // inside the critical section — drop is brief for
            // standard wakers.
            unsafe { *node.waker.get() = Some(cx.waker().clone()) };
        }
        Poll::Pending
    }
}

impl Drop for Cancelled {
    fn drop(&mut self) {
        // Fast path (CALLOUT 3): cancel() already drained, our node
        // was unlinked. Skip the lock entirely — common case for the
        // "cancel fired then awaiter drops" pattern.
        if !self.node.in_list.load(Ordering::Acquire) {
            return;
        }

        // Slow path: still in the list. Take the lock and unlink.
        let _guard = SpinGuard::new(&self.inner.list_lock);
        // Re-check under the lock: cancel() may have drained between
        // the load above and our lock acquisition.
        if self.node.in_list.load(Ordering::Relaxed) {
            // SAFETY: list_lock held; node is in_list which means
            // its prev/next are valid pointers (or null for boundary).
            unsafe {
                let prev = *self.node.prev.get();
                let next = *self.node.next.get();
                if prev.is_null() {
                    // Was head — advance head to next.
                    *self.inner.head.get() = next;
                } else {
                    *(*prev).next.get() = next;
                }
                if !next.is_null() {
                    *(*next).prev.get() = prev;
                }
                // Clear our pointers (defensive; the node is about
                // to drop).
                *self.node.next.get() = std::ptr::null_mut();
                *self.node.prev.get() = std::ptr::null_mut();
                // Drop the stored waker (if any). cancel() may have
                // already taken it; either way, this is correct.
                let _ = (*self.node.waker.get()).take();
            }
            self.node.in_list.store(false, Ordering::Release);
        }
        // _guard's Drop releases the lock.
    }
}

// =============================================================================
// DropGuard
// =============================================================================

/// A guard that cancels a [`CancellationToken`] when dropped.
///
/// Created by [`CancellationToken::drop_guard()`]. Call
/// [`disarm()`](DropGuard::disarm) to prevent cancellation on drop.
pub struct DropGuard {
    token: Option<CancellationToken>,
}

impl DropGuard {
    /// Disarm the guard — the token will NOT be cancelled on drop.
    /// Returns the token.
    pub fn disarm(mut self) -> CancellationToken {
        self.token.take().expect("DropGuard already disarmed")
    }
}

impl Drop for DropGuard {
    fn drop(&mut self) {
        if let Some(ref token) = self.token {
            token.cancel();
        }
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::task::{RawWaker, RawWakerVTable};

    fn noop_waker() -> Waker {
        fn noop(_: *const ()) {}
        fn noop_clone(p: *const ()) -> RawWaker {
            RawWaker::new(p, &VTABLE)
        }
        const VTABLE: RawWakerVTable = RawWakerVTable::new(noop_clone, noop, noop, noop);
        // SAFETY: all vtable functions are no-ops or trivial clones; the
        // null data pointer is never dereferenced.
        unsafe { Waker::from_raw(RawWaker::new(std::ptr::null(), &VTABLE)) }
    }

    fn poll_once<F: Future>(f: Pin<&mut F>) -> Poll<F::Output> {
        let waker = noop_waker();
        let mut cx = Context::from_waker(&waker);
        f.poll(&mut cx)
    }

    #[test]
    fn not_cancelled_by_default() {
        let token = CancellationToken::new();
        assert!(!token.is_cancelled());
    }

    #[test]
    fn cancel_sets_flag() {
        let token = CancellationToken::new();
        token.cancel();
        assert!(token.is_cancelled());
    }

    #[test]
    fn cancel_is_idempotent() {
        let token = CancellationToken::new();
        token.cancel();
        token.cancel();
        assert!(token.is_cancelled());
    }

    #[test]
    fn clone_shares_state() {
        let token = CancellationToken::new();
        let clone = token.clone();
        token.cancel();
        assert!(clone.is_cancelled());
    }

    #[test]
    fn child_sees_parent_cancel() {
        let parent = CancellationToken::new();
        let child = parent.child();
        assert!(!child.is_cancelled());
        parent.cancel();
        assert!(child.is_cancelled());
    }

    #[test]
    fn grandchild_sees_ancestor_cancel() {
        let root = CancellationToken::new();
        let child = root.child();
        let grandchild = child.child();
        assert!(!grandchild.is_cancelled());
        root.cancel();
        assert!(grandchild.is_cancelled());
    }

    #[test]
    fn child_cancel_does_not_affect_parent() {
        let parent = CancellationToken::new();
        let child = parent.child();
        child.cancel();
        assert!(child.is_cancelled());
        assert!(!parent.is_cancelled());
    }

    #[test]
    fn cancelled_future_ready_when_cancelled() {
        let token = CancellationToken::new();
        token.cancel();

        let mut fut = std::pin::pin!(token.cancelled());
        assert!(matches!(poll_once(fut.as_mut()), Poll::Ready(())));
    }

    #[test]
    fn cancelled_future_pending_then_ready() {
        let token = CancellationToken::new();

        let mut fut = std::pin::pin!(token.cancelled());
        assert!(matches!(poll_once(fut.as_mut()), Poll::Pending));

        token.cancel();
        // Re-poll — now ready.
        assert!(matches!(poll_once(fut.as_mut()), Poll::Ready(())));
    }

    #[test]
    fn child_cancelled_future_from_parent() {
        let parent = CancellationToken::new();
        let child = parent.child();

        let mut fut = std::pin::pin!(child.cancelled());
        assert!(matches!(poll_once(fut.as_mut()), Poll::Pending));

        parent.cancel();
        assert!(matches!(poll_once(fut.as_mut()), Poll::Ready(())));
    }

    #[test]
    fn multiple_waiters() {
        let token = CancellationToken::new();

        let mut fut1 = std::pin::pin!(token.cancelled());
        let mut fut2 = std::pin::pin!(token.cancelled());

        assert!(matches!(poll_once(fut1.as_mut()), Poll::Pending));
        assert!(matches!(poll_once(fut2.as_mut()), Poll::Pending));

        token.cancel();

        assert!(matches!(poll_once(fut1.as_mut()), Poll::Ready(())));
        assert!(matches!(poll_once(fut2.as_mut()), Poll::Ready(())));
    }

    #[test]
    fn cross_thread_cancel() {
        let token = CancellationToken::new();
        let clone = token.clone();

        let handle = std::thread::spawn(move || {
            std::thread::sleep(std::time::Duration::from_millis(10));
            clone.cancel();
        });

        while !token.is_cancelled() {
            std::hint::spin_loop();
        }

        handle.join().unwrap();
    }

    #[test]
    fn drop_guard_cancels_on_drop() {
        let token = CancellationToken::new();
        let clone = token.clone();
        {
            let _guard = token.drop_guard();
            assert!(!clone.is_cancelled());
        }
        assert!(clone.is_cancelled());
    }

    #[test]
    fn drop_guard_disarm() {
        let token = CancellationToken::new();
        let clone = token.clone();
        let guard = token.drop_guard();
        let recovered = guard.disarm();
        drop(recovered);
        assert!(!clone.is_cancelled());
    }

    #[test]
    fn drop_guard_on_panic() {
        let token = CancellationToken::new();
        let clone = token.clone();

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _guard = token.drop_guard();
            panic!("simulated panic");
        }));

        assert!(result.is_err());
        assert!(clone.is_cancelled());
    }

    #[test]
    fn send_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<CancellationToken>();
        assert_send_sync::<Cancelled>();
    }

    #[test]
    fn drop_without_cancel_cleans_up() {
        // Tokens dropped without cancellation — nodes should be
        // unlinked via Cancelled::Drop's slow path; Inner::Drop's
        // debug_assert verifies the list is empty at that point.
        let token = CancellationToken::new();
        let _child = token.child();
        let mut fut = std::pin::pin!(token.cancelled());
        let _ = poll_once(fut.as_mut()); // register a waiter
        // Everything dropped — Cancelled::Drop unlinks; Inner::Drop
        // debug-asserts empty list.
    }

    #[test]
    fn many_children() {
        let parent = CancellationToken::new();
        let children: Vec<_> = (0..100).map(|_| parent.child()).collect();

        parent.cancel();
        for child in &children {
            assert!(child.is_cancelled());
        }
    }

    #[test]
    fn child_created_after_parent_cancelled() {
        let parent = CancellationToken::new();
        parent.cancel();
        let child = parent.child();
        assert!(child.is_cancelled());
    }

    #[test]
    fn poll_after_cancel_drained_uses_in_list_false_path() {
        // After cancel() drains, the node's in_list is false. A
        // subsequent poll on the SAME pinned future hits the "first
        // poll" branch (`!in_list.load`), which would re-insert. But
        // the lock-free fast-out (`is_cancelled`) catches it BEFORE
        // we attempt insertion, so we resolve to Ready without
        // touching the list. Verify by polling after cancel —
        // result is Ready and the list discipline (Inner::Drop
        // debug_assert) holds.
        let token = CancellationToken::new();
        let mut fut = std::pin::pin!(token.cancelled());
        assert!(matches!(poll_once(fut.as_mut()), Poll::Pending));
        token.cancel();
        // After cancel drains, our node's in_list is false.
        // Subsequent poll: is_cancelled fast-out → Ready.
        assert!(matches!(poll_once(fut.as_mut()), Poll::Ready(())));
    }

    /// PR3-John-review item 1 / 2 regression test.
    ///
    /// **The race (pre-fix):** `Inner::cancel`'s drain loop did
    /// `in_list.store(false, Release)` BEFORE `(*node.waker.get()).take()`.
    /// A concurrent `Cancelled::Drop` fast-path (Acquire-loads
    /// `in_list`, returns immediately if false, freeing the
    /// WaiterNode memory) could interleave between the store and the
    /// subsequent `*node` access. UAF on the freed WaiterNode.
    ///
    /// **The window** is normally a few cycles — too narrow for
    /// reliable reproduction in unit tests on modern hardware (the
    /// existing `concurrent_register_and_cancel_race` test runs ~50
    /// iterations and doesn't deterministically hit it).
    ///
    /// **Widening:** `token.enable_race_yield()` makes THIS token's
    /// drain loop yield right after the in_list=false store. That
    /// turns "a few cycles" into a scheduler quantum, which is
    /// reliable. Per-token (not process-global) so parallel tests
    /// don't see this token's yield (#[cfg(test)]-only — production
    /// is unaffected).
    ///
    /// **Test shape:** spawn N=200 trials. Each trial: thread A pins
    /// then polls a Cancelled to register, signals "registered",
    /// spins on `is_cancelled()`, drops the future as soon as the
    /// flag fires. Thread B waits for "registered", then calls
    /// `token.cancel()`. With the per-token yield enabled, this hits
    /// the race window deterministically pre-fix.
    ///
    /// Pre-fix: tree-borrows miri reports UB in the drain loop
    /// reading freed WaiterNode memory. Post-fix: clean.
    #[test]
    fn cancel_drain_race_regression() {
        use std::sync::Arc;
        use std::sync::atomic::AtomicBool;

        // Smaller iteration count under miri (which is ~100x slower);
        // larger in normal cargo test.
        #[cfg(miri)]
        const TRIALS: usize = 20;
        #[cfg(not(miri))]
        const TRIALS: usize = 200;

        for _ in 0..TRIALS {
            let token = CancellationToken::new();
            // Per-token toggle: only THIS token's drain yields.
            // Other tests running in parallel are unaffected.
            token.enable_race_yield();
            let registered = Arc::new(AtomicBool::new(false));

            let drop_thread = {
                let token = token.clone();
                let registered = registered.clone();
                std::thread::spawn(move || {
                    let mut fut = Box::pin(token.cancelled());
                    // Register: poll once.
                    assert!(matches!(poll_once(fut.as_mut()), Poll::Pending));
                    registered.store(true, Ordering::Release);
                    // Spin until cancel flag visible, then immediately
                    // drop. The Drop fast-path will Acquire-load
                    // in_list. With the yield hook in cancel's drain,
                    // there's a scheduler-quantum window between the
                    // drain's in_list=false store and (pre-fix) its
                    // subsequent waker take — Drop's fast-path
                    // returns and frees, drain UAFs.
                    while !token.is_cancelled() {
                        std::hint::spin_loop();
                    }
                    drop(fut);
                })
            };

            let cancel_thread = {
                let token = token.clone();
                let registered = registered.clone();
                std::thread::spawn(move || {
                    while !registered.load(Ordering::Acquire) {
                        std::hint::spin_loop();
                    }
                    token.cancel();
                })
            };

            drop_thread.join().unwrap();
            cancel_thread.join().unwrap();
        }
    }
}
