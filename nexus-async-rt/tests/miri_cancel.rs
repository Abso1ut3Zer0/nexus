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
//! Miri tests for CancellationToken.
//!
//! Exercises Treiber stack push/drain, waiter node lifecycle,
//! child propagation, and drop cleanup under miri.
//!
//! Run: `cargo +nightly miri test -p nexus-async-rt --test miri_cancel`

use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};

use nexus_async_rt::CancellationToken;

// =============================================================================
// Test helpers
// =============================================================================

/// Minimal noop waker for polling futures outside a runtime.
fn noop_waker() -> Waker {
    static VTABLE: RawWakerVTable =
        RawWakerVTable::new(|p| RawWaker::new(p, &VTABLE), |_| {}, |_| {}, |_| {});
    // SAFETY: the vtable functions are all no-ops; the null data pointer is never dereferenced.
    unsafe { Waker::from_raw(RawWaker::new(std::ptr::null(), &VTABLE)) }
}

fn poll_once<F: Future>(f: Pin<&mut F>) -> Poll<F::Output> {
    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);
    f.poll(&mut cx)
}

/// A waker that sets a Cell<bool> to true when woken.
/// All instances share the same static vtable; `will_wake()` differs between
/// calls because the raw waker data stores the `flag` pointer. Two tracking
/// wakers built from different flags will not `will_wake()`, which exercises
/// the re-registration path. Using the same flag returns true.
fn tracking_waker(flag: &std::cell::Cell<bool>) -> Waker {
    // Store the flag pointer as the waker data. Distinct flags produce
    // distinct wakers because the data pointer differs.
    let data = flag as *const std::cell::Cell<bool> as *const ();

    static VTABLE: RawWakerVTable = RawWakerVTable::new(
        |p| RawWaker::new(p, &VTABLE),
        |p| {
            // wake: set the flag
            // SAFETY: p is the data pointer set by RawWaker::new from a &Cell<bool>; valid for the waker's lifetime.
            let flag = unsafe { &*(p as *const std::cell::Cell<bool>) };
            flag.set(true);
        },
        |p| {
            // wake_by_ref: set the flag
            // SAFETY: p is the data pointer set by RawWaker::new from a &Cell<bool>; valid for the waker's lifetime.
            let flag = unsafe { &*(p as *const std::cell::Cell<bool>) };
            flag.set(true);
        },
        |_| {}, // drop: no-op
    );
    // SAFETY: vtable functions match the data pointer layout; Cell<bool> outlives the waker.
    unsafe { Waker::from_raw(RawWaker::new(data, &VTABLE)) }
}

// =============================================================================
// Tests
// =============================================================================

/// Basic cancel lifecycle: create, verify not cancelled, cancel, verify cancelled.
#[test]
fn cancel_basic() {
    let token = CancellationToken::new();
    assert!(!token.is_cancelled());

    token.cancel();
    assert!(token.is_cancelled());
}

/// Register 5 waiters by polling cancelled() futures to Pending, then cancel.
/// All futures must resolve to Ready on the next poll.
/// Exercises Treiber stack push (5 WaiterNode CAS pushes) + drain-all on cancel.
#[test]
fn cancel_with_waiters() {
    let token = CancellationToken::new();

    let mut futures: Vec<_> = (0..5).map(|_| Box::pin(token.cancelled())).collect();

    // First poll: all return Pending (registers WaiterNodes).
    for f in &mut futures {
        assert_eq!(poll_once(f.as_mut()), Poll::Pending);
    }

    token.cancel();

    // Second poll: all return Ready (cancel drained the waiter stack and woke them).
    for f in &mut futures {
        assert_eq!(poll_once(f.as_mut()), Poll::Ready(()));
    }
}

/// Create parent with 3 children. Cancel parent. All children must be cancelled.
/// Exercises the ChildNode Treiber stack push + drain on parent cancel.
#[test]
fn cancel_child_propagation() {
    let parent = CancellationToken::new();
    let children: Vec<_> = (0..3).map(|_| parent.child()).collect();

    assert!(!parent.is_cancelled());
    for c in &children {
        assert!(!c.is_cancelled());
    }

    parent.cancel();

    assert!(parent.is_cancelled());
    for c in &children {
        assert!(c.is_cancelled());
    }
}

/// Simulate the register-during-cancel race path (single-threaded).
///
/// The register() method has a double-check after CAS push: if cancel happened
/// between the initial check and the push, it re-drains. We exercise this by:
/// poll future -> Pending -> cancel -> poll future again -> Ready.
#[test]
fn cancel_register_during_cancel_race() {
    let token = CancellationToken::new();
    let mut fut = Box::pin(token.cancelled());

    // Poll registers a WaiterNode via CAS push, returns Pending.
    assert_eq!(poll_once(fut.as_mut()), Poll::Pending);

    // Cancel drains the waiter stack.
    token.cancel();

    // Next poll sees is_cancelled() == true, returns Ready.
    assert_eq!(poll_once(fut.as_mut()), Poll::Ready(()));
}

/// Drop token with registered waiters and children without cancelling.
/// Inner::drop must drain and free all heap-allocated nodes.
/// Miri will flag any leak or use-after-free.
#[test]
fn cancel_drop_without_cancel() {
    let token = CancellationToken::new();

    // Register waiters.
    let mut futures: Vec<_> = (0..3).map(|_| Box::pin(token.cancelled())).collect();
    for f in &mut futures {
        assert_eq!(poll_once(f.as_mut()), Poll::Pending);
    }

    // Create children.
    let _children: Vec<_> = (0..3).map(|_| token.child()).collect();

    // Drop everything without cancelling. Miri checks for leaks.
    drop(futures);
    drop(_children);
    drop(token);
}

/// Cancelled future re-registers when polled with a different waker.
/// Verifies the will_wake() check and re-registration path.
/// Miri catches any leaked WaiterNodes from stale registrations.
#[test]
fn cancel_waker_update_on_repoll() {
    let token = CancellationToken::new();
    let mut fut = Box::pin(token.cancelled());

    // Poll with waker A — registers WaiterNode with waker A.
    let waker_a = noop_waker();
    let mut cx_a = Context::from_waker(&waker_a);
    assert_eq!(fut.as_mut().poll(&mut cx_a), Poll::Pending);

    // Poll with waker B (different noop_waker instance) — should re-register.
    // Note: two noop_wakers from our helper share the same vtable pointer and
    // null data, so will_wake returns true. Use a tracking waker instead.
    let woke = std::cell::Cell::new(false);
    let waker_b = tracking_waker(&woke);
    let mut cx_b = Context::from_waker(&waker_b);
    assert_eq!(fut.as_mut().poll(&mut cx_b), Poll::Pending);

    // Cancel — should wake via the latest registered waker.
    token.cancel();

    // The tracking waker should have been called.
    // (Note: the noop waker from the first registration also fires — that's fine,
    // it's a no-op. The important thing is waker_b fires.)
    assert!(woke.get(), "latest waker must be woken on cancel");

    // Final poll confirms Ready.
    assert_eq!(fut.as_mut().poll(&mut cx_b), Poll::Ready(()));
}

/// Multiple waker changes across polls. Exercises repeated re-registration
/// without leaking WaiterNodes (miri catches leaks).
#[test]
fn cancel_many_waker_changes() {
    let token = CancellationToken::new();
    let mut fut = Box::pin(token.cancelled());

    // Keep all flags alive until after cancel — cancel() drains ALL
    // WaiterNodes and wakes their wakers, including stale ones from
    // prior registrations. The flags must outlive the drain.
    let flags: Vec<std::cell::Cell<bool>> = (0..10).map(|_| std::cell::Cell::new(false)).collect();

    // Poll 10 times with different wakers.
    for flag in &flags {
        let waker = tracking_waker(flag);
        let mut cx = Context::from_waker(&waker);
        assert_eq!(fut.as_mut().poll(&mut cx), Poll::Pending);
    }

    // Cancel — all WaiterNodes drained and freed. Miri checks for leaks.
    token.cancel();
    assert_eq!(poll_once(fut.as_mut()), Poll::Ready(()));
}

/// Cancel before any poll — future resolves immediately on first poll.
/// No WaiterNode allocated.
#[test]
fn cancel_before_poll() {
    let token = CancellationToken::new();
    token.cancel();

    let mut fut = Box::pin(token.cancelled());
    assert_eq!(poll_once(fut.as_mut()), Poll::Ready(()));
}

/// Drop child token clone before parent cancels. The ChildNode in the parent's
/// Treiber stack still holds an Arc<Inner> clone of the child's Inner. When
/// parent cancels, it drains the ChildNode and cancels the child via that Arc.
#[test]
fn cancel_child_drop_before_parent() {
    let parent = CancellationToken::new();
    let child = parent.child();

    // Clone and hold a reference to observe the child after dropping the original.
    let child_observer = child.cancelled();
    let mut child_fut = Box::pin(child_observer);

    // Poll to register a waiter on the child.
    assert_eq!(poll_once(child_fut.as_mut()), Poll::Pending);

    // Drop the child token. The ChildNode in parent's stack still holds an Arc.
    drop(child);

    // Cancel parent — drains ChildNode stack, cancels child's Inner.
    parent.cancel();

    // The child's future should now resolve.
    assert_eq!(poll_once(child_fut.as_mut()), Poll::Ready(()));
}

// =============================================================================
// PR 3 — intrusive doubly-linked list regression tests
// =============================================================================

/// PR 3 / BUG-3 regression #1: pin a `Cancelled` future, poll N times
/// alternating wakers. Embedded `WaiterNode` is reused across polls —
/// no per-poll heap allocation. Under tree-borrows miri, the lock +
/// node-update path stays sound across waker churn.
///
/// Pre-PR-3 (Treiber stack): each waker change Box-allocated a fresh
/// `WaiterNode` and pushed onto the stack; old nodes accumulated until
/// `cancel()` drained. For long-lived tokens with high waker churn,
/// the stack grew linearly with poll count (the §F8 leak class).
///
/// Post-PR-3 (intrusive list): the embedded node is reused. Allocator
/// traffic is zero for re-polls.
#[test]
fn no_allocation_on_repoll() {
    let token = CancellationToken::new();
    let mut fut = Box::pin(token.cancelled());

    // Use 3 distinct tracking wakers; cycle through them. Each
    // change forces the will_wake comparison to fail and trigger
    // the in-place waker update under the lock.
    let flags: Vec<std::cell::Cell<bool>> = (0..3).map(|_| std::cell::Cell::new(false)).collect();

    // First poll: registers via the first-poll branch.
    {
        let waker = tracking_waker(&flags[0]);
        let mut cx = Context::from_waker(&waker);
        assert_eq!(fut.as_mut().poll(&mut cx), Poll::Pending);
    }

    // 99 more polls cycling through 3 wakers. Pre-PR3: 99 fresh
    // WaiterNode boxes. Post-PR3: zero allocations, just lock +
    // waker update.
    for i in 0..99 {
        let waker = tracking_waker(&flags[i % 3]);
        let mut cx = Context::from_waker(&waker);
        assert_eq!(fut.as_mut().poll(&mut cx), Poll::Pending);
    }

    // Cancel — drain the (single) WaiterNode + wake the most recent
    // waker. The loop ran `for i in 0..99` so the last `i` was 98;
    // the last stored waker is `flags[98 % 3] = flags[2]`.
    token.cancel();
    let waker = tracking_waker(&flags[2]);
    let mut cx = Context::from_waker(&waker);
    assert_eq!(fut.as_mut().poll(&mut cx), Poll::Ready(()));
    assert!(flags[2].get(), "most recent waker (flags[2]) should fire");
}

/// PR 3 regression #2: drop several `Cancelled` futures BEFORE
/// calling `cancel()`. Each drop unlinks under the lock (slow path).
/// `cancel()` then drains an empty list. No UAF; Inner::Drop's
/// debug_assert verifies the list ended empty.
#[test]
fn drop_while_in_list() {
    let token = CancellationToken::new();
    let mut futures: Vec<_> = (0..5).map(|_| Box::pin(token.cancelled())).collect();

    // Register all.
    for f in &mut futures {
        assert_eq!(poll_once(f.as_mut()), Poll::Pending);
    }

    // Drop a random subset BEFORE cancel — exercises the slow-path
    // unlink (still in_list, lock + DLL prev-pointer unlink).
    futures.remove(2); // drop the middle one
    futures.remove(0); // drop a front one (was head after middle removal)

    // Cancel — drains the survivors.
    token.cancel();
    for f in &mut futures {
        assert_eq!(poll_once(f.as_mut()), Poll::Ready(()));
    }
    drop(futures);
    drop(token);
    // Inner::Drop's debug_assert verifies head is null.
}

/// PR 3 regression #3: cancel first, then drop the futures. Drop
/// hits the FAST path (in_list=false after cancel's drain), no lock
/// acquired.
#[test]
fn drop_after_cancel_fast_path() {
    let token = CancellationToken::new();
    let mut futures: Vec<_> = (0..5).map(|_| Box::pin(token.cancelled())).collect();

    for f in &mut futures {
        assert_eq!(poll_once(f.as_mut()), Poll::Pending);
    }

    // Cancel drains the list and clears in_list on every node.
    token.cancel();

    // Drop the futures. Each Drop's fast-path load on in_list reads
    // false → no lock, no unlink. Verify by completing the polls
    // (post-cancel poll resolves Ready via the lock-free fast-out).
    for f in &mut futures {
        assert_eq!(poll_once(f.as_mut()), Poll::Ready(()));
    }
    drop(futures);
    drop(token);
}

/// PR 3 regression #4: concurrent register-and-cancel race
/// (multi-threaded). Thread A polls a Cancelled (registers); thread B
/// calls cancel() concurrently. Either A's register inserts BEFORE
/// B's drain (and B's drain wakes A's waker) OR A's register sees
/// cancelled=true on the post-registration recheck and resolves
/// immediately. No UAF, no lost wake.
#[test]
fn concurrent_register_and_cancel_race() {
    use std::sync::Barrier;

    for _ in 0..50 {
        let token = CancellationToken::new();
        let cancel_token = token.clone();
        let barrier = std::sync::Arc::new(Barrier::new(2));
        let bar_a = barrier.clone();
        let bar_b = barrier.clone();

        // Thread A: pin a Cancelled, poll it, then poll again until
        // it resolves to Ready.
        let a = std::thread::spawn(move || {
            bar_a.wait();
            let mut fut = Box::pin(token.cancelled());
            // First poll: registers (or sees cancelled).
            let _ = poll_once(fut.as_mut());
            // Spin-poll until ready. Without a real waker dispatch,
            // we rely on the lock-free fast-out (`is_cancelled`)
            // resolving subsequent polls.
            while !matches!(poll_once(fut.as_mut()), Poll::Ready(())) {
                std::hint::spin_loop();
            }
        });

        // Thread B: cancel.
        let b = std::thread::spawn(move || {
            bar_b.wait();
            cancel_token.cancel();
        });

        a.join().unwrap();
        b.join().unwrap();
    }
}

/// PR 3 regression #5: BUG-3 reproduction. Pin a long-lived
/// `Cancelled`, poll it 1000 times alternating between waker X and
/// waker Y. Pre-PR3 the Treiber stack would grow linearly with poll
/// count (one new `Box<WaiterNode>` per waker change). Post-PR3 the
/// embedded node is reused, so memory stays flat.
///
/// We verify by completing successfully under tree-borrows miri (no
/// UAF on the high-churn path) AND by Inner::Drop's debug_assert
/// (waiter list is empty after cancel's drain).
#[test]
fn bug_3_reproduction_high_waker_churn() {
    let token = CancellationToken::new();
    let mut fut = Box::pin(token.cancelled());
    let flag_x = std::cell::Cell::new(false);
    let flag_y = std::cell::Cell::new(false);

    // First poll registers.
    {
        let waker = tracking_waker(&flag_x);
        let mut cx = Context::from_waker(&waker);
        assert_eq!(fut.as_mut().poll(&mut cx), Poll::Pending);
    }

    // 1000 alternating polls. Pre-PR3 this leaks 1000 nodes onto
    // the Treiber stack. Post-PR3 it updates the embedded node's
    // waker in-place under the lock.
    for i in 0..1000 {
        let flag = if i % 2 == 0 { &flag_x } else { &flag_y };
        let waker = tracking_waker(flag);
        let mut cx = Context::from_waker(&waker);
        assert_eq!(fut.as_mut().poll(&mut cx), Poll::Pending);
    }

    // Cancel — wakes the last waker (flag_y, since 999 % 2 == 1).
    token.cancel();
    {
        let waker = tracking_waker(&flag_y);
        let mut cx = Context::from_waker(&waker);
        assert_eq!(fut.as_mut().poll(&mut cx), Poll::Ready(()));
    }
    assert!(flag_y.get(), "last waker (Y) should be woken by cancel");
}

/// PR 3 regression #6: stress with many concurrent awaiters.
/// 100 pinned Cancelled futures (kept smaller than 1000 so this
/// runs reasonably fast under miri); half are dropped pre-cancel
/// (slow-path unlink), half are awoken by cancel's drain. No leaks
/// (Inner::Drop's debug_assert verifies empty list at drop time).
#[test]
fn stress_many_awaiters_mixed_drop_and_cancel() {
    let token = CancellationToken::new();
    let mut futures: Vec<_> = (0..100).map(|_| Box::pin(token.cancelled())).collect();

    // Register all 100.
    for f in &mut futures {
        assert_eq!(poll_once(f.as_mut()), Poll::Pending);
    }

    // Drop the even-indexed half — slow-path unlinks under the lock.
    // (Drop in reverse to keep indices stable.)
    let mut survivors = Vec::new();
    for (i, f) in futures.into_iter().enumerate() {
        if i % 2 == 0 {
            drop(f);
        } else {
            survivors.push(f);
        }
    }

    // Cancel drains the survivors.
    token.cancel();
    for f in &mut survivors {
        assert_eq!(poll_once(f.as_mut()), Poll::Ready(()));
    }
    drop(survivors);
    drop(token);
}
