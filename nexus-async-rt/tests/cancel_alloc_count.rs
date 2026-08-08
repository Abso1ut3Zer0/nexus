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
//! PR 3 / BUG-3 — allocation-counting regression test.
//!
//! Pre-PR-3 (Treiber stack of `Box<WaiterNode>`): each `Cancelled::poll`
//! that observed a changed waker `Box::new`'d a fresh `WaiterNode` and
//! pushed onto the stack. Old nodes accumulated until `cancel()` drained
//! them. Long-lived tokens awaited via `select!`/`Timeout` patterns
//! (which churn wakers per outer poll) leaked one node per re-poll.
//!
//! Post-PR-3 (intrusive doubly-linked list, embedded `WaiterNode`): the
//! node is reused across polls. Allocation count for re-polls is zero.
//!
//! This test installs a counting global allocator, polls a pinned
//! `Cancelled` future N times across changing wakers, and asserts the
//! observed allocation count stays bounded — the polls themselves
//! produce zero new allocations after the first poll's setup.
//!
//! **Lives in its own test binary** because `#[global_allocator]` is
//! process-wide; mixing it with the broader test suite would affect
//! every other test's allocator behavior. Cargo runs each
//! `tests/*.rs` file as a separate binary, isolating the allocator
//! installation.

use std::alloc::{GlobalAlloc, Layout, System};
use std::pin::Pin;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};

use nexus_async_rt::CancellationToken;

// =============================================================================
// Counting global allocator
// =============================================================================

struct CountingAllocator {
    counting_active: AtomicBool,
    allocs: AtomicUsize,
}

// SAFETY: delegates to the system allocator; alloc/dealloc contract is upheld.
unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if self.counting_active.load(Ordering::Relaxed) {
            self.allocs.fetch_add(1, Ordering::Relaxed);
        }
        // SAFETY: layout is non-zero; pointer returned by alloc is valid.
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // SAFETY: layout is non-zero; pointer returned by alloc is valid.
        unsafe { System.dealloc(ptr, layout) };
    }
}

#[global_allocator]
static ALLOC: CountingAllocator = CountingAllocator {
    counting_active: AtomicBool::new(false),
    allocs: AtomicUsize::new(0),
};

fn start_counting() {
    ALLOC.allocs.store(0, Ordering::Relaxed);
    ALLOC.counting_active.store(true, Ordering::Relaxed);
}

fn stop_counting() -> usize {
    ALLOC.counting_active.store(false, Ordering::Relaxed);
    ALLOC.allocs.load(Ordering::Relaxed)
}

// =============================================================================
// Tracking waker (distinct data → distinct will_wake identity)
// =============================================================================

fn tracking_waker(flag: &std::cell::Cell<bool>) -> Waker {
    let data = flag as *const std::cell::Cell<bool> as *const ();
    static VTABLE: RawWakerVTable = RawWakerVTable::new(
        |p| RawWaker::new(p, &VTABLE),
        |p| {
            // SAFETY: p is the data pointer set by RawWaker::new from a &Cell<bool>; valid for the waker's lifetime.
            let flag = unsafe { &*(p as *const std::cell::Cell<bool>) };
            flag.set(true);
        },
        |p| {
            // SAFETY: p is the data pointer set by RawWaker::new from a &Cell<bool>; valid for the waker's lifetime.
            let flag = unsafe { &*(p as *const std::cell::Cell<bool>) };
            flag.set(true);
        },
        |_| {},
    );
    // SAFETY: vtable functions match the data pointer layout; Cell<bool> outlives the waker.
    unsafe { Waker::from_raw(RawWaker::new(data, &VTABLE)) }
}

fn poll_with<F: std::future::Future>(f: Pin<&mut F>, w: &Waker) -> Poll<F::Output> {
    let mut cx = Context::from_waker(w);
    f.poll(&mut cx)
}

// =============================================================================
// Test
// =============================================================================

/// Repoll a pinned `Cancelled` 100 times across 5 distinct wakers.
/// Pre-PR-3: 100 `Box<WaiterNode>` allocations. Post-PR-3: zero
/// allocations within the loop (the embedded node is reused).
///
/// The test asserts the loop-only allocation count is zero. Setup
/// (constructing the future, the wakers, the flags) happens before
/// counting starts; cleanup happens after counting stops.
#[test]
fn no_allocation_on_repoll_across_wakers() {
    let token = CancellationToken::new();

    // Setup outside the counted region.
    let flags: Vec<std::cell::Cell<bool>> = (0..5).map(|_| std::cell::Cell::new(false)).collect();
    let wakers: Vec<Waker> = flags.iter().map(tracking_waker).collect();

    let mut fut = Box::pin(token.cancelled());
    // First poll registers the embedded WaiterNode under the lock.
    // This will allocate Cancelled-internal state if it does any
    // heap traffic, so we count it OUTSIDE the no-alloc assertion.
    assert!(matches!(poll_with(fut.as_mut(), &wakers[0]), Poll::Pending));

    // Warmup: cycle through every waker twice before measurement.
    // Some platforms (notably glibc with per-thread `tcache`) lazily
    // initialize allocator state on first access to a given size
    // class, and the standard library can lazily initialize per-waker
    // vtable resolution caches. Without warmup, the first transition
    // to each new waker can record a one-time allocation that has
    // nothing to do with `Cancelled`'s loop. With warmup, every
    // codepath the counted loop will hit has been exercised at least
    // once, so the counted region measures genuine steady-state
    // allocation behavior — which should be zero.
    for _ in 0..2 {
        for waker in &wakers {
            assert!(matches!(poll_with(fut.as_mut(), waker), Poll::Pending));
        }
    }

    // Now the heavy loop. Pre-PR-3 this would Box::new a fresh
    // WaiterNode every iteration where the waker changed (effectively
    // every iteration since we cycle through 5 distinct wakers).
    start_counting();
    for i in 0..100 {
        assert!(matches!(
            poll_with(fut.as_mut(), &wakers[i % 5]),
            Poll::Pending
        ));
    }
    let allocs = stop_counting();

    assert_eq!(
        allocs, 0,
        "PR 3 (BUG-3 fix): 100 re-polls across cycling wakers must \
         allocate 0 times. Pre-fix this was 100 (one Box<WaiterNode> \
         per re-poll). Got {allocs}."
    );

    // Cleanup outside the counted region.
    token.cancel();
    let _ = poll_with(fut.as_mut(), &wakers[0]);
}
