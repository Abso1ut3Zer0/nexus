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
//! Stress tests for JoinHandle lifecycle paths.
//!
//! Randomized spawn/await/abort/detach patterns with drop counters
//! to verify no leaks, no double-drops, no use-after-free.
//!
//! Run: `cargo test -p nexus-async-rt --test join_handle_stress --release`

use std::cell::Cell;
use std::future::Future;
use std::pin::Pin;
use std::rc::Rc;
use std::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};

use nexus_async_rt::Executor;

// =============================================================================
// Helpers
// =============================================================================

fn test_executor() -> Executor {
    Executor::new(256)
}

fn noop_waker() -> Waker {
    static VTABLE: RawWakerVTable =
        RawWakerVTable::new(|p| RawWaker::new(p, &VTABLE), |_| {}, |_| {}, |_| {});
    // SAFETY: the vtable functions are all no-ops; the null data pointer is never dereferenced.
    unsafe { Waker::from_raw(RawWaker::new(std::ptr::null(), &VTABLE)) }
}

/// Drop counter with a shared count.
struct DropTracker {
    count: Rc<Cell<u32>>,
    value: u64,
}

impl DropTracker {
    fn new(count: Rc<Cell<u32>>, value: u64) -> Self {
        Self { count, value }
    }
}

impl Drop for DropTracker {
    fn drop(&mut self) {
        self.count.set(self.count.get() + 1);
    }
}

// =============================================================================
// Exactly-once drop across all lifecycle paths
// =============================================================================

/// Path 1: spawn → poll → read output → drop handle
#[test]
fn drop_once_normal_path() {
    for _ in 0..1000 {
        let count = Rc::new(Cell::new(0u32));
        let c = count.clone();
        let mut exec = test_executor();

        let mut handle = exec.spawn_boxed(async move { DropTracker::new(c, 42) });
        exec.poll();

        let waker = noop_waker();
        let mut cx = Context::from_waker(&waker);
        let tracker = match Pin::new(&mut handle).poll(&mut cx) {
            Poll::Ready(t) => t,
            Poll::Pending => panic!("expected Ready"),
        };
        assert_eq!(tracker.value, 42);
        drop(tracker);
        assert_eq!(count.get(), 1, "output dropped exactly once (by user)");

        drop(handle);
        // JoinHandle drop sees OUTPUT_TAKEN, skips drop_fn.
        assert_eq!(count.get(), 1, "no extra drops from JoinHandle");
    }
}

/// Path 2: spawn → poll → detach (drop handle without reading)
#[test]
fn drop_once_detach_after_completion() {
    for _ in 0..1000 {
        let count = Rc::new(Cell::new(0u32));
        let c = count.clone();
        let mut exec = test_executor();

        let handle = exec.spawn_boxed(async move { DropTracker::new(c, 99) });
        exec.poll(); // task completes
        assert_eq!(count.get(), 0, "output alive in slot");

        drop(handle); // JoinHandle drops output via drop_fn
        assert_eq!(count.get(), 1, "output dropped exactly once");
    }
}

/// Path 3: spawn → detach → poll (task completes after handle dropped)
#[test]
fn drop_once_detach_before_completion() {
    for _ in 0..1000 {
        let count = Rc::new(Cell::new(0u32));
        let c = count.clone();
        let mut exec = test_executor();

        let handle = exec.spawn_boxed(async move { DropTracker::new(c, 7) });
        drop(handle); // detach — clears HAS_JOIN

        exec.poll(); // complete_task sees !HAS_JOIN, drops output
        assert_eq!(
            count.get(),
            1,
            "output dropped exactly once by complete_task"
        );
    }
}

/// Path 4: spawn → abort → poll (future dropped, no output)
#[test]
fn drop_future_on_abort() {
    for _ in 0..1000 {
        let future_drop_count = Rc::new(Cell::new(0u32));
        let fc = future_drop_count.clone();
        let mut exec = test_executor();

        let capture = DropTracker::new(fc, 0);
        let handle = exec.spawn_boxed(async move {
            // capture is moved into the future's state — dropped when future drops.
            let _keep = &capture;
            std::future::pending::<u64>().await
        });

        let _ = handle.abort(); // consumes handle
        exec.poll();
        assert!(
            future_drop_count.get() >= 1,
            "future's captures must be dropped on abort"
        );
    }
}

// =============================================================================
// Interleaved spawn/poll/detach/abort — randomized
// =============================================================================

#[test]
fn interleaved_lifecycle_operations() {
    // Use a simple PRNG for reproducibility.
    let mut rng = SimpleRng::new(0xDEAD_BEEF);

    for _ in 0..100 {
        let mut exec = test_executor();
        let mut handles = Vec::new();
        let mut drop_counts: Vec<Rc<Cell<u32>>> = Vec::new();

        // Spawn 10-50 tasks
        let n = 10 + (rng.next() % 41) as usize;
        for i in 0..n {
            let count = Rc::new(Cell::new(0u32));
            drop_counts.push(count.clone());
            let c = count;
            handles.push(Some(
                exec.spawn_boxed(async move { DropTracker::new(c, i as u64) }),
            ));
        }

        // Randomly abort, detach, or keep some handles
        for handle_opt in &mut handles {
            match rng.next() % 3 {
                0 => {
                    // Abort
                    if let Some(h) = handle_opt.take() {
                        let _ = h.abort(); // consumes h
                    }
                }
                1 => {
                    // Detach
                    let _ = handle_opt.take();
                }
                _ => {} // Keep for reading
            }
        }

        // Poll to completion
        for _ in 0..10 {
            exec.poll();
            if exec.task_count() == 0 {
                break;
            }
        }

        // Read remaining handles
        let waker = noop_waker();
        let mut cx = Context::from_waker(&waker);
        for handle_opt in &mut handles {
            if let Some(h) = handle_opt.take() {
                if h.is_finished() {
                    let mut h = h;
                    let _ = Pin::new(&mut h).poll(&mut cx);
                    drop(h);
                } else {
                    drop(h);
                }
            }
        }

        // Drain deferred frees
        exec.poll();
        drop(exec);

        // Verify no double-drops
        for (i, count) in drop_counts.iter().enumerate() {
            assert!(
                count.get() <= 1,
                "task {i}: output dropped {} times (expected 0 or 1)",
                count.get()
            );
        }
    }
}

// =============================================================================
// Output size variations
// =============================================================================

#[test]
fn various_output_sizes() {
    #[allow(clippy::vec_init_then_push)]
    let sizes_and_values: Vec<Box<dyn FnOnce() -> Box<dyn std::any::Any>>> = vec![
        // ZST
        Box::new(|| Box::new(())),
        // u8
        Box::new(|| Box::new(42u8)),
        // u64
        Box::new(|| Box::new(0xDEAD_BEEFu64)),
        // Small struct
        Box::new(|| Box::new((1u32, 2u32, 3u32))),
        // String (heap)
        Box::new(|| Box::new(String::from("hello"))),
        // Vec (heap)
        Box::new(|| Box::new(vec![1u64; 100])),
        // Large array
        Box::new(|| Box::new([0xABu8; 512])),
    ];

    for factory in sizes_and_values {
        let _val = factory();
    }

    // Specific typed tests for miri-relevant paths:
    let mut exec = test_executor();

    // ZST
    let h = exec.spawn_boxed(async {});
    exec.poll();
    drop(h);

    // Small
    let h = exec.spawn_boxed(async { 42u8 });
    exec.poll();
    drop(h);

    // Medium
    let h = exec.spawn_boxed(async { [0u64; 8] });
    exec.poll();
    drop(h);

    // Large (output > future)
    let h = exec.spawn_boxed(async { [0u8; 1024] });
    exec.poll();
    drop(h);

    // Heap-allocated
    let h = exec.spawn_boxed(async { vec![String::from("a"); 50] });
    exec.poll();
    drop(h);

    exec.poll();
}

// =============================================================================
// Rapid spawn + drain cycles
// =============================================================================

#[test]
fn rapid_spawn_drain() {
    let mut exec = test_executor();
    let total_drops = Rc::new(Cell::new(0u32));

    for cycle in 0..100 {
        let count = Rc::new(Cell::new(0u32));
        let mut handles = Vec::new();

        for i in 0..10 {
            let c = count.clone();
            let td = total_drops.clone();
            handles.push(exec.spawn_boxed(async move {
                let t = DropTracker::new(c, (cycle * 10 + i) as u64);
                td.set(td.get()); // touch td to keep it alive
                t
            }));
        }

        exec.poll();

        // Drop all handles (output dropped via drop_fn)
        handles.clear();

        // Drain deferred frees
        exec.poll();

        assert_eq!(count.get(), 10, "cycle {cycle}: all 10 outputs dropped");
    }
}

// =============================================================================
// Simple PRNG (no deps)
// =============================================================================

struct SimpleRng(u64);

impl SimpleRng {
    fn new(seed: u64) -> Self {
        Self(seed)
    }

    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}
