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
//! Spike: compare Vec-based ready queue vs intrusive MPSC queue.
//!
//! Measures the cost of CAS-based push vs Vec push for the executor's
//! ready queue. If the intrusive MPSC is within ~5 cycles of the Vec,
//! we can unify local + cross-thread wake into one queue.

use std::hint::black_box;
use std::sync::atomic::{AtomicPtr, Ordering};
use std::time::Instant;

// =============================================================================
// Intrusive MPSC queue (Vyukov style)
// =============================================================================

/// Minimal node for the spike. In the real impl this would be a field
/// in the task header.
#[repr(C)]
struct Node {
    next: AtomicPtr<Node>,
    _payload: u64, // simulate task data
}

impl Node {
    fn new() -> Self {
        Self {
            next: AtomicPtr::new(std::ptr::null_mut()),
            _payload: 0,
        }
    }
}

/// Vyukov MPSC queue. Lock-free producers, single consumer.
struct IntrusiveMpsc {
    head: *mut Node,       // consumer reads from here
    tail: AtomicPtr<Node>, // producers CAS here
    stub: Box<Node>,       // sentinel
}

impl IntrusiveMpsc {
    fn new() -> Self {
        let stub = Box::new(Node::new());
        let stub_ptr = (&raw const *stub).cast_mut();
        Self {
            head: stub_ptr,
            tail: AtomicPtr::new(stub_ptr),
            stub,
        }
    }

    /// Push a node (producer side). Thread-safe.
    #[inline]
    fn push(&self, node: *mut Node) {
        // SAFETY: node is a valid, live node not in any queue.
        unsafe { (*node).next.store(std::ptr::null_mut(), Ordering::Relaxed) };
        let prev = self.tail.swap(node, Ordering::AcqRel);
        // SAFETY: prev was either the stub or a previously pushed node.
        unsafe { (*prev).next.store(node, Ordering::Release) };
    }

    /// Pop a node (consumer side). Single-threaded.
    #[inline]
    fn pop(&mut self) -> *mut Node {
        let mut head = self.head;
        // SAFETY: head points to a valid Node (stub or previously pushed); single consumer ensures exclusive access.
        let mut next = unsafe { (*head).next.load(Ordering::Acquire) };

        // Skip stub
        let stub_ptr = (&raw const *self.stub).cast_mut();
        if head == stub_ptr {
            if next.is_null() {
                return std::ptr::null_mut();
            }
            self.head = next;
            head = next;
            // SAFETY: head was just updated to next (a non-null, valid Node); single consumer ensures exclusive access.
            next = unsafe { (*head).next.load(Ordering::Acquire) };
        }

        if !next.is_null() {
            self.head = next;
            return head;
        }

        let tail = self.tail.load(Ordering::Acquire);
        if head != tail {
            return std::ptr::null_mut(); // producer hasn't linked yet
        }

        // Re-insert stub to prevent losing the tail
        self.push(stub_ptr);
        // SAFETY: head is still valid; the stub re-insertion preserves queue invariants; single consumer.
        next = unsafe { (*head).next.load(Ordering::Acquire) };
        if !next.is_null() {
            self.head = next;
            return head;
        }

        std::ptr::null_mut()
    }
}

// =============================================================================
// Benchmarks
// =============================================================================

const ITERS: usize = 1_000_000;
const WARMUP: usize = 100_000;

#[test]
#[ignore]
fn spike_vec_push_pop() {
    let mut queue: Vec<*mut u8> = Vec::with_capacity(64);

    // Warmup
    for i in 0..WARMUP {
        queue.push(i as *mut u8);
    }
    queue.clear();

    // Measure push+pop (simulates: wake pushes, poll drains)
    let start = Instant::now();
    for i in 0..ITERS {
        queue.push(black_box(i as *mut u8));
    }
    let mut drain = Vec::new();
    std::mem::swap(&mut queue, &mut drain);
    for ptr in &drain {
        black_box(*ptr);
    }
    drain.clear();
    let elapsed = start.elapsed();

    let ns_per = elapsed.as_nanos() as f64 / ITERS as f64;
    println!("\n=== Vec push+drain ===");
    println!("  total: {elapsed:?}");
    println!("  per-op: {ns_per:.2} ns");
    println!("  cycles (est @ 3.5GHz): {:.1}", ns_per * 3.5);
}

#[test]
#[ignore]
fn spike_intrusive_mpsc_push_pop() {
    let mut queue = IntrusiveMpsc::new();

    // Pre-allocate nodes (simulates task slab)
    let mut nodes: Vec<Box<Node>> = (0..ITERS).map(|_| Box::new(Node::new())).collect();

    // Warmup
    for node in &mut nodes[..WARMUP] {
        let ptr = &raw mut **node;
        queue.push(ptr);
    }
    loop {
        let p = queue.pop();
        if p.is_null() {
            break;
        }
    }

    // Measure push+pop
    let start = Instant::now();
    for node in &mut nodes {
        let ptr = &raw mut **node;
        queue.push(black_box(ptr));
    }
    let mut count = 0usize;
    loop {
        let p = queue.pop();
        if p.is_null() {
            break;
        }
        black_box(p);
        count += 1;
    }
    let elapsed = start.elapsed();

    let ns_per = elapsed.as_nanos() as f64 / ITERS as f64;
    println!("\n=== Intrusive MPSC push+drain ===");
    println!("  popped: {count}");
    println!("  total: {elapsed:?}");
    println!("  per-op: {ns_per:.2} ns");
    println!("  cycles (est @ 3.5GHz): {:.1}", ns_per * 3.5);
}

#[test]
#[ignore]
fn spike_pingpong_vec() {
    // Simulate executor: push 1, pop 1, push 1, pop 1 (self-waking task)
    let mut queue: Vec<*mut u8> = Vec::with_capacity(64);
    let sentinel = 0xDEAD as *mut u8;

    // Warmup
    for _ in 0..WARMUP {
        queue.push(sentinel);
        queue.pop();
    }

    let start = Instant::now();
    for _ in 0..ITERS {
        queue.push(black_box(sentinel));
        black_box(queue.pop().unwrap());
    }
    let elapsed = start.elapsed();

    let ns_per = elapsed.as_nanos() as f64 / ITERS as f64;
    println!("\n=== Vec ping-pong (push 1, pop 1) ===");
    println!("  per-op: {ns_per:.2} ns");
    println!("  cycles (est @ 3.5GHz): {:.1}", ns_per * 3.5);
}

#[test]
#[ignore]
fn spike_pingpong_intrusive() {
    let mut queue = IntrusiveMpsc::new();
    let mut node = Box::new(Node::new());
    let ptr = &raw mut *node;

    // Warmup
    for _ in 0..WARMUP {
        queue.push(ptr);
        let p = queue.pop();
        assert!(!p.is_null());
    }

    let start = Instant::now();
    for _ in 0..ITERS {
        queue.push(black_box(ptr));
        let p = queue.pop();
        black_box(p);
    }
    let elapsed = start.elapsed();

    let ns_per = elapsed.as_nanos() as f64 / ITERS as f64;
    println!("\n=== Intrusive MPSC ping-pong (push 1, pop 1) ===");
    println!("  per-op: {ns_per:.2} ns");
    println!("  cycles (est @ 3.5GHz): {:.1}", ns_per * 3.5);
}
