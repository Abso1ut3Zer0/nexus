//! Index-based SPSC ring buffer.
//!
//! Uses cached head/tail indices with separate cache lines. Optimized for
//! ping-pong latency on multi-socket systems where bidirectional cache line
//! bouncing of slot-based designs is more expensive.
//!
//! # When to use
//!
//! - Request-response patterns (1 message in flight)
//! - Multi-socket / NUMA systems
//! - Tick-to-trade latency critical paths
//!
//! # Trade-offs vs slot-based
//!
//! | Metric | index | slot |
//! |--------|-------|------|
//! | Ping-pong latency | Better | Worse |
//! | Streaming throughput | Worse | Better |

use std::fmt;
use std::mem::ManuallyDrop;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use crossbeam_utils::CachePadded;

use crate::Full;

pub fn ring_buffer<T>(capacity: usize) -> (Producer<T>, Consumer<T>) {
    assert!(capacity > 0, "capacity must be non-zero");

    let capacity = capacity.next_power_of_two();
    let mask = capacity - 1;

    let mut slots = ManuallyDrop::new(Vec::<T>::with_capacity(capacity));
    let buffer = slots.as_mut_ptr();

    let shared = Arc::new(Shared {
        tail: CachePadded::new(AtomicUsize::new(0)),
        head: CachePadded::new(AtomicUsize::new(0)),
        buffer,
        mask,
    });

    (
        Producer {
            local_tail: 0,
            cached_head: 0,
            buffer,
            mask,
            shared: Arc::clone(&shared),
        },
        Consumer {
            local_head: 0,
            cached_tail: 0,
            buffer,
            mask,
            shared,
        },
    )
}

#[repr(C)]
struct Shared<T> {
    tail: CachePadded<AtomicUsize>,
    head: CachePadded<AtomicUsize>,
    buffer: *mut T,
    mask: usize,
}

unsafe impl<T: Send> Send for Shared<T> {}
unsafe impl<T: Send> Sync for Shared<T> {}

impl<T> Drop for Shared<T> {
    fn drop(&mut self) {
        let head = self.head.load(Ordering::Relaxed);
        let tail = self.tail.load(Ordering::Relaxed);

        let mut i = head;
        while i != tail {
            unsafe { self.buffer.add(i & self.mask).drop_in_place() };
            i = i.wrapping_add(1);
        }

        unsafe {
            let capacity = self.mask + 1;
            let _ = Vec::from_raw_parts(self.buffer, 0, capacity);
        }
    }
}

#[repr(C)]
pub struct Producer<T> {
    local_tail: usize,
    cached_head: usize,
    buffer: *mut T,
    mask: usize,
    shared: Arc<Shared<T>>,
}

unsafe impl<T: Send> Send for Producer<T> {}

impl<T> Producer<T> {
    #[inline]
    #[must_use = "push returns Err if full, which should be handled"]
    pub fn push(&mut self, value: T) -> Result<(), Full<T>> {
        let tail = self.local_tail;

        if tail.wrapping_sub(self.cached_head) > self.mask {
            self.cached_head = self.shared.head.load(Ordering::Acquire);
            if tail.wrapping_sub(self.cached_head) > self.mask {
                return Err(Full(value));
            }
        }

        unsafe { self.buffer.add(tail & self.mask).write(value) };

        self.local_tail = tail.wrapping_add(1);
        self.shared.tail.store(self.local_tail, Ordering::Release);

        Ok(())
    }

    #[inline]
    pub fn capacity(&self) -> usize {
        self.mask + 1
    }

    #[inline]
    pub fn is_disconnected(&self) -> bool {
        Arc::strong_count(&self.shared) == 1
    }
}

impl<T> fmt::Debug for Producer<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Producer")
            .field("capacity", &self.capacity())
            .finish_non_exhaustive()
    }
}

#[repr(C)]
pub struct Consumer<T> {
    local_head: usize,
    cached_tail: usize,
    buffer: *mut T,
    mask: usize,
    shared: Arc<Shared<T>>,
}

unsafe impl<T: Send> Send for Consumer<T> {}

impl<T> Consumer<T> {
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        let head = self.local_head;

        if head == self.cached_tail {
            self.cached_tail = self.shared.tail.load(Ordering::Acquire);
            if head == self.cached_tail {
                return None;
            }
        }

        let value = unsafe { self.buffer.add(head & self.mask).read() };

        self.local_head = head.wrapping_add(1);
        self.shared.head.store(self.local_head, Ordering::Release);

        Some(value)
    }

    #[inline]
    pub fn capacity(&self) -> usize {
        self.mask + 1
    }

    #[inline]
    pub fn is_disconnected(&self) -> bool {
        Arc::strong_count(&self.shared) == 1
    }
}

impl<T> fmt::Debug for Consumer<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Consumer")
            .field("capacity", &self.capacity())
            .finish_non_exhaustive()
    }
}
