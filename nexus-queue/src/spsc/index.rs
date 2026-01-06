//! Single-producer single-consumer queue using cached indices.
//!
//! This is the default implementation.
//!
//! # Design
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────┐
//! │ Shared:                                                     │
//! │   tail: CachePadded<AtomicUsize>   ← Producer writes        │
//! │   head: CachePadded<AtomicUsize>   ← Consumer writes        │
//! │   buffer: *mut T                                            │
//! └─────────────────────────────────────────────────────────────┘
//!
//! ┌─────────────────────┐     ┌─────────────────────┐
//! │ Producer:           │     │ Consumer:           │
//! │   local_tail        │     │   local_head        │
//! │   cached_head       │     │   cached_tail       │
//! └─────────────────────┘     └─────────────────────┘
//! ```
//!
//! Producer and consumer each maintain a cached copy of the other's index,
//! only refreshing from the atomic when the cache indicates the queue is
//! full (producer) or empty (consumer). Head and tail are on separate cache
//! lines to avoid false sharing.
//!
//! # Performance Characteristics
//!
//! This implementation has different performance characteristics than the
//! [`slot`](super::slot) implementation. The key difference is cache line
//! ownership:
//!
//! - **index**: Producer and consumer write to separate cache lines (head/tail)
//! - **slot**: Producer and consumer write to the same cache line (the slot's lap counter)
//!
//! Which performs better depends on your hardware topology, particularly NUMA
//! configuration and cache hierarchy. **Benchmark both on your target hardware.**
//!
//! Enable the alternative with:
//!
//! ```toml
//! [dependencies]
//! nexus-queue = { version = "...", features = ["slot-based"] }
//! ```
//!
//! # Example
//!
//! ```
//! use nexus_queue::spsc;
//!
//! let (mut tx, mut rx) = spsc::ring_buffer::<u64>(1024);
//!
//! tx.push(42).unwrap();
//! assert_eq!(rx.pop(), Some(42));
//! ```

use std::fmt;
use std::mem::ManuallyDrop;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use crossbeam_utils::CachePadded;

use crate::Full;

/// Creates a bounded SPSC ring buffer with the given capacity.
///
/// Capacity is rounded up to the next power of two.
///
/// # Panics
///
/// Panics if `capacity` is zero.
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

/// The producer endpoint of an SPSC queue.
///
/// This endpoint can only push values into the queue.
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
    /// Pushes a value into the queue.
    ///
    /// Returns `Err(Full(value))` if the queue is full, returning ownership
    /// of the value to the caller.
    #[inline]
    #[must_use = "push returns Err if full, which should be handled"]
    pub fn push(&mut self, value: T) -> Result<(), Full<T>> {
        let tail = self.local_tail;

        if tail.wrapping_sub(self.cached_head) > self.mask {
            self.cached_head = self.shared.head.load(Ordering::Relaxed);

            std::sync::atomic::fence(Ordering::Acquire);
            if tail.wrapping_sub(self.cached_head) > self.mask {
                return Err(Full(value));
            }
        }

        unsafe { self.buffer.add(tail & self.mask).write(value) };
        let new_tail = tail.wrapping_add(1);
        std::sync::atomic::fence(Ordering::Release);

        self.shared.tail.store(new_tail, Ordering::Relaxed);
        self.local_tail = new_tail;

        Ok(())
    }

    /// Returns the capacity of the queue.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.mask + 1
    }

    /// Returns `true` if the consumer has been dropped.
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

/// The consumer endpoint of an SPSC queue.
///
/// This endpoint can only pop values from the queue.
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
    /// Pops a value from the queue.
    ///
    /// Returns `None` if the queue is empty.
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        let head = self.local_head;

        if head == self.cached_tail {
            self.cached_tail = self.shared.tail.load(Ordering::Relaxed);
            std::sync::atomic::fence(Ordering::Acquire);

            if head == self.cached_tail {
                return None;
            }
        }

        let value = unsafe { self.buffer.add(head & self.mask).read() };
        let new_head = head.wrapping_add(1);
        std::sync::atomic::fence(Ordering::Release);

        self.shared.head.store(new_head, Ordering::Relaxed);
        self.local_head = new_head;

        Some(value)
    }

    /// Returns the capacity of the queue.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.mask + 1
    }

    /// Returns `true` if the producer has been dropped.
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

#[cfg(test)]
mod tests {
    use super::*;

    // ============================================================================
    // Basic Operations
    // ============================================================================

    #[test]
    fn basic_push_pop() {
        let (mut prod, mut cons) = ring_buffer::<u64>(4);

        assert!(prod.push(1).is_ok());
        assert!(prod.push(2).is_ok());
        assert!(prod.push(3).is_ok());

        assert_eq!(cons.pop(), Some(1));
        assert_eq!(cons.pop(), Some(2));
        assert_eq!(cons.pop(), Some(3));
        assert_eq!(cons.pop(), None);
    }

    #[test]
    fn empty_pop_returns_none() {
        let (_, mut cons) = ring_buffer::<u64>(4);
        assert_eq!(cons.pop(), None);
        assert_eq!(cons.pop(), None);
    }

    #[test]
    fn fill_then_drain() {
        let (mut prod, mut cons) = ring_buffer::<u64>(4);

        for i in 0..4 {
            assert!(prod.push(i).is_ok());
        }

        for i in 0..4 {
            assert_eq!(cons.pop(), Some(i));
        }

        assert_eq!(cons.pop(), None);
    }

    #[test]
    fn push_returns_error_when_full() {
        let (mut prod, _cons) = ring_buffer::<u64>(4);

        assert!(prod.push(1).is_ok());
        assert!(prod.push(2).is_ok());
        assert!(prod.push(3).is_ok());
        assert!(prod.push(4).is_ok());

        let err = prod.push(5).unwrap_err();
        assert_eq!(err.into_inner(), 5);
    }
    // ============================================================================
    // Interleaved Operations
    // ============================================================================

    #[test]
    fn interleaved_no_overwrite() {
        let (mut prod, mut cons) = ring_buffer::<u64>(8);

        for i in 0..1000 {
            assert!(prod.push(i).is_ok());
            assert_eq!(cons.pop(), Some(i));
        }
    }

    #[test]
    fn partial_fill_drain_cycles() {
        let (mut prod, mut cons) = ring_buffer::<u64>(8);

        for round in 0..100 {
            for i in 0..4 {
                assert!(prod.push(round * 4 + i).is_ok());
            }

            for i in 0..4 {
                assert_eq!(cons.pop(), Some(round * 4 + i));
            }
        }
    }

    // ============================================================================
    // Single Slot
    // ============================================================================

    #[test]
    fn single_slot_bounded() {
        let (mut prod, mut cons) = ring_buffer::<u64>(1);

        assert!(prod.push(1).is_ok());
        assert!(prod.push(2).is_err());

        assert_eq!(cons.pop(), Some(1));
        assert!(prod.push(2).is_ok());
    }

    // ============================================================================
    // Disconnection
    // ============================================================================

    #[test]
    fn producer_disconnected() {
        let (prod, cons) = ring_buffer::<u64>(4);

        assert!(!cons.is_disconnected());
        drop(prod);
        assert!(cons.is_disconnected());
    }

    #[test]
    fn consumer_disconnected() {
        let (prod, cons) = ring_buffer::<u64>(4);

        assert!(!prod.is_disconnected());
        drop(cons);
        assert!(prod.is_disconnected());
    }

    // ============================================================================
    // Drop Behavior
    // ============================================================================

    #[test]
    fn drop_cleans_up_remaining() {
        use std::sync::atomic::AtomicUsize;

        static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

        struct DropCounter;
        impl Drop for DropCounter {
            fn drop(&mut self) {
                DROP_COUNT.fetch_add(1, Ordering::SeqCst);
            }
        }

        DROP_COUNT.store(0, Ordering::SeqCst);

        let (mut prod, cons) = ring_buffer::<DropCounter>(4);

        let _ = prod.push(DropCounter);
        let _ = prod.push(DropCounter);
        let _ = prod.push(DropCounter);

        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), 0);

        drop(prod);
        drop(cons);

        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), 3);
    }

    // ============================================================================
    // Cross-Thread
    // ============================================================================

    #[test]
    fn cross_thread_bounded() {
        use std::thread;

        let (mut prod, mut cons) = ring_buffer::<u64>(64);

        let producer = thread::spawn(move || {
            for i in 0..10_000 {
                while prod.push(i).is_err() {
                    std::hint::spin_loop();
                }
            }
        });

        let consumer = thread::spawn(move || {
            let mut received = 0u64;
            while received < 10_000 {
                if cons.pop().is_some() {
                    received += 1;
                } else {
                    std::hint::spin_loop();
                }
            }
            received
        });

        producer.join().unwrap();
        let received = consumer.join().unwrap();
        assert_eq!(received, 10_000);
    }

    // ============================================================================
    // Special Types
    // ============================================================================

    #[test]
    fn zero_sized_type() {
        let (mut prod, mut cons) = ring_buffer::<()>(8);

        let _ = prod.push(());
        let _ = prod.push(());

        assert_eq!(cons.pop(), Some(()));
        assert_eq!(cons.pop(), Some(()));
        assert_eq!(cons.pop(), None);
    }

    #[test]
    fn string_type() {
        let (mut prod, mut cons) = ring_buffer::<String>(4);

        let _ = prod.push("hello".to_string());
        let _ = prod.push("world".to_string());

        assert_eq!(cons.pop(), Some("hello".to_string()));
        assert_eq!(cons.pop(), Some("world".to_string()));
    }

    #[test]
    #[should_panic(expected = "capacity must be non-zero")]
    fn zero_capacity_panics() {
        let _ = ring_buffer::<u64>(0);
    }

    #[test]
    fn large_message_type() {
        #[repr(C, align(64))]
        struct LargeMessage {
            data: [u8; 256],
        }

        let (mut prod, mut cons) = ring_buffer::<LargeMessage>(8);

        let msg = LargeMessage { data: [42u8; 256] };
        assert!(prod.push(msg).is_ok());

        let received = cons.pop().unwrap();
        assert_eq!(received.data[0], 42);
        assert_eq!(received.data[255], 42);
    }

    #[test]
    fn multiple_laps() {
        let (mut prod, mut cons) = ring_buffer::<u64>(4);

        // 10 full laps through 4-slot buffer
        for i in 0..40 {
            assert!(prod.push(i).is_ok());
            assert_eq!(cons.pop(), Some(i));
        }
    }

    #[test]
    fn fifo_order_cross_thread() {
        use std::thread;

        let (mut prod, mut cons) = ring_buffer::<u64>(64);

        let producer = thread::spawn(move || {
            for i in 0..10_000u64 {
                while prod.push(i).is_err() {
                    std::hint::spin_loop();
                }
            }
        });

        let consumer = thread::spawn(move || {
            let mut expected = 0u64;
            while expected < 10_000 {
                if let Some(val) = cons.pop() {
                    assert_eq!(val, expected, "FIFO order violated");
                    expected += 1;
                } else {
                    std::hint::spin_loop();
                }
            }
        });

        producer.join().unwrap();
        consumer.join().unwrap();
    }

    #[test]
    fn stress_high_volume() {
        use std::thread;

        const COUNT: u64 = 1_000_000;

        let (mut prod, mut cons) = ring_buffer::<u64>(1024);

        let producer = thread::spawn(move || {
            for i in 0..COUNT {
                while prod.push(i).is_err() {
                    std::hint::spin_loop();
                }
            }
        });

        let consumer = thread::spawn(move || {
            let mut sum = 0u64;
            let mut received = 0u64;
            while received < COUNT {
                if let Some(val) = cons.pop() {
                    sum = sum.wrapping_add(val);
                    received += 1;
                } else {
                    std::hint::spin_loop();
                }
            }
            sum
        });

        producer.join().unwrap();
        let sum = consumer.join().unwrap();
        assert_eq!(sum, COUNT * (COUNT - 1) / 2);
    }

    #[test]
    fn capacity_rounds_to_power_of_two() {
        let (prod, _) = ring_buffer::<u64>(100);
        assert_eq!(prod.capacity(), 128);

        let (prod, _) = ring_buffer::<u64>(1000);
        assert_eq!(prod.capacity(), 1024);
    }
}
