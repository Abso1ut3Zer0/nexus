//! Single-producer single-consumer (SPSC) bounded ring buffer.
//!
//! This is the fastest queue variant, using only acquire/release semantics
//! with no compare-and-swap operations on the hot path.
//!
//! # Example
//!
//! ```
//! use nexus_queue::spsc::bounded;
//!
//! let (mut producer, mut consumer) = bounded::ring_buffer::<u64>(1024);
//!
//! producer.push(1).unwrap();
//! producer.push(2).unwrap();
//!
//! assert_eq!(consumer.pop(), Some(1));
//! assert_eq!(consumer.pop(), Some(2));
//! ```
//!
//! # Performance Notes
//!
//! The hot path (when queue is neither full nor empty) performs:
//! - Zero atomic operations for the fast check (uses cached indices)
//! - One atomic store with Release ordering to publish
//!
//! Atomic loads only occur on the slow path when the queue appears full/empty.
//!
//! # Memory Layout
//!
//! The ring buffer uses a single contiguous allocation with cache-line
//! padded head and tail indices to prevent false sharing between producer
//! and consumer threads.

use std::fmt;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use crossbeam_utils::CachePadded;

/// Creates a new SPSC ring buffer with the given capacity.
///
/// Returns a `(Producer, Consumer)` pair. Both endpoints cache the other's
/// index, amortizing atomic loads across multiple operations.
///
/// The actual capacity will be rounded up to the next power of two for efficient
/// index masking.
///
/// # Example
///
/// ```
/// use nexus_queue::spsc::bounded;
///
/// let (mut tx, mut rx) = bounded::ring_buffer::<u64>(1024);
/// tx.push(42).unwrap();
/// assert_eq!(rx.pop(), Some(42));
/// ```
pub fn ring_buffer<T>(capacity: usize) -> (Producer<T>, Consumer<T>) {
    let capacity = capacity.next_power_of_two();
    let mask = capacity - 1;
    let buffer_ptr = std::mem::ManuallyDrop::new(Vec::<T>::with_capacity(capacity)).as_mut_ptr();
    let inner = Arc::new(Inner {
        head: CachePadded::new(AtomicUsize::new(0)),
        tail: CachePadded::new(AtomicUsize::new(0)),
        buffer: buffer_ptr,
        capacity,
        mask,
    });
    let head_atomic = &*inner.head as *const AtomicUsize;
    let tail_atomic = &*inner.tail as *const AtomicUsize;
    (
        Producer {
            _inner: Arc::clone(&inner),
            buffer: buffer_ptr,
            mask,
            head_atomic,
            tail_atomic,
            local_head: 0,
            cached_tail: 0,
        },
        Consumer {
            _inner: inner,
            buffer: buffer_ptr,
            mask,
            tail_atomic,
            head_atomic,
            local_tail: 0,
            cached_head: 0,
        },
    )
}

/// Shared state between producer and consumer.
#[repr(C)]
struct Inner<T> {
    // === Separate cache lines (CachePadded handles this) ===
    /// Producer's write position.
    head: CachePadded<AtomicUsize>,
    /// Consumer's read position.
    tail: CachePadded<AtomicUsize>,

    // === Immutable after construction ===
    /// Raw pointer to buffer (owned by Vec we leaked).
    buffer: *mut T,
    /// Capacity of the buffer.
    capacity: usize,
    /// Capacity - 1, for efficient modulo via bitwise AND.
    mask: usize,
}

// Safety: The ring buffer is safe to share across threads.
// Producer and Consumer have exclusive access to their respective indices.
unsafe impl<T: Send> Send for Inner<T> {}
unsafe impl<T: Send> Sync for Inner<T> {}

/// The producer half of an SPSC ring buffer.
///
/// Use [`push`](Producer::push) to add elements. Takes `&mut self` to
/// statically ensure single-producer access.
///
/// This struct can be sent to another thread but cannot be shared
/// (implements `Send` but not `Sync`).
#[repr(C)]
pub struct Producer<T> {
    // === Hot path fields ===
    /// Our write position (authoritative).
    local_head: usize,
    /// Cached consumer's read position.
    cached_tail: usize,
    /// Cached buffer pointer - avoids Arc deref on hot path.
    buffer: *mut T,
    /// Cached mask - avoids Arc deref on hot path.
    mask: usize,
    /// Pointer to head atomic - avoids Arc deref on hot path.
    head_atomic: *const AtomicUsize,

    // === Cold path fields ===
    /// Pointer to tail atomic - for refreshing cached_tail.
    tail_atomic: *const AtomicUsize,
    /// Handle to inner ring buffer for cleanup
    _inner: Arc<Inner<T>>,
}

// Safety: Producer is Send but not Sync - only one thread can use it.
unsafe impl<T: Send> Send for Producer<T> {}

impl<T> Producer<T> {
    /// Attempts to push a value into the ring buffer.
    ///
    /// Returns `Err(value)` if the buffer is full, giving the value back
    /// to the caller.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_queue::spsc::bounded;
    ///
    /// let (mut producer, mut consumer) = bounded::ring_buffer::<u32>(2);
    ///
    /// assert!(producer.push(1).is_ok());
    /// assert!(producer.push(2).is_ok());
    ///
    /// // Queue is now full
    /// assert_eq!(producer.push(3), Err(bounded::RingBufferFull::new(3)));
    /// ```
    #[inline]
    pub fn push(&mut self, value: T) -> Result<(), RingBufferFull<T>> {
        let head = self.local_head;
        let mut tail = self.cached_tail;

        if head.wrapping_sub(tail) > self.mask {
            // Refresh cache
            tail = unsafe { (*self.tail_atomic).load(Ordering::Relaxed) };
            std::sync::atomic::fence(Ordering::Acquire);

            self.cached_tail = tail;
            if head.wrapping_sub(tail) > self.mask {
                return Err(RingBufferFull::new(value));
            }
        }

        unsafe {
            self.buffer.add(head & self.mask).write(value);
        }
        let next_head = head.wrapping_add(1);

        std::sync::atomic::fence(Ordering::Release);
        unsafe { (*self.head_atomic).store(next_head, Ordering::Relaxed) };

        // Note - keep this instruction here as it gives cache coherency
        // a head start, which gives us more consistent behavior
        self.local_head = next_head;
        Ok(())
    }
}

impl<T> Producer<T> {
    /// Returns the capacity of the ring buffer.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.mask + 1
    }

    /// Returns the number of elements currently in the buffer.
    ///
    /// Note: This is a snapshot and may be immediately stale in concurrent contexts.
    #[inline]
    pub fn len(&self) -> usize {
        let head = unsafe { (*self.head_atomic).load(Ordering::Relaxed) };
        let tail = unsafe { (*self.tail_atomic).load(Ordering::Relaxed) };
        head.wrapping_sub(tail)
    }

    /// Returns `true` if the buffer is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<T> fmt::Debug for Producer<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Producer")
            .field("capacity", &self.capacity())
            .field("len", &self.len())
            .finish_non_exhaustive()
    }
}

/// The consumer half of an SPSC ring buffer.
///
/// Use [`pop`](Consumer::pop) to remove elements. Takes `&mut self` to
/// statically ensure single-consumer access.
///
/// This struct can be sent to another thread but cannot be shared
/// (implements `Send` but not `Sync`).
#[repr(C)]
pub struct Consumer<T> {
    // === Hot path fields ===
    /// Our read position (authoritative).
    local_tail: usize,
    /// Cached producer's write position.
    cached_head: usize,
    /// Cached buffer pointer - avoids Arc deref on hot path.
    buffer: *mut T,
    /// Cached mask - avoids Arc deref on hot path.
    mask: usize,
    /// Pointer to tail atomic - avoids Arc deref on hot path.
    tail_atomic: *const AtomicUsize,

    // === Cold path fields ===
    /// Pointer to head atomic - for refreshing cached_head.
    head_atomic: *const AtomicUsize,
    /// Handle to inner ring buffer for cleanup
    _inner: Arc<Inner<T>>,
}

// Safety: Consumer is Send but not Sync - only one thread can use it.
unsafe impl<T: Send> Send for Consumer<T> {}

impl<T> Consumer<T> {
    /// Attempts to pop a value from the ring buffer.
    ///
    /// Returns `None` if the buffer is empty.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_queue::spsc::bounded;
    ///
    /// let (mut producer, mut consumer) = bounded::ring_buffer::<u32>(8);
    ///
    /// // Queue is empty
    /// assert_eq!(consumer.pop(), None);
    ///
    /// producer.push(42).unwrap();
    /// assert_eq!(consumer.pop(), Some(42));
    /// ```
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        let tail = self.local_tail;
        let mut head = self.cached_head;

        if tail == head {
            // Refresh cache
            head = unsafe { (*self.head_atomic).load(Ordering::Relaxed) };
            std::sync::atomic::fence(Ordering::Acquire);

            self.cached_head = head;
            if tail == head {
                return None;
            }
        }

        let value = unsafe { self.buffer.add(tail & self.mask).read() };
        let next_tail = tail.wrapping_add(1);

        std::sync::atomic::fence(Ordering::Release);
        unsafe { (*self.tail_atomic).store(next_tail, Ordering::Release) };

        // Note - keep this instruction here as it gives cache coherency
        // a head start, which gives us more consistent behavior
        self.local_tail = next_tail;
        Some(value)
    }
}

impl<T> Consumer<T> {
    /// Returns the capacity of the ring buffer.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.mask + 1
    }

    /// Returns the number of elements currently in the buffer.
    ///
    /// Note: This is a snapshot and may be immediately stale in concurrent contexts.
    #[inline]
    pub fn len(&self) -> usize {
        let head = unsafe { (*self.head_atomic).load(Ordering::Relaxed) };
        let tail = unsafe { (*self.tail_atomic).load(Ordering::Relaxed) };
        head.wrapping_sub(tail)
    }

    /// Returns `true` if the buffer is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<T> fmt::Debug for Consumer<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Consumer")
            .field("capacity", &self.capacity())
            .field("len", &self.len())
            .finish_non_exhaustive()
    }
}

/// Error returned by [`Producer::push`] when the ring buffer is full.
///
/// Contains the value that could not be pushed, allowing the caller to
/// retry or handle the value differently.
///
/// # Example
///
/// ```
/// use nexus_queue::spsc::bounded::{self, RingBufferFull};
///
/// let (mut producer, mut consumer) = bounded::ring_buffer::<u32>(1);
///
/// producer.push(1).unwrap();
///
/// // Buffer is full, get our value back
/// let err = producer.push(2).unwrap_err();
/// assert_eq!(err.into_inner(), 2);
/// ```
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct RingBufferFull<T>(T);

impl<T> RingBufferFull<T> {
    /// Creates a new `PushError` containing the given value.
    pub fn new(value: T) -> Self {
        Self(value)
    }

    /// Returns the value that could not be pushed.
    pub fn into_inner(self) -> T {
        self.0
    }
}

impl<T> fmt::Display for RingBufferFull<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ring buffer is full")
    }
}

impl<T> fmt::Debug for RingBufferFull<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RingBufferFull").finish_non_exhaustive()
    }
}

impl<T> std::error::Error for RingBufferFull<T> {}

impl<T> Drop for Inner<T> {
    fn drop(&mut self) {
        // Drop any remaining elements in [tail, head)
        let head = self.head.load(Ordering::Relaxed);
        let tail = self.tail.load(Ordering::Relaxed);

        for i in tail..head {
            unsafe {
                self.buffer.add(i & self.mask).drop_in_place();
            }
        }

        // Reconstruct and drop the Vec to free memory
        unsafe {
            let _ = Vec::from_raw_parts(self.buffer, 0, self.capacity);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ============================================================================
    // Basic Operations
    // ============================================================================

    #[test]
    fn push_pop_interleaved() {
        let (mut producer, mut consumer) = ring_buffer::<u64>(8);

        for i in 0..100 {
            producer.push(i).unwrap();
            assert_eq!(consumer.pop(), Some(i));
        }
    }

    #[test]
    fn fill_then_drain() {
        let (mut producer, mut consumer) = ring_buffer::<u64>(8);

        for i in 0..8 {
            producer.push(i).unwrap();
        }

        for i in 0..8 {
            assert_eq!(consumer.pop(), Some(i));
        }

        assert_eq!(consumer.pop(), None);
    }

    #[test]
    fn pop_when_empty_returns_none() {
        let (mut producer, mut consumer) = ring_buffer::<u64>(8);

        assert_eq!(consumer.pop(), None);

        producer.push(1).unwrap();
        let _ = consumer.pop();

        assert_eq!(consumer.pop(), None);
    }

    #[test]
    fn push_when_full_returns_err() {
        let (mut producer, mut consumer) = ring_buffer::<u64>(4);

        producer.push(1).unwrap();
        producer.push(2).unwrap();
        producer.push(3).unwrap();
        producer.push(4).unwrap();

        // Queue is full
        assert_eq!(producer.push(5), Err(RingBufferFull(5)));

        // After consuming one, can push again
        assert_eq!(consumer.pop(), Some(1));
        producer.push(5).unwrap();
    }

    // ============================================================================
    // Capacity and Rounding
    // ============================================================================

    #[test]
    fn capacity_rounds_to_power_of_two() {
        let (producer, _consumer) = ring_buffer::<u64>(100);
        assert_eq!(producer.capacity(), 128);

        let (producer, _consumer) = ring_buffer::<u64>(1);
        assert_eq!(producer.capacity(), 1);

        let (producer, _consumer) = ring_buffer::<u64>(0);
        assert_eq!(producer.capacity(), 1); // 0 rounds up to 1

        let (producer, _consumer) = ring_buffer::<u64>(1024);
        assert_eq!(producer.capacity(), 1024);
    }

    #[test]
    fn single_capacity() {
        let (mut producer, mut consumer) = ring_buffer::<u64>(1);
        assert_eq!(producer.capacity(), 1);

        producer.push(1).unwrap();
        assert_eq!(producer.push(2), Err(RingBufferFull(2))); // Full with just 1 element

        assert_eq!(consumer.pop(), Some(1));
        producer.push(2).unwrap();
        assert_eq!(consumer.pop(), Some(2));
    }

    // ============================================================================
    // Index Wrapping
    // ============================================================================

    #[test]
    fn multiple_wraparounds() {
        let (mut producer, mut consumer) = ring_buffer::<u64>(4);

        for lap in 0..100 {
            for i in 0..4 {
                producer.push(lap * 4 + i).unwrap();
            }
            for i in 0..4 {
                assert_eq!(consumer.pop(), Some(lap * 4 + i));
            }
        }
    }

    #[test]
    fn partial_fill_drain_wraparound() {
        let (mut producer, mut consumer) = ring_buffer::<u64>(8);

        for _ in 0..50 {
            producer.push(1).unwrap();
            producer.push(2).unwrap();
            producer.push(3).unwrap();

            assert_eq!(consumer.pop(), Some(1));
            assert_eq!(consumer.pop(), Some(2));

            producer.push(4).unwrap();
            producer.push(5).unwrap();

            assert_eq!(consumer.pop(), Some(3));
            assert_eq!(consumer.pop(), Some(4));
            assert_eq!(consumer.pop(), Some(5));
        }
    }

    // ============================================================================
    // Drop Handling
    // ============================================================================

    #[test]
    fn drop_remaining_items() {
        use std::sync::atomic::{AtomicUsize, Ordering};

        let drop_count = Arc::new(AtomicUsize::new(0));

        struct DropCounter(Arc<AtomicUsize>);
        impl Drop for DropCounter {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }

        let (mut producer, consumer) = ring_buffer::<DropCounter>(8);

        producer.push(DropCounter(Arc::clone(&drop_count))).unwrap();
        producer.push(DropCounter(Arc::clone(&drop_count))).unwrap();

        assert_eq!(drop_count.load(Ordering::SeqCst), 0);

        drop(producer);
        drop(consumer);

        assert_eq!(drop_count.load(Ordering::SeqCst), 2);
    }

    #[test]
    fn drop_partial_consumed() {
        use std::sync::atomic::{AtomicUsize, Ordering};

        let drop_count = Arc::new(AtomicUsize::new(0));

        struct DropCounter(Arc<AtomicUsize>);
        impl Drop for DropCounter {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }

        let (mut producer, mut consumer) = ring_buffer::<DropCounter>(8);

        producer.push(DropCounter(Arc::clone(&drop_count))).unwrap();
        producer.push(DropCounter(Arc::clone(&drop_count))).unwrap();
        producer.push(DropCounter(Arc::clone(&drop_count))).unwrap();

        // Consume one
        let _ = consumer.pop();
        assert_eq!(drop_count.load(Ordering::SeqCst), 1);

        // Drop with 2 remaining
        drop(producer);
        drop(consumer);

        assert_eq!(drop_count.load(Ordering::SeqCst), 3);
    }

    // ============================================================================
    // Cross-Thread
    // ============================================================================

    #[test]
    fn cross_thread_basic() {
        use std::thread;

        let (mut producer, mut consumer) = ring_buffer::<u64>(64);

        let producer_handle = thread::spawn(move || {
            for i in 0..100 {
                while producer.push(i).is_err() {
                    thread::yield_now();
                }
            }
        });

        let consumer_handle = thread::spawn(move || {
            for i in 0..100 {
                loop {
                    if let Some(v) = consumer.pop() {
                        assert_eq!(v, i);
                        break;
                    }
                    thread::yield_now();
                }
            }
        });

        producer_handle.join().unwrap();
        consumer_handle.join().unwrap();
    }

    #[test]
    fn cross_thread_throughput() {
        use std::thread;

        const COUNT: u64 = 100_000;

        let (mut producer, mut consumer) = ring_buffer::<u64>(1024);

        let producer_handle = thread::spawn(move || {
            for i in 0..COUNT {
                while producer.push(i).is_err() {
                    std::hint::spin_loop();
                }
            }
        });

        let consumer_handle = thread::spawn(move || {
            let mut received = 0;
            let mut expected = 0;
            while received < COUNT {
                if let Some(v) = consumer.pop() {
                    assert_eq!(v, expected);
                    expected += 1;
                    received += 1;
                } else {
                    std::hint::spin_loop();
                }
            }
            received
        });

        producer_handle.join().unwrap();
        let received = consumer_handle.join().unwrap();
        assert_eq!(received, COUNT);
    }

    #[test]
    fn cross_thread_producer_faster() {
        use std::thread;
        use std::time::Duration;

        let (mut producer, mut consumer) = ring_buffer::<u64>(16);

        let producer_handle = thread::spawn(move || {
            for i in 0..1000 {
                while producer.push(i).is_err() {
                    std::hint::spin_loop();
                }
            }
        });

        let consumer_handle = thread::spawn(move || {
            let mut count = 0;
            while count < 1000 {
                match consumer.pop() {
                    Some(_) => count += 1,
                    None => thread::sleep(Duration::from_micros(10)),
                }
            }
            count
        });

        producer_handle.join().unwrap();
        let count = consumer_handle.join().unwrap();
        assert_eq!(count, 1000);
    }

    #[test]
    fn cross_thread_consumer_faster() {
        use std::thread;
        use std::time::Duration;

        let (mut producer, mut consumer) = ring_buffer::<u64>(16);

        let producer_handle = thread::spawn(move || {
            for i in 0..100 {
                thread::sleep(Duration::from_micros(10));
                while producer.push(i).is_err() {
                    std::hint::spin_loop();
                }
            }
        });

        let consumer_handle = thread::spawn(move || {
            let mut count = 0;
            while count < 100 {
                if consumer.pop().is_some() {
                    count += 1;
                } else {
                    std::hint::spin_loop();
                }
            }
            count
        });

        producer_handle.join().unwrap();
        let count = consumer_handle.join().unwrap();
        assert_eq!(count, 100);
    }

    // ============================================================================
    // Special Types
    // ============================================================================

    #[test]
    fn zero_sized_type() {
        let (mut producer, mut consumer) = ring_buffer::<()>(8);

        producer.push(()).unwrap();
        producer.push(()).unwrap();
        producer.push(()).unwrap();

        assert_eq!(consumer.pop(), Some(()));
        assert_eq!(consumer.pop(), Some(()));
        assert_eq!(consumer.pop(), Some(()));
        assert_eq!(consumer.pop(), None);
    }

    #[test]
    fn large_message_4kb() {
        #[derive(Clone, PartialEq, Debug)]
        struct LargeMessage {
            data: [u8; 4096],
            id: u64,
        }

        let (mut producer, mut consumer) = ring_buffer::<LargeMessage>(4);

        let msg = LargeMessage {
            data: [0xAB; 4096],
            id: 12345,
        };

        producer.push(msg.clone()).unwrap();
        let received = consumer.pop().unwrap();

        assert_eq!(received.id, 12345);
        assert_eq!(received.data[0], 0xAB);
        assert_eq!(received.data[4095], 0xAB);
    }

    #[test]
    fn string_messages() {
        let (mut producer, mut consumer) = ring_buffer::<String>(8);

        producer.push("hello".to_string()).unwrap();
        producer.push("world".to_string()).unwrap();

        assert_eq!(consumer.pop(), Some("hello".to_string()));
        assert_eq!(consumer.pop(), Some("world".to_string()));
    }

    #[test]
    fn vec_messages() {
        let (mut producer, mut consumer) = ring_buffer::<Vec<u8>>(8);

        producer.push(vec![1, 2, 3]).unwrap();
        producer.push(vec![4, 5, 6, 7, 8]).unwrap();

        assert_eq!(consumer.pop(), Some(vec![1, 2, 3]));
        assert_eq!(consumer.pop(), Some(vec![4, 5, 6, 7, 8]));
    }

    // ============================================================================
    // Utility Methods
    // ============================================================================

    #[test]
    fn len_and_is_empty() {
        let (mut producer, mut consumer) = ring_buffer::<u64>(4);

        assert!(consumer.is_empty());
        assert_eq!(consumer.len(), 0);

        producer.push(1).unwrap();
        assert!(!consumer.is_empty());
        assert_eq!(consumer.len(), 1);

        producer.push(2).unwrap();
        producer.push(3).unwrap();
        producer.push(4).unwrap();

        assert_eq!(consumer.len(), 4);

        for _ in 0..4 {
            let _ = consumer.pop();
        }

        assert!(consumer.is_empty());
        assert_eq!(consumer.len(), 0);
    }

    #[test]
    fn debug_impl() {
        let (producer, consumer) = ring_buffer::<u64>(8);

        // Just verify Debug doesn't panic
        let _ = format!("{:?}", producer);
        let _ = format!("{:?}", consumer);
    }

    // ============================================================================
    // Stress Tests
    // ============================================================================

    #[test]
    fn stress_test_sequential() {
        let (mut producer, mut consumer) = ring_buffer::<u64>(16);

        for i in 0..100_000 {
            producer.push(i).unwrap();
            assert_eq!(consumer.pop(), Some(i));
        }
    }

    #[test]
    fn stress_test_cross_thread() {
        use std::thread;

        const ITERATIONS: u64 = 500_000;

        let (mut producer, mut consumer) = ring_buffer::<u64>(256);

        let producer_handle = thread::spawn(move || {
            for i in 0..ITERATIONS {
                while producer.push(i).is_err() {
                    std::hint::spin_loop();
                }
            }
        });

        let consumer_handle = thread::spawn(move || {
            let mut expected = 0;
            while expected < ITERATIONS {
                if let Some(v) = consumer.pop() {
                    assert_eq!(v, expected);
                    expected += 1;
                } else {
                    std::hint::spin_loop();
                }
            }
        });

        producer_handle.join().unwrap();
        consumer_handle.join().unwrap();
    }

    #[test]
    fn stress_test_sum_verification() {
        use std::thread;

        const COUNT: u64 = 1_000_000;
        const EXPECTED_SUM: u64 = COUNT * (COUNT - 1) / 2;

        let (mut producer, mut consumer) = ring_buffer::<u64>(1024);

        let producer_handle = thread::spawn(move || {
            for i in 0..COUNT {
                while producer.push(i).is_err() {
                    std::hint::spin_loop();
                }
            }
        });

        let consumer_handle = thread::spawn(move || {
            let mut sum = 0u64;
            let mut received = 0u64;
            while received < COUNT {
                if let Some(v) = consumer.pop() {
                    sum = sum.wrapping_add(v);
                    received += 1;
                } else {
                    std::hint::spin_loop();
                }
            }
            sum
        });

        producer_handle.join().unwrap();
        let sum = consumer_handle.join().unwrap();
        assert_eq!(sum, EXPECTED_SUM);
    }
}
