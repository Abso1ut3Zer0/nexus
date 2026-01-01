//! Single-Producer Single-Consumer (SPSC) ring buffer with per-slot sequencing.
//!
//! This module provides a high-performance SPSC queue with two push modes:
//! - [`push`](Producer::push) - Returns error if buffer is full (bounded behavior)
//! - [`force_push`](Producer::force_push) - Overwrites oldest unread value if full
//!
//! # Design
//!
//! Uses per-slot lap counters instead of cached head/tail indices. This provides:
//! - Lower latency for ping-pong workloads (no stale cache refresh)
//! - Better cache locality (lap counter and data on same cache line)
//! - Simpler control flow with fewer branches
//!
//! # Example
//!
//! ```
//! use nexus_queue::spsc;
//!
//! let (mut producer, mut consumer) = spsc::ring_buffer::<u64>(4);
//!
//! // Bounded push - returns error if full
//! producer.push(1).unwrap();
//! producer.push(2).unwrap();
//! producer.push(3).unwrap();
//! producer.push(4).unwrap();
//! assert!(producer.push(5).is_err()); // Full!
//!
//! assert_eq!(consumer.pop(), Some(1));
//!
//! // Force push - overwrites if full
//! producer.push(5).unwrap(); // Now there's room
//! producer.force_push(6); // Would overwrite if full
//! ```

use std::cell::UnsafeCell;
use std::fmt;
use std::mem::{ManuallyDrop, MaybeUninit};
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering, fence};

/// Creates a new SPSC ring buffer with the given capacity.
///
/// Returns a `(Producer, Consumer)` pair.
///
/// The actual capacity will be rounded up to the next power of two.
///
/// # Panics
///
/// Panics if `capacity` is 0.
pub fn ring_buffer<T>(capacity: usize) -> (Producer<T>, Consumer<T>) {
    assert!(capacity > 0, "capacity must be non-zero");

    let capacity = capacity.next_power_of_two();
    let mask = capacity - 1;
    let shift = capacity.trailing_zeros() as usize;

    // Allocate slot buffer
    let mut slots = ManuallyDrop::new(Vec::<Slot<T>>::with_capacity(capacity));
    for _ in 0..capacity {
        slots.push(Slot {
            lap: AtomicUsize::new(0),
            data: UnsafeCell::new(MaybeUninit::uninit()),
        });
    }
    let buffer = slots.as_mut_ptr();

    let inner = Arc::new(Inner {
        tail: AtomicUsize::new(0),
        buffer,
        capacity,
        mask,
    });

    let tail_atomic = &inner.tail as *const AtomicUsize;

    (
        Producer {
            local_tail: 0,
            buffer,
            mask,
            shift,
            tail_atomic,
            inner: Arc::clone(&inner),
        },
        Consumer {
            local_head: 0,
            buffer,
            mask,
            shift,
            tail_atomic,
            inner,
        },
    )
}

/// A slot in the ring buffer with a lap counter.
///
/// The lap counter serves as the synchronization mechanism:
/// - `lap == 0`: slot is empty/consumed
/// - `lap == n`: slot contains data written during lap `n` (1-indexed)
#[repr(C)]
struct Slot<T> {
    lap: AtomicUsize,
    data: UnsafeCell<MaybeUninit<T>>,
}

/// Shared state between producer and consumer.
#[repr(C)]
struct Inner<T> {
    /// Producer's write position - used by consumer to catch up when lapped.
    tail: AtomicUsize,
    buffer: *mut Slot<T>,
    capacity: usize,
    mask: usize,
}

unsafe impl<T: Send> Send for Inner<T> {}
unsafe impl<T: Send> Sync for Inner<T> {}

impl<T> Drop for Inner<T> {
    fn drop(&mut self) {
        // Drop any remaining data in slots
        for i in 0..self.capacity {
            let slot = unsafe { &*self.buffer.add(i) };
            let lap = slot.lap.load(Ordering::Relaxed);
            if lap > 0 {
                unsafe { (*slot.data.get()).assume_init_drop() };
            }
        }

        // Free the Vec
        unsafe {
            let _ = Vec::from_raw_parts(self.buffer, self.capacity, self.capacity);
        }
    }
}

/// The producer half of an SPSC ring buffer.
///
/// Provides two push methods:
/// - [`push`](Producer::push) - Bounded, returns error if full
/// - [`force_push`](Producer::force_push) - Overwrites oldest if full
///
/// Takes `&mut self` to statically ensure single-producer access.
#[repr(C)]
pub struct Producer<T> {
    // === Hot path fields ===
    local_tail: usize,
    buffer: *mut Slot<T>,
    mask: usize,
    shift: usize,
    tail_atomic: *const AtomicUsize,

    // === Cold path fields ===
    inner: Arc<Inner<T>>,
}

unsafe impl<T: Send> Send for Producer<T> {}

impl<T> Producer<T> {
    /// Attempts to push a value into the ring buffer.
    ///
    /// Returns `Err(Full(value))` if the buffer is full, giving the value back.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_queue::spsc;
    ///
    /// let (mut producer, mut consumer) = spsc::ring_buffer::<u32>(2);
    ///
    /// assert!(producer.push(1).is_ok());
    /// assert!(producer.push(2).is_ok());
    /// assert!(producer.push(3).is_err()); // Full
    /// ```
    #[inline]
    pub fn push(&mut self, value: T) -> Result<(), Full<T>> {
        let tail = self.local_tail;
        let slot = unsafe { &*self.buffer.add(tail & self.mask) };

        // Check if slot is occupied (lap > 0 means data present)
        let slot_lap = slot.lap.load(Ordering::Relaxed);
        fence(Ordering::Acquire);

        if slot_lap != 0 {
            return Err(Full(value));
        }

        // Write new value
        unsafe { (*slot.data.get()).write(value) };

        // Publish with new lap
        let lap = (tail >> self.shift) + 1;
        fence(Ordering::Release);
        slot.lap.store(lap, Ordering::Relaxed);

        // Update tail (for consumer catch-up)
        let next_tail = tail.wrapping_add(1);
        unsafe { (*self.tail_atomic).store(next_tail, Ordering::Relaxed) };

        self.local_tail = next_tail;

        Ok(())
    }

    /// Pushes a value, overwriting the oldest unread value if full.
    ///
    /// Returns `None` if the slot was empty, or `Some(old_value)` if
    /// an unread value was overwritten (indicates consumer is falling behind).
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_queue::spsc;
    ///
    /// let (mut producer, mut consumer) = spsc::ring_buffer::<u32>(2);
    ///
    /// assert!(producer.force_push(1).is_none()); // Slot was empty
    /// assert!(producer.force_push(2).is_none()); // Slot was empty
    /// assert_eq!(producer.force_push(3), Some(1)); // Overwrote value 1
    /// ```
    #[inline]
    pub fn force_push(&mut self, value: T) -> Option<T> {
        let tail = self.local_tail;
        let slot = unsafe { &*self.buffer.add(tail & self.mask) };

        // Check for unconsumed data (lap > 0 means data present)
        let old_lap = slot.lap.load(Ordering::Relaxed);
        fence(Ordering::Acquire);

        let old_value = if old_lap > 0 {
            Some(unsafe { (*slot.data.get()).assume_init_read() })
        } else {
            None
        };

        // Write new value
        unsafe { (*slot.data.get()).write(value) };

        // Publish with new lap
        let lap = (tail >> self.shift) + 1;
        fence(Ordering::Release);
        slot.lap.store(lap, Ordering::Relaxed);

        // Update tail (for consumer catch-up)
        let next_tail = tail.wrapping_add(1);
        unsafe { (*self.tail_atomic).store(next_tail, Ordering::Relaxed) };

        self.local_tail = next_tail;

        old_value
    }

    /// Returns the capacity of the ring buffer.
    #[inline]
    pub fn capacity(&self) -> usize {
        1 << self.shift
    }

    /// Returns `true` if the consumer has been dropped.
    #[inline]
    pub fn is_disconnected(&self) -> bool {
        Arc::strong_count(&self.inner) == 1
    }
}

impl<T> fmt::Debug for Producer<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Producer")
            .field("capacity", &self.capacity())
            .finish_non_exhaustive()
    }
}

/// The consumer half of an SPSC ring buffer.
///
/// Use [`pop`](Consumer::pop) to remove elements. Takes `&mut self` to
/// statically ensure single-consumer access.
#[repr(C)]
pub struct Consumer<T> {
    // === Hot path fields ===
    local_head: usize,
    buffer: *mut Slot<T>,
    mask: usize,
    shift: usize,

    // === Cold path fields ===
    tail_atomic: *const AtomicUsize,
    inner: Arc<Inner<T>>,
}

unsafe impl<T: Send> Send for Consumer<T> {}

impl<T> Consumer<T> {
    /// Attempts to pop a value from the ring buffer.
    ///
    /// Returns `Some(value)` if data is available, `None` if the buffer is empty.
    /// Values are returned in FIFO order. If the consumer was lapped (only possible
    /// when producer uses `force_push`), it automatically catches up to the oldest
    /// valid position.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_queue::spsc;
    ///
    /// let (mut producer, mut consumer) = spsc::ring_buffer::<u32>(8);
    ///
    /// assert_eq!(consumer.pop(), None); // Empty
    ///
    /// producer.push(42).unwrap();
    /// assert_eq!(consumer.pop(), Some(42));
    /// ```
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        let head = self.local_head;
        let slot = unsafe { &*self.buffer.add(head & self.mask) };
        let expected_lap = (head >> self.shift) + 1;

        let slot_lap = slot.lap.load(Ordering::Relaxed);
        fence(Ordering::Acquire);

        if slot_lap == 0 {
            // Slot is empty/consumed
            return None;
        }

        if slot_lap < expected_lap {
            // Slot hasn't been written for this lap yet (shouldn't happen in normal operation)
            return None;
        }

        if slot_lap > expected_lap {
            // We've been lapped - catch up to oldest valid position
            let tail = unsafe { (*self.tail_atomic).load(Ordering::Relaxed) };
            fence(Ordering::Acquire);

            // Oldest valid position is tail - capacity
            let oldest_valid = tail.saturating_sub(self.capacity());
            self.local_head = oldest_valid;

            // Retry from new position
            return self.pop();
        }

        // Normal case: slot_lap == expected_lap
        let value = unsafe { (*slot.data.get()).assume_init_read() };

        // Mark consumed
        fence(Ordering::Release);
        slot.lap.store(0, Ordering::Relaxed);

        self.local_head = head.wrapping_add(1);

        Some(value)
    }

    /// Returns the capacity of the ring buffer.
    #[inline]
    pub const fn capacity(&self) -> usize {
        1 << self.shift
    }

    /// Returns `true` if the producer has been dropped.
    #[inline]
    pub fn is_disconnected(&self) -> bool {
        Arc::strong_count(&self.inner) == 1
    }
}

impl<T> fmt::Debug for Consumer<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Consumer")
            .field("capacity", &self.capacity())
            .finish_non_exhaustive()
    }
}

/// Error returned when the ring buffer is full.
///
/// Contains the value that could not be pushed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Full<T>(pub T);

impl<T> Full<T> {
    /// Returns the value that could not be pushed.
    pub fn into_inner(self) -> T {
        self.0
    }
}

impl<T> fmt::Display for Full<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ring buffer is full")
    }
}

impl<T: fmt::Debug> std::error::Error for Full<T> {}

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
    // Force Push (Overwriting) Behavior
    // ============================================================================

    #[test]
    fn force_push_returns_old_value() {
        let (mut prod, _cons) = ring_buffer::<u64>(4);

        assert_eq!(prod.force_push(1), None);
        assert_eq!(prod.force_push(2), None);
        assert_eq!(prod.force_push(3), None);
        assert_eq!(prod.force_push(4), None);

        // Now full - overwrites begin
        assert_eq!(prod.force_push(5), Some(1));
        assert_eq!(prod.force_push(6), Some(2));
        assert_eq!(prod.force_push(7), Some(3));
        assert_eq!(prod.force_push(8), Some(4));
    }

    #[test]
    fn consumed_slot_returns_none_on_force_push() {
        let (mut prod, mut cons) = ring_buffer::<u64>(4);

        prod.force_push(1);
        prod.force_push(2);
        prod.force_push(3);
        prod.force_push(4);

        // Consume one
        assert_eq!(cons.pop(), Some(1));

        // Force push to consumed slot - should return None
        assert_eq!(prod.force_push(5), None);

        // Force push to unconsumed slot - should return old value
        assert_eq!(prod.force_push(6), Some(2));
    }

    #[test]
    fn consumer_catches_up_fifo() {
        let (mut prod, mut cons) = ring_buffer::<u64>(4);

        // Fill buffer
        for i in 1..=4 {
            prod.force_push(i);
        }

        // Overwrite slot 0
        assert_eq!(prod.force_push(5), Some(1));

        // Consumer should catch up and read in FIFO order
        assert_eq!(cons.pop(), Some(2));
        assert_eq!(cons.pop(), Some(3));
        assert_eq!(cons.pop(), Some(4));
        assert_eq!(cons.pop(), Some(5));
        assert_eq!(cons.pop(), None);
    }

    // ============================================================================
    // Mixed Push Modes
    // ============================================================================

    #[test]
    fn mixed_push_and_force_push() {
        let (mut prod, mut cons) = ring_buffer::<u64>(4);

        // Use regular push until full
        assert!(prod.push(1).is_ok());
        assert!(prod.push(2).is_ok());
        assert!(prod.push(3).is_ok());
        assert!(prod.push(4).is_ok());
        assert!(prod.push(5).is_err());

        // Switch to force_push
        assert_eq!(prod.force_push(5), Some(1));

        // Consumer reads in order
        assert_eq!(cons.pop(), Some(2));
        assert_eq!(cons.pop(), Some(3));
        assert_eq!(cons.pop(), Some(4));
        assert_eq!(cons.pop(), Some(5));
    }

    // ============================================================================
    // Multiple Laps
    // ============================================================================

    #[test]
    fn full_lap_overwrite() {
        let (mut prod, mut cons) = ring_buffer::<u64>(4);

        // Write 2 full laps (8 values)
        for i in 0..8 {
            prod.force_push(i);
        }

        // Buffer now contains values 4,5,6,7
        assert_eq!(cons.pop(), Some(4));
        assert_eq!(cons.pop(), Some(5));
        assert_eq!(cons.pop(), Some(6));
        assert_eq!(cons.pop(), Some(7));
        assert_eq!(cons.pop(), None);
    }

    #[test]
    fn many_laps() {
        let (mut prod, mut cons) = ring_buffer::<u64>(4);

        // Write 5 laps worth (20 values)
        for i in 0..20 {
            prod.force_push(i);
        }

        // Buffer contains values 16,17,18,19
        let mut values = Vec::new();
        while let Some(v) = cons.pop() {
            values.push(v);
        }

        assert_eq!(values, vec![16, 17, 18, 19]);
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

    #[test]
    fn single_slot_overwriting() {
        let (mut prod, mut cons) = ring_buffer::<u64>(1);

        assert_eq!(prod.force_push(1), None);
        assert_eq!(prod.force_push(2), Some(1));
        assert_eq!(prod.force_push(3), Some(2));

        assert_eq!(cons.pop(), Some(3));
        assert_eq!(cons.pop(), None);
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

    #[test]
    fn force_push_drops_old_via_return() {
        use std::sync::atomic::AtomicUsize;

        static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

        struct DropCounter;
        impl Drop for DropCounter {
            fn drop(&mut self) {
                DROP_COUNT.fetch_add(1, Ordering::SeqCst);
            }
        }

        DROP_COUNT.store(0, Ordering::SeqCst);

        let (mut prod, _cons) = ring_buffer::<DropCounter>(4);

        for _ in 0..4 {
            prod.force_push(DropCounter);
        }
        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), 0);

        let old = prod.force_push(DropCounter);
        drop(old);
        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), 1);
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

    #[test]
    fn cross_thread_overwriting() {
        use std::thread;

        let (mut prod, mut cons) = ring_buffer::<u64>(64);

        let producer = thread::spawn(move || {
            for i in 0..10_000 {
                prod.force_push(i);
            }
        });

        let consumer = thread::spawn(move || {
            let mut received = 0;
            loop {
                match cons.pop() {
                    Some(_) => received += 1,
                    None => {
                        if cons.is_disconnected() {
                            break;
                        }
                        std::hint::spin_loop();
                    }
                }
            }
            received
        });

        producer.join().unwrap();
        let received = consumer.join().unwrap();
        assert!(received > 0);
    }

    #[test]
    fn cross_thread_fifo_preserved() {
        use std::thread;

        let (mut prod, mut cons) = ring_buffer::<u64>(64);

        let producer = thread::spawn(move || {
            for i in 0..1000 {
                prod.force_push(i);
            }
        });

        let consumer = thread::spawn(move || {
            let mut last_seen: Option<u64> = None;
            let mut out_of_order = 0;

            loop {
                match cons.pop() {
                    Some(v) => {
                        if let Some(last) = last_seen {
                            if v <= last {
                                out_of_order += 1;
                            }
                        }
                        last_seen = Some(v);
                    }
                    None => {
                        if cons.is_disconnected() {
                            break;
                        }
                        std::hint::spin_loop();
                    }
                }
            }
            out_of_order
        });

        producer.join().unwrap();
        let out_of_order = consumer.join().unwrap();
        assert_eq!(out_of_order, 0, "FIFO order was violated");
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

    // ============================================================================
    // Stress Tests
    // ============================================================================

    #[test]
    fn stress_many_overwrites() {
        let (mut prod, mut cons) = ring_buffer::<u64>(16);

        for i in 0..100_000 {
            prod.force_push(i);
        }

        let mut count = 0;
        while cons.pop().is_some() {
            count += 1;
        }

        assert_eq!(count, 16);
    }

    #[test]
    fn stress_cross_thread_high_volume() {
        use std::thread;

        const COUNT: u64 = 1_000_000;

        let (mut prod, mut cons) = ring_buffer::<u64>(1024);

        let producer = thread::spawn(move || {
            for i in 0..COUNT {
                prod.force_push(i);
            }
        });

        let consumer = thread::spawn(move || {
            let mut received = 0u64;
            loop {
                match cons.pop() {
                    Some(_) => received += 1,
                    None => {
                        if cons.is_disconnected() {
                            break;
                        }
                        std::hint::spin_loop();
                    }
                }
            }
            received
        });

        producer.join().unwrap();
        let received = consumer.join().unwrap();

        assert!(received > 0);
        assert!(received <= COUNT);
    }
}
