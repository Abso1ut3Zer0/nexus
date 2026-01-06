//! Single-producer single-consumer queue using per-slot lap counters.
//!
//! # Design
//!
//! ```text
//! ┌──────────────────────────────────────────────────────────┐
//! │ buffer[0]: { lap: AtomicUsize, data: T }                 │
//! │ buffer[1]: { lap: AtomicUsize, data: T }                 │
//! │ ...                                                      │
//! └──────────────────────────────────────────────────────────┘
//! ```
//!
//! Each slot contains its own lap counter. Producer and consumer synchronize
//! by reading/writing the lap counter on the slot they're accessing. This
//! provides excellent cache locality - the synchronization word and data are
//! on the same cache line.
//!
//! # Performance Characteristics
//!
//! This implementation has different performance characteristics than the
//! default [`index`](super::index) implementation. The key difference is
//! cache line ownership:
//!
//! - **slot**: Producer and consumer write to the same cache line (the slot's lap counter)
//! - **index**: Producer and consumer write to separate cache lines (head/tail)
//!
//! Which performs better depends on your hardware topology, particularly NUMA
//! configuration and cache hierarchy. **Benchmark both on your target hardware.**
//!
//! Enable with:
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

use std::cell::UnsafeCell;
use std::fmt;
use std::mem::{ManuallyDrop, MaybeUninit};
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering, fence};

use crate::Full;

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
        buffer,
        capacity,
        mask,
    });

    (
        Producer {
            local_tail: 0,
            buffer,
            mask,
            shift,
            inner: Arc::clone(&inner),
        },
        Consumer {
            local_head: 0,
            buffer,
            mask,
            shift,
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
/// Takes `&mut self` to statically ensure single-producer access.
#[repr(C)]
pub struct Producer<T> {
    // === Hot path fields ===
    local_tail: usize,
    buffer: *mut Slot<T>,
    mask: usize,
    shift: usize,

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
    /// use nexus_queue;
    ///
    /// let (mut producer, mut consumer) = nexus_queue::spsc::ring_buffer::<u32>(2);
    ///
    /// assert!(producer.push(1).is_ok());
    /// assert!(producer.push(2).is_ok());
    /// assert!(producer.push(3).is_err()); // Full
    /// ```
    #[inline]
    #[must_use = "push returns Err if full, which should be handled"]
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
        self.local_tail = tail.wrapping_add(1);

        Ok(())
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
    inner: Arc<Inner<T>>,
}

unsafe impl<T: Send> Send for Consumer<T> {}

impl<T> Consumer<T> {
    /// Attempts to pop a value from the ring buffer.
    ///
    /// Returns `Some(value)` if data is available, `None` if the buffer is empty.
    /// Values are returned in FIFO order.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_queue;
    ///
    /// let (mut producer, mut consumer) = nexus_queue::spsc::ring_buffer::<u32>(8);
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

        if slot_lap != expected_lap {
            return None;
        }

        let value = unsafe { (*slot.data.get()).assume_init_read() };

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
