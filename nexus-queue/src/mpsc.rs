//! Multi-producer single-consumer bounded queue.
//!
//! A lock-free ring buffer optimized for multiple producer threads sending to
//! one consumer thread. Uses CAS-based slot claiming with Vyukov-style turn
//! counters for synchronization.
//!
//! # Design
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────┐
//! │ Shared (Arc):                                               │
//! │   tail: CachePadded<AtomicUsize>   ← Producers CAS here     │
//! │   head: CachePadded<AtomicUsize>   ← Consumer writes        │
//! │   slots: *mut Slot<T>              ← Per-slot turn counters │
//! └─────────────────────────────────────────────────────────────┘
//!
//! ┌─────────────────────┐     ┌─────────────────────┐
//! │ Producer (Clone):   │     │ Consumer (!Clone):  │
//! │   cached_head       │     │   local_head        │
//! │   shared: Arc       │     │   shared: Arc       │
//! └─────────────────────┘     └─────────────────────┘
//! ```
//!
//! Producers compete via CAS on the tail index. After claiming a slot, the
//! producer waits for the slot's turn counter to indicate it's writable, writes
//! the data, then advances the turn to signal readiness.
//!
//! The consumer checks the turn counter to know when data is ready, reads it,
//! then advances the turn for the next producer lap.
//!
//! # Turn Counter Protocol
//!
//! For slot at index `i` on lap `turn`:
//! - `turn * 2`: Slot is ready for producer to write
//! - `turn * 2 + 1`: Slot contains data, ready for consumer
//!
//! # Example
//!
//! ```
//! use nexus_queue::mpsc;
//! use std::thread;
//!
//! let (tx, rx) = mpsc::ring_buffer::<u64>(1024);
//!
//! let tx2 = tx.clone();
//! let h1 = thread::spawn(move || {
//!     for i in 0..100 {
//!         while tx.push(i).is_err() { std::hint::spin_loop(); }
//!     }
//! });
//! let h2 = thread::spawn(move || {
//!     for i in 100..200 {
//!         while tx2.push(i).is_err() { std::hint::spin_loop(); }
//!     }
//! });
//!
//! let mut received = 0;
//! while received < 200 {
//!     if rx.pop().is_some() { received += 1; }
//! }
//!
//! h1.join().unwrap();
//! h2.join().unwrap();
//! ```

use std::cell::Cell;
use std::fmt;
use std::mem::MaybeUninit;

use crate::loom_impl::{Arc, AtomicUsize, Ordering, UnsafeCell};

use crossbeam_utils::CachePadded;

use crate::Full;

/// Creates a bounded MPSC ring buffer. Renamed to [`ring_buffer`].
#[deprecated(since = "1.3.0", note = "renamed to ring_buffer()")]
#[inline]
pub fn bounded<T>(capacity: usize) -> (Producer<T>, Consumer<T>) {
    ring_buffer(capacity)
}

/// Creates a bounded MPSC queue with the given capacity.
///
/// Capacity is rounded up to the next power of two.
///
/// # Panics
///
/// Panics if `capacity` is zero or too large to round to a power of two.
pub fn ring_buffer<T>(capacity: usize) -> (Producer<T>, Consumer<T>) {
    assert!(capacity > 0, "capacity must be non-zero");

    let capacity = capacity
        .checked_next_power_of_two()
        .expect("capacity too large (must be <= usize::MAX / 2)");
    let mask = capacity - 1;

    // Allocate slots with turn counters initialized to 0 (ready for turn 0 producers)
    let slots: Vec<Slot<T>> = (0..capacity)
        .map(|_| Slot {
            turn: AtomicUsize::new(0),
            data: UnsafeCell::new(MaybeUninit::uninit()),
        })
        .collect();
    let slots = Box::into_raw(slots.into_boxed_slice()) as *mut Slot<T>;

    let shift = capacity.trailing_zeros();

    let shared = Arc::new(Shared {
        tail: CachePadded::new(AtomicUsize::new(0)),
        head: CachePadded::new(AtomicUsize::new(0)),
        slots,
        capacity,
        shift,
        mask,
    });

    (
        Producer {
            cached_head: Cell::new(0),
            slots,
            mask,
            capacity,
            shift,
            shared: Arc::clone(&shared),
        },
        Consumer {
            local_head: Cell::new(0),
            slots,
            mask,
            shift,
            shared,
        },
    )
}

/// A slot in the ring buffer with turn-based synchronization.
struct Slot<T> {
    /// Turn counter for Vyukov-style synchronization.
    /// - `turn * 2`: ready for producer
    /// - `turn * 2 + 1`: ready for consumer
    turn: AtomicUsize,
    /// The data stored in this slot.
    data: UnsafeCell<MaybeUninit<T>>,
}

/// Shared state between producers and the consumer.
// repr(C): Guarantees field order for cache line layout.
#[repr(C)]
struct Shared<T> {
    /// Tail index - producers CAS on this to claim slots.
    tail: CachePadded<AtomicUsize>,
    /// Head index - consumer publishes progress here.
    head: CachePadded<AtomicUsize>,
    /// Pointer to the slot array.
    slots: *mut Slot<T>,
    /// Actual capacity (power of two).
    capacity: usize,
    /// Shift for fast division by capacity (log2(capacity)).
    shift: u32,
    /// Mask for fast modulo (capacity - 1).
    mask: usize,
}

// SAFETY: Shared contains atomics and raw pointers. Access is synchronized via
// the turn counters. T: Send ensures data can move between threads.
unsafe impl<T: Send> Send for Shared<T> {}
// SAFETY: same as Send — all shared state is atomic; cross-thread access is
// coordinated by the turn counters.
unsafe impl<T: Send> Sync for Shared<T> {}

impl<T> Drop for Shared<T> {
    fn drop(&mut self) {
        let head = self.head.load(Ordering::Relaxed);
        let tail = self.tail.load(Ordering::Relaxed);

        // Drop any remaining elements in the queue
        let mut i = head;
        while i != tail {
            // SAFETY: slots pointer is valid (allocated in ring_buffer, freed below).
            // i & mask is in bounds. We have exclusive access (drop requires &mut self).
            let slot = unsafe { &*self.slots.add(i & self.mask) };
            let turn = i >> self.shift;

            // Only drop if the slot was actually written (turn is odd = consumer-ready)
            if slot.turn.load(Ordering::Relaxed) == turn * 2 + 1 {
                // SAFETY: Slot contains initialized data at this turn.
                slot.data
                    .with_mut(|ptr| unsafe { (*ptr).assume_init_drop() });
            }
            i = i.wrapping_add(1);
        }

        // SAFETY: slots was allocated via Box::into_raw from a Vec.
        unsafe {
            let _ = Box::from_raw(std::ptr::slice_from_raw_parts_mut(
                self.slots,
                self.capacity,
            ));
        }
    }
}

/// The producer endpoint of an MPSC queue.
///
/// This endpoint can be cloned to create additional producers. Each clone
/// maintains its own cached state for performance.
// repr(C): Hot fields at struct base share cache line with struct pointer.
#[repr(C)]
pub struct Producer<T> {
    /// Cached head for fast full-check. Only refreshed when cache indicates full.
    cached_head: Cell<usize>,
    /// Cached slots pointer (avoids Arc deref on hot path).
    slots: *mut Slot<T>,
    /// Cached mask (avoids Arc deref on hot path).
    mask: usize,
    /// Cached capacity (avoids Arc deref on hot path).
    capacity: usize,
    /// Cached shift for fast division (log2(capacity)).
    shift: u32,
    shared: Arc<Shared<T>>,
}

impl<T> Clone for Producer<T> {
    fn clone(&self) -> Self {
        Producer {
            // Fresh cache - will be populated on first push
            cached_head: Cell::new(self.shared.head.load(Ordering::Relaxed)),
            slots: self.slots,
            mask: self.mask,
            capacity: self.capacity,
            shift: self.shift,
            shared: Arc::clone(&self.shared),
        }
    }
}

// SAFETY: Producer can be sent to another thread. Each Producer instance is
// used by one thread (not Sync - use clone() for multiple threads).
unsafe impl<T: Send> Send for Producer<T> {}

impl<T> Producer<T> {
    /// Pushes a value into the queue.
    ///
    /// Returns `Err(Full(value))` if the queue is full, returning ownership
    /// of the value to the caller for backpressure handling.
    ///
    /// This method spins internally on CAS contention but returns immediately
    /// when the queue is actually full.
    #[inline]
    #[must_use = "push returns Err if full, which should be handled"]
    pub fn push(&self, value: T) -> Result<(), Full<T>> {
        let mut spin_count = 0u32;

        loop {
            let tail = self.shared.tail.load(Ordering::Relaxed);

            // Check against cached head (avoids atomic load most of the time)
            if tail.wrapping_sub(self.cached_head.get()) >= self.capacity {
                // Cache miss: refresh from shared head
                self.cached_head
                    .set(self.shared.head.load(Ordering::Acquire));

                // Re-check with fresh head - if still full, return error
                if tail.wrapping_sub(self.cached_head.get()) >= self.capacity {
                    return Err(Full(value));
                }
            }

            // SAFETY: slots pointer is valid for the lifetime of shared.
            let slot = unsafe { &*self.slots.add(tail & self.mask) };
            let turn = tail >> self.shift;
            let expected_stamp = turn * 2;

            // Check if slot is ready BEFORE attempting CAS (Vyukov optimization)
            let stamp = slot.turn.load(Ordering::Acquire);

            if stamp == expected_stamp {
                // Slot is ready - try to claim it
                if self
                    .shared
                    .tail
                    .compare_exchange_weak(
                        tail,
                        tail.wrapping_add(1),
                        Ordering::Relaxed,
                        Ordering::Relaxed,
                    )
                    .is_ok()
                {
                    // SAFETY: We own this slot via successful CAS.
                    slot.data.with_mut(|ptr| unsafe { (*ptr).write(value) });

                    // Signal ready for consumer: turn * 2 + 1
                    slot.turn.store(turn * 2 + 1, Ordering::Release);

                    return Ok(());
                }
            }

            // CAS failed or slot not ready - exponential backoff
            // Cap at 6 to avoid excessive spinning (1, 2, 4, 8, 16, 32, 64 iterations)
            let spins = 1 << spin_count.min(6);
            for _ in 0..spins {
                std::hint::spin_loop();
            }
            spin_count += 1;

            // Periodically check if the consumer disconnected during spin.
            // Without this, a producer spins forever if the consumer drops
            // while we're in the retry loop.
            if spin_count >= 5 && self.is_disconnected() {
                return Err(Full(value));
            }
        }
    }

    /// Returns the capacity of the queue.
    #[inline]
    pub fn capacity(&self) -> usize {
        1 << self.shift
    }

    /// Returns `true` if the consumer has been dropped.
    ///
    /// With multiple producers, this returns `true` only when this is the
    /// last handle (all other producers and the consumer are dropped).
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

/// The consumer endpoint of an MPSC queue.
///
/// This endpoint cannot be cloned - only one consumer thread is allowed.
// repr(C): Hot fields at struct base share cache line with struct pointer.
#[repr(C)]
pub struct Consumer<T> {
    /// Local head index - only this thread reads/writes.
    local_head: Cell<usize>,
    /// Cached slots pointer (avoids Arc deref on hot path).
    slots: *mut Slot<T>,
    /// Cached mask (avoids Arc deref on hot path).
    mask: usize,
    /// Cached shift for fast division (log2(capacity)).
    shift: u32,
    shared: Arc<Shared<T>>,
}

// SAFETY: Consumer can be sent to another thread. It has exclusive read access
// to slots (via turn protocol) and maintains the head index.
unsafe impl<T: Send> Send for Consumer<T> {}

impl<T> Consumer<T> {
    /// Pops a value from the queue.
    ///
    /// Returns `None` if the queue is empty.
    #[inline]
    pub fn pop(&self) -> Option<T> {
        let head = self.local_head.get();
        // SAFETY: slots pointer is valid for the lifetime of shared.
        let slot = unsafe { &*self.slots.add(head & self.mask) };
        let turn = head >> self.shift;

        // Check if slot is ready (turn * 2 + 1 means producer has written)
        if slot.turn.load(Ordering::Acquire) != turn * 2 + 1 {
            return None;
        }

        // SAFETY: Turn counter confirms producer has written to this slot.
        let value = slot
            .data
            .with_mut(|ptr| unsafe { (*ptr).assume_init_read() });

        // Signal slot is free for next lap: (turn + 1) * 2
        slot.turn.store((turn + 1) * 2, Ordering::Release);

        // Advance head and publish for producers' capacity check
        let new_head = head.wrapping_add(1);
        self.local_head.set(new_head);
        self.shared.head.store(new_head, Ordering::Release);

        Some(value)
    }

    /// Returns the capacity of the queue.
    #[inline]
    pub fn capacity(&self) -> usize {
        1 << self.shift
    }

    /// Returns `true` if all producers have been dropped.
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
        let (tx, rx) = ring_buffer::<u64>(4);

        assert!(tx.push(1).is_ok());
        assert!(tx.push(2).is_ok());
        assert!(tx.push(3).is_ok());

        assert_eq!(rx.pop(), Some(1));
        assert_eq!(rx.pop(), Some(2));
        assert_eq!(rx.pop(), Some(3));
        assert_eq!(rx.pop(), None);
    }

    #[test]
    fn empty_pop_returns_none() {
        let (_, rx) = ring_buffer::<u64>(4);
        assert_eq!(rx.pop(), None);
        assert_eq!(rx.pop(), None);
    }

    #[test]
    fn fill_then_drain() {
        let (tx, rx) = ring_buffer::<u64>(4);

        for i in 0..4 {
            assert!(tx.push(i).is_ok());
        }

        for i in 0..4 {
            assert_eq!(rx.pop(), Some(i));
        }

        assert_eq!(rx.pop(), None);
    }

    #[test]
    fn push_returns_error_when_full() {
        let (tx, _rx) = ring_buffer::<u64>(4);

        assert!(tx.push(1).is_ok());
        assert!(tx.push(2).is_ok());
        assert!(tx.push(3).is_ok());
        assert!(tx.push(4).is_ok());

        let err = tx.push(5).unwrap_err();
        assert_eq!(err.into_inner(), 5);
    }

    // ============================================================================
    // Interleaved Operations
    // ============================================================================

    #[test]
    fn interleaved_single_producer() {
        let (tx, rx) = ring_buffer::<u64>(8);

        for i in 0..1000 {
            assert!(tx.push(i).is_ok());
            assert_eq!(rx.pop(), Some(i));
        }
    }

    #[test]
    fn partial_fill_drain_cycles() {
        let (tx, rx) = ring_buffer::<u64>(8);

        for round in 0..100 {
            for i in 0..4 {
                assert!(tx.push(round * 4 + i).is_ok());
            }

            for i in 0..4 {
                assert_eq!(rx.pop(), Some(round * 4 + i));
            }
        }
    }

    // ============================================================================
    // Multiple Producers
    // ============================================================================

    #[test]
    fn two_producers_single_consumer() {
        use std::thread;

        let (tx, rx) = ring_buffer::<u64>(64);
        let tx2 = tx.clone();

        let h1 = thread::spawn(move || {
            for i in 0..1000 {
                while tx.push(i).is_err() {
                    std::hint::spin_loop();
                }
            }
        });

        let h2 = thread::spawn(move || {
            for i in 1000..2000 {
                while tx2.push(i).is_err() {
                    std::hint::spin_loop();
                }
            }
        });

        let mut received = Vec::new();
        while received.len() < 2000 {
            if let Some(val) = rx.pop() {
                received.push(val);
            } else {
                std::hint::spin_loop();
            }
        }

        h1.join().unwrap();
        h2.join().unwrap();

        // All values received (order not guaranteed across producers)
        received.sort_unstable();
        assert_eq!(received, (0..2000).collect::<Vec<_>>());
    }

    #[test]
    fn four_producers_single_consumer() {
        use std::thread;

        let (tx, rx) = ring_buffer::<u64>(256);

        let handles: Vec<_> = (0..4)
            .map(|p| {
                let tx = tx.clone();
                thread::spawn(move || {
                    for i in 0..1000 {
                        let val = p * 1000 + i;
                        while tx.push(val).is_err() {
                            std::hint::spin_loop();
                        }
                    }
                })
            })
            .collect();

        drop(tx); // Drop original producer

        let mut received = Vec::new();
        while received.len() < 4000 {
            if let Some(val) = rx.pop() {
                received.push(val);
            } else if rx.is_disconnected() && received.len() < 4000 {
                // Keep trying if not all received
                std::hint::spin_loop();
            } else {
                std::hint::spin_loop();
            }
        }

        for h in handles {
            h.join().unwrap();
        }

        received.sort_unstable();
        let expected: Vec<u64> = (0..4)
            .flat_map(|p| (0..1000).map(move |i| p * 1000 + i))
            .collect();
        let mut expected_sorted = expected;
        expected_sorted.sort_unstable();
        assert_eq!(received, expected_sorted);
    }

    // ============================================================================
    // Single Slot
    // ============================================================================

    #[test]
    fn single_slot_bounded() {
        let (tx, rx) = ring_buffer::<u64>(1);

        assert!(tx.push(1).is_ok());
        assert!(tx.push(2).is_err());

        assert_eq!(rx.pop(), Some(1));
        assert!(tx.push(2).is_ok());
    }

    // ============================================================================
    // Disconnection
    // ============================================================================

    #[test]
    fn producer_disconnected() {
        let (tx, rx) = ring_buffer::<u64>(4);

        assert!(!rx.is_disconnected());
        drop(tx);
        assert!(rx.is_disconnected());
    }

    #[test]
    fn consumer_disconnected() {
        let (tx, rx) = ring_buffer::<u64>(4);

        assert!(!tx.is_disconnected());
        drop(rx);
        assert!(tx.is_disconnected());
    }

    #[test]
    fn multiple_producers_one_disconnects() {
        let (tx1, rx) = ring_buffer::<u64>(4);
        let tx2 = tx1.clone();

        assert!(!rx.is_disconnected());
        drop(tx1);
        assert!(!rx.is_disconnected()); // tx2 still alive
        drop(tx2);
        assert!(rx.is_disconnected());
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

        let (tx, rx) = ring_buffer::<DropCounter>(4);

        let _ = tx.push(DropCounter);
        let _ = tx.push(DropCounter);
        let _ = tx.push(DropCounter);

        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), 0);

        drop(tx);
        drop(rx);

        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), 3);
    }

    // ============================================================================
    // Special Types
    // ============================================================================

    #[test]
    fn zero_sized_type() {
        let (tx, rx) = ring_buffer::<()>(8);

        let _ = tx.push(());
        let _ = tx.push(());

        assert_eq!(rx.pop(), Some(()));
        assert_eq!(rx.pop(), Some(()));
        assert_eq!(rx.pop(), None);
    }

    #[test]
    fn string_type() {
        let (tx, rx) = ring_buffer::<String>(4);

        let _ = tx.push("hello".to_string());
        let _ = tx.push("world".to_string());

        assert_eq!(rx.pop(), Some("hello".to_string()));
        assert_eq!(rx.pop(), Some("world".to_string()));
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

        let (tx, rx) = ring_buffer::<LargeMessage>(8);

        let msg = LargeMessage { data: [42u8; 256] };
        assert!(tx.push(msg).is_ok());

        let received = rx.pop().unwrap();
        assert_eq!(received.data[0], 42);
        assert_eq!(received.data[255], 42);
    }

    #[test]
    fn multiple_laps() {
        let (tx, rx) = ring_buffer::<u64>(4);

        // 10 full laps through 4-slot buffer
        for i in 0..40 {
            assert!(tx.push(i).is_ok());
            assert_eq!(rx.pop(), Some(i));
        }
    }

    #[test]
    fn capacity_rounds_to_power_of_two() {
        let (tx, _) = ring_buffer::<u64>(100);
        assert_eq!(tx.capacity(), 128);

        let (tx, _) = ring_buffer::<u64>(1000);
        assert_eq!(tx.capacity(), 1024);
    }

    // ============================================================================
    // Stress Tests
    // ============================================================================

    #[test]
    fn stress_single_producer() {
        use std::thread;

        const COUNT: u64 = 100_000;

        let (tx, rx) = ring_buffer::<u64>(1024);

        let producer = thread::spawn(move || {
            for i in 0..COUNT {
                while tx.push(i).is_err() {
                    std::hint::spin_loop();
                }
            }
        });

        let consumer = thread::spawn(move || {
            let mut sum = 0u64;
            let mut received = 0u64;
            while received < COUNT {
                if let Some(val) = rx.pop() {
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
    fn stress_multiple_producers() {
        use std::thread;

        const PRODUCERS: u64 = 4;
        const PER_PRODUCER: u64 = 25_000;
        const TOTAL: u64 = PRODUCERS * PER_PRODUCER;

        let (tx, rx) = ring_buffer::<u64>(1024);

        let handles: Vec<_> = (0..PRODUCERS)
            .map(|_| {
                let tx = tx.clone();
                thread::spawn(move || {
                    for i in 0..PER_PRODUCER {
                        while tx.push(i).is_err() {
                            std::hint::spin_loop();
                        }
                    }
                })
            })
            .collect();

        drop(tx);

        let mut received = 0u64;
        while received < TOTAL {
            if rx.pop().is_some() {
                received += 1;
            } else {
                std::hint::spin_loop();
            }
        }

        for h in handles {
            h.join().unwrap();
        }

        assert_eq!(received, TOTAL);
    }
}
