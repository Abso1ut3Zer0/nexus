//! Single-producer multi-consumer bounded queue.
//!
//! A lock-free ring buffer optimized for one producer thread fanning out to
//! multiple consumer threads. Uses Vyukov-style turn counters with CAS-based
//! head claiming for consumers.
//!
//! # Design
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────┐
//! │ Shared (Arc):                                                   │
//! │   head: CachePadded<AtomicUsize>   ← Consumers CAS here         │
//! │   tail: CachePadded<AtomicUsize>   ← Producer publishes here    │
//! │   producer_alive: AtomicBool       ← Disconnection detection    │
//! │   slots: *mut Slot<T>              ← Per-slot turn counters     │
//! └─────────────────────────────────────────────────────────────────┘
//!
//! ┌─────────────────────┐     ┌─────────────────────┐
//! │ Producer (!Clone):  │     │ Consumer (Clone):    │
//! │   local_tail        │     │   shared: Arc        │
//! │   shared: Arc       │     └─────────────────────┘
//! └─────────────────────┘
//! ```
//!
//! The producer writes directly (no CAS) since it's the sole writer. Consumers
//! compete via CAS on the head index to claim slots. After claiming, the consumer
//! reads the data and advances the turn counter for the next producer lap.
//!
//! # Turn Counter Protocol
//!
//! For slot at index `i` on lap `turn`:
//! - `turn * 2`: Slot is ready for producer to write
//! - `turn * 2 + 1`: Slot contains data, ready for consumer
//!
//! # Disconnection
//!
//! Unlike MPSC where `Arc::strong_count == 1` detects disconnection on both
//! sides, SPMC consumers hold Arc refs to each other. An `AtomicBool` tracks
//! whether the producer is alive so consumers can detect disconnection.
//!
//! # Example
//!
//! ```
//! use nexus_queue::spmc;
//! use std::thread;
//!
//! let (tx, rx) = spmc::ring_buffer::<u64>(1024);
//!
//! let rx2 = rx.clone();
//! let rx1 = rx;
//! let h1 = thread::spawn(move || {
//!     let mut received = Vec::new();
//!     loop {
//!         if let Some(v) = rx1.pop() {
//!             received.push(v);
//!         } else if rx1.is_disconnected() {
//!             while let Some(v) = rx1.pop() { received.push(v); }
//!             break;
//!         } else {
//!             std::hint::spin_loop();
//!         }
//!     }
//!     received
//! });
//! let h2 = thread::spawn(move || {
//!     let mut received = Vec::new();
//!     loop {
//!         if let Some(v) = rx2.pop() {
//!             received.push(v);
//!         } else if rx2.is_disconnected() {
//!             while let Some(v) = rx2.pop() { received.push(v); }
//!             break;
//!         } else {
//!             std::hint::spin_loop();
//!         }
//!     }
//!     received
//! });
//!
//! for i in 0..200 {
//!     while tx.push(i).is_err() { std::hint::spin_loop(); }
//! }
//! drop(tx);
//!
//! let mut all: Vec<_> = h1.join().unwrap();
//! all.extend(h2.join().unwrap());
//! all.sort();
//! assert_eq!(all, (0..200).collect::<Vec<_>>());
//! ```

use std::cell::Cell;
use std::fmt;
use std::mem::MaybeUninit;

use crate::loom_impl::{Arc, AtomicBool, AtomicUsize, Ordering, UnsafeCell};

use crossbeam_utils::CachePadded;

use crate::Full;

/// Creates a bounded SPMC ring buffer. Renamed to [`ring_buffer`].
#[deprecated(since = "1.3.0", note = "renamed to ring_buffer()")]
#[inline]
pub fn bounded<T>(capacity: usize) -> (Producer<T>, Consumer<T>) {
    ring_buffer(capacity)
}

/// Creates a bounded SPMC queue with the given capacity.
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

    // Allocate slots with turn counters initialized to 0 (ready for turn 0 producer)
    let slots: Vec<Slot<T>> = (0..capacity)
        .map(|_| Slot {
            turn: AtomicUsize::new(0),
            data: UnsafeCell::new(MaybeUninit::uninit()),
        })
        .collect();
    let slots = Box::into_raw(slots.into_boxed_slice()) as *mut Slot<T>;

    let shift = capacity.trailing_zeros();

    let shared = Arc::new(Shared {
        head: CachePadded::new(AtomicUsize::new(0)),
        tail: CachePadded::new(AtomicUsize::new(0)),
        producer_alive: AtomicBool::new(true),
        slots,
        capacity,
        shift,
        mask,
    });

    (
        Producer {
            local_tail: Cell::new(0),
            slots,
            mask,
            shift,
            shared: Arc::clone(&shared),
        },
        Consumer {
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

/// Shared state between the producer and consumers.
// repr(C): Guarantees field order for cache line layout.
#[repr(C)]
struct Shared<T> {
    /// Head index - consumers CAS on this to claim slots.
    head: CachePadded<AtomicUsize>,
    /// Tail index - written by producer on drop for Shared::drop cleanup.
    tail: CachePadded<AtomicUsize>,
    /// Whether the producer is still alive (for consumer disconnection detection).
    producer_alive: AtomicBool,
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

/// The producer endpoint of an SPMC queue.
///
/// This endpoint cannot be cloned - only one producer thread is allowed.
/// The single-writer design eliminates CAS contention on the tail index.
// repr(C): Hot fields at struct base share cache line with struct pointer.
#[repr(C)]
pub struct Producer<T> {
    /// Local tail index - only this thread reads/writes.
    local_tail: Cell<usize>,
    /// Cached slots pointer (avoids Arc deref on hot path).
    slots: *mut Slot<T>,
    /// Cached mask (avoids Arc deref on hot path).
    mask: usize,
    /// Cached shift for fast division (log2(capacity)).
    shift: u32,
    shared: Arc<Shared<T>>,
}

// SAFETY: Producer can be sent to another thread. It has exclusive write access
// to slots (via turn protocol) and maintains the tail index.
unsafe impl<T: Send> Send for Producer<T> {}

impl<T> Producer<T> {
    /// Pushes a value into the queue.
    ///
    /// Returns `Err(Full(value))` if the queue is full, returning ownership
    /// of the value to the caller for backpressure handling.
    ///
    /// No CAS required - single writer principle.
    #[inline]
    #[must_use = "push returns Err if full, which should be handled"]
    pub fn push(&self, value: T) -> Result<(), Full<T>> {
        let tail = self.local_tail.get();
        // SAFETY: slots pointer is valid for the lifetime of shared.
        let slot = unsafe { &*self.slots.add(tail & self.mask) };
        let turn = tail >> self.shift;

        // Check if slot is ready (consumer has freed it).
        if slot.turn.load(Ordering::Acquire) != turn * 2 {
            return Err(Full(value));
        }

        // SAFETY: Turn counter confirms slot is free for this lap.
        slot.data.with_mut(|ptr| unsafe { (*ptr).write(value) });

        // Signal ready for consumer: turn * 2 + 1
        slot.turn.store(turn * 2 + 1, Ordering::Release);

        self.local_tail.set(tail.wrapping_add(1));

        Ok(())
    }

    /// Returns the capacity of the queue.
    #[inline]
    pub fn capacity(&self) -> usize {
        1 << self.shift
    }

    /// Returns `true` if all consumers have been dropped.
    #[inline]
    pub fn is_disconnected(&self) -> bool {
        Arc::strong_count(&self.shared) == 1
    }
}

impl<T> Drop for Producer<T> {
    fn drop(&mut self) {
        // Publish final tail for Shared::drop cleanup
        self.shared
            .tail
            .store(self.local_tail.get(), Ordering::Relaxed);
        self.shared.producer_alive.store(false, Ordering::Release);
    }
}

impl<T> fmt::Debug for Producer<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Producer")
            .field("capacity", &self.capacity())
            .finish_non_exhaustive()
    }
}

/// The consumer endpoint of an SPMC queue.
///
/// This endpoint can be cloned to create additional consumers. Each clone
/// competes via CAS on the shared head index.
// repr(C): Hot fields at struct base share cache line with struct pointer.
#[repr(C)]
pub struct Consumer<T> {
    /// Cached slots pointer (avoids Arc deref on hot path).
    slots: *mut Slot<T>,
    /// Cached mask (avoids Arc deref on hot path).
    mask: usize,
    /// Cached shift for fast division (log2(capacity)).
    shift: u32,
    shared: Arc<Shared<T>>,
}

impl<T> Clone for Consumer<T> {
    fn clone(&self) -> Self {
        Consumer {
            slots: self.slots,
            mask: self.mask,
            shift: self.shift,
            shared: Arc::clone(&self.shared),
        }
    }
}

// SAFETY: Consumer can be sent to another thread. Each Consumer instance is
// used by one thread (not Sync - use clone() for multiple threads).
unsafe impl<T: Send> Send for Consumer<T> {}

impl<T> Consumer<T> {
    /// Pops a value from the queue.
    ///
    /// Returns `None` if the queue is empty.
    ///
    /// This method spins internally on CAS contention but returns immediately
    /// when the queue is actually empty.
    #[inline]
    pub fn pop(&self) -> Option<T> {
        let mut spin_count = 0u32;

        loop {
            let head = self.shared.head.load(Ordering::Relaxed);

            // SAFETY: slots pointer is valid for the lifetime of shared.
            let slot = unsafe { &*self.slots.add(head & self.mask) };
            let turn = head >> self.shift;

            let stamp = slot.turn.load(Ordering::Acquire);

            if stamp == turn * 2 + 1 {
                // Slot has data - try to claim it
                if self
                    .shared
                    .head
                    .compare_exchange_weak(
                        head,
                        head.wrapping_add(1),
                        Ordering::Relaxed,
                        Ordering::Relaxed,
                    )
                    .is_ok()
                {
                    // SAFETY: We own this slot via successful CAS.
                    let value = slot
                        .data
                        .with_mut(|ptr| unsafe { (*ptr).assume_init_read() });

                    // Signal slot is free for next lap: (turn + 1) * 2
                    slot.turn.store((turn + 1) * 2, Ordering::Release);

                    return Some(value);
                }

                // CAS failed - another consumer claimed it, retry with backoff
                let spins = 1 << spin_count.min(6);
                for _ in 0..spins {
                    std::hint::spin_loop();
                }
                spin_count += 1;
            } else {
                // Slot not ready - queue is empty
                return None;
            }
        }
    }

    /// Returns the capacity of the queue.
    #[inline]
    pub fn capacity(&self) -> usize {
        1 << self.shift
    }

    /// Returns `true` if the producer has been dropped.
    #[inline]
    pub fn is_disconnected(&self) -> bool {
        !self.shared.producer_alive.load(Ordering::Acquire)
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
    fn interleaved_single_consumer() {
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
    // Multiple Consumers
    // ============================================================================

    #[test]
    fn two_consumers_single_producer() {
        use std::thread;

        let (tx, rx) = ring_buffer::<u64>(64);
        let rx2 = rx.clone();

        let rx1 = rx;
        let h1 = thread::spawn(move || {
            let mut received = Vec::new();
            loop {
                if let Some(val) = rx1.pop() {
                    received.push(val);
                } else if rx1.is_disconnected() {
                    while let Some(val) = rx1.pop() {
                        received.push(val);
                    }
                    break;
                } else {
                    std::hint::spin_loop();
                }
            }
            received
        });

        let h2 = thread::spawn(move || {
            let mut received = Vec::new();
            loop {
                if let Some(val) = rx2.pop() {
                    received.push(val);
                } else if rx2.is_disconnected() {
                    while let Some(val) = rx2.pop() {
                        received.push(val);
                    }
                    break;
                } else {
                    std::hint::spin_loop();
                }
            }
            received
        });

        for i in 0..2000 {
            while tx.push(i).is_err() {
                std::hint::spin_loop();
            }
        }
        drop(tx);

        let mut received = h1.join().unwrap();
        received.extend(h2.join().unwrap());

        // All values received (order not guaranteed across consumers)
        received.sort_unstable();
        assert_eq!(received, (0..2000).collect::<Vec<_>>());
    }

    #[test]
    fn four_consumers_single_producer() {
        use std::thread;

        let (tx, rx) = ring_buffer::<u64>(256);

        let handles: Vec<_> = (0..4)
            .map(|_| {
                let rx = rx.clone();
                thread::spawn(move || {
                    let mut received = Vec::new();
                    loop {
                        if let Some(val) = rx.pop() {
                            received.push(val);
                        } else if rx.is_disconnected() {
                            while let Some(val) = rx.pop() {
                                received.push(val);
                            }
                            break;
                        } else {
                            std::hint::spin_loop();
                        }
                    }
                    received
                })
            })
            .collect();

        drop(rx); // Drop original consumer

        for i in 0..4000u64 {
            while tx.push(i).is_err() {
                std::hint::spin_loop();
            }
        }
        drop(tx);

        let mut received = Vec::new();
        for h in handles {
            received.extend(h.join().unwrap());
        }

        received.sort_unstable();
        assert_eq!(received, (0..4000).collect::<Vec<_>>());
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
    fn consumer_detects_producer_drop() {
        let (tx, rx) = ring_buffer::<u64>(4);

        assert!(!rx.is_disconnected());
        drop(tx);
        assert!(rx.is_disconnected());
    }

    #[test]
    fn producer_detects_all_consumers_drop() {
        let (tx, rx) = ring_buffer::<u64>(4);

        assert!(!tx.is_disconnected());
        drop(rx);
        assert!(tx.is_disconnected());
    }

    #[test]
    fn one_consumer_drops_others_alive() {
        let (tx, rx) = ring_buffer::<u64>(4);
        let rx2 = rx.clone();

        assert!(!tx.is_disconnected());
        drop(rx);
        assert!(!tx.is_disconnected()); // rx2 still alive
        assert!(!rx2.is_disconnected()); // producer still alive
        drop(rx2);
        assert!(tx.is_disconnected());
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
    fn stress_single_consumer() {
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
    fn stress_multiple_consumers() {
        use std::thread;

        const CONSUMERS: usize = 4;
        const TOTAL: u64 = 100_000;

        let (tx, rx) = ring_buffer::<u64>(1024);

        let handles: Vec<_> = (0..CONSUMERS)
            .map(|_| {
                let rx = rx.clone();
                thread::spawn(move || {
                    let mut received = Vec::new();
                    loop {
                        if let Some(val) = rx.pop() {
                            received.push(val);
                        } else if rx.is_disconnected() {
                            while let Some(val) = rx.pop() {
                                received.push(val);
                            }
                            break;
                        } else {
                            std::hint::spin_loop();
                        }
                    }
                    received
                })
            })
            .collect();

        drop(rx);

        let producer = thread::spawn(move || {
            for i in 0..TOTAL {
                while tx.push(i).is_err() {
                    std::hint::spin_loop();
                }
            }
        });

        producer.join().unwrap();

        let mut all_received = Vec::new();
        for h in handles {
            all_received.extend(h.join().unwrap());
        }

        all_received.sort_unstable();
        assert_eq!(all_received, (0..TOTAL).collect::<Vec<_>>());
    }
}
