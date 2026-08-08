//! Single-producer single-consumer bounded queue.
//!
//! A lock-free ring buffer optimized for exactly one producer thread and one
//! consumer thread. Uses cached indices to minimize atomic operations on the
//! hot path.
//!
//! # Design
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────┐
//! │ Shared (Arc):                                               │
//! │   tail: CachePadded<AtomicUsize>   ← Producer writes        │
//! │   head: CachePadded<AtomicUsize>   ← Consumer writes        │
//! │   buffer: *mut T                                            │
//! └─────────────────────────────────────────────────────────────┘
//!
//! ┌─────────────────────┐     ┌─────────────────────┐
//! │ Producer:           │     │ Consumer:           │
//! │   local_tail        │     │   local_head        │
//! │   cached_head       │     │   cached_tail       │
//! │   buffer (cached)   │     │   buffer (cached)   │
//! │   mask (cached)     │     │   mask (cached)     │
//! └─────────────────────┘     └─────────────────────┘
//! ```
//!
//! Producer and consumer each cache the buffer pointer and mask locally to
//! avoid Arc dereference on every operation. They also maintain a cached copy
//! of the other's index, only refreshing from the atomic when the cache
//! indicates the queue is full (producer) or empty (consumer).
//!
//! Head and tail are on separate cache lines (128-byte padding) to avoid false
//! sharing between producer and consumer threads.
//!
//! # Example
//!
//! ```
//! use nexus_queue::spsc;
//!
//! let (tx, rx) = spsc::ring_buffer::<u64>(1024);
//!
//! tx.push(42).unwrap();
//! assert_eq!(rx.pop(), Some(42));
//! ```

use std::cell::Cell;
use std::fmt;
#[cfg(not(loom))]
use std::mem::ManuallyDrop;
#[cfg(loom)]
use std::mem::MaybeUninit;

use crossbeam_utils::CachePadded;

use crate::Full;
#[cfg(loom)]
use crate::loom_impl::UnsafeCell;
use crate::loom_impl::{Arc, AtomicUsize, Ordering, fence};

/// Creates a bounded SPSC ring buffer with the given capacity.
///
/// Capacity is rounded up to the next power of two.
///
/// # Panics
///
/// Panics if `capacity` is zero.
#[cfg(not(loom))]
pub fn ring_buffer<T>(capacity: usize) -> (Producer<T>, Consumer<T>) {
    assert!(capacity > 0, "capacity must be non-zero");

    let capacity = capacity
        .checked_next_power_of_two()
        .expect("capacity too large (must be <= usize::MAX / 2)");
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
            local_tail: Cell::new(0),
            cached_head: Cell::new(0),
            buffer,
            mask,
            shared: Arc::clone(&shared),
        },
        Consumer {
            local_head: Cell::new(0),
            cached_tail: Cell::new(0),
            buffer,
            mask,
            shared,
        },
    )
}

#[cfg(loom)]
/// Creates a bounded SPSC ring buffer with the given capacity (loom variant).
pub fn ring_buffer<T>(capacity: usize) -> (Producer<T>, Consumer<T>) {
    assert!(capacity > 0, "capacity must be non-zero");

    let capacity = capacity
        .checked_next_power_of_two()
        .expect("capacity too large (must be <= usize::MAX / 2)");
    let mask = capacity - 1;

    let buffer: Vec<UnsafeCell<MaybeUninit<T>>> = (0..capacity)
        .map(|_| UnsafeCell::new(MaybeUninit::uninit()))
        .collect();

    let shared = Arc::new(Shared {
        tail: CachePadded::new(AtomicUsize::new(0)),
        head: CachePadded::new(AtomicUsize::new(0)),
        buffer: buffer.into_boxed_slice(),
        mask,
    });

    (
        Producer {
            local_tail: Cell::new(0),
            cached_head: Cell::new(0),
            mask,
            shared: Arc::clone(&shared),
        },
        Consumer {
            local_head: Cell::new(0),
            cached_tail: Cell::new(0),
            mask,
            shared,
        },
    )
}

#[cfg(not(loom))]
#[repr(C)]
struct Shared<T> {
    tail: CachePadded<AtomicUsize>,
    head: CachePadded<AtomicUsize>,
    buffer: *mut T,
    mask: usize,
}

#[cfg(loom)]
struct Shared<T> {
    tail: CachePadded<AtomicUsize>,
    head: CachePadded<AtomicUsize>,
    buffer: Box<[UnsafeCell<MaybeUninit<T>>]>,
    mask: usize,
}

// SAFETY: Shared only contains atomics and a raw pointer (or boxed slice under loom).
// The buffer is only accessed through Producer (write) and Consumer (read), which
// are !Sync. T: Send ensures the data can be transferred between threads.
unsafe impl<T: Send> Send for Shared<T> {}
// SAFETY: same as Send — all shared state is atomic; access is coordinated by
// Producer (write) and Consumer (read), which are !Sync.
unsafe impl<T: Send> Sync for Shared<T> {}

#[cfg(not(loom))]
impl<T> Drop for Shared<T> {
    fn drop(&mut self) {
        let head = self.head.load(Ordering::Relaxed);
        let tail = self.tail.load(Ordering::Relaxed);

        let mut i = head;
        while i != tail {
            // SAFETY: Slots in [head, tail) contain initialized values. We have
            // exclusive access (drop requires &mut self, both endpoints dropped).
            unsafe { self.buffer.add(i & self.mask).drop_in_place() };
            i = i.wrapping_add(1);
        }

        // SAFETY: buffer was allocated by Vec::with_capacity(capacity) in ring_buffer().
        // We pass len=0 because we already dropped all elements above.
        unsafe {
            let capacity = self.mask + 1;
            let _ = Vec::from_raw_parts(self.buffer, 0, capacity);
        }
    }
}

#[cfg(loom)]
impl<T> Drop for Shared<T> {
    fn drop(&mut self) {
        let head = self.head.load(Ordering::Relaxed);
        let tail = self.tail.load(Ordering::Relaxed);

        let mut i = head;
        while i != tail {
            // SAFETY: Slots in [head, tail) contain initialized values. We have
            // exclusive access (drop requires &mut self, both endpoints dropped).
            self.buffer[i & self.mask].with_mut(|ptr| unsafe { (*ptr).assume_init_drop() });
            i = i.wrapping_add(1);
        }
    }
}

/// The producer endpoint of an SPSC queue.
///
/// This endpoint can only push values into the queue.
#[cfg(not(loom))]
#[repr(C)]
pub struct Producer<T> {
    local_tail: Cell<usize>,
    cached_head: Cell<usize>,
    buffer: *mut T,
    mask: usize,
    shared: Arc<Shared<T>>,
}

/// The producer endpoint of an SPSC queue.
///
/// This endpoint can only push values into the queue.
#[cfg(loom)]
pub struct Producer<T> {
    local_tail: Cell<usize>,
    cached_head: Cell<usize>,
    mask: usize,
    shared: Arc<Shared<T>>,
}

// SAFETY: Producer can be sent to another thread. It has exclusive write access
// to the buffer slots and maintains the tail index. T: Send ensures the data
// can be transferred.
unsafe impl<T: Send> Send for Producer<T> {}

impl<T> Producer<T> {
    /// Pushes a value into the queue.
    ///
    /// Returns `Err(Full(value))` if the queue is full, returning ownership
    /// of the value to the caller.
    #[inline]
    #[must_use = "push returns Err if full, which should be handled"]
    pub fn push(&self, value: T) -> Result<(), Full<T>> {
        let tail = self.local_tail.get();

        if tail.wrapping_sub(self.cached_head.get()) > self.mask {
            self.cached_head
                .set(self.shared.head.load(Ordering::Relaxed));

            fence(Ordering::Acquire);
            if tail.wrapping_sub(self.cached_head.get()) > self.mask {
                return Err(Full(value));
            }
        }

        // SAFETY: We verified tail - cached_head <= mask, so the slot is not occupied
        // by unconsumed data. tail & mask gives a valid index within the buffer.
        #[cfg(not(loom))]
        unsafe {
            self.buffer.add(tail & self.mask).write(value);
        }
        // SAFETY: Same invariant as above — slot is unoccupied. Loom UnsafeCell
        // requires with_mut for access; the MaybeUninit write is valid on uninit memory.
        #[cfg(loom)]
        self.shared.buffer[tail & self.mask].with_mut(|ptr| unsafe { (*ptr).write(value) });

        let new_tail = tail.wrapping_add(1);
        fence(Ordering::Release);

        self.shared.tail.store(new_tail, Ordering::Relaxed);
        self.local_tail.set(new_tail);

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
#[cfg(not(loom))]
#[repr(C)]
pub struct Consumer<T> {
    local_head: Cell<usize>,
    cached_tail: Cell<usize>,
    buffer: *mut T,
    mask: usize,
    shared: Arc<Shared<T>>,
}

/// The consumer endpoint of an SPSC queue.
///
/// This endpoint can only pop values from the queue.
#[cfg(loom)]
pub struct Consumer<T> {
    local_head: Cell<usize>,
    cached_tail: Cell<usize>,
    mask: usize,
    shared: Arc<Shared<T>>,
}

// SAFETY: Consumer can be sent to another thread. It has exclusive read access
// to buffer slots and maintains the head index. T: Send ensures the data can
// be transferred.
unsafe impl<T: Send> Send for Consumer<T> {}

impl<T> Consumer<T> {
    /// Pops a value from the queue.
    ///
    /// Returns `None` if the queue is empty.
    #[inline]
    pub fn pop(&self) -> Option<T> {
        let head = self.local_head.get();

        if head == self.cached_tail.get() {
            self.cached_tail
                .set(self.shared.tail.load(Ordering::Relaxed));
            fence(Ordering::Acquire);

            if head == self.cached_tail.get() {
                return None;
            }
        }

        // SAFETY: We verified head != cached_tail, so the slot contains valid data
        // written by the producer. head & mask gives a valid index within the buffer.
        #[cfg(not(loom))]
        let value = unsafe { self.buffer.add(head & self.mask).read() };
        // SAFETY: Same invariant as above — slot contains valid data written by
        // the producer. Loom UnsafeCell requires with_mut; assume_init_read moves
        // the value out, and the slot will not be read again until re-written.
        #[cfg(loom)]
        let value = self.shared.buffer[head & self.mask]
            .with_mut(|ptr| unsafe { (*ptr).assume_init_read() });

        let new_head = head.wrapping_add(1);
        fence(Ordering::Release);

        self.shared.head.store(new_head, Ordering::Relaxed);
        self.local_head.set(new_head);

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
        let (prod, cons) = ring_buffer::<u64>(4);

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
        let (_, cons) = ring_buffer::<u64>(4);
        assert_eq!(cons.pop(), None);
        assert_eq!(cons.pop(), None);
    }

    #[test]
    fn fill_then_drain() {
        let (prod, cons) = ring_buffer::<u64>(4);

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
        let (prod, _cons) = ring_buffer::<u64>(4);

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
        let (prod, cons) = ring_buffer::<u64>(8);

        for i in 0..1000 {
            assert!(prod.push(i).is_ok());
            assert_eq!(cons.pop(), Some(i));
        }
    }

    #[test]
    fn partial_fill_drain_cycles() {
        let (prod, cons) = ring_buffer::<u64>(8);

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
        let (prod, cons) = ring_buffer::<u64>(1);

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

        let (prod, cons) = ring_buffer::<DropCounter>(4);

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

        let (prod, cons) = ring_buffer::<u64>(64);

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
        let (prod, cons) = ring_buffer::<()>(8);

        let _ = prod.push(());
        let _ = prod.push(());

        assert_eq!(cons.pop(), Some(()));
        assert_eq!(cons.pop(), Some(()));
        assert_eq!(cons.pop(), None);
    }

    #[test]
    fn string_type() {
        let (prod, cons) = ring_buffer::<String>(4);

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

        let (prod, cons) = ring_buffer::<LargeMessage>(8);

        let msg = LargeMessage { data: [42u8; 256] };
        assert!(prod.push(msg).is_ok());

        let received = cons.pop().unwrap();
        assert_eq!(received.data[0], 42);
        assert_eq!(received.data[255], 42);
    }

    #[test]
    fn multiple_laps() {
        let (prod, cons) = ring_buffer::<u64>(4);

        // 10 full laps through 4-slot buffer
        for i in 0..40 {
            assert!(prod.push(i).is_ok());
            assert_eq!(cons.pop(), Some(i));
        }
    }

    #[test]
    fn fifo_order_cross_thread() {
        use std::thread;

        let (prod, cons) = ring_buffer::<u64>(64);

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

        let (prod, cons) = ring_buffer::<u64>(1024);

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
