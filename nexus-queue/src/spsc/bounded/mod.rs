//! Single-producer single-consumer (SPSC) bounded queue.
//!
//! This is the fastest queue variant, using only acquire/release semantics
//! with no compare-and-swap operations on the hot path.
//!
//! # Example
//!
//! ```
//! use nexus_queue::spsc;
//!
//! let (tx, rx) = spsc::bounded::channel::<u64>(1024);
//!
//! tx.try_send(1).unwrap();
//! tx.try_send(2).unwrap();
//!
//! assert_eq!(rx.try_recv().unwrap(), 1);
//! assert_eq!(rx.try_recv().unwrap(), 2);
//! ```
//!
//! # Disconnection
//!
//! When either the [`Sender`] or [`Receiver`] is dropped, the channel becomes
//! disconnected. The remaining endpoint will observe this:
//!
//! - [`Sender::try_send`] returns [`TrySendError::Disconnected`] if the receiver is dropped
//! - [`Receiver::try_recv`] returns [`TryRecvError::Disconnected`] if the sender is dropped
//!   AND the queue is empty
//!
//! # Performance Notes
//!
//! The hot path (when queue is neither full nor empty) performs:
//! - Zero atomic operations for the fast check (uses cached indices)
//! - One atomic store with Release ordering to publish
//!
//! Atomic loads only occur on the slow path when the queue appears full/empty.

mod ring;

use std::cell::Cell;
use std::fmt;
use std::ptr::NonNull;
use std::sync::atomic::{AtomicUsize, Ordering};

use ring::RingBuffer;

/// Creates a new SPSC channel with the given capacity.
///
/// The actual capacity will be rounded up to the next power of two
/// (minimum 2) for efficient index masking.
///
/// # Example
///
/// ```
/// use nexus_queue::spsc;
///
/// let (tx, rx) = spsc::bounded::channel::<String>(100);
/// // Actual capacity will be 128 (next power of two)
/// assert_eq!(tx.capacity(), 128);
/// ```
pub fn channel<T>(capacity: usize) -> (Sender<T>, Receiver<T>) {
    let inner = RingBuffer::<T>::allocate(capacity);
    let rb = unsafe { inner.as_ref() };

    (
        Sender {
            inner,
            // Cached hot fields
            buffer: rb.buffer(),
            mask: rb.mask(),
            capacity: rb.capacity(),
            tail_atomic: rb.tail_ptr(),
            // Local state
            local_tail: Cell::new(0),
            cached_head: Cell::new(0),
        },
        Receiver {
            inner,
            // Cached hot fields
            buffer: rb.buffer(),
            mask: rb.mask(),
            head_atomic: rb.head_ptr(),
            // Local state
            local_head: Cell::new(0),
            cached_tail: Cell::new(0),
        },
    )
}

/// The sending half of an SPSC channel.
///
/// This struct can only be owned by a single thread at a time (implements `Send` but not `Sync`).
pub struct Sender<T> {
    inner: NonNull<RingBuffer<T>>,

    // === Cached hot fields (avoid indirection through inner) ===
    buffer: *mut T,
    mask: usize,
    capacity: usize,
    tail_atomic: *const AtomicUsize,

    // === Local state ===
    /// Our write position (authoritative, only we update this)
    local_tail: Cell<usize>,
    /// Cached snapshot of consumer's head position.
    /// Only refreshed when queue appears full.
    cached_head: Cell<usize>,
}

// Safety: Sender can be sent to another thread, but cannot be shared
// across threads (not Sync). The ring buffer is properly synchronized.
unsafe impl<T: Send> Send for Sender<T> {}

impl<T> Sender<T> {
    /// Attempts to send a value into the queue.
    ///
    /// # Errors
    ///
    /// Returns `Err(TrySendError::Full(value))` if the queue is full.
    /// Returns `Err(TrySendError::Disconnected(value))` if the receiver has been dropped.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_queue::spsc::{self, bounded::TrySendError};
    ///
    /// let (tx, rx) = spsc::bounded::channel::<u32>(2);
    ///
    /// assert!(tx.try_send(1).is_ok());
    /// assert!(tx.try_send(2).is_ok());
    ///
    /// // Queue is now full
    /// assert!(matches!(tx.try_send(3), Err(TrySendError::Full(3))));
    /// ```
    #[inline]
    pub fn try_send(&self, value: T) -> Result<(), TrySendError<T>> {
        let tail = self.local_tail.get();

        // Fast path: check cached head (no atomic load!)
        // Queue has space if tail - head < capacity
        if tail.wrapping_sub(self.cached_head.get()) < self.capacity {
            unsafe { self.buffer.add(tail & self.mask).write(value) };
            let next = tail.wrapping_add(1);
            unsafe { (*self.tail_atomic).store(next, Ordering::Release) };
            self.local_tail.set(next);
            return Ok(());
        }

        self.try_send_slow(tail, value)
    }

    #[cold]
    fn try_send_slow(&self, tail: usize, value: T) -> Result<(), TrySendError<T>> {
        let inner = unsafe { self.inner.as_ref() };

        // Refresh cached head from consumer
        let head = inner.load_head();
        self.cached_head.set(head);

        if tail.wrapping_sub(head) < self.capacity {
            unsafe { self.buffer.add(tail & self.mask).write(value) };
            let next = tail.wrapping_add(1);
            unsafe { (*self.tail_atomic).store(next, Ordering::Release) };
            self.local_tail.set(next);
            return Ok(());
        }

        // Queue is truly full - check if receiver disconnected
        if inner.is_receiver_disconnected() {
            return Err(TrySendError::Disconnected(value));
        }

        Err(TrySendError::Full(value))
    }

    /// Returns the capacity of the queue.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// Returns `true` if the receiver has been dropped.
    ///
    /// Note: This may return a stale value; the receiver could be dropped
    /// immediately after this returns `false`.
    #[inline]
    pub fn is_disconnected(&self) -> bool {
        unsafe { self.inner.as_ref().is_receiver_disconnected() }
    }

    /// Returns the number of elements currently in the queue.
    ///
    /// Note: This is a snapshot and may be immediately stale in concurrent contexts.
    #[inline]
    pub fn len(&self) -> usize {
        let inner = unsafe { self.inner.as_ref() };
        let tail = inner.load_tail();
        let head = inner.load_head();
        tail.wrapping_sub(head)
    }

    /// Returns `true` if the queue is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<T> Drop for Sender<T> {
    fn drop(&mut self) {
        unsafe {
            self.inner.as_ref().set_sender_disconnected();
            RingBuffer::release(self.inner);
        }
    }
}

impl<T> fmt::Debug for Sender<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Sender")
            .field("capacity", &self.capacity())
            .field("disconnected", &self.is_disconnected())
            .finish_non_exhaustive()
    }
}

/// The receiving half of an SPSC channel.
///
/// This struct can only be owned by a single thread at a time (implements `Send` but not `Sync`).
pub struct Receiver<T> {
    inner: NonNull<RingBuffer<T>>,

    // === Cached hot fields (avoid indirection through inner) ===
    buffer: *mut T,
    mask: usize,
    head_atomic: *const AtomicUsize,

    // === Local state ===
    /// Our read position (authoritative, only we update this)
    local_head: Cell<usize>,
    /// Cached snapshot of producer's tail position.
    /// Only refreshed when queue appears empty.
    cached_tail: Cell<usize>,
}

// Safety: Receiver can be sent to another thread, but cannot be shared
// across threads (not Sync). The ring buffer is properly synchronized.
unsafe impl<T: Send> Send for Receiver<T> {}

impl<T> Receiver<T> {
    /// Attempts to receive a value from the queue.
    ///
    /// # Errors
    ///
    /// Returns `Err(TryRecvError::Empty)` if the queue is empty.
    /// Returns `Err(TryRecvError::Disconnected)` if the sender has been dropped
    /// AND the queue is empty.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_queue::spsc::{self, bounded::TryRecvError};
    ///
    /// let (tx, rx) = spsc::bounded::channel::<u32>(8);
    ///
    /// // Queue is empty
    /// assert!(matches!(rx.try_recv(), Err(TryRecvError::Empty)));
    ///
    /// tx.try_send(42).unwrap();
    /// assert_eq!(rx.try_recv().unwrap(), 42);
    /// ```
    #[inline]
    pub fn try_recv(&self) -> Result<T, TryRecvError> {
        let head = self.local_head.get();

        // Fast path: check cached tail (no atomic load!)
        // Queue has data if head != tail
        if head != self.cached_tail.get() {
            let value = unsafe { self.buffer.add(head & self.mask).read() };
            let next = head.wrapping_add(1);
            unsafe { (*self.head_atomic).store(next, Ordering::Release) };
            self.local_head.set(next);
            return Ok(value);
        }

        self.try_recv_slow(head)
    }

    #[cold]
    fn try_recv_slow(&self, head: usize) -> Result<T, TryRecvError> {
        let inner = unsafe { self.inner.as_ref() };

        // Refresh cached tail from producer
        let tail = inner.load_tail();
        self.cached_tail.set(tail);

        if head != tail {
            let value = unsafe { self.buffer.add(head & self.mask).read() };
            let next = head.wrapping_add(1);
            unsafe { (*self.head_atomic).store(next, Ordering::Release) };
            self.local_head.set(next);
            return Ok(value);
        }

        // Queue is truly empty - check if sender disconnected
        if inner.is_sender_disconnected() {
            return Err(TryRecvError::Disconnected);
        }

        Err(TryRecvError::Empty)
    }

    /// Returns the capacity of the queue.
    #[inline]
    pub fn capacity(&self) -> usize {
        unsafe { self.inner.as_ref().capacity() }
    }

    /// Returns `true` if the sender has been dropped.
    ///
    /// Note: This may return a stale value; the sender could be dropped
    /// immediately after this returns `false`.
    #[inline]
    pub fn is_disconnected(&self) -> bool {
        unsafe { self.inner.as_ref().is_sender_disconnected() }
    }

    /// Returns the number of elements currently in the queue.
    ///
    /// Note: This is a snapshot and may be immediately stale in concurrent contexts.
    #[inline]
    pub fn len(&self) -> usize {
        let inner = unsafe { self.inner.as_ref() };
        let tail = inner.load_tail();
        let head = inner.load_head();
        tail.wrapping_sub(head)
    }

    /// Returns `true` if the queue is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<T> Drop for Receiver<T> {
    fn drop(&mut self) {
        unsafe {
            self.inner.as_ref().set_receiver_disconnected();
            RingBuffer::release(self.inner);
        }
    }
}

impl<T> fmt::Debug for Receiver<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Receiver")
            .field("capacity", &self.capacity())
            .field("disconnected", &self.is_disconnected())
            .finish_non_exhaustive()
    }
}

/// Error returned by [`Sender::try_send`].
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum TrySendError<T> {
    /// The queue is full. Contains the value that couldn't be sent.
    Full(T),
    /// The receiver has been dropped. Contains the value that couldn't be sent.
    Disconnected(T),
}

impl<T> TrySendError<T> {
    /// Returns the value that couldn't be sent.
    pub fn into_inner(self) -> T {
        match self {
            Self::Full(val) | Self::Disconnected(val) => val,
        }
    }

    /// Returns `true` if this error is the `Full` variant.
    pub fn is_full(&self) -> bool {
        matches!(self, Self::Full(_))
    }

    /// Returns `true` if this error is the `Disconnected` variant.
    pub fn is_disconnected(&self) -> bool {
        matches!(self, Self::Disconnected(_))
    }
}

impl<T> fmt::Display for TrySendError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Full(_) => write!(f, "queue is full"),
            Self::Disconnected(_) => write!(f, "receiver disconnected"),
        }
    }
}

impl<T> fmt::Debug for TrySendError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self, f)
    }
}

impl<T> std::error::Error for TrySendError<T> {}

/// Error returned by [`Receiver::try_recv`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TryRecvError {
    /// The queue is empty.
    Empty,
    /// The sender has been dropped and the queue is empty.
    Disconnected,
}

impl TryRecvError {
    /// Returns `true` if this error is the `Empty` variant.
    pub fn is_empty(&self) -> bool {
        matches!(self, Self::Empty)
    }

    /// Returns `true` if this error is the `Disconnected` variant.
    pub fn is_disconnected(&self) -> bool {
        matches!(self, Self::Disconnected)
    }
}

impl fmt::Display for TryRecvError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Empty => write!(f, "queue is empty"),
            Self::Disconnected => write!(f, "sender disconnected"),
        }
    }
}

impl std::error::Error for TryRecvError {}

#[cfg(test)]
mod tests {
    // ============================================================================
    // Basic Operations
    // ============================================================================

    use crate::spsc::bounded::{TryRecvError, TrySendError, channel};

    #[test]
    fn send_recv_interleaved() {
        let (tx, rx) = channel::<u64>(8);

        for i in 0..100 {
            tx.try_send(i).unwrap();
            assert_eq!(rx.try_recv().unwrap(), i);
        }
    }

    #[test]
    fn fill_then_drain() {
        let (tx, rx) = channel::<u64>(8);

        for i in 0..8 {
            tx.try_send(i).unwrap();
        }

        for i in 0..8 {
            assert_eq!(rx.try_recv().unwrap(), i);
        }

        assert!(matches!(rx.try_recv(), Err(TryRecvError::Empty)));
    }

    #[test]
    fn recv_when_empty_returns_error() {
        let (tx, rx) = channel::<u64>(8);

        assert!(matches!(rx.try_recv(), Err(TryRecvError::Empty)));

        tx.try_send(1).unwrap();
        let _ = rx.try_recv();

        assert!(matches!(rx.try_recv(), Err(TryRecvError::Empty)));
    }

    #[test]
    fn receiver_disconnect() {
        let (tx, rx) = channel::<u64>(4);

        // Fill the queue
        tx.try_send(1).unwrap();
        tx.try_send(2).unwrap();
        tx.try_send(3).unwrap();
        tx.try_send(4).unwrap();

        drop(rx);

        // Now sender discovers receiver is gone when it can't make progress
        assert!(matches!(tx.try_send(5), Err(TrySendError::Disconnected(5))));
    }

    // ============================================================================
    // Disconnection
    // ============================================================================

    #[test]
    fn sender_disconnect_empty_queue() {
        let (tx, rx) = channel::<u64>(8);

        drop(tx);

        assert!(matches!(rx.try_recv(), Err(TryRecvError::Disconnected)));
    }

    #[test]
    fn drop_receiver_drops_remaining_items() {
        use std::sync::Arc;
        use std::sync::atomic::{AtomicUsize, Ordering};

        let drop_count = Arc::new(AtomicUsize::new(0));

        struct DropCounter(Arc<AtomicUsize>);
        impl Drop for DropCounter {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }

        let (tx, rx) = channel::<DropCounter>(8);

        tx.try_send(DropCounter(Arc::clone(&drop_count))).unwrap();
        tx.try_send(DropCounter(Arc::clone(&drop_count))).unwrap();

        assert_eq!(drop_count.load(Ordering::SeqCst), 0);

        drop(tx);
        drop(rx);

        assert_eq!(drop_count.load(Ordering::SeqCst), 2);
    }

    // ============================================================================
    // Index Wrapping
    // ============================================================================

    #[test]
    fn multiple_wraparounds() {
        let (tx, rx) = channel::<u64>(4);

        for lap in 0..100 {
            for i in 0..4 {
                tx.try_send(lap * 4 + i).unwrap();
            }
            for i in 0..4 {
                assert_eq!(rx.try_recv().unwrap(), lap * 4 + i);
            }
        }
    }

    #[test]
    fn partial_fill_drain_wraparound() {
        let (tx, rx) = channel::<u64>(8);

        for _ in 0..50 {
            tx.try_send(1).unwrap();
            tx.try_send(2).unwrap();
            tx.try_send(3).unwrap();

            assert_eq!(rx.try_recv().unwrap(), 1);
            assert_eq!(rx.try_recv().unwrap(), 2);

            tx.try_send(4).unwrap();
            tx.try_send(5).unwrap();

            assert_eq!(rx.try_recv().unwrap(), 3);
            assert_eq!(rx.try_recv().unwrap(), 4);
            assert_eq!(rx.try_recv().unwrap(), 5);
        }
    }

    // ============================================================================
    // Cross-Thread
    // ============================================================================

    #[test]
    fn cross_thread_basic() {
        use std::thread;

        let (tx, rx) = channel::<u64>(64);

        let producer = thread::spawn(move || {
            for i in 0..100 {
                while tx.try_send(i).is_err() {
                    thread::yield_now();
                }
            }
        });

        let consumer = thread::spawn(move || {
            for i in 0..100 {
                loop {
                    match rx.try_recv() {
                        Ok(v) => {
                            assert_eq!(v, i);
                            break;
                        }
                        Err(TryRecvError::Empty) => thread::yield_now(),
                        Err(TryRecvError::Disconnected) => panic!("unexpected disconnect"),
                    }
                }
            }
        });

        producer.join().unwrap();
        consumer.join().unwrap();
    }

    #[test]
    fn cross_thread_throughput() {
        use std::thread;

        const COUNT: u64 = 100_000;

        let (tx, rx) = channel::<u64>(1024);

        let producer = thread::spawn(move || {
            for i in 0..COUNT {
                while tx.try_send(i).is_err() {
                    std::hint::spin_loop();
                }
            }
        });

        let consumer = thread::spawn(move || {
            let mut received = 0;
            let mut expected = 0;
            while received < COUNT {
                match rx.try_recv() {
                    Ok(v) => {
                        assert_eq!(v, expected);
                        expected += 1;
                        received += 1;
                    }
                    Err(TryRecvError::Empty) => std::hint::spin_loop(),
                    Err(TryRecvError::Disconnected) => break,
                }
            }
            received
        });

        producer.join().unwrap();
        let received = consumer.join().unwrap();
        assert_eq!(received, COUNT);
    }

    #[test]
    fn cross_thread_producer_faster() {
        use std::thread;
        use std::time::Duration;

        let (tx, rx) = channel::<u64>(16);

        let producer = thread::spawn(move || {
            for i in 0..1000 {
                while tx.try_send(i).is_err() {
                    std::hint::spin_loop();
                }
            }
        });

        let consumer = thread::spawn(move || {
            let mut count = 0;
            loop {
                match rx.try_recv() {
                    Ok(_) => count += 1,
                    Err(TryRecvError::Empty) => {
                        thread::sleep(Duration::from_micros(10));
                    }
                    Err(TryRecvError::Disconnected) => break,
                }
            }
            count
        });

        producer.join().unwrap();
        let count = consumer.join().unwrap();
        assert_eq!(count, 1000);
    }

    #[test]
    fn cross_thread_consumer_faster() {
        use std::thread;
        use std::time::Duration;

        let (tx, rx) = channel::<u64>(16);

        let producer = thread::spawn(move || {
            for i in 0..100 {
                thread::sleep(Duration::from_micros(10));
                while tx.try_send(i).is_err() {
                    std::hint::spin_loop();
                }
            }
        });

        let consumer = thread::spawn(move || {
            let mut count = 0;
            loop {
                match rx.try_recv() {
                    Ok(_) => count += 1,
                    Err(TryRecvError::Empty) => std::hint::spin_loop(),
                    Err(TryRecvError::Disconnected) => break,
                }
            }
            count
        });

        producer.join().unwrap();
        let count = consumer.join().unwrap();
        assert_eq!(count, 100);
    }

    // ============================================================================
    // Special Types
    // ============================================================================

    #[test]
    fn zero_sized_type() {
        let (tx, rx) = channel::<()>(8);

        tx.try_send(()).unwrap();
        tx.try_send(()).unwrap();
        tx.try_send(()).unwrap();

        assert_eq!(rx.try_recv().unwrap(), ());
        assert_eq!(rx.try_recv().unwrap(), ());
        assert_eq!(rx.try_recv().unwrap(), ());
        assert!(matches!(rx.try_recv(), Err(TryRecvError::Empty)));
    }

    #[test]
    fn large_message_4kb() {
        #[derive(Clone, PartialEq, Debug)]
        struct LargeMessage {
            data: [u8; 4096],
            id: u64,
        }

        let (tx, rx) = channel::<LargeMessage>(4);

        let msg = LargeMessage {
            data: [0xAB; 4096],
            id: 12345,
        };

        tx.try_send(msg.clone()).unwrap();
        let received = rx.try_recv().unwrap();

        assert_eq!(received.id, 12345);
        assert_eq!(received.data[0], 0xAB);
        assert_eq!(received.data[4095], 0xAB);
    }

    #[test]
    fn string_messages() {
        let (tx, rx) = channel::<String>(8);

        tx.try_send("hello".to_string()).unwrap();
        tx.try_send("world".to_string()).unwrap();

        assert_eq!(rx.try_recv().unwrap(), "hello");
        assert_eq!(rx.try_recv().unwrap(), "world");
    }

    #[test]
    fn vec_messages() {
        let (tx, rx) = channel::<Vec<u8>>(8);

        tx.try_send(vec![1, 2, 3]).unwrap();
        tx.try_send(vec![4, 5, 6, 7, 8]).unwrap();

        assert_eq!(rx.try_recv().unwrap(), vec![1, 2, 3]);
        assert_eq!(rx.try_recv().unwrap(), vec![4, 5, 6, 7, 8]);
    }

    // ============================================================================
    // Edge Cases
    // ============================================================================

    #[test]
    fn single_capacity() {
        let (tx, rx) = channel::<u64>(1);
        // Rounds to 2

        tx.try_send(1).unwrap();
        tx.try_send(2).unwrap();
        assert!(matches!(tx.try_send(3), Err(TrySendError::Full(3))));

        assert_eq!(rx.try_recv().unwrap(), 1);
        tx.try_send(3).unwrap();
    }

    #[test]
    fn is_empty_check() {
        let (tx, rx) = channel::<u64>(4);

        assert!(rx.is_empty());

        tx.try_send(1).unwrap();
        assert!(!rx.is_empty());

        tx.try_send(2).unwrap();
        tx.try_send(3).unwrap();
        tx.try_send(4).unwrap();

        assert!(!rx.is_empty());

        for _ in 0..4 {
            let _ = rx.try_recv();
        }

        assert!(rx.is_empty());
    }

    #[test]
    fn disconnect_flags() {
        let (tx, rx) = channel::<u64>(8);

        assert!(!tx.is_disconnected());
        assert!(!rx.is_disconnected());

        drop(rx);
        assert!(tx.is_disconnected());
    }

    #[test]
    fn disconnect_flags_sender_first() {
        let (tx, rx) = channel::<u64>(8);

        drop(tx);
        assert!(rx.is_disconnected());
    }

    // ============================================================================
    // Stress Tests
    // ============================================================================

    #[test]
    fn stress_test_sequential() {
        let (tx, rx) = channel::<u64>(16);

        for i in 0..100_000 {
            tx.try_send(i).unwrap();
            assert_eq!(rx.try_recv().unwrap(), i);
        }
    }

    #[test]
    fn stress_test_cross_thread() {
        use std::thread;

        const ITERATIONS: u64 = 500_000;

        let (tx, rx) = channel::<u64>(256);

        let producer = thread::spawn(move || {
            for i in 0..ITERATIONS {
                while tx.try_send(i).is_err() {
                    std::hint::spin_loop();
                }
            }
        });

        let consumer = thread::spawn(move || {
            let mut expected = 0;
            while expected < ITERATIONS {
                match rx.try_recv() {
                    Ok(v) => {
                        assert_eq!(v, expected);
                        expected += 1;
                    }
                    Err(TryRecvError::Empty) => std::hint::spin_loop(),
                    Err(TryRecvError::Disconnected) => panic!("unexpected disconnect"),
                }
            }
        });

        producer.join().unwrap();
        consumer.join().unwrap();
    }
}
