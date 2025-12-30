//! Multi-producer single-consumer (MPSC) bounded queue.
//!
//! Multiple producers can send concurrently, with a single consumer receiving.
//! Uses per-slot sequence numbers to handle out-of-order producer completion.
//!
//! # Example
//!
//! ```
//! use nexus_queue::mpsc;
//! use std::thread;
//!
//! let (tx, mut rx) = mpsc::bounded::channel::<u64>(1024);
//!
//! // Clone sender for multiple producers
//! let tx2 = tx.clone();
//!
//! let h1 = thread::spawn(move || {
//!     for i in 0..100 {
//!         while tx.try_send(i).is_err() {
//!             std::hint::spin_loop();
//!         }
//!     }
//! });
//!
//! let h2 = thread::spawn(move || {
//!     for i in 100..200 {
//!         while tx2.try_send(i).is_err() {
//!             std::hint::spin_loop();
//!         }
//!     }
//! });
//!
//! let mut received = Vec::new();
//! while received.len() < 200 {
//!     if let Ok(val) = rx.try_recv() {
//!         received.push(val);
//!     }
//! }
//!
//! h1.join().unwrap();
//! h2.join().unwrap();
//!
//! assert_eq!(received.len(), 200);
//! ```
//!
//! # Performance Notes
//!
//! Unlike SPSC, producers must use atomic compare-and-swap to claim slots.
//! However, out-of-order completion is supported — a fast producer won't
//! be blocked by a slow one.
//!
//! The consumer side is similar to SPSC: it checks per-slot sequences
//! to determine if data is ready.

mod ring;

use std::fmt;
use std::ptr::NonNull;
use std::sync::atomic::{AtomicUsize, Ordering};

use crossbeam_utils::Backoff;

use ring::{RingBuffer, Slot};

/// Creates a new MPSC channel with the given capacity.
///
/// The actual capacity will be rounded up to the next power of two
/// (minimum 2) for efficient index masking.
///
/// # Example
///
/// ```
/// use nexus_queue::mpsc;
///
/// let (tx, rx) = mpsc::bounded::channel::<String>(100);
/// // Actual capacity will be 128 (next power of two)
/// assert_eq!(tx.capacity(), 128);
/// ```
pub fn channel<T>(capacity: usize) -> (Sender<T>, Receiver<T>) {
    let inner = RingBuffer::<T>::allocate(capacity);

    let inner_ref = unsafe { inner.as_ref() };

    (
        Sender {
            inner,
            // Cache hot fields to avoid indirection on every send
            buffer: inner_ref.buffer_ptr(),
            mask: inner_ref.mask(),
            tail: inner_ref.tail_ptr(),
        },
        Receiver {
            inner,
            local_head: 0,
        },
    )
}

/// The sending half of an MPSC channel.
///
/// This struct can be cloned to create multiple producers.
/// All clones share the same underlying queue.
pub struct Sender<T> {
    inner: NonNull<RingBuffer<T>>,

    // Cached hot fields - avoid indirection on hot path
    buffer: *mut Slot<T>,
    mask: usize,
    tail: *const AtomicUsize,
}

// Safety: Sender can be sent to another thread. The ring buffer uses
// proper atomic synchronization for multi-producer access.
unsafe impl<T: Send> Send for Sender<T> {}

// Safety: Sender can be shared across threads (for cloning).
unsafe impl<T: Send> Sync for Sender<T> {}

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
    /// use nexus_queue::mpsc::{self, bounded::TrySendError};
    ///
    /// let (tx, rx) = mpsc::bounded::channel::<u32>(2);
    ///
    /// assert!(tx.try_send(1).is_ok());
    /// assert!(tx.try_send(2).is_ok());
    ///
    /// // Queue is now full
    /// assert!(matches!(tx.try_send(3), Err(TrySendError::Full(3))));
    /// ```
    #[inline]
    pub fn try_send(&self, value: T) -> Result<(), TrySendError<T>> {
        let backoff = Backoff::new();
        let tail_atomic = unsafe { &*self.tail };
        let mut tail = tail_atomic.load(Ordering::Relaxed);

        loop {
            let slot = unsafe { self.buffer.add(tail & self.mask) };
            let seq = unsafe { (*slot).sequence.load(Ordering::Acquire) };
            let diff = seq as isize - tail as isize;

            if diff == 0 {
                match tail_atomic.compare_exchange_weak(
                    tail,
                    tail.wrapping_add(1),
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => {
                        unsafe {
                            (*slot).data.get().cast::<T>().write(value);
                            (*slot)
                                .sequence
                                .store(tail.wrapping_add(1), Ordering::Release);
                        }
                        return Ok(());
                    }
                    Err(t) => {
                        tail = t;
                        backoff.spin();
                    }
                }
            } else if diff < 0 {
                return self.try_send_slow(value);
            } else {
                tail = tail_atomic.load(Ordering::Relaxed);
                backoff.spin();
            }
        }
    }

    #[cold]
    fn try_send_slow(&self, value: T) -> Result<(), TrySendError<T>> {
        let inner = unsafe { self.inner.as_ref() };
        if inner.is_receiver_disconnected() {
            Err(TrySendError::Disconnected(value))
        } else {
            Err(TrySendError::Full(value))
        }
    }

    /// Returns the capacity of the queue.
    #[inline]
    pub fn capacity(&self) -> usize {
        unsafe { self.inner.as_ref().capacity() }
    }

    /// Returns `true` if the receiver has been dropped.
    #[inline]
    pub fn is_disconnected(&self) -> bool {
        unsafe { self.inner.as_ref().is_receiver_disconnected() }
    }
}

impl<T> Clone for Sender<T> {
    fn clone(&self) -> Self {
        let inner = unsafe { self.inner.as_ref() };
        inner.add_sender();
        RingBuffer::acquire(self.inner);

        Self {
            inner: self.inner,
            buffer: self.buffer,
            mask: self.mask,
            tail: self.tail,
        }
    }
}

impl<T> Drop for Sender<T> {
    fn drop(&mut self) {
        unsafe {
            // Decrement sender count
            self.inner.as_ref().remove_sender();
            // Decrement ref count (may deallocate)
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

/// The receiving half of an MPSC channel.
///
/// This struct cannot be cloned — there is only one consumer.
pub struct Receiver<T> {
    inner: NonNull<RingBuffer<T>>,

    /// Our read position. We're the only reader, so no atomic needed.
    local_head: usize,
}

// Safety: Receiver can be sent to another thread, but not shared (not Sync).
unsafe impl<T: Send> Send for Receiver<T> {}

impl<T> Receiver<T> {
    /// Attempts to receive a value from the queue.
    ///
    /// # Errors
    ///
    /// Returns `Err(TryRecvError::Empty)` if no message is currently available.
    /// This includes both the case where the queue is empty and where a producer
    /// has claimed a slot but hasn't finished publishing yet.
    ///
    /// Returns `Err(TryRecvError::Disconnected)` if all senders have been dropped
    /// AND the queue is completely empty (no in-flight messages).
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_queue::mpsc::{self, bounded::TryRecvError};
    ///
    /// let (tx, mut rx) = mpsc::bounded::channel::<u32>(8);
    ///
    /// // Queue is empty
    /// assert!(matches!(rx.try_recv(), Err(TryRecvError::Empty)));
    ///
    /// tx.try_send(42).unwrap();
    /// assert_eq!(rx.try_recv().unwrap(), 42);
    /// ```
    #[inline]
    pub fn try_recv(&mut self) -> Result<T, TryRecvError> {
        let inner = unsafe { self.inner.as_ref() };

        // Try to read from current position
        // Safety: We're the only consumer
        match unsafe { inner.try_read(self.local_head) } {
            Some(value) => {
                self.local_head = self.local_head.wrapping_add(1);
                Ok(value)
            }
            None => self.try_recv_slow(inner),
        }
    }

    #[cold]
    fn try_recv_slow(&self, inner: &RingBuffer<T>) -> Result<T, TryRecvError> {
        // Slot not ready - either empty or producer still publishing
        if inner.sender_count() == 0 {
            // All senders gone, but check if there are in-flight messages
            // by comparing head to tail. If head < tail, a producer claimed
            // a slot but we haven't seen the publish yet.
            if self.local_head == inner.load_tail() {
                // Truly empty
                Err(TryRecvError::Disconnected)
            } else {
                // In-flight message, spin
                Err(TryRecvError::Empty)
            }
        } else {
            Err(TryRecvError::Empty)
        }
    }

    /// Returns the capacity of the queue.
    #[inline]
    pub fn capacity(&self) -> usize {
        unsafe { self.inner.as_ref().capacity() }
    }

    /// Returns `true` if all senders have been dropped.
    #[inline]
    pub fn is_disconnected(&self) -> bool {
        unsafe { self.inner.as_ref().sender_count() == 0 }
    }
}

impl<T> Drop for Receiver<T> {
    fn drop(&mut self) {
        unsafe {
            let inner = self.inner.as_ref();
            // Sync our local head position for drop_remaining_elements
            inner.store_head(self.local_head);
            inner.set_receiver_disconnected();
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
    /// All senders have been dropped and the queue is empty.
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
            Self::Disconnected => write!(f, "all senders disconnected"),
        }
    }
}

impl std::error::Error for TryRecvError {}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use std::thread;

    #[test]
    fn basic_send_recv() {
        let (tx, mut rx) = channel::<u64>(8);

        tx.try_send(1).unwrap();
        tx.try_send(2).unwrap();
        tx.try_send(3).unwrap();

        assert_eq!(rx.try_recv().unwrap(), 1);
        assert_eq!(rx.try_recv().unwrap(), 2);
        assert_eq!(rx.try_recv().unwrap(), 3);
        assert!(matches!(rx.try_recv(), Err(TryRecvError::Empty)));
    }

    #[test]
    fn capacity_rounds_to_power_of_two() {
        let (tx, _rx) = channel::<u64>(100);
        assert_eq!(tx.capacity(), 128);

        let (tx, _rx) = channel::<u64>(1);
        assert_eq!(tx.capacity(), 2);

        let (tx, _rx) = channel::<u64>(1024);
        assert_eq!(tx.capacity(), 1024);
    }

    #[test]
    fn queue_full() {
        let (tx, mut rx) = channel::<u64>(4);

        tx.try_send(1).unwrap();
        tx.try_send(2).unwrap();
        tx.try_send(3).unwrap();
        tx.try_send(4).unwrap();

        assert!(matches!(tx.try_send(5), Err(TrySendError::Full(5))));

        assert_eq!(rx.try_recv().unwrap(), 1);

        tx.try_send(5).unwrap();
    }

    #[test]
    fn sender_disconnect() {
        let (tx, mut rx) = channel::<u64>(8);

        tx.try_send(1).unwrap();
        tx.try_send(2).unwrap();

        drop(tx);

        assert_eq!(rx.try_recv().unwrap(), 1);
        assert_eq!(rx.try_recv().unwrap(), 2);
        assert!(matches!(rx.try_recv(), Err(TryRecvError::Disconnected)));
    }

    #[test]
    fn receiver_disconnect() {
        let (tx, rx) = channel::<u64>(4);

        drop(rx);

        // Disconnect is only detected when queue is full (slow path optimization)
        // Fill the queue first
        tx.try_send(1).unwrap();
        tx.try_send(2).unwrap();
        tx.try_send(3).unwrap();
        tx.try_send(4).unwrap();

        // Now we should get Disconnected
        assert!(matches!(tx.try_send(5), Err(TrySendError::Disconnected(5))));
    }

    #[test]
    fn clone_sender() {
        let (tx1, mut rx) = channel::<u64>(8);
        let tx2 = tx1.clone();

        tx1.try_send(1).unwrap();
        tx2.try_send(2).unwrap();

        assert_eq!(rx.try_recv().unwrap(), 1);
        assert_eq!(rx.try_recv().unwrap(), 2);
    }

    #[test]
    fn all_senders_drop() {
        let (tx1, mut rx) = channel::<u64>(8);
        let tx2 = tx1.clone();

        tx1.try_send(1).unwrap();

        drop(tx1);
        // Still one sender alive
        assert!(!rx.is_disconnected());

        drop(tx2);
        // Now all senders dropped
        assert_eq!(rx.try_recv().unwrap(), 1);
        assert!(matches!(rx.try_recv(), Err(TryRecvError::Disconnected)));
    }

    #[test]
    fn multi_producer() {
        let (tx, mut rx) = channel::<u64>(1024);

        let handles: Vec<_> = (0..4)
            .map(|producer_id| {
                let tx = tx.clone();
                thread::spawn(move || {
                    for i in 0..100 {
                        let val = producer_id * 1000 + i;
                        while tx.try_send(val).is_err() {
                            std::hint::spin_loop();
                        }
                    }
                })
            })
            .collect();

        drop(tx); // Drop original sender

        let mut received = Vec::new();
        loop {
            match rx.try_recv() {
                Ok(val) => received.push(val),
                Err(TryRecvError::Empty) => std::hint::spin_loop(),
                Err(TryRecvError::Disconnected) => break,
            }
        }

        for handle in handles {
            handle.join().unwrap();
        }

        assert_eq!(received.len(), 400);
    }

    #[test]
    fn with_drop_type() {
        use std::sync::atomic::{AtomicUsize, Ordering};

        let drop_count = Arc::new(AtomicUsize::new(0));

        struct DropCounter(Arc<AtomicUsize>);
        impl Drop for DropCounter {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }

        let (tx, mut rx) = channel::<DropCounter>(8);

        tx.try_send(DropCounter(Arc::clone(&drop_count))).unwrap();
        tx.try_send(DropCounter(Arc::clone(&drop_count))).unwrap();
        tx.try_send(DropCounter(Arc::clone(&drop_count))).unwrap();

        assert_eq!(drop_count.load(Ordering::SeqCst), 0);

        let _ = rx.try_recv().unwrap();
        assert_eq!(drop_count.load(Ordering::SeqCst), 1);

        drop(rx);
        drop(tx);

        assert_eq!(drop_count.load(Ordering::SeqCst), 3);
    }

    #[test]
    fn no_message_loss_on_disconnect() {
        // Regression test: ensure messages aren't lost when senders
        // disconnect while messages are in-flight
        for _ in 0..100 {
            let (tx, mut rx) = channel::<u64>(64);
            const N: usize = 1000;
            const PRODUCERS: usize = 4;

            let handles: Vec<_> = (0..PRODUCERS)
                .map(|_| {
                    let tx = tx.clone();
                    thread::spawn(move || {
                        for i in 0..N {
                            while tx.try_send(i as u64).is_err() {
                                std::hint::spin_loop();
                            }
                        }
                    })
                })
                .collect();

            drop(tx);

            let mut count = 0;
            loop {
                match rx.try_recv() {
                    Ok(_) => count += 1,
                    Err(TryRecvError::Empty) => std::hint::spin_loop(),
                    Err(TryRecvError::Disconnected) => break,
                }
            }

            for h in handles {
                h.join().unwrap();
            }

            assert_eq!(count, N * PRODUCERS, "lost messages!");
        }
    }
}
