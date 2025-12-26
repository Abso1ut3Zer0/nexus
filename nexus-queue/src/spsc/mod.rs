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
//! let (tx, rx) = spsc::channel::<u64>(1024);
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
/// let (tx, rx) = spsc::channel::<String>(100);
/// // Actual capacity will be 128 (next power of two)
/// assert_eq!(tx.capacity(), 128);
/// ```
pub fn channel<T>(capacity: usize) -> (Sender<T>, Receiver<T>) {
    let inner = RingBuffer::<T>::allocate(capacity);

    (
        Sender {
            inner,
            local_head: Cell::new(0),
            cached_tail: Cell::new(0),
        },
        Receiver {
            inner,
            local_tail: Cell::new(0),
            cached_head: Cell::new(0),
        },
    )
}

/// The sending half of an SPSC channel.
///
/// This struct can only be owned by a single thread at a time (implements `Send` but not `Sync`).
pub struct Sender<T> {
    inner: NonNull<RingBuffer<T>>,

    /// Our write position (authoritative, only we update this)
    local_head: Cell<usize>,

    /// Cached snapshot of consumer's tail position
    /// Only refreshed when queue appears full
    cached_tail: Cell<usize>,
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
    /// use nexus_queue::spsc::{self, TrySendError};
    ///
    /// let (tx, rx) = spsc::channel::<u32>(2);
    ///
    /// assert!(tx.try_send(1).is_ok());
    /// assert!(tx.try_send(2).is_ok());
    ///
    /// // Queue is now full
    /// assert!(matches!(tx.try_send(3), Err(TrySendError::Full(3))));
    /// ```
    #[inline]
    pub fn try_send(&self, value: T) -> Result<(), TrySendError<T>> {
        // Safety: We have a valid pointer from construction, and we're the only producer
        let inner = unsafe { self.inner.as_ref() };

        // Check for receiver disconnect first (Relaxed is fine - just a hint)
        if inner.is_receiver_disconnected() {
            return Err(TrySendError::Disconnected(value));
        }

        let head = self.local_head.get();

        // Fast path: check cached tail (no atomic load!)
        if head.wrapping_sub(self.cached_tail.get()) < inner.capacity() {
            // Safety: We have exclusive write access to this slot
            unsafe {
                inner.write_slot(head, value);
            }
            inner.publish_head(head.wrapping_add(1));
            self.local_head.set(head.wrapping_add(1));
            return Ok(());
        }

        // Slow path: refresh cached tail
        self.try_send_slow(inner, head, value)
    }

    #[cold]
    fn try_send_slow(
        &self,
        inner: &RingBuffer<T>,
        head: usize,
        value: T,
    ) -> Result<(), TrySendError<T>> {
        let tail = inner.load_tail();
        self.cached_tail.set(tail);

        if head.wrapping_sub(tail) < inner.capacity() {
            // Safety: We have exclusive write access to this slot
            unsafe {
                inner.write_slot(head, value);
            }
            inner.publish_head(head.wrapping_add(1));
            self.local_head.set(head.wrapping_add(1));
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
        // Safety: Valid pointer from construction
        unsafe { self.inner.as_ref().capacity() }
    }

    /// Returns `true` if the receiver has been dropped.
    ///
    /// Note: This may return a stale value; the receiver could be dropped
    /// immediately after this returns `false`.
    #[inline]
    pub fn is_disconnected(&self) -> bool {
        // Safety: Valid pointer from construction
        unsafe { self.inner.as_ref().is_receiver_disconnected() }
    }

    /// Returns the number of elements currently in the queue.
    ///
    /// Note: This is a snapshot and may be immediately stale in concurrent contexts.
    #[inline]
    pub fn len(&self) -> usize {
        // Safety: Valid pointer from construction
        let inner = unsafe { self.inner.as_ref() };
        let head = inner.load_head();
        let tail = inner.load_tail();
        head.wrapping_sub(tail)
    }

    /// Returns `true` if the queue is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<T> Drop for Sender<T> {
    fn drop(&mut self) {
        // Safety: Valid pointer, we're being dropped so no more access after this
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

    /// Our read position (authoritative, only we update this)
    local_tail: Cell<usize>,

    /// Cached snapshot of producer's head position
    /// Only refreshed when queue appears empty
    cached_head: Cell<usize>,
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
    /// use nexus_queue::spsc::{self, TryRecvError};
    ///
    /// let (tx, rx) = spsc::channel::<u32>(8);
    ///
    /// // Queue is empty
    /// assert!(matches!(rx.try_recv(), Err(TryRecvError::Empty)));
    ///
    /// tx.try_send(42).unwrap();
    /// assert_eq!(rx.try_recv().unwrap(), 42);
    /// ```
    #[inline]
    pub fn try_recv(&self) -> Result<T, TryRecvError> {
        // Safety: We have a valid pointer from construction, and we're the only consumer
        let inner = unsafe { self.inner.as_ref() };
        let tail = self.local_tail.get();

        // Fast path: check cached head (no atomic load!)
        if tail != self.cached_head.get() {
            // Safety: We have exclusive read access to this slot
            let value = unsafe { inner.read_slot(tail) };
            inner.publish_tail(tail.wrapping_add(1));
            self.local_tail.set(tail.wrapping_add(1));
            return Ok(value);
        }

        // Slow path: refresh cached head
        self.try_recv_slow(inner, tail)
    }

    #[cold]
    fn try_recv_slow(&self, inner: &RingBuffer<T>, tail: usize) -> Result<T, TryRecvError> {
        let head = inner.load_head();
        self.cached_head.set(head);

        if tail != head {
            // Safety: We have exclusive read access to this slot
            let value = unsafe { inner.read_slot(tail) };
            inner.publish_tail(tail.wrapping_add(1));
            self.local_tail.set(tail.wrapping_add(1));
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
        // Safety: Valid pointer from construction
        unsafe { self.inner.as_ref().capacity() }
    }

    /// Returns `true` if the sender has been dropped.
    ///
    /// Note: This may return a stale value; the sender could be dropped
    /// immediately after this returns `false`.
    #[inline]
    pub fn is_disconnected(&self) -> bool {
        // Safety: Valid pointer from construction
        unsafe { self.inner.as_ref().is_sender_disconnected() }
    }

    /// Returns the number of elements currently in the queue.
    ///
    /// Note: This is a snapshot and may be immediately stale in concurrent contexts.
    #[inline]
    pub fn len(&self) -> usize {
        // Safety: Valid pointer from construction
        let inner = unsafe { self.inner.as_ref() };
        let head = inner.load_head();
        let tail = inner.load_tail();
        head.wrapping_sub(tail)
    }

    /// Returns `true` if the queue is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<T> Drop for Receiver<T> {
    fn drop(&mut self) {
        // Safety: Valid pointer, we're being dropped so no more access after this
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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

impl<T: fmt::Debug> fmt::Display for TrySendError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Full(_) => write!(f, "queue is full"),
            Self::Disconnected(_) => write!(f, "receiver disconnected"),
        }
    }
}

impl<T: fmt::Debug> std::error::Error for TrySendError<T> {}

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
    use super::*;

    #[test]
    fn basic_send_recv() {
        let (tx, rx) = channel::<u64>(8);

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
        assert_eq!(tx.capacity(), 2); // Minimum is 2

        let (tx, _rx) = channel::<u64>(1024);
        assert_eq!(tx.capacity(), 1024);
    }

    #[test]
    fn queue_full() {
        let (tx, rx) = channel::<u64>(4);

        // Fill the queue
        tx.try_send(1).unwrap();
        tx.try_send(2).unwrap();
        tx.try_send(3).unwrap();
        tx.try_send(4).unwrap();

        // Should be full now
        assert!(matches!(tx.try_send(5), Err(TrySendError::Full(5))));

        // Drain one
        assert_eq!(rx.try_recv().unwrap(), 1);

        // Should have space again
        tx.try_send(5).unwrap();
    }

    #[test]
    fn sender_disconnect() {
        let (tx, rx) = channel::<u64>(8);

        tx.try_send(1).unwrap();
        tx.try_send(2).unwrap();

        drop(tx);

        // Should still be able to drain
        assert_eq!(rx.try_recv().unwrap(), 1);
        assert_eq!(rx.try_recv().unwrap(), 2);

        // Now should get disconnected
        assert!(matches!(rx.try_recv(), Err(TryRecvError::Disconnected)));
    }

    #[test]
    fn receiver_disconnect() {
        let (tx, rx) = channel::<u64>(8);

        drop(rx);

        assert!(matches!(
            tx.try_send(1),
            Err(TrySendError::Disconnected(1))
        ));
    }

    #[test]
    fn wrapping_indices() {
        let (tx, rx) = channel::<u64>(4);

        // Send and receive many more messages than capacity
        for i in 0..1000 {
            tx.try_send(i).unwrap();
            assert_eq!(rx.try_recv().unwrap(), i);
        }
    }

    #[test]
    fn with_drop_type() {
        use std::sync::atomic::{AtomicUsize, Ordering};
        use std::sync::Arc;

        let drop_count = Arc::new(AtomicUsize::new(0));

        #[derive(Debug)]
        struct DropCounter(Arc<AtomicUsize>);
        impl Drop for DropCounter {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }

        let (tx, rx) = channel::<DropCounter>(8);

        tx.try_send(DropCounter(Arc::clone(&drop_count))).unwrap();
        tx.try_send(DropCounter(Arc::clone(&drop_count))).unwrap();
        tx.try_send(DropCounter(Arc::clone(&drop_count))).unwrap();

        assert_eq!(drop_count.load(Ordering::SeqCst), 0);

        let _ = rx.try_recv().unwrap();
        assert_eq!(drop_count.load(Ordering::SeqCst), 1);

        // Drop remaining items via channel drop
        drop(rx);
        drop(tx);

        assert_eq!(drop_count.load(Ordering::SeqCst), 3);
    }

    #[test]
    fn large_struct() {
        #[derive(Debug, PartialEq)]
        struct LargeMessage {
            data: [u8; 256],
            id: u64,
        }

        let (tx, rx) = channel::<LargeMessage>(8);

        let msg = LargeMessage {
            data: [42; 256],
            id: 123,
        };

        tx.try_send(LargeMessage {
            data: [42; 256],
            id: 123,
        })
        .unwrap();

        assert_eq!(rx.try_recv().unwrap(), msg);
    }
}
