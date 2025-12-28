//! Overwriting Single-Producer Single-Consumer (SPSC) queue.
//!
//! This variant never blocks or returns "full" - when the queue is full,
//! the oldest unread message is overwritten. The consumer can detect when
//! it has been lapped (messages were lost).
//!
//! # Use Cases
//!
//! - Real-time data feeds where latest data matters most
//! - Logging where dropping old entries is acceptable
//! - Sensor data streams where only recent values are relevant
//!
//! # Example
//!
//! ```
//! use nexus_queue::spsc::overwriting;
//!
//! let (mut tx, mut rx) = overwriting::channel::<u32>(4);
//!
//! // Fill the queue
//! tx.send(1);
//! tx.send(2);
//! tx.send(3);
//! tx.send(4);
//!
//! // This overwrites the oldest (1)
//! tx.send(5);
//!
//! // Consumer sees 2, 3, 4, 5 (1 was lost)
//! let result = rx.recv().unwrap();
//! assert!(result.lagged > 0); // We lost at least one message
//! ```

mod ring;

use std::ptr::NonNull;

use ring::RingBuffer;

/// Creates a new overwriting SPSC channel with the given capacity.
///
/// The capacity will be rounded up to the next power of 2.
///
/// # Panics
///
/// Panics if `capacity` is 0.
pub fn channel<T>(capacity: usize) -> (Sender<T>, Receiver<T>) {
    let ring = RingBuffer::allocate(capacity);

    let sender = Sender {
        inner: ring,
        local_head: 0,
    };

    let receiver = Receiver {
        inner: ring,
        local_tail: 0,
    };

    (sender, receiver)
}

/// Result of a successful receive operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecvResult<T> {
    /// The received value.
    pub value: T,
    /// Number of messages that were lost due to the producer lapping the consumer.
    ///
    /// If this is 0, no messages were lost. If this is > 0, the producer
    /// overwrote `lagged` messages before the consumer could read them.
    pub lagged: usize,
}

impl<T> RecvResult<T> {
    /// Returns the value, discarding lag information.
    #[inline]
    pub fn into_value(self) -> T {
        self.value
    }
}

/// Error returned when receiving fails.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TryRecvError {
    /// The queue is empty.
    Empty,
    /// The sender has been dropped and the queue is empty.
    Disconnected,
}

/// Error returned when sending fails.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SendError<T> {
    /// The receiver has been dropped.
    Disconnected(T),
}

/// The sending half of an overwriting SPSC channel.
///
/// Unlike the bounded sender, `send()` never fails due to a full queue -
/// it simply overwrites the oldest unread value and returns it.
pub struct Sender<T> {
    inner: NonNull<RingBuffer<T>>,
    /// Local copy of head position (only this sender modifies head).
    local_head: usize,
}

unsafe impl<T: Send> Send for Sender<T> {}

impl<T> Sender<T> {
    /// Sends a value, overwriting the oldest unread value if the queue is full.
    ///
    /// Returns `Ok(None)` if sent without overwriting, or `Ok(Some(old_value))`
    /// if an unread value was overwritten.
    ///
    /// # Errors
    ///
    /// Returns `Err(SendError::Disconnected(value))` if the receiver has been dropped.
    #[inline]
    pub fn send(&mut self, value: T) -> Result<Option<T>, SendError<T>> {
        let inner = unsafe { self.inner.as_ref() };

        // Check if receiver is still alive
        if inner.is_receiver_disconnected() {
            return Err(SendError::Disconnected(value));
        }

        let head = self.local_head;

        // Write and publish, getting back any overwritten value
        let old_value = unsafe { inner.write_and_publish(head, value) };

        // Advance head
        self.local_head = head.wrapping_add(1);
        inner.store_head(self.local_head);

        Ok(old_value)
    }

    /// Sends a value without checking if the receiver is disconnected.
    ///
    /// Returns `None` if sent without overwriting, or `Some(old_value)`
    /// if an unread value was overwritten.
    ///
    /// This is slightly faster than `send()` when you know the receiver is alive,
    /// or don't care about the disconnection.
    #[inline]
    pub fn send_unchecked(&mut self, value: T) -> Option<T> {
        let inner = unsafe { self.inner.as_ref() };

        let head = self.local_head;

        // Write and publish
        let old_value = unsafe { inner.write_and_publish(head, value) };

        // Advance head
        self.local_head = head.wrapping_add(1);
        inner.store_head(self.local_head);

        old_value
    }

    /// Returns `true` if the receiver has been dropped.
    #[inline]
    pub fn is_disconnected(&self) -> bool {
        unsafe { self.inner.as_ref().is_receiver_disconnected() }
    }

    /// Returns the capacity of the queue.
    #[inline]
    pub fn capacity(&self) -> usize {
        unsafe { self.inner.as_ref().capacity() }
    }
}

impl<T> Drop for Sender<T> {
    fn drop(&mut self) {
        let inner = unsafe { self.inner.as_ref() };
        inner.set_sender_disconnected();

        // If receiver is already gone, we need to clean up
        if inner.is_receiver_disconnected() {
            unsafe {
                let tail = inner.load_tail();
                inner.drop_remaining(tail, self.local_head);
                RingBuffer::deallocate(self.inner);
            }
        }
    }
}

/// The receiving half of an overwriting SPSC channel.
pub struct Receiver<T> {
    inner: NonNull<RingBuffer<T>>,
    /// Local tail position.
    local_tail: usize,
}

unsafe impl<T: Send> Send for Receiver<T> {}

impl<T> Receiver<T> {
    /// Attempts to receive a value from the queue.
    ///
    /// # Returns
    ///
    /// - `Ok(RecvResult { value, lagged })` - Successfully received. `lagged` indicates
    ///   how many messages were lost if the producer lapped the consumer.
    /// - `Err(TryRecvError::Empty)` - The queue is empty.
    /// - `Err(TryRecvError::Disconnected)` - The sender was dropped and queue is empty.
    #[inline]
    pub fn try_recv(&mut self) -> Result<RecvResult<T>, TryRecvError> {
        let inner = unsafe { self.inner.as_ref() };

        // Try to read from current position
        match unsafe { inner.try_read(self.local_tail) } {
            Some((value, lagged)) => {
                if lagged > 0 {
                    // We were lapped - need to catch up
                    self.local_tail = inner.catch_up_tail();
                }
                self.local_tail = self.local_tail.wrapping_add(1);
                Ok(RecvResult { value, lagged })
            }
            None => {
                // No data at current position - check if disconnected
                if inner.is_sender_disconnected() {
                    let head = inner.load_head();
                    if self.local_tail >= head {
                        // We've caught up to producer
                        Err(TryRecvError::Disconnected)
                    } else {
                        // Producer stopped but we haven't reached head yet.
                        // This can happen if:
                        // 1. We already consumed this slot (lap=0)
                        // 2. Producer stopped mid-lap (slot_lap < expected_lap)
                        //
                        // Advance local_tail to try next position.
                        // This ensures we don't get stuck on consumed slots
                        // after wrapping around the buffer.
                        self.local_tail = self.local_tail.wrapping_add(1);
                        Err(TryRecvError::Empty)
                    }
                } else {
                    Err(TryRecvError::Empty)
                }
            }
        }
    }

    /// Receives a value, blocking until one is available.
    ///
    /// # Returns
    ///
    /// - `Ok(RecvResult { value, lagged })` - Successfully received.
    /// - `Err(TryRecvError::Disconnected)` - The sender was dropped and queue is empty.
    #[inline]
    pub fn recv(&mut self) -> Result<RecvResult<T>, TryRecvError> {
        loop {
            match self.try_recv() {
                Ok(result) => return Ok(result),
                Err(TryRecvError::Empty) => {
                    std::hint::spin_loop();
                }
                Err(TryRecvError::Disconnected) => {
                    return Err(TryRecvError::Disconnected);
                }
            }
        }
    }

    /// Returns `true` if the sender has been dropped.
    #[inline]
    pub fn is_disconnected(&self) -> bool {
        unsafe { self.inner.as_ref().is_sender_disconnected() }
    }

    /// Returns `true` if the queue is empty.
    ///
    /// Note: This is a snapshot and may be immediately outdated.
    #[inline]
    pub fn is_empty(&self) -> bool {
        let inner = unsafe { self.inner.as_ref() };
        self.local_tail >= inner.load_head()
    }

    /// Returns the capacity of the queue.
    #[inline]
    pub fn capacity(&self) -> usize {
        unsafe { self.inner.as_ref().capacity() }
    }
}

impl<T> Drop for Receiver<T> {
    fn drop(&mut self) {
        let inner = unsafe { self.inner.as_ref() };

        // Sync our local tail before marking disconnected
        inner.store_tail(self.local_tail);
        inner.set_receiver_disconnected();

        // If sender is already gone, we need to clean up
        if inner.is_sender_disconnected() {
            unsafe {
                let head = inner.load_head();
                inner.drop_remaining(self.local_tail, head);
                RingBuffer::deallocate(self.inner);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_send_recv() {
        let (mut tx, mut rx) = channel::<u32>(4);

        tx.send(1).unwrap();
        tx.send(2).unwrap();

        let r1 = rx.try_recv().unwrap();
        assert_eq!(r1.value, 1);
        assert_eq!(r1.lagged, 0);

        let r2 = rx.try_recv().unwrap();
        assert_eq!(r2.value, 2);
        assert_eq!(r2.lagged, 0);

        assert!(matches!(rx.try_recv(), Err(TryRecvError::Empty)));
    }

    #[test]
    fn overwrite_when_full() {
        let (mut tx, mut rx) = channel::<u32>(4);

        // Fill the queue (capacity rounds to 4)
        assert_eq!(tx.send(1).unwrap(), None); // No overwrite
        assert_eq!(tx.send(2).unwrap(), None);
        assert_eq!(tx.send(3).unwrap(), None);
        assert_eq!(tx.send(4).unwrap(), None);

        // These should overwrite oldest values and return them
        assert_eq!(tx.send(5).unwrap(), Some(1)); // Overwrote 1
        assert_eq!(tx.send(6).unwrap(), Some(2)); // Overwrote 2

        // First recv should detect lapping
        let r1 = rx.try_recv().unwrap();
        // We should see one of the newer values, with lagged > 0
        assert!(r1.lagged > 0, "Expected lagged > 0, got {}", r1.lagged);
    }

    #[test]
    fn producer_laps_consumer_multiple_times() {
        let (mut tx, mut rx) = channel::<u32>(4);

        // Producer writes 12 values (3 full laps around a size-4 buffer)
        for i in 0..12 {
            tx.send(i).unwrap();
        }

        // Consumer should detect significant lag
        let r1 = rx.try_recv().unwrap();
        assert!(r1.lagged > 0, "Expected lag, got 0");
        // Should see one of the recent values (8, 9, 10, or 11)
        assert!(r1.value >= 8, "Expected recent value, got {}", r1.value);
    }

    #[test]
    fn disconnect_sender() {
        let (tx, mut rx) = channel::<u32>(4);

        drop(tx);

        assert!(rx.is_disconnected());
        assert!(matches!(rx.try_recv(), Err(TryRecvError::Disconnected)));
    }

    #[test]
    fn disconnect_receiver() {
        let (mut tx, rx) = channel::<u32>(4);

        drop(rx);

        assert!(tx.is_disconnected());
        assert!(matches!(tx.send(1), Err(SendError::Disconnected(1))));
    }

    #[test]
    fn recv_result_into_value() {
        let (mut tx, mut rx) = channel::<String>(4);

        tx.send("hello".to_string()).unwrap();

        let result = rx.try_recv().unwrap();
        let s: String = result.into_value();
        assert_eq!(s, "hello");
    }

    #[test]
    fn send_unchecked() {
        let (mut tx, mut rx) = channel::<u32>(4);

        tx.send_unchecked(42);
        tx.send_unchecked(43);

        assert_eq!(rx.try_recv().unwrap().value, 42);
        assert_eq!(rx.try_recv().unwrap().value, 43);
    }

    #[test]
    fn drops_on_overwrite() {
        use std::sync::Arc;
        use std::sync::atomic::{AtomicUsize, Ordering};

        #[derive(Debug)]
        struct DropCounter(Arc<AtomicUsize>);
        impl Drop for DropCounter {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }

        let drop_count = Arc::new(AtomicUsize::new(0));
        let (mut tx, rx) = channel::<DropCounter>(4);

        // Fill queue
        for _ in 0..4 {
            tx.send(DropCounter(drop_count.clone())).unwrap();
        }

        assert_eq!(drop_count.load(Ordering::SeqCst), 0, "Nothing dropped yet");

        // Overwrite - should drop the oldest
        tx.send(DropCounter(drop_count.clone())).unwrap();
        assert_eq!(
            drop_count.load(Ordering::SeqCst),
            1,
            "Should have dropped 1"
        );

        tx.send(DropCounter(drop_count.clone())).unwrap();
        assert_eq!(
            drop_count.load(Ordering::SeqCst),
            2,
            "Should have dropped 2"
        );

        // Drop channel - remaining 4 items should be dropped
        drop(rx);
        drop(tx);

        assert_eq!(
            drop_count.load(Ordering::SeqCst),
            6,
            "All 6 should be dropped"
        );
    }

    #[test]
    fn capacity_rounds_to_power_of_two() {
        let (tx, _rx) = channel::<u32>(5);
        assert_eq!(tx.capacity(), 8);

        let (tx, _rx) = channel::<u32>(7);
        assert_eq!(tx.capacity(), 8);

        let (tx, _rx) = channel::<u32>(8);
        assert_eq!(tx.capacity(), 8);
    }
}
