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

use core::fmt;
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
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum SendError<T> {
    /// The receiver has been dropped.
    Disconnected(T),
}

impl<T> fmt::Display for SendError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "receiver disconnected")
    }
}

impl<T> fmt::Debug for SendError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self, f)
    }
}

impl<T> std::error::Error for SendError<T> {}

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
                } else {
                    self.local_tail = self.local_tail.wrapping_add(1);
                }
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
    // ============================================================================
    // Basic Operations
    // ============================================================================

    use crate::spsc::overwriting::{SendError, TryRecvError, channel};

    #[test]
    fn send_returns_none_when_not_overwriting() {
        let (mut tx, mut rx) = channel::<u64>(8);

        assert_eq!(tx.send(1).unwrap(), None);
        assert_eq!(tx.send(2).unwrap(), None);
        assert_eq!(tx.send(3).unwrap(), None);

        assert_eq!(rx.try_recv().unwrap().value, 1);
        assert_eq!(rx.try_recv().unwrap().value, 2);
        assert_eq!(rx.try_recv().unwrap().value, 3);
    }

    #[test]
    fn send_returns_old_value_when_overwriting() {
        let (mut tx, _rx) = channel::<u64>(4);

        assert_eq!(tx.send(1).unwrap(), None);
        assert_eq!(tx.send(2).unwrap(), None);
        assert_eq!(tx.send(3).unwrap(), None);
        assert_eq!(tx.send(4).unwrap(), None);

        assert_eq!(tx.send(5).unwrap(), Some(1));
        assert_eq!(tx.send(6).unwrap(), Some(2));
        assert_eq!(tx.send(7).unwrap(), Some(3));
        assert_eq!(tx.send(8).unwrap(), Some(4));
    }

    #[test]
    fn recv_returns_lagged_zero_normal() {
        let (mut tx, mut rx) = channel::<u64>(8);

        tx.send(1).unwrap();
        tx.send(2).unwrap();

        let r1 = rx.try_recv().unwrap();
        assert_eq!(r1.value, 1);
        assert_eq!(r1.lagged, 0);

        let r2 = rx.try_recv().unwrap();
        assert_eq!(r2.value, 2);
        assert_eq!(r2.lagged, 0);
    }

    #[test]
    fn recv_returns_lagged_nonzero_when_lapped() {
        let (mut tx, mut rx) = channel::<u64>(4);

        for i in 0..8 {
            tx.send(i).unwrap();
        }

        let result = rx.try_recv().unwrap();
        assert!(
            result.lagged > 0,
            "Expected lagged > 0, got {}",
            result.lagged
        );
        assert!(
            result.value >= 4,
            "Expected value >= 4, got {}",
            result.value
        );
    }

    #[test]
    fn fill_then_overwrite_all() {
        let (mut tx, mut rx) = channel::<u64>(4);

        for i in 0..4 {
            assert_eq!(tx.send(i).unwrap(), None);
        }

        for i in 4..8 {
            let old = tx.send(i).unwrap();
            assert_eq!(old, Some(i - 4));
        }

        let mut values = Vec::new();
        while let Ok(result) = rx.try_recv() {
            values.push(result.value);
        }
        assert!(values.iter().all(|&v| v >= 4));
    }

    // ============================================================================
    // Lapping
    // ============================================================================

    #[test]
    fn producer_laps_consumer_once() {
        let (mut tx, mut rx) = channel::<u64>(4);

        for i in 0..8 {
            tx.send(i).unwrap();
        }

        let result = rx.try_recv().unwrap();
        assert!(result.lagged > 0);
        assert!(result.value >= 4);
    }

    #[test]
    fn consumer_catches_up_after_lag() {
        let (mut tx, mut rx) = channel::<u64>(4);

        for i in 0..8 {
            tx.send(i).unwrap();
        }

        let r1 = rx.try_recv().unwrap();
        assert!(r1.lagged > 0);

        let r2 = rx.try_recv().unwrap();
        assert_eq!(r2.lagged, 0);

        let r3 = rx.try_recv().unwrap();
        assert_eq!(r3.lagged, 0);
    }

    #[test]
    fn lagged_count_accuracy() {
        let (mut tx, mut rx) = channel::<u64>(4);

        for i in 0..8 {
            tx.send(i).unwrap();
        }

        let result = rx.try_recv().unwrap();
        assert!(
            result.lagged >= 2 && result.lagged <= 8,
            "Expected lagged between 2-8, got {}",
            result.lagged
        );
    }

    // ============================================================================
    // Disconnection
    // ============================================================================

    #[test]
    fn sender_disconnect_then_recv_drains() {
        let (mut tx, mut rx) = channel::<u64>(8);

        tx.send(1).unwrap();
        tx.send(2).unwrap();
        tx.send(3).unwrap();

        drop(tx);

        assert_eq!(rx.try_recv().unwrap().value, 1);
        assert_eq!(rx.try_recv().unwrap().value, 2);
        assert_eq!(rx.try_recv().unwrap().value, 3);
        assert!(matches!(rx.try_recv(), Err(TryRecvError::Disconnected)));
    }

    #[test]
    fn sender_disconnect_empty_queue() {
        let (tx, mut rx) = channel::<u64>(8);

        drop(tx);

        assert!(matches!(rx.try_recv(), Err(TryRecvError::Disconnected)));
    }

    #[test]
    fn sender_disconnect_after_overwrite() {
        let (mut tx, mut rx) = channel::<u64>(4);

        for i in 0..8 {
            tx.send(i).unwrap();
        }

        drop(tx);

        let mut count = 0;
        loop {
            match rx.try_recv() {
                Ok(_) => count += 1,
                Err(TryRecvError::Empty) => {}
                Err(TryRecvError::Disconnected) => break,
            }
        }
        assert_eq!(count, 4);
    }

    #[test]
    fn receiver_disconnect_returns_disconnected_error() {
        let (mut tx, rx) = channel::<u64>(4);

        tx.send(1).unwrap();
        tx.send(2).unwrap();
        tx.send(3).unwrap();
        tx.send(4).unwrap();

        drop(rx);

        match tx.send(5) {
            Err(SendError::Disconnected(5)) => {}
            _ => panic!("Expected Disconnected error"),
        }
    }

    // ============================================================================
    // Drop Behavior
    // ============================================================================

    #[test]
    fn drop_sender_drops_remaining_items() {
        use std::sync::Arc;
        use std::sync::atomic::{AtomicUsize, Ordering};

        let drop_count = Arc::new(AtomicUsize::new(0));

        struct DropCounter(Arc<AtomicUsize>);
        impl Drop for DropCounter {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }

        let (mut tx, rx) = channel::<DropCounter>(8);

        tx.send(DropCounter(Arc::clone(&drop_count))).unwrap();
        tx.send(DropCounter(Arc::clone(&drop_count))).unwrap();
        tx.send(DropCounter(Arc::clone(&drop_count))).unwrap();

        assert_eq!(drop_count.load(Ordering::SeqCst), 0);

        drop(rx);
        drop(tx);

        assert_eq!(drop_count.load(Ordering::SeqCst), 3);
    }

    #[test]
    fn overwrite_returns_old_value_for_drop() {
        use std::sync::Arc;
        use std::sync::atomic::{AtomicUsize, Ordering};

        let drop_count = Arc::new(AtomicUsize::new(0));

        struct DropCounter(Arc<AtomicUsize>);
        impl Drop for DropCounter {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }

        let (mut tx, _rx) = channel::<DropCounter>(4);

        for _ in 0..4 {
            tx.send(DropCounter(Arc::clone(&drop_count))).unwrap();
        }
        assert_eq!(drop_count.load(Ordering::SeqCst), 0);

        let old = tx.send(DropCounter(Arc::clone(&drop_count))).unwrap();
        drop(old);
        assert_eq!(drop_count.load(Ordering::SeqCst), 1);

        let old = tx.send(DropCounter(Arc::clone(&drop_count))).unwrap();
        drop(old);
        assert_eq!(drop_count.load(Ordering::SeqCst), 2);
    }

    #[test]
    fn consumed_slot_returns_none_on_overwrite() {
        use std::sync::Arc;
        use std::sync::atomic::{AtomicUsize, Ordering};

        let drop_count = Arc::new(AtomicUsize::new(0));

        struct DropCounter(Arc<AtomicUsize>);
        impl Drop for DropCounter {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }

        let (mut tx, mut rx) = channel::<DropCounter>(4);

        tx.send(DropCounter(Arc::clone(&drop_count))).unwrap();
        let item = rx.try_recv().unwrap().value;
        drop(item);
        assert_eq!(drop_count.load(Ordering::SeqCst), 1);

        tx.send(DropCounter(Arc::clone(&drop_count))).unwrap();
        tx.send(DropCounter(Arc::clone(&drop_count))).unwrap();
        tx.send(DropCounter(Arc::clone(&drop_count))).unwrap();

        let old = tx.send(DropCounter(Arc::clone(&drop_count))).unwrap();
        assert!(
            old.is_none(),
            "Slot was consumed, shouldn't return old value"
        );
        assert_eq!(drop_count.load(Ordering::SeqCst), 1);
    }

    // ============================================================================
    // Cross-Thread
    // ============================================================================

    #[test]
    fn cross_thread_basic() {
        use std::thread;

        let (mut tx, mut rx) = channel::<u64>(64);

        let producer = thread::spawn(move || {
            for i in 0..1000 {
                tx.send(i).unwrap();
            }
        });

        let consumer = thread::spawn(move || {
            let mut received = 0;
            let mut lagged_total = 0;
            loop {
                match rx.try_recv() {
                    Ok(result) => {
                        received += 1;
                        lagged_total += result.lagged;
                    }
                    Err(TryRecvError::Empty) => thread::yield_now(),
                    Err(TryRecvError::Disconnected) => break,
                }
            }
            (received, lagged_total)
        });

        producer.join().unwrap();
        let (received, _lagged) = consumer.join().unwrap();
        assert!(received > 0);
    }

    #[test]
    fn cross_thread_fast_producer_slow_consumer() {
        use std::thread;
        use std::time::Duration;

        let (mut tx, mut rx) = channel::<u64>(16);

        let producer = thread::spawn(move || {
            for i in 0..10000 {
                tx.send(i).unwrap();
            }
        });

        let consumer = thread::spawn(move || {
            let mut lagged_total = 0;
            loop {
                match rx.try_recv() {
                    Ok(result) => {
                        lagged_total += result.lagged;
                        thread::sleep(Duration::from_micros(1));
                    }
                    Err(TryRecvError::Empty) => thread::yield_now(),
                    Err(TryRecvError::Disconnected) => break,
                }
            }
            lagged_total
        });

        producer.join().unwrap();
        let lagged = consumer.join().unwrap();
        assert!(lagged > 0, "Expected lag with fast producer");
    }

    #[test]
    fn cross_thread_disconnect_terminates() {
        use std::thread;

        let (tx, mut rx) = channel::<u64>(16);

        let consumer = thread::spawn(move || {
            loop {
                match rx.try_recv() {
                    Ok(_) => {}
                    Err(TryRecvError::Empty) => thread::yield_now(),
                    Err(TryRecvError::Disconnected) => return true,
                }
            }
        });

        drop(tx);

        let terminated = consumer.join().unwrap();
        assert!(terminated);
    }

    #[test]
    fn cross_thread_no_hang_after_disconnect() {
        use std::sync::Arc;
        use std::sync::atomic::{AtomicBool, Ordering};
        use std::thread;
        use std::time::Duration;

        let (mut tx, mut rx) = channel::<u64>(16);
        let finished = Arc::new(AtomicBool::new(false));
        let finished_clone = Arc::clone(&finished);

        for i in 0..100 {
            tx.send(i).unwrap();
        }

        let consumer = thread::spawn(move || {
            loop {
                match rx.try_recv() {
                    Ok(_) => {}
                    Err(TryRecvError::Empty) => {
                        if finished_clone.load(Ordering::Relaxed) {
                            thread::sleep(Duration::from_millis(1));
                        }
                        thread::yield_now();
                    }
                    Err(TryRecvError::Disconnected) => return,
                }
            }
        });

        drop(tx);
        finished.store(true, Ordering::Relaxed);

        let result = consumer.join();
        assert!(result.is_ok());
    }

    // ============================================================================
    // Special Types
    // ============================================================================

    #[test]
    fn zero_sized_type() {
        let (mut tx, mut rx) = channel::<()>(8);

        tx.send(()).unwrap();
        tx.send(()).unwrap();

        assert_eq!(rx.try_recv().unwrap().value, ());
        assert_eq!(rx.try_recv().unwrap().value, ());
    }

    #[test]
    fn large_message_4kb() {
        #[derive(Clone, PartialEq, Debug)]
        struct LargeMessage {
            data: [u8; 4096],
            id: u64,
        }

        let (mut tx, mut rx) = channel::<LargeMessage>(4);

        let msg = LargeMessage {
            data: [0xAB; 4096],
            id: 12345,
        };

        tx.send(msg.clone()).unwrap();
        let received = rx.try_recv().unwrap().value;

        assert_eq!(received.id, 12345);
        assert_eq!(received.data[0], 0xAB);
        assert_eq!(received.data[4095], 0xAB);
    }

    #[test]
    fn non_copy_type_drops_correctly() {
        use std::sync::Arc;
        use std::sync::atomic::{AtomicUsize, Ordering};

        let drop_count = Arc::new(AtomicUsize::new(0));

        struct NonCopy {
            data: String,
            counter: Arc<AtomicUsize>,
        }
        impl Drop for NonCopy {
            fn drop(&mut self) {
                self.counter.fetch_add(1, Ordering::SeqCst);
            }
        }

        let (mut tx, mut rx) = channel::<NonCopy>(4);

        tx.send(NonCopy {
            data: "hello".to_string(),
            counter: Arc::clone(&drop_count),
        })
        .unwrap();

        let item = rx.try_recv().unwrap().value;
        assert_eq!(item.data, "hello");
        drop(item);
        assert_eq!(drop_count.load(Ordering::SeqCst), 1);
    }

    // ============================================================================
    // send_unchecked
    // ============================================================================

    #[test]
    fn send_unchecked_returns_old_value() {
        let (mut tx, _rx) = channel::<u64>(4);

        assert_eq!(tx.send_unchecked(1), None);
        assert_eq!(tx.send_unchecked(2), None);
        assert_eq!(tx.send_unchecked(3), None);
        assert_eq!(tx.send_unchecked(4), None);

        assert_eq!(tx.send_unchecked(5), Some(1));
        assert_eq!(tx.send_unchecked(6), Some(2));
    }

    // ============================================================================
    // Stress Tests
    // ============================================================================

    #[test]
    fn stress_test_many_overwrites() {
        let (mut tx, mut rx) = channel::<u64>(16);

        for i in 0..100_000 {
            tx.send(i).unwrap();
        }

        let mut count = 0;
        while rx.try_recv().is_ok() {
            count += 1;
        }

        assert_eq!(count, 16);
    }

    #[test]
    fn stress_test_cross_thread_high_volume() {
        use std::thread;

        const COUNT: u64 = 1_000_000;

        let (mut tx, mut rx) = channel::<u64>(1024);

        let producer = thread::spawn(move || {
            for i in 0..COUNT {
                tx.send(i).unwrap();
            }
        });

        let consumer = thread::spawn(move || {
            let mut received = 0u64;
            loop {
                match rx.try_recv() {
                    Ok(_) => received += 1,
                    Err(TryRecvError::Empty) => std::hint::spin_loop(),
                    Err(TryRecvError::Disconnected) => break,
                }
            }
            received
        });

        producer.join().unwrap();
        let received = consumer.join().unwrap();

        // Verify we received some messages and didn't hang
        assert!(received > 0, "Should have received at least some messages");
        assert!(received <= COUNT, "Can't receive more than sent");
    }

    #[test]
    fn stress_test_alternating_overwrite_consume() {
        let (mut tx, mut rx) = channel::<u64>(4);

        for round in 0..1000 {
            for i in 0..8 {
                tx.send(round * 8 + i).unwrap();
            }

            let mut count = 0;
            while rx.try_recv().is_ok() {
                count += 1;
            }
            assert_eq!(count, 4, "Round {}: expected 4 items", round);
        }
    }

    // ============================================================================
    // Edge Cases
    // ============================================================================

    #[test]
    fn empty_then_overwrite() {
        let (mut tx, mut rx) = channel::<u64>(4);

        for i in 0..4 {
            tx.send(i).unwrap();
        }
        for _ in 0..4 {
            rx.try_recv().unwrap();
        }

        for i in 4..12 {
            tx.send(i).unwrap();
        }

        let result = rx.try_recv().unwrap();
        assert!(result.value >= 8 || result.lagged > 0);
    }

    #[test]
    fn interleaved_send_recv_no_overwrite() {
        let (mut tx, mut rx) = channel::<u64>(8);

        for i in 0..1000 {
            tx.send(i).unwrap();
            let result = rx.try_recv().unwrap();
            assert_eq!(result.value, i);
            assert_eq!(result.lagged, 0);
        }
    }

    #[test]
    fn single_slot_queue() {
        let (mut tx, mut rx) = channel::<u64>(1);
        // Capacity 1 - single slot, every send after first overwrites

        assert_eq!(tx.send(1).unwrap(), None); // First write, no overwrite
        assert_eq!(tx.send(2).unwrap(), Some(1)); // Overwrites 1
        assert_eq!(tx.send(3).unwrap(), Some(2)); // Overwrites 2

        let r = rx.try_recv().unwrap();
        assert_eq!(r.value, 3);
        assert!(r.lagged > 0); // We missed messages
    }
}
