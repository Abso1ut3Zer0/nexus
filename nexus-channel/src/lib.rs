//! High-performance bounded SPSC channel for low-latency systems.
//!
//! This crate provides a blocking single-producer single-consumer channel
//! optimized for trading systems and other latency-critical workloads.
//!
//! For MPSC (multi-producer), use [`crossbeam-channel`](https://docs.rs/crossbeam-channel)
//! which is well-optimized for that use case. For raw MPSC queue performance without
//! blocking semantics, see [`nexus-queue::mpsc`](https://docs.rs/nexus-queue).
//!
//! # Design
//!
//! The channel uses a three-phase backoff strategy that minimizes syscall overhead:
//!
//! 1. **Fast path**: Try the operation immediately
//! 2. **Backoff**: Spin with exponential backoff using `crossbeam::Backoff`
//! 3. **Park**: Sleep until woken by the other end
//!
//! The key optimization is *conditional parking*: we only issue expensive unpark
//! syscalls when the other end has actually gone to sleep. This dramatically
//! reduces tail latency compared to channels that unpark unconditionally.
//!
//! # Quick Start
//!
//! ```
//! use nexus_channel::channel;
//!
//! let (tx, rx) = channel::<u64>(1024);
//!
//! tx.send(42).unwrap();
//! assert_eq!(rx.recv().unwrap(), 42);
//! ```
//!
//! # Timeout Support
//!
//! ```
//! use nexus_channel::{channel, RecvTimeoutError};
//! use std::time::Duration;
//!
//! let (tx, rx) = channel::<u64>(4);
//!
//! match rx.recv_timeout(Duration::from_millis(100)) {
//!     Ok(value) => println!("got {}", value),
//!     Err(RecvTimeoutError::Timeout) => println!("timed out"),
//!     Err(RecvTimeoutError::Disconnected) => println!("sender dropped"),
//! }
//! ```
//!
//! # Performance
//!
//! Benchmarked against `crossbeam-channel` on Intel Core Ultra 7 @ 2.7GHz,
//! pinned to physical cores with turbo disabled:
//!
//! | Metric | nexus-channel | crossbeam-channel | Improvement |
//! |--------|---------------|-------------------|-------------|
//! | p50 latency | 665 cycles | 1344 cycles | **2.0x** |
//! | p999 latency | 2501 cycles | 37023 cycles | **14.8x** |
//! | Throughput | 64 M msgs/sec | 34 M msgs/sec | **1.9x** |
//!
//! The large p999 improvement comes from avoiding unnecessary syscalls.

#![deny(unsafe_op_in_unsafe_fn)]
#![warn(missing_docs, missing_debug_implementations)]

use core::fmt;
use std::mem::ManuallyDrop;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering, fence};
use std::time::{Duration, Instant};

use crossbeam_utils::sync::{Parker, Unparker};
use crossbeam_utils::{Backoff, CachePadded};
use nexus_queue::Full;
use nexus_queue::spsc::{Consumer, Producer, ring_buffer};

// Re-export spsc module for backwards compatibility
pub mod spsc {
    //! Single-producer single-consumer bounded channel (re-export).
    //!
    //! This module re-exports the channel types from the crate root for
    //! backwards compatibility. You can also use `nexus_channel::channel()`
    //! directly.

    pub use crate::{Receiver, Sender, channel, channel_with_config};
}

// ============================================================================
// Channel Creation
// ============================================================================

/// Default number of backoff snooze iterations before parking.
const DEFAULT_SNOOZE_ITERS: usize = 8;

/// Shared state between sender and receiver.
struct Shared {
    sender_parked: CachePadded<AtomicBool>,
    receiver_parked: CachePadded<AtomicBool>,
}

/// Creates a bounded SPSC channel with the given capacity.
///
/// Returns a `(Sender, Receiver)` pair. The actual capacity will be rounded
/// up to the next power of two.
///
/// # Panics
///
/// Panics if `capacity` is 0.
///
/// # Example
///
/// ```
/// use nexus_channel::channel;
///
/// let (tx, rx) = channel::<String>(100);
///
/// tx.send("hello".to_string()).unwrap();
/// assert_eq!(rx.recv().unwrap(), "hello");
/// ```
pub fn channel<T>(capacity: usize) -> (Sender<T>, Receiver<T>) {
    channel_with_config(capacity, DEFAULT_SNOOZE_ITERS)
}

/// Creates a bounded SPSC channel with custom backoff configuration.
///
/// # Arguments
///
/// * `capacity` - Maximum number of messages the channel can hold (rounded to power of 2)
/// * `snooze_iters` - Number of backoff iterations before parking. Higher values
///   burn more CPU but reduce latency for bursty workloads.
///
/// # Panics
///
/// Panics if `capacity` is 0.
pub fn channel_with_config<T>(capacity: usize, snooze_iters: usize) -> (Sender<T>, Receiver<T>) {
    let (producer, consumer) = ring_buffer(capacity);

    let shared = Arc::new(Shared {
        sender_parked: CachePadded::new(AtomicBool::new(false)),
        receiver_parked: CachePadded::new(AtomicBool::new(false)),
    });

    let sender_parker = Parker::new();
    let sender_unparker = sender_parker.unparker().clone();

    let receiver_parker = Parker::new();
    let receiver_unparker = receiver_parker.unparker().clone();

    (
        Sender {
            producer: ManuallyDrop::new(producer),
            shared: Arc::clone(&shared),
            parker: sender_parker,
            receiver_unparker,
            snooze_iters,
        },
        Receiver {
            consumer: ManuallyDrop::new(consumer),
            shared,
            parker: receiver_parker,
            sender_unparker,
            snooze_iters,
        },
    )
}

// ============================================================================
// Sender
// ============================================================================

/// The sending half of an SPSC channel.
///
/// Messages can be sent with [`send`](Sender::send) (blocking) or
/// [`try_send`](Sender::try_send) (non-blocking).
pub struct Sender<T> {
    producer: ManuallyDrop<Producer<T>>,
    shared: Arc<Shared>,
    parker: Parker,
    receiver_unparker: Unparker,
    snooze_iters: usize,
}

impl<T> Sender<T> {
    /// Sends a message into the channel, blocking if necessary.
    ///
    /// If the channel is full, this method will block until space is available
    /// or the receiver disconnects.
    ///
    /// Returns `Err(SendError(value))` if the receiver has been dropped.
    #[inline]
    pub fn send(&self, value: T) -> Result<(), SendError<T>> {
        if self.producer.is_disconnected() {
            return cold_send_err(value);
        }

        let mut val = value;

        // Fast path
        match self.producer.push(val) {
            Ok(()) => {
                self.notify_receiver();
                return Ok(());
            }
            Err(Full(v)) => val = v,
        }

        // Backoff phase
        let backoff = Backoff::new();
        for _ in 0..self.snooze_iters {
            backoff.snooze();

            if self.producer.is_disconnected() {
                return cold_send_err(val);
            }

            match self.producer.push(val) {
                Ok(()) => {
                    self.notify_receiver();
                    return Ok(());
                }
                Err(Full(v)) => val = v,
            }
        }

        // Park phase
        loop {
            self.shared.sender_parked.store(true, Ordering::SeqCst);
            fence(Ordering::SeqCst);

            if self.producer.is_disconnected() {
                self.shared.sender_parked.store(false, Ordering::Relaxed);
                return cold_send_err(val);
            }

            match self.producer.push(val) {
                Ok(()) => {
                    self.shared.sender_parked.store(false, Ordering::Relaxed);
                    self.notify_receiver();
                    return Ok(());
                }
                Err(Full(v)) => val = v,
            }

            self.parker.park();
            self.shared.sender_parked.store(false, Ordering::Relaxed);

            if self.producer.is_disconnected() {
                return cold_send_err(val);
            }

            match self.producer.push(val) {
                Ok(()) => {
                    self.notify_receiver();
                    return Ok(());
                }
                Err(Full(v)) => val = v,
            }
        }
    }

    /// Attempts to send a message without blocking.
    ///
    /// Returns immediately with:
    /// - `Ok(())` if the message was sent
    /// - `Err(TrySendError::Full(value))` if the channel is full
    /// - `Err(TrySendError::Disconnected(value))` if the receiver was dropped
    #[inline]
    pub fn try_send(&self, value: T) -> Result<(), TrySendError<T>> {
        if self.producer.is_disconnected() {
            return cold_try_send_disconnected(value);
        }

        match self.producer.push(value) {
            Ok(()) => {
                self.notify_receiver();
                Ok(())
            }
            Err(Full(v)) => Err(TrySendError::Full(v)),
        }
    }

    #[inline]
    fn notify_receiver(&self) {
        fence(Ordering::SeqCst);
        if self.shared.receiver_parked.load(Ordering::SeqCst) {
            self.receiver_unparker.unpark();
        }
    }

    /// Returns `true` if the receiver has been dropped.
    #[inline]
    pub fn is_disconnected(&self) -> bool {
        self.producer.is_disconnected()
    }

    /// Returns the capacity of the channel.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.producer.capacity()
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

impl<T> Drop for Sender<T> {
    fn drop(&mut self) {
        // SAFETY: producer is valid (ManuallyDrop preserves it). We drop it here to
        // trigger the Producer's disconnect logic before unparking the receiver, so
        // the receiver sees is_disconnected() == true after waking.
        unsafe { ManuallyDrop::drop(&mut self.producer) };
        self.receiver_unparker.unpark();
    }
}

// ============================================================================
// Receiver
// ============================================================================

/// The receiving half of an SPSC channel.
///
/// Messages can be received with [`recv`](Receiver::recv) (blocking),
/// [`recv_timeout`](Receiver::recv_timeout) (blocking with timeout), or
/// [`try_recv`](Receiver::try_recv) (non-blocking).
pub struct Receiver<T> {
    consumer: ManuallyDrop<Consumer<T>>,
    shared: Arc<Shared>,
    parker: Parker,
    sender_unparker: Unparker,
    snooze_iters: usize,
}

impl<T> Receiver<T> {
    /// Receives a message from the channel, blocking if necessary.
    ///
    /// If the channel is empty, this method will block until a message arrives
    /// or the sender disconnects.
    ///
    /// Returns `Err(RecvError)` if the sender has been dropped and no messages
    /// remain in the channel.
    #[inline]
    pub fn recv(&self) -> Result<T, RecvError> {
        // Fast path
        if let Some(v) = self.consumer.pop() {
            self.notify_sender();
            return Ok(v);
        }

        // Backoff phase
        let backoff = Backoff::new();
        for _ in 0..self.snooze_iters {
            backoff.snooze();

            if let Some(v) = self.consumer.pop() {
                self.notify_sender();
                return Ok(v);
            }

            if self.consumer.is_disconnected() {
                return self.consumer.pop().ok_or(RecvError);
            }
        }

        // Park phase
        loop {
            self.shared.receiver_parked.store(true, Ordering::SeqCst);
            fence(Ordering::SeqCst);

            if let Some(v) = self.consumer.pop() {
                self.shared.receiver_parked.store(false, Ordering::Relaxed);
                self.notify_sender();
                return Ok(v);
            }

            if self.consumer.is_disconnected() {
                self.shared.receiver_parked.store(false, Ordering::Relaxed);
                return cold_recv_err();
            }

            self.parker.park();
            self.shared.receiver_parked.store(false, Ordering::Relaxed);

            if let Some(v) = self.consumer.pop() {
                self.notify_sender();
                return Ok(v);
            }

            if self.consumer.is_disconnected() {
                return cold_recv_err();
            }
        }
    }

    /// Receives a message from the channel, blocking for at most `timeout`.
    ///
    /// Returns:
    /// - `Ok(value)` if a message was received
    /// - `Err(RecvTimeoutError::Timeout)` if the timeout elapsed
    /// - `Err(RecvTimeoutError::Disconnected)` if the sender was dropped
    pub fn recv_timeout(&self, timeout: Duration) -> Result<T, RecvTimeoutError> {
        let deadline = Instant::now() + timeout;

        // Fast path
        if let Some(v) = self.consumer.pop() {
            self.notify_sender();
            return Ok(v);
        }

        // Backoff phase
        let backoff = Backoff::new();
        for _ in 0..self.snooze_iters {
            if Instant::now() >= deadline {
                return Err(RecvTimeoutError::Timeout);
            }

            backoff.snooze();

            if let Some(v) = self.consumer.pop() {
                self.notify_sender();
                return Ok(v);
            }

            if self.consumer.is_disconnected() {
                return self.consumer.pop().ok_or(RecvTimeoutError::Disconnected);
            }
        }

        // Park phase with timeout
        loop {
            let now = Instant::now();
            if now >= deadline {
                return Err(RecvTimeoutError::Timeout);
            }

            self.shared.receiver_parked.store(true, Ordering::SeqCst);
            fence(Ordering::SeqCst);

            if let Some(v) = self.consumer.pop() {
                self.shared.receiver_parked.store(false, Ordering::Relaxed);
                self.notify_sender();
                return Ok(v);
            }

            if self.consumer.is_disconnected() {
                self.shared.receiver_parked.store(false, Ordering::Relaxed);
                return cold_recv_timeout_disconnected();
            }

            let remaining = deadline - now;
            self.parker.park_timeout(remaining);
            self.shared.receiver_parked.store(false, Ordering::Relaxed);

            if let Some(v) = self.consumer.pop() {
                self.notify_sender();
                return Ok(v);
            }

            if self.consumer.is_disconnected() {
                return cold_recv_timeout_disconnected();
            }
        }
    }

    /// Attempts to receive a message without blocking.
    ///
    /// Returns immediately with:
    /// - `Ok(value)` if a message was available
    /// - `Err(TryRecvError::Empty)` if the channel is empty
    /// - `Err(TryRecvError::Disconnected)` if the sender was dropped and channel is empty
    #[inline]
    #[allow(clippy::option_if_let_else)]
    pub fn try_recv(&self) -> Result<T, TryRecvError> {
        match self.consumer.pop() {
            Some(v) => {
                self.notify_sender();
                Ok(v)
            }
            None => {
                if self.consumer.is_disconnected() {
                    cold_try_recv_disconnected()
                } else {
                    Err(TryRecvError::Empty)
                }
            }
        }
    }

    #[inline]
    fn notify_sender(&self) {
        fence(Ordering::SeqCst);
        if self.shared.sender_parked.load(Ordering::SeqCst) {
            self.sender_unparker.unpark();
        }
    }

    /// Returns `true` if the sender has been dropped.
    #[inline]
    pub fn is_disconnected(&self) -> bool {
        self.consumer.is_disconnected()
    }

    /// Returns the capacity of the channel.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.consumer.capacity()
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

impl<T> Drop for Receiver<T> {
    fn drop(&mut self) {
        // SAFETY: consumer is valid (ManuallyDrop preserves it). We drop it here to
        // trigger the Consumer's disconnect logic before unparking the sender, so
        // the sender sees is_disconnected() == true after waking.
        unsafe { ManuallyDrop::drop(&mut self.consumer) };
        self.sender_unparker.unpark();
    }
}

// ============================================================================
// Error Types
// ============================================================================

/// Error returned when sending fails due to disconnection.
///
/// Contains the message that could not be sent, allowing recovery of the value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SendError<T>(pub T);

impl<T> SendError<T> {
    /// Returns the message that could not be sent.
    pub fn into_inner(self) -> T {
        self.0
    }
}

impl<T> fmt::Display for SendError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "channel disconnected")
    }
}

impl<T: fmt::Debug> std::error::Error for SendError<T> {}

/// Error returned when receiving fails due to disconnection.
///
/// This error occurs when all senders have been dropped and no messages
/// remain in the channel.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RecvError;

impl fmt::Display for RecvError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "channel disconnected")
    }
}

impl std::error::Error for RecvError {}

/// Error returned by `try_send`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TrySendError<T> {
    /// The channel is full but still connected.
    Full(T),

    /// The receiver has been dropped.
    Disconnected(T),
}

impl<T> TrySendError<T> {
    /// Returns the message that could not be sent.
    pub fn into_inner(self) -> T {
        match self {
            TrySendError::Full(v) | TrySendError::Disconnected(v) => v,
        }
    }

    /// Returns `true` if this error is the `Full` variant.
    pub fn is_full(&self) -> bool {
        matches!(self, TrySendError::Full(_))
    }

    /// Returns `true` if this error is the `Disconnected` variant.
    pub fn is_disconnected(&self) -> bool {
        matches!(self, TrySendError::Disconnected(_))
    }
}

impl<T> fmt::Display for TrySendError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TrySendError::Full(_) => write!(f, "channel full"),
            TrySendError::Disconnected(_) => write!(f, "channel disconnected"),
        }
    }
}

impl<T: fmt::Debug> std::error::Error for TrySendError<T> {}

/// Error returned by `try_recv`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TryRecvError {
    /// The channel is empty but still connected.
    Empty,

    /// All senders have been dropped and no messages remain.
    Disconnected,
}

impl TryRecvError {
    /// Returns `true` if this error is the `Empty` variant.
    pub fn is_empty(&self) -> bool {
        matches!(self, TryRecvError::Empty)
    }

    /// Returns `true` if this error is the `Disconnected` variant.
    pub fn is_disconnected(&self) -> bool {
        matches!(self, TryRecvError::Disconnected)
    }
}

impl fmt::Display for TryRecvError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TryRecvError::Empty => write!(f, "channel empty"),
            TryRecvError::Disconnected => write!(f, "channel disconnected"),
        }
    }
}

impl std::error::Error for TryRecvError {}

/// Error returned by `recv_timeout`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RecvTimeoutError {
    /// The timeout elapsed before a message arrived.
    Timeout,

    /// All senders have been dropped and no messages remain.
    Disconnected,
}

impl RecvTimeoutError {
    /// Returns `true` if this error is the `Timeout` variant.
    pub fn is_timeout(&self) -> bool {
        matches!(self, RecvTimeoutError::Timeout)
    }

    /// Returns `true` if this error is the `Disconnected` variant.
    pub fn is_disconnected(&self) -> bool {
        matches!(self, RecvTimeoutError::Disconnected)
    }
}

impl fmt::Display for RecvTimeoutError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RecvTimeoutError::Timeout => write!(f, "timed out"),
            RecvTimeoutError::Disconnected => write!(f, "channel disconnected"),
        }
    }
}

impl std::error::Error for RecvTimeoutError {}

// ============================================================================
// Cold error constructors
// ============================================================================

#[cold]
fn cold_send_err<T>(val: T) -> Result<(), SendError<T>> {
    Err(SendError(val))
}

#[cold]
fn cold_try_send_disconnected<T>(val: T) -> Result<(), TrySendError<T>> {
    Err(TrySendError::Disconnected(val))
}

#[cold]
fn cold_recv_err<T>() -> Result<T, RecvError> {
    Err(RecvError)
}

#[cold]
fn cold_try_recv_disconnected<T>() -> Result<T, TryRecvError> {
    Err(TryRecvError::Disconnected)
}

#[cold]
fn cold_recv_timeout_disconnected<T>() -> Result<T, RecvTimeoutError> {
    Err(RecvTimeoutError::Disconnected)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::AtomicUsize;
    use std::thread;

    // ============================================================================
    // Basic Operations
    // ============================================================================

    #[test]
    fn basic_send_recv() {
        let (tx, rx) = channel::<u64>(4);

        tx.send(1).unwrap();
        tx.send(2).unwrap();
        tx.send(3).unwrap();

        assert_eq!(rx.recv().unwrap(), 1);
        assert_eq!(rx.recv().unwrap(), 2);
        assert_eq!(rx.recv().unwrap(), 3);
    }

    #[test]
    fn try_send_try_recv() {
        let (tx, rx) = channel::<u64>(2);

        assert!(tx.try_send(1).is_ok());
        assert!(tx.try_send(2).is_ok());
        assert!(matches!(tx.try_send(3), Err(TrySendError::Full(3))));

        assert_eq!(rx.try_recv().unwrap(), 1);
        assert_eq!(rx.try_recv().unwrap(), 2);
        assert!(matches!(rx.try_recv(), Err(TryRecvError::Empty)));
    }

    #[test]
    fn send_fills_then_recv_drains() {
        let (tx, rx) = channel::<u64>(4);

        for i in 0..4 {
            tx.try_send(i).unwrap();
        }
        assert!(matches!(tx.try_send(99), Err(TrySendError::Full(99))));

        for i in 0..4 {
            assert_eq!(rx.recv().unwrap(), i);
        }
        assert!(matches!(rx.try_recv(), Err(TryRecvError::Empty)));
    }

    // ============================================================================
    // Timeout Operations
    // ============================================================================

    #[test]
    fn recv_timeout_success() {
        let (tx, rx) = channel::<u64>(4);

        tx.send(42).unwrap();

        let result = rx.recv_timeout(Duration::from_millis(100));
        assert_eq!(result.unwrap(), 42);
    }

    #[test]
    fn recv_timeout_expires() {
        let (_tx, rx) = channel::<u64>(4);

        let start = Instant::now();
        let result = rx.recv_timeout(Duration::from_millis(50));

        assert!(matches!(result, Err(RecvTimeoutError::Timeout)));
        assert!(start.elapsed() >= Duration::from_millis(50));
    }

    #[test]
    fn recv_timeout_disconnected() {
        let (tx, rx) = channel::<u64>(4);

        drop(tx);

        let result = rx.recv_timeout(Duration::from_millis(100));
        assert!(matches!(result, Err(RecvTimeoutError::Disconnected)));
    }

    #[test]
    fn recv_timeout_data_arrives() {
        let (tx, rx) = channel::<u64>(4);

        let handle = thread::spawn(move || {
            thread::sleep(Duration::from_millis(25));
            tx.send(42).unwrap();
        });

        let result = rx.recv_timeout(Duration::from_millis(100));
        assert_eq!(result.unwrap(), 42);

        handle.join().unwrap();
    }

    #[test]
    fn recv_timeout_disconnect_while_waiting() {
        let (tx, rx) = channel::<u64>(4);

        let handle = thread::spawn(move || {
            thread::sleep(Duration::from_millis(25));
            drop(tx);
        });

        let result = rx.recv_timeout(Duration::from_millis(100));
        assert!(matches!(result, Err(RecvTimeoutError::Disconnected)));

        handle.join().unwrap();
    }

    // ============================================================================
    // Disconnection
    // ============================================================================

    #[test]
    fn recv_returns_error_when_sender_dropped() {
        let (tx, rx) = channel::<u64>(4);

        drop(tx);

        assert!(rx.recv().is_err());
        assert!(matches!(rx.try_recv(), Err(TryRecvError::Disconnected)));
    }

    #[test]
    fn recv_drains_before_error_when_sender_dropped() {
        let (tx, rx) = channel::<u64>(4);

        tx.send(1).unwrap();
        tx.send(2).unwrap();
        drop(tx);

        assert_eq!(rx.recv().unwrap(), 1);
        assert_eq!(rx.recv().unwrap(), 2);
        assert!(rx.recv().is_err());
    }

    #[test]
    fn send_returns_error_when_receiver_dropped() {
        let (tx, rx) = channel::<u64>(4);

        drop(rx);

        assert!(tx.send(1).is_err());
        assert!(matches!(tx.try_send(1), Err(TrySendError::Disconnected(1))));
    }

    #[test]
    fn is_disconnected_sender() {
        let (tx, rx) = channel::<u64>(4);

        assert!(!tx.is_disconnected());
        drop(rx);
        assert!(tx.is_disconnected());
    }

    #[test]
    fn is_disconnected_receiver() {
        let (tx, rx) = channel::<u64>(4);

        assert!(!rx.is_disconnected());
        drop(tx);
        assert!(rx.is_disconnected());
    }

    // ============================================================================
    // Cross-Thread Basic
    // ============================================================================

    #[test]
    fn cross_thread_single_message() {
        let (tx, rx) = channel::<u64>(4);

        let handle = thread::spawn(move || rx.recv().unwrap());

        tx.send(42).unwrap();

        assert_eq!(handle.join().unwrap(), 42);
    }

    #[test]
    fn cross_thread_multiple_messages() {
        let (tx, rx) = channel::<u64>(4);

        let handle = thread::spawn(move || {
            let mut sum = 0;
            for _ in 0..100 {
                sum += rx.recv().unwrap();
            }
            sum
        });

        for i in 0..100 {
            tx.send(i).unwrap();
        }

        let sum = handle.join().unwrap();
        assert_eq!(sum, 99 * 100 / 2);
    }

    // ============================================================================
    // FIFO Ordering
    // ============================================================================

    #[test]
    fn fifo_ordering_single_thread() {
        let (tx, rx) = channel::<u64>(8);

        for i in 0..8 {
            tx.try_send(i).unwrap();
        }

        for i in 0..8 {
            assert_eq!(rx.recv().unwrap(), i);
        }
    }

    #[test]
    fn fifo_ordering_cross_thread() {
        let (tx, rx) = channel::<u64>(64);

        let handle = thread::spawn(move || {
            let mut expected = 0u64;
            while expected < 10_000 {
                let val = rx.recv().unwrap();
                assert_eq!(val, expected, "FIFO order violated");
                expected += 1;
            }
        });

        for i in 0..10_000 {
            tx.send(i).unwrap();
        }

        handle.join().unwrap();
    }

    // ============================================================================
    // Blocking Behavior
    // ============================================================================

    #[test]
    fn recv_blocks_until_send() {
        let (tx, rx) = channel::<u64>(4);

        let start = Instant::now();

        let handle = thread::spawn(move || rx.recv().unwrap());

        thread::sleep(Duration::from_millis(50));
        tx.send(42).unwrap();

        let val = handle.join().unwrap();
        assert_eq!(val, 42);
        assert!(start.elapsed() >= Duration::from_millis(50));
    }

    #[test]
    fn send_blocks_until_recv() {
        let (tx, rx) = channel::<u64>(2);

        // Fill the buffer
        tx.try_send(1).unwrap();
        tx.try_send(2).unwrap();

        let start = Instant::now();

        let handle = thread::spawn(move || {
            tx.send(3).unwrap(); // Should block
            tx
        });

        thread::sleep(Duration::from_millis(50));
        rx.recv().unwrap(); // Free up space

        let _ = handle.join().unwrap();
        assert!(start.elapsed() >= Duration::from_millis(50));
    }

    // ============================================================================
    // Wake on Disconnect
    // ============================================================================

    #[test]
    fn recv_wakes_on_sender_drop() {
        let (tx, rx) = channel::<u64>(4);

        let handle = thread::spawn(move || {
            let result = rx.recv();
            assert!(result.is_err());
        });

        thread::sleep(Duration::from_millis(50));
        drop(tx);

        // Should complete, not hang
        handle.join().unwrap();
    }

    #[test]
    fn send_wakes_on_receiver_drop() {
        let (tx, rx) = channel::<u64>(1);

        tx.try_send(1).unwrap(); // Fill it

        let handle = thread::spawn(move || {
            let result = tx.send(2); // Should block then error
            assert!(result.is_err());
        });

        thread::sleep(Duration::from_millis(50));
        drop(rx);

        // Should complete, not hang
        handle.join().unwrap();
    }

    // ============================================================================
    // Capacity Edge Cases
    // ============================================================================

    #[test]
    fn capacity_one() {
        let (tx, rx) = channel::<u64>(1);

        for i in 0..100 {
            tx.send(i).unwrap();
            assert_eq!(rx.recv().unwrap(), i);
        }
    }

    #[test]
    fn capacity_one_cross_thread() {
        let (tx, rx) = channel::<u64>(1);

        let handle = thread::spawn(move || {
            for _ in 0..1000 {
                rx.recv().unwrap();
            }
        });

        for i in 0..1000 {
            tx.send(i).unwrap();
        }

        handle.join().unwrap();
    }

    // ============================================================================
    // Drop Behavior
    // ============================================================================

    #[test]
    fn values_dropped_on_channel_drop() {
        static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

        #[derive(Debug)]
        struct DropCounter;
        impl Drop for DropCounter {
            fn drop(&mut self) {
                DROP_COUNT.fetch_add(1, Ordering::SeqCst);
            }
        }

        DROP_COUNT.store(0, Ordering::SeqCst);

        let (tx, rx) = channel::<DropCounter>(4);

        tx.try_send(DropCounter).unwrap();
        tx.try_send(DropCounter).unwrap();
        tx.try_send(DropCounter).unwrap();

        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), 0);

        drop(tx);
        drop(rx);

        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), 3);
    }

    #[test]
    fn failed_send_returns_value() {
        let (tx, rx) = channel::<String>(1);

        tx.try_send("hello".to_string()).unwrap();

        let err = tx.try_send("world".to_string());
        match err {
            Err(TrySendError::Full(s)) => assert_eq!(s, "world"),
            _ => panic!("expected Full error"),
        }

        drop(rx);

        let err = tx.try_send("test".to_string());
        match err {
            Err(TrySendError::Disconnected(s)) => assert_eq!(s, "test"),
            _ => panic!("expected Disconnected error"),
        }
    }

    // ============================================================================
    // Special Types
    // ============================================================================

    #[test]
    fn zero_sized_type() {
        let (tx, rx) = channel::<()>(4);

        tx.send(()).unwrap();
        tx.send(()).unwrap();

        assert_eq!(rx.recv().unwrap(), ());
        assert_eq!(rx.recv().unwrap(), ());
    }

    #[test]
    fn large_message_type() {
        #[derive(Clone, PartialEq, Debug)]
        struct LargeMessage {
            data: [u8; 4096],
        }

        let (tx, rx) = channel::<LargeMessage>(4);

        let msg = LargeMessage { data: [42u8; 4096] };
        tx.send(msg).unwrap();

        let received = rx.recv().unwrap();
        assert_eq!(received.data[0], 42);
        assert_eq!(received.data[4095], 42);
    }

    // ============================================================================
    // Multiple Laps
    // ============================================================================

    #[test]
    fn many_laps_single_thread() {
        let (tx, rx) = channel::<u64>(4);

        // 1000 messages through 4-slot buffer = 250 laps
        for i in 0..1000 {
            tx.send(i).unwrap();
            assert_eq!(rx.recv().unwrap(), i);
        }
    }

    #[test]
    fn many_laps_cross_thread() {
        const COUNT: u64 = 100_000;

        let (tx, rx) = channel::<u64>(4); // Small buffer, many laps

        let producer = thread::spawn(move || {
            for i in 0..COUNT {
                tx.send(i).unwrap();
            }
        });

        let consumer = thread::spawn(move || {
            let mut expected = 0u64;
            while expected < COUNT {
                let val = rx.recv().unwrap();
                assert_eq!(val, expected);
                expected += 1;
            }
        });

        producer.join().unwrap();
        consumer.join().unwrap();
    }

    // ============================================================================
    // Stress Tests
    // ============================================================================

    #[test]
    fn stress_high_volume() {
        const COUNT: u64 = 100_000;

        let (tx, rx) = channel::<u64>(1024);

        let producer = thread::spawn(move || {
            for i in 0..COUNT {
                tx.send(i).unwrap();
            }
        });

        let consumer = thread::spawn(move || {
            let mut sum = 0u64;
            for _ in 0..COUNT {
                sum = sum.wrapping_add(rx.recv().unwrap());
            }
            sum
        });

        producer.join().unwrap();
        let sum = consumer.join().unwrap();
        assert_eq!(sum, COUNT * (COUNT - 1) / 2);
    }

    #[test]
    fn stress_small_buffer() {
        const COUNT: u64 = 10_000;

        let (tx, rx) = channel::<u64>(4);

        let producer = thread::spawn(move || {
            for i in 0..COUNT {
                tx.send(i).unwrap();
            }
        });

        let consumer = thread::spawn(move || {
            let mut received = 0u64;
            while received < COUNT {
                rx.recv().unwrap();
                received += 1;
            }
            received
        });

        producer.join().unwrap();
        let received = consumer.join().unwrap();
        assert_eq!(received, COUNT);
    }

    #[test]
    fn stress_capacity_one_high_volume() {
        const COUNT: u64 = 10_000;

        let (tx, rx) = channel::<u64>(1);

        let producer = thread::spawn(move || {
            for i in 0..COUNT {
                tx.send(i).unwrap();
            }
        });

        let consumer = thread::spawn(move || {
            let mut expected = 0u64;
            while expected < COUNT {
                let val = rx.recv().unwrap();
                assert_eq!(val, expected);
                expected += 1;
            }
        });

        producer.join().unwrap();
        consumer.join().unwrap();
    }

    // ============================================================================
    // Ping-Pong Tests (exercises park/unpark heavily)
    // ============================================================================

    #[test]
    fn ping_pong_basic() {
        let (tx1, rx1) = channel::<u64>(1);
        let (tx2, rx2) = channel::<u64>(1);

        let handle = thread::spawn(move || {
            for i in 0..1000 {
                let val = rx1.recv().unwrap();
                assert_eq!(val, i);
                tx2.send(i).unwrap();
            }
        });

        for i in 0..1000 {
            tx1.send(i).unwrap();
            let val = rx2.recv().unwrap();
            assert_eq!(val, i);
        }

        handle.join().unwrap();
    }

    #[test]
    fn ping_pong_high_iterations() {
        let (tx1, rx1) = channel::<u64>(1);
        let (tx2, rx2) = channel::<u64>(1);

        let handle = thread::spawn(move || {
            for i in 0..10_000 {
                let val = rx1.recv().unwrap();
                assert_eq!(val, i);
                tx2.send(i * 2).unwrap();
            }
        });

        for i in 0..10_000 {
            tx1.send(i).unwrap();
            let val = rx2.recv().unwrap();
            assert_eq!(val, i * 2);
        }

        handle.join().unwrap();
    }

    // ============================================================================
    // Deadlock Prevention Tests
    // ============================================================================

    #[test]
    fn no_deadlock_alternating() {
        let (tx, rx) = channel::<u64>(1);

        let handle = thread::spawn(move || {
            for i in 0..1000u64 {
                tx.send(i).unwrap();
            }
        });

        for _ in 0..1000 {
            rx.recv().unwrap();
        }

        handle.join().unwrap();
    }

    #[test]
    fn no_deadlock_burst_then_drain() {
        let (tx, rx) = channel::<u64>(8);

        for round in 0..100 {
            // Burst
            for i in 0..8 {
                tx.try_send(round * 8 + i).unwrap();
            }
            // Drain
            for i in 0..8 {
                assert_eq!(rx.recv().unwrap(), round * 8 + i);
            }
        }
    }

    #[test]
    fn no_deadlock_concurrent_full_empty_transitions() {
        let (tx, rx) = channel::<u64>(2);

        let producer = thread::spawn(move || {
            for i in 0..10_000u64 {
                tx.send(i).unwrap();
            }
        });

        let consumer = thread::spawn(move || {
            for _ in 0..10_000 {
                rx.recv().unwrap();
            }
        });

        producer.join().unwrap();
        consumer.join().unwrap();
    }

    #[test]
    fn no_deadlock_disconnect_while_blocked_recv() {
        let (tx, rx) = channel::<u64>(1);

        let handle = thread::spawn(move || {
            // Will block waiting for data
            let result = rx.recv();
            assert!(result.is_err()); // Should error, not deadlock
        });

        thread::sleep(Duration::from_millis(50));
        drop(tx); // Disconnect while receiver is blocked

        handle.join().unwrap();
    }

    #[test]
    fn no_deadlock_disconnect_while_blocked_send() {
        let (tx, rx) = channel::<u64>(1);
        tx.try_send(1).unwrap(); // Fill it

        let handle = thread::spawn(move || {
            // Will block waiting for space
            let result = tx.send(2);
            assert!(result.is_err()); // Should error, not deadlock
        });

        thread::sleep(Duration::from_millis(50));
        drop(rx); // Disconnect while sender is blocked

        handle.join().unwrap();
    }

    // ============================================================================
    // Stress: Rapid Park/Unpark Cycles
    // ============================================================================

    #[test]
    fn stress_rapid_park_unpark_sender() {
        let (tx, rx) = channel::<u64>(1);

        let handle = thread::spawn(move || {
            for _ in 0..10_000 {
                rx.recv().unwrap();
            }
        });

        for i in 0..10_000 {
            tx.send(i).unwrap();
        }

        handle.join().unwrap();
    }

    #[test]
    fn stress_rapid_park_unpark_receiver() {
        let (tx, rx) = channel::<u64>(1);

        let handle = thread::spawn(move || {
            for i in 0..10_000 {
                tx.send(i).unwrap();
            }
        });

        for _ in 0..10_000 {
            rx.recv().unwrap();
        }

        handle.join().unwrap();
    }

    #[test]
    fn stress_park_unpark_both_sides() {
        // Both sender and receiver will park repeatedly
        let (tx, rx) = channel::<u64>(1);

        let sender = thread::spawn(move || {
            for i in 0..50_000 {
                tx.send(i).unwrap();
            }
        });

        let receiver = thread::spawn(move || {
            let mut count = 0;
            for _ in 0..50_000 {
                rx.recv().unwrap();
                count += 1;
            }
            count
        });

        sender.join().unwrap();
        assert_eq!(receiver.join().unwrap(), 50_000);
    }

    // ============================================================================
    // Timed Tests (ensure no indefinite blocking)
    // ============================================================================

    #[test]
    fn completes_in_reasonable_time() {
        use std::sync::mpsc;

        let (done_tx, done_rx) = mpsc::channel();

        let handle = thread::spawn(move || {
            let (tx, rx) = channel::<u64>(1);

            let h = thread::spawn(move || {
                for i in 0..1000 {
                    tx.send(i).unwrap();
                }
            });

            for _ in 0..1000 {
                rx.recv().unwrap();
            }

            h.join().unwrap();
            done_tx.send(()).unwrap();
        });

        // Should complete in well under a second
        let result = done_rx.recv_timeout(Duration::from_secs(5));
        assert!(result.is_ok(), "Test timed out - possible deadlock!");

        handle.join().unwrap();
    }

    #[test]
    fn does_not_hang_on_disconnect_during_recv() {
        let done = Arc::new(AtomicBool::new(false));
        let done_clone = done.clone();

        let (tx, rx) = channel::<u64>(4);

        let handle = thread::spawn(move || {
            let _ = rx.recv(); // Will block, then return Err on disconnect
            done_clone.store(true, Ordering::SeqCst);
        });

        thread::sleep(Duration::from_millis(50));
        assert!(!done.load(Ordering::SeqCst)); // Still blocked

        drop(tx);

        handle.join().unwrap();
        assert!(done.load(Ordering::SeqCst)); // Completed
    }

    #[test]
    fn does_not_hang_on_disconnect_during_send() {
        let done = Arc::new(AtomicBool::new(false));
        let done_clone = done.clone();

        let (tx, rx) = channel::<u64>(1);
        tx.try_send(1).unwrap(); // Fill it

        let handle = thread::spawn(move || {
            let _ = tx.send(2); // Will block, then return Err on disconnect
            done_clone.store(true, Ordering::SeqCst);
        });

        thread::sleep(Duration::from_millis(50));
        assert!(!done.load(Ordering::SeqCst)); // Still blocked

        drop(rx);

        handle.join().unwrap();
        assert!(done.load(Ordering::SeqCst)); // Completed
    }

    // ============================================================================
    // Rapid Connect/Disconnect
    // ============================================================================

    #[test]
    fn rapid_channel_creation() {
        for _ in 0..1000 {
            let (tx, rx) = channel::<u64>(4);
            tx.try_send(1).unwrap();
            assert_eq!(rx.recv().unwrap(), 1);
        }
    }

    #[test]
    fn rapid_disconnect() {
        for _ in 0..1000 {
            let (tx, rx) = channel::<u64>(4);
            drop(tx);
            drop(rx);
        }
    }

    // ============================================================================
    // Error Variant Coverage
    // ============================================================================

    #[test]
    fn send_error_returns_value_on_disconnect() {
        let (tx, rx) = channel::<u64>(4);
        drop(rx);

        match tx.send(42) {
            Err(SendError(v)) => assert_eq!(v, 42),
            Ok(()) => panic!("expected SendError"),
        }
    }

    #[test]
    fn send_error_into_inner() {
        let (tx, rx) = channel::<String>(4);
        drop(rx);

        let err = tx.send("hello".to_string()).unwrap_err();
        assert_eq!(err.into_inner(), "hello");
    }

    #[test]
    fn recv_error_on_disconnect() {
        let (tx, rx) = channel::<u64>(4);
        drop(tx);

        match rx.recv() {
            Err(RecvError) => {}
            Ok(_) => panic!("expected RecvError"),
        }
    }

    #[test]
    fn try_send_error_full_helpers() {
        let (tx, _rx) = channel::<u64>(1);
        tx.try_send(1).unwrap();

        let err = tx.try_send(2).unwrap_err();
        assert!(err.is_full());
        assert!(!err.is_disconnected());
        assert_eq!(err.into_inner(), 2);
    }

    #[test]
    fn try_send_error_disconnected_helpers() {
        let (tx, rx) = channel::<u64>(4);
        drop(rx);

        let err = tx.try_send(7).unwrap_err();
        assert!(err.is_disconnected());
        assert!(!err.is_full());
        assert_eq!(err.into_inner(), 7);
    }

    #[test]
    fn try_recv_error_empty_helpers() {
        let (_tx, rx) = channel::<u64>(4);

        let err = rx.try_recv().unwrap_err();
        assert!(err.is_empty());
        assert!(!err.is_disconnected());
    }

    #[test]
    fn try_recv_error_disconnected_helpers() {
        let (tx, rx) = channel::<u64>(4);
        drop(tx);

        let err = rx.try_recv().unwrap_err();
        assert!(err.is_disconnected());
        assert!(!err.is_empty());
    }

    #[test]
    fn recv_timeout_error_timeout_helpers() {
        let (_tx, rx) = channel::<u64>(4);

        let err = rx.recv_timeout(Duration::from_millis(1)).unwrap_err();
        assert!(err.is_timeout());
        assert!(!err.is_disconnected());
    }

    #[test]
    fn recv_timeout_error_disconnected_helpers() {
        let (tx, rx) = channel::<u64>(4);
        drop(tx);

        let err = rx.recv_timeout(Duration::from_millis(100)).unwrap_err();
        assert!(err.is_disconnected());
        assert!(!err.is_timeout());
    }

    // ============================================================================
    // Error Display Coverage
    // ============================================================================

    #[test]
    fn send_error_display() {
        let err = SendError(0u64);
        assert_eq!(err.to_string(), "channel disconnected");
    }

    #[test]
    fn recv_error_display() {
        assert_eq!(RecvError.to_string(), "channel disconnected");
    }

    #[test]
    fn try_send_error_display() {
        assert_eq!(TrySendError::Full(0u64).to_string(), "channel full");
        assert_eq!(
            TrySendError::Disconnected(0u64).to_string(),
            "channel disconnected"
        );
    }

    #[test]
    fn try_recv_error_display() {
        assert_eq!(TryRecvError::Empty.to_string(), "channel empty");
        assert_eq!(
            TryRecvError::Disconnected.to_string(),
            "channel disconnected"
        );
    }

    #[test]
    fn recv_timeout_error_display() {
        assert_eq!(RecvTimeoutError::Timeout.to_string(), "timed out");
        assert_eq!(
            RecvTimeoutError::Disconnected.to_string(),
            "channel disconnected"
        );
    }
}
