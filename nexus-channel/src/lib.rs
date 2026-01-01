//! A high-performance bounded SPSC channel with blocking semantics.
//!
//! This channel wraps [`nexus_queue`]'s lock-free ring buffer and adds
//! blocking send/recv operations with an optimized parking strategy that
//! minimizes syscall overhead.
//!
//! # Performance
//!
//! Benchmarked against `crossbeam-channel` (bounded) on Intel Core Ultra 7 155H
//! @ 2.7GHz base, pinned to physical cores 0,2 with turbo disabled:
//!
//! | Metric | nexus-channel | crossbeam-channel | Improvement |
//! |--------|---------------|-------------------|-------------|
//! | p50 latency | 665 cycles (247 ns) | 1344 cycles (499 ns) | **2.0x faster** |
//! | p99 latency | 1360 cycles (505 ns) | 1708 cycles (634 ns) | **1.3x faster** |
//! | p999 latency | 2501 cycles (928 ns) | 37023 cycles (13.7 µs) | **14.8x faster** |
//! | Throughput | 64 M msgs/sec | 34 M msgs/sec | **1.9x faster** |
//!
//! # Why It's Fast
//!
//! ## 1. Conditional Parking
//!
//! The key insight: syscalls are expensive (~1000+ cycles), so avoid them.
//!
//! ```text
//! Traditional channel (crossbeam):
//! ┌─────────────────────────────────────────────────────────┐
//! │ send() -> push -> unpark() -> SYSCALL (every time!)     │
//! │ recv() -> pop empty -> park() -> SYSCALL                │
//! └─────────────────────────────────────────────────────────┘
//!
//! nexus-channel:
//! ┌─────────────────────────────────────────────────────────┐
//! │ send() -> push -> if (receiver_parked) unpark()         │
//! │ recv() -> pop empty -> spin -> snooze -> park()         │
//! └─────────────────────────────────────────────────────────┘
//!    Only syscall when receiver is ACTUALLY sleeping
//! ```
//!
//! ## 2. Three-Phase Backoff
//!
//! Before committing to an expensive park syscall, we try cheaper options:
//!
//! ```text
//! Phase 1: Fast path
//! ├── Try operation immediately
//! ├── Cost: ~10-50 cycles
//! └── Succeeds when data is already available
//!
//! Phase 2: Backoff (spin + yield)
//! ├── Use crossbeam's Backoff::snooze()
//! ├── Cost: ~100-1000 cycles per iteration
//! ├── Configurable iterations (default: 8)
//! └── Catches data arriving "soon"
//!
//! Phase 3: Park (syscall)
//! ├── Actually sleep via futex/os primitive
//! ├── Cost: ~1000-10000+ cycles
//! └── Only when data is truly not coming
//! ```
//!
//! ## 3. Cache-Padded Parking Flags
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────┐
//! │ Cache Line 0: sender_parked (AtomicBool + 63 bytes pad) │
//! ├─────────────────────────────────────────────────────────┤
//! │ Cache Line 1: receiver_parked (AtomicBool + 63 bytes)   │
//! └─────────────────────────────────────────────────────────┘
//!    No false sharing between sender checking receiver_parked
//!    and receiver checking sender_parked
//! ```
//!
//! ## 4. Lock-Free Underlying Queue
//!
//! The actual data transfer uses `nexus_queue`'s per-slot lap counter design,
//! which achieves ~250 cycle one-way latency for the raw queue operations.
//! See [`nexus_queue`] documentation for details.
//!
//! # The p999 Win Explained
//!
//! The 14.8x improvement at p999 (928 ns vs 13.7 µs) comes from syscall
//! avoidance. In high-throughput scenarios:
//!
//! ```text
//! crossbeam: Every send() calls unpark() -> futex syscall
//!            Even if receiver is spinning and will see data immediately
//!
//! nexus:     send() checks receiver_parked flag (just a load)
//!            If receiver is spinning, no syscall needed
//!            Only syscall when receiver actually went to sleep
//! ```
//!
//! Since ping-pong workloads rarely have the receiver actually asleep
//! (data arrives quickly), we almost never hit the syscall path.
//!
//! # Example
//!
//! ```
//! use nexus_channel::channel;
//!
//! let (mut tx, mut rx) = channel::<u64>(1024);
//!
//! // Blocking send - waits if buffer is full
//! tx.send(42).unwrap();
//!
//! // Blocking recv - waits if buffer is empty
//! assert_eq!(rx.recv().unwrap(), 42);
//! ```
//!
//! # Non-blocking Operations
//!
//! ```
//! use nexus_channel::{channel, TrySendError, TryRecvError};
//!
//! let (mut tx, mut rx) = channel::<u64>(2);
//!
//! // try_send returns immediately
//! tx.try_send(1).unwrap();
//! tx.try_send(2).unwrap();
//! assert!(matches!(tx.try_send(3), Err(TrySendError::Full(3))));
//!
//! // try_recv returns immediately
//! assert_eq!(rx.try_recv().unwrap(), 1);
//! assert_eq!(rx.try_recv().unwrap(), 2);
//! assert!(matches!(rx.try_recv(), Err(TryRecvError::Empty)));
//! ```
//!
//! # Disconnection
//!
//! When either end is dropped, the channel becomes disconnected:
//!
//! ```
//! use nexus_channel::{channel, RecvError};
//!
//! let (mut tx, mut rx) = channel::<u64>(4);
//!
//! tx.send(1).unwrap();
//! tx.send(2).unwrap();
//! drop(tx); // Disconnect
//!
//! // Can still receive buffered messages
//! assert_eq!(rx.recv().unwrap(), 1);
//! assert_eq!(rx.recv().unwrap(), 2);
//!
//! // Then get disconnection error
//! assert!(rx.recv().is_err());
//! ```
//!
//! # Tuning the Backoff
//!
//! The default backoff uses 8 snooze iterations before parking. For different
//! workloads, you can tune this:
//!
//! ```
//! use nexus_channel::channel_with_config;
//!
//! // More spinning for ultra-low-latency (burns more CPU)
//! let (tx, rx) = channel_with_config::<u64>(1024, 32);
//!
//! // Less spinning for power efficiency
//! let (tx, rx) = channel_with_config::<u64>(1024, 2);
//! ```
//!
//! # Memory Ordering
//!
//! The parking flags use `SeqCst` ordering to ensure correctness:
//!
//! ```text
//! Receiver:                        Sender:
//! ─────────────────────            ─────────────────────
//! store(receiver_parked, true)
//! [SeqCst barrier]                 push(data)
//! pop() -> empty                   [SeqCst barrier]
//! park()                           load(receiver_parked) -> true
//!                                  unpark()
//! ```
//!
//! The `SeqCst` creates a total order that prevents the race where:
//! 1. Sender pushes data
//! 2. Sender loads `receiver_parked` (sees false)
//! 3. Receiver stores `receiver_parked = true`
//! 4. Receiver pops (sees empty - data not visible yet!)
//! 5. Receiver parks forever
//!
//! # When to Use This
//!
//! Use `nexus_channel` when:
//! - You have exactly one sender and one receiver
//! - You need blocking semantics (send waits when full, recv waits when empty)
//! - You want the lowest possible latency for a blocking channel
//! - Tail latency matters (p999, p9999)
//!
//! Consider alternatives when:
//! - Multiple senders → use `crossbeam-channel` or `flume`
//! - Multiple receivers → use `crossbeam-channel` or `flume`
//! - You need `select!` macro support → use `crossbeam-channel`
//! - You don't need blocking → use `nexus_queue` directly
//! - You need async/await → use `tokio::sync::mpsc`
//!
//! # Benchmarking
//!
//! Latency benchmarks use ping-pong between two threads pinned to separate
//! physical cores (avoiding hyperthreading). We measure round-trip time with
//! `rdtscp` and divide by 2 for one-way latency.
//!
//! ```bash
//! echo 1 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo
//! sudo taskset -c 0,2 ./target/release/deps/profile_channel-*
//! ```

use core::fmt;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

use crossbeam_utils::sync::{Parker, Unparker};
use crossbeam_utils::{Backoff, CachePadded};
use nexus_queue::{Consumer, Full, Producer, ring_buffer};

/// Default number of backoff snooze iterations before parking.
///
/// Each snooze uses `crossbeam_utils::Backoff::snooze()` which starts with
/// spinning and eventually yields to the OS scheduler.
const DEFAULT_SNOOZE_ITERS: usize = 8;

/// Shared state between sender and receiver.
///
/// The parking flags are cache-padded to prevent false sharing when
/// sender checks `receiver_parked` while receiver checks `sender_parked`.
struct Shared {
    sender_parked: CachePadded<AtomicBool>,
    receiver_parked: CachePadded<AtomicBool>,
}

/// The sending half of a channel.
///
/// Messages can be sent through this channel with [`send`](Sender::send) or
/// [`try_send`](Sender::try_send).
///
/// The sender takes `&mut self` to statically ensure single-producer access.
/// This eliminates the need for atomic operations on the send path beyond
/// what's required for the underlying queue.
///
/// # Example
///
/// ```
/// use nexus_channel::channel;
///
/// let (mut tx, mut rx) = channel::<i32>(10);
///
/// tx.send(1).unwrap();
/// tx.send(2).unwrap();
///
/// assert_eq!(rx.recv().unwrap(), 1);
/// assert_eq!(rx.recv().unwrap(), 2);
/// ```
pub struct Sender<T> {
    producer: Producer<T>,
    shared: Arc<Shared>,
    parker: Parker,
    receiver_unparker: Unparker,
    snooze_iters: usize,
}

/// The receiving half of a channel.
///
/// Messages can be received through this channel with [`recv`](Receiver::recv)
/// or [`try_recv`](Receiver::try_recv).
///
/// The receiver takes `&mut self` to statically ensure single-consumer access.
///
/// # Example
///
/// ```
/// use nexus_channel::channel;
/// use std::thread;
///
/// let (mut tx, mut rx) = channel::<i32>(10);
///
/// thread::spawn(move || {
///     tx.send(42).unwrap();
/// });
///
/// assert_eq!(rx.recv().unwrap(), 42);
/// ```
pub struct Receiver<T> {
    consumer: Consumer<T>,
    shared: Arc<Shared>,
    parker: Parker,
    sender_unparker: Unparker,
    snooze_iters: usize,
}

/// Creates a bounded SPSC channel with the given capacity.
///
/// Returns a `(Sender, Receiver)` pair. The actual capacity will be rounded
/// up to the next power of two.
///
/// Uses default backoff settings (8 snooze iterations before parking).
/// For custom backoff tuning, use [`channel_with_config`].
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
/// let (mut tx, mut rx) = channel::<String>(100);
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
///
/// # Example
///
/// ```
/// use nexus_channel::channel_with_config;
///
/// // More aggressive spinning for lower latency
/// let (mut tx, mut rx) = channel_with_config::<u64>(1024, 32);
/// ```
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
            producer,
            shared: Arc::clone(&shared),
            parker: sender_parker,
            receiver_unparker,
            snooze_iters,
        },
        Receiver {
            consumer,
            shared,
            parker: receiver_parker,
            sender_unparker,
            snooze_iters,
        },
    )
}

impl<T> Sender<T> {
    /// Sends a message into the channel, blocking if necessary.
    ///
    /// If the channel is full, this method will:
    /// 1. Spin briefly (fast path)
    /// 2. Use exponential backoff with yields
    /// 3. Park the thread until space is available
    ///
    /// Returns `Err(SendError(value))` if the receiver has been dropped.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_channel::channel;
    ///
    /// let (mut tx, rx) = channel::<i32>(2);
    ///
    /// tx.send(1).unwrap();
    /// tx.send(2).unwrap();
    /// // tx.send(3) would block here until rx.recv() is called
    ///
    /// drop(rx);
    /// assert!(tx.send(3).is_err()); // Disconnected
    /// ```
    pub fn send(&mut self, value: T) -> Result<(), SendError<T>> {
        // Check disconnection first
        if self.producer.is_disconnected() {
            return Err(SendError(value));
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
                return Err(SendError(val));
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

            // Check after signaling - prevents missed wakeup race
            if self.producer.is_disconnected() {
                self.shared.sender_parked.store(false, Ordering::Relaxed);
                return Err(SendError(val));
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
                return Err(SendError(val));
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
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_channel::{channel, TrySendError};
    ///
    /// let (mut tx, rx) = channel::<i32>(1);
    ///
    /// assert!(tx.try_send(1).is_ok());
    /// assert!(matches!(tx.try_send(2), Err(TrySendError::Full(2))));
    ///
    /// drop(rx);
    /// assert!(matches!(tx.try_send(3), Err(TrySendError::Disconnected(3))));
    /// ```
    pub fn try_send(&mut self, value: T) -> Result<(), TrySendError<T>> {
        // Check disconnection first
        if self.producer.is_disconnected() {
            return Err(TrySendError::Disconnected(value));
        }

        match self.producer.push(value) {
            Ok(()) => {
                self.notify_receiver();
                Ok(())
            }
            Err(Full(v)) => Err(TrySendError::Full(v)),
        }
    }

    /// Wakes the receiver if it's parked.
    ///
    /// This is the key optimization: we only issue an expensive unpark syscall
    /// when the receiver has actually gone to sleep. If the receiver is spinning
    /// or processing, this is just an atomic load.
    #[inline]
    fn notify_receiver(&self) {
        if self.shared.receiver_parked.load(Ordering::SeqCst) {
            self.receiver_unparker.unpark();
        }
    }

    /// Returns `true` if the receiver has been dropped.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_channel::channel;
    ///
    /// let (tx, rx) = channel::<i32>(4);
    /// assert!(!tx.is_disconnected());
    ///
    /// drop(rx);
    /// assert!(tx.is_disconnected());
    /// ```
    #[inline]
    pub fn is_disconnected(&self) -> bool {
        self.producer.is_disconnected()
    }

    /// Returns the capacity of the channel.
    ///
    /// This is the maximum number of messages that can be buffered.
    /// Note: The actual capacity is rounded up to a power of two.
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

impl<T> Receiver<T> {
    /// Receives a message from the channel, blocking if necessary.
    ///
    /// If the channel is empty, this method will:
    /// 1. Check immediately (fast path)
    /// 2. Use exponential backoff with yields
    /// 3. Park the thread until a message arrives
    ///
    /// Returns `Err(RecvError)` if the sender has been dropped and
    /// no messages remain in the channel.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_channel::channel;
    /// use std::thread;
    ///
    /// let (mut tx, mut rx) = channel::<i32>(4);
    ///
    /// thread::spawn(move || {
    ///     tx.send(42).unwrap();
    /// });
    ///
    /// assert_eq!(rx.recv().unwrap(), 42);
    /// ```
    pub fn recv(&mut self) -> Result<T, RecvError> {
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

            // Check after signaling - prevents missed wakeup race
            if let Some(v) = self.consumer.pop() {
                self.shared.receiver_parked.store(false, Ordering::Relaxed);
                self.notify_sender();
                return Ok(v);
            }

            if self.consumer.is_disconnected() {
                self.shared.receiver_parked.store(false, Ordering::Relaxed);
                return Err(RecvError);
            }

            self.parker.park();
            self.shared.receiver_parked.store(false, Ordering::Relaxed);

            // Try again after wake
            if let Some(v) = self.consumer.pop() {
                self.notify_sender();
                return Ok(v);
            }

            if self.consumer.is_disconnected() {
                return Err(RecvError);
            }
        }
    }

    /// Attempts to receive a message without blocking.
    ///
    /// Returns immediately with:
    /// - `Ok(value)` if a message was available
    /// - `Err(TryRecvError::Empty)` if the channel is empty
    /// - `Err(TryRecvError::Disconnected)` if the sender was dropped and channel is empty
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_channel::{channel, TryRecvError};
    ///
    /// let (mut tx, mut rx) = channel::<i32>(4);
    ///
    /// assert!(matches!(rx.try_recv(), Err(TryRecvError::Empty)));
    ///
    /// tx.send(1).unwrap();
    /// assert_eq!(rx.try_recv().unwrap(), 1);
    ///
    /// drop(tx);
    /// assert!(matches!(rx.try_recv(), Err(TryRecvError::Disconnected)));
    /// ```
    pub fn try_recv(&mut self) -> Result<T, TryRecvError> {
        match self.consumer.pop() {
            Some(v) => {
                self.notify_sender();
                Ok(v)
            }
            None => {
                if self.consumer.is_disconnected() {
                    Err(TryRecvError::Disconnected)
                } else {
                    Err(TryRecvError::Empty)
                }
            }
        }
    }

    /// Wakes the sender if it's parked.
    ///
    /// Called after receiving a message to unblock a sender that
    /// may be waiting for space in the buffer.
    #[inline]
    fn notify_sender(&self) {
        if self.shared.sender_parked.load(Ordering::SeqCst) {
            self.sender_unparker.unpark();
        }
    }

    /// Returns `true` if the sender has been dropped.
    ///
    /// Note: Even if disconnected, there may still be messages in the buffer
    /// that can be received.
    ///
    /// # Example
    ///
    /// ```
    /// use nexus_channel::channel;
    ///
    /// let (tx, rx) = channel::<i32>(4);
    /// assert!(!rx.is_disconnected());
    ///
    /// drop(tx);
    /// assert!(rx.is_disconnected());
    /// ```
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

// ============================================================================
// Error Types
// ============================================================================

/// Error returned when [`Sender::send`] fails due to disconnection.
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

/// Error returned when [`Receiver::recv`] fails due to disconnection.
///
/// This error occurs when the sender has been dropped and no messages
/// remain in the channel.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RecvError;

impl fmt::Display for RecvError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "channel disconnected")
    }
}

impl std::error::Error for RecvError {}

/// Error returned by [`Sender::try_send`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TrySendError<T> {
    /// The channel is full but still connected.
    ///
    /// The message is returned so it can be retried or handled.
    Full(T),

    /// The receiver has been dropped.
    ///
    /// The message is returned for cleanup.
    Disconnected(T),
}

impl<T> TrySendError<T> {
    /// Returns the message that could not be sent.
    pub fn into_inner(self) -> T {
        match self {
            TrySendError::Full(v) => v,
            TrySendError::Disconnected(v) => v,
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

/// Error returned by [`Receiver::try_recv`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TryRecvError {
    /// The channel is empty but still connected.
    ///
    /// A message may arrive later.
    Empty,

    /// The sender has been dropped and no messages remain.
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

// ============================================================================
// Drop Implementations
// ============================================================================

impl<T> Drop for Sender<T> {
    fn drop(&mut self) {
        // Wake receiver so it can see disconnection and return error
        // instead of parking forever.
        self.receiver_unparker.unpark();
    }
}

impl<T> Drop for Receiver<T> {
    fn drop(&mut self) {
        // Wake sender so it can see disconnection and return error
        // instead of parking forever.
        self.sender_unparker.unpark();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::thread;
    use std::time::{Duration, Instant};

    // ============================================================================
    // Basic Operations
    // ============================================================================

    #[test]
    fn basic_send_recv() {
        let (mut tx, mut rx) = channel::<u64>(4);

        tx.send(1).unwrap();
        tx.send(2).unwrap();
        tx.send(3).unwrap();

        assert_eq!(rx.recv().unwrap(), 1);
        assert_eq!(rx.recv().unwrap(), 2);
        assert_eq!(rx.recv().unwrap(), 3);
    }

    #[test]
    fn try_send_try_recv() {
        let (mut tx, mut rx) = channel::<u64>(2);

        assert!(tx.try_send(1).is_ok());
        assert!(tx.try_send(2).is_ok());
        assert!(matches!(tx.try_send(3), Err(TrySendError::Full(3))));

        assert_eq!(rx.try_recv().unwrap(), 1);
        assert_eq!(rx.try_recv().unwrap(), 2);
        assert!(matches!(rx.try_recv(), Err(TryRecvError::Empty)));
    }

    #[test]
    fn send_fills_then_recv_drains() {
        let (mut tx, mut rx) = channel::<u64>(4);

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
    // Disconnection
    // ============================================================================

    #[test]
    fn recv_returns_error_when_sender_dropped() {
        let (tx, mut rx) = channel::<u64>(4);

        drop(tx);

        assert!(rx.recv().is_err());
        assert!(matches!(rx.try_recv(), Err(TryRecvError::Disconnected)));
    }

    #[test]
    fn recv_drains_before_error_when_sender_dropped() {
        let (mut tx, mut rx) = channel::<u64>(4);

        tx.send(1).unwrap();
        tx.send(2).unwrap();
        drop(tx);

        assert_eq!(rx.recv().unwrap(), 1);
        assert_eq!(rx.recv().unwrap(), 2);
        assert!(rx.recv().is_err());
    }

    #[test]
    fn send_returns_error_when_receiver_dropped() {
        let (mut tx, rx) = channel::<u64>(4);

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
        let (mut tx, mut rx) = channel::<u64>(4);

        let handle = thread::spawn(move || rx.recv().unwrap());

        tx.send(42).unwrap();

        assert_eq!(handle.join().unwrap(), 42);
    }

    #[test]
    fn cross_thread_multiple_messages() {
        let (mut tx, mut rx) = channel::<u64>(4);

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
        let (mut tx, mut rx) = channel::<u64>(8);

        for i in 0..8 {
            tx.try_send(i).unwrap();
        }

        for i in 0..8 {
            assert_eq!(rx.recv().unwrap(), i);
        }
    }

    #[test]
    fn fifo_ordering_cross_thread() {
        let (mut tx, mut rx) = channel::<u64>(64);

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
        let (mut tx, mut rx) = channel::<u64>(4);

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
        let (mut tx, mut rx) = channel::<u64>(2);

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
        let (tx, mut rx) = channel::<u64>(4);

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
        let (mut tx, rx) = channel::<u64>(1);

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
        let (mut tx, mut rx) = channel::<u64>(1);

        for i in 0..100 {
            tx.send(i).unwrap();
            assert_eq!(rx.recv().unwrap(), i);
        }
    }

    #[test]
    fn capacity_one_cross_thread() {
        let (mut tx, mut rx) = channel::<u64>(1);

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
    // Stress Tests
    // ============================================================================

    #[test]
    fn stress_high_volume() {
        const COUNT: u64 = 100_000;

        let (mut tx, mut rx) = channel::<u64>(1024);

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

        let (mut tx, mut rx) = channel::<u64>(4);

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

        let (mut tx, mut rx) = channel::<u64>(1);

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
    // Drop Behavior
    // ============================================================================

    #[test]
    fn values_dropped_on_channel_drop() {
        use std::sync::atomic::{AtomicUsize, Ordering};

        static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

        #[derive(Debug)]
        struct DropCounter;
        impl Drop for DropCounter {
            fn drop(&mut self) {
                DROP_COUNT.fetch_add(1, Ordering::SeqCst);
            }
        }

        DROP_COUNT.store(0, Ordering::SeqCst);

        let (mut tx, rx) = channel::<DropCounter>(4);

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
        let (mut tx, rx) = channel::<String>(1);

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
    // Deadlock Prevention
    // ============================================================================

    #[test]
    fn no_deadlock_alternating() {
        let (mut tx, mut rx) = channel::<u64>(1);

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
        let (mut tx, mut rx) = channel::<u64>(8);

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
        let (mut tx, mut rx) = channel::<u64>(2);

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

    // ============================================================================
    // Timeout Simulation (no actual timeout API, just checking it doesn't hang)
    // ============================================================================

    #[test]
    fn does_not_hang_on_disconnect_during_recv() {
        use std::sync::Arc;
        use std::sync::atomic::{AtomicBool, Ordering};

        let done = Arc::new(AtomicBool::new(false));
        let done_clone = done.clone();

        let (tx, mut rx) = channel::<u64>(4);

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
        use std::sync::Arc;
        use std::sync::atomic::{AtomicBool, Ordering};

        let done = Arc::new(AtomicBool::new(false));
        let done_clone = done.clone();

        let (mut tx, rx) = channel::<u64>(1);
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
            let (mut tx, mut rx) = channel::<u64>(4);
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
    // ZST and Large Types
    // ============================================================================

    #[test]
    fn zero_sized_type() {
        let (mut tx, mut rx) = channel::<()>(4);

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

        let (mut tx, mut rx) = channel::<LargeMessage>(4);

        let msg = LargeMessage { data: [42u8; 4096] };
        tx.send(msg.clone()).unwrap();

        let received = rx.recv().unwrap();
        assert_eq!(received.data[0], 42);
        assert_eq!(received.data[4095], 42);
    }

    // ============================================================================
    // Multiple Laps
    // ============================================================================

    #[test]
    fn many_laps_single_thread() {
        let (mut tx, mut rx) = channel::<u64>(4);

        // 1000 messages through 4-slot buffer = 250 laps
        for i in 0..1000 {
            tx.send(i).unwrap();
            assert_eq!(rx.recv().unwrap(), i);
        }
    }

    #[test]
    fn many_laps_cross_thread() {
        const COUNT: u64 = 100_000;

        let (mut tx, mut rx) = channel::<u64>(4); // Small buffer, many laps

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
    // Ping-Pong Stress Tests (exercises park/unpark heavily)
    // ============================================================================

    #[test]
    fn ping_pong_basic() {
        let (mut tx1, mut rx1) = channel::<u64>(1);
        let (mut tx2, mut rx2) = channel::<u64>(1);

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
    fn ping_pong_capacity_one_high_iterations() {
        let (mut tx1, mut rx1) = channel::<u64>(1);
        let (mut tx2, mut rx2) = channel::<u64>(1);

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

    #[test]
    fn ping_pong_both_block() {
        // Both sides will need to park at some point
        let (mut tx1, mut rx1) = channel::<u64>(1);
        let (mut tx2, mut rx2) = channel::<u64>(1);

        let handle = thread::spawn(move || {
            for _ in 0..5000 {
                // Receive blocks until sender sends
                let val = rx1.recv().unwrap();
                // Send blocks until receiver receives
                tx2.send(val + 1).unwrap();
            }
        });

        for i in 0..5000 {
            tx1.send(i).unwrap();
            let val = rx2.recv().unwrap();
            assert_eq!(val, i + 1);
        }

        handle.join().unwrap();
    }

    #[test]
    fn ping_pong_with_varying_delays() {
        let (mut tx1, mut rx1) = channel::<u64>(1);
        let (mut tx2, mut rx2) = channel::<u64>(1);

        let handle = thread::spawn(move || {
            for i in 0..100 {
                let val = rx1.recv().unwrap();
                // Occasional delay to force other side to park
                if i % 20 == 0 {
                    thread::sleep(Duration::from_micros(100));
                }
                tx2.send(val).unwrap();
            }
        });

        for i in 0..100 {
            // Occasional delay to force other side to park
            if i % 17 == 0 {
                thread::sleep(Duration::from_micros(100));
            }
            tx1.send(i).unwrap();
            let val = rx2.recv().unwrap();
            assert_eq!(val, i);
        }

        handle.join().unwrap();
    }

    #[test]
    fn ping_pong_multiple_pairs() {
        // Multiple ping-pong pairs running concurrently
        let mut handles = vec![];

        for _ in 0..4 {
            let (mut tx1, mut rx1) = channel::<u64>(1);
            let (mut tx2, mut rx2) = channel::<u64>(1);

            let h1 = thread::spawn(move || {
                for _ in 0..1000 {
                    let val = rx1.recv().unwrap();
                    tx2.send(val + 1).unwrap();
                }
            });

            let h2 = thread::spawn(move || {
                for i in 0..1000u64 {
                    tx1.send(i).unwrap();
                    let val = rx2.recv().unwrap();
                    assert_eq!(val, i + 1);
                }
            });

            handles.push(h1);
            handles.push(h2);
        }

        for h in handles {
            h.join().unwrap();
        }
    }

    // ============================================================================
    // Deadlock Prevention Tests
    // ============================================================================

    #[test]
    fn no_deadlock_send_recv_interleaved() {
        // Alternating sends and receives shouldn't deadlock
        let (mut tx, mut rx) = channel::<u64>(1);

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
    fn no_deadlock_full_buffer_unblock() {
        // Sender blocks on full, receiver unblocks it
        let (mut tx, mut rx) = channel::<u64>(2);

        // Fill buffer
        tx.try_send(1).unwrap();
        tx.try_send(2).unwrap();

        let handle = thread::spawn(move || {
            thread::sleep(Duration::from_millis(50));
            // Drain to unblock sender
            rx.recv().unwrap();
            rx.recv().unwrap();
            rx.recv().unwrap(); // The one that was blocked
        });

        // This should block then succeed
        tx.send(3).unwrap();

        handle.join().unwrap();
    }

    #[test]
    fn no_deadlock_empty_buffer_unblock() {
        // Receiver blocks on empty, sender unblocks it
        let (mut tx, mut rx) = channel::<u64>(2);

        let handle = thread::spawn(move || {
            thread::sleep(Duration::from_millis(50));
            tx.send(42).unwrap();
        });

        // This should block then succeed
        let val = rx.recv().unwrap();
        assert_eq!(val, 42);

        handle.join().unwrap();
    }

    #[test]
    fn no_deadlock_simultaneous_block() {
        // Both sides trying to do operations that could block
        let (mut tx, mut rx) = channel::<u64>(1);

        let sender = thread::spawn(move || {
            for i in 0..1000 {
                tx.send(i).unwrap();
            }
        });

        let receiver = thread::spawn(move || {
            for _ in 0..1000 {
                rx.recv().unwrap();
            }
        });

        sender.join().unwrap();
        receiver.join().unwrap();
    }

    #[test]
    fn no_deadlock_disconnect_while_blocked_recv() {
        let (tx, mut rx) = channel::<u64>(1);

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
        let (mut tx, rx) = channel::<u64>(1);
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
    // Park/Unpark Race Condition Tests
    // ============================================================================

    #[test]
    fn race_send_before_recv_parks() {
        // Send happens just before recv decides to park
        for _ in 0..100 {
            let (mut tx, mut rx) = channel::<u64>(1);

            let handle = thread::spawn(move || rx.recv().unwrap());

            // Tiny delay to let receiver potentially start parking
            thread::yield_now();
            tx.send(42).unwrap();

            assert_eq!(handle.join().unwrap(), 42);
        }
    }

    #[test]
    fn race_recv_before_send_parks() {
        // Recv happens just before send decides to park on full buffer
        for _ in 0..100 {
            let (mut tx, mut rx) = channel::<u64>(1);
            tx.try_send(1).unwrap(); // Fill it

            let handle = thread::spawn(move || {
                tx.send(2).unwrap();
            });

            // Tiny delay to let sender potentially start parking
            thread::yield_now();
            rx.recv().unwrap(); // Make space

            handle.join().unwrap();
        }
    }

    #[test]
    fn race_disconnect_during_park_transition() {
        // Disconnect happens during the brief window of parking
        for _ in 0..100 {
            let (tx, mut rx) = channel::<u64>(1);

            let handle = thread::spawn(move || {
                let _ = rx.recv(); // May succeed or fail, shouldn't deadlock
            });

            // Immediately disconnect
            drop(tx);

            handle.join().unwrap();
        }
    }

    // ============================================================================
    // Stress: Rapid Park/Unpark Cycles
    // ============================================================================

    #[test]
    fn stress_rapid_park_unpark_sender() {
        let (mut tx, mut rx) = channel::<u64>(1);

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
        let (mut tx, mut rx) = channel::<u64>(1);

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
        let (mut tx, mut rx) = channel::<u64>(1);

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
            let (mut tx, mut rx) = channel::<u64>(1);

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
}
