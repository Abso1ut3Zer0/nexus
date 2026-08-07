//! Bounded cross-thread SPSC channel.
//!
//! `Sender`: `Send` (not Clone). `Receiver`: `Send`.
//! Uses `nexus_queue::spsc` for the data path (lock-free, cache-line padded).
//! Zero allocation on the send/recv hot path.
//!
//! Must be created inside [`Runtime::block_on`](crate::Runtime::block_on).
//!
//! ```ignore
//! use nexus_async_rt::channel::spsc;
//!
//! // Inside block_on:
//! let (tx, rx) = spsc::channel::<u64>(64);
//!
//! std::thread::spawn(move || {
//!     tx.try_send(42).unwrap();
//! });
//!
//! let val = rx.recv().await.unwrap();
//! ```

use std::future::Future;
use std::pin::Pin;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::task::{Context, Poll};

use super::{RecvError, SendError, TryRecvError, TrySendError};
use crate::cross_wake::{FallbackWaker, TaskWakerSlot, TxWakerSlot};

// =============================================================================
// Shared state
// =============================================================================

struct Inner<T> {
    producer: nexus_queue::spsc::Producer<T>,
    consumer: nexus_queue::spsc::Consumer<T>,

    rx_slot: TaskWakerSlot,
    rx_fallback: FallbackWaker,
    tx_waker: TxWakerSlot,

    _cross_wake_owner: Arc<crate::cross_wake::CrossWakeContext>,

    /// Sender alive flag.
    tx_alive: AtomicBool,
    /// Receiver alive flag.
    rx_closed: AtomicBool,
}

// SAFETY: All cross-thread fields use atomics (tx_alive, rx_closed) or
// are designed for cross-thread use (TaskWakerSlot, FallbackWaker, TxWakerSlot).
// Producer and Consumer from nexus_queue::spsc are Send.
unsafe impl<T: Send> Send for Inner<T> {}
// SAFETY: Queue<T> owns the data; raw pointers are not shared across threads unsafely.
unsafe impl<T: Send> Sync for Inner<T> {}

impl<T> Inner<T> {
    fn wake_rx(&self) {
        if !self.rx_slot.wake() {
            self.rx_fallback.wake();
        }
    }

    fn has_rx_waker(&self) -> bool {
        self.rx_slot.has_waker() || self.rx_fallback.has_waker()
    }
}

// =============================================================================
// channel()
// =============================================================================

/// Create a bounded cross-thread SPSC channel.
///
/// `capacity` is rounded up to the next power of two.
///
/// # Panics
///
/// - Panics if called outside [`Runtime::block_on`](crate::Runtime::block_on).
/// - Panics if `capacity` is 0.
pub fn channel<T: Send>(capacity: usize) -> (Sender<T>, Receiver<T>) {
    crate::context::assert_in_runtime("spsc::channel() called outside Runtime::block_on");

    assert!(capacity > 0, "channel capacity must be > 0");

    let cross_ctx = crate::cross_wake::cross_wake_context()
        .expect("spsc::channel() requires runtime context for cross-thread wake");

    let (producer, consumer) = nexus_queue::spsc::ring_buffer(capacity);

    let rx_slot = TaskWakerSlot::new(Arc::as_ptr(&cross_ctx));

    let inner = Arc::new(Inner {
        producer,
        consumer,
        rx_slot,
        rx_fallback: FallbackWaker::new(),
        tx_waker: TxWakerSlot::new(),
        _cross_wake_owner: cross_ctx,
        tx_alive: AtomicBool::new(true),
        rx_closed: AtomicBool::new(false),
    });

    let tx = Sender {
        inner: inner.clone(),
    };
    let rx = Receiver { inner };
    (tx, rx)
}

// =============================================================================
// Sender
// =============================================================================

/// Sending half of a bounded SPSC channel.
///
/// `Send` but not `Clone` — single producer.
pub struct Sender<T> {
    inner: Arc<Inner<T>>,
}

impl<T: Send> Sender<T> {
    /// Send a value, waiting if the buffer is full.
    pub fn send(&self, value: T) -> SendFut<'_, T> {
        SendFut {
            sender: self,
            value: Some(value),
        }
    }

    /// Try to send without waiting.
    pub fn try_send(&self, value: T) -> Result<(), TrySendError<T>> {
        if self.inner.rx_closed.load(Ordering::Acquire) {
            return Err(TrySendError::Closed(value));
        }

        match self.inner.producer.push(value) {
            Ok(()) => {
                if self.inner.has_rx_waker() {
                    self.inner.wake_rx();
                }
                Ok(())
            }
            Err(nexus_queue::Full(value)) => Err(TrySendError::Full(value)),
        }
    }
}

impl<T> Drop for Sender<T> {
    fn drop(&mut self) {
        self.inner.tx_alive.store(false, Ordering::Release);
        self.inner.wake_rx();
    }
}

// SAFETY: Sender holds Arc<Inner<T>> where Inner<T>: Send+Sync for T: Send.
// Single-producer semantics enforced by the API (no Clone).
unsafe impl<T: Send> Send for Sender<T> {}

// =============================================================================
// SendFut
// =============================================================================

/// Future returned by [`Sender::send`].
pub struct SendFut<'a, T> {
    sender: &'a Sender<T>,
    value: Option<T>,
}

impl<T: Send> Future for SendFut<'_, T> {
    type Output = Result<(), SendError<T>>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // SAFETY: SendFut has no self-referential fields — unpinning is safe.
        let this = unsafe { self.get_unchecked_mut() };
        let inner = &this.sender.inner;

        if inner.rx_closed.load(Ordering::Acquire) {
            let value = this.value.take().expect("polled after completion");
            return Poll::Ready(Err(SendError(value)));
        }

        let value = this.value.take().expect("polled after completion");
        match inner.producer.push(value) {
            Ok(()) => {
                if inner.has_rx_waker() {
                    inner.wake_rx();
                }
                Poll::Ready(Ok(()))
            }
            Err(nexus_queue::Full(value)) => {
                this.value = Some(value);
                inner.tx_waker.register(cx.waker());
                Poll::Pending
            }
        }
    }
}

// SAFETY: SendFut borrows a Sender (Send) and holds an Option<T> where T: Send.
unsafe impl<T: Send> Send for SendFut<'_, T> {}

// =============================================================================
// Receiver
// =============================================================================

/// Receiving half of a bounded SPSC channel.
///
/// `Send` but not `Clone` — single consumer.
pub struct Receiver<T> {
    inner: Arc<Inner<T>>,
}

impl<T: Send> Receiver<T> {
    /// Receive a value, waiting if the buffer is empty.
    pub fn recv(&self) -> RecvFut<'_, T> {
        RecvFut { receiver: self }
    }

    /// Try to receive without waiting.
    #[allow(clippy::option_if_let_else)]
    pub fn try_recv(&self) -> Result<T, TryRecvError> {
        match self.inner.consumer.pop() {
            Some(value) => {
                if self.inner.tx_waker.has_waker() {
                    self.inner.tx_waker.wake();
                }
                Ok(value)
            }
            None => {
                if self.inner.tx_alive.load(Ordering::Acquire) {
                    Err(TryRecvError::Empty)
                } else {
                    Err(TryRecvError::Closed)
                }
            }
        }
    }
}

impl<T> Drop for Receiver<T> {
    fn drop(&mut self) {
        self.inner.rx_closed.store(true, Ordering::Release);
        self.inner.tx_waker.wake();
    }
}

// SAFETY: Receiver holds Arc<Inner<T>> where Inner<T>: Send+Sync for T: Send.
// Single-consumer semantics enforced by the API (no Clone).
unsafe impl<T: Send> Send for Receiver<T> {}

// =============================================================================
// RecvFut
// =============================================================================

/// Future returned by [`Receiver::recv`].
pub struct RecvFut<'a, T> {
    receiver: &'a Receiver<T>,
}

impl<T> Drop for RecvFut<'_, T> {
    fn drop(&mut self) {
        // Clear the TaskWakerSlot to prevent use-after-free: if a sender on
        // another thread calls wake() after this recv future is dropped,
        // it would read a dangling task pointer. The CAS ensures mutual
        // exclusion with the sender's wake() CAS on the same slot.
        self.receiver.inner.rx_slot.clear();
    }
}

impl<T: Send> Future for RecvFut<'_, T> {
    type Output = Result<T, RecvError>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let inner = &self.receiver.inner;

        if let Some(value) = inner.consumer.pop() {
            if inner.tx_waker.has_waker() {
                inner.tx_waker.wake();
            }
            return Poll::Ready(Ok(value));
        }

        if !inner.tx_alive.load(Ordering::Acquire) {
            return Poll::Ready(Err(RecvError));
        }

        // Park with cross-thread-safe waker.
        if !inner.rx_slot.try_register_local(cx.waker()) {
            inner.rx_fallback.register(cx.waker());
        }

        // Re-check after register to avoid lost wake.
        if let Some(value) = inner.consumer.pop() {
            if inner.tx_waker.has_waker() {
                inner.tx_waker.wake();
            }
            return Poll::Ready(Ok(value));
        }

        if !inner.tx_alive.load(Ordering::Acquire) {
            return Poll::Ready(Err(RecvError));
        }

        Poll::Pending
    }
}

// SAFETY: RecvFut borrows a Receiver (Send). No non-Send fields.
unsafe impl<T: Send> Send for RecvFut<'_, T> {}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn test_channel<T: Send>(capacity: usize) -> (Sender<T>, Receiver<T>) {
        let poll = mio::Poll::new().unwrap();
        let mio_waker = Arc::new(mio::Waker::new(poll.registry(), mio::Token(usize::MAX)).unwrap());
        let cross_ctx = Arc::new(crate::cross_wake::CrossWakeContext {
            queue: crate::cross_wake::CrossWakeQueue::new(),
            mio_waker,
            parked: AtomicBool::new(false),
        });

        let (producer, consumer) = nexus_queue::spsc::ring_buffer(capacity);
        let rx_slot = TaskWakerSlot::new(Arc::as_ptr(&cross_ctx));

        let inner = Arc::new(Inner {
            producer,
            consumer,
            rx_slot,
            rx_fallback: FallbackWaker::new(),
            tx_waker: TxWakerSlot::new(),
            _cross_wake_owner: cross_ctx,
            tx_alive: AtomicBool::new(true),
            rx_closed: AtomicBool::new(false),
        });
        (
            Sender {
                inner: inner.clone(),
            },
            Receiver { inner },
        )
    }

    #[test]
    fn send_recv_single() {
        let (tx, rx) = test_channel::<u32>(4);
        tx.try_send(1).unwrap();
        tx.try_send(2).unwrap();
        tx.try_send(3).unwrap();

        assert_eq!(rx.try_recv().unwrap(), 1);
        assert_eq!(rx.try_recv().unwrap(), 2);
        assert_eq!(rx.try_recv().unwrap(), 3);
        assert_eq!(rx.try_recv(), Err(TryRecvError::Empty));
    }

    #[test]
    fn fifo_ordering() {
        let (tx, rx) = test_channel(8);
        for i in 0..8u32 {
            tx.try_send(i).unwrap();
        }
        for i in 0..8u32 {
            assert_eq!(rx.try_recv().unwrap(), i);
        }
    }

    #[test]
    fn try_send_full() {
        let (tx, rx) = test_channel(2);
        tx.try_send(1u32).unwrap();
        tx.try_send(2).unwrap();

        let err = tx.try_send(3).unwrap_err();
        assert!(err.is_full());
        assert_eq!(err.into_inner(), 3);

        assert_eq!(rx.try_recv().unwrap(), 1);
        tx.try_send(3).unwrap();
    }

    #[test]
    fn try_recv_empty() {
        let (tx, rx) = test_channel::<u32>(4);
        assert_eq!(rx.try_recv(), Err(TryRecvError::Empty));
        tx.try_send(1).unwrap();
        assert_eq!(rx.try_recv().unwrap(), 1);
        assert_eq!(rx.try_recv(), Err(TryRecvError::Empty));
    }

    #[test]
    fn sender_drop_signals_closed() {
        let (tx, rx) = test_channel::<u32>(4);
        tx.try_send(42).unwrap();
        drop(tx);
        assert_eq!(rx.try_recv().unwrap(), 42);
        assert_eq!(rx.try_recv(), Err(TryRecvError::Closed));
    }

    #[test]
    fn receiver_drop_signals_closed() {
        let (tx, rx) = test_channel::<u32>(4);
        drop(rx);
        let err = tx.try_send(1).unwrap_err();
        assert!(err.is_closed());
    }

    #[test]
    fn sender_is_send() {
        fn assert_send<T: Send>() {}
        assert_send::<Sender<u64>>();
    }

    #[test]
    fn receiver_is_send() {
        fn assert_send<T: Send>() {}
        assert_send::<Receiver<u64>>();
    }

    #[test]
    fn cross_thread_try_send() {
        let (tx, rx) = test_channel::<u64>(128);

        let handle = std::thread::spawn(move || {
            for i in 0..100 {
                tx.try_send(i).unwrap();
            }
        });

        handle.join().unwrap();
        for i in 0..100u64 {
            assert_eq!(rx.try_recv().unwrap(), i);
        }
    }

    #[test]
    fn stress_sequential() {
        let (tx, rx) = test_channel(64);
        let n = if cfg!(miri) { 100 } else { 100_000 };
        for i in 0..n {
            tx.try_send(i).unwrap();
            assert_eq!(rx.try_recv().unwrap(), i);
        }
    }

    #[test]
    fn sender_drop_while_receiver_alive() {
        let (tx, rx) = test_channel::<u32>(4);
        tx.try_send(1).unwrap();
        tx.try_send(2).unwrap();
        drop(tx);

        // Buffered values still available.
        assert_eq!(rx.try_recv().unwrap(), 1);
        assert_eq!(rx.try_recv().unwrap(), 2);
        assert_eq!(rx.try_recv(), Err(TryRecvError::Closed));

        // Dropping receiver is clean.
        drop(rx);
    }
}

// =============================================================================
// BUG-2 (#168) — cross-thread wake-path UAF regression tests
// =============================================================================
//
// Tests live in `crate::cross_wake::uaf_scenarios` (one canonical body
// per scenario, shared across all four channels). These per-channel
// `#[test]` wrappers exist for `cargo test spsc::uaf_tests` output
// visibility and to verify the consolidated `TaskWakerSlot` works
// identically across channel modules.
#[cfg(test)]
mod uaf_tests {
    use crate::cross_wake::uaf_scenarios as h;

    #[test]
    fn waker_slot_uaf_when_task_freed_mid_dispatch() {
        h::waker_slot_uaf_when_task_freed_mid_dispatch();
    }

    #[test]
    fn slot_drop_releases_ref_when_still_registered() {
        h::slot_drop_releases_ref_when_still_registered();
    }

    #[test]
    fn register_during_wake_does_not_leak_ref() {
        h::register_during_wake_does_not_leak_ref();
    }
}
