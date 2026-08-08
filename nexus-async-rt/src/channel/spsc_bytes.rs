//! Bounded cross-thread SPSC byte channel.
//!
//! Variable-length messages over `nexus_logbuf::spsc`. Each message is
//! a `&[u8]` written into a claim region and committed. The consumer
//! reads `ReadClaim` references that deref to `&[u8]`.
//!
//! Zero allocation on the send/recv hot path. Must be created inside
//! [`Runtime::block_on`](crate::Runtime::block_on).
//!
//! ```ignore
//! use nexus_async_rt::channel::spsc_bytes;
//!
//! let (mut tx, mut rx) = spsc_bytes::channel(64 * 1024);
//!
//! // Claim, write, commit (zero-copy)
//! let mut claim = tx.claim(5).await?;
//! claim.copy_from_slice(b"hello");
//! claim.commit();
//!
//! // Or convenience: claim + copy + commit
//! tx.send(b"world").await?;
//!
//! // Receive
//! let msg = rx.recv().await?;
//! assert_eq!(&*msg, b"hello");
//! drop(msg);  // advances consumer head
//! ```

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::task::Poll;

use std::ops::{Deref, DerefMut};

use crate::cross_wake::{FallbackWaker, TaskWakerSlot, TxWakerSlot};

// =============================================================================
// Shared state
// =============================================================================

struct Inner {
    rx_slot: TaskWakerSlot,
    rx_fallback: FallbackWaker,
    tx_waker: TxWakerSlot,
    _cross_wake_owner: Arc<crate::cross_wake::CrossWakeContext>,
    tx_alive: AtomicBool,
    rx_closed: AtomicBool,
}

// SAFETY: All fields use atomics or are designed for cross-thread use
// (TaskWakerSlot, FallbackWaker, TxWakerSlot). No raw non-atomic state.
unsafe impl Send for Inner {}
// SAFETY: Queue<T> owns the data; raw pointers are not shared across threads unsafely.
unsafe impl Sync for Inner {}

impl Inner {
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
// Error types
// =============================================================================

// =============================================================================
// WriteClaim wrapper — auto-notifies receiver on commit
// =============================================================================

// =============================================================================
// ReadClaim wrapper — auto-wakes sender on drop (frees space)
// =============================================================================

/// A received message from the byte channel. Dereferences to `&[u8]`.
///
/// When dropped, the record region is freed (consumer head advances)
/// and the sender is woken if it was parked on a full buffer.
pub struct ReadClaim<'a> {
    inner: nexus_logbuf::queue::spsc::ReadClaim<'a>,
    notify: &'a Inner,
}

impl ReadClaim<'_> {
    /// Payload length in bytes.
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Always false.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }
}

impl Deref for ReadClaim<'_> {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        &self.inner
    }
}

impl Drop for ReadClaim<'_> {
    fn drop(&mut self) {
        // The inner ReadClaim drops after this impl runs (field drop order),
        // which advances the consumer head and frees space. We wake the
        // sender BEFORE inner drops — the sender will re-try and see space
        // once inner's drop completes. This ordering is acceptable because
        // the sender's try_claim will simply fail and re-park if the space
        // isn't freed yet. On the next poll it succeeds.
        //
        // Alternatively we could manually drop inner first, but the
        // timing difference is one poll cycle at worst.
        if self.notify.tx_waker.has_waker() {
            self.notify.tx_waker.wake();
        }
    }
}

// =============================================================================
// WriteClaim wrapper — auto-notifies receiver on commit
// =============================================================================

/// A claimed write region in the byte channel. Dereferences to `&mut [u8]`.
///
/// Call [`.commit()`](WriteClaim::commit) to publish the record and
/// wake the receiver. Dropping without commit writes a skip marker (abort).
pub struct WriteClaim<'a> {
    inner: nexus_logbuf::queue::spsc::WriteClaim<'a>,
    notify: &'a Inner,
}

impl WriteClaim<'_> {
    /// Commit the record, making it visible to the receiver.
    /// Automatically wakes the receiver if it's parked.
    pub fn commit(self) {
        let notify = self.notify;
        self.inner.commit();
        if notify.has_rx_waker() {
            notify.wake_rx();
        }
    }

    /// Payload length in bytes.
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Always false (claims must have len > 0).
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }
}

impl Deref for WriteClaim<'_> {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        &self.inner
    }
}

impl DerefMut for WriteClaim<'_> {
    fn deref_mut(&mut self) -> &mut [u8] {
        &mut self.inner
    }
}

// =============================================================================
// Error types
// =============================================================================

/// Claim failed.
///
/// `len == 0` is not a runtime error — it's a precondition violation and
/// panics in [`nexus_logbuf::queue::spsc::Producer::try_claim`].
#[derive(Debug)]
#[non_exhaustive]
pub enum ClaimError {
    /// Receiver was dropped.
    Closed,
    /// Requested length exceeds buffer capacity (can never succeed).
    TooLarge,
}

impl std::fmt::Display for ClaimError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Closed => f.write_str("byte channel closed"),
            Self::TooLarge => f.write_str("message exceeds buffer capacity"),
        }
    }
}

impl std::error::Error for ClaimError {}

/// Receive failed — sender dropped and buffer empty.
#[derive(Debug)]
pub struct RecvError;

impl std::fmt::Display for RecvError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("byte channel closed")
    }
}

impl std::error::Error for RecvError {}

// =============================================================================
// channel()
// =============================================================================

/// Create a bounded cross-thread SPSC byte channel.
///
/// `capacity` is the ring buffer size in bytes.
///
/// # Panics
///
/// - Panics if called outside [`Runtime::block_on`](crate::Runtime::block_on).
pub fn channel(capacity: usize) -> (Sender, Receiver) {
    crate::context::assert_in_runtime("spsc_bytes::channel() called outside Runtime::block_on");

    let cross_ctx = crate::cross_wake::cross_wake_context()
        .expect("spsc_bytes::channel() requires runtime context");

    let (producer, consumer) = nexus_logbuf::queue::spsc::new(capacity);
    let rx_slot = TaskWakerSlot::new(Arc::as_ptr(&cross_ctx));

    let inner = Arc::new(Inner {
        rx_slot,
        rx_fallback: FallbackWaker::new(),
        tx_waker: TxWakerSlot::new(),
        _cross_wake_owner: cross_ctx,
        tx_alive: AtomicBool::new(true),
        rx_closed: AtomicBool::new(false),
    });

    (
        Sender {
            producer,
            inner: inner.clone(),
        },
        Receiver { consumer, inner },
    )
}

// =============================================================================
// Sender
// =============================================================================

/// Sending half of a bounded SPSC byte channel.
///
/// `Send` but not `Clone` — single producer.
pub struct Sender {
    producer: nexus_logbuf::queue::spsc::Producer,
    inner: Arc<Inner>,
}

impl Sender {
    /// Send a complete byte message. Claims space, copies, commits.
    ///
    /// Waits if the buffer is full. Returns `Err` if receiver dropped.
    /// Claim `len` bytes for zero-copy writing.
    ///
    /// Waits if the buffer is full. Write into the returned `WriteClaim`,
    /// then call `.commit()` to publish. Drop without commit writes a
    /// skip marker (abort).
    ///
    /// Returns `Err(ClaimError::TooLarge)` immediately if `len` exceeds
    /// the buffer capacity (can never succeed).
    ///
    /// # Panics
    ///
    /// Polling the returned future with `len == 0` panics (see
    /// [`nexus_logbuf::queue::spsc::Producer::try_claim`]).
    pub fn claim(&mut self, len: usize) -> ClaimFut<'_> {
        ClaimFut { sender: self, len }
    }

    /// Try to claim without waiting.
    ///
    /// # Panics
    ///
    /// Panics if `len == 0` (see
    /// [`nexus_logbuf::queue::spsc::Producer::try_claim`]).
    pub fn try_claim(&mut self, len: usize) -> Result<WriteClaim<'_>, nexus_logbuf::BufferFull> {
        let inner_claim = self.producer.try_claim(len)?;
        Ok(WriteClaim {
            inner: inner_claim,
            notify: &self.inner,
        })
    }
}

/// Future returned by [`Sender::claim`].
pub struct ClaimFut<'a> {
    sender: &'a mut Sender,
    len: usize,
}

impl<'a> Future for ClaimFut<'a> {
    type Output = Result<WriteClaim<'a>, ClaimError>;

    fn poll(self: std::pin::Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> Poll<Self::Output> {
        // SAFETY: ClaimFut has no self-referential fields — unpinning is safe.
        let this = unsafe { &mut *std::pin::Pin::into_inner_unchecked(self) };
        // SAFETY: Extend the reborrow lifetime to 'a. This is sound because:
        // - ClaimFut holds &'a mut Sender, so the Sender lives for 'a
        // - WriteClaim borrows &mut Producer from that Sender
        // - The future won't be polled again after returning Ready
        let sender: &'a mut Sender = unsafe { &mut *(this.sender as *mut Sender) };

        // Precondition check before any state inspection — `len == 0` is a
        // contract violation regardless of channel state, and the doc
        // contract is honest only if it panics unconditionally.
        assert!(this.len > 0, "payload length must be non-zero");

        if sender.inner.rx_closed.load(Ordering::Acquire) {
            return Poll::Ready(Err(ClaimError::Closed));
        }

        if this.len > sender.producer.capacity() {
            return Poll::Ready(Err(ClaimError::TooLarge));
        }

        if let Ok(inner_claim) = sender.producer.try_claim(this.len) {
            return Poll::Ready(Ok(WriteClaim {
                inner: inner_claim,
                notify: &sender.inner,
            }));
        }
        // BufferFull — park and wake on receiver progress.
        sender.inner.tx_waker.register(cx.waker());
        Poll::Pending
    }
}

// SAFETY: ClaimFut borrows a Sender (Send) and holds a usize. All Send-safe.
unsafe impl Send for ClaimFut<'_> {}

impl Drop for Sender {
    fn drop(&mut self) {
        self.inner.tx_alive.store(false, Ordering::Release);
        self.inner.wake_rx();
    }
}

// SAFETY: Sender holds a Producer (Send) and Arc<Inner> (Send+Sync).
unsafe impl Send for Sender {}

// =============================================================================
// Receiver
// =============================================================================

/// Receiving half of a bounded SPSC byte channel.
///
/// `Send` but not `Clone` — single consumer.
pub struct Receiver {
    consumer: nexus_logbuf::queue::spsc::Consumer,
    inner: Arc<Inner>,
}

impl Receiver {
    /// Receive the next message. Returns a `ReadClaim` that derefs to `&[u8]`.
    ///
    /// Dropping the claim advances the consumer head and wakes the sender
    /// if it was blocked on a full buffer.
    pub fn recv(&mut self) -> RecvFut<'_> {
        RecvFut { receiver: self }
    }

    /// Try to receive without waiting.
    pub fn try_recv(&mut self) -> Option<ReadClaim<'_>> {
        let inner_claim = self.consumer.try_claim()?;
        Some(ReadClaim {
            inner: inner_claim,
            notify: &self.inner,
        })
    }
}

/// Future returned by [`Receiver::recv`].
pub struct RecvFut<'a> {
    receiver: &'a mut Receiver,
}

impl Drop for RecvFut<'_> {
    fn drop(&mut self) {
        self.receiver.inner.rx_slot.clear();
    }
}

impl<'a> Future for RecvFut<'a> {
    type Output = Result<ReadClaim<'a>, RecvError>;

    fn poll(self: std::pin::Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> Poll<Self::Output> {
        // SAFETY: RecvFut is not Unpin-sensitive. We need &mut access to
        // receiver.consumer for try_claim, and the returned ReadClaim must
        // have lifetime 'a (tied to the Receiver, not this poll call).
        let this = unsafe { &mut *std::pin::Pin::into_inner_unchecked(self) };

        // SAFETY: Extend the reborrow lifetime to 'a. This is sound because:
        // - RecvFut holds &'a mut Receiver, so the Receiver lives for 'a
        // - ReadClaim borrows &mut Consumer from that Receiver
        // - The future won't be polled again after returning Ready
        let receiver: &'a mut Receiver = unsafe { &mut *(this.receiver as *mut Receiver) };

        // Try to claim.
        if let Some(inner_claim) = receiver.consumer.try_claim() {
            return Poll::Ready(Ok(ReadClaim {
                inner: inner_claim,
                notify: &receiver.inner,
            }));
        }

        // Empty + sender dropped → closed.
        if !receiver.inner.tx_alive.load(Ordering::Acquire) {
            return Poll::Ready(Err(RecvError));
        }

        // Park.
        if !receiver.inner.rx_slot.try_register_local(cx.waker()) {
            receiver.inner.rx_fallback.register(cx.waker());
        }

        Poll::Pending
    }
}

// SAFETY: RecvFut borrows a Receiver (Send). No non-Send fields.
unsafe impl Send for RecvFut<'_> {}

impl Drop for Receiver {
    fn drop(&mut self) {
        self.inner.rx_closed.store(true, Ordering::Release);
        self.inner.tx_waker.wake();
    }
}

// SAFETY: Receiver holds a Consumer (Send) and Arc<Inner> (Send+Sync).
unsafe impl Send for Receiver {}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn test_channel(capacity: usize) -> (Sender, Receiver) {
        let poll = mio::Poll::new().unwrap();
        let mio_waker = Arc::new(mio::Waker::new(poll.registry(), mio::Token(usize::MAX)).unwrap());
        let cross_ctx = Arc::new(crate::cross_wake::CrossWakeContext {
            queue: crate::cross_wake::CrossWakeQueue::new(),
            mio_waker,
            parked: AtomicBool::new(false),
        });

        let (producer, consumer) = nexus_logbuf::queue::spsc::new(capacity);
        let rx_slot = TaskWakerSlot::new(Arc::as_ptr(&cross_ctx));

        let inner = Arc::new(Inner {
            rx_slot,
            rx_fallback: FallbackWaker::new(),
            tx_waker: TxWakerSlot::new(),
            _cross_wake_owner: cross_ctx,
            tx_alive: AtomicBool::new(true),
            rx_closed: AtomicBool::new(false),
        });

        (
            Sender {
                producer,
                inner: inner.clone(),
            },
            Receiver { consumer, inner },
        )
    }

    fn try_send(tx: &mut Sender, data: &[u8]) {
        let mut claim = tx.try_claim(data.len()).unwrap();
        claim.copy_from_slice(data);
        claim.commit(); // auto-notifies receiver
    }

    #[test]
    fn claim_commit_recv() {
        let (mut tx, mut rx) = test_channel(4096);
        try_send(&mut tx, b"hello");
        try_send(&mut tx, b"world");

        let msg = rx.try_recv().unwrap();
        assert_eq!(&*msg, b"hello");
        drop(msg);

        let msg = rx.try_recv().unwrap();
        assert_eq!(&*msg, b"world");
        drop(msg);

        assert!(rx.try_recv().is_none());
    }

    #[test]
    fn fifo_ordering() {
        let (mut tx, mut rx) = test_channel(4096);
        for i in 0u32..10 {
            try_send(&mut tx, &i.to_le_bytes());
        }
        for i in 0u32..10 {
            let msg = rx.try_recv().unwrap();
            assert_eq!(&*msg, &i.to_le_bytes());
        }
    }

    #[test]
    fn sender_drop_signals_closed() {
        let (mut tx, mut rx) = test_channel(4096);
        try_send(&mut tx, b"last");
        drop(tx);

        let msg = rx.try_recv().unwrap();
        assert_eq!(&*msg, b"last");
        drop(msg);

        assert!(rx.try_recv().is_none());
    }

    #[test]
    fn variable_length_messages() {
        let (mut tx, mut rx) = test_channel(8192);

        try_send(&mut tx, b"hi");
        try_send(&mut tx, &[0xABu8; 100]);
        try_send(&mut tx, &vec![0xCDu8; 1000]);

        let msg = rx.try_recv().unwrap();
        assert_eq!(msg.len(), 2);
        drop(msg);

        let msg = rx.try_recv().unwrap();
        assert_eq!(msg.len(), 100);
        drop(msg);

        let msg = rx.try_recv().unwrap();
        assert_eq!(msg.len(), 1000);
    }

    #[test]
    fn cross_thread_claim_send() {
        let (mut tx, mut rx) = test_channel(64 * 1024);

        let handle = std::thread::spawn(move || {
            for i in 0u64..100 {
                try_send(&mut tx, &i.to_le_bytes());
            }
        });

        handle.join().unwrap();

        for i in 0u64..100 {
            let msg = rx.try_recv().unwrap();
            assert_eq!(&*msg, &i.to_le_bytes());
        }
    }

    #[test]
    fn stress_sequential() {
        let (mut tx, mut rx) = test_channel(4096);
        let data = [0xFFu8; 32];

        let n = if cfg!(miri) { 100 } else { 10_000 };
        for _ in 0..n {
            try_send(&mut tx, &data);
            let msg = rx.try_recv().unwrap();
            assert_eq!(msg.len(), 32);
        }
    }

    #[test]
    fn receiver_drop_signals_sender() {
        let (tx, rx) = test_channel(4096);
        drop(rx);
        assert!(tx.inner.rx_closed.load(Ordering::Acquire));
    }

    #[test]
    fn claim_without_commit_aborts() {
        let (mut tx, mut rx) = test_channel(4096);

        // Claim and drop without commit — skip marker.
        let claim = tx.try_claim(10).unwrap();
        drop(claim);

        // Next claim + commit should work.
        try_send(&mut tx, b"after_abort");

        let msg = rx.try_recv().unwrap();
        assert_eq!(&*msg, b"after_abort");
    }
}

// =============================================================================
// BUG-2 (#168) — cross-thread wake-path UAF regression tests
// =============================================================================
//
// Tests live in `crate::cross_wake::uaf_scenarios` (one canonical body
// per scenario, shared across all four channels). These per-channel
// `#[test]` wrappers exist for `cargo test spsc_bytes::uaf_tests`
// output visibility and to verify the consolidated `TaskWakerSlot`
// works identically across channel modules.
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
