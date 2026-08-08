//! Bounded local MPSC channel.
//!
//! `!Send`, `!Sync` — single-threaded only. No atomics, no `Arc`.
//! Fixed-capacity power-of-two ring buffer with intrusive waiter list.
//!
//! Must be created inside [`Runtime::block_on`](crate::Runtime::block_on).
//!
//! ```ignore
//! use nexus_async_rt::channel::local;
//!
//! // Inside block_on:
//! let (tx, rx) = local::channel::<u64>(64);
//! tx.send(42).await.unwrap();
//! assert_eq!(rx.recv().await.unwrap(), 42);
//! ```

use std::cell::UnsafeCell;
use std::future::Future;
use std::mem::ManuallyDrop;
use std::pin::Pin;
use std::rc::Rc;
use std::task::{Context, Poll, Waker};

use super::{RecvError, SendError, TryRecvError, TrySendError};

// =============================================================================
// Ring buffer — fixed-capacity, power-of-two, zero-alloc after init
// =============================================================================

struct RingBuffer<T> {
    buf: *mut T,
    mask: usize,
    head: usize,
    tail: usize,
}

impl<T> RingBuffer<T> {
    fn new(capacity: usize) -> Self {
        assert!(capacity > 0, "channel capacity must be > 0");
        let capacity = capacity.next_power_of_two();
        let mask = capacity - 1;

        // Allocate via Vec, take ownership of the raw pointer.
        let slots = ManuallyDrop::new(Vec::<T>::with_capacity(capacity));
        let buf = slots.as_ptr().cast_mut();

        Self {
            buf,
            mask,
            head: 0,
            tail: 0,
        }
    }

    fn capacity(&self) -> usize {
        self.mask + 1
    }

    fn len(&self) -> usize {
        self.tail.wrapping_sub(self.head)
    }

    fn is_empty(&self) -> bool {
        self.head == self.tail
    }

    fn is_full(&self) -> bool {
        self.len() == self.capacity()
    }

    /// Push a value. Caller must check `!is_full()` first.
    ///
    /// # Safety
    ///
    /// Undefined behavior if the buffer is full.
    unsafe fn push(&mut self, value: T) {
        debug_assert!(!self.is_full());
        // SAFETY: index is within allocated capacity; slot is unoccupied.
        unsafe {
            self.buf.add(self.tail & self.mask).write(value);
        }
        self.tail = self.tail.wrapping_add(1);
    }

    /// Pop a value. Caller must check `!is_empty()` first.
    ///
    /// # Safety
    ///
    /// Undefined behavior if the buffer is empty.
    unsafe fn pop(&mut self) -> T {
        debug_assert!(!self.is_empty());
        // SAFETY: index is within allocated capacity; slot is occupied.
        let val = unsafe { self.buf.add(self.head & self.mask).read() };
        self.head = self.head.wrapping_add(1);
        val
    }
}

impl<T> Drop for RingBuffer<T> {
    fn drop(&mut self) {
        // Drop remaining elements.
        while !self.is_empty() {
            // SAFETY: we just checked non-empty; each element is initialized.
            unsafe {
                self.buf.add(self.head & self.mask).drop_in_place();
            }
            self.head = self.head.wrapping_add(1);
        }

        // Deallocate the buffer.
        // SAFETY: buf was allocated by Vec::with_capacity(capacity).
        // We pass len=0 because elements are already dropped above.
        unsafe {
            let capacity = self.mask + 1;
            drop(Vec::from_raw_parts(self.buf, 0, capacity));
        }
    }
}

// =============================================================================
// Intrusive waiter list — zero-allocation sender wait queue
// =============================================================================

struct Waiter {
    waker: Option<Waker>,
    next: *mut Waiter,
    prev: *mut Waiter,
    queued: bool,
}

impl Waiter {
    fn new() -> Self {
        Self {
            waker: None,
            next: std::ptr::null_mut(),
            prev: std::ptr::null_mut(),
            queued: false,
        }
    }
}

struct WaiterList {
    head: *mut Waiter,
    tail: *mut Waiter,
}

impl WaiterList {
    fn new() -> Self {
        Self {
            head: std::ptr::null_mut(),
            tail: std::ptr::null_mut(),
        }
    }

    /// Link a waiter at the tail. The waiter must not already be queued.
    ///
    /// # Safety
    ///
    /// `waiter` must point to a pinned, live `Waiter` that is not in any list.
    unsafe fn push_back(&mut self, waiter: *mut Waiter) {
        // SAFETY: waiter is a valid pointer to a live Waiter; accessed only from the single-threaded executor.
        debug_assert!(unsafe { !(*waiter).queued });
        // SAFETY: waiter is a valid pointer to a live Waiter; accessed only from the single-threaded executor.
        unsafe {
            (*waiter).queued = true;
            (*waiter).next = std::ptr::null_mut();
            (*waiter).prev = self.tail;
        }

        if self.tail.is_null() {
            self.head = waiter;
        } else {
            // SAFETY: self.tail is non-null (checked above) and points to a live Waiter; accessed only from the single-threaded executor.
            unsafe { (*self.tail).next = waiter };
        }
        self.tail = waiter;
    }

    /// Pop the head waiter. Returns null if empty.
    unsafe fn pop_front(&mut self) -> *mut Waiter {
        let waiter = self.head;
        if waiter.is_null() {
            return std::ptr::null_mut();
        }

        // SAFETY: waiter is the head of this list and points to a live Waiter; accessed only from the single-threaded executor.
        self.head = unsafe { (*waiter).next };
        if self.head.is_null() {
            self.tail = std::ptr::null_mut();
        } else {
            // SAFETY: self.head is non-null (checked above) and points to a live Waiter; accessed only from the single-threaded executor.
            unsafe { (*self.head).prev = std::ptr::null_mut() };
        }

        // SAFETY: waiter is a valid pointer to a live Waiter being removed; accessed only from the single-threaded executor.
        unsafe {
            (*waiter).next = std::ptr::null_mut();
            (*waiter).prev = std::ptr::null_mut();
            (*waiter).queued = false;
        }
        waiter
    }

    /// Remove a specific waiter from the list.
    ///
    /// # Safety
    ///
    /// `waiter` must be in this list.
    unsafe fn remove(&mut self, waiter: *mut Waiter) {
        // SAFETY: waiter is a valid pointer to a live Waiter; accessed only from the single-threaded executor.
        if unsafe { !(*waiter).queued } {
            return;
        }

        // SAFETY: waiter is a valid pointer to a live Waiter; accessed only from the single-threaded executor.
        let prev = unsafe { (*waiter).prev };
        // SAFETY: waiter is a valid pointer to a live Waiter; accessed only from the single-threaded executor.
        let next = unsafe { (*waiter).next };

        if prev.is_null() {
            self.head = next;
        } else {
            // SAFETY: prev is non-null (checked above) and points to a live Waiter; accessed only from the single-threaded executor.
            unsafe { (*prev).next = next };
        }

        if next.is_null() {
            self.tail = prev;
        } else {
            // SAFETY: next is non-null (checked above) and points to a live Waiter; accessed only from the single-threaded executor.
            unsafe { (*next).prev = prev };
        }

        // SAFETY: waiter is a valid pointer to a live Waiter being unlinked; accessed only from the single-threaded executor.
        unsafe {
            (*waiter).next = std::ptr::null_mut();
            (*waiter).prev = std::ptr::null_mut();
            (*waiter).queued = false;
        }
    }

    /// Wake all waiters and clear the list.
    unsafe fn wake_all(&mut self) {
        let mut cursor = self.head;
        while !cursor.is_null() {
            // SAFETY: cursor is a valid pointer to a live Waiter; accessed only from the single-threaded executor.
            let next = unsafe { (*cursor).next };
            // SAFETY: cursor is a valid pointer to a live Waiter being unlinked; accessed only from the single-threaded executor.
            unsafe {
                (*cursor).next = std::ptr::null_mut();
                (*cursor).prev = std::ptr::null_mut();
                (*cursor).queued = false;
            }
            // SAFETY: cursor is a valid pointer to a live Waiter; accessed only from the single-threaded executor.
            if let Some(waker) = unsafe { (*cursor).waker.take() } {
                waker.wake();
            }
            cursor = next;
        }
        self.head = std::ptr::null_mut();
        self.tail = std::ptr::null_mut();
    }
}

// =============================================================================
// Shared state
// =============================================================================

struct Inner<T> {
    buffer: RingBuffer<T>,
    rx_waker: Option<Waker>,
    tx_waiters: WaiterList,
    sender_count: u32,
    closed: bool,
}

impl<T> Inner<T> {
    fn new(capacity: usize) -> Self {
        Self {
            buffer: RingBuffer::new(capacity),
            rx_waker: None,
            tx_waiters: WaiterList::new(),
            sender_count: 1,
            closed: false,
        }
    }
}

type Shared<T> = Rc<UnsafeCell<Inner<T>>>;

/// Get a mutable reference to the inner state.
///
/// # Safety
///
/// Single-threaded only. Must not be called re-entrantly.
#[inline]
#[allow(clippy::mut_from_ref)] // Intentional: UnsafeCell + single-threaded guarantee.
unsafe fn inner<T>(shared: &Shared<T>) -> &mut Inner<T> {
    // SAFETY: accessed only from the single-threaded executor; no re-entrant access.
    unsafe { &mut *shared.get() }
}

// =============================================================================
// channel()
// =============================================================================

/// Create a bounded local MPSC channel.
///
/// `capacity` is rounded up to the next power of two.
///
/// # Panics
///
/// - Panics if called outside [`Runtime::block_on`](crate::Runtime::block_on).
/// - Panics if `capacity` is 0.
pub fn channel<T>(capacity: usize) -> (Sender<T>, Receiver<T>) {
    crate::context::assert_in_runtime("local::channel() called outside Runtime::block_on");
    channel_inner(capacity)
}

fn channel_inner<T>(capacity: usize) -> (Sender<T>, Receiver<T>) {
    let shared: Shared<T> = Rc::new(UnsafeCell::new(Inner::new(capacity)));
    let tx = Sender {
        inner: shared.clone(),
    };
    let rx = Receiver { inner: shared };
    (tx, rx)
}

// =============================================================================
// Sender
// =============================================================================

/// Sending half of a bounded MPSC channel.
///
/// `Clone` to create multiple producers. `!Send`, `!Sync`.
pub struct Sender<T> {
    inner: Shared<T>,
}

impl<T> Sender<T> {
    /// Send a value, waiting if the buffer is full.
    ///
    /// Returns `Err(SendError(value))` if the receiver was dropped.
    pub fn send(&self, value: T) -> Send<'_, T> {
        Send {
            sender: self,
            value: Some(value),
            waiter: Waiter::new(),
        }
    }

    /// Try to send a value without waiting.
    ///
    /// Returns immediately with `Err(TrySendError::Full(value))` if the
    /// buffer is full, or `Err(TrySendError::Closed(value))` if the
    /// receiver was dropped.
    pub fn try_send(&self, value: T) -> Result<(), TrySendError<T>> {
        // SAFETY: single-threaded, no re-entrancy.
        let state = unsafe { inner(&self.inner) };

        if state.closed {
            return Err(TrySendError::Closed(value));
        }
        if state.buffer.is_full() {
            return Err(TrySendError::Full(value));
        }

        // SAFETY: just checked not full.
        unsafe { state.buffer.push(value) };

        // Wake receiver if waiting.
        if let Some(waker) = state.rx_waker.take() {
            waker.wake();
        }

        Ok(())
    }
}

impl<T> Clone for Sender<T> {
    fn clone(&self) -> Self {
        // SAFETY: single-threaded, no re-entrancy.
        let state = unsafe { inner(&self.inner) };
        state.sender_count += 1;
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<T> Drop for Sender<T> {
    fn drop(&mut self) {
        // SAFETY: single-threaded, no re-entrancy.
        let state = unsafe { inner(&self.inner) };
        state.sender_count -= 1;

        // Last sender dropped — wake receiver so it sees RecvError.
        if state.sender_count == 0
            && let Some(waker) = state.rx_waker.take()
        {
            waker.wake();
        }
    }
}

// =============================================================================
// Send future
// =============================================================================

/// Future returned by [`Sender::send`].
///
/// Must be polled to completion or dropped. Dropping cancels the send
/// and unlinks the waiter from the queue.
pub struct Send<'a, T> {
    sender: &'a Sender<T>,
    value: Option<T>,
    waiter: Waiter,
}

impl<T> Future for Send<'_, T> {
    type Output = Result<(), SendError<T>>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // SAFETY: we only access fields through the pin projection.
        // `waiter` is pinned because `Send` is pinned.
        let this = unsafe { self.get_unchecked_mut() };

        // SAFETY: single-threaded, no re-entrancy.
        let state = unsafe { inner(&this.sender.inner) };

        // Channel closed?
        if state.closed {
            let value = this.value.take().expect("polled after completion");
            if this.waiter.queued {
                // SAFETY: waiter is in the list.
                unsafe { state.tx_waiters.remove(&raw mut this.waiter) };
            }
            return Poll::Ready(Err(SendError(value)));
        }

        // Buffer has room?
        if !state.buffer.is_full() {
            let value = this.value.take().expect("polled after completion");
            if this.waiter.queued {
                // SAFETY: waiter is in the list.
                unsafe { state.tx_waiters.remove(&raw mut this.waiter) };
            }
            // SAFETY: just checked not full.
            unsafe { state.buffer.push(value) };

            // Wake receiver if waiting.
            if let Some(waker) = state.rx_waker.take() {
                waker.wake();
            }

            return Poll::Ready(Ok(()));
        }

        // Buffer full — park this sender.
        this.waiter.waker = Some(cx.waker().clone());
        if !this.waiter.queued {
            // SAFETY: this.waiter is pinned (Send is pinned), lives until
            // drop which unlinks it.
            unsafe { state.tx_waiters.push_back(&raw mut this.waiter) };
        }

        Poll::Pending
    }
}

impl<T> Drop for Send<'_, T> {
    fn drop(&mut self) {
        if self.waiter.queued {
            // SAFETY: single-threaded, waiter is in the list.
            let state = unsafe { inner(&self.sender.inner) };
            // SAFETY: waiter is queued and this is the sole owner removing it; accessed only from the single-threaded executor.
            unsafe { state.tx_waiters.remove(&raw mut self.waiter) };
        }
    }
}

// =============================================================================
// Receiver
// =============================================================================

/// Receiving half of a bounded MPSC channel.
///
/// Not `Clone` — single consumer only. `!Send`, `!Sync`.
pub struct Receiver<T> {
    inner: Shared<T>,
}

impl<T> Receiver<T> {
    /// Receive a value, waiting if the buffer is empty.
    ///
    /// Returns `Err(RecvError)` when all senders have been dropped and
    /// the buffer is empty.
    pub fn recv(&self) -> Recv<'_, T> {
        Recv { receiver: self }
    }

    /// Try to receive a value without waiting.
    pub fn try_recv(&self) -> Result<T, TryRecvError> {
        // SAFETY: single-threaded, no re-entrancy.
        let state = unsafe { inner(&self.inner) };

        if !state.buffer.is_empty() {
            // SAFETY: just checked non-empty.
            let value = unsafe { state.buffer.pop() };

            // Wake one blocked sender.
            // SAFETY: accessed only from the single-threaded executor.
            let waiter = unsafe { state.tx_waiters.pop_front() };
            if !waiter.is_null() {
                // SAFETY: waiter was in the list, has a valid waker.
                if let Some(waker) = unsafe { (*waiter).waker.take() } {
                    waker.wake();
                }
            }

            return Ok(value);
        }

        if state.sender_count == 0 {
            Err(TryRecvError::Closed)
        } else {
            Err(TryRecvError::Empty)
        }
    }
}

impl<T> Drop for Receiver<T> {
    fn drop(&mut self) {
        // SAFETY: single-threaded, no re-entrancy.
        let state = unsafe { inner(&self.inner) };
        state.closed = true;

        // Wake all blocked senders so they see the closed error.
        // SAFETY: accessed only from the single-threaded executor; wake_all unlinks all waiters safely.
        unsafe { state.tx_waiters.wake_all() };
    }
}

// =============================================================================
// Recv future
// =============================================================================

/// Future returned by [`Receiver::recv`].
pub struct Recv<'a, T> {
    receiver: &'a Receiver<T>,
}

impl<T> Future for Recv<'_, T> {
    type Output = Result<T, RecvError>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // SAFETY: single-threaded, no re-entrancy.
        let state = unsafe { inner(&self.receiver.inner) };

        // Buffer has data?
        if !state.buffer.is_empty() {
            // SAFETY: just checked non-empty.
            let value = unsafe { state.buffer.pop() };

            // Wake one blocked sender.
            // SAFETY: accessed only from the single-threaded executor.
            let waiter = unsafe { state.tx_waiters.pop_front() };
            if !waiter.is_null() {
                // SAFETY: waiter is non-null and points to a live Waiter; accessed only from the single-threaded executor.
                if let Some(waker) = unsafe { (*waiter).waker.take() } {
                    waker.wake();
                }
            }

            return Poll::Ready(Ok(value));
        }

        // Empty + no senders → closed.
        if state.sender_count == 0 {
            return Poll::Ready(Err(RecvError));
        }

        // Empty + senders alive → park.
        state.rx_waker = Some(cx.waker().clone());
        Poll::Pending
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::task::{RawWaker, RawWakerVTable};

    // =========================================================================
    // Minimal test executor + fake runtime context
    // =========================================================================

    fn noop_waker() -> Waker {
        fn noop(_: *const ()) {}
        fn noop_clone(p: *const ()) -> RawWaker {
            RawWaker::new(p, &VTABLE)
        }
        const VTABLE: RawWakerVTable = RawWakerVTable::new(noop_clone, noop, noop, noop);
        // SAFETY: all vtable functions are no-ops or trivial clones; the
        // null data pointer is never dereferenced.
        unsafe { Waker::from_raw(RawWaker::new(std::ptr::null(), &VTABLE)) }
    }

    fn poll_once<F: Future>(f: Pin<&mut F>) -> Poll<F::Output> {
        let waker = noop_waker();
        let mut cx = Context::from_waker(&waker);
        f.poll(&mut cx)
    }

    // =========================================================================
    // Ring buffer tests
    // =========================================================================

    #[test]
    fn ring_buffer_push_pop() {
        let mut rb = RingBuffer::<u32>::new(4);
        assert_eq!(rb.capacity(), 4);
        assert!(rb.is_empty());

        // SAFETY: buffer is not full; verified by test setup.
        unsafe { rb.push(1) };
        // SAFETY: buffer is not full; verified by test setup.
        unsafe { rb.push(2) };
        // SAFETY: buffer is not full; verified by test setup.
        unsafe { rb.push(3) };
        assert_eq!(rb.len(), 3);

        // SAFETY: buffer is not empty; verified by test setup.
        assert_eq!(unsafe { rb.pop() }, 1);
        // SAFETY: buffer is not empty; verified by test setup.
        assert_eq!(unsafe { rb.pop() }, 2);
        // SAFETY: buffer is not empty; verified by test setup.
        assert_eq!(unsafe { rb.pop() }, 3);
        assert!(rb.is_empty());
    }

    #[test]
    fn ring_buffer_full() {
        let mut rb = RingBuffer::<u32>::new(2);
        assert_eq!(rb.capacity(), 2);

        // SAFETY: buffer is not full; verified by test setup.
        unsafe { rb.push(1) };
        // SAFETY: buffer is not full; verified by test setup.
        unsafe { rb.push(2) };
        assert!(rb.is_full());
        assert_eq!(rb.len(), 2);

        // SAFETY: buffer is not empty; verified by test setup.
        assert_eq!(unsafe { rb.pop() }, 1);
        assert!(!rb.is_full());
    }

    #[test]
    fn ring_buffer_wrap_around() {
        let mut rb = RingBuffer::<u32>::new(4);

        // Fill and drain a few times to wrap indices.
        for cycle in 0..10u32 {
            let base = cycle * 4;
            // SAFETY: buffer is not full; verified by test setup.
            unsafe { rb.push(base) };
            // SAFETY: buffer is not full; verified by test setup.
            unsafe { rb.push(base + 1) };
            // SAFETY: buffer is not full; verified by test setup.
            unsafe { rb.push(base + 2) };
            // SAFETY: buffer is not full; verified by test setup.
            unsafe { rb.push(base + 3) };
            assert!(rb.is_full());

            // SAFETY: buffer is not empty; verified by test setup.
            assert_eq!(unsafe { rb.pop() }, base);
            // SAFETY: buffer is not empty; verified by test setup.
            assert_eq!(unsafe { rb.pop() }, base + 1);
            // SAFETY: buffer is not empty; verified by test setup.
            assert_eq!(unsafe { rb.pop() }, base + 2);
            // SAFETY: buffer is not empty; verified by test setup.
            assert_eq!(unsafe { rb.pop() }, base + 3);
            assert!(rb.is_empty());
        }
    }

    #[test]
    fn ring_buffer_rounds_up_to_power_of_two() {
        let rb = RingBuffer::<u8>::new(3);
        assert_eq!(rb.capacity(), 4);

        let rb = RingBuffer::<u8>::new(5);
        assert_eq!(rb.capacity(), 8);

        let rb = RingBuffer::<u8>::new(8);
        assert_eq!(rb.capacity(), 8);
    }

    #[test]
    #[should_panic(expected = "capacity must be > 0")]
    fn ring_buffer_zero_capacity_panics() {
        let _ = RingBuffer::<u8>::new(0);
    }

    #[test]
    fn ring_buffer_drop_remaining() {
        use std::cell::Cell;
        use std::rc::Rc;

        let dropped = Rc::new(Cell::new(0u32));

        struct DropCounter(Rc<Cell<u32>>);
        impl Drop for DropCounter {
            fn drop(&mut self) {
                self.0.set(self.0.get() + 1);
            }
        }

        let mut rb = RingBuffer::new(4);
        // SAFETY: buffer is not full; verified by test setup.
        unsafe { rb.push(DropCounter(dropped.clone())) };
        // SAFETY: buffer is not full; verified by test setup.
        unsafe { rb.push(DropCounter(dropped.clone())) };
        // SAFETY: buffer is not full; verified by test setup.
        unsafe { rb.push(DropCounter(dropped.clone())) };
        assert_eq!(dropped.get(), 0);

        drop(rb);
        assert_eq!(dropped.get(), 3);
    }

    // =========================================================================
    // Channel tests
    // =========================================================================

    #[test]
    fn send_recv_single() {
        let (tx, rx) = channel_inner::<u32>(4);

        // try_send then try_recv
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
        let (tx, rx) = channel_inner(8);
        for i in 0..8u32 {
            tx.try_send(i).unwrap();
        }
        for i in 0..8u32 {
            assert_eq!(rx.try_recv().unwrap(), i);
        }
    }

    #[test]
    fn try_send_full() {
        let (tx, rx) = channel_inner(2);
        tx.try_send(1u32).unwrap();
        tx.try_send(2).unwrap();

        let err = tx.try_send(3).unwrap_err();
        assert!(err.is_full());
        assert_eq!(err.into_inner(), 3);

        // Pop one, then send succeeds.
        assert_eq!(rx.try_recv().unwrap(), 1);
        tx.try_send(3).unwrap();
    }

    #[test]
    fn try_recv_empty() {
        let (tx, rx) = channel_inner::<u32>(4);
        assert_eq!(rx.try_recv(), Err(TryRecvError::Empty));

        tx.try_send(1).unwrap();
        assert_eq!(rx.try_recv().unwrap(), 1);
        assert_eq!(rx.try_recv(), Err(TryRecvError::Empty));
    }

    #[test]
    fn sender_drop_signals_closed() {
        let (tx, rx) = channel_inner::<u32>(4);
        tx.try_send(42).unwrap();
        drop(tx);

        // Can still drain buffered values.
        assert_eq!(rx.try_recv().unwrap(), 42);
        // Then closed.
        assert_eq!(rx.try_recv(), Err(TryRecvError::Closed));
    }

    #[test]
    fn receiver_drop_signals_closed() {
        let (tx, rx) = channel_inner::<u32>(4);
        drop(rx);

        let err = tx.try_send(1).unwrap_err();
        assert!(err.is_closed());
    }

    #[test]
    fn multiple_senders() {
        let (tx1, rx) = channel_inner(8);
        let tx2 = tx1.clone();

        tx1.try_send(1u32).unwrap();
        tx2.try_send(2).unwrap();
        tx1.try_send(3).unwrap();

        assert_eq!(rx.try_recv().unwrap(), 1);
        assert_eq!(rx.try_recv().unwrap(), 2);
        assert_eq!(rx.try_recv().unwrap(), 3);
    }

    #[test]
    fn last_sender_drop_wakes_receiver() {
        let (tx, rx) = channel_inner::<u32>(4);

        let mut recv_fut = std::pin::pin!(rx.recv());
        // Poll recv — should be Pending (buffer empty, sender alive).
        assert!(poll_once(recv_fut.as_mut()).is_pending());

        // Drop sender — should signal closed.
        drop(tx);

        // Next poll should return RecvError... but our noop waker
        // doesn't actually re-poll. Just verify via try_recv.
        assert_eq!(rx.try_recv(), Err(TryRecvError::Closed));
    }

    #[test]
    fn recv_pending_then_ready() {
        let (tx, rx) = channel_inner::<u32>(4);

        let mut recv_fut = std::pin::pin!(rx.recv());

        // Empty — Pending.
        assert!(poll_once(recv_fut.as_mut()).is_pending());

        // Send a value (this would wake the receiver in a real executor).
        tx.try_send(99).unwrap();

        // Re-poll — now Ready.
        match poll_once(recv_fut.as_mut()) {
            Poll::Ready(Ok(99)) => {}
            other => panic!("expected Ready(Ok(99)), got {other:?}"),
        }
    }

    #[test]
    fn send_pending_then_ready() {
        let (tx, rx) = channel_inner(2);
        tx.try_send(1u32).unwrap();
        tx.try_send(2).unwrap();
        // Buffer full.

        let mut send_fut = std::pin::pin!(tx.send(3));

        // Full — Pending.
        assert!(poll_once(send_fut.as_mut()).is_pending());

        // Pop one value (this would wake a sender in a real executor).
        assert_eq!(rx.try_recv().unwrap(), 1);

        // Re-poll — now Ready.
        match poll_once(send_fut.as_mut()) {
            Poll::Ready(Ok(())) => {}
            other => panic!("expected Ready(Ok(())), got {other:?}"),
        }

        // The value should now be in the buffer.
        assert_eq!(rx.try_recv().unwrap(), 2);
        assert_eq!(rx.try_recv().unwrap(), 3);
    }

    #[test]
    fn send_cancelled_on_drop() {
        let (tx, rx) = channel_inner(2);
        tx.try_send(1u32).unwrap();
        tx.try_send(2).unwrap();

        {
            let mut send_fut = std::pin::pin!(tx.send(3));
            // Park the sender.
            assert!(poll_once(send_fut.as_mut()).is_pending());
            // Drop the future — should unlink from waiter list.
        }

        // Pop and verify the cancelled send's value is NOT in the buffer.
        assert_eq!(rx.try_recv().unwrap(), 1);
        assert_eq!(rx.try_recv().unwrap(), 2);
        assert_eq!(rx.try_recv(), Err(TryRecvError::Empty));
    }

    // =========================================================================
    // Edge cases
    // =========================================================================

    #[test]
    fn capacity_one() {
        let (tx, rx) = channel_inner(1);
        tx.try_send(42u32).unwrap();
        assert!(tx.try_send(43).unwrap_err().is_full());
        assert_eq!(rx.try_recv().unwrap(), 42);
        tx.try_send(43).unwrap();
        assert_eq!(rx.try_recv().unwrap(), 43);
    }

    #[test]
    fn non_power_of_two_rounds_up() {
        // capacity 3 → 4, capacity 5 → 8
        let (tx, rx) = channel_inner(3);
        for i in 0..4u32 {
            tx.try_send(i).unwrap();
        }
        assert!(tx.try_send(4).unwrap_err().is_full());
        for i in 0..4u32 {
            assert_eq!(rx.try_recv().unwrap(), i);
        }
    }

    #[test]
    fn clone_sender_increments_count() {
        let (tx, rx) = channel_inner::<u32>(4);
        let tx2 = tx.clone();
        let tx3 = tx.clone();

        // Drop original and one clone — channel still open.
        drop(tx);
        drop(tx2);
        tx3.try_send(1).unwrap();
        assert_eq!(rx.try_recv().unwrap(), 1);

        // Drop last sender — channel closed.
        drop(tx3);
        assert_eq!(rx.try_recv(), Err(TryRecvError::Closed));
    }

    #[test]
    fn recv_drains_buffer_after_all_senders_drop() {
        let (tx, rx) = channel_inner(8);
        tx.try_send(1u32).unwrap();
        tx.try_send(2).unwrap();
        tx.try_send(3).unwrap();
        drop(tx);

        // All buffered values are still available.
        assert_eq!(rx.try_recv().unwrap(), 1);
        assert_eq!(rx.try_recv().unwrap(), 2);
        assert_eq!(rx.try_recv().unwrap(), 3);
        assert_eq!(rx.try_recv(), Err(TryRecvError::Closed));
    }

    #[test]
    fn send_after_receiver_drop_returns_closed() {
        let (tx, rx) = channel_inner::<u32>(4);
        drop(rx);

        let mut send_fut = std::pin::pin!(tx.send(1));
        match poll_once(send_fut.as_mut()) {
            Poll::Ready(Err(SendError(1))) => {}
            other => panic!("expected Ready(Err(SendError(1))), got {other:?}"),
        }
    }

    #[test]
    fn multiple_senders_blocked_then_unblocked() {
        let (tx1, rx) = channel_inner(2);
        let tx2 = tx1.clone();
        tx1.try_send(1u32).unwrap();
        tx2.try_send(2).unwrap();
        // Buffer full — both senders should block.

        let mut send1 = std::pin::pin!(tx1.send(3));
        let mut send2 = std::pin::pin!(tx2.send(4));
        assert!(poll_once(send1.as_mut()).is_pending());
        assert!(poll_once(send2.as_mut()).is_pending());

        // Pop one — should unblock the first waiter (FIFO).
        assert_eq!(rx.try_recv().unwrap(), 1);

        // Re-poll first sender — should succeed.
        match poll_once(send1.as_mut()) {
            Poll::Ready(Ok(())) => {}
            other => panic!("expected Ready(Ok(())), got {other:?}"),
        }

        // Pop another — should unblock second waiter.
        assert_eq!(rx.try_recv().unwrap(), 2);
        match poll_once(send2.as_mut()) {
            Poll::Ready(Ok(())) => {}
            other => panic!("expected Ready(Ok(())), got {other:?}"),
        }

        // Verify all values arrived.
        assert_eq!(rx.try_recv().unwrap(), 3);
        assert_eq!(rx.try_recv().unwrap(), 4);
    }

    #[test]
    fn receiver_drop_wakes_blocked_senders() {
        let (tx, rx) = channel_inner(1);
        tx.try_send(1u32).unwrap();

        let mut send_fut = std::pin::pin!(tx.send(2));
        assert!(poll_once(send_fut.as_mut()).is_pending());

        // Drop receiver — sender should get Closed on next poll.
        drop(rx);
        match poll_once(send_fut.as_mut()) {
            Poll::Ready(Err(SendError(2))) => {}
            other => panic!("expected Ready(Err(SendError(2))), got {other:?}"),
        }
    }

    #[test]
    fn drop_values_on_channel_close() {
        use std::cell::Cell;
        use std::rc::Rc;

        let dropped = Rc::new(Cell::new(0u32));

        struct DropCounter(Rc<Cell<u32>>);
        impl Drop for DropCounter {
            fn drop(&mut self) {
                self.0.set(self.0.get() + 1);
            }
        }

        let (tx, rx) = channel_inner(4);
        tx.try_send(DropCounter(dropped.clone())).unwrap();
        tx.try_send(DropCounter(dropped.clone())).unwrap();
        tx.try_send(DropCounter(dropped.clone())).unwrap();
        assert_eq!(dropped.get(), 0);

        // Drop both sides — remaining values should be dropped.
        drop(tx);
        drop(rx);
        assert_eq!(dropped.get(), 3);
    }

    // =========================================================================
    // Stress tests
    // =========================================================================

    #[test]
    fn stress_sequential_send_recv() {
        let (tx, rx) = channel_inner(64);
        let n = if cfg!(miri) { 100 } else { 100_000 };
        for i in 0..n {
            tx.try_send(i).unwrap();
            assert_eq!(rx.try_recv().unwrap(), i);
        }
    }

    #[test]
    fn stress_fill_drain_cycles() {
        let (tx, rx) = channel_inner(64);
        for _ in 0..1_000 {
            // Fill
            for i in 0..64u32 {
                tx.try_send(i).unwrap();
            }
            assert!(tx.try_send(999).unwrap_err().is_full());

            // Drain
            for i in 0..64u32 {
                assert_eq!(rx.try_recv().unwrap(), i);
            }
            assert_eq!(rx.try_recv(), Err(TryRecvError::Empty));
        }
    }

    #[test]
    fn stress_interleaved_small_buffer() {
        // Small buffer forces frequent wrap-around.
        let (tx, rx) = channel_inner(2);
        for i in 0..50_000u64 {
            tx.try_send(i).unwrap();
            assert_eq!(rx.try_recv().unwrap(), i);
        }
    }
}
