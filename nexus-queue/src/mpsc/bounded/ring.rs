//! The underlying ring buffer storage for MPSC queues.
//!
//! This uses per-slot sequence numbers to coordinate multiple producers
//! and handle out-of-order completion.

use std::alloc::{Layout, alloc, dealloc, handle_alloc_error};
use std::cell::UnsafeCell;
use std::mem::MaybeUninit;
use std::ptr::{self, NonNull};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

use crossbeam_utils::{Backoff, CachePadded};

/// A slot in the sequenced ring buffer.
///
/// The sequence number indicates the slot's state:
/// - `sequence == index`: slot is empty/writable
/// - `sequence == index + 1`: slot contains data, readable
/// - `sequence == index + capacity`: slot recycled, writable next lap
#[repr(C)]
struct Slot<T> {
    sequence: AtomicUsize,
    data: UnsafeCell<MaybeUninit<T>>,
}

/// The backing storage for an MPSC queue.
///
/// Memory layout:
/// ```text
/// ┌───────────────────────────────────────────────────────┐
/// │ RingBuffer header                                     │
/// │   ref_count, capacity, mask, buffer, layout           │
/// │   sender_count, receiver_disconnected                 │
/// ├───────────────────────────────────────────────────────┤
/// │ head (cache-line padded) - producer claim position    │
/// ├───────────────────────────────────────────────────────┤
/// │ tail (cache-line padded) - consumer read position     │
/// ├───────────────────────────────────────────────────────┤
/// │ Slot[0]: { sequence, data }                           │
/// │ Slot[1]: { sequence, data }                           │
/// │ ...                                                   │
/// └───────────────────────────────────────────────────────┘
/// ```
#[repr(C)]
pub struct RingBuffer<T> {
    // === Reference counting ===
    ref_count: AtomicUsize,

    // === Immutable configuration ===
    capacity: usize,
    mask: usize,
    buffer: *mut Slot<T>,
    layout: Layout,

    // === Liveness tracking ===
    /// Number of senders alive. When 0, all producers disconnected.
    sender_count: AtomicUsize,
    /// Set when the receiver is dropped.
    receiver_disconnected: AtomicBool,

    // === Cache-line padded indices ===
    /// Next slot for producers to claim (via CAS).
    head: CachePadded<AtomicUsize>,
    /// Next slot for consumer to read.
    tail: CachePadded<AtomicUsize>,
}

unsafe impl<T: Send> Send for RingBuffer<T> {}
unsafe impl<T: Send> Sync for RingBuffer<T> {}

impl<T> RingBuffer<T> {
    /// Computes the memory layout for a ring buffer with the given capacity.
    fn layout_for(capacity: usize) -> (Layout, usize) {
        let header = Layout::new::<Self>();
        let slots = Layout::array::<Slot<T>>(capacity).expect("capacity too large");
        let (layout, buffer_offset) = header.extend(slots).expect("layout overflow");
        (layout.pad_to_align(), buffer_offset)
    }

    /// Allocates and initializes a new ring buffer.
    ///
    /// The capacity will be rounded up to the next power of two (minimum 2).
    /// Initial ref_count is 2 (one sender + one receiver).
    pub fn allocate(capacity: usize) -> NonNull<Self> {
        let capacity = capacity.next_power_of_two().max(2);
        let (layout, buffer_offset) = Self::layout_for(capacity);

        let ptr = unsafe { alloc(layout) };
        if ptr.is_null() {
            handle_alloc_error(layout);
        }

        let buffer = unsafe { ptr.add(buffer_offset).cast::<Slot<T>>() };
        let rb = ptr.cast::<Self>();

        unsafe {
            ptr::write(
                rb,
                Self {
                    ref_count: AtomicUsize::new(2),
                    capacity,
                    mask: capacity - 1,
                    buffer,
                    layout,
                    sender_count: AtomicUsize::new(1),
                    receiver_disconnected: AtomicBool::new(false),
                    head: CachePadded::new(AtomicUsize::new(0)),
                    tail: CachePadded::new(AtomicUsize::new(0)),
                },
            );

            // Initialize slot sequences: slot[i].sequence = i (empty/writable)
            for i in 0..capacity {
                let slot = buffer.add(i);
                ptr::write(ptr::addr_of_mut!((*slot).sequence), AtomicUsize::new(i));
                // data left uninitialized (MaybeUninit)
            }

            NonNull::new_unchecked(rb)
        }
    }

    #[inline]
    fn slot(&self, index: usize) -> &Slot<T> {
        unsafe { &*self.buffer.add(index & self.mask) }
    }

    #[inline]
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    // === Producer operations ===

    /// Attempts to claim a slot for writing.
    ///
    /// Returns `Some(index)` if a slot was claimed, `None` if queue is full.
    #[inline]
    pub fn try_claim(&self) -> Option<usize> {
        let mut head = self.head.load(Ordering::Relaxed);

        loop {
            let slot = self.slot(head);
            let seq = slot.sequence.load(Ordering::Acquire);
            let diff = seq as isize - head as isize;

            if diff == 0 {
                // Slot is writable, try to claim it
                match self.head.compare_exchange_weak(
                    head,
                    head.wrapping_add(1),
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => return Some(head),
                    Err(h) => {
                        // CAS failed - contention. Use backoff for retries.
                        return self.try_claim_contended(h);
                    }
                }
            } else if diff < 0 {
                // Slot not yet recycled by consumer - queue is full
                return None;
            } else {
                // Another producer claimed this slot, reload head
                head = self.head.load(Ordering::Relaxed);
            }
        }
    }

    #[cold]
    fn try_claim_contended(&self, mut head: usize) -> Option<usize> {
        let backoff = Backoff::new();

        loop {
            let slot = self.slot(head);
            let seq = slot.sequence.load(Ordering::Acquire);
            let diff = seq as isize - head as isize;

            if diff == 0 {
                match self.head.compare_exchange_weak(
                    head,
                    head.wrapping_add(1),
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => return Some(head),
                    Err(h) => {
                        head = h;
                        backoff.spin();
                    }
                }
            } else if diff < 0 {
                return None;
            } else {
                head = self.head.load(Ordering::Relaxed);
                backoff.spin();
            }
        }
    }

    /// Writes a value to a claimed slot.
    ///
    /// # Safety
    ///
    /// The index must have been returned by a successful `try_claim()` call,
    /// and this must be called exactly once per claim.
    #[inline]
    pub unsafe fn write_slot(&self, index: usize, value: T) {
        let slot = self.slot(index);
        unsafe {
            ptr::write((*slot.data.get()).as_mut_ptr(), value);
        }
    }

    /// Publishes a slot after writing, making it readable by the consumer.
    ///
    /// # Safety
    ///
    /// Must be called after `write_slot` for the same index.
    #[inline]
    pub unsafe fn publish(&self, index: usize) {
        let slot = self.slot(index);
        // sequence = index + 1 signals "readable"
        slot.sequence
            .store(index.wrapping_add(1), Ordering::Release);
    }

    // === Consumer operations ===

    /// Attempts to read from the next slot.
    ///
    /// Returns `Some(value)` if data was available, `None` if queue is empty.
    ///
    /// # Safety
    ///
    /// Must only be called from a single consumer thread.
    #[inline]
    pub unsafe fn try_read(&self, tail: usize) -> Option<T> {
        let slot = self.slot(tail);
        let seq = slot.sequence.load(Ordering::Acquire);
        let expected = tail.wrapping_add(1);

        if seq == expected {
            // Slot is readable
            let value = unsafe { ptr::read((*slot.data.get()).as_ptr()) };

            // Recycle the slot: sequence = tail + capacity
            slot.sequence
                .store(tail.wrapping_add(self.capacity), Ordering::Release);

            Some(value)
        } else {
            None
        }
    }

    /// Loads the current head position.
    #[inline]
    pub fn load_head(&self) -> usize {
        self.head.load(Ordering::Acquire)
    }

    /// Stores the tail position.
    #[inline]
    pub fn store_tail(&self, tail: usize) {
        self.tail.store(tail, Ordering::Relaxed);
    }

    // === Liveness ===

    #[inline]
    pub fn add_sender(&self) {
        self.sender_count.fetch_add(1, Ordering::Relaxed);
    }

    #[inline]
    pub fn remove_sender(&self) -> usize {
        self.sender_count.fetch_sub(1, Ordering::AcqRel)
    }

    #[inline]
    pub fn sender_count(&self) -> usize {
        self.sender_count.load(Ordering::Acquire)
    }

    #[inline]
    pub fn is_receiver_disconnected(&self) -> bool {
        self.receiver_disconnected.load(Ordering::Relaxed)
    }

    #[inline]
    pub fn set_receiver_disconnected(&self) {
        self.receiver_disconnected.store(true, Ordering::Release);
    }

    // === Lifecycle ===

    pub fn acquire(this: NonNull<Self>) {
        unsafe {
            this.as_ref().ref_count.fetch_add(1, Ordering::Relaxed);
        }
    }

    pub unsafe fn release(this: NonNull<Self>) {
        let inner = unsafe { this.as_ref() };

        if inner.ref_count.fetch_sub(1, Ordering::AcqRel) == 1 {
            unsafe {
                Self::drop_remaining_elements(this);
                let layout = inner.layout;
                ptr::drop_in_place(this.as_ptr());
                dealloc(this.as_ptr().cast(), layout);
            }
        }
    }

    unsafe fn drop_remaining_elements(this: NonNull<Self>) {
        let inner = unsafe { this.as_ref() };
        let tail = inner.tail.load(Ordering::Relaxed);
        let head = inner.head.load(Ordering::Relaxed);

        // Check each slot in [tail, head) - only drop if sequence indicates it was written
        for i in tail..head {
            let slot = inner.slot(i);
            let seq = slot.sequence.load(Ordering::Relaxed);
            let expected_written = i.wrapping_add(1);

            if seq == expected_written {
                // Slot contains valid data
                unsafe {
                    ptr::drop_in_place((*slot.data.get()).as_mut_ptr());
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn slot_sequence_initialization() {
        let rb = RingBuffer::<u64>::allocate(8);

        unsafe {
            let inner = rb.as_ref();

            // All slots should start with sequence == index
            for i in 0..8 {
                let slot = inner.slot(i);
                assert_eq!(slot.sequence.load(Ordering::Relaxed), i);
            }

            RingBuffer::release(rb);
            RingBuffer::release(rb);
        }
    }

    #[test]
    fn claim_write_publish_read() {
        let rb = RingBuffer::<u64>::allocate(8);

        unsafe {
            let inner = rb.as_ref();

            // Claim and write
            let idx = inner.try_claim().unwrap();
            assert_eq!(idx, 0);

            inner.write_slot(idx, 42);
            inner.publish(idx);

            // Read
            let val = inner.try_read(0).unwrap();
            assert_eq!(val, 42);

            RingBuffer::release(rb);
            RingBuffer::release(rb);
        }
    }

    #[test]
    fn full_queue() {
        let rb = RingBuffer::<u64>::allocate(4);

        unsafe {
            let inner = rb.as_ref();

            // Fill the queue
            for i in 0..4 {
                let idx = inner.try_claim().unwrap();
                inner.write_slot(idx, i as u64);
                inner.publish(idx);
            }

            // Should be full now
            assert!(inner.try_claim().is_none());

            // Read one to free a slot
            let val = inner.try_read(0).unwrap();
            assert_eq!(val, 0);
            inner.store_tail(1);

            // Now we can claim again
            assert!(inner.try_claim().is_some());

            RingBuffer::release(rb);
            RingBuffer::release(rb);
        }
    }
}
