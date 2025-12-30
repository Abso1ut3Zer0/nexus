//! The underlying ring buffer storage for MPSC queues.
//!
//! This uses per-slot sequence numbers to coordinate multiple producers
//! and handle out-of-order completion.

use std::cell::UnsafeCell;
use std::mem::{ManuallyDrop, MaybeUninit};
use std::ptr::{self, NonNull};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

use crossbeam_utils::CachePadded;

/// A slot in the sequenced ring buffer.
///
/// The sequence number indicates the slot's state:
/// - `sequence == index`: slot is empty/writable
/// - `sequence == index + 1`: slot contains data, readable
/// - `sequence == index + capacity`: slot recycled, writable next lap
#[repr(C)]
pub(crate) struct Slot<T> {
    pub(crate) sequence: AtomicUsize,
    pub(crate) data: UnsafeCell<MaybeUninit<T>>,
}

/// The backing storage for an MPSC queue.
///
/// Memory layout:
/// ```text
/// ┌───────────────────────────────────────────────────────┐
/// │ RingBuffer header                                     │
/// ├───────────────────────────────────────────────────────┤
/// │ head (cache-line padded) - consumer read position     │
/// ├───────────────────────────────────────────────────────┤
/// │ tail (cache-line padded) - producer claim position    │
/// ├───────────────────────────────────────────────────────┤
/// │ Slot[0]: { sequence, data }                           │
/// │ Slot[1]: { sequence, data }                           │
/// │ ...                                                   │
/// └───────────────────────────────────────────────────────┘
/// ```
///
/// Queue contains elements in range [head, tail).
/// - Producers claim at tail (via CAS), then write and publish
/// - Consumer reads at head, then increments head
#[repr(C)]
pub struct RingBuffer<T> {
    // === Hot path - cache-line padded indices ===
    /// Consumer's read position.
    head: CachePadded<AtomicUsize>,
    /// Producer's claim position (multiple producers CAS on this).
    tail: CachePadded<AtomicUsize>,

    // === Buffer pointer ===
    buffer: *mut Slot<T>,

    // === Immutable configuration ===
    capacity: usize,
    mask: usize,

    // === Reference counting ===
    ref_count: AtomicUsize,

    // === Liveness tracking (cold path) ===
    /// Number of senders alive. When 0, all producers disconnected.
    sender_count: AtomicUsize,
    /// Set when the receiver is dropped.
    receiver_disconnected: AtomicBool,
}

unsafe impl<T: Send> Send for RingBuffer<T> {}
unsafe impl<T: Send> Sync for RingBuffer<T> {}

impl<T> RingBuffer<T> {
    /// Allocates and initializes a new ring buffer.
    ///
    /// The capacity will be rounded up to the next power of two (minimum 2).
    /// Initial ref_count is 2 (one sender + one receiver).
    pub fn allocate(capacity: usize) -> NonNull<Self> {
        let capacity = capacity.next_power_of_two().max(2);

        // Use Vec for slot buffer - guarantees good alignment
        let buffer = ManuallyDrop::new(Vec::<Slot<T>>::with_capacity(capacity)).as_mut_ptr();

        // Initialize slot sequences: slot[i].sequence = i (empty/writable)
        for i in 0..capacity {
            unsafe {
                let slot = buffer.add(i);
                ptr::addr_of_mut!((*slot).sequence).write(AtomicUsize::new(i));
                // data left uninitialized (MaybeUninit)
            }
        }

        let rb = Box::new(Self {
            head: CachePadded::new(AtomicUsize::new(0)),
            tail: CachePadded::new(AtomicUsize::new(0)),
            buffer,
            capacity,
            mask: capacity - 1,
            ref_count: AtomicUsize::new(2),
            sender_count: AtomicUsize::new(1),
            receiver_disconnected: AtomicBool::new(false),
        });

        unsafe { NonNull::new_unchecked(Box::into_raw(rb)) }
    }

    // === Accessors ===

    #[inline]
    fn slot_ptr(&self, index: usize) -> *mut Slot<T> {
        unsafe { self.buffer.add(index & self.mask) }
    }

    #[inline]
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    #[inline]
    pub fn mask(&self) -> usize {
        self.mask
    }

    #[inline]
    pub fn buffer_ptr(&self) -> *mut Slot<T> {
        self.buffer
    }

    #[inline]
    pub fn tail_ptr(&self) -> *const AtomicUsize {
        &*self.tail as *const AtomicUsize
    }

    // === Producer operations (tail) ===

    /// Loads the current tail position (producer claim position).
    #[inline]
    pub fn load_tail(&self) -> usize {
        self.tail.load(Ordering::Acquire)
    }

    // === Consumer operations (head) ===

    /// Attempts to read from the next slot.
    ///
    /// Returns `Some(value)` if data was available, `None` if queue is empty.
    ///
    /// # Safety
    ///
    /// Must only be called from a single consumer thread.
    #[inline]
    pub unsafe fn try_read(&self, head: usize) -> Option<T> {
        let slot = self.slot_ptr(head);
        let seq = unsafe { (*slot).sequence.load(Ordering::Acquire) };
        let expected = head.wrapping_add(1);

        if seq == expected {
            // Slot is readable
            let value = unsafe { (*(*slot).data.get()).assume_init_read() };

            // Recycle the slot: sequence = head + capacity
            unsafe {
                (*slot)
                    .sequence
                    .store(head.wrapping_add(self.capacity), Ordering::Release);
            }

            Some(value)
        } else {
            None
        }
    }

    /// Stores the head position (called by consumer after reading).
    #[inline]
    pub fn store_head(&self, head: usize) {
        self.head.store(head, Ordering::Relaxed);
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

                // Reconstruct and drop the Vec to free slot buffer
                let _ = Vec::from_raw_parts(inner.buffer, 0, inner.capacity);

                // Reconstruct and drop the Box to free header
                let _ = Box::from_raw(this.as_ptr());
            }
        }
    }

    unsafe fn drop_remaining_elements(this: NonNull<Self>) {
        let inner = unsafe { this.as_ref() };
        let head = inner.head.load(Ordering::Relaxed);
        let tail = inner.tail.load(Ordering::Relaxed);

        for i in head..tail {
            let slot = inner.slot_ptr(i);
            let seq = unsafe { (*slot).sequence.load(Ordering::Relaxed) };
            let expected_written = i.wrapping_add(1);

            if seq == expected_written {
                unsafe {
                    ptr::drop_in_place((*slot).data.get().cast::<T>());
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
                let slot = inner.slot_ptr(i);
                assert_eq!((*slot).sequence.load(Ordering::Relaxed), i);
            }

            RingBuffer::release(rb);
            RingBuffer::release(rb);
        }
    }
}
