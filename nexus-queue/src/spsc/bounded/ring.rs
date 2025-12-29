//! The underlying ring buffer storage for SPSC queues.
//!
//! This is a single contiguous allocation containing:
//! - Header with metadata and synchronization primitives
//! - Cache-line padded indices
//! - The actual data buffer

use std::mem::ManuallyDrop;
use std::ptr::{self, NonNull};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

use crossbeam_utils::CachePadded;

/// The backing storage for an SPSC queue.
///
/// Memory layout:
/// ```text
/// ┌───────────────────────────────────────────────────────┐
/// │ RingBuffer header                                     │
/// ├───────────────────────────────────────────────────────┤
/// │ head (cache-line padded) - consumer read position     │
/// ├───────────────────────────────────────────────────────┤
/// │ tail (cache-line padded) - producer write position    │
/// ├───────────────────────────────────────────────────────┤
/// │ Buffer: [T; capacity]                                 │
/// └───────────────────────────────────────────────────────┘
/// ```
///
/// Queue contains elements in range [head, tail).
/// - Producer writes at tail, then increments tail
/// - Consumer reads at head, then increments head
#[repr(C)]
pub struct RingBuffer<T> {
    // === Hot path data - put first for cache locality ===
    /// Consumer's read position. Updated by receiver, read by sender.
    head: CachePadded<AtomicUsize>,
    /// Producer's write position. Updated by sender, read by receiver.
    tail: CachePadded<AtomicUsize>,

    /// Pointer to the data buffer
    buffer: *mut T,

    // === Immutable configuration (set once at construction) ===
    capacity: usize,
    mask: usize,

    // === Reference counting ===
    ref_count: AtomicUsize,

    // === Disconnect flags (only checked on slow path) ===
    sender_disconnected: AtomicBool,
    receiver_disconnected: AtomicBool,
}

// Safety: RingBuffer can be shared across threads. The atomic operations
// provide the necessary synchronization.
unsafe impl<T: Send> Send for RingBuffer<T> {}
unsafe impl<T: Send> Sync for RingBuffer<T> {}

impl<T> RingBuffer<T> {
    /// Allocates and initializes a new ring buffer with the given capacity.
    ///
    /// The capacity will be rounded up to the next power of two (minimum 2).
    /// The returned `NonNull` has a reference count of 2 (one for sender, one for receiver).
    pub fn allocate(capacity: usize) -> NonNull<Self> {
        let capacity = capacity.next_power_of_two().max(2);

        // Use Vec for buffer - guarantees good alignment
        let buffer = ManuallyDrop::new(Vec::<T>::with_capacity(capacity)).as_mut_ptr();

        // Box the header
        let rb = Box::new(Self {
            head: CachePadded::new(AtomicUsize::new(0)),
            tail: CachePadded::new(AtomicUsize::new(0)),
            buffer,
            capacity,
            mask: capacity - 1,
            ref_count: AtomicUsize::new(2),
            sender_disconnected: AtomicBool::new(false),
            receiver_disconnected: AtomicBool::new(false),
        });

        // Leak the Box, we manage lifetime manually
        unsafe { NonNull::new_unchecked(Box::into_raw(rb)) }
    }

    #[inline]
    pub fn buffer(&self) -> *mut T {
        self.buffer
    }

    #[inline]
    pub fn mask(&self) -> usize {
        self.mask
    }

    #[inline]
    pub fn head_ptr(&self) -> *const AtomicUsize {
        &*self.head as *const AtomicUsize
    }

    #[inline]
    pub fn tail_ptr(&self) -> *const AtomicUsize {
        &*self.tail as *const AtomicUsize
    }

    /// Returns a pointer to the slot at the given index (automatically masked).
    #[inline(always)]
    fn slot_ptr(&self, index: usize) -> *mut T {
        unsafe { self.buffer.add(index & self.mask) }
    }

    /// Returns the capacity of the buffer.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    // === Index operations ===

    /// Loads the current head (consumer read position).
    #[inline(always)]
    pub fn load_head(&self) -> usize {
        self.head.load(Ordering::Acquire)
    }

    /// Loads the current tail (producer write position).
    #[inline(always)]
    pub fn load_tail(&self) -> usize {
        self.tail.load(Ordering::Acquire)
    }

    // === Disconnect operations ===

    /// Returns true if the sender has been dropped.
    #[inline(always)]
    pub fn is_sender_disconnected(&self) -> bool {
        self.sender_disconnected.load(Ordering::Relaxed)
    }

    /// Returns true if the receiver has been dropped.
    #[inline(always)]
    pub fn is_receiver_disconnected(&self) -> bool {
        self.receiver_disconnected.load(Ordering::Relaxed)
    }

    /// Marks the sender as disconnected.
    #[inline(always)]
    pub fn set_sender_disconnected(&self) {
        self.sender_disconnected.store(true, Ordering::Release);
    }

    /// Marks the receiver as disconnected.
    #[inline(always)]
    pub fn set_receiver_disconnected(&self) {
        self.receiver_disconnected.store(true, Ordering::Release);
    }

    // === Lifecycle ===

    /// Decrements the reference count and deallocates if it reaches zero.
    ///
    /// # Safety
    ///
    /// Must only be called when a handle (Sender or Receiver) is being dropped.
    /// The pointer must be valid and not used after this call returns.
    pub unsafe fn release(this: NonNull<Self>) {
        let inner = unsafe { this.as_ref() };

        if inner.ref_count.fetch_sub(1, Ordering::AcqRel) == 1 {
            unsafe {
                Self::drop_remaining_elements(this);

                // Reconstruct and drop the Vec to free buffer memory
                let _ = Vec::from_raw_parts(inner.buffer, 0, inner.capacity);

                // Reconstruct and drop the Box to free header
                let _ = Box::from_raw(this.as_ptr());
            }
        }
    }

    /// Drops any elements remaining in the queue.
    ///
    /// # Safety
    ///
    /// Must only be called during deallocation when we're the sole owner.
    unsafe fn drop_remaining_elements(this: NonNull<Self>) {
        let inner = unsafe { this.as_ref() };

        // These loads can be Relaxed since we're the only accessor
        let head = inner.head.load(Ordering::Relaxed);
        let tail = inner.tail.load(Ordering::Relaxed);

        // Drop elements in [head, tail) - head is read pos, tail is write pos
        for i in head..tail {
            unsafe {
                ptr::drop_in_place(inner.slot_ptr(i));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn allocation_and_release() {
        let rb = RingBuffer::<u64>::allocate(8);

        // Check capacity is power of two
        unsafe {
            assert_eq!(rb.as_ref().capacity(), 8);
            assert_eq!(rb.as_ref().mask, 7);
        }

        // Both release calls should succeed without double-free
        unsafe {
            RingBuffer::release(rb);
            RingBuffer::release(rb);
        }
    }
}
