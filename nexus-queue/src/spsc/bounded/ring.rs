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
/// │   ref_count, capacity, mask, buffer, layout           │
/// │   sender_disconnected, receiver_disconnected          │
/// ├───────────────────────────────────────────────────────┤
/// │ head (cache-line padded) - producer write position    │
/// ├───────────────────────────────────────────────────────┤
/// │ tail (cache-line padded) - consumer read position     │
/// ├───────────────────────────────────────────────────────┤
/// │ Buffer: [MaybeUninit<T>; capacity]                    │
/// └───────────────────────────────────────────────────────┘
/// ```
#[repr(C)]
pub struct RingBuffer<T> {
    // === Hot path data - put first for cache locality ===
    // === Cache-line padded indices ===
    /// Producer's write position. Updated by sender, read by receiver.
    head: CachePadded<AtomicUsize>,
    /// Consumer's read position. Updated by receiver, read by sender.
    tail: CachePadded<AtomicUsize>,

    /// Cached pointer to the buffer (avoids recomputing base + offset on every access)
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

    /// Returns a pointer to the slot at the given index (automatically masked).
    #[inline(always)]
    fn slot_ptr(&self, index: usize) -> *mut T {
        // Safety: buffer is valid and masking ensures we're in bounds
        unsafe { self.buffer.add(index & self.mask) }
    }

    /// Returns the capacity of the buffer.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    // === Index operations ===

    /// Loads the current head (producer write position).
    #[inline(always)]
    pub fn load_head(&self) -> usize {
        self.head.load(Ordering::Acquire)
    }

    /// Loads the current tail (consumer read position).
    #[inline(always)]
    pub fn load_tail(&self) -> usize {
        self.tail.load(Ordering::Acquire)
    }

    /// Publishes a new head position (called by producer after writing).
    #[inline(always)]
    pub fn publish_head(&self, head: usize) {
        self.head.store(head, Ordering::Release);
    }

    /// Publishes a new tail position (called by consumer after reading).
    #[inline(always)]
    pub fn publish_tail(&self, tail: usize) {
        self.tail.store(tail, Ordering::Release);
    }

    // === Slot operations ===

    /// Writes a value into the slot at the given index.
    ///
    /// # Safety
    ///
    /// Caller must ensure:
    /// - Exclusive write access to this slot
    /// - The slot is not currently occupied (no live value to drop)
    #[inline(always)]
    pub unsafe fn write_slot(&self, index: usize, value: T) {
        // Safety: Caller guarantees exclusive access and slot is empty
        unsafe {
            self.slot_ptr(index).write(value);
        }
    }

    /// Reads a value from the slot at the given index.
    ///
    /// # Safety
    ///
    /// Caller must ensure:
    /// - Exclusive read access to this slot
    /// - The slot contains a valid, initialized value
    #[inline(always)]
    pub unsafe fn read_slot(&self, index: usize) -> T {
        // Safety: Caller guarantees exclusive access and slot contains valid data
        unsafe { self.slot_ptr(index).read() }
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
        let tail = inner.tail.load(Ordering::Relaxed);
        let head = inner.head.load(Ordering::Relaxed);

        // Drop elements in [tail, head)
        for i in tail..head {
            // Safety: These slots contain valid data that was written but never read
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

    #[test]
    fn write_and_read() {
        let rb = RingBuffer::<u64>::allocate(8);

        unsafe {
            let inner = rb.as_ref();

            // Write some values
            inner.write_slot(0, 42);
            inner.write_slot(1, 43);
            inner.write_slot(7, 49); // Test wrapping

            // Read them back
            assert_eq!(inner.read_slot(0), 42);
            assert_eq!(inner.read_slot(1), 43);
            assert_eq!(inner.read_slot(7), 49);

            // Cleanup
            RingBuffer::release(rb);
            RingBuffer::release(rb);
        }
    }

    #[test]
    fn index_masking() {
        let rb = RingBuffer::<u64>::allocate(4);

        unsafe {
            let inner = rb.as_ref();

            // Write at index 0 and index 4 (should be same slot)
            inner.write_slot(0, 100);
            let val = inner.read_slot(0);
            assert_eq!(val, 100);

            inner.write_slot(4, 200);
            let val = inner.read_slot(4);
            assert_eq!(val, 200);

            // Both should access the same underlying slot (index & mask = index & 3)
            inner.write_slot(0, 300);
            let val = inner.read_slot(4); // Should read from slot 0
            assert_eq!(val, 300);

            RingBuffer::release(rb);
            RingBuffer::release(rb);
        }
    }
}
