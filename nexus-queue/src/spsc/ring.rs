//! The underlying ring buffer storage for SPSC queues.
//!
//! This is a single contiguous allocation containing:
//! - Header with metadata and synchronization primitives
//! - Cache-line padded indices
//! - The actual data buffer

use std::alloc::{Layout, alloc, dealloc, handle_alloc_error};
use std::cell::UnsafeCell;
use std::mem::MaybeUninit;
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
    // === Reference counting ===
    ref_count: AtomicUsize,

    // === Immutable configuration (set once at construction) ===
    capacity: usize,
    mask: usize,
    /// Cached pointer to the buffer (avoids recomputing base + offset on every access)
    buffer: *mut UnsafeCell<MaybeUninit<T>>,
    layout: Layout,

    // === Disconnect flags (only checked on slow path) ===
    sender_disconnected: AtomicBool,
    receiver_disconnected: AtomicBool,

    // === Cache-line padded indices ===
    /// Producer's write position. Updated by sender, read by receiver.
    head: CachePadded<AtomicUsize>,
    /// Consumer's read position. Updated by receiver, read by sender.
    tail: CachePadded<AtomicUsize>,
}

// Safety: RingBuffer can be shared across threads. The atomic operations
// provide the necessary synchronization.
unsafe impl<T: Send> Send for RingBuffer<T> {}
unsafe impl<T: Send> Sync for RingBuffer<T> {}

impl<T> RingBuffer<T> {
    /// Computes the memory layout for a ring buffer with the given capacity.
    ///
    /// Returns the total layout and the byte offset to the buffer.
    fn layout_for(capacity: usize) -> (Layout, usize) {
        let header = Layout::new::<Self>();

        let buffer = Layout::array::<UnsafeCell<MaybeUninit<T>>>(capacity)
            .expect("capacity too large for layout");

        let (layout, buffer_offset) = header.extend(buffer).expect("layout overflow");

        (layout.pad_to_align(), buffer_offset)
    }

    /// Allocates and initializes a new ring buffer with the given capacity.
    ///
    /// The capacity will be rounded up to the next power of two (minimum 2).
    /// The returned `NonNull` has a reference count of 2 (one for sender, one for receiver).
    pub fn allocate(capacity: usize) -> NonNull<Self> {
        let capacity = capacity.next_power_of_two().max(2);
        let (layout, buffer_offset) = Self::layout_for(capacity);

        // Safety: We're allocating with a valid layout
        let ptr = unsafe { alloc(layout) };
        if ptr.is_null() {
            handle_alloc_error(layout);
        }

        // Compute buffer pointer before writing the struct
        // Safety: ptr is valid and buffer_offset is within the allocation
        let buffer = unsafe { ptr.add(buffer_offset).cast::<UnsafeCell<MaybeUninit<T>>>() };

        let rb = ptr.cast::<Self>();

        // Safety: We just allocated this memory and it's properly aligned
        unsafe {
            ptr::write(
                rb,
                Self {
                    ref_count: AtomicUsize::new(2), // Sender + Receiver
                    capacity,
                    mask: capacity - 1,
                    buffer,
                    layout,
                    sender_disconnected: AtomicBool::new(false),
                    receiver_disconnected: AtomicBool::new(false),
                    head: CachePadded::new(AtomicUsize::new(0)),
                    tail: CachePadded::new(AtomicUsize::new(0)),
                },
            );

            // Buffer slots are left uninitialized (MaybeUninit)
            NonNull::new_unchecked(rb)
        }
    }

    /// Returns a pointer to the slot at the given index (automatically masked).
    #[inline]
    fn slot_ptr(&self, index: usize) -> *mut MaybeUninit<T> {
        // Safety: buffer is valid and masking ensures we're in bounds
        unsafe { (*self.buffer.add(index & self.mask)).get() }
    }

    /// Returns the capacity of the buffer.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    // === Index operations ===

    /// Loads the current head (producer write position).
    #[inline]
    pub fn load_head(&self) -> usize {
        self.head.load(Ordering::Acquire)
    }

    /// Loads the current tail (consumer read position).
    #[inline]
    pub fn load_tail(&self) -> usize {
        self.tail.load(Ordering::Acquire)
    }

    /// Publishes a new head position (called by producer after writing).
    #[inline]
    pub fn publish_head(&self, head: usize) {
        self.head.store(head, Ordering::Release);
    }

    /// Publishes a new tail position (called by consumer after reading).
    #[inline]
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
    #[inline]
    pub unsafe fn write_slot(&self, index: usize, value: T) {
        // Safety: Caller guarantees exclusive access and slot is empty
        unsafe {
            ptr::write(self.slot_ptr(index).cast::<T>(), value);
        }
    }

    /// Reads a value from the slot at the given index.
    ///
    /// # Safety
    ///
    /// Caller must ensure:
    /// - Exclusive read access to this slot
    /// - The slot contains a valid, initialized value
    #[inline]
    pub unsafe fn read_slot(&self, index: usize) -> T {
        // Safety: Caller guarantees exclusive access and slot contains valid data
        unsafe { ptr::read(self.slot_ptr(index).cast::<T>()) }
    }

    // === Disconnect operations ===

    /// Returns true if the sender has been dropped.
    #[inline]
    pub fn is_sender_disconnected(&self) -> bool {
        self.sender_disconnected.load(Ordering::Relaxed)
    }

    /// Returns true if the receiver has been dropped.
    #[inline]
    pub fn is_receiver_disconnected(&self) -> bool {
        self.receiver_disconnected.load(Ordering::Relaxed)
    }

    /// Marks the sender as disconnected.
    #[inline]
    pub fn set_sender_disconnected(&self) {
        self.sender_disconnected.store(true, Ordering::Release);
    }

    /// Marks the receiver as disconnected.
    #[inline]
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
        // Safety: Pointer is valid per caller's contract
        let inner = unsafe { this.as_ref() };

        // AcqRel ensures we see all writes from other threads before we
        // potentially deallocate, and our disconnect store is visible.
        if inner.ref_count.fetch_sub(1, Ordering::AcqRel) == 1 {
            // Last reference - clean up
            // Safety: We're the last owner
            unsafe {
                Self::drop_remaining_elements(this);

                let layout = inner.layout;
                ptr::drop_in_place(this.as_ptr());
                dealloc(this.as_ptr().cast(), layout);
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
                ptr::drop_in_place(inner.slot_ptr(i).cast::<T>());
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn layout_sanity() {
        let (layout, offset) = RingBuffer::<u64>::layout_for(8);
        assert!(layout.size() > 0);
        assert!(offset > 0);
        assert!(offset < layout.size());
    }

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
