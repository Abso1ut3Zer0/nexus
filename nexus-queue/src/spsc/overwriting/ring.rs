//! Ring buffer implementation for overwriting SPSC queue.
//!
//! Unlike the bounded SPSC, this ring uses per-slot lap counters to detect
//! when the consumer has been lapped by the producer.

use std::alloc::{self, Layout};
use std::cell::UnsafeCell;
use std::mem::MaybeUninit;
use std::ptr::{self, NonNull};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

use crossbeam_utils::CachePadded;

/// A slot in the ring buffer with a lap counter.
///
/// The lap counter tracks which "lap" around the ring this slot was written on.
/// This allows the consumer to detect if it was lapped by the producer.
#[repr(C)]
struct Slot<T> {
    /// The lap number when this slot was last written.
    ///
    /// - `lap == 0` means never written or consumed
    /// - `lap == n` means written during lap `n` (1-indexed)
    lap: AtomicUsize,
    /// The actual data.
    data: UnsafeCell<MaybeUninit<T>>,
}

/// Ring buffer backing storage for overwriting SPSC queue.
///
/// Memory layout (single allocation):
/// ```text
/// ┌─────────────────────────────────────────────┐
/// │ RingBuffer<T> (header)                      │
/// │   head, tail, capacity, mask, etc.          │
/// ├─────────────────────────────────────────────┤
/// │ Slot[0]: { lap, data }                      │
/// │ Slot[1]: { lap, data }                      │
/// │ ...                                         │
/// │ Slot[capacity-1]: { lap, data }             │
/// └─────────────────────────────────────────────┘
/// ```
///
/// Queue contains elements in range [head, tail).
/// - Producer writes at tail, then increments tail
/// - Consumer reads at head, then increments head
#[repr(C)]
pub struct RingBuffer<T> {
    // === Cache line 1: Consumer-owned ===
    /// Consumer's read position (monotonically increasing).
    head: CachePadded<AtomicUsize>,

    // === Cache line 2: Producer-owned ===
    /// Producer's write position (monotonically increasing).
    /// In overwriting mode, this advances even when buffer is full.
    tail: CachePadded<AtomicUsize>,

    // === Metadata (read-only after creation) ===
    /// Capacity of the buffer (power of 2).
    capacity: usize,
    /// Bitmask for fast modulo: `index & mask == index % capacity`.
    mask: usize,
    /// Pointer to the slot array (flexible array member pattern).
    buffer: NonNull<Slot<T>>,

    // === Liveness tracking ===
    /// True if sender has been dropped.
    sender_disconnected: AtomicBool,
    /// True if receiver has been dropped.
    receiver_disconnected: AtomicBool,
}

// Safety: RingBuffer can be shared between threads.
// The atomic operations and slot-level synchronization ensure safe access.
unsafe impl<T: Send> Send for RingBuffer<T> {}
unsafe impl<T: Send> Sync for RingBuffer<T> {}

impl<T> RingBuffer<T> {
    /// Allocates a new ring buffer with the given capacity.
    ///
    /// Capacity will be rounded up to the next power of 2.
    ///
    /// # Panics
    ///
    /// Panics if capacity is 0 or if allocation fails.
    pub fn allocate(min_capacity: usize) -> NonNull<Self> {
        assert!(min_capacity > 0, "capacity must be non-zero");

        // Round up to power of 2
        let capacity = min_capacity.next_power_of_two();
        let mask = capacity - 1;

        // Calculate layout for header + slots
        let header_layout = Layout::new::<RingBuffer<T>>();
        let slot_layout = Layout::array::<Slot<T>>(capacity).expect("capacity overflow");
        let (layout, slot_offset) = header_layout.extend(slot_layout).expect("layout overflow");

        // Allocate
        let ptr = unsafe { alloc::alloc_zeroed(layout) };
        if ptr.is_null() {
            alloc::handle_alloc_error(layout);
        }

        // Initialize header
        let ring = ptr as *mut RingBuffer<T>;
        let buffer_ptr = unsafe { ptr.add(slot_offset) as *mut Slot<T> };

        unsafe {
            ptr::write(
                ring,
                RingBuffer {
                    head: CachePadded::new(AtomicUsize::new(0)),
                    tail: CachePadded::new(AtomicUsize::new(0)),
                    capacity,
                    mask,
                    buffer: NonNull::new_unchecked(buffer_ptr),
                    sender_disconnected: AtomicBool::new(false),
                    receiver_disconnected: AtomicBool::new(false),
                },
            );

            // Initialize all slots with lap=0 (never written)
            for i in 0..capacity {
                let slot = buffer_ptr.add(i);
                ptr::write(
                    slot,
                    Slot {
                        lap: AtomicUsize::new(0),
                        data: UnsafeCell::new(MaybeUninit::uninit()),
                    },
                );
            }
        }

        unsafe { NonNull::new_unchecked(ring) }
    }

    /// Deallocates the ring buffer.
    ///
    /// # Safety
    ///
    /// - Must only be called once
    /// - No other references to the ring buffer may exist
    /// - Caller must ensure all data has been properly dropped
    pub unsafe fn deallocate(this: NonNull<Self>) {
        let ring = unsafe { this.as_ref() };
        let capacity = ring.capacity;

        let header_layout = Layout::new::<RingBuffer<T>>();
        let slot_layout = Layout::array::<Slot<T>>(capacity).expect("capacity overflow");
        let (layout, _) = header_layout.extend(slot_layout).expect("layout overflow");

        unsafe {
            alloc::dealloc(this.as_ptr() as *mut u8, layout);
        }
    }

    // === Accessors ===

    #[inline]
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    #[inline]
    fn slot(&self, index: usize) -> &Slot<T> {
        unsafe { &*self.buffer.as_ptr().add(index & self.mask) }
    }

    /// Returns the current lap for a given absolute position.
    #[inline]
    pub fn lap_of(&self, pos: usize) -> usize {
        pos / self.capacity + 1 // 1-indexed laps
    }

    // === Consumer operations (head) ===

    /// Loads the current head position (consumer read position).
    #[inline]
    pub fn load_head(&self) -> usize {
        self.head.load(Ordering::Acquire)
    }

    /// Returns a pointer to the head atomic for direct access.
    #[inline]
    pub fn head_ptr(&self) -> *const AtomicUsize {
        &*self.head as *const AtomicUsize
    }

    /// Attempts to read from the given position.
    ///
    /// Returns `Some((value, lagged))` if data is available, where `lagged` is
    /// the number of messages that were lost due to lapping.
    ///
    /// Returns `None` if the slot hasn't been written yet.
    ///
    /// # Safety
    ///
    /// - Only one consumer may call this
    /// - `head` must be the consumer's current position
    #[inline]
    pub unsafe fn try_read(&self, head: usize) -> Option<(T, usize)> {
        let slot = self.slot(head);
        let expected_lap = self.lap_of(head);

        let slot_lap = slot.lap.load(Ordering::Acquire);

        if slot_lap == 0 || slot_lap < expected_lap {
            // Not yet written, or we're somehow ahead (shouldn't happen)
            return None;
        }

        // Check if we were lapped
        let lagged = if slot_lap > expected_lap {
            // Producer lapped us!
            // Calculate how many full laps + partial
            let laps_behind = slot_lap - expected_lap;
            laps_behind * self.capacity
        } else {
            0
        };

        // Read the value
        let value = unsafe { (*slot.data.get()).assume_init_read() };

        // Mark slot as consumed (lap 0 means empty/consumed)
        slot.lap.store(0, Ordering::Release);

        Some((value, lagged))
    }

    /// Calculates the new head position after detecting a lap.
    ///
    /// When consumer is lapped, it needs to jump to the oldest valid position.
    #[inline]
    pub fn catch_up_head(&self) -> usize {
        // The oldest valid position is (tail - capacity + 1)
        // But we need to be careful about the race - tail may have moved
        let tail = self.tail.load(Ordering::Acquire);
        if tail >= self.capacity {
            tail - self.capacity + 1
        } else {
            0
        }
    }

    // === Producer operations (tail) ===

    /// Loads the current tail position (producer write position).
    #[inline]
    pub fn load_tail(&self) -> usize {
        self.tail.load(Ordering::Relaxed)
    }

    /// Returns a pointer to the tail atomic for direct access.
    #[inline]
    pub fn tail_ptr(&self) -> *const AtomicUsize {
        &*self.tail as *const AtomicUsize
    }

    /// Writes a value to the given slot index, potentially overwriting.
    ///
    /// Returns the old value if there was unconsumed data in the slot.
    ///
    /// # Safety
    ///
    /// - Caller must have exclusive access to write to this slot position
    /// - `tail` must be the position being written to
    #[inline]
    pub unsafe fn write_and_publish(&self, tail: usize, value: T) -> Option<T> {
        let slot = self.slot(tail);
        let lap = self.lap_of(tail);

        // If slot has existing unconsumed data, read it out before overwriting
        let old_lap = slot.lap.load(Ordering::Acquire);
        let old_value = if old_lap > 0 {
            // There's unconsumed data - take ownership of it
            Some(unsafe { (*slot.data.get()).assume_init_read() })
        } else {
            None
        };

        // Write new value
        unsafe {
            (*slot.data.get()).write(value);
        }

        // Publish with new lap number
        slot.lap.store(lap, Ordering::Release);

        old_value
    }

    // === Liveness tracking ===

    #[inline]
    pub fn is_sender_disconnected(&self) -> bool {
        self.sender_disconnected.load(Ordering::Acquire)
    }

    #[inline]
    pub fn set_sender_disconnected(&self) {
        self.sender_disconnected.store(true, Ordering::Release);
    }

    #[inline]
    pub fn is_receiver_disconnected(&self) -> bool {
        self.receiver_disconnected.load(Ordering::Relaxed)
    }

    #[inline]
    pub fn set_receiver_disconnected(&self) {
        self.receiver_disconnected.store(true, Ordering::Release);
    }

    // === Cleanup ===

    /// Drops all remaining elements in the buffer.
    ///
    /// # Safety
    ///
    /// Must only be called during buffer destruction when no other
    /// threads are accessing the buffer.
    pub unsafe fn drop_remaining(&self, head: usize, tail: usize) {
        // Drop elements from head to tail (head is read pos, tail is write pos)
        for pos in head..tail {
            let slot = self.slot(pos);
            let slot_lap = slot.lap.load(Ordering::Relaxed);
            let expected_lap = self.lap_of(pos);

            // Only drop if this slot has valid data for this position
            if slot_lap == expected_lap {
                unsafe {
                    let data_ptr = (*slot.data.get()).as_mut_ptr();
                    ptr::drop_in_place(data_ptr);
                }
            }
        }
    }
}
