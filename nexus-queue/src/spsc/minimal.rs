//! SPSC ring buffer modeled after rtrb's proven architecture.
//!
//! This is rtrb's design with one optimization: power-of-2 capacity
//! enables bitwise AND masking instead of branch-based index wrapping.
//!
//! Key design principles (from rtrb):
//! - Producer/Consumer are 24 bytes each (Arc + 2 cached indices)
//! - Single indirection through Arc to RingBuffer
//! - Contiguous memory layout for cache friendliness
//! - Cached indices to minimize atomic operations

use std::cell::Cell;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use crossbeam_utils::CachePadded;

/// Creates a new SPSC ring buffer with the given capacity.
///
/// Capacity is rounded up to the next power of two (minimum 2).
pub fn ring_buffer<T>(capacity: usize) -> (Producer<T>, Consumer<T>) {
    let capacity = capacity.next_power_of_two().max(2);

    // Allocate buffer
    let data_ptr = {
        let mut v = Vec::<T>::with_capacity(capacity);
        let ptr = v.as_mut_ptr();
        std::mem::forget(v);
        ptr
    };

    let rb = Arc::new(RingBuffer {
        data_ptr,
        capacity,
        mask: capacity - 1,
        head: CachePadded::new(AtomicUsize::new(0)),
        tail: CachePadded::new(AtomicUsize::new(0)),
    });

    (
        Producer {
            rb: rb.clone(),
            cached_head: Cell::new(0),
            cached_tail: Cell::new(0),
        },
        Consumer {
            rb,
            cached_head: Cell::new(0),
            cached_tail: Cell::new(0),
        },
    )
}

/// Shared ring buffer storage.
#[repr(C)]
struct RingBuffer<T> {
    /// Consumer's read position.
    head: CachePadded<AtomicUsize>,

    /// Producer's write position.
    tail: CachePadded<AtomicUsize>,

    /// Pointer to the data buffer.
    data_ptr: *mut T,

    /// Buffer capacity (always power of 2).
    capacity: usize,

    /// Mask for index wrapping (capacity - 1).
    mask: usize,

}

unsafe impl<T: Send> Send for RingBuffer<T> {}
unsafe impl<T: Send> Sync for RingBuffer<T> {}

impl<T> Drop for RingBuffer<T> {
    fn drop(&mut self) {
        // Drop any remaining elements
        let head = self.head.load(Ordering::Relaxed);
        let tail = self.tail.load(Ordering::Relaxed);

        let mut i = head;
        while i != tail {
            unsafe {
                self.data_ptr.add(i & self.mask).drop_in_place();
            }
            i = i.wrapping_add(1);
        }

        // Free the buffer
        unsafe {
            drop(Vec::from_raw_parts(self.data_ptr, 0, self.capacity));
        }
    }
}

/// The producer endpoint (24 bytes, same as rtrb).
pub struct Producer<T> {
    rb: Arc<RingBuffer<T>>,
    cached_head: Cell<usize>,
    cached_tail: Cell<usize>,
}

unsafe impl<T: Send> Send for Producer<T> {}

impl<T> Producer<T> {
    /// Push a value into the queue.
    #[inline]
    pub fn push(&mut self, value: T) -> Result<(), T> {
        let tail = self.cached_tail.get();

        // Fast path: check if there's space using cached head
        if tail.wrapping_sub(self.cached_head.get()) < self.rb.capacity {
            unsafe {
                self.rb.data_ptr.add(tail & self.rb.mask).write(value);
            }
            let next_tail = tail.wrapping_add(1);
            self.rb.tail.store(next_tail, Ordering::Release);
            self.cached_tail.set(next_tail);
            return Ok(());
        }

        // Slow path: refresh cached head
        let head = self.rb.head.load(Ordering::Acquire);
        self.cached_head.set(head);

        if tail.wrapping_sub(head) < self.rb.capacity {
            unsafe {
                self.rb.data_ptr.add(tail & self.rb.mask).write(value);
            }
            let next_tail = tail.wrapping_add(1);
            self.rb.tail.store(next_tail, Ordering::Release);
            self.cached_tail.set(next_tail);
            Ok(())
        } else {
            Err(value)
        }
    }

    /// Returns the capacity.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.rb.capacity
    }
}

/// The consumer endpoint (24 bytes, same as rtrb).
pub struct Consumer<T> {
    rb: Arc<RingBuffer<T>>,
    cached_head: Cell<usize>,
    cached_tail: Cell<usize>,
}

unsafe impl<T: Send> Send for Consumer<T> {}

impl<T> Consumer<T> {
    /// Pop a value from the queue.
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        let head = self.cached_head.get();

        // Fast path: check if there's data using cached tail
        if head != self.cached_tail.get() {
            let value = unsafe { self.rb.data_ptr.add(head & self.rb.mask).read() };
            let next_head = head.wrapping_add(1);
            self.rb.head.store(next_head, Ordering::Release);
            self.cached_head.set(next_head);
            return Some(value);
        }

        // Slow path: refresh cached tail
        let tail = self.rb.tail.load(Ordering::Acquire);
        self.cached_tail.set(tail);

        if head != tail {
            let value = unsafe { self.rb.data_ptr.add(head & self.rb.mask).read() };
            let next_head = head.wrapping_add(1);
            self.rb.head.store(next_head, Ordering::Release);
            self.cached_head.set(next_head);
            Some(value)
        } else {
            None
        }
    }

    /// Returns the capacity.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.rb.capacity
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn struct_sizes() {
        assert_eq!(std::mem::size_of::<Producer<u64>>(), 24);
        assert_eq!(std::mem::size_of::<Consumer<u64>>(), 24);
    }

    #[test]
    fn basic_push_pop() {
        let (mut producer, mut consumer) = ring_buffer::<u64>(8);

        producer.push(1).unwrap();
        producer.push(2).unwrap();
        producer.push(3).unwrap();

        assert_eq!(consumer.pop(), Some(1));
        assert_eq!(consumer.pop(), Some(2));
        assert_eq!(consumer.pop(), Some(3));
        assert_eq!(consumer.pop(), None);
    }

    #[test]
    fn full_buffer() {
        let (mut producer, mut consumer) = ring_buffer::<u64>(4);

        producer.push(1).unwrap();
        producer.push(2).unwrap();
        producer.push(3).unwrap();
        producer.push(4).unwrap();

        assert_eq!(producer.push(5), Err(5));

        assert_eq!(consumer.pop(), Some(1));
        producer.push(5).unwrap();
    }

    #[test]
    fn wraparound() {
        let (mut producer, mut consumer) = ring_buffer::<u64>(4);

        for lap in 0..100 {
            for i in 0..4 {
                producer.push(lap * 4 + i).unwrap();
            }
            for i in 0..4 {
                assert_eq!(consumer.pop(), Some(lap * 4 + i));
            }
        }
    }

    #[test]
    fn cross_thread() {
        use std::thread;

        let (mut producer, mut consumer) = ring_buffer::<u64>(1024);

        let handle = thread::spawn(move || {
            for i in 0..100_000u64 {
                while producer.push(i).is_err() {
                    std::hint::spin_loop();
                }
            }
        });

        let mut expected = 0u64;
        while expected < 100_000 {
            if let Some(val) = consumer.pop() {
                assert_eq!(val, expected);
                expected += 1;
            }
        }

        handle.join().unwrap();
    }
}
