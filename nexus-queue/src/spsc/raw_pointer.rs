//! Raw SPSC ring buffer with cached slot pointers.
//!
//! Same as `raw` but caches the pointer to the next slot to read/write,
//! rather than computing `buffer.add(index & mask)` on each operation.
//! This gives the CPU more opportunity to prefetch the next slot.
//!
//! # Example
//!
//! ```
//! use nexus_queue::spsc::raw_pointer;
//!
//! let (mut producer, mut consumer) = raw_pointer::ring_buffer::<u64>(1024);
//!
//! producer.push(42).unwrap();
//! assert_eq!(consumer.pop().unwrap(), 42);
//! ```

use std::cell::Cell;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use crossbeam_utils::CachePadded;

/// Creates a new raw SPSC ring buffer with the given capacity.
///
/// Returns a `(Producer, Consumer)` pair. The actual capacity will be
/// rounded up to the next power of two (minimum 2).
pub fn ring_buffer<T>(capacity: usize) -> (Producer<T>, Consumer<T>) {
    let capacity = capacity.next_power_of_two().max(2);
    let mask = capacity - 1;

    let buffer_ptr = std::mem::ManuallyDrop::new(Vec::<T>::with_capacity(capacity)).as_mut_ptr();

    let inner = Arc::new(Inner {
        head: CachePadded::new(AtomicUsize::new(0)),
        tail: CachePadded::new(AtomicUsize::new(0)),
        buffer: buffer_ptr,
        capacity,
        mask,
    });

    let head_atomic = &*inner.head as *const AtomicUsize;
    let tail_atomic = &*inner.tail as *const AtomicUsize;

    (
        Producer {
            inner: Arc::clone(&inner),
            buffer: buffer_ptr,
            mask,
            head_atomic,
            tail_atomic,
            local_head: Cell::new(0),
            cached_tail: Cell::new(0),
            next_slot: Cell::new(buffer_ptr), // Start at slot 0
        },
        Consumer {
            inner,
            buffer: buffer_ptr,
            mask,
            tail_atomic,
            head_atomic,
            local_tail: Cell::new(0),
            cached_head: Cell::new(0),
            next_slot: Cell::new(buffer_ptr), // Start at slot 0
        },
    )
}

struct Inner<T> {
    head: CachePadded<AtomicUsize>,
    tail: CachePadded<AtomicUsize>,
    buffer: *mut T,
    capacity: usize,
    mask: usize,
}

unsafe impl<T: Send> Send for Inner<T> {}
unsafe impl<T: Send> Sync for Inner<T> {}

/// The producer half of a raw ring buffer.
pub struct Producer<T> {
    inner: Arc<Inner<T>>,
    buffer: *mut T,
    mask: usize,
    head_atomic: *const AtomicUsize,
    tail_atomic: *const AtomicUsize,
    local_head: Cell<usize>,
    cached_tail: Cell<usize>,
    /// Cached pointer to the next slot to write to
    next_slot: Cell<*mut T>,
}

unsafe impl<T: Send> Send for Producer<T> {}

impl<T> Producer<T> {
    /// Attempts to push a value into the ring buffer.
    ///
    /// Returns `Err(value)` if the buffer is full.
    #[inline]
    pub fn push(&mut self, value: T) -> Result<(), T> {
        let head = self.local_head.get();

        // Fast path: check cached tail
        if head.wrapping_sub(self.cached_tail.get()) <= self.mask {
            // Write to the cached slot pointer
            unsafe {
                self.next_slot.get().write(value);
            }
            let next_head = head.wrapping_add(1);
            self.local_head.set(next_head);
            // Cache the NEXT slot pointer for the next push
            self.next_slot
                .set(unsafe { self.buffer.add(next_head & self.mask) });
            unsafe { (*self.head_atomic).store(next_head, Ordering::Release) };
            return Ok(());
        }

        self.push_slow(head, value)
    }

    #[cold]
    fn push_slow(&mut self, head: usize, value: T) -> Result<(), T> {
        // Refresh cached tail
        let tail = unsafe { (*self.tail_atomic).load(Ordering::Acquire) };
        self.cached_tail.set(tail);

        if head.wrapping_sub(tail) <= self.mask {
            unsafe {
                self.next_slot.get().write(value);
            }
            let next_head = head.wrapping_add(1);
            self.local_head.set(next_head);
            self.next_slot
                .set(unsafe { self.buffer.add(next_head & self.mask) });
            unsafe { (*self.head_atomic).store(next_head, Ordering::Release) };
            Ok(())
        } else {
            Err(value)
        }
    }

    /// Returns the capacity of the ring buffer.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.mask + 1
    }

    /// Returns the number of elements currently in the buffer.
    #[inline]
    pub fn len(&self) -> usize {
        let head = unsafe { (*self.head_atomic).load(Ordering::Relaxed) };
        let tail = unsafe { (*self.tail_atomic).load(Ordering::Relaxed) };
        head.wrapping_sub(tail)
    }

    /// Returns `true` if the buffer is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// The consumer half of a raw ring buffer.
pub struct Consumer<T> {
    inner: Arc<Inner<T>>,
    buffer: *mut T,
    mask: usize,
    tail_atomic: *const AtomicUsize,
    head_atomic: *const AtomicUsize,
    local_tail: Cell<usize>,
    cached_head: Cell<usize>,
    /// Cached pointer to the next slot to read from
    next_slot: Cell<*mut T>,
}

unsafe impl<T: Send> Send for Consumer<T> {}

impl<T> Consumer<T> {
    /// Attempts to pop a value from the ring buffer.
    ///
    /// Returns `None` if the buffer is empty.
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        let tail = self.local_tail.get();

        // Fast path: check cached head
        if tail != self.cached_head.get() {
            // Read from the cached slot pointer
            let value = unsafe { self.next_slot.get().read() };
            let next_tail = tail.wrapping_add(1);
            self.local_tail.set(next_tail);
            // Cache the NEXT slot pointer for the next pop
            self.next_slot
                .set(unsafe { self.buffer.add(next_tail & self.mask) });
            unsafe { (*self.tail_atomic).store(next_tail, Ordering::Release) };
            return Some(value);
        }

        self.pop_slow(tail)
    }

    #[cold]
    fn pop_slow(&mut self, tail: usize) -> Option<T> {
        // Refresh cached head
        let head = unsafe { (*self.head_atomic).load(Ordering::Acquire) };
        self.cached_head.set(head);

        if tail != head {
            let value = unsafe { self.next_slot.get().read() };
            let next_tail = tail.wrapping_add(1);
            self.local_tail.set(next_tail);
            self.next_slot
                .set(unsafe { self.buffer.add(next_tail & self.mask) });
            unsafe { (*self.tail_atomic).store(next_tail, Ordering::Release) };
            Some(value)
        } else {
            None
        }
    }

    /// Returns the capacity of the ring buffer.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.mask + 1
    }

    /// Returns the number of elements currently in the buffer.
    #[inline]
    pub fn len(&self) -> usize {
        let head = unsafe { (*self.head_atomic).load(Ordering::Relaxed) };
        let tail = unsafe { (*self.tail_atomic).load(Ordering::Relaxed) };
        head.wrapping_sub(tail)
    }

    /// Returns `true` if the buffer is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<T> Drop for Inner<T> {
    fn drop(&mut self) {
        let head = self.head.load(Ordering::Relaxed);
        let tail = self.tail.load(Ordering::Relaxed);

        for i in tail..head {
            unsafe {
                self.buffer.add(i & self.mask).drop_in_place();
            }
        }

        unsafe {
            let _ = Vec::from_raw_parts(self.buffer, 0, self.capacity);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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

        // Fill and drain multiple times to test wraparound
        for round in 0..10 {
            for i in 0..4 {
                producer.push(round * 4 + i).unwrap();
            }
            for i in 0..4 {
                assert_eq!(consumer.pop(), Some(round * 4 + i));
            }
        }
    }

    #[test]
    fn cross_thread() {
        use std::thread;

        let (mut producer, mut consumer) = ring_buffer::<u64>(1024);

        let handle = thread::spawn(move || {
            for i in 0..10_000 {
                while producer.push(i).is_err() {
                    std::hint::spin_loop();
                }
            }
        });

        let mut received = 0u64;
        let mut expected = 0u64;
        while expected < 10_000 {
            if let Some(val) = consumer.pop() {
                assert_eq!(val, expected);
                expected += 1;
                received += 1;
            }
        }

        handle.join().unwrap();
        assert_eq!(received, 10_000);
    }
}
