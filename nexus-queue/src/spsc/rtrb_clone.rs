//! SPSC ring buffer - exact rtrb clone with pow2 capacity.
//!
//! This matches rtrb's implementation exactly, only difference is
//! capacity is rounded to power of 2.

use std::cell::Cell;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use crossbeam_utils::CachePadded;

/// Creates a new SPSC ring buffer.
pub fn ring_buffer<T>(capacity: usize) -> (Producer<T>, Consumer<T>) {
    let capacity = capacity.next_power_of_two().max(2);

    let data_ptr = {
        let mut v = Vec::<T>::with_capacity(capacity);
        let ptr = v.as_mut_ptr();
        std::mem::forget(v);
        ptr
    };

    let rb = Arc::new(RingBuffer {
        head: CachePadded::new(AtomicUsize::new(0)),
        tail: CachePadded::new(AtomicUsize::new(0)),
        data_ptr,
        capacity,
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

struct RingBuffer<T> {
    head: CachePadded<AtomicUsize>,
    tail: CachePadded<AtomicUsize>,
    data_ptr: *mut T,
    capacity: usize,
}

unsafe impl<T: Send> Send for RingBuffer<T> {}
unsafe impl<T: Send> Sync for RingBuffer<T> {}

impl<T> RingBuffer<T> {
    // rtrb's exact collapse_position logic
    #[inline(always)]
    fn collapse_position(&self, pos: usize) -> usize {
        if pos < self.capacity {
            pos
        } else {
            pos - self.capacity
        }
    }

    // rtrb's exact increment logic
    #[inline(always)]
    fn increment(&self, pos: usize) -> usize {
        if pos < 2 * self.capacity - 1 {
            pos + 1
        } else {
            0
        }
    }

    // rtrb's exact distance logic
    #[inline(always)]
    fn distance(&self, a: usize, b: usize) -> usize {
        if a <= b {
            b - a
        } else {
            2 * self.capacity - a + b
        }
    }
}

impl<T> Drop for RingBuffer<T> {
    fn drop(&mut self) {
        let mut head = self.head.load(Ordering::Relaxed);
        let tail = self.tail.load(Ordering::Relaxed);

        while head != tail {
            unsafe {
                self.data_ptr
                    .add(self.collapse_position(head))
                    .drop_in_place();
            }
            head = self.increment(head);
        }

        unsafe {
            drop(Vec::from_raw_parts(self.data_ptr, 0, self.capacity));
        }
    }
}

pub struct Producer<T> {
    rb: Arc<RingBuffer<T>>,
    cached_head: Cell<usize>,
    cached_tail: Cell<usize>,
}

unsafe impl<T: Send> Send for Producer<T> {}

impl<T> Producer<T> {
    #[inline]
    pub fn push(&mut self, value: T) -> Result<(), T> {
        let tail = self.cached_tail.get();

        // Fast path
        if self.rb.distance(self.cached_head.get(), tail) < self.rb.capacity {
            unsafe {
                self.rb
                    .data_ptr
                    .add(self.rb.collapse_position(tail))
                    .write(value);
            }
            let next_tail = self.rb.increment(tail);
            self.rb.tail.store(next_tail, Ordering::Release);
            self.cached_tail.set(next_tail);
            return Ok(());
        }

        // Slow path
        let head = self.rb.head.load(Ordering::Acquire);
        self.cached_head.set(head);

        if self.rb.distance(head, tail) < self.rb.capacity {
            unsafe {
                self.rb
                    .data_ptr
                    .add(self.rb.collapse_position(tail))
                    .write(value);
            }
            let next_tail = self.rb.increment(tail);
            self.rb.tail.store(next_tail, Ordering::Release);
            self.cached_tail.set(next_tail);
            Ok(())
        } else {
            Err(value)
        }
    }

    #[inline]
    pub fn capacity(&self) -> usize {
        self.rb.capacity
    }
}

pub struct Consumer<T> {
    rb: Arc<RingBuffer<T>>,
    cached_head: Cell<usize>,
    cached_tail: Cell<usize>,
}

unsafe impl<T: Send> Send for Consumer<T> {}

impl<T> Consumer<T> {
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        let head = self.cached_head.get();

        // Fast path
        if head != self.cached_tail.get() {
            let value = unsafe { self.rb.data_ptr.add(self.rb.collapse_position(head)).read() };
            let next_head = self.rb.increment(head);
            self.rb.head.store(next_head, Ordering::Release);
            self.cached_head.set(next_head);
            return Some(value);
        }

        // Slow path
        let tail = self.rb.tail.load(Ordering::Acquire);
        self.cached_tail.set(tail);

        if head != tail {
            let value = unsafe { self.rb.data_ptr.add(self.rb.collapse_position(head)).read() };
            let next_head = self.rb.increment(head);
            self.rb.head.store(next_head, Ordering::Release);
            self.cached_head.set(next_head);
            Some(value)
        } else {
            None
        }
    }

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
    fn basic() {
        let (mut p, mut c) = ring_buffer::<u64>(8);
        p.push(1).unwrap();
        p.push(2).unwrap();
        assert_eq!(c.pop(), Some(1));
        assert_eq!(c.pop(), Some(2));
        assert_eq!(c.pop(), None);
    }

    #[test]
    fn full() {
        let (mut p, mut c) = ring_buffer::<u64>(4);
        p.push(1).unwrap();
        p.push(2).unwrap();
        p.push(3).unwrap();
        p.push(4).unwrap();
        assert!(p.push(5).is_err());
        c.pop();
        p.push(5).unwrap();
    }

    #[test]
    fn cross_thread() {
        use std::thread;
        let (mut p, mut c) = ring_buffer::<u64>(1024);

        let h = thread::spawn(move || {
            for i in 0..100_000u64 {
                while p.push(i).is_err() {
                    std::hint::spin_loop();
                }
            }
        });

        let mut expected = 0u64;
        while expected < 100_000 {
            if let Some(v) = c.pop() {
                assert_eq!(v, expected);
                expected += 1;
            }
        }
        h.join().unwrap();
    }
}
