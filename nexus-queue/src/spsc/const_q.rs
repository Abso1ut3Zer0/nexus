//! Const-generic SPSC ring buffer.
//!
//! Zero-cost abstractions: capacity and mask are compile-time constants,
//! buffer is inline, and hot-path pointers are cached to avoid Arc deref.
//!
//! # Example
//!
//! ```
//! use nexus_queue::spsc::bounded::RingBuffer;
//!
//! // Capacity must be a power of 2
//! let (mut tx, mut rx) = RingBuffer::<u64, 1024>::new();
//!
//! tx.push(42).unwrap();
//! assert_eq!(rx.pop(), Some(42));
//! ```
//!
//! # Compile-Time Enforcement
//!
//! Non-power-of-2 capacities will fail to compile:
//! ```compile_fail
//! use nexus_queue::spsc::bounded::RingBuffer;
//! let (tx, rx) = RingBuffer::<u64, 100>::new(); // ERROR: 100 is not a power of 2
//! ```

use std::cell::Cell;
use std::mem::MaybeUninit;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use crossbeam_utils::CachePadded;

/// A fixed-capacity SPSC ring buffer.
///
/// `N` must be a power of 2 (enforced at compile time).
#[repr(C)]
pub struct RingBuffer<T, const N: usize> {
    /// Producer's write position.
    head: CachePadded<AtomicUsize>,
    /// Consumer's read position.
    tail: CachePadded<AtomicUsize>,
    /// Inline buffer - no pointer indirection!
    buffer: [MaybeUninit<T>; N],
}

impl<T, const N: usize> RingBuffer<T, N> {
    /// Mask for index wrapping. Compile-time constant!
    const MASK: usize = N - 1;

    /// Compile-time assertion that N is a power of 2.
    const _ASSERT_POW2: () = assert!(N > 0 && (N & (N - 1)) == 0, "N must be a power of 2");

    /// Creates a new ring buffer, returning (Producer, Consumer).
    pub fn new() -> (Producer<T, N>, Consumer<T, N>) {
        // Force the compile-time assertion to be evaluated
        let _ = Self::_ASSERT_POW2;

        let rb = Arc::new(Self {
            head: CachePadded::new(AtomicUsize::new(0)),
            tail: CachePadded::new(AtomicUsize::new(0)),
            // Safety: MaybeUninit doesn't require initialization
            buffer: unsafe { MaybeUninit::uninit().assume_init() },
        });

        // Cache raw pointers to avoid Arc deref on hot path
        let head_ptr = &*rb.head as *const AtomicUsize;
        let tail_ptr = &*rb.tail as *const AtomicUsize;
        let buffer_ptr = rb.buffer.as_ptr();

        (
            Producer {
                rb: Arc::clone(&rb),
                buffer: buffer_ptr,
                head: head_ptr,
                tail: tail_ptr,
                local_head: Cell::new(0),
                cached_tail: Cell::new(0),
            },
            Consumer {
                rb,
                buffer: buffer_ptr,
                head: head_ptr,
                tail: tail_ptr,
                local_tail: Cell::new(0),
                cached_head: Cell::new(0),
            },
        )
    }
}

impl<T, const N: usize> Drop for RingBuffer<T, N> {
    fn drop(&mut self) {
        let head = self.head.load(Ordering::Relaxed);
        let tail = self.tail.load(Ordering::Relaxed);

        // Drop remaining elements
        let mut i = tail;
        while i != head {
            unsafe {
                let ptr = self.buffer.as_ptr().add(i & Self::MASK) as *mut T;
                ptr.drop_in_place();
            }
            i = i.wrapping_add(1);
        }
    }
}

// Safety: RingBuffer is Send+Sync if T is Send
unsafe impl<T: Send, const N: usize> Send for RingBuffer<T, N> {}
unsafe impl<T: Send, const N: usize> Sync for RingBuffer<T, N> {}

/// Producer half of the ring buffer.
///
/// Caches pointers to avoid Arc deref on hot path.
pub struct Producer<T, const N: usize> {
    rb: Arc<RingBuffer<T, N>>,
    /// Cached buffer pointer.
    buffer: *const MaybeUninit<T>,
    /// Cached head atomic pointer.
    head: *const AtomicUsize,
    /// Cached tail atomic pointer.
    tail: *const AtomicUsize,
    /// Our write position.
    local_head: Cell<usize>,
    /// Cached consumer position.
    cached_tail: Cell<usize>,
}

unsafe impl<T: Send, const N: usize> Send for Producer<T, N> {}

impl<T, const N: usize> Producer<T, N> {
    /// Mask - compile time constant.
    const MASK: usize = N - 1;

    /// Push a value. Returns `Err(value)` if full.
    #[inline]
    pub fn push(&mut self, value: T) -> Result<(), T> {
        let head = self.local_head.get();

        // Fast path: check cached tail, all local/cached data
        if head.wrapping_sub(self.cached_tail.get()) < N {
            unsafe {
                let slot = self.buffer.add(head & Self::MASK) as *mut T;
                slot.write(value);
                (*self.head).store(head.wrapping_add(1), Ordering::Release);
            }
            self.local_head.set(head.wrapping_add(1));
            return Ok(());
        }

        self.push_slow(head, value)
    }

    #[cold]
    fn push_slow(&mut self, head: usize, value: T) -> Result<(), T> {
        // Refresh cached tail
        let tail = unsafe { (*self.tail).load(Ordering::Acquire) };
        self.cached_tail.set(tail);

        if head.wrapping_sub(tail) < N {
            unsafe {
                let slot = self.buffer.add(head & Self::MASK) as *mut T;
                slot.write(value);
                (*self.head).store(head.wrapping_add(1), Ordering::Release);
            }
            self.local_head.set(head.wrapping_add(1));
            Ok(())
        } else {
            Err(value)
        }
    }

    /// Returns the capacity (compile-time constant).
    #[inline]
    pub const fn capacity(&self) -> usize {
        N
    }

    /// Returns current length (snapshot, may be stale).
    #[inline]
    pub fn len(&self) -> usize {
        unsafe {
            let head = (*self.head).load(Ordering::Relaxed);
            let tail = (*self.tail).load(Ordering::Relaxed);
            head.wrapping_sub(tail)
        }
    }

    /// Returns true if empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// Consumer half of the ring buffer.
///
/// Caches pointers to avoid Arc deref on hot path.
pub struct Consumer<T, const N: usize> {
    rb: Arc<RingBuffer<T, N>>,
    /// Cached buffer pointer.
    buffer: *const MaybeUninit<T>,
    /// Cached head atomic pointer.
    head: *const AtomicUsize,
    /// Cached tail atomic pointer.
    tail: *const AtomicUsize,
    /// Our read position.
    local_tail: Cell<usize>,
    /// Cached producer position.
    cached_head: Cell<usize>,
}

unsafe impl<T: Send, const N: usize> Send for Consumer<T, N> {}

impl<T, const N: usize> Consumer<T, N> {
    /// Mask - compile time constant.
    const MASK: usize = N - 1;

    /// Pop a value. Returns `None` if empty.
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        let tail = self.local_tail.get();

        // Fast path: check cached head, all local/cached data
        if tail != self.cached_head.get() {
            unsafe {
                let slot = self.buffer.add(tail & Self::MASK) as *const T;
                let value = slot.read();
                (*self.tail).store(tail.wrapping_add(1), Ordering::Release);
                self.local_tail.set(tail.wrapping_add(1));
                return Some(value);
            }
        }

        self.pop_slow(tail)
    }

    #[cold]
    fn pop_slow(&mut self, tail: usize) -> Option<T> {
        // Refresh cached head
        let head = unsafe { (*self.head).load(Ordering::Acquire) };
        self.cached_head.set(head);

        if tail != head {
            unsafe {
                let slot = self.buffer.add(tail & Self::MASK) as *const T;
                let value = slot.read();
                (*self.tail).store(tail.wrapping_add(1), Ordering::Release);
                self.local_tail.set(tail.wrapping_add(1));
                Some(value)
            }
        } else {
            None
        }
    }

    /// Returns the capacity (compile-time constant).
    #[inline]
    pub const fn capacity(&self) -> usize {
        N
    }

    /// Returns current length (snapshot, may be stale).
    #[inline]
    pub fn len(&self) -> usize {
        unsafe {
            let head = (*self.head).load(Ordering::Relaxed);
            let tail = (*self.tail).load(Ordering::Relaxed);
            head.wrapping_sub(tail)
        }
    }

    /// Returns true if empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn struct_sizes() {
        // Larger due to cached pointers, but faster
        assert_eq!(std::mem::size_of::<Producer<u64, 1024>>(), 56);
        assert_eq!(std::mem::size_of::<Consumer<u64, 1024>>(), 56);
    }

    #[test]
    fn basic_push_pop() {
        let (mut tx, mut rx) = RingBuffer::<u64, 8>::new();

        tx.push(1).unwrap();
        tx.push(2).unwrap();
        tx.push(3).unwrap();

        assert_eq!(rx.pop(), Some(1));
        assert_eq!(rx.pop(), Some(2));
        assert_eq!(rx.pop(), Some(3));
        assert_eq!(rx.pop(), None);
    }

    #[test]
    fn full_buffer() {
        let (mut tx, mut rx) = RingBuffer::<u64, 4>::new();

        tx.push(1).unwrap();
        tx.push(2).unwrap();
        tx.push(3).unwrap();
        tx.push(4).unwrap();

        assert_eq!(tx.push(5), Err(5));

        rx.pop();
        tx.push(5).unwrap();
    }

    #[test]
    fn wraparound() {
        let (mut tx, mut rx) = RingBuffer::<u64, 4>::new();

        for lap in 0..100u64 {
            for i in 0..4 {
                tx.push(lap * 4 + i).unwrap();
            }
            for i in 0..4 {
                assert_eq!(rx.pop(), Some(lap * 4 + i));
            }
        }
    }

    #[test]
    fn cross_thread() {
        use std::thread;

        let (mut tx, mut rx) = RingBuffer::<u64, 1024>::new();

        let h = thread::spawn(move || {
            for i in 0..100_000u64 {
                while tx.push(i).is_err() {
                    std::hint::spin_loop();
                }
            }
        });

        let mut expected = 0u64;
        while expected < 100_000 {
            if let Some(v) = rx.pop() {
                assert_eq!(v, expected);
                expected += 1;
            }
        }

        h.join().unwrap();
    }

    #[test]
    fn drop_remaining() {
        use std::sync::Arc;
        use std::sync::atomic::{AtomicUsize, Ordering};

        let drop_count = Arc::new(AtomicUsize::new(0));

        #[derive(Debug)]
        struct DropCounter(Arc<AtomicUsize>);
        impl Drop for DropCounter {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }

        let (mut tx, rx) = RingBuffer::<DropCounter, 8>::new();

        tx.push(DropCounter(Arc::clone(&drop_count))).unwrap();
        tx.push(DropCounter(Arc::clone(&drop_count))).unwrap();
        tx.push(DropCounter(Arc::clone(&drop_count))).unwrap();

        assert_eq!(drop_count.load(Ordering::SeqCst), 0);

        drop(tx);
        drop(rx);

        assert_eq!(drop_count.load(Ordering::SeqCst), 3);
    }
}
