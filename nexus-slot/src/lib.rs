//! Single-value SPSC conflation slot.
//!
//! This is optimized for the "latest value wins" pattern common in market data:
//! - Writer overwrites with newest data
//! - Reader gets each new value exactly once
//! - Old values are silently discarded (conflated)
//!
//! # Performance
//!
//! | Operation | Cycles | Notes |
//! |-----------|--------|-------|
//! | write (64 bytes) | ~12-18 | Two stores + memcpy |
//! | read (64 bytes) | ~15-25 | Two loads + memcpy |
//! | read (no new data) | ~3-5 | Single load + compare |
//! | has_update | ~3-5 | Single load + compare |
//!
//! # Example
//!
//! ```rust
//! use nexus_slot::{self, Pod};
//!
//! #[derive(Clone, Default)]
//! #[repr(C)]
//! struct Quote {
//!     price: f64,
//!     size: f64,
//! }
//!
//! unsafe impl Pod for Quote {}
//!
//! let (mut writer, mut reader) = nexus_slot::new::<Quote>();
//!
//! // No data yet
//! assert!(reader.read().is_none());
//!
//! // Write some data
//! writer.write(Quote { price: 100.0, size: 10.0 });
//!
//! // Read consumes it
//! let quote = reader.read().unwrap();
//! assert_eq!(quote.price, 100.0);
//!
//! // Already consumed, returns None
//! assert!(reader.read().is_none());
//!
//! // New write makes data available again
//! writer.write(Quote { price: 101.0, size: 20.0 });
//! assert!(reader.read().is_some());
//! ```

use std::cell::UnsafeCell;
use std::fmt;
use std::mem::MaybeUninit;
use std::sync::atomic::{fence, AtomicUsize, Ordering};
use std::sync::Arc;

/// Marker trait for types safe to use in a conflated slot.
///
/// # Safety
///
/// Implementor guarantees:
///
/// 1. **No heap allocations**: No `Vec`, `String`, `Box`, `Arc`, etc.
/// 2. **No owned resources**: No `File`, `TcpStream`, `Mutex`, etc.
/// 3. **No drop glue**: `std::mem::needs_drop::<Self>()` returns false.
/// 4. **Byte-copyable**: Safe to memcpy without cleanup.
///
/// Essentially: the type could be `Copy`, but chooses not to.
///
/// # Example
///
/// ```rust
/// use nexus_slot::Pod;
///
/// #[repr(C)]
/// struct OrderBook {
///     bids: [f64; 20],  // 10 levels × (price, size)
///     asks: [f64; 20],
///     bid_count: u8,
///     ask_count: u8,
///     sequence: u64,
/// }
///
/// // SAFETY: Just bytes, no heap
/// unsafe impl Pod for OrderBook {}
/// ```
pub unsafe trait Pod: Sized {
    const _ASSERT_NO_DROP: () = {
        assert!(
            !std::mem::needs_drop::<Self>(),
            "Pod types must not require drop"
        );
    };
}

// Any Copy type is Pod
unsafe impl<T: Copy> Pod for T {}

/// Shared state between writer and reader.
#[repr(C)]
struct Inner<T> {
    /// Sequence number. Odd = write in progress, even = stable, 0 = never written.
    seq: AtomicUsize,
    data: UnsafeCell<MaybeUninit<T>>,
}

unsafe impl<T: Send> Send for Inner<T> {}
unsafe impl<T: Send> Sync for Inner<T> {}

/// The writing half of a conflated slot.
pub struct Writer<T> {
    local_seq: usize,
    inner: Arc<Inner<T>>,
}

unsafe impl<T: Send> Send for Writer<T> {}

/// The reading half of a conflated slot.
pub struct Reader<T> {
    cached_seq: usize,
    inner: Arc<Inner<T>>,
}

unsafe impl<T: Send> Send for Reader<T> {}

/// Creates a new conflated slot.
///
/// Returns a `(Writer, Reader)` pair.
pub fn new<T: Pod>() -> (Writer<T>, Reader<T>) {
    let _ = T::_ASSERT_NO_DROP;

    let inner = Arc::new(Inner {
        seq: AtomicUsize::new(0),
        data: UnsafeCell::new(MaybeUninit::uninit()),
    });

    (
        Writer {
            local_seq: 0,
            inner: Arc::clone(&inner),
        },
        Reader {
            cached_seq: 0,
            inner,
        },
    )
}

impl<T: Pod> Writer<T> {
    /// Writes a value, overwriting any previous.
    ///
    /// Never blocks. If the reader is mid-read, they detect and retry.
    #[inline]
    pub fn write(&mut self, value: T) {
        let inner = &*self.inner;
        let seq = self.local_seq;

        // Odd = write in progress
        inner.seq.store(seq.wrapping_add(1), Ordering::Relaxed);
        fence(Ordering::Release);

        unsafe { (*inner.data.get()).write(value) };

        fence(Ordering::Release);
        self.local_seq = seq.wrapping_add(2);
        inner.seq.store(self.local_seq, Ordering::Relaxed);
    }

    /// Returns `true` if the reader has been dropped.
    #[inline]
    pub fn is_disconnected(&self) -> bool {
        Arc::strong_count(&self.inner) == 1
    }
}

impl<T: Pod> fmt::Debug for Writer<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Writer")
            .field("seq", &self.local_seq)
            .finish_non_exhaustive()
    }
}

impl<T: Pod> Reader<T> {
    /// Reads the latest value if new data is available.
    ///
    /// Returns `Some(value)` if:
    /// - A value has been written, AND
    /// - It hasn't been read yet (or a new write occurred since last read)
    ///
    /// Returns `None` if:
    /// - No value has ever been written, OR
    /// - The current value was already consumed by a previous `read()`
    ///
    /// # Performance
    ///
    /// - No new data: ~3-5 cycles (single load + compare)
    /// - New data: ~15-25 cycles (two loads + memcpy)
    #[inline]
    pub fn read(&mut self) -> Option<T> {
        let inner = &*self.inner;

        loop {
            let seq1 = inner.seq.load(Ordering::Relaxed);

            // Never written or already consumed
            if seq1 == 0 || seq1 == self.cached_seq {
                return None;
            }

            // Write in progress
            if seq1 & 1 != 0 {
                core::hint::spin_loop();
                continue;
            }

            fence(Ordering::Acquire);

            let value = unsafe { (*inner.data.get()).assume_init_read() };

            fence(Ordering::Acquire);
            let seq2 = inner.seq.load(Ordering::Relaxed);

            if seq1 == seq2 {
                self.cached_seq = seq1;
                return Some(value);
            }

            // Torn read, retry
            core::hint::spin_loop();
        }
    }

    /// Checks if new data is available without consuming it.
    ///
    /// Returns `true` if `read()` would return `Some`.
    ///
    /// # Performance
    ///
    /// ~3-5 cycles (single load + compare).
    #[inline]
    pub fn has_update(&self) -> bool {
        let seq = self.inner.seq.load(Ordering::Relaxed);
        seq != 0 && seq != self.cached_seq && seq & 1 == 0
    }

    /// Returns `true` if the writer has been dropped.
    #[inline]
    pub fn is_disconnected(&self) -> bool {
        Arc::strong_count(&self.inner) == 1
    }
}

impl<T: Pod> fmt::Debug for Reader<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Reader")
            .field("cached_seq", &self.cached_seq)
            .finish_non_exhaustive()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Default, PartialEq, Debug)]
    #[repr(C)]
    struct TestData {
        a: u64,
        b: u64,
    }

    unsafe impl Pod for TestData {}

    // ========================================================================
    // Queue-like Semantics
    // ========================================================================

    #[test]
    fn read_before_write_returns_none() {
        let (_, mut reader) = new::<TestData>();
        assert!(reader.read().is_none());
    }

    #[test]
    fn read_consumes_value() {
        let (mut writer, mut reader) = new::<TestData>();

        writer.write(TestData { a: 1, b: 2 });

        // First read succeeds
        assert_eq!(reader.read(), Some(TestData { a: 1, b: 2 }));

        // Second read returns None - already consumed
        assert!(reader.read().is_none());
        assert!(reader.read().is_none());
    }

    #[test]
    fn new_write_makes_data_available_again() {
        let (mut writer, mut reader) = new::<TestData>();

        writer.write(TestData { a: 1, b: 0 });
        assert!(reader.read().is_some());
        assert!(reader.read().is_none()); // Consumed

        writer.write(TestData { a: 2, b: 0 });
        assert!(reader.read().is_some()); // Available again
        assert!(reader.read().is_none()); // Consumed again
    }

    #[test]
    fn multiple_writes_before_read_conflates() {
        let (mut writer, mut reader) = new::<TestData>();

        writer.write(TestData { a: 1, b: 0 });
        writer.write(TestData { a: 2, b: 0 });
        writer.write(TestData { a: 3, b: 0 });

        // Only get the latest
        assert_eq!(reader.read(), Some(TestData { a: 3, b: 0 }));
        assert!(reader.read().is_none());
    }

    #[test]
    fn has_update_does_not_consume() {
        let (mut writer, mut reader) = new::<TestData>();

        assert!(!reader.has_update());

        writer.write(TestData { a: 1, b: 0 });

        assert!(reader.has_update());
        assert!(reader.has_update()); // Still true
        assert!(reader.has_update());

        reader.read(); // Now consume

        assert!(!reader.has_update());
    }

    // ========================================================================
    // Disconnection
    // ========================================================================

    #[test]
    fn writer_detects_disconnect() {
        let (writer, reader) = new::<TestData>();
        assert!(!writer.is_disconnected());
        drop(reader);
        assert!(writer.is_disconnected());
    }

    #[test]
    fn reader_detects_disconnect() {
        let (writer, reader) = new::<TestData>();
        assert!(!reader.is_disconnected());
        drop(writer);
        assert!(reader.is_disconnected());
    }

    #[test]
    fn can_read_after_writer_disconnect() {
        let (mut writer, mut reader) = new::<TestData>();

        writer.write(TestData { a: 42, b: 0 });
        drop(writer);

        assert!(reader.is_disconnected());
        assert_eq!(reader.read(), Some(TestData { a: 42, b: 0 }));
    }

    // ========================================================================
    // Cross-Thread
    // ========================================================================

    #[test]
    fn cross_thread_write_read() {
        use std::thread;

        let (mut writer, mut reader) = new::<TestData>();

        let handle = thread::spawn(move || {
            while reader.read().is_none() {
                core::hint::spin_loop();
            }
        });

        writer.write(TestData { a: 1, b: 2 });
        handle.join().unwrap();
    }

    #[test]
    fn cross_thread_conflation() {
        use std::thread;

        let (mut writer, mut reader) = new::<u64>();

        let handle = thread::spawn(move || {
            let mut last = 0;
            let mut count = 0;

            loop {
                if reader.is_disconnected() && !reader.has_update() {
                    break;
                }
                if let Some(v) = reader.read() {
                    assert!(v >= last, "must be monotonic");
                    last = v;
                    count += 1;
                }
            }
            (last, count)
        });

        for i in 0..100_000u64 {
            writer.write(i);
        }
        drop(writer);

        let (last, count) = handle.join().unwrap();
        assert_eq!(last, 99_999);
        assert!(count <= 100_000); // Conflated
        assert!(count >= 1);
    }

    #[test]
    fn data_integrity() {
        use std::thread;

        #[derive(Clone)]
        #[repr(C)]
        struct Checkable {
            value: u64,
            check: u64,
        }
        unsafe impl Pod for Checkable {}

        let (mut writer, mut reader) = new::<Checkable>();

        let handle = thread::spawn(move || {
            loop {
                if reader.is_disconnected() && !reader.has_update() {
                    break;
                }
                if let Some(data) = reader.read() {
                    assert_eq!(data.check, !data.value, "torn read!");
                }
            }
        });

        for i in 0..100_000u64 {
            writer.write(Checkable {
                value: i,
                check: !i,
            });
        }
        drop(writer);

        handle.join().unwrap();
    }

    #[test]
    fn large_struct_integrity() {
        use std::thread;

        #[derive(Clone)]
        #[repr(C)]
        struct Large {
            seq: u64,
            data: [u64; 31],
        }
        unsafe impl Pod for Large {}

        let (mut writer, mut reader) = new::<Large>();

        let handle = thread::spawn(move || {
            loop {
                if reader.is_disconnected() && !reader.has_update() {
                    break;
                }
                if let Some(d) = reader.read() {
                    for &val in &d.data {
                        assert_eq!(val, d.seq, "torn read");
                    }
                }
            }
        });

        for i in 0..10_000u64 {
            writer.write(Large {
                seq: i,
                data: [i; 31],
            });
        }
        drop(writer);

        handle.join().unwrap();
    }

    // ========================================================================
    // Stress
    // ========================================================================

    #[test]
    fn stress_writes_then_single_read() {
        let (mut writer, mut reader) = new::<u64>();

        for i in 0..1_000_000 {
            writer.write(i);
        }

        assert_eq!(reader.read(), Some(999_999));
        assert!(reader.read().is_none());
    }

    #[test]
    fn ping_pong() {
        use std::thread;

        let (mut w1, mut r1) = new::<u64>();
        let (mut w2, mut r2) = new::<u64>();

        let handle = thread::spawn(move || {
            for i in 0..10_000u64 {
                while r1.read().is_none() {
                    core::hint::spin_loop();
                }
                w2.write(i);
            }
        });

        for i in 0..10_000u64 {
            w1.write(i);
            while r2.read().is_none() {
                core::hint::spin_loop();
            }
        }

        handle.join().unwrap();
    }
}
