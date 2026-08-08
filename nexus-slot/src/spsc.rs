//! Single-producer, single-consumer conflation slot.
//!
//! Uses a seqlock for lock-free publication. The writer increments a sequence
//! counter, copies data via word-at-a-time atomics, and increments again.
//! The reader speculatively reads and retries if the sequence changed.
//!
//! The SPSC constraint allows caching the sequence number on the writer side,
//! eliminating an atomic load per write.
//!
//! # Example
//!
//! ```rust
//! #[derive(Copy, Clone, Default)]
//! struct Quote { bid: f64, ask: f64, seq: u64 }
//!
//! let (mut writer, mut reader) = nexus_slot::spsc::slot::<Quote>();
//!
//! writer.write(Quote { bid: 100.0, ask: 100.05, seq: 1 });
//! assert_eq!(reader.read().unwrap().seq, 1);
//! assert!(reader.read().is_none()); // consumed
//! ```

#[cfg(not(loom))]
use std::cell::UnsafeCell;
use std::fmt;
#[cfg(loom)]
use std::marker::PhantomData;
#[cfg(not(loom))]
use std::mem::MaybeUninit;

use crate::Pod;
use crate::loom_impl::{Arc, AtomicUsize, Ordering, fence};
#[cfg(not(loom))]
use crate::{atomic_load, atomic_store};

/// Shared state between writer and reader.
#[repr(C)]
struct Inner<T> {
    /// Sequence number. Odd = write in progress, even = stable, 0 = never written.
    seq: AtomicUsize,
    #[cfg(not(loom))]
    data: UnsafeCell<MaybeUninit<T>>,
    #[cfg(loom)]
    data: AtomicUsize,
    #[cfg(loom)]
    _marker: PhantomData<T>,
}

// SAFETY: Inner is shared via Arc between exactly one Writer and one Reader,
// each on potentially different threads. All access to `data` goes through
// word-at-a-time atomics (atomic_store/atomic_load), and the seqlock protocol
// ensures no torn reads. T: Send is required because values cross thread boundaries.
unsafe impl<T: Send> Send for Inner<T> {}
// SAFETY: same as Send; seqlock atomics make concurrent immutable access safe across threads.
unsafe impl<T: Send> Sync for Inner<T> {}

/// The writing half of a conflated slot.
pub struct Writer<T> {
    local_seq: usize,
    inner: Arc<Inner<T>>,
}

// SAFETY: Writer holds an Arc<Inner<T>> and is the sole writer. Sending it to
// another thread is safe because T: Send and the seqlock protocol coordinates
// all shared access to Inner's data.
unsafe impl<T: Send> Send for Writer<T> {}

/// The reading half of a conflated slot.
pub struct Reader<T> {
    cached_seq: usize,
    inner: Arc<Inner<T>>,
}

// SAFETY: Reader holds an Arc<Inner<T>> and is the sole reader. Sending it to
// another thread is safe because T: Send and the seqlock protocol coordinates
// all shared access to Inner's data.
unsafe impl<T: Send> Send for Reader<T> {}

/// Creates a new SPSC conflated slot.
///
/// Returns a `(Writer, Reader)` pair. Neither is `Clone` — for multiple
/// readers, use [`spmc::shared_slot`](crate::spmc::shared_slot).
pub fn slot<T: Pod>() -> (Writer<T>, Reader<T>) {
    const {
        assert!(
            !std::mem::needs_drop::<T>(),
            "Pod types must not require drop"
        );
    };

    // Start at 2 instead of 0 so that wrapping on 32-bit never hits
    // 0 (the "never written" sentinel). Sequence uses even values for
    // "write complete" and odd for "write in progress": 2→3→4→5→...
    let inner = Arc::new(Inner {
        seq: AtomicUsize::new(2),
        #[cfg(not(loom))]
        data: UnsafeCell::new(MaybeUninit::uninit()),
        #[cfg(loom)]
        data: AtomicUsize::new(0),
        #[cfg(loom)]
        _marker: PhantomData,
    });

    (
        Writer {
            local_seq: 2,
            inner: Arc::clone(&inner),
        },
        Reader {
            cached_seq: 2,
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

        // SAFETY: We are the sole writer. The Release fence ensures the odd
        // sequence is visible before we touch data. Readers seeing the odd
        // sequence will spin. The data pointer is from UnsafeCell — no
        // references are created to the shared data, only raw pointer access
        // through word-at-a-time atomics.
        #[cfg(not(loom))]
        // SAFETY: sole writer, data from UnsafeCell, word-at-a-time atomics.
        unsafe {
            atomic_store(inner.data.get().cast::<T>(), &value);
        }
        #[cfg(loom)]
        crate::loom_impl::loom_store(&inner.data, &value);

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
    /// Returns `Some(value)` if a new write occurred since the last read.
    /// Returns `None` if no value has been written or the current value
    /// was already consumed.
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
                crate::loom_impl::spin_yield();
                continue;
            }

            fence(Ordering::Acquire);

            // SAFETY: seq1 is even and non-zero, so a complete write occurred.
            // The Acquire fence synchronizes with the writer's Release fence.
            // If a concurrent write occurs, we detect it via seq2 != seq1.
            // No references are created — raw pointer access through atomics.
            #[cfg(not(loom))]
            let value = unsafe { atomic_load(inner.data.get().cast::<T>()) };
            #[cfg(loom)]
            let value = crate::loom_impl::loom_load::<T>(&inner.data);

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

    /// Read with version tracking for conflation detection.
    ///
    /// Returns `Some((value, version))` where `version` is a write counter
    /// derived from the seqlock sequence. Increases on each write, but wraps
    /// after `usize::MAX / 2` writes. Use wrapping arithmetic to compute
    /// missed writes:
    ///
    /// ```ignore
    /// let mut last_ver = 0;
    /// loop {
    ///     if let Some((quote, ver)) = reader.read_versioned() {
    ///         let missed = ver.wrapping_sub(last_ver).wrapping_sub(1);
    ///         if missed > 0 { log::warn!("conflated {missed} writes"); }
    ///         last_ver = ver;
    ///         process(quote);
    ///     }
    /// }
    /// ```
    ///
    /// Zero overhead vs [`Self::read()`] — the version is derived from the
    /// seqlock sequence that is already loaded during the read.
    #[inline]
    pub fn read_versioned(&mut self) -> Option<(T, u64)> {
        let inner = &*self.inner;

        loop {
            let seq1 = inner.seq.load(Ordering::Relaxed);

            if seq1 == 0 || seq1 == self.cached_seq {
                return None;
            }

            if seq1 & 1 != 0 {
                crate::loom_impl::spin_yield();
                continue;
            }

            fence(Ordering::Acquire);

            // SAFETY: same as read() — seq1 is even and non-zero.
            #[cfg(not(loom))]
            let value = unsafe { atomic_load(inner.data.get().cast::<T>()) };
            #[cfg(loom)]
            let value = crate::loom_impl::loom_load::<T>(&inner.data);

            fence(Ordering::Acquire);
            let seq2 = inner.seq.load(Ordering::Relaxed);

            if seq1 == seq2 {
                self.cached_seq = seq1;
                // Version = seq / 2 (writer increments by 2 per write)
                return Some((value, seq1 as u64 / 2));
            }

            core::hint::spin_loop();
        }
    }

    /// Checks if new data is available without consuming it.
    ///
    /// Returns `true` if [`read()`](Self::read) would return `Some`.
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

#[cfg(all(test, not(loom)))]
mod tests {
    use super::*;

    #[derive(Clone, Default, PartialEq, Debug)]
    #[repr(C)]
    struct TestData {
        a: u64,
        b: u64,
    }

    // SAFETY: TestData is repr(C) with only Copy fields, no heap pointers, no Drop, all bit patterns valid.
    unsafe impl Pod for TestData {}

    // ========================================================================
    // Queue-like Semantics
    // ========================================================================

    #[test]
    fn read_before_write_returns_none() {
        let (_, mut reader) = slot::<TestData>();
        assert!(reader.read().is_none());
    }

    #[test]
    fn read_consumes_value() {
        let (mut writer, mut reader) = slot::<TestData>();

        writer.write(TestData { a: 1, b: 2 });

        // First read succeeds
        assert_eq!(reader.read(), Some(TestData { a: 1, b: 2 }));

        // Second read returns None - already consumed
        assert!(reader.read().is_none());
        assert!(reader.read().is_none());
    }

    #[test]
    fn new_write_makes_data_available_again() {
        let (mut writer, mut reader) = slot::<TestData>();

        writer.write(TestData { a: 1, b: 0 });
        assert!(reader.read().is_some());
        assert!(reader.read().is_none()); // Consumed

        writer.write(TestData { a: 2, b: 0 });
        assert!(reader.read().is_some()); // Available again
        assert!(reader.read().is_none()); // Consumed again
    }

    #[test]
    fn multiple_writes_before_read_conflates() {
        let (mut writer, mut reader) = slot::<TestData>();

        writer.write(TestData { a: 1, b: 0 });
        writer.write(TestData { a: 2, b: 0 });
        writer.write(TestData { a: 3, b: 0 });

        // Only get the latest
        assert_eq!(reader.read(), Some(TestData { a: 3, b: 0 }));
        assert!(reader.read().is_none());
    }

    #[test]
    fn has_update_does_not_consume() {
        let (mut writer, mut reader) = slot::<TestData>();

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
        let (writer, reader) = slot::<TestData>();
        assert!(!writer.is_disconnected());
        drop(reader);
        assert!(writer.is_disconnected());
    }

    #[test]
    fn reader_detects_disconnect() {
        let (writer, reader) = slot::<TestData>();
        assert!(!reader.is_disconnected());
        drop(writer);
        assert!(reader.is_disconnected());
    }

    #[test]
    fn can_read_after_writer_disconnect() {
        let (mut writer, mut reader) = slot::<TestData>();

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

        let (mut writer, mut reader) = slot::<TestData>();

        let handle = thread::spawn(move || {
            while reader.read().is_none() {
                crate::loom_impl::spin_yield();
            }
        });

        writer.write(TestData { a: 1, b: 2 });
        handle.join().unwrap();
    }

    #[test]
    fn cross_thread_conflation() {
        use std::thread;

        let (mut writer, mut reader) = slot::<u64>();

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
        // SAFETY: Checkable is repr(C) with only Copy fields, no heap pointers, no Drop, all bit patterns valid.
        unsafe impl Pod for Checkable {}

        let (mut writer, mut reader) = slot::<Checkable>();

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
        // SAFETY: Large is repr(C) with only Copy fields, no heap pointers, no Drop, all bit patterns valid.
        unsafe impl Pod for Large {}

        let (mut writer, mut reader) = slot::<Large>();

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
        let (mut writer, mut reader) = slot::<u64>();

        for i in 0..1_000_000 {
            writer.write(i);
        }

        assert_eq!(reader.read(), Some(999_999));
        assert!(reader.read().is_none());
    }

    #[test]
    fn ping_pong() {
        use std::thread;

        let (mut w1, mut r1) = slot::<u64>();
        let (mut w2, mut r2) = slot::<u64>();

        let handle = thread::spawn(move || {
            for i in 0..10_000u64 {
                while r1.read().is_none() {
                    crate::loom_impl::spin_yield();
                }
                w2.write(i);
            }
        });

        for i in 0..10_000u64 {
            w1.write(i);
            while r2.read().is_none() {
                crate::loom_impl::spin_yield();
            }
        }

        handle.join().unwrap();
    }

    #[test]
    fn read_versioned_returns_version() {
        let (mut writer, mut reader) = slot::<TestData>();

        writer.write(TestData { a: 1, b: 2 });
        let (val, ver1) = reader.read_versioned().unwrap();
        assert_eq!(val.a, 1);

        writer.write(TestData { a: 3, b: 4 });
        let (val, ver2) = reader.read_versioned().unwrap();
        assert_eq!(val.a, 3);
        // Each write increments version by 1.
        assert_eq!(ver2.wrapping_sub(ver1), 1);
    }

    #[test]
    fn read_versioned_detects_conflation() {
        let (mut writer, mut reader) = slot::<TestData>();

        // Write 5 times, read once — missed 4 writes
        for i in 0..5 {
            writer.write(TestData { a: i, b: 0 });
        }

        let (val, ver1) = reader.read_versioned().unwrap();
        assert_eq!(val.a, 4); // last write

        // No new data
        assert!(reader.read_versioned().is_none());

        // Write again
        writer.write(TestData { a: 99, b: 0 });
        let (val, ver2) = reader.read_versioned().unwrap();
        assert_eq!(val.a, 99);
        // Missed = ver2 - ver1 - 1 = 1 - 1 = 0 (no conflation since last read)
        assert_eq!(ver2.wrapping_sub(ver1), 1);
    }

    #[test]
    fn read_versioned_none_before_first_write() {
        let (_writer, mut reader) = slot::<TestData>();
        assert!(reader.read_versioned().is_none());
    }
}
