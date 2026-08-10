//! Single-producer, multiple-consumer conflation slot.
//!
//! Same seqlock design as [`spsc`](crate::spsc), but the reader is `Clone`.
//! Each clone maintains independent consumption state — all readers see
//! every write (unless conflated by a subsequent write before they read).
//!
//! Writer disconnect detection uses an explicit flag rather than reference
//! counting, since multiple readers make `Arc::strong_count` ambiguous
//! for that check.
//!
//! # Example
//!
//! ```rust
//! let (mut writer, mut reader1) = nexus_slot::spmc::shared_slot::<u64>();
//! let mut reader2 = reader1.clone();
//!
//! writer.write(42);
//!
//! // Both readers see the value independently
//! assert_eq!(reader1.read(), Some(42));
//! assert_eq!(reader2.read(), Some(42));
//!
//! // Both consumed — returns None until next write
//! assert!(reader1.read().is_none());
//! assert!(reader2.read().is_none());
//! ```

#[cfg(not(loom))]
use std::cell::UnsafeCell;
use std::fmt;
#[cfg(loom)]
use std::marker::PhantomData;
#[cfg(not(loom))]
use std::mem::MaybeUninit;

use crate::Pod;
use crate::loom_impl::{Arc, AtomicBool, AtomicUsize, Ordering, fence};
#[cfg(not(loom))]
use crate::{atomic_load, atomic_store};

/// Shared state between writer and readers.
#[repr(C)]
struct Inner<T> {
    /// Sequence number. Odd = write in progress, even = stable, 0 = never written.
    seq: AtomicUsize,
    /// Set to `false` when the writer is dropped.
    writer_alive: AtomicBool,
    #[cfg(not(loom))]
    data: UnsafeCell<MaybeUninit<T>>,
    #[cfg(loom)]
    data: AtomicUsize,
    #[cfg(loom)]
    _marker: PhantomData<T>,
}

// SAFETY: Inner is shared via Arc between one Writer and multiple SharedReaders.
// All access to `data` goes through word-at-a-time atomics (atomic_store/atomic_load),
// and the seqlock protocol detects torn reads and retries. T: Send is required because
// values cross thread boundaries. writer_alive uses atomic ordering for visibility.
unsafe impl<T: Send> Send for Inner<T> {}
// SAFETY: same as Send; seqlock atomics make concurrent immutable access safe across threads.
unsafe impl<T: Send> Sync for Inner<T> {}

/// The writing half of a shared conflated slot.
pub struct Writer<T> {
    local_seq: usize,
    inner: Arc<Inner<T>>,
}

// SAFETY: Writer holds an Arc<Inner<T>> and is the sole writer. Sending it to
// another thread is safe because T: Send and the seqlock protocol coordinates
// all shared access to Inner's data.
unsafe impl<T: Send> Send for Writer<T> {}

/// The reading half of a shared conflated slot.
///
/// `Clone` creates an independent reader starting from the same consumption
/// position as the original. Each reader tracks its own "last seen" sequence
/// and consumes writes independently.
pub struct SharedReader<T> {
    cached_seq: usize,
    inner: Arc<Inner<T>>,
}

// SAFETY: SharedReader holds an Arc<Inner<T>> and only reads via the seqlock
// protocol. Each reader's cached_seq is private (not shared). Sending to
// another thread is safe because T: Send and all data access is atomic.
unsafe impl<T: Send> Send for SharedReader<T> {}

impl<T> Clone for SharedReader<T> {
    fn clone(&self) -> Self {
        Self {
            cached_seq: self.cached_seq,
            inner: Arc::clone(&self.inner),
        }
    }
}

/// Creates a new SPMC conflated slot.
///
/// Returns a `(Writer, SharedReader)` pair. The reader can be cloned
/// for multiple consumers.
pub fn shared_slot<T: Pod>() -> (Writer<T>, SharedReader<T>) {
    const {
        assert!(
            !std::mem::needs_drop::<T>(),
            "Pod types must not require drop"
        );
    };

    // Start at 2 instead of 0 so that wrapping on 32-bit never hits
    // 0 (the "never written" sentinel). See spsc.rs for detailed rationale.
    let inner = Arc::new(Inner {
        seq: AtomicUsize::new(2),
        writer_alive: AtomicBool::new(true),
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
        SharedReader {
            cached_seq: 2,
            inner,
        },
    )
}

impl<T: Pod> Writer<T> {
    /// Writes a value, overwriting any previous.
    ///
    /// Never blocks. If any reader is mid-read, they detect and retry.
    #[allow(clippy::needless_pass_by_value)] // must own value; T: Pod has no drop glue
    #[inline]
    pub fn write(&mut self, value: T) {
        let inner = &*self.inner;
        let seq = self.local_seq;

        // Odd = write in progress
        inner.seq.store(seq.wrapping_add(1), Ordering::Relaxed);
        fence(Ordering::Release);

        // SAFETY: Same as spsc::Writer::write — sole writer, data accessed
        // through word-at-a-time atomics, no references created.
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

    /// Returns `true` if all readers have been dropped.
    #[inline]
    pub fn is_disconnected(&self) -> bool {
        Arc::strong_count(&self.inner) == 1
    }
}

impl<T> Drop for Writer<T> {
    fn drop(&mut self) {
        self.inner.writer_alive.store(false, Ordering::Release);
    }
}

impl<T: Pod> fmt::Debug for Writer<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Writer")
            .field("seq", &self.local_seq)
            .finish_non_exhaustive()
    }
}

impl<T: Pod> SharedReader<T> {
    /// Reads the latest value if new data is available.
    ///
    /// Returns `Some(value)` if a new write occurred since the last read.
    /// Returns `None` if no value has been written or the current value
    /// was already consumed by this reader.
    ///
    /// Each cloned reader consumes independently — one reader's `read()`
    /// does not affect another's.
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

            // SAFETY: Same as spsc::Reader::read.
            #[cfg(not(loom))]
            let buf = unsafe { atomic_load(inner.data.get().cast::<T>()) };
            #[cfg(loom)]
            let buf = crate::loom_impl::loom_load::<T>(&inner.data);

            fence(Ordering::Acquire);
            let seq2 = inner.seq.load(Ordering::Relaxed);

            if seq1 == seq2 {
                self.cached_seq = seq1;
                // SAFETY: seq1 == seq2 confirms a consistent seqlock read.
                return Some(unsafe { buf.assume_init() });
            }

            // Torn read, retry
            core::hint::spin_loop();
        }
    }

    /// Read with version tracking for conflation detection.
    ///
    /// See [`spsc::Reader::read_versioned`](crate::spsc::Reader::read_versioned)
    /// for details. Each cloned reader tracks versions independently.
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

            // SAFETY: Same as spsc::Reader::read_versioned.
            #[cfg(not(loom))]
            let buf = unsafe { atomic_load(inner.data.get().cast::<T>()) };
            #[cfg(loom)]
            let buf = crate::loom_impl::loom_load::<T>(&inner.data);

            fence(Ordering::Acquire);
            let seq2 = inner.seq.load(Ordering::Relaxed);

            if seq1 == seq2 {
                self.cached_seq = seq1;
                // SAFETY: same as read(); seq1 == seq2 confirms consistency.
                return Some((unsafe { buf.assume_init() }, seq1 as u64 / 2));
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
    ///
    /// Acquire-loads `writer_alive`. Pairs with the writer's Release
    /// store in `Drop` so a reader observing `writer_alive == false`
    /// is also guaranteed to observe the writer's final published data
    /// (the last `seq.store(..., Release)` before drop). Without the
    /// Acquire, the canonical drain-then-disconnect pattern
    /// `while !disconnected || has_update() { ... }` could exit early
    /// and miss the writer's last value.
    #[inline]
    pub fn is_disconnected(&self) -> bool {
        !self.inner.writer_alive.load(Ordering::Acquire)
    }
}

impl<T: Pod> fmt::Debug for SharedReader<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SharedReader")
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
    // Basic Semantics (same as SPSC)
    // ========================================================================

    #[test]
    fn read_before_write_returns_none() {
        let (_, mut reader) = shared_slot::<TestData>();
        assert!(reader.read().is_none());
    }

    #[test]
    fn read_consumes_value() {
        let (mut writer, mut reader) = shared_slot::<TestData>();

        writer.write(TestData { a: 1, b: 2 });
        assert_eq!(reader.read(), Some(TestData { a: 1, b: 2 }));
        assert!(reader.read().is_none());
    }

    #[test]
    fn multiple_writes_conflate() {
        let (mut writer, mut reader) = shared_slot::<TestData>();

        writer.write(TestData { a: 1, b: 0 });
        writer.write(TestData { a: 2, b: 0 });
        writer.write(TestData { a: 3, b: 0 });

        assert_eq!(reader.read(), Some(TestData { a: 3, b: 0 }));
        assert!(reader.read().is_none());
    }

    #[test]
    fn has_update_does_not_consume() {
        let (mut writer, mut reader) = shared_slot::<TestData>();

        assert!(!reader.has_update());
        writer.write(TestData { a: 1, b: 0 });
        assert!(reader.has_update());
        assert!(reader.has_update());
        reader.read();
        assert!(!reader.has_update());
    }

    // ========================================================================
    // Multi-Reader
    // ========================================================================

    #[test]
    fn two_readers_independent_consumption() {
        let (mut writer, mut reader1) = shared_slot::<u64>();
        let mut reader2 = reader1.clone();

        writer.write(42);

        // Both see it
        assert_eq!(reader1.read(), Some(42));
        assert_eq!(reader2.read(), Some(42));

        // Both consumed
        assert!(reader1.read().is_none());
        assert!(reader2.read().is_none());
    }

    #[test]
    fn clone_after_read_starts_at_parent_position() {
        let (mut writer, mut reader1) = shared_slot::<u64>();

        writer.write(1);
        assert_eq!(reader1.read(), Some(1));

        // Clone after consuming — clone has same cached_seq
        let mut reader2 = reader1.clone();

        // Neither sees old value
        assert!(reader1.read().is_none());
        assert!(reader2.read().is_none());

        // New write — both see it
        writer.write(2);
        assert_eq!(reader1.read(), Some(2));
        assert_eq!(reader2.read(), Some(2));
    }

    #[test]
    fn clone_before_read_both_see_value() {
        let (mut writer, mut reader1) = shared_slot::<u64>();
        let mut reader2 = reader1.clone();

        writer.write(99);

        assert_eq!(reader1.read(), Some(99));
        assert_eq!(reader2.read(), Some(99));
    }

    #[test]
    fn reader1_consumes_reader2_unaffected() {
        let (mut writer, mut reader1) = shared_slot::<u64>();
        let mut reader2 = reader1.clone();

        writer.write(10);

        // reader1 consumes
        assert_eq!(reader1.read(), Some(10));
        assert!(reader1.read().is_none());

        // reader2 still sees it
        assert!(reader2.has_update());
        assert_eq!(reader2.read(), Some(10));
    }

    #[test]
    fn many_readers() {
        let (mut writer, reader) = shared_slot::<u64>();
        let mut readers: Vec<_> = (0..10).map(|_| reader.clone()).collect();
        drop(reader);

        writer.write(42);

        for r in &mut readers {
            assert_eq!(r.read(), Some(42));
        }
    }

    // ========================================================================
    // Disconnection
    // ========================================================================

    #[test]
    fn writer_detects_all_readers_dropped() {
        let (writer, reader1) = shared_slot::<TestData>();
        let reader2 = reader1.clone();

        assert!(!writer.is_disconnected());
        drop(reader1);
        assert!(!writer.is_disconnected()); // reader2 still alive
        drop(reader2);
        assert!(writer.is_disconnected());
    }

    #[test]
    fn reader_detects_writer_dropped() {
        let (writer, reader) = shared_slot::<TestData>();
        assert!(!reader.is_disconnected());
        drop(writer);
        assert!(reader.is_disconnected());
    }

    #[test]
    fn cloned_reader_detects_writer_dropped() {
        let (writer, reader1) = shared_slot::<TestData>();
        let reader2 = reader1.clone();

        drop(writer);

        assert!(reader1.is_disconnected());
        assert!(reader2.is_disconnected());
    }

    #[test]
    fn can_read_after_writer_disconnect() {
        let (mut writer, mut reader) = shared_slot::<TestData>();

        writer.write(TestData { a: 42, b: 0 });
        drop(writer);

        assert!(reader.is_disconnected());
        assert_eq!(reader.read(), Some(TestData { a: 42, b: 0 }));
    }

    // ========================================================================
    // Cross-Thread
    // ========================================================================

    #[test]
    fn cross_thread_two_readers() {
        use std::thread;

        let (mut writer, mut reader1) = shared_slot::<u64>();
        let mut reader2 = reader1.clone();

        let h1 = thread::spawn(move || {
            let mut last = 0;
            loop {
                if reader1.is_disconnected() && !reader1.has_update() {
                    break;
                }
                if let Some(v) = reader1.read() {
                    assert!(v >= last, "reader1: monotonicity violation");
                    last = v;
                }
            }
            last
        });

        let h2 = thread::spawn(move || {
            let mut last = 0;
            loop {
                if reader2.is_disconnected() && !reader2.has_update() {
                    break;
                }
                if let Some(v) = reader2.read() {
                    assert!(v >= last, "reader2: monotonicity violation");
                    last = v;
                }
            }
            last
        });

        for i in 0..100_000u64 {
            writer.write(i);
        }
        drop(writer);

        let last1 = h1.join().unwrap();
        let last2 = h2.join().unwrap();

        assert_eq!(last1, 99_999);
        assert_eq!(last2, 99_999);
    }

    #[test]
    fn cross_thread_data_integrity() {
        use std::thread;

        #[derive(Clone)]
        #[repr(C)]
        struct Checkable {
            value: u64,
            check: u64,
        }
        // SAFETY: Checkable is repr(C) with only Copy fields, no heap pointers, no Drop, all bit patterns valid.
        unsafe impl Pod for Checkable {}

        let (mut writer, mut reader1) = shared_slot::<Checkable>();
        let mut reader2 = reader1.clone();

        let h1 = thread::spawn(move || {
            loop {
                if reader1.is_disconnected() && !reader1.has_update() {
                    break;
                }
                if let Some(data) = reader1.read() {
                    assert_eq!(data.check, !data.value, "reader1: torn read!");
                }
            }
        });

        let h2 = thread::spawn(move || {
            loop {
                if reader2.is_disconnected() && !reader2.has_update() {
                    break;
                }
                if let Some(data) = reader2.read() {
                    assert_eq!(data.check, !data.value, "reader2: torn read!");
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

        h1.join().unwrap();
        h2.join().unwrap();
    }
}
