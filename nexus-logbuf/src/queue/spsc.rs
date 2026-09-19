//! Single-producer single-consumer byte ring buffer.
//!
//! # Design
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────────────┐
//! │ Shared:                                                                 │
//! │   head: CachePadded<AtomicUsize>  ← Consumer writes, producer reads     │
//! │   buffer: *mut u8                                                       │
//! │   capacity: usize                 (power of 2)                          │
//! │   mask: usize                     (capacity - 1)                        │
//! └─────────────────────────────────────────────────────────────────────────┘
//!
//! ┌─────────────────────────────────┐   ┌─────────────────────────────────┐
//! │ Producer:                       │   │ Consumer:                       │
//! │   tail: usize        (local)    │   │   head: usize        (local)    │
//! │   cached_head: usize (local)    │   │                                 │
//! └─────────────────────────────────┘   └─────────────────────────────────┘
//! ```
//!
//! # Record Layout
//!
//! ```text
//! ┌──────────────────────────────────────────────┐
//! │ len: usize              (8 bytes on 64-bit)   │ ← payload length / commit marker
//! ├──────────────────────────────────────────────┤
//! │ payload: [u8; len]      (variable)           │ ← raw bytes
//! ├──────────────────────────────────────────────┤
//! │ padding: [u8; ...]      (0-7 bytes)          │ ← align to 8-byte boundary
//! └──────────────────────────────────────────────┘
//! ```
//!
//! Records are packed contiguously. Total record size is
//! `align8(size_of::<usize>() + len)`. Using `usize` for the header ensures
//! the payload starts at a word-aligned offset.
//!
//! # Len Field Encoding
//!
//! - `len == 0`: Not committed, consumer waits
//! - `len > 0, high bit clear`: Committed record, payload is `len` bytes
//! - `len high bit set`: Skip marker, advance by `len & LEN_MASK` bytes

use std::alloc::{Layout, alloc_zeroed, dealloc, handle_alloc_error};
use std::cell::Cell;
use std::ops::{Deref, DerefMut};
use std::ptr;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering, fence};

use crossbeam_utils::CachePadded;

use crate::{BufferFull, LEN_MASK, SKIP_BIT, align8};

/// Header size in bytes — one system word (`usize`).
///
/// On 64-bit this is 8 bytes, ensuring the payload starts at 8-byte alignment.
const HEADER_SIZE: usize = std::mem::size_of::<usize>();

/// Creates a bounded SPSC byte ring buffer.
///
/// Capacity is rounded up to the next power of two.
///
/// # Panics
///
/// Panics if `capacity` is zero or less than 16 bytes.
pub fn new(capacity: usize) -> (Producer, Consumer) {
    assert!(capacity >= 16, "capacity must be at least 16 bytes");

    let capacity = capacity.next_power_of_two();
    let mask = capacity - 1;

    // Allocate buffer, zero-initialized, 8-byte aligned for atomic len stamps
    let layout = Layout::from_size_align(capacity, 8)
        .expect("valid layout: capacity is a power of two >= 16, align is 8");
    // SAFETY: Layout is valid — capacity >= 16 (power of two), align is 8.
    let buffer_ptr = unsafe { alloc_zeroed(layout) };
    if buffer_ptr.is_null() {
        handle_alloc_error(layout);
    }

    let shared = Arc::new(Shared {
        head: CachePadded::new(AtomicUsize::new(0)),
        buffer: buffer_ptr,
        capacity,
        mask,
    });

    (
        Producer {
            tail: Cell::new(0),
            cached_head: Cell::new(0),
            shared: Arc::clone(&shared),
        },
        Consumer {
            head: Cell::new(0),
            shared,
        },
    )
}

struct Shared {
    /// Consumer's read position. Updated by consumer, read by producer.
    head: CachePadded<AtomicUsize>,
    /// Buffer pointer.
    buffer: *mut u8,
    /// Buffer capacity (power of 2).
    capacity: usize,
    /// Mask for wrapping (capacity - 1).
    mask: usize,
}

// SAFETY: Buffer is only accessed by one producer and one consumer.
// The atomic head provides synchronization between them.
unsafe impl Send for Shared {}
// SAFETY: All mutable access to the buffer is partitioned between
// producer (tail region) and consumer (head region) via atomic offsets.
unsafe impl Sync for Shared {}

impl Drop for Shared {
    fn drop(&mut self) {
        let layout = Layout::from_size_align(self.capacity, 8)
            .expect("valid layout: capacity was validated at construction");
        // SAFETY: buffer was allocated with alloc_zeroed using this exact layout.
        // Shared is only dropped once (Arc prevents earlier drops).
        unsafe { dealloc(self.buffer, layout) };
    }
}

// ============================================================================
// Producer
// ============================================================================

/// Producer endpoint of the SPSC ring buffer.
///
/// Use [`try_claim`](Producer::try_claim) to claim space for writing.
pub struct Producer {
    /// Local tail position (free-running).
    tail: Cell<usize>,
    /// Cached head position (Rigtorp optimization).
    cached_head: Cell<usize>,
    /// Shared state.
    shared: Arc<Shared>,
}

// SAFETY: Producer is only used from one thread (not Clone, &mut self API).
// Sending it to another thread is safe; using from multiple threads is not.
unsafe impl Send for Producer {}

impl Producer {
    /// Attempts to claim space for a record with the given payload length.
    ///
    /// Returns a [`WriteClaim`] that can be written to and then committed.
    ///
    /// # Errors
    ///
    /// Returns [`BufferFull`] if the buffer has no space for the record.
    ///
    /// # Panics
    ///
    /// Panics if `len == 0`. The wire format reserves `len == 0` as the
    /// "uncommitted" sentinel — letting it through would silently hang the
    /// consumer. Aborting a non-zero claim is fully supported (drop the
    /// [`WriteClaim`] without committing); only claiming zero bytes upfront
    /// is forbidden.
    ///
    /// # Safety Contract
    ///
    /// `len` must not exceed `LEN_MASK`. On 64-bit this is ~9.2 exabytes
    /// (unreachable in practice). On 32-bit, records >2GB could set
    /// `SKIP_BIT` and corrupt the stream — enforced with `assert!`.
    /// On 64-bit this is checked with `debug_assert!` only.
    #[inline]
    pub fn try_claim(&mut self, len: usize) -> Result<WriteClaim<'_>, BufferFull> {
        assert!(len > 0, "payload length must be non-zero");
        #[cfg(target_pointer_width = "32")]
        assert!(len <= LEN_MASK, "payload too large for 32-bit logbuf");
        #[cfg(not(target_pointer_width = "32"))]
        debug_assert!(len <= LEN_MASK, "payload too large");

        let record_size = align8(HEADER_SIZE + len);

        // Check if we have space
        let tail = self.tail.get();
        let available = self.shared.capacity - (tail.wrapping_sub(self.cached_head.get()));

        if available < record_size {
            // Reload head from shared state
            self.cached_head
                .set(self.shared.head.load(Ordering::Relaxed));
            fence(Ordering::Acquire);

            let available = self.shared.capacity - (tail.wrapping_sub(self.cached_head.get()));
            if available < record_size {
                return Err(BufferFull);
            }
        }

        // Check if record fits before buffer end, or needs wrap
        let offset = tail & self.shared.mask;
        let space_to_end = self.shared.capacity - offset;

        if space_to_end < record_size {
            // Need to wrap. First check if we have space for padding + record at start.
            let total_needed = space_to_end + record_size;
            let available = self.shared.capacity - (tail.wrapping_sub(self.cached_head.get()));

            if available < total_needed {
                // Reload and recheck
                self.cached_head
                    .set(self.shared.head.load(Ordering::Relaxed));
                fence(Ordering::Acquire);

                let available = self.shared.capacity - (tail.wrapping_sub(self.cached_head.get()));
                if available < total_needed {
                    return Err(BufferFull);
                }
            }

            // Write padding skip marker
            let buffer = self.shared.buffer;
            let skip_len = space_to_end | SKIP_BIT;
            fence(Ordering::Release);
            // SAFETY: offset is masked to [0, capacity) and 8-byte aligned.
            // Buffer is valid for capacity bytes. We are the sole producer.
            let len_ptr = unsafe { buffer.add(offset) }.cast::<AtomicUsize>();
            // SAFETY: len_ptr points to a valid, aligned, zero-initialized usize
            // within the buffer. AtomicUsize reference is used for store visibility.
            unsafe { &*len_ptr }.store(skip_len, Ordering::Relaxed);

            // Advance tail past padding
            self.tail.set(tail.wrapping_add(space_to_end));
            let new_offset = 0;

            Ok(WriteClaim {
                producer: self,
                offset: new_offset,
                len,
                record_size,
                committed: false,
            })
        } else {
            // Fits without wrapping
            Ok(WriteClaim {
                producer: self,
                offset,
                len,
                record_size,
                committed: false,
            })
        }
    }

    /// Returns the capacity of the buffer.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.shared.capacity
    }

    /// Best-effort hint: returns `true` if the consumer has likely been dropped.
    ///
    /// Uses `Arc::strong_count` which is inherently racy — the count can
    /// change between the check and the caller's next action. Suitable for
    /// graceful shutdown detection, not for correctness. For reliable
    /// disconnection detection, use the channel layer (`channel::spsc`)
    /// which tracks disconnection via dedicated atomic flags.
    // Decision: No AtomicBool flag at the raw queue level. The channel
    // layer (channel::spsc) provides reliable detection via dedicated
    // flags. Adding one here would cost an atomic on every push/pop
    // for a feature only the channel layer needs.
    #[inline]
    pub fn is_disconnected(&self) -> bool {
        Arc::strong_count(&self.shared) == 1
    }
}

impl std::fmt::Debug for Producer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Producer")
            .field("capacity", &self.capacity())
            .finish_non_exhaustive()
    }
}

// ============================================================================
// WriteClaim
// ============================================================================

/// A claimed region for writing a record.
///
/// Dereferences to `&mut [u8]` for the payload region. Call [`commit`](WriteClaim::commit)
/// when done writing to publish the record. If dropped without committing, a skip
/// marker is written so the consumer can advance past the dead region.
///
/// # Important
///
/// Leaking a `WriteClaim` via [`mem::forget`](std::mem::forget) will permanently
/// block the consumer at this record's offset. This is not undefined behavior
/// but causes an unrecoverable deadlock. Always drop or explicitly abort claims.
pub struct WriteClaim<'a> {
    producer: &'a mut Producer,
    offset: usize,
    len: usize,
    record_size: usize,
    committed: bool,
}

impl WriteClaim<'_> {
    /// Commits the record, making it visible to the consumer.
    #[inline]
    pub fn commit(mut self) {
        self.do_commit();
        self.committed = true;
    }

    #[inline]
    fn do_commit(&mut self) {
        let buffer = self.producer.shared.buffer;
        // SAFETY: offset is within [0, capacity), 8-byte aligned. Buffer is valid.
        let len_ptr = unsafe { buffer.add(self.offset) }.cast::<AtomicUsize>();

        // Release fence: ensures payload writes are visible before len store
        fence(Ordering::Release);
        // SAFETY: len_ptr points to a valid, aligned usize within the buffer.
        unsafe { &*len_ptr }.store(self.len, Ordering::Relaxed);

        // Advance tail
        self.producer
            .tail
            .set(self.producer.tail.get().wrapping_add(self.record_size));
    }

    /// Returns the length of the payload region.
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the payload is empty (always false, len must be > 0).
    #[inline]
    pub fn is_empty(&self) -> bool {
        false
    }
}

impl Deref for WriteClaim<'_> {
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &Self::Target {
        let buffer = self.producer.shared.buffer;
        // SAFETY: offset + HEADER_SIZE is within the buffer. The claim owns
        // exclusive access to this region via &mut Producer borrow.
        let payload_ptr = unsafe { buffer.add(self.offset + HEADER_SIZE) };
        // SAFETY: payload_ptr is valid for self.len bytes, word-aligned,
        // and exclusively owned by this claim. Lifetime tied to &self.
        unsafe { std::slice::from_raw_parts(payload_ptr, self.len) }
    }
}

impl DerefMut for WriteClaim<'_> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        let buffer = self.producer.shared.buffer;
        // SAFETY: offset + HEADER_SIZE is within the buffer. Exclusive access
        // guaranteed by &mut self (only one WriteClaim exists per try_claim).
        let payload_ptr = unsafe { buffer.add(self.offset + HEADER_SIZE) };
        // SAFETY: payload_ptr is valid for self.len bytes, word-aligned,
        // and exclusively owned by this claim. Lifetime tied to &mut self.
        unsafe { std::slice::from_raw_parts_mut(payload_ptr, self.len) }
    }
}

impl Drop for WriteClaim<'_> {
    fn drop(&mut self) {
        if !self.committed {
            // Write skip marker so consumer can advance past this region
            let buffer = self.producer.shared.buffer;
            // SAFETY: offset is within [0, capacity), 8-byte aligned. Buffer is valid.
            let len_ptr = unsafe { buffer.add(self.offset) }.cast::<AtomicUsize>();
            let skip_len = self.record_size | SKIP_BIT;

            fence(Ordering::Release);
            // SAFETY: len_ptr points to a valid, aligned usize within the buffer.
            unsafe { &*len_ptr }.store(skip_len, Ordering::Relaxed);

            // Advance tail past the dead region
            self.producer
                .tail
                .set(self.producer.tail.get().wrapping_add(self.record_size));
        }
    }
}

// ============================================================================
// Consumer
// ============================================================================

/// Consumer endpoint of the SPSC ring buffer.
///
/// Use [`try_claim`](Consumer::try_claim) to claim the next record for reading.
pub struct Consumer {
    /// Local head position (free-running).
    head: Cell<usize>,
    /// Shared state.
    shared: Arc<Shared>,
}

// SAFETY: Consumer is only used from one thread (not Clone, &mut self API).
// Sending it to another thread is safe; using from multiple threads is not.
unsafe impl Send for Consumer {}

impl Consumer {
    /// Attempts to claim the next record for reading.
    ///
    /// Returns a [`ReadClaim`] if a record is available. The claim dereferences
    /// to `&[u8]` for the payload. When dropped, the record region is zeroed
    /// and the head is advanced.
    ///
    /// Returns `None` if no committed record is available.
    #[inline]
    pub fn try_claim(&mut self) -> Option<ReadClaim<'_>> {
        let buffer = self.shared.buffer;

        loop {
            let offset = self.head.get() & self.shared.mask;
            // SAFETY: offset is masked to [0, capacity), always 8-byte aligned
            // (head advances by align8'd record sizes). Buffer is valid.
            let len_ptr = unsafe { buffer.add(offset) }.cast::<AtomicUsize>();

            // Relaxed atomic load, then Acquire fence for payload visibility
            // SAFETY: len_ptr points to a valid, aligned usize within the buffer.
            let len_raw = unsafe { &*len_ptr }.load(Ordering::Relaxed);
            fence(Ordering::Acquire);

            if len_raw == 0 {
                // Not committed yet
                return None;
            }

            if len_raw & SKIP_BIT != 0 {
                // Skip marker: zero the region and advance
                let skip_size = len_raw & LEN_MASK;
                // Zero payload first, then stamp last (mirrors write path)
                if skip_size > HEADER_SIZE {
                    // SAFETY: offset + HEADER_SIZE .. offset + skip_size is within
                    // the buffer. Consumer has exclusive read access to this region.
                    unsafe {
                        ptr::write_bytes(
                            buffer.add(offset + HEADER_SIZE),
                            0,
                            skip_size - HEADER_SIZE,
                        );
                    }
                }
                // Ensure payload zeroing completes before clearing stamp
                fence(Ordering::Release);
                // SAFETY: len_ptr is still valid, computed above.
                unsafe { &*len_ptr }.store(0, Ordering::Relaxed);

                self.head.set(self.head.get().wrapping_add(skip_size));

                // Ensure stamp clear completes before head advance
                fence(Ordering::Release);
                self.shared.head.store(self.head.get(), Ordering::Relaxed);

                // Continue to check next position
                continue;
            }

            // Valid record
            let len = len_raw;
            let record_size = align8(HEADER_SIZE + len);

            return Some(ReadClaim {
                consumer: self,
                offset,
                len,
                record_size,
            });
        }
    }

    /// Returns the capacity of the buffer.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.shared.capacity
    }

    /// Best-effort hint: returns `true` if the producer has likely been dropped.
    ///
    /// See [`Producer::is_disconnected`] for caveats — uses `Arc::strong_count`.
    #[inline]
    pub fn is_disconnected(&self) -> bool {
        Arc::strong_count(&self.shared) == 1
    }
}

impl std::fmt::Debug for Consumer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Consumer")
            .field("capacity", &self.capacity())
            .finish_non_exhaustive()
    }
}

// ============================================================================
// ReadClaim
// ============================================================================

/// A claimed record for reading.
///
/// Dereferences to `&[u8]` for the payload. When dropped, the record region
/// is zeroed and the head is advanced, freeing space for the producer.
pub struct ReadClaim<'a> {
    consumer: &'a mut Consumer,
    offset: usize,
    len: usize,
    record_size: usize,
}

impl ReadClaim<'_> {
    /// Returns the length of the payload.
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the payload is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl Deref for ReadClaim<'_> {
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &Self::Target {
        let buffer = self.consumer.shared.buffer;
        // SAFETY: offset + HEADER_SIZE is within the buffer. The claim owns
        // exclusive read access via &mut Consumer borrow.
        let payload_ptr = unsafe { buffer.add(self.offset + HEADER_SIZE) };
        // SAFETY: payload_ptr is valid for self.len bytes. The producer has
        // finished writing (len was non-zero, preceded by Release fence).
        unsafe { std::slice::from_raw_parts(payload_ptr, self.len) }
    }
}

impl Drop for ReadClaim<'_> {
    fn drop(&mut self) {
        let buffer = self.consumer.shared.buffer;

        // Zero payload first, then stamp last (mirrors write path)
        if self.record_size > HEADER_SIZE {
            // SAFETY: offset + HEADER_SIZE .. offset + record_size is within
            // the buffer. Consumer owns this region exclusively.
            unsafe {
                ptr::write_bytes(
                    buffer.add(self.offset + HEADER_SIZE),
                    0,
                    self.record_size - HEADER_SIZE,
                );
            }
        }
        // Ensure payload zeroing completes before clearing stamp
        fence(Ordering::Release);
        // SAFETY: offset is within [0, capacity), 8-byte aligned. Buffer is valid.
        let len_ptr = unsafe { buffer.add(self.offset) }.cast::<AtomicUsize>();
        // SAFETY: len_ptr points to a valid, aligned usize within the buffer.
        unsafe { &*len_ptr }.store(0, Ordering::Relaxed);

        // Advance head
        let new_head = self.consumer.head.get().wrapping_add(self.record_size);
        self.consumer.head.set(new_head);

        // Ensure stamp clear completes before head advance
        fence(Ordering::Release);
        self.consumer.shared.head.store(new_head, Ordering::Relaxed);
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_write_read() {
        let (mut prod, mut cons) = new(1024);

        let payload = b"hello world";
        let mut claim = prod.try_claim(payload.len()).unwrap();
        claim.copy_from_slice(payload);
        claim.commit();

        let record = cons.try_claim().unwrap();
        assert_eq!(&*record, payload);
    }

    #[test]
    fn empty_returns_none() {
        let (_, mut cons) = new(1024);
        assert!(cons.try_claim().is_none());
    }

    #[test]
    fn multiple_records() {
        let (mut prod, mut cons) = new(1024);

        for i in 0..10 {
            let payload = format!("message {}", i);
            let mut claim = prod.try_claim(payload.len()).unwrap();
            claim.copy_from_slice(payload.as_bytes());
            claim.commit();
        }

        for i in 0..10 {
            let record = cons.try_claim().unwrap();
            let expected = format!("message {}", i);
            assert_eq!(&*record, expected.as_bytes());
        }

        assert!(cons.try_claim().is_none());
    }

    #[test]
    fn aborted_claim_creates_skip() {
        let (mut prod, mut cons) = new(1024);

        // Claim and drop without committing
        {
            let mut claim = prod.try_claim(10).unwrap();
            claim.copy_from_slice(b"0123456789");
            // drop without commit
        }

        // Write another record
        {
            let mut claim = prod.try_claim(5).unwrap();
            claim.copy_from_slice(b"hello");
            claim.commit();
        }

        // Consumer should skip the aborted record and read the committed one
        let record = cons.try_claim().unwrap();
        assert_eq!(&*record, b"hello");
    }

    #[test]
    fn wrap_around() {
        let (mut prod, mut cons) = new(64);

        // Fill with messages that will cause wrap-around
        for i in 0..20 {
            let payload = format!("msg{:02}", i);
            loop {
                match prod.try_claim(payload.len()) {
                    Ok(mut claim) => {
                        claim.copy_from_slice(payload.as_bytes());
                        claim.commit();
                        break;
                    }
                    Err(_) => {
                        // Drain some
                        while cons.try_claim().is_some() {}
                    }
                }
            }
        }
    }

    #[test]
    fn full_returns_error() {
        let (mut prod, _cons) = new(64);

        // Fill the buffer
        let mut count = 0;
        while let Ok(mut claim) = prod.try_claim(8) {
            claim.copy_from_slice(b"12345678");
            claim.commit();
            count += 1;
        }

        assert!(count > 0);
        assert!(prod.try_claim(8).is_err());
    }

    #[test]
    fn cross_thread() {
        use std::thread;

        let (mut prod, mut cons) = new(4096);

        let producer = thread::spawn(move || {
            for i in 0..10_000u64 {
                let payload = i.to_le_bytes();
                loop {
                    match prod.try_claim(payload.len()) {
                        Ok(mut claim) => {
                            claim.copy_from_slice(&payload);
                            claim.commit();
                            break;
                        }
                        Err(_) => std::hint::spin_loop(),
                    }
                }
            }
        });

        let consumer = thread::spawn(move || {
            let mut received = 0u64;
            while received < 10_000 {
                if let Some(record) = cons.try_claim() {
                    let value = u64::from_le_bytes((*record).try_into().unwrap());
                    assert_eq!(value, received);
                    received += 1;
                } else {
                    std::hint::spin_loop();
                }
            }
        });

        producer.join().unwrap();
        consumer.join().unwrap();
    }

    #[test]
    fn disconnection_detection() {
        let (prod, cons) = new(1024);

        assert!(!prod.is_disconnected());
        assert!(!cons.is_disconnected());

        drop(cons);
        assert!(prod.is_disconnected());
    }

    #[test]
    #[should_panic(expected = "capacity must be at least 16")]
    fn tiny_capacity_panics() {
        let _ = new(8);
    }

    #[test]
    #[should_panic(expected = "payload length must be non-zero")]
    fn zero_len_panics() {
        let (mut prod, _) = new(1024);
        let _ = prod.try_claim(0);
    }

    #[test]
    fn capacity_rounds_to_power_of_two() {
        let (prod, _) = new(100);
        assert_eq!(prod.capacity(), 128);

        let (prod, _) = new(1000);
        assert_eq!(prod.capacity(), 1024);
    }

    #[test]
    fn variable_length_records() {
        let (mut prod, mut cons) = new(4096);

        let messages = [
            "a",
            "hello",
            "this is a longer message",
            "x",
            "medium length",
        ];

        for msg in &messages {
            let mut claim = prod.try_claim(msg.len()).unwrap();
            claim.copy_from_slice(msg.as_bytes());
            claim.commit();
        }

        for msg in &messages {
            let record = cons.try_claim().unwrap();
            assert_eq!(&*record, msg.as_bytes());
        }
    }

    /// High-volume stress test with variable-length messages.
    ///
    /// Tests correctness under sustained load with wrap-around.
    #[test]
    fn stress_high_volume() {
        use std::thread;

        const COUNT: u64 = 1_000_000;
        const BUFFER_SIZE: usize = 64 * 1024; // 64KB

        let (mut prod, mut cons) = new(BUFFER_SIZE);

        let producer = thread::spawn(move || {
            for i in 0..COUNT {
                // Variable length: 8-64 bytes based on sequence
                let len = 8 + ((i % 8) * 8) as usize;
                let mut payload = vec![0u8; len];
                // Write sequence number at start
                payload[..8].copy_from_slice(&i.to_le_bytes());

                loop {
                    match prod.try_claim(len) {
                        Ok(mut claim) => {
                            claim.copy_from_slice(&payload);
                            claim.commit();
                            break;
                        }
                        Err(_) => std::hint::spin_loop(),
                    }
                }
            }
        });

        let consumer = thread::spawn(move || {
            let mut received = 0u64;
            while received < COUNT {
                if let Some(record) = cons.try_claim() {
                    // Verify sequence number
                    let seq = u64::from_le_bytes(record[..8].try_into().unwrap());
                    assert_eq!(seq, received, "sequence mismatch at {}", received);

                    // Verify expected length
                    let expected_len = 8 + ((received % 8) * 8) as usize;
                    assert_eq!(
                        record.len(),
                        expected_len,
                        "length mismatch at {}",
                        received
                    );

                    received += 1;
                } else {
                    std::hint::spin_loop();
                }
            }
            received
        });

        producer.join().unwrap();
        let received = consumer.join().unwrap();
        assert_eq!(received, COUNT);
    }

    /// Stress test with maximum contention - tiny buffer, high throughput.
    #[test]
    fn stress_high_contention() {
        use std::thread;

        const COUNT: u64 = 100_000;
        const BUFFER_SIZE: usize = 256; // Tiny buffer forces constant wrap-around

        let (mut prod, mut cons) = new(BUFFER_SIZE);

        let producer = thread::spawn(move || {
            for i in 0..COUNT {
                let payload = i.to_le_bytes();
                loop {
                    match prod.try_claim(payload.len()) {
                        Ok(mut claim) => {
                            claim.copy_from_slice(&payload);
                            claim.commit();
                            break;
                        }
                        Err(_) => std::hint::spin_loop(),
                    }
                }
            }
        });

        let consumer = thread::spawn(move || {
            let mut received = 0u64;
            let mut sum = 0u64;
            while received < COUNT {
                if let Some(record) = cons.try_claim() {
                    let value = u64::from_le_bytes((*record).try_into().unwrap());
                    assert_eq!(value, received);
                    sum = sum.wrapping_add(value);
                    received += 1;
                } else {
                    std::hint::spin_loop();
                }
            }
            sum
        });

        producer.join().unwrap();
        let sum = consumer.join().unwrap();
        // Sum of 0..COUNT = COUNT * (COUNT-1) / 2
        let expected = COUNT * (COUNT - 1) / 2;
        assert_eq!(sum, expected);
    }

    /// Payload pointers must be word-aligned so users can write aligned structs.
    #[test]
    fn payload_is_word_aligned() {
        let (mut prod, mut cons) = new(1024);

        // Test several payload sizes to cover padding edge cases
        for len in [1, 3, 7, 8, 13, 64, 255] {
            let mut claim = prod.try_claim(len).unwrap();
            let ptr = claim.as_mut_ptr();
            assert_eq!(
                ptr as usize % std::mem::align_of::<usize>(),
                0,
                "WriteClaim payload not word-aligned for len={len}"
            );
            claim.commit();

            let record = cons.try_claim().unwrap();
            let ptr = record.as_ptr();
            assert_eq!(
                ptr as usize % std::mem::align_of::<usize>(),
                0,
                "ReadClaim payload not word-aligned for len={len}"
            );
        }
    }
}

// =============================================================================
// Proptests
// =============================================================================

#[cfg(test)]
mod proptests {
    use super::*;
    use proptest::prelude::*;
    use std::collections::VecDeque;

    /// Operation against an SPSC ring buffer under test.
    #[derive(Debug, Clone)]
    enum Op {
        /// Claim `len` bytes, write a recognizable payload, and commit.
        Write { len: usize },
        /// Claim `len` bytes and drop without committing (skip-marker path).
        Abort { len: usize },
        /// Attempt to read and release the next record.
        Read,
    }

    fn op_strategy() -> impl Strategy<Value = Op> {
        prop_oneof![
            (1usize..48).prop_map(|len| Op::Write { len }),
            (1usize..48).prop_map(|len| Op::Abort { len }),
            Just(Op::Read),
        ]
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(500))]

        /// Fuzz write/abort/read interleaving.
        ///
        /// Drives the SPSC queue from a single thread with random
        /// commit/abort/read sequences against small power-of-two
        /// capacities, so records routinely straddle the ring boundary
        /// (exercising the skip-marker/wraparound path). Tracks every
        /// committed payload in an oracle queue:
        ///
        /// - a successful `Read` must match the oldest committed payload
        ///   exactly (byte-for-byte, correct length, correct order) --
        ///   the "record-length stamping" invariant
        /// - `Read` returning nothing is only valid when the oracle is
        ///   also empty -- with a single thread and no concurrent writer,
        ///   any committed-but-unread record must be immediately visible,
        ///   so this cross-checks the head/tail occupancy bookkeeping
        /// - after draining, the oracle must be fully empty -- nothing
        ///   committed is ever lost or duplicated
        #[test]
        fn fuzz_write_abort_read_roundtrip(
            capacity_pow in 4u32..9,
            ops in proptest::collection::vec(op_strategy(), 1..300),
        ) {
            let capacity = 1usize << capacity_pow;
            let (mut producer, mut consumer) = new(capacity);

            let mut expected: VecDeque<Vec<u8>> = VecDeque::new();
            let mut tag: u8 = 0;

            for op in &ops {
                match op {
                    Op::Write { len } => {
                        if let Ok(mut claim) = producer.try_claim(*len) {
                            tag = tag.wrapping_add(1);
                            let payload = vec![tag; *len];
                            claim.copy_from_slice(&payload);
                            claim.commit();
                            expected.push_back(payload);
                        }
                    }
                    Op::Abort { len } => {
                        if let Ok(_claim) = producer.try_claim(*len) {
                            // Dropped without commit: writes a skip marker.
                        }
                    }
                    Op::Read => match consumer.try_claim() {
                        Some(record) => {
                            let want = expected.pop_front();
                            prop_assert_eq!(
                                want.as_deref(),
                                Some(&*record),
                                "read returned unexpected payload"
                            );
                        }
                        None => {
                            prop_assert!(
                                expected.is_empty(),
                                "read found nothing but {} committed record(s) are still pending",
                                expected.len()
                            );
                        }
                    },
                }
            }

            // Drain everything and confirm nothing was lost or duplicated.
            while let Some(want) = expected.pop_front() {
                let record = consumer
                    .try_claim()
                    .unwrap_or_else(|| panic!("expected record of len {} missing at drain", want.len()));
                prop_assert_eq!(&*record, want.as_slice());
            }
            prop_assert!(consumer.try_claim().is_none());
        }

        /// Fuzz capacity recovery.
        ///
        /// Fills the buffer to `BufferFull` with same-size records, frees
        /// exactly one via `Read`, and asserts a same-size `Write`
        /// immediately succeeds. This is the "occupancy" invariant: a
        /// record's footprint must be fully reclaimed once read, with no
        /// permanent bookkeeping leak.
        #[test]
        fn fuzz_capacity_recovery(
            (capacity, len) in (4u32..9).prop_flat_map(|capacity_pow| {
                let capacity = 1usize << capacity_pow;
                let max_len = (capacity / 4).max(2);
                (Just(capacity), 1usize..max_len)
            }),
        ) {
            let (mut producer, mut consumer) = new(capacity);

            // Fill to BufferFull with same-size records.
            let mut written = 0usize;
            while let Ok(claim) = producer.try_claim(len) {
                claim.commit();
                written += 1;
            }
            prop_assert!(
                written > 0,
                "first write of len {len} did not fit in capacity {capacity}"
            );

            // Free exactly one record.
            consumer
                .try_claim()
                .expect("at least one record was committed");

            // The same-size write must now succeed -- space was reclaimed.
            prop_assert!(
                producer.try_claim(len).is_ok(),
                "write of len {len} did not recover after freeing one record (capacity {capacity})"
            );
        }
    }
}
