use std::marker::PhantomData;
use std::path::Path;
use std::sync::atomic::{AtomicU64, Ordering};

use nexus_platform::{MapHints, MappedFile};

use crate::error::ShmError;
use crate::pod::Pod;
use crate::segment::{Segment, Status};

const TAIL_OFFSET: usize = 0;
const HEAD_OFFSET: usize = 64;
const CAP_OFFSET: usize = 128;
const ELEM_SIZE_OFFSET: usize = 136;
const DATA_OFFSET: usize = 192;

fn ring_tail(segment: &Segment) -> &AtomicU64 {
    unsafe { &*segment.data().add(TAIL_OFFSET).cast::<AtomicU64>() }
}

fn ring_head(segment: &Segment) -> &AtomicU64 {
    unsafe { &*segment.data().add(HEAD_OFFSET).cast::<AtomicU64>() }
}

fn read_capacity(segment: &Segment) -> u64 {
    unsafe { std::ptr::read(segment.data().add(CAP_OFFSET).cast::<u64>()) }
}

fn read_elem_size(segment: &Segment) -> u64 {
    unsafe { std::ptr::read(segment.data().add(ELEM_SIZE_OFFSET).cast::<u64>()) }
}

fn slot_ptr<T>(segment: &Segment, slot_idx: u64) -> *mut T {
    unsafe {
        segment
            .data()
            .add(DATA_OFFSET + slot_idx as usize * size_of::<T>())
            .cast::<T>()
    }
}

/// SPSC ring buffer writer backed by a shared-memory segment.
///
/// Creates the backing file. Only one writer per file; the process that drops
/// the writer marks the segment dead, signaling all readers.
pub struct ShmRingWriter<T: Pod> {
    segment: Segment,
    local_tail: u64,
    cached_head: u64,
    capacity: u64,
    mask: u64,
    _marker: PhantomData<T>,
}

/// SPSC ring buffer reader backed by a shared-memory segment.
pub struct ShmRingReader<T: Pod> {
    segment: Segment,
    local_head: u64,
    cached_tail: u64,
    capacity: u64,
    mask: u64,
    _marker: PhantomData<T>,
}

impl<T: Pod> ShmRingWriter<T> {
    /// Create a new ring buffer at `path` with `capacity` slots.
    ///
    /// `capacity` must be a non-zero power of two.
    /// Fails if another live writer owns the file.
    pub fn create(
        path: impl AsRef<Path>,
        capacity: usize,
        hints: MapHints,
    ) -> Result<Self, ShmError> {
        assert!(
            capacity.is_power_of_two(),
            "capacity must be a non-zero power of two, got {capacity}"
        );
        assert!(
            align_of::<T>() <= DATA_OFFSET,
            "align_of::<T>() = {} exceeds DATA_OFFSET = {DATA_OFFSET}",
            align_of::<T>(),
        );
        let data_len = capacity
            .checked_mul(size_of::<T>())
            .and_then(|s| s.checked_add(DATA_OFFSET))
            .ok_or(ShmError::SizeOverflow)?;
        let total = Segment::total_size(data_len)?;
        let mf = MappedFile::create(path.as_ref(), total)?;
        let segment = Segment::create(mf, data_len, hints)?;
        unsafe {
            std::ptr::write_bytes(segment.data(), 0, data_len);
            std::ptr::write(
                segment.data().add(CAP_OFFSET).cast::<u64>(),
                capacity as u64,
            );
            std::ptr::write(
                segment.data().add(ELEM_SIZE_OFFSET).cast::<u64>(),
                size_of::<T>() as u64,
            );
        }
        Ok(Self {
            segment,
            local_tail: 0,
            cached_head: 0,
            capacity: capacity as u64,
            mask: capacity as u64 - 1,
            _marker: PhantomData,
        })
    }

    /// Push `value` into the ring buffer.
    ///
    /// Returns `false` without writing if the buffer is full.
    pub fn try_push(&mut self, value: &T) -> bool {
        let tail = self.local_tail;
        if tail.wrapping_sub(self.cached_head) >= self.capacity {
            self.cached_head = ring_head(&self.segment).load(Ordering::Acquire);
            if tail.wrapping_sub(self.cached_head) >= self.capacity {
                return false;
            }
        }
        let dst = slot_ptr::<T>(&self.segment, tail & self.mask);
        unsafe { std::ptr::copy_nonoverlapping(value as *const T, dst, 1) };
        self.local_tail = tail.wrapping_add(1);
        ring_tail(&self.segment).store(self.local_tail, Ordering::Release);
        true
    }

    /// Number of slots currently occupied.
    pub fn len(&self) -> usize {
        let head = ring_head(&self.segment).load(Ordering::Acquire);
        self.local_tail.wrapping_sub(head) as usize
    }

    /// `true` if no items are queued.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Maximum number of items the buffer can hold.
    pub fn capacity(&self) -> usize {
        self.capacity as usize
    }
}

unsafe impl<T: Pod + Send> Send for ShmRingWriter<T> {}

impl<T: Pod> ShmRingReader<T> {
    /// Attach to an existing ring buffer at `path`.
    ///
    /// Returns `Err` if the header is corrupt, the element size doesn't match
    /// `size_of::<T>()`, or the mapping is too small for the stored capacity.
    pub fn attach(path: impl AsRef<Path>) -> Result<Self, ShmError> {
        let mf = MappedFile::open(path.as_ref())?;
        let segment = Segment::attach(mf)?;
        let capacity = read_capacity(&segment);
        if !capacity.is_power_of_two() || capacity == 0 {
            return Err(ShmError::CorruptHeader);
        }
        let elem_size = read_elem_size(&segment) as usize;
        if elem_size != size_of::<T>() {
            return Err(ShmError::ElemSizeMismatch {
                written: elem_size,
                expected: size_of::<T>(),
            });
        }
        Ok(Self {
            segment,
            local_head: 0,
            cached_tail: 0,
            capacity,
            mask: capacity - 1,
            _marker: PhantomData,
        })
    }

    /// Pop the next value from the ring buffer.
    ///
    /// Returns `None` if the buffer is empty.
    pub fn try_pop(&mut self) -> Option<T> {
        let head = self.local_head;
        if head == self.cached_tail {
            self.cached_tail = ring_tail(&self.segment).load(Ordering::Acquire);
            if head == self.cached_tail {
                return None;
            }
        }
        let src = slot_ptr::<T>(&self.segment, head & self.mask).cast_const();
        let value = unsafe { std::ptr::read(src) };
        self.local_head = head.wrapping_add(1);
        ring_head(&self.segment).store(self.local_head, Ordering::Release);
        Some(value)
    }

    /// Tier-1 liveness of the writer (atomic status field).
    ///
    /// `Dead` is authoritative. `Alive` may be stale under `panic=abort` or
    /// SIGKILL; use `Segment::peer_liveness` for kernel-level confirmation.
    pub fn writer_status(&self) -> Status {
        self.segment.status()
    }

    /// Maximum number of items the buffer can hold.
    pub fn capacity(&self) -> usize {
        self.capacity as usize
    }
}

unsafe impl<T: Pod + Send> Send for ShmRingReader<T> {}

#[cfg(test)]
mod tests {
    use super::*;
    use nexus_platform::MapHints;

    fn temp_path(name: &str) -> std::path::PathBuf {
        std::env::temp_dir().join(format!("nexus-shm-ring-{}-{}", std::process::id(), name))
    }

    #[test]
    fn empty_on_create() {
        let path = temp_path("empty");
        let _ = std::fs::remove_file(&path);

        let writer = ShmRingWriter::<u64>::create(&path, 4, MapHints::default()).unwrap();
        let mut reader = ShmRingReader::<u64>::attach(&path).unwrap();

        assert!(writer.is_empty());
        assert!(reader.try_pop().is_none());

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn push_pop_roundtrip() {
        let path = temp_path("roundtrip");
        let _ = std::fs::remove_file(&path);

        let mut writer = ShmRingWriter::<u64>::create(&path, 4, MapHints::default()).unwrap();
        let mut reader = ShmRingReader::<u64>::attach(&path).unwrap();

        assert!(writer.try_push(&42));
        assert_eq!(reader.try_pop(), Some(42));
        assert!(reader.try_pop().is_none());

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn fifo_ordering() {
        let path = temp_path("fifo");
        let _ = std::fs::remove_file(&path);

        let mut writer = ShmRingWriter::<u32>::create(&path, 8, MapHints::default()).unwrap();
        let mut reader = ShmRingReader::<u32>::attach(&path).unwrap();

        for i in 0..8u32 {
            assert!(writer.try_push(&i));
        }
        for i in 0..8u32 {
            assert_eq!(reader.try_pop(), Some(i));
        }
        assert!(reader.try_pop().is_none());

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn full_returns_false() {
        let path = temp_path("full");
        let _ = std::fs::remove_file(&path);

        let mut writer = ShmRingWriter::<u64>::create(&path, 2, MapHints::default()).unwrap();
        let _reader = ShmRingReader::<u64>::attach(&path).unwrap();

        assert!(writer.try_push(&1));
        assert!(writer.try_push(&2));
        assert!(!writer.try_push(&3)); // full

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn wrap_around() {
        let path = temp_path("wrap");
        let _ = std::fs::remove_file(&path);

        let mut writer = ShmRingWriter::<u64>::create(&path, 4, MapHints::default()).unwrap();
        let mut reader = ShmRingReader::<u64>::attach(&path).unwrap();

        for round in 0..8u64 {
            for i in 0..4u64 {
                let val = round * 4 + i;
                assert!(writer.try_push(&val), "push failed at val={val}");
            }
            for i in 0..4u64 {
                let expected = round * 4 + i;
                assert_eq!(reader.try_pop(), Some(expected));
            }
        }

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn writer_drop_reader_drains_then_empty() {
        let path = temp_path("drain");
        let _ = std::fs::remove_file(&path);

        let mut writer = ShmRingWriter::<u64>::create(&path, 4, MapHints::default()).unwrap();
        let mut reader = ShmRingReader::<u64>::attach(&path).unwrap();

        writer.try_push(&10);
        writer.try_push(&20);
        drop(writer);

        assert_eq!(reader.try_pop(), Some(10));
        assert_eq!(reader.try_pop(), Some(20));
        assert!(reader.try_pop().is_none());
        assert_eq!(reader.writer_status(), Status::Dead);

        std::fs::remove_file(&path).unwrap();
    }

    #[derive(Clone, Copy)]
    #[repr(C)]
    struct Order {
        price: u64,
        qty: u32,
        side: u8,
        _pad: [u8; 3],
    }
    unsafe impl Pod for Order {}

    #[test]
    fn struct_pod_roundtrip() {
        let path = temp_path("struct");
        let _ = std::fs::remove_file(&path);

        let mut writer = ShmRingWriter::<Order>::create(&path, 8, MapHints::default()).unwrap();
        let mut reader = ShmRingReader::<Order>::attach(&path).unwrap();

        let order = Order {
            price: 10050,
            qty: 100,
            side: 1,
            _pad: [0; 3],
        };
        assert!(writer.try_push(&order));

        let got = reader.try_pop().unwrap();
        assert_eq!(got.price, 10050);
        assert_eq!(got.qty, 100);
        assert_eq!(got.side, 1);

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn threaded_spsc_torture() {
        const COUNT: u64 = 100_000;
        let path = temp_path("threaded");
        let _ = std::fs::remove_file(&path);

        let mut writer = ShmRingWriter::<u64>::create(&path, 256, MapHints::default()).unwrap();
        let mut reader = ShmRingReader::<u64>::attach(&path).unwrap();

        let wt = std::thread::spawn(move || {
            for i in 0..COUNT {
                while !writer.try_push(&i) {
                    std::hint::spin_loop();
                }
            }
        });

        let rt = std::thread::spawn(move || {
            let mut expected = 0u64;
            while expected < COUNT {
                match reader.try_pop() {
                    Some(v) => {
                        assert_eq!(v, expected, "SPSC ordering violation");
                        expected += 1;
                    }
                    None => std::hint::spin_loop(),
                }
            }
        });

        wt.join().unwrap();
        rt.join().unwrap();
        std::fs::remove_file(&path).unwrap();
    }
}
