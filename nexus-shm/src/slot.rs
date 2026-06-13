use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::path::Path;
use std::sync::atomic::{AtomicU64, Ordering};

use nexus_platform::{MapHints, MappedFile};

use crate::error::ShmError;
use crate::pod::Pod;
use crate::segment::{Segment, Status};

// Version and payload are on separate cache lines to prevent false sharing.
const PAYLOAD_OFFSET: usize = 64;

fn data_len<T>() -> usize {
    PAYLOAD_OFFSET + size_of::<T>()
}

fn version_ptr(segment: &Segment) -> *mut AtomicU64 {
    segment.data().cast::<AtomicU64>()
}

fn payload_ptr<T>(segment: &Segment) -> *mut T {
    unsafe { segment.data().add(PAYLOAD_OFFSET).cast::<T>() }
}

/// Writes into a shared-memory seqlock slot.
///
/// Creates the backing file. Multiple threads may share a writer via `Arc`.
/// Dropped when the creating process exits; marks the segment dead on drop.
pub struct ShmSlotWriter<T: Pod> {
    segment: Segment,
    _marker: PhantomData<T>,
}

/// Reads from a shared-memory seqlock slot.
///
/// Attaches to a file created by [`ShmSlotWriter`].
/// Maintains a shadow copy of the last consistent read for stale-read fallback.
pub struct ShmSlotReader<T: Pod> {
    segment: Segment,
    buf: Box<MaybeUninit<T>>,
    shadow: Box<MaybeUninit<T>>,
    shadow_valid: bool,
    _marker: PhantomData<T>,
}

/// Result of [`ShmSlotReader::read`].
pub enum SlotRead<'a, T> {
    /// Consistent value from the current write epoch.
    Fresh(&'a T),
    /// Writer is dead mid-write; last successfully read value returned.
    Stale(&'a T),
    /// No write has occurred since the slot was created.
    Empty,
}

impl<T: Pod> ShmSlotWriter<T> {
    /// Create a new slot backed by `path`.
    ///
    /// Fails if another live writer owns the file.
    pub fn create(path: impl AsRef<Path>, hints: MapHints) -> Result<Self, ShmError> {
        assert!(
            align_of::<T>() <= PAYLOAD_OFFSET,
            "align_of::<T>() = {} exceeds PAYLOAD_OFFSET = {}; use a repr(C) type with smaller alignment",
            align_of::<T>(),
            PAYLOAD_OFFSET,
        );
        let data_len = data_len::<T>();
        let total = Segment::total_size(data_len)?;
        let mf = MappedFile::create(path.as_ref(), total)?;
        let segment = Segment::create(mf, data_len, hints)?;
        // Zero the data region: version = 0 means "never written".
        unsafe { std::ptr::write_bytes(segment.data(), 0, data_len) };
        Ok(Self {
            segment,
            _marker: PhantomData,
        })
    }

    /// Publish `value` to all readers.
    ///
    /// Odd version marks mid-write; readers retry or fall back to shadow.
    pub fn write(&self, value: &T) {
        let ver = unsafe { &*version_ptr(&self.segment) };
        let dst = payload_ptr::<T>(&self.segment);
        ver.fetch_add(1, Ordering::Release);
        unsafe { std::ptr::copy_nonoverlapping(value as *const T, dst, 1) };
        ver.fetch_add(1, Ordering::Release);
    }
}

// SAFETY: `Segment` wraps a shared mmap; `write` uses the seqlock protocol
// for synchronization. Multiple concurrent `write` callers would corrupt the
// seqlock invariant — callers must serialize writes externally if needed.
// Sharing via `Arc` is safe when writes are externally serialized.
unsafe impl<T: Pod + Send> Send for ShmSlotWriter<T> {}
unsafe impl<T: Pod + Sync> Sync for ShmSlotWriter<T> {}

impl<T: Pod> ShmSlotReader<T> {
    /// Attach to an existing slot at `path`.
    pub fn attach(path: impl AsRef<Path>) -> Result<Self, ShmError> {
        let mf = MappedFile::open(path.as_ref())?;
        let segment = Segment::attach(mf)?;
        Ok(Self {
            segment,
            buf: Box::new(MaybeUninit::uninit()),
            shadow: Box::new(MaybeUninit::uninit()),
            shadow_valid: false,
            _marker: PhantomData,
        })
    }

    /// Read the latest value.
    ///
    /// Retries on version mismatch (writer mid-write). Returns `Stale` with
    /// the last good shadow if the writer died mid-write. Returns `Empty` if
    /// no write has occurred and no shadow exists.
    pub fn read(&mut self) -> SlotRead<'_, T> {
        let ver = unsafe { &*version_ptr(&self.segment) };
        let src = payload_ptr::<T>(&self.segment).cast_const();
        loop {
            let v1 = ver.load(Ordering::Acquire);
            if v1 == 0 {
                return SlotRead::Empty;
            }
            if v1 & 1 == 1 {
                match self.segment.status() {
                    Status::Alive => {
                        std::hint::spin_loop();
                        continue;
                    }
                    _ => {
                        return if self.shadow_valid {
                            SlotRead::Stale(unsafe { self.shadow.assume_init_ref() })
                        } else {
                            SlotRead::Empty
                        };
                    }
                }
            }
            unsafe { std::ptr::copy_nonoverlapping(src, self.buf.as_mut_ptr(), 1) };
            let v2 = ver.load(Ordering::Acquire);
            if v1 != v2 {
                std::hint::spin_loop();
                continue;
            }
            unsafe {
                std::ptr::copy_nonoverlapping(self.buf.as_ptr(), self.shadow.as_mut_ptr(), 1);
            }
            self.shadow_valid = true;
            return SlotRead::Fresh(unsafe { self.shadow.assume_init_ref() });
        }
    }
}

unsafe impl<T: Pod + Send> Send for ShmSlotReader<T> {}

#[cfg(test)]
mod tests {
    use super::*;
    use nexus_platform::MapHints;

    fn temp_path(name: &str) -> std::path::PathBuf {
        std::env::temp_dir().join(format!("nexus-shm-slot-{}-{}", std::process::id(), name))
    }

    #[test]
    fn empty_before_first_write() {
        let path = temp_path("empty");
        let _ = std::fs::remove_file(&path);

        let _writer = ShmSlotWriter::<u64>::create(&path, MapHints::default()).unwrap();
        let mut reader = ShmSlotReader::<u64>::attach(&path).unwrap();

        assert!(matches!(reader.read(), SlotRead::Empty));

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn write_read_roundtrip() {
        let path = temp_path("roundtrip");
        let _ = std::fs::remove_file(&path);

        let writer = ShmSlotWriter::<u64>::create(&path, MapHints::default()).unwrap();
        let mut reader = ShmSlotReader::<u64>::attach(&path).unwrap();

        writer.write(&42u64);
        match reader.read() {
            SlotRead::Fresh(v) => assert_eq!(*v, 42),
            _ => panic!("expected Fresh"),
        }

        writer.write(&99u64);
        match reader.read() {
            SlotRead::Fresh(v) => assert_eq!(*v, 99),
            _ => panic!("expected Fresh after second write"),
        }

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn reader_sees_latest_after_multiple_writes() {
        let path = temp_path("multi");
        let _ = std::fs::remove_file(&path);

        let writer = ShmSlotWriter::<u64>::create(&path, MapHints::default()).unwrap();
        let mut reader = ShmSlotReader::<u64>::attach(&path).unwrap();

        for i in 0u64..1000 {
            writer.write(&i);
        }
        match reader.read() {
            SlotRead::Fresh(v) => assert_eq!(*v, 999),
            _ => panic!("expected Fresh"),
        }

        std::fs::remove_file(&path).unwrap();
    }

    #[derive(Clone, Copy)]
    #[repr(C)]
    struct Price {
        bid: f64,
        ask: f64,
        seq: u64,
    }
    unsafe impl Pod for Price {}

    #[test]
    fn struct_pod_roundtrip() {
        let path = temp_path("struct");
        let _ = std::fs::remove_file(&path);

        let writer = ShmSlotWriter::<Price>::create(&path, MapHints::default()).unwrap();
        let mut reader = ShmSlotReader::<Price>::attach(&path).unwrap();

        writer.write(&Price {
            bid: 100.5,
            ask: 100.6,
            seq: 7,
        });
        match reader.read() {
            SlotRead::Fresh(p) => {
                assert_eq!(p.bid, 100.5);
                assert_eq!(p.ask, 100.6);
                assert_eq!(p.seq, 7);
            }
            _ => panic!("expected Fresh"),
        }

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn writer_drop_marks_dead_reader_still_reads() {
        let path = temp_path("dead");
        let _ = std::fs::remove_file(&path);

        let writer = ShmSlotWriter::<u64>::create(&path, MapHints::default()).unwrap();
        let mut reader = ShmSlotReader::<u64>::attach(&path).unwrap();

        writer.write(&55u64);
        match reader.read() {
            SlotRead::Fresh(v) => assert_eq!(*v, 55),
            _ => panic!("expected Fresh"),
        }

        drop(writer); // marks segment Dead, version left at even value

        // Even version + Dead segment → reader still sees a consistent value.
        match reader.read() {
            SlotRead::Fresh(v) | SlotRead::Stale(v) => assert_eq!(*v, 55),
            SlotRead::Empty => panic!("unexpected Empty after write"),
        }

        std::fs::remove_file(&path).unwrap();
    }
}
