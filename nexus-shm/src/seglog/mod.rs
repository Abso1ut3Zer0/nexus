mod conductor;
mod error;
mod frame;
mod manifest;
#[cfg(test)]
mod tests;

use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

use crate::segment::Segment;
use nexus_platform::{FileLock, MappedFile};

use crate::MapHints;

use conductor::CleanRequest;
use frame::{ALIGN, FRAME_HDR, align_up, commit_len_ptr, footprint, session_id_ptr};
use manifest::Manifest;

pub use conductor::{Conductor, ConductorBuilder};
pub use error::{LogError, OpenError};
pub use frame::{Frame, LogOffset};

const MANIFEST_FILE: &str = "journal.manifest";
const SESSION_LOCK_FILE: &str = "session.lock";
const EPOCH_MASK: u32 = 0x3FFF_FFFF;

// ---------------------------------------------------------------------------
// Internal types
// ---------------------------------------------------------------------------

struct SessionResources {
    tx: std::sync::mpsc::SyncSender<CleanRequest>,
    ready: Arc<AtomicBool>,
    session_lock: FileLock,
}

struct Slot {
    _segment: Segment,
    data: *mut u8,
}

// SAFETY: a `Slot` is a mmap'd segment handle plus a cached data pointer into
// that mapping. The mapping lives in shared memory, not thread-local state.
// Concurrent access is governed by the frame-level atomics.
unsafe impl Send for Slot {}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Builder for configuring and opening a [`SegmentedLog`].
///
/// Obtained via [`Conductor::session()`]. The conductor tracks session
/// ownership and provides the background cleanup thread.
pub struct SegmentedLogBuilder<'a> {
    conductor: &'a mut Conductor,
    segment_size: usize,
    session_id: Option<u32>,
    name: Option<String>,
    pretouch: bool,
    huge_pages: bool,
}

impl<'a> SegmentedLogBuilder<'a> {
    pub(crate) fn new(conductor: &'a mut Conductor) -> Self {
        Self {
            conductor,
            segment_size: 4 * 1024 * 1024,
            session_id: None,
            name: None,
            pretouch: false,
            huge_pages: false,
        }
    }

    pub fn segment_size(mut self, size: usize) -> Self {
        self.segment_size = size;
        self
    }

    pub fn session_id(mut self, id: u32) -> Self {
        self.session_id = Some(id);
        self
    }

    /// Optional display name for the session (max 64 bytes, truncated).
    pub fn name(mut self, name: &str) -> Self {
        self.name = Some(name.to_owned());
        self
    }

    /// Fault all pages into memory on creation (MAP_POPULATE).
    pub fn pretouch(mut self, enable: bool) -> Self {
        self.pretouch = enable;
        self
    }

    pub fn huge_pages(mut self, enable: bool) -> Self {
        self.huge_pages = enable;
        self
    }

    /// Open or recover a session log.
    ///
    /// If the session directory contains an existing manifest, its structural
    /// config (segment size) takes precedence over the builder's settings.
    /// Use [`open_strict`](Self::open_strict) to error on mismatch instead.
    pub fn open(self) -> Result<SegmentedLog, OpenError> {
        self.open_inner(false)
    }

    /// Open or recover a session log, erroring if the manifest's structural
    /// config does not match the builder's settings.
    pub fn open_strict(self) -> Result<SegmentedLog, OpenError> {
        self.open_inner(true)
    }

    fn open_inner(self, strict: bool) -> Result<SegmentedLog, OpenError> {
        let id = match self.session_id {
            Some(id) => {
                self.conductor.register_explicit_id(id)?;
                id
            }
            None => self.conductor.next_session_id()?,
        };

        let session_dir = self.conductor.dir().join(id.to_string());
        std::fs::create_dir_all(&session_dir)?;

        let session_lock = FileLock::try_lock(session_dir.join(SESSION_LOCK_FILE))?
            .ok_or(OpenError::SessionInUse { session_id: id })?;

        let hints = self.map_hints();
        let size = align_up(self.segment_size.max(FRAME_HDR * 8));
        if size > u32::MAX as usize {
            return Err(OpenError::SegmentTooLarge { size });
        }
        let name_bytes = self.name.as_deref().unwrap_or("").as_bytes();
        let res = SessionResources {
            tx: self.conductor.sender(),
            ready: Arc::new(AtomicBool::new(true)),
            session_lock,
        };

        let mpath = manifest_path(&session_dir);
        if mpath.exists() {
            SegmentedLog::recover(&session_dir, size, hints, strict, id, res)
        } else {
            SegmentedLog::create_fresh(&session_dir, size, hints, id, name_bytes, res)
        }
    }

    fn map_hints(&self) -> MapHints {
        MapHints {
            pretouch: self.pretouch,
            huge_pages: self.huge_pages,
        }
    }
}

/// Three-segment bounded append log with background segment rotation.
///
/// Maintains three fixed mmap'd segments: one active for appends, one
/// read-only for lookups, one being cleaned by a conductor thread. When the
/// active segment fills, roles rotate: old readable becomes conductor input,
/// active becomes readable, clean standby becomes active. The hot-path append
/// never blocks on cleaning; the conductor must finish before the *next*
/// rotation (size segments with enough headroom for the expected message rate).
///
/// # Directory layout
///
/// Each session lives in its own subdirectory under the conductor's root:
///
/// ```text
/// {conductor_dir}/{session_id}/
///   session.lock      <- OFD-locked while open
///   journal.manifest  <- structural config + epoch + session metadata
///   seg0.dat          <- rotation slot 0
///   seg1.dat          <- rotation slot 1
///   seg2.dat          <- rotation slot 2
/// ```
///
/// # Global offset addressing
///
/// Sequential reads use a monotonically increasing `u64` position that spans
/// all segments. The physical slot is derived via modular arithmetic:
///
/// ```text
/// segment_number = pos / segment_size
/// local_offset   = pos % segment_size
/// slot_index     = segment_number % 3
/// ```
///
/// This works because the init order (`current=0, prev=2, standby=1`) is
/// chosen so that the rotation cycle (`current->prev, standby->current,
/// old_prev->standby`) visits slots in order 0 -> 1 -> 2 -> 0 -> ...:
///
/// ```text
/// epoch 0: current=0  prev=2  standby=1
/// epoch 1: current=1  prev=0  standby=2
/// epoch 2: current=2  prev=1  standby=0
/// epoch 3: current=0  prev=2  standby=1   (cycle repeats)
/// ```
///
/// At any point, only the current (`epoch`) and previous (`epoch - 1`)
/// segments are readable. Older segments have been handed to the conductor
/// for cleaning.
///
/// # Durability
///
/// Epoch advances are written to the mmap'd manifest but not fsynced.
/// After a crash, the on-disk epoch may lag by one rotation, causing
/// recovery to discard the most recent segment's data. This matches
/// the Aeron journal model: replay from the last durable point.
pub struct SegmentedLog {
    slots: [Slot; 3],
    manifest: Manifest,
    tx: std::sync::mpsc::SyncSender<CleanRequest>,
    ready: Arc<AtomicBool>,
    _session_lock: FileLock,
    segment_size: usize,
    session_id: u32,
    current: usize,
    prev: usize,
    standby: usize,
    cursor: usize,
    epoch: u64,
    slot_gen: [u32; 3],
}

impl SegmentedLog {
    pub fn segment_size(&self) -> usize {
        self.segment_size
    }

    pub fn session_id(&self) -> u32 {
        self.session_id
    }

    pub fn session_name(&self) -> &str {
        let bytes = self.manifest.name();
        std::str::from_utf8(bytes).unwrap_or("")
    }

    /// Append `payload` to the active segment.
    ///
    /// The session ID is set by the conductor at open time and written into
    /// every frame header automatically.
    ///
    /// Returns a [`LogOffset`] valid for reads until the slot is rotated out
    /// (two rotations after this write).
    ///
    /// # Panics
    ///
    /// Panics if the conductor cleanup thread has exited (indicates a bug).
    pub fn append(&mut self, payload: &[u8]) -> Result<LogOffset, LogError> {
        let body = payload.len();
        let foot = footprint(body);
        if foot > self.segment_size {
            return Err(LogError::RecordTooLarge {
                max: self.segment_size.saturating_sub(FRAME_HDR),
            });
        }
        if self.cursor + foot > self.segment_size {
            self.rotate()?;
        }
        let off = self.cursor;
        let data = self.slots[self.current].data;
        // SAFETY: `off + foot <= self.segment_size` (checked above or after rotate).
        // `data` points into a live mmap'd segment that is at least `segment_size`
        // bytes. Frame header fields are at 4-byte-aligned offsets within the
        // segment. The sentinel store at `data.add(next)` is bounds-checked before
        // it is written.
        // Write order matters for lock-free correctness:
        //   1. Copy payload bytes
        //   2. Write session_id
        //   3. Zero the next frame's commit_len (sentinel for readers/recovery)
        //   4. Release-store this frame's commit_len (publishes the frame)
        // A reader loading commit_len with Acquire sees either 0 (not yet
        // committed) or the final value — never a partial payload.
        unsafe {
            let ptr = data.add(off);
            std::ptr::copy_nonoverlapping(payload.as_ptr(), ptr.add(FRAME_HDR), body);
            *session_id_ptr(ptr) = self.session_id;
            let next = off + foot;
            if next + FRAME_HDR <= self.segment_size {
                (*commit_len_ptr(data.add(next))).store(0, Ordering::Relaxed);
            }
            // commit_len encodes body length as `len + 1` so that zero
            // means "uncommitted". This allows zero-length payloads (stored
            // as 1) while reserving 0 as the sentinel for readers/recovery.
            (*commit_len_ptr(ptr)).store((body as u32).wrapping_add(1), Ordering::Release);
        }
        self.cursor += foot;
        Ok(LogOffset::new(
            self.current as u8,
            off,
            self.slot_gen[self.current],
        ))
    }

    /// Return the frame stored at `offset`, or `None` if the slot has been
    /// rotated out and is no longer readable.
    pub fn read(&self, offset: LogOffset) -> Option<Frame<'_>> {
        let slot = offset.slot();
        if slot != self.current && slot != self.prev {
            return None;
        }
        if offset.epoch() != self.slot_gen[slot] {
            return None;
        }
        let off = offset.local_off();
        let data = self.slots[slot].data;
        // SAFETY: `slot` is either `current` or `prev`, both of which hold live
        // mmap'd segments. `off` is a value previously returned by `append()` for
        // this slot, so `off < segment_size`. The bounds check on `off + FRAME_HDR
        // + body` prevents reading past the end of the segment.
        unsafe {
            let ptr = data.add(off);
            let stored = (*commit_len_ptr(ptr)).load(Ordering::Acquire);
            if stored == 0 {
                return None;
            }
            let body = (stored - 1) as usize;
            if off + FRAME_HDR + body > self.segment_size {
                return None;
            }
            Some(Frame::new(
                std::slice::from_raw_parts(ptr.add(FRAME_HDR), body),
                offset.global_offset(self.segment_size),
                *session_id_ptr(ptr),
            ))
        }
    }

    /// Monotonically increasing global offset at the current write position.
    pub fn write_pos(&self) -> u64 {
        self.epoch * self.segment_size as u64 + self.cursor as u64
    }

    /// Global offset at the start of the oldest readable segment.
    pub fn read_start(&self) -> u64 {
        if self.epoch == 0 {
            0
        } else {
            (self.epoch - 1) * self.segment_size as u64
        }
    }

    /// Read the next committed frame at `pos`, advancing past it.
    ///
    /// Returns `None` when caught up to the writer or when `pos` references
    /// an evicted segment. The slot is determined by `pos / segment_size % 3`;
    /// the init order guarantees this maps directly to the physical slot index.
    ///
    /// `pos` must be frame-aligned (a multiple of 8). Values obtained from
    /// [`read_start`] and advanced by this method satisfy this invariant.
    pub fn read_next(&self, pos: &mut u64) -> Option<Frame<'_>> {
        debug_assert!(
            (*pos).is_multiple_of(ALIGN as u64),
            "pos must be frame-aligned (got {pos})",
            pos = *pos,
        );
        let seg_size = self.segment_size as u64;
        let seg = *pos / seg_size;
        let local = (*pos % seg_size) as usize;
        let epoch = self.epoch;

        if seg > epoch || (epoch > 0 && seg + 1 < epoch) {
            return None;
        }

        let slot = (seg % 3) as usize;

        if local + FRAME_HDR > self.segment_size {
            if seg < epoch {
                *pos = (seg + 1) * seg_size;
                return self.read_next(pos);
            }
            return None;
        }

        let data = self.slots[slot].data;
        // SAFETY: `slot` is `seg % 3` where `seg` is either `epoch` (current) or
        // `epoch - 1` (prev), both live mmap'd segments. `local` is bounded by
        // `segment_size` via the modulo. The `local + FRAME_HDR` check above ensures
        // we don't read past the segment for the header. The `local + FRAME_HDR + body`
        // check below prevents reading past the segment for the payload.
        unsafe {
            let ptr = data.add(local);
            let stored = (*commit_len_ptr(ptr)).load(Ordering::Acquire);
            if stored == 0 {
                if seg < epoch {
                    *pos = (seg + 1) * seg_size;
                    return self.read_next(pos);
                }
                return None;
            }
            let body = (stored - 1) as usize;
            if local + FRAME_HDR + body > self.segment_size {
                return None;
            }
            let frame_offset = *pos;
            *pos += footprint(body) as u64;
            Some(Frame::new(
                std::slice::from_raw_parts(ptr.add(FRAME_HDR), body),
                frame_offset,
                *session_id_ptr(ptr),
            ))
        }
    }

    // -- private --

    fn create_fresh(
        dir: &Path,
        size: usize,
        hints: MapHints,
        session_id: u32,
        name: &[u8],
        res: SessionResources,
    ) -> Result<Self, OpenError> {
        let manifest = Manifest::create(&manifest_path(dir), size as u64, session_id, name)?;

        let mk = |i: u8| -> Result<Slot, OpenError> {
            let total = Segment::total_size(size)?;
            let mf = file_create(&seg_path(dir, i), total, hints)?;
            let seg = Segment::create(mf, size, hints)?;
            let data = seg.data();
            Ok(Slot {
                _segment: seg,
                data,
            })
        };

        let s0 = mk(0)?;
        let s1 = mk(1)?;
        let s2 = mk(2)?;

        // SAFETY: each slot data pointer is the start of a freshly mapped segment
        // with at least FRAME_HDR bytes and 4-byte alignment from mmap.
        unsafe {
            (*commit_len_ptr(s0.data)).store(0, Ordering::Relaxed);
            (*commit_len_ptr(s1.data)).store(0, Ordering::Relaxed);
            (*commit_len_ptr(s2.data)).store(0, Ordering::Relaxed);
        }

        Ok(Self {
            slots: [s0, s1, s2],
            manifest,
            tx: res.tx,
            ready: res.ready,
            _session_lock: res.session_lock,
            segment_size: size,
            session_id,
            current: 0,
            prev: 2,
            standby: 1,
            cursor: 0,
            epoch: 0,
            // u32::MAX marks inactive slots — no real epoch will match,
            // so reads against prev/standby correctly return None.
            slot_gen: [0, u32::MAX, u32::MAX],
        })
    }

    fn recover(
        dir: &Path,
        requested_size: usize,
        hints: MapHints,
        strict: bool,
        expected_session_id: u32,
        res: SessionResources,
    ) -> Result<Self, OpenError> {
        let manifest = Manifest::open(&manifest_path(dir))?;
        let manifest_size = manifest.segment_size() as usize;
        let session_id = manifest.session_id();

        if session_id != expected_session_id {
            return Err(OpenError::ConfigMismatch {
                field: "session_id",
                expected: expected_session_id as u64,
                found: session_id as u64,
            });
        }

        if strict && manifest_size != requested_size {
            return Err(OpenError::ConfigMismatch {
                field: "segment_size",
                expected: requested_size as u64,
                found: manifest_size as u64,
            });
        }

        let size = manifest_size;
        let epoch = manifest.epoch();

        let (current, prev, standby) = match epoch {
            0 => (0, 2, 1),
            1 => (1, 0, 2),
            _ => {
                let c = (epoch % 3) as usize;
                let p = ((epoch - 1) % 3) as usize;
                // {c, p, s} is always a permutation of {0, 1, 2}
                let s = 3 - c - p;
                (c, p, s)
            }
        };

        let mk = |i: u8| -> Result<Slot, OpenError> {
            let path = seg_path(dir, i);
            let seg = if path.exists() {
                Segment::attach(file_open(&path, hints)?)?
            } else {
                let total = Segment::total_size(size)?;
                Segment::create(file_create(&path, total, hints)?, size, hints)?
            };
            let data = seg.data();
            Ok(Slot {
                _segment: seg,
                data,
            })
        };

        let s0 = mk(0)?;
        let s1 = mk(1)?;
        let s2 = mk(2)?;
        let slots = [s0, s1, s2];

        let cursor = recover_tail(slots[current].data, size);

        // The standby segment may contain stale committed frames from a
        // previous epoch. Zero its commit_len so those frames are not
        // mistaken for valid data when this slot becomes active.
        // SAFETY: standby is a valid slot index into a live mmap'd segment.
        unsafe {
            (*commit_len_ptr(slots[standby].data)).store(0, Ordering::Relaxed);
        }

        let mut slot_gen = [u32::MAX; 3];
        slot_gen[current] = (epoch as u32) & EPOCH_MASK;
        if epoch > 0 {
            slot_gen[prev] = ((epoch - 1) as u32) & EPOCH_MASK;
        }

        Ok(Self {
            slots,
            manifest,
            tx: res.tx,
            ready: res.ready,
            _session_lock: res.session_lock,
            segment_size: size,
            session_id,
            current,
            prev,
            standby,
            cursor,
            epoch,
            slot_gen,
        })
    }

    fn rotate(&mut self) -> Result<(), LogError> {
        if !self.ready.load(Ordering::Acquire) {
            return Err(LogError::StandbyNotReady);
        }

        let old_prev = self.prev;
        let request = CleanRequest {
            data: self.slots[old_prev].data,
            segment_size: self.segment_size,
            ready: Arc::clone(&self.ready),
        };

        self.ready.store(false, Ordering::Release);
        match self.tx.try_send(request) {
            Ok(()) => {}
            Err(std::sync::mpsc::TrySendError::Full(_)) => {
                self.ready.store(true, Ordering::Release);
                return Err(LogError::StandbyNotReady);
            }
            Err(std::sync::mpsc::TrySendError::Disconnected(_)) => {
                panic!("conductor cleanup thread has exited unexpectedly");
            }
        }

        self.prev = self.current;
        self.current = self.standby;
        self.standby = old_prev;
        self.cursor = 0;
        self.epoch += 1;
        self.slot_gen[self.current] = (self.epoch as u32) & EPOCH_MASK;
        self.manifest.set_epoch(self.epoch);

        Ok(())
    }
}

impl Drop for SegmentedLog {
    fn drop(&mut self) {
        // Wait for any in-flight clean request to finish before unmapping
        // segments. The conductor thread holds a raw pointer into our mmap'd
        // data — if we unmap first, it would touch freed memory.
        //
        // yield_now() is appropriate here because the conductor's work is a
        // single atomic store — this spin completes in nanoseconds. A sleep
        // would add milliseconds of unnecessary latency to drop.
        while !self.ready.load(Ordering::Acquire) {
            std::thread::yield_now();
        }
        // _session_lock is dropped here, releasing the OFD lock.
    }
}

// ---------------------------------------------------------------------------
// Free functions
// ---------------------------------------------------------------------------

fn seg_path(dir: &Path, i: u8) -> PathBuf {
    dir.join(format!("seg{i}.dat"))
}

fn manifest_path(dir: &Path) -> PathBuf {
    dir.join(MANIFEST_FILE)
}

fn file_create(
    path: &Path,
    len: std::num::NonZeroUsize,
    hints: MapHints,
) -> Result<MappedFile, nexus_platform::MapError> {
    let mut opts = MappedFile::options();
    opts.pretouch(hints.pretouch).huge_pages(hints.huge_pages);
    opts.create(path, len)
}

fn file_open(path: &Path, hints: MapHints) -> Result<MappedFile, nexus_platform::MapError> {
    let mut opts = MappedFile::options();
    opts.pretouch(hints.pretouch).huge_pages(hints.huge_pages);
    opts.open(path)
}

/// Scan from the start of a segment to find the write tail.
///
/// Walks committed frames (non-zero `commit_len`) and stops at the first
/// uncommitted slot. Returns the byte offset of the tail.
fn recover_tail(data: *mut u8, segment_size: usize) -> usize {
    let mut cur = 0;
    while cur + FRAME_HDR <= segment_size {
        // SAFETY: `cur` is an 8-aligned offset within the mapped data region.
        let stored = unsafe { (*commit_len_ptr(data.add(cur))).load(Ordering::Acquire) };
        if stored == 0 {
            break;
        }
        let body = (stored - 1) as usize;
        if body > segment_size {
            break;
        }
        let foot = footprint(body);
        if cur + foot > segment_size {
            break;
        }
        cur += foot;
    }
    cur
}
