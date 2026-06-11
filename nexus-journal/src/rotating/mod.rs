mod conductor;
mod error;
mod frame;
mod manifest;
#[cfg(test)]
mod tests;

use std::num::NonZeroUsize;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

use nexus_platform::MapHints;
use nexus_platform::{FileLock, MappedFile, Mapping};
use nexus_queue::mpsc;

use conductor::{CleanRequest, SWAP_CLEAN, SWAP_DIRTY, SegmentSwap};
use frame::{
    ALIGN, FRAME_HDR, align_up, footprint, read_commit_len, session_id_ptr, write_commit_len,
};
use manifest::Manifest;

pub use conductor::{Conductor, ConductorBuilder};
pub use error::{OpenError, WriteError};
pub use frame::{Frame, LogOffset};

pub(crate) const MANIFEST_FILE: &str = "journal.manifest";
const SESSION_LOCK_FILE: &str = "session.lock";
const EPOCH_MASK: u32 = 0x3FFF_FFFF;

// ---------------------------------------------------------------------------
// Internal types
// ---------------------------------------------------------------------------

struct SessionResources {
    tx: mpsc::Producer<CleanRequest>,
    alive: Arc<AtomicBool>,
    wake_thread: std::thread::Thread,
    session_lock: FileLock,
}

struct Slot {
    mapping: Option<Mapping>,
    path: PathBuf,
    data: *mut u8,
}

// SAFETY: `Slot` owns an optional mmap'd Mapping and a `data` pointer into it
// (`null_mut()` when the standby slot's mapping lives in the swap). The mmap
// is not thread-local. Concurrent access is governed by the SegmentSwap state
// machine.
unsafe impl Send for Slot {}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Builder for configuring and opening a [`RotatingJournal`].
///
/// Obtained via [`Conductor::session()`]. The conductor tracks session
/// ownership and provides the background cleanup thread.
pub struct RotatingJournalBuilder<'a> {
    conductor: &'a mut Conductor,
    segment_size: usize,
    session_id: Option<u32>,
    name: Option<String>,
    pretouch: bool,
    huge_pages: bool,
}

impl<'a> RotatingJournalBuilder<'a> {
    pub(crate) fn new(conductor: &'a mut Conductor) -> Self {
        Self {
            conductor,
            segment_size: 4 * 1024 * 1024,
            session_id: None,
            name: None,
            pretouch: true,
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

    /// Fault all pages into memory up front (`MAP_POPULATE`). Enabled by
    /// default: the conductor maps every segment, so the page-fault cost is
    /// paid on the conductor thread, off the append hot path. Disabling it
    /// pushes those faults onto the writer — a per-page tail spike as each
    /// fresh page is first touched while filling a segment.
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
    pub fn open(self) -> Result<RotatingJournal, OpenError> {
        self.open_inner(false)
    }

    /// Open or recover a session log, erroring if the manifest's structural
    /// config does not match the builder's settings.
    pub fn open_strict(self) -> Result<RotatingJournal, OpenError> {
        self.open_inner(true)
    }

    fn open_inner(self, strict: bool) -> Result<RotatingJournal, OpenError> {
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
            alive: self.conductor.alive(),
            wake_thread: self.conductor.wake_thread(),
            session_lock,
        };

        let archive_dir = self
            .conductor
            .archive()
            .then(|| session_dir.join("archive"));

        let mpath = manifest_path(&session_dir);
        if mpath.exists() {
            RotatingJournal::recover(&session_dir, size, hints, strict, id, res, archive_dir)
        } else {
            RotatingJournal::create_fresh(
                &session_dir,
                size,
                hints,
                id,
                name_bytes,
                res,
                archive_dir,
            )
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
pub struct RotatingJournal {
    slots: [Slot; 3],
    manifest: Manifest,
    tx: mpsc::Producer<CleanRequest>,
    alive: Arc<AtomicBool>,
    wake_thread: std::thread::Thread,
    swap: Arc<SegmentSwap>,
    _session_lock: FileLock,
    segment_size: usize,
    session_id: u32,
    current: usize,
    prev: usize,
    standby: usize,
    cursor: usize,
    epoch: u64,
    slot_gen: [u32; 3],
    hints: MapHints,
    archive_dir: Option<PathBuf>,
}

impl RotatingJournal {
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
    pub fn append(&mut self, payload: &[u8]) -> Result<LogOffset, WriteError> {
        self.try_flush_dirty();
        let body = payload.len();
        let foot = footprint(body);
        if foot > self.segment_size {
            return Err(WriteError::RecordTooLarge {
                max: self.segment_size.saturating_sub(FRAME_HDR),
            });
        }
        if self.cursor + foot > self.segment_size {
            self.rotate()?;
        }
        let off = self.cursor;
        let data = self.slots[self.current].data;
        // SAFETY: `off + foot <= self.segment_size` (checked above or after rotate).
        // `data` points into a live mmap'd mapping that is at least `segment_size`
        // bytes. Frame header fields are at 4-byte-aligned offsets.
        // Write order: payload, session_id, next sentinel, then commit_len.
        // commit_len encodes body length as `len + 1` so that zero means
        // "uncommitted", allowing zero-length payloads.
        unsafe {
            let ptr = data.add(off);
            std::ptr::copy_nonoverlapping(payload.as_ptr(), ptr.add(FRAME_HDR), body);
            *session_id_ptr(ptr) = self.session_id;
            let next = off + foot;
            if next + FRAME_HDR <= self.segment_size {
                write_commit_len(data.add(next), 0);
            }
            write_commit_len(ptr, (body as u32).wrapping_add(1));
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
        // SAFETY: `slot` is either `current` or `prev`, both holding live
        // mmap'd mappings. `off` was returned by `append()` for this slot.
        unsafe {
            let ptr = data.add(off);
            let stored = read_commit_len(ptr);
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
    /// [`read_start`](Self::read_start) and advanced by this method satisfy this invariant.
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
        // `epoch - 1` (prev), both live mmap'd mappings. `local` is bounded by
        // `segment_size` via the modulo.
        unsafe {
            let ptr = data.add(local);
            let stored = read_commit_len(ptr);
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
        archive_dir: Option<PathBuf>,
    ) -> Result<Self, OpenError> {
        let manifest = Manifest::create(&manifest_path(dir), size as u64, session_id, name)?;
        let total = NonZeroUsize::new(size).expect("segment size is non-zero");

        let mk = |i: u8| -> Result<Slot, OpenError> {
            let path = seg_path(dir, i);
            let mf = file_create(&path, total, hints)?;
            let mapping: Mapping = mf.into();
            let data = mapping.as_ptr();
            // SAFETY: freshly mapped, sole owner.
            unsafe { write_commit_len(data, 0) };
            Ok(Slot {
                mapping: Some(mapping),
                path,
                data,
            })
        };

        let s0 = mk(0)?;
        // Standby mapping lives exclusively in the swap; slots[1] starts empty.
        let standby_path = seg_path(dir, 1);
        let standby_mf = file_create(&standby_path, total, hints)?;
        let standby_mapping: Mapping = standby_mf.into();
        // SAFETY: freshly mapped, sole owner.
        unsafe { write_commit_len(standby_mapping.as_ptr(), 0) };
        let swap = Arc::new(SegmentSwap::new_clean(standby_mapping));
        let s1 = Slot {
            mapping: None,
            path: standby_path,
            data: std::ptr::null_mut(),
        };
        let s2 = mk(2)?;

        Ok(Self {
            slots: [s0, s1, s2],
            manifest,
            tx: res.tx,
            alive: res.alive,
            wake_thread: res.wake_thread,
            swap,
            _session_lock: res.session_lock,
            segment_size: size,
            session_id,
            current: 0,
            prev: 2,
            standby: 1,
            cursor: 0,
            epoch: 0,
            slot_gen: [0, u32::MAX, u32::MAX],
            hints,
            archive_dir,
        })
    }

    fn recover(
        dir: &Path,
        requested_size: usize,
        hints: MapHints,
        strict: bool,
        expected_session_id: u32,
        res: SessionResources,
        archive_dir: Option<PathBuf>,
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
                let s = 3 - c - p;
                (c, p, s)
            }
        };

        let total = NonZeroUsize::new(size).expect("segment size is non-zero");

        let mk = |i: u8| -> Result<Slot, OpenError> {
            let path = seg_path(dir, i);
            let mapping: Mapping = if path.exists() {
                file_open(&path, hints)?.into()
            } else {
                file_create(&path, total, hints)?.into()
            };
            let data = mapping.as_ptr();
            Ok(Slot {
                mapping: Some(mapping),
                path,
                data,
            })
        };

        let mut slots = [mk(0)?, mk(1)?, mk(2)?];

        let cursor = recover_tail(slots[current].data, size);

        // Move the standby mapping into the swap; its slot becomes empty.
        let standby_mapping = slots[standby].mapping.take().expect("just created");
        // SAFETY: sole owner; zeroing commit_len hides stale frames from previous session.
        unsafe { write_commit_len(standby_mapping.as_ptr(), 0) };
        slots[standby].data = std::ptr::null_mut();
        let swap = Arc::new(SegmentSwap::new_clean(standby_mapping));

        let mut slot_gen = [u32::MAX; 3];
        slot_gen[current] = (epoch as u32) & EPOCH_MASK;
        if epoch > 0 {
            slot_gen[prev] = ((epoch - 1) as u32) & EPOCH_MASK;
        }

        Ok(Self {
            slots,
            manifest,
            tx: res.tx,
            alive: res.alive,
            wake_thread: res.wake_thread,
            swap,
            _session_lock: res.session_lock,
            segment_size: size,
            session_id,
            current,
            prev,
            standby,
            cursor,
            epoch,
            slot_gen,
            hints,
            archive_dir,
        })
    }

    fn rotate(&mut self) -> Result<(), WriteError> {
        if self.swap.state() != SWAP_CLEAN {
            return Err(WriteError::StandbyNotReady);
        }

        // Take the replacement mapping the conductor prepared.
        // SAFETY: state == Clean guarantees payload is initialized.
        let new_mapping = unsafe { self.swap.take() };
        let new_data = new_mapping.as_ptr();

        // Install replacement in standby slot (becomes new current).
        self.slots[self.standby].mapping = Some(new_mapping);
        self.slots[self.standby].data = new_data;

        // Evict the prev slot (becomes new standby — empty until conductor replaces it).
        let old_prev = self.prev;
        let evicted = self.slots[old_prev]
            .mapping
            .take()
            .expect("prev must have mapping");
        self.slots[old_prev].data = std::ptr::null_mut();

        // Park the evicted mapping in the swap so try_flush_dirty can send it.
        // SAFETY: we just took from swap (inner is uninit).
        unsafe { self.swap.store_dirty(evicted) };

        self.prev = self.current;
        self.current = self.standby;
        self.standby = old_prev;
        self.cursor = 0;
        self.epoch += 1;
        self.slot_gen[self.current] = (self.epoch as u32) & EPOCH_MASK;
        self.manifest.set_epoch(self.epoch);

        self.try_flush_dirty();
        Ok(())
    }

    fn try_flush_dirty(&mut self) {
        if self.swap.state() != SWAP_DIRTY {
            return;
        }

        // SAFETY: state == Dirty guarantees the evicted mapping is in the
        // swap and we own it.
        let evicted = unsafe { self.swap.take() };

        let request = CleanRequest {
            mapping: Some(evicted),
            segment_size: self.segment_size,
            epoch: self.epoch.saturating_sub(2),
            swap: Arc::clone(&self.swap),
            seg_path: self.slots[self.standby].path.clone(),
            hints: self.hints,
            archive_dir: self.archive_dir.clone(),
        };

        // Transition Dirty → Pending before send.
        self.swap.mark_pending();

        match self.tx.push(request) {
            Ok(()) => {
                self.wake_thread.unpark();
            }
            Err(full) => {
                assert!(
                    self.alive.load(Ordering::Acquire),
                    "conductor cleanup thread has exited unexpectedly"
                );
                let mapping = full.into_inner().mapping.expect("just set it");
                // SAFETY: we set Pending above; inner is uninit; restoring Dirty.
                unsafe { self.swap.store_dirty(mapping) };
            }
        }
    }
}

impl Drop for RotatingJournal {
    fn drop(&mut self) {
        // If a request is in-flight (Pending), wait for the conductor to
        // publish a replacement (Clean). Once Clean, the conductor is done
        // with the evicted segment so it's safe to unmap everything.
        while self.swap.state() == conductor::SWAP_PENDING {
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
        let stored = unsafe { read_commit_len(data.add(cur)) };
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
