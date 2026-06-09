use std::cell::UnsafeCell;
use std::io::{Read as _, Seek, SeekFrom, Write as _};
use std::mem::MaybeUninit;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicU8, Ordering};
use std::thread::JoinHandle;
use std::time::Duration;

use nexus_platform::{FileLock, MapOptions};

use crate::segment::Segment;

use super::frame::commit_len_ptr;

const LOCK_FILE: &str = "conductor.lock";
const DEFAULT_CLEAN_QUEUE_DEPTH: usize = 4;

// ---------------------------------------------------------------------------
// SegmentSwap — three-state handoff between SegmentedLog and conductor
// ---------------------------------------------------------------------------

pub(crate) const SWAP_CLEAN: u8 = 0; // conductor wrote a fresh segment; SegmentedLog can rotate
pub(crate) const SWAP_DIRTY: u8 = 1; // SegmentedLog wrote an evicted segment; conductor must process
pub(crate) const SWAP_PENDING: u8 = 2; // sent to conductor channel; inner is uninit

/// Lock-free three-state handoff cell.
///
/// State machine:
/// ```text
/// Clean  ──(rotate takes)──▶ [inner uninit] ──(store_dirty)──▶ Dirty
/// Dirty  ──(try_flush sends)──▶ Pending
/// Pending ──(conductor publishes)──▶ Clean
/// ```
///
/// The `state` atomic provides the Acquire/Release barriers:
/// - `Clean` Acquire: safe to read `inner` (conductor wrote it)
/// - `Dirty` Acquire: safe to read `inner` (SegmentedLog wrote it)
/// - `Pending`: `inner` is uninit — nobody touches it
pub(crate) struct SegmentSwap {
    state: AtomicU8,
    inner: UnsafeCell<MaybeUninit<Segment>>,
}

// SAFETY: access is serialized by `state` — at most one side holds the payload
// at any point, enforced by the state machine above.
unsafe impl Sync for SegmentSwap {}

impl SegmentSwap {
    pub(crate) fn new_clean(segment: Segment) -> Self {
        Self {
            state: AtomicU8::new(SWAP_CLEAN),
            inner: UnsafeCell::new(MaybeUninit::new(segment)),
        }
    }

    pub(crate) fn state(&self) -> u8 {
        self.state.load(Ordering::Acquire)
    }

    /// Take the segment out, leaving `inner` uninit.
    ///
    /// # Safety
    /// `state` must be `SWAP_CLEAN` or `SWAP_DIRTY` (payload initialized).
    pub(crate) unsafe fn take(&self) -> Segment {
        unsafe { (*self.inner.get()).assume_init_read() }
    }

    /// Write the evicted segment into `inner` and transition to `Dirty`.
    ///
    /// # Safety
    /// `inner` must be uninit (caller just called `take()`).
    pub(crate) unsafe fn store_dirty(&self, segment: Segment) {
        unsafe { (*self.inner.get()).write(segment) };
        self.state.store(SWAP_DIRTY, Ordering::Release);
    }

    pub(crate) fn set_state(&self, s: u8) {
        self.state.store(s, Ordering::Release);
    }

    /// Write a fresh replacement segment and transition to `Clean`.
    ///
    /// # Safety
    /// Called only from the conductor thread after `inner` was uninit.
    pub(crate) unsafe fn publish_clean(&self, segment: Segment) {
        unsafe { (*self.inner.get()).write(segment) };
        self.state.store(SWAP_CLEAN, Ordering::Release);
    }
}

impl Drop for SegmentSwap {
    fn drop(&mut self) {
        let s = *self.state.get_mut();
        if s == SWAP_CLEAN || s == SWAP_DIRTY {
            // SAFETY: state guarantees payload is initialized.
            unsafe { self.inner.get_mut().assume_init_drop() };
        }
    }
}

// ---------------------------------------------------------------------------
// CleanRequest
// ---------------------------------------------------------------------------

pub(crate) struct CleanRequest {
    /// The evicted segment to archive (rename) then drop. `None` for
    /// retry-only requests where the segment was already dropped.
    pub(crate) segment: Option<Segment>,
    pub(crate) segment_size: usize,
    pub(crate) epoch: u64,
    pub(crate) swap: Arc<SegmentSwap>,
    /// Path of the slot file to create fresh for the replacement segment.
    pub(crate) seg_path: PathBuf,
    pub(crate) map: MapOptions,
    pub(crate) archive_dir: Option<PathBuf>,
}

// SAFETY: `CleanRequest` carries `Segment` ownership across the channel.
// `Segment` itself wraps a `MappedFile` (mmap handle) which is not `Send`
// by default only because raw pointers aren't, but the mapping is stable
// in memory. The conductor thread is the sole owner once the request is sent.
unsafe impl Send for CleanRequest {}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Builder for configuring a [`Conductor`].
pub struct ConductorBuilder {
    dir: PathBuf,
    clean_queue_depth: usize,
    archive: bool,
}

impl ConductorBuilder {
    pub fn new(dir: impl AsRef<Path>) -> Self {
        Self {
            dir: dir.as_ref().to_path_buf(),
            clean_queue_depth: DEFAULT_CLEAN_QUEUE_DEPTH,
            archive: false,
        }
    }

    pub fn clean_queue_depth(mut self, depth: usize) -> Self {
        self.clean_queue_depth = depth;
        self
    }

    /// Archive evicted segments to `{session_dir}/archive/seg_{epoch}.dat`
    /// before dropping them (default: off).
    ///
    /// When enabled, the segment file is fsynced then renamed (atomic on the
    /// same filesystem) rather than zeroed. The rename preserves the exact
    /// on-disk frame format — no copy step, no partial-write risk.
    pub fn archive(mut self, enable: bool) -> Self {
        self.archive = enable;
        self
    }

    pub fn open(self) -> Result<Conductor, super::OpenError> {
        std::fs::create_dir_all(&self.dir)?;

        let (tx, rx) = std::sync::mpsc::sync_channel(self.clean_queue_depth);
        let thread = std::thread::spawn(move || conductor_main(&rx));

        Ok(Conductor {
            dir: self.dir,
            tx: Some(tx),
            thread: Some(thread),
            archive: self.archive,
        })
    }
}

/// Top-level journal manager.
pub struct Conductor {
    dir: PathBuf,
    tx: Option<std::sync::mpsc::SyncSender<CleanRequest>>,
    thread: Option<JoinHandle<()>>,
    archive: bool,
}

impl Conductor {
    pub fn open(dir: impl AsRef<Path>) -> Result<Self, super::OpenError> {
        ConductorBuilder::new(dir).open()
    }

    pub fn session(&mut self) -> super::SegmentedLogBuilder<'_> {
        super::SegmentedLogBuilder::new(self)
    }

    pub fn sessions_on_disk(&self) -> Result<Vec<u32>, super::OpenError> {
        let mut ids = Vec::new();
        for entry in std::fs::read_dir(&self.dir)? {
            let entry = entry?;
            if !entry.file_type()?.is_dir() {
                continue;
            }
            if entry.path().join(super::MANIFEST_FILE).exists()
                && let Some(name) = entry.file_name().to_str()
                && let Ok(id) = name.parse::<u32>()
            {
                ids.push(id);
            }
        }
        ids.sort_unstable();
        Ok(ids)
    }

    pub(crate) fn next_session_id(&self) -> Result<u32, super::OpenError> {
        claim_next_session_id(&self.dir)
    }

    pub(crate) fn register_explicit_id(&self, id: u32) -> Result<(), super::OpenError> {
        ensure_counter_at_least(&self.dir, id)
    }

    pub(crate) fn dir(&self) -> &Path {
        &self.dir
    }

    pub(crate) fn sender(&self) -> std::sync::mpsc::SyncSender<CleanRequest> {
        self.tx.as_ref().expect("conductor shut down").clone()
    }

    pub(crate) fn archive(&self) -> bool {
        self.archive
    }
}

impl Drop for Conductor {
    fn drop(&mut self) {
        drop(self.tx.take());
        if let Some(t) = self.thread.take() {
            let _ = t.join();
        }
    }
}

// ---------------------------------------------------------------------------
// Conductor work loop
// ---------------------------------------------------------------------------

struct PendingCreate {
    swap: Arc<SegmentSwap>,
    seg_path: PathBuf,
    segment_size: usize,
    map: MapOptions,
}

fn conductor_main(rx: &std::sync::mpsc::Receiver<CleanRequest>) {
    let mut pending: Vec<PendingCreate> = Vec::new();

    loop {
        // Retry any previously failed segment creates (e.g. ENOSPC).
        pending.retain(|p| {
            Segment::create(&p.seg_path, p.segment_size, p.map).map_or(true, |seg| {
                // SAFETY: conductor is sole owner; state is Pending (inner uninit).
                unsafe { p.swap.publish_clean(seg) };
                false
            })
        });

        // Non-blocking drain of new requests.
        let mut drained = false;
        while let Ok(req) = rx.try_recv() {
            drained = true;
            process_request(req, &mut pending);
        }

        // Block only when idle; sleep briefly if still retrying.
        if pending.is_empty() {
            match rx.recv() {
                Ok(req) => process_request(req, &mut pending),
                Err(_) => break,
            }
        } else if !drained {
            std::thread::sleep(Duration::from_millis(250));
        }
    }
}

fn process_request(req: CleanRequest, pending: &mut Vec<PendingCreate>) {
    if let Some(segment) = req.segment {
        // fsync before rename so the archive file is durable.
        let _ = segment.sync();

        if let Some(ref archive_dir) = req.archive_dir
            && std::fs::create_dir_all(archive_dir).is_ok()
        {
            let dst = archive_dir.join(format!("seg_{}.dat", req.epoch));
            // Rename is atomic on the same filesystem; the mmap follows
            // the inode so existing readers are unaffected.
            let _ = std::fs::rename(segment.path(), dst);
        }

        // Drop the Segment (munmap). The file is either renamed or still at
        // its original path — either way we're done with the mapping.
        drop(segment);
    }

    match Segment::create(&req.seg_path, req.segment_size, req.map) {
        Ok(seg) => {
            // Zero the first commit_len so the fresh segment reads as empty.
            // SAFETY: fresh segment, conductor is sole owner.
            unsafe {
                (*commit_len_ptr(seg.data())).store(0, std::sync::atomic::Ordering::Relaxed);
            }
            // SAFETY: state is Pending (inner uninit after SegmentedLog took it).
            unsafe { req.swap.publish_clean(seg) };
        }
        Err(_) => {
            pending.push(PendingCreate {
                swap: req.swap,
                seg_path: req.seg_path,
                segment_size: req.segment_size,
                map: req.map,
            });
        }
    }
}

// ---------------------------------------------------------------------------
// Session ID management
// ---------------------------------------------------------------------------

fn claim_next_session_id(dir: &Path) -> Result<u32, super::OpenError> {
    let mut lock = FileLock::lock(dir.join(LOCK_FILE))?;
    let current = read_counter(lock.file())?;
    let next = current + 1;
    write_counter(lock.file(), next)?;
    Ok(next)
}

fn ensure_counter_at_least(dir: &Path, id: u32) -> Result<(), super::OpenError> {
    let mut lock = FileLock::lock(dir.join(LOCK_FILE))?;
    let current = read_counter(lock.file())?;
    if id > current {
        write_counter(lock.file(), id)?;
    }
    Ok(())
}

fn read_counter(file: &mut std::fs::File) -> Result<u32, std::io::Error> {
    file.seek(SeekFrom::Start(0))?;
    let mut buf = String::new();
    file.read_to_string(&mut buf)?;
    Ok(buf.trim().parse().unwrap_or(0))
}

fn write_counter(file: &mut std::fs::File, val: u32) -> Result<(), std::io::Error> {
    file.seek(SeekFrom::Start(0))?;
    file.set_len(0)?;
    write!(file, "{val}")?;
    Ok(())
}
