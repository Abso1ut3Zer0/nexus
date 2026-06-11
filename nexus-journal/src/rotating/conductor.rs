use std::cell::UnsafeCell;
use std::io::{Read as _, Seek, SeekFrom, Write as _};
use std::mem::MaybeUninit;
use std::num::NonZeroUsize;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicU8, Ordering};
use std::thread::JoinHandle;
use std::time::Duration;

use nexus_platform::MapHints;
use nexus_platform::{FileLock, MappedFile, Mapping};
use nexus_queue::mpsc;

const LOCK_FILE: &str = "conductor.lock";
const DEFAULT_CLEAN_QUEUE_DEPTH: usize = 4;

// ---------------------------------------------------------------------------
// SegmentSwap — three-state handoff between RotatingJournal and conductor
// ---------------------------------------------------------------------------

pub(crate) const SWAP_CLEAN: u8 = 0; // conductor wrote a fresh segment; RotatingJournal can rotate
pub(crate) const SWAP_DIRTY: u8 = 1; // RotatingJournal wrote an evicted segment; conductor must process
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
/// - `Dirty` Acquire: safe to read `inner` (RotatingJournal wrote it)
/// - `Pending`: `inner` is uninit — nobody touches it
pub(crate) struct SegmentSwap {
    state: AtomicU8,
    inner: UnsafeCell<MaybeUninit<Mapping>>,
}

// SAFETY: access is serialized by `state` — at most one side holds the payload
// at any point, enforced by the state machine above.
unsafe impl Sync for SegmentSwap {}

impl SegmentSwap {
    pub(crate) fn new_clean(mapping: Mapping) -> Self {
        Self {
            state: AtomicU8::new(SWAP_CLEAN),
            inner: UnsafeCell::new(MaybeUninit::new(mapping)),
        }
    }

    pub(crate) fn state(&self) -> u8 {
        self.state.load(Ordering::Acquire)
    }

    /// Take the mapping out, leaving `inner` uninit.
    ///
    /// # Safety
    /// `state` must be `SWAP_CLEAN` or `SWAP_DIRTY` (payload initialized).
    pub(crate) unsafe fn take(&self) -> Mapping {
        unsafe { (*self.inner.get()).assume_init_read() }
    }

    /// Write the evicted mapping into `inner` and transition to `Dirty`.
    ///
    /// # Safety
    /// `inner` must be uninit (caller just called `take()`).
    pub(crate) unsafe fn store_dirty(&self, mapping: Mapping) {
        unsafe { (*self.inner.get()).write(mapping) };
        self.state.store(SWAP_DIRTY, Ordering::Release);
    }

    pub(crate) fn mark_pending(&self) {
        self.state.store(SWAP_PENDING, Ordering::Release);
    }

    /// Write a fresh replacement mapping and transition to `Clean`.
    ///
    /// # Safety
    /// Called only from the conductor thread after `inner` was uninit.
    pub(crate) unsafe fn publish_clean(&self, mapping: Mapping) {
        unsafe { (*self.inner.get()).write(mapping) };
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
    /// The evicted mapping to archive (rename) then drop. `None` for
    /// retry-only requests where the mapping was already dropped.
    pub(crate) mapping: Option<Mapping>,
    pub(crate) segment_size: usize,
    pub(crate) epoch: u64,
    pub(crate) swap: Arc<SegmentSwap>,
    /// Path of the slot file to create fresh for the replacement mapping.
    pub(crate) seg_path: PathBuf,
    pub(crate) hints: MapHints,
    pub(crate) archive_dir: Option<PathBuf>,
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Builder for configuring a [`Conductor`].
///
/// Obtained via [`ConductorBuilder::new`]. Call [`open`](Self::open) to spawn
/// the background thread and begin accepting sessions.
pub struct ConductorBuilder {
    dir: PathBuf,
    clean_queue_depth: usize,
    archive: bool,
}

impl ConductorBuilder {
    /// Create a builder rooted at `dir`.
    pub fn new(dir: impl AsRef<Path>) -> Self {
        Self {
            dir: dir.as_ref().to_path_buf(),
            clean_queue_depth: DEFAULT_CLEAN_QUEUE_DEPTH,
            archive: false,
        }
    }

    /// Set the backlog depth of the clean-request channel (default: 4).
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

    /// Spawn the conductor background thread and open the directory.
    pub fn open(self) -> Result<Conductor, super::OpenError> {
        std::fs::create_dir_all(&self.dir)?;

        let (tx, rx) = mpsc::ring_buffer(self.clean_queue_depth);
        let closing = Arc::new(AtomicBool::new(false));
        let alive = Arc::new(AtomicBool::new(true));

        let closing_c = Arc::clone(&closing);
        let alive_c = Arc::clone(&alive);
        let thread = std::thread::spawn(move || conductor_main(&rx, &closing_c, &alive_c));
        let wake_thread = thread.thread().clone();

        Ok(Conductor {
            dir: self.dir,
            tx,
            thread: Some(thread),
            closing,
            alive,
            wake_thread,
            archive: self.archive,
        })
    }
}

/// Top-level journal manager.
///
/// Owns the background cleanup thread that archives evicted segments and
/// creates fresh replacements. Drop to shut the thread down gracefully.
///
/// Must outlive any [`RotatingJournal`](super::RotatingJournal) opened through it.
pub struct Conductor {
    dir: PathBuf,
    tx: mpsc::Producer<CleanRequest>,
    thread: Option<JoinHandle<()>>,
    closing: Arc<AtomicBool>,
    alive: Arc<AtomicBool>,
    wake_thread: std::thread::Thread,
    archive: bool,
}

impl Conductor {
    /// Shorthand for [`ConductorBuilder::new(dir).open()`](ConductorBuilder::open).
    pub fn open(dir: impl AsRef<Path>) -> Result<Self, super::OpenError> {
        ConductorBuilder::new(dir).open()
    }

    /// Open a new or existing session log under this conductor.
    pub fn session(&mut self) -> super::RotatingJournalBuilder<'_> {
        super::RotatingJournalBuilder::new(self)
    }

    /// List session IDs that have a manifest on disk, sorted ascending.
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

    pub(crate) fn sender(&self) -> mpsc::Producer<CleanRequest> {
        self.tx.clone()
    }

    pub(crate) fn alive(&self) -> Arc<AtomicBool> {
        Arc::clone(&self.alive)
    }

    pub(crate) fn wake_thread(&self) -> std::thread::Thread {
        self.wake_thread.clone()
    }

    pub(crate) fn archive(&self) -> bool {
        self.archive
    }
}

impl Drop for Conductor {
    fn drop(&mut self) {
        self.closing.store(true, Ordering::Release);
        self.wake_thread.unpark();
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
    hints: MapHints,
}

fn conductor_main(rx: &mpsc::Consumer<CleanRequest>, closing: &AtomicBool, alive: &AtomicBool) {
    const MAX_SLEEP: Duration = Duration::from_secs(3);
    let mut sleep_dur = Duration::from_millis(1);
    let mut pending: Vec<PendingCreate> = Vec::new();

    loop {
        // Retry any previously failed mapping creates (e.g. ENOSPC).
        pending.retain(|p| {
            let Some(total) = NonZeroUsize::new(p.segment_size) else {
                return true;
            };
            let Some(mf) = file_create(&p.seg_path, total, p.hints).ok() else {
                return true;
            };
            let mapping: Mapping = mf.into();
            // SAFETY: conductor sole owner; state is Pending (inner uninit).
            unsafe {
                prefault(&mapping);
                p.swap.publish_clean(mapping);
            }
            false
        });

        // Drain all available requests.
        let mut drained = false;
        while let Some(req) = rx.pop() {
            drained = true;
            process_request(req, &mut pending);
        }

        if closing.load(Ordering::Acquire) {
            break;
        }

        if drained {
            sleep_dur = Duration::from_millis(1);
            continue;
        }

        std::thread::park_timeout(sleep_dur);
        if closing.load(Ordering::Acquire) {
            break;
        }
        sleep_dur = (sleep_dur * 2).min(MAX_SLEEP);
    }

    alive.store(false, Ordering::Release);
}

/// Prefault a freshly provisioned or reused segment before publishing it.
///
/// Write-touches (zeroes) every page so the `page_mkwrite` faults land here on
/// the conductor — off the writer's append hot path — when the writer next
/// refills the segment. Without this the writer eats the faults itself: a reused
/// segment that sat idle long enough for the kernel to write its pages back and
/// re-protect them re-faults on first touch. Zeroing also clears stale frames
/// from the previous epoch.
///
/// # Safety
/// `mapping` must be a live, writable mapping the conductor solely owns (swap is
/// `Pending`, so no other thread touches it).
unsafe fn prefault(mapping: &Mapping) {
    // SAFETY: caller guarantees `mapping` covers `len()` writable bytes owned by
    // this thread for the duration of the write.
    unsafe { std::ptr::write_bytes(mapping.as_ptr(), 0, mapping.len()) };
}

fn process_request(req: CleanRequest, pending: &mut Vec<PendingCreate>) {
    // Non-archiving fast path: reuse the evicted mapping in place. The slot's
    // replacement file *is* the evicted segment's own file, and `create()`
    // never truncates (only grows) — so recreating it would munmap, reopen, and
    // re-mmap the same file for nothing. We keep the mapping and just prefault
    // it. No munmap, no open, no ftruncate, no mmap: zero syscalls, so the
    // fs-metadata stall that delays provisioning simply cannot occur.
    if req.archive_dir.is_none() {
        if let Some(mapping) = req.mapping {
            // SAFETY: swap is Pending (inner uninit) until publish_clean; the
            // conductor solely owns the mapping here.
            unsafe {
                prefault(&mapping);
                req.swap.publish_clean(mapping);
            }
        }
        return;
    }

    // Archiving path: the evicted file is renamed out of the slot, so a fresh
    // replacement file must be created.
    if let Some(mapping) = req.mapping {
        // Durability before rename: the archive file must be on disk before it
        // is moved into place. msync(MS_SYNC) blocks, but only the archiving
        // path pays it.
        if let Some(ref archive_dir) = req.archive_dir
            && mapping.sync().is_ok()
            && std::fs::create_dir_all(archive_dir).is_ok()
        {
            let dst = archive_dir.join(format!("seg_{}.dat", req.epoch));
            let _ = std::fs::rename(&req.seg_path, dst);
        }

        drop(mapping);
    }

    let Some(total) = NonZeroUsize::new(req.segment_size) else {
        pending.push(PendingCreate {
            swap: req.swap,
            seg_path: req.seg_path,
            segment_size: req.segment_size,
            hints: req.hints,
        });
        return;
    };

    match file_create(&req.seg_path, total, req.hints)
        .ok()
        .map(Mapping::from)
    {
        Some(mapping) => {
            // SAFETY: state is Pending (inner uninit); conductor solely owns it.
            unsafe {
                prefault(&mapping);
                req.swap.publish_clean(mapping);
            }
        }
        None => {
            pending.push(PendingCreate {
                swap: req.swap,
                seg_path: req.seg_path,
                segment_size: req.segment_size,
                hints: req.hints,
            });
        }
    }
}

fn file_create(
    path: &Path,
    len: NonZeroUsize,
    hints: MapHints,
) -> Result<MappedFile, nexus_platform::MapError> {
    let mut opts = MappedFile::options();
    opts.pretouch(hints.pretouch).huge_pages(hints.huge_pages);
    opts.create(path, len)
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
