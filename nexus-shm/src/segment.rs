use std::num::NonZeroUsize;
use std::path::Path;
use std::sync::atomic::AtomicU32;

use nexus_platform::{Liveness, MappedFile, Mapping, ProcessLease};

use crate::MapHints;

use crate::control::{ControlBlock, status};
use crate::error::ShmError;

const HEADER: NonZeroUsize = match NonZeroUsize::new(size_of::<ControlBlock>()) {
    Some(n) => n,
    None => panic!("control block is zero-sized"),
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Status {
    Uninit,
    Alive,
    Dead,
}

/// A mapped shared-memory segment: a control block followed by a payload.
///
/// File lifecycle (unlink, rotate, archive) is the caller's responsibility. The
/// backing file persists after drop so a restarting peer can run crash
/// recovery; segment owns only the mapping and its liveness signals.
pub struct Segment {
    mapping: Mapping,
    creator: bool,
}

impl Segment {
    /// The total mapping size needed for a segment with `data_len` payload bytes.
    pub fn total_size(data_len: usize) -> Result<NonZeroUsize, ShmError> {
        HEADER.checked_add(data_len).ok_or(ShmError::SizeOverflow)
    }

    /// Create a new segment backed by the file at `path`, creating or truncating it.
    ///
    /// If the file already exists and its owner is still alive (`peer_liveness()` returns
    /// `Alive`), returns `ShmError::OwnerActive`. If the owner is dead the segment is
    /// re-incarnated in place and `generation()` is incremented.
    pub fn create_file(
        path: impl AsRef<Path>,
        data_len: usize,
        hints: MapHints,
    ) -> Result<Self, ShmError> {
        let total = Self::total_size(data_len)?;
        let mf = MappedFile::create(path.as_ref(), total)?;
        Self::create(mf, data_len, hints)
    }

    /// Attach to an existing segment backed by the file at `path`.
    ///
    /// Equivalent to `MappedFile::open` + `Segment::attach`.
    pub fn attach_file(path: impl AsRef<Path>) -> Result<Self, ShmError> {
        let mf = MappedFile::open(path.as_ref())?;
        Self::attach(mf)
    }

    pub fn create(
        mapping: impl Into<Mapping>,
        data_len: usize,
        hints: MapHints,
    ) -> Result<Self, ShmError> {
        if data_len == 0 {
            return Err(ShmError::EmptySegment);
        }
        let mapping = mapping.into();
        let required = HEADER.get() + data_len;
        if mapping.len() < required {
            return Err(ShmError::MappingTooSmall {
                required,
                actual: mapping.len(),
            });
        }

        if !ProcessLease::claim(mapping.as_fd())? {
            return Err(ShmError::OwnerActive);
        }

        // SAFETY: we hold the OFD owner lock acquired above, so no other process
        // is writing the control block; mmap returns page-aligned memory (hence
        // ControlBlock-aligned) covering at least the header.
        let cb = unsafe { &mut *mapping.as_ptr().cast::<ControlBlock>() };
        let generation = cb.generation().wrapping_add(1);
        cb.write_header(
            flags(hints),
            generation,
            std::process::id(),
            data_len as u64,
        );

        Ok(Self {
            mapping,
            creator: true,
        })
    }

    pub fn attach(mapping: impl Into<Mapping>) -> Result<Self, ShmError> {
        let mapping = mapping.into();
        let cb = Self::control_of(&mapping);
        cb.validate()?;
        let required = HEADER.get() + cb.data_len() as usize;
        if mapping.len() < required {
            return Err(ShmError::MappingTooSmall {
                required,
                actual: mapping.len(),
            });
        }
        Ok(Self {
            mapping,
            creator: false,
        })
    }

    /// Tier-1 liveness from the atomic status field.
    ///
    /// `Dead` is authoritative. `Alive` may be stale if the owner died without
    /// running its drop guard (`SIGKILL`, `panic=abort`); confirm with
    /// [`Segment::peer_liveness`], which consults the kernel-held OFD lock.
    pub fn status(&self) -> Status {
        match self.control().status() {
            s if s == status::ALIVE => Status::Alive,
            s if s == status::DEAD => Status::Dead,
            _ => Status::Uninit,
        }
    }

    pub fn peer_liveness(&self) -> Liveness {
        ProcessLease::probe(self.mapping.as_fd())
    }

    pub fn sync(&self) -> std::io::Result<()> {
        self.mapping.sync()
    }

    pub fn data(&self) -> *mut u8 {
        // SAFETY: the mapping is HEADER + data_len bytes, so HEADER is in bounds.
        unsafe { self.mapping.as_ptr().add(HEADER.get()) }
    }

    /// `AtomicU32` at `offset` within the payload (commit-length field).
    ///
    /// # Safety
    /// `offset` must be 4-byte-aligned and within `data_len()`.
    #[inline]
    pub unsafe fn commit_len_at(&self, offset: usize) -> &AtomicU32 {
        unsafe { AtomicU32::from_ptr(self.data().add(offset).cast()) }
    }

    /// Frame discriminant (bytes 4-5 of the frame header) at `offset`.
    ///
    /// # Safety
    /// The frame header at `offset` must be published (read after an Acquire
    /// load of `commit_len_at`) and within `data_len()`.
    #[inline]
    pub unsafe fn frame_kind_at(&self, offset: usize) -> u16 {
        unsafe { std::ptr::read_unaligned(self.data().add(offset + 4).cast()) }
    }

    /// Write the frame discriminant at `offset` (bytes 4-5) and zero bytes 6-7.
    ///
    /// # Safety
    /// The 8-byte frame header at `offset` must be within `data_len()` and
    /// reserved for this record.
    #[inline]
    pub unsafe fn write_frame_kind_at(&self, offset: usize, kind: u16) {
        unsafe {
            std::ptr::write_unaligned(self.data().add(offset + 4).cast::<u16>(), kind);
            std::ptr::write_unaligned(self.data().add(offset + 6).cast::<u16>(), 0);
        }
    }

    /// Write `val` at `offset` (unaligned).
    ///
    /// # Safety
    /// `[offset, offset + size_of::<T>())` must be within `data_len()` and
    /// reserved for this write.
    #[inline]
    pub unsafe fn write_at<T: Copy>(&self, offset: usize, val: T) {
        unsafe { std::ptr::write_unaligned(self.data().add(offset).cast(), val) }
    }

    /// Read a `T` at `offset` (unaligned).
    ///
    /// # Safety
    /// `[offset, offset + size_of::<T>())` must be within `data_len()` and
    /// the data must be published before this call.
    #[inline]
    pub unsafe fn read_at<T: Copy>(&self, offset: usize) -> T {
        unsafe { std::ptr::read_unaligned(self.data().add(offset).cast()) }
    }

    /// Immutable byte slice `[offset, offset + len)`.
    ///
    /// # Safety
    /// The range must be within `data_len()` and the bytes must be published.
    /// The returned slice borrows `self` so the segment must outlive the slice.
    #[inline]
    pub unsafe fn slice_at(&self, offset: usize, len: usize) -> &[u8] {
        unsafe { std::slice::from_raw_parts(self.data().add(offset), len) }
    }

    /// Mutable byte slice `[offset, offset + len)`.
    ///
    /// # Safety
    /// The range must be within `data_len()`, exclusively reserved for this
    /// write, and the segment must outlive the slice.
    #[inline]
    pub unsafe fn slice_mut_at(&mut self, offset: usize, len: usize) -> &mut [u8] {
        unsafe { std::slice::from_raw_parts_mut(self.data().add(offset), len) }
    }

    pub fn data_len(&self) -> usize {
        self.control().data_len() as usize
    }

    /// Incarnation counter — incremented each time the segment is re-created over the same file.
    ///
    /// Use this to detect that a peer has restarted and re-initialized the region since you
    /// attached. Not suitable as a per-access validity check.
    pub fn generation(&self) -> u64 {
        self.control().generation()
    }

    /// PID of the process that last called `create` or `create_file` on this segment.
    ///
    /// Diagnostic/observability only. PIDs are reused by the OS after a process exits, so
    /// this is not a liveness check. Use `peer_liveness()` to determine if the owner is alive.
    pub fn owner_pid(&self) -> u32 {
        self.control().owner_pid()
    }

    fn control(&self) -> &ControlBlock {
        Self::control_of(&self.mapping)
    }

    fn control_of(mapping: &Mapping) -> &ControlBlock {
        // SAFETY: mmap maps whole pages, so the control block (<= one page) is
        // mapped and page-aligned. All control-block fields are atomic or
        // written once before sharing, so shared `&` access is sound.
        unsafe { &*mapping.as_ptr().cast::<ControlBlock>() }
    }
}

impl Drop for Segment {
    fn drop(&mut self) {
        if self.creator {
            self.control().mark_dead();
        }
    }
}

fn flags(hints: MapHints) -> u16 {
    u16::from(hints.pretouch) | (u16::from(hints.huge_pages) << 1)
}

#[cfg(test)]
mod tests {
    use super::{Liveness, Segment, Status};
    use crate::MapHints;
    use crate::error::ShmError;
    use nexus_platform::MappedFile;

    fn temp_path(name: &str) -> std::path::PathBuf {
        std::env::temp_dir().join(format!("nexus-shm-{}-{}", std::process::id(), name))
    }

    fn create_file(path: &std::path::Path, data_len: usize) -> MappedFile {
        let total = Segment::total_size(data_len).unwrap();
        MappedFile::create(path, total).unwrap()
    }

    fn open_file(path: &std::path::Path) -> MappedFile {
        MappedFile::open(path).unwrap()
    }

    #[test]
    fn create_attach_roundtrip() {
        let path = temp_path("roundtrip");
        let _ = std::fs::remove_file(&path);

        let mf = create_file(&path, 4096);
        let mut seg = Segment::create(mf, 4096, MapHints::default()).unwrap();
        assert_eq!(seg.data_len(), 4096);
        assert_eq!(seg.status(), Status::Alive);

        unsafe { seg.slice_mut_at(0, 1)[0] = 0xAB };

        let peer = Segment::attach(open_file(&path)).unwrap();
        assert_eq!(peer.data_len(), 4096);
        assert_eq!(peer.status(), Status::Alive);
        assert_eq!(unsafe { peer.slice_at(0, 1)[0] }, 0xAB);

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn creator_drop_marks_dead() {
        let path = temp_path("dead");
        let _ = std::fs::remove_file(&path);

        let seg = Segment::create(create_file(&path, 64), 64, MapHints::default()).unwrap();
        drop(seg);

        let peer = Segment::attach(open_file(&path)).unwrap();
        assert_eq!(peer.status(), Status::Dead);

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn rejects_zero_data_len() {
        let path = temp_path("zero");
        let _ = std::fs::remove_file(&path);
        let mf = create_file(&path, 64);
        assert!(matches!(
            Segment::create(mf, 0, MapHints::default()),
            Err(ShmError::EmptySegment)
        ));
        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn kernel_liveness_tracks_owner() {
        let path = temp_path("liveness");
        let _ = std::fs::remove_file(&path);

        let owner = Segment::create(create_file(&path, 64), 64, MapHints::default()).unwrap();
        let peer = Segment::attach(open_file(&path)).unwrap();
        assert_eq!(peer.peer_liveness(), Liveness::Alive);

        drop(owner);
        assert_eq!(peer.peer_liveness(), Liveness::Dead);

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn rejects_foreign_file() {
        let path = temp_path("foreign");
        std::fs::write(&path, vec![0u8; 4096]).unwrap();

        assert!(Segment::attach(open_file(&path)).is_err());

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn create_file_attach_file_roundtrip() {
        let path = temp_path("file-api");
        let _ = std::fs::remove_file(&path);

        let seg = Segment::create_file(&path, 512, MapHints::default()).unwrap();
        assert_eq!(seg.status(), Status::Alive);

        let peer = Segment::attach_file(&path).unwrap();
        assert_eq!(peer.data_len(), 512);
        assert_eq!(peer.status(), Status::Alive);

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn generation_increments_on_recreate() {
        let path = temp_path("generation");
        let _ = std::fs::remove_file(&path);

        let seg = Segment::create_file(&path, 64, MapHints::default()).unwrap();
        let gen1 = seg.generation();
        drop(seg);

        let seg2 = Segment::create_file(&path, 64, MapHints::default()).unwrap();
        assert_eq!(seg2.generation(), gen1 + 1);

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn owner_pid_is_current_process() {
        let path = temp_path("owner-pid");
        let _ = std::fs::remove_file(&path);

        let seg = Segment::create_file(&path, 64, MapHints::default()).unwrap();
        assert_eq!(seg.owner_pid(), std::process::id());

        std::fs::remove_file(&path).unwrap();
    }
}
