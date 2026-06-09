use std::num::NonZeroUsize;
use std::path::Path;
use std::sync::atomic::{AtomicU64, Ordering};

use nexus_platform::MappedFile;

use crate::error::ShmError;

const MAGIC: u32 = u32::from_le_bytes(*b"NXLG");
const VERSION: u16 = 1;

pub(crate) const SESSION_NAME_LEN: usize = 64;

/// Fixed-size header at the start of `journal.manifest`.
///
/// Mmap'd directly — reads and writes go through the page cache with no
/// serialization layer. All fields except `epoch` are written once at
/// creation and never change. `epoch` is atomically updated on each
/// segment rotation, which is how crash recovery knows which slot was
/// active: `slot_index = epoch % 3`.
///
/// # Binary layout (96 bytes, 8-byte aligned)
///
/// ```text
///  offset  size  field
///  ──────  ────  ─────────────────
///    0      64   name             (UTF-8, padded with zeros)
///   64       8   segment_size     (bytes per segment file)
///   72       8   epoch            (AtomicU64, rotation counter)
///   80       4   magic            (0x4E584C47 = "NXLG" LE)
///   84       4   session_id
///   88       2   version          (format version, currently 1)
///   90       1   name_len         (valid bytes in name[])
///   91       5   _pad
/// ```
#[repr(C)]
struct ManifestHeader {
    name: [u8; SESSION_NAME_LEN],
    segment_size: u64,
    epoch: AtomicU64,
    magic: u32,
    session_id: u32,
    version: u16,
    name_len: u8,
    _pad: [u8; 5],
}

const _: () = {
    assert!(size_of::<ManifestHeader>() == 96);
    assert!(align_of::<ManifestHeader>() == 8);
};

const MANIFEST_FILE_SIZE: usize = 4096;

/// Persistent metadata for a single journal session.
///
/// Each session's `journal.manifest` is a 4096-byte mmap'd file containing
/// a [`ManifestHeader`]. The file is created when a session is first opened
/// and persists across process restarts.
///
/// On recovery, the manifest provides two things:
///
/// 1. **Structural config** — `segment_size` and `session_id` are checked
///    against the builder's settings (strict mode errors on mismatch,
///    non-strict mode uses the manifest's values).
///
/// 2. **Rotation state** — `epoch` tells recovery which slot was `current`
///    (`epoch % 3`), which was `prev` (`(epoch - 1) % 3`), and which is
///    `standby`. Recovery then scans the current slot's frames to find
///    the write tail.
pub(crate) struct Manifest {
    mapping: MappedFile,
}

impl Manifest {
    pub(crate) fn create(
        path: &Path,
        segment_size: u64,
        session_id: u32,
        name: &[u8],
    ) -> Result<Self, ShmError> {
        let len = NonZeroUsize::new(MANIFEST_FILE_SIZE).unwrap();
        let mapping = MappedFile::create(path, len)?;

        // SAFETY: the mapping covers at least MANIFEST_FILE_SIZE bytes and is
        // page-aligned. We hold exclusive access (just created the file).
        let hdr = unsafe { &mut *mapping.as_ptr().cast::<ManifestHeader>() };
        let n = name.len().min(SESSION_NAME_LEN);
        hdr.name = [0; SESSION_NAME_LEN];
        hdr.name[..n].copy_from_slice(&name[..n]);
        hdr.segment_size = segment_size;
        *hdr.epoch.get_mut() = 0;
        hdr.magic = MAGIC;
        hdr.session_id = session_id;
        hdr.version = VERSION;
        hdr.name_len = n as u8;
        hdr._pad = [0; 5];

        Ok(Self { mapping })
    }

    pub(crate) fn open(path: &Path) -> Result<Self, ShmError> {
        let mapping = MappedFile::open(path)?;
        let hdr = Self::header_of(&mapping);

        if hdr.magic != MAGIC {
            return Err(ShmError::BadMagic { found: hdr.magic });
        }
        if hdr.version != VERSION {
            return Err(ShmError::UnsupportedLayout {
                found: hdr.version,
                expected: VERSION,
            });
        }

        Ok(Self { mapping })
    }

    pub(crate) fn segment_size(&self) -> u64 {
        self.header().segment_size
    }

    pub(crate) fn session_id(&self) -> u32 {
        self.header().session_id
    }

    pub(crate) fn name(&self) -> &[u8] {
        let hdr = self.header();
        let n = hdr.name_len as usize;
        &hdr.name[..n]
    }

    pub(crate) fn epoch(&self) -> u64 {
        self.header().epoch.load(Ordering::Acquire)
    }

    pub(crate) fn set_epoch(&self, epoch: u64) {
        self.header().epoch.store(epoch, Ordering::Release);
    }

    fn header(&self) -> &ManifestHeader {
        Self::header_of(&self.mapping)
    }

    fn header_of(mapping: &MappedFile) -> &ManifestHeader {
        // SAFETY: the mapping is at least MANIFEST_FILE_SIZE bytes and
        // page-aligned. ManifestHeader is 96 bytes with 8-byte alignment.
        unsafe { &*mapping.as_ptr().cast::<ManifestHeader>() }
    }
}
