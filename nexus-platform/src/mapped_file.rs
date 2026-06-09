use std::fs::{File, OpenOptions};
use std::num::NonZeroUsize;
use std::os::fd::OwnedFd;
use std::path::Path;

use crate::mapping::{MapError, MappedFileOptions, Mapping, Protection, Sharing};

/// RAII file-backed memory mapping. Unmaps on drop.
///
/// Maps a persistent file on a durable filesystem (ext4, xfs, etc.) into
/// the process address space. The backing file is **not** removed on
/// drop — file lifecycle (unlink, rotate, archive) is the caller's
/// responsibility. The file persists so that peers or restarting processes
/// can access it.
///
/// All operations on the mapped bytes (`as_slice`, `read_at`, `write_at`,
/// `as_ptr`) are delegated to the inner [`Mapping`]. See its documentation
/// for the shared-mapping caveat.
///
/// # Usage
///
/// ## Convenience constructors (default options)
///
/// ```no_run
/// # use nexus_platform::MappedFile;
/// # use std::num::NonZeroUsize;
/// # let path = std::path::Path::new("/tmp/seg");
/// let mf = MappedFile::create(path, NonZeroUsize::new(4096).unwrap())?;
/// let mf = MappedFile::open(path)?;
/// let mf = MappedFile::open_readonly(path)?;
/// # Ok::<_, nexus_platform::MapError>(())
/// ```
///
/// ## Builder (full control)
///
/// ```no_run
/// # use nexus_platform::MappedFile;
/// # use std::num::NonZeroUsize;
/// # let path = std::path::Path::new("/tmp/seg");
/// let mf = MappedFile::options()
///     .read_write()
///     .shared()
///     .pretouch(true)
///     .create(path, NonZeroUsize::new(4096).unwrap())?;
/// # Ok::<_, nexus_platform::MapError>(())
/// ```
pub struct MappedFile {
    mapping: Mapping,
}

impl MappedFile {
    /// Return a builder for full control over protection, sharing, and hints.
    pub fn options() -> MappedFileOptions {
        MappedFileOptions::default()
    }

    /// Create or open a file at `path`, set its length to `len`, and map it
    /// as [`Sharing::Shared`] with [`Protection::ReadWrite`].
    ///
    /// This is the common case for IPC segments. The file is created if it
    /// does not exist. If the file already exists, it is resized to `len`
    /// (extending or truncating as needed).
    pub fn create(path: &Path, len: NonZeroUsize) -> Result<Self, MapError> {
        MappedFileOptions::default().create(path, len)
    }

    /// Open an existing file and map it as [`Sharing::Shared`] with
    /// [`Protection::ReadWrite`] at its current length.
    pub fn open(path: &Path) -> Result<Self, MapError> {
        MappedFileOptions::default().open(path)
    }

    /// Open an existing file read-only and map it as [`Sharing::Private`].
    pub fn open_readonly(path: &Path) -> Result<Self, MapError> {
        MappedFileOptions::default().read_only().private().open(path)
    }

    /// Access the underlying [`Mapping`].
    pub fn mapping(&self) -> &Mapping {
        &self.mapping
    }
}

impl std::ops::Deref for MappedFile {
    type Target = Mapping;

    fn deref(&self) -> &Mapping {
        &self.mapping
    }
}

impl MappedFileOptions {
    /// Create or open a file at `path`, set its length to `len`, and map it.
    ///
    /// The file is created if it does not exist. If the file already exists,
    /// it is resized to `len` (extending or truncating as needed).
    pub fn create(self, path: &Path, len: NonZeroUsize) -> Result<MappedFile, MapError> {
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(path)?;
        file.set_len(len.get() as u64)?;
        let fd = OwnedFd::from(file);
        let mapping = Mapping::new(fd, len, self)?;
        Ok(MappedFile { mapping })
    }

    /// Open an existing file and map it at its current length.
    ///
    /// The file is opened with the access mode implied by the protection
    /// setting. `offset` is ignored; the whole file is mapped from the start.
    pub fn open(self, path: &Path) -> Result<MappedFile, MapError> {
        let write = self.prot == Protection::ReadWrite;
        let file = OpenOptions::new().read(true).write(write).open(path)?;
        let len =
            NonZeroUsize::new(file.metadata()?.len() as usize).ok_or(MapError::EmptyFile)?;
        let fd = OwnedFd::from(file);
        let opts = MappedFileOptions { offset: 0, ..self };
        let mapping = Mapping::new(fd, len, opts)?;
        Ok(MappedFile { mapping })
    }

    /// Map an already-opened file with full control over length and offset.
    ///
    /// `self.offset` must be page-aligned (typically 4096 on Linux).
    /// Returns [`MapError::OutOfBounds`] if `offset + len` exceeds the
    /// file size.
    pub fn from_file(self, file: File, len: NonZeroUsize) -> Result<MappedFile, MapError> {
        let file_len = file.metadata()?.len();
        let end = self
            .offset
            .checked_add(len.get() as u64)
            .ok_or(MapError::OutOfBounds)?;
        if end > file_len {
            return Err(MapError::OutOfBounds);
        }
        let fd = OwnedFd::from(file);
        let mapping = Mapping::new(fd, len, self)?;
        Ok(MappedFile { mapping })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn temp_path(name: &str) -> std::path::PathBuf {
        std::env::temp_dir().join(format!("nexus-mmap-{}-{}", std::process::id(), name))
    }

    #[test]
    fn create_and_read_write() {
        let path = temp_path("rw");
        let _ = std::fs::remove_file(&path);

        let m = MappedFile::create(&path, NonZeroUsize::new(4096).unwrap()).unwrap();
        assert_eq!(m.len(), 4096);
        assert!(m.is_writable());

        m.write_at(&[0xDE, 0xAD, 0xBE, 0xEF], 0).unwrap();
        let mut buf = [0u8; 4];
        assert_eq!(m.read_at(&mut buf, 0), 4);
        assert_eq!(buf, [0xDE, 0xAD, 0xBE, 0xEF]);

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn open_existing() {
        let path = temp_path("open");
        let _ = std::fs::remove_file(&path);

        let m = MappedFile::create(&path, NonZeroUsize::new(256).unwrap()).unwrap();
        m.write_at(b"hello", 10).unwrap();
        drop(m);

        let m2 = MappedFile::open(&path).unwrap();
        let mut buf = [0u8; 5];
        m2.read_at(&mut buf, 10);
        assert_eq!(&buf, b"hello");

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn open_readonly() {
        let path = temp_path("readonly");
        let _ = std::fs::remove_file(&path);

        let m = MappedFile::create(&path, NonZeroUsize::new(128).unwrap()).unwrap();
        m.write_at(b"data", 0).unwrap();
        drop(m);

        let m2 = MappedFile::open_readonly(&path).unwrap();
        assert!(!m2.is_writable());
        assert_eq!(&m2.as_slice()[..4], b"data");

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn as_slice_roundtrip() {
        let path = temp_path("slice");
        let _ = std::fs::remove_file(&path);

        let m = MappedFile::create(&path, NonZeroUsize::new(64).unwrap()).unwrap();
        m.write_at(&[1, 2, 3, 4], 0).unwrap();
        assert_eq!(&m.as_slice()[..4], &[1, 2, 3, 4]);

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn read_at_partial() {
        let path = temp_path("partial");
        let _ = std::fs::remove_file(&path);

        let m = MappedFile::create(&path, NonZeroUsize::new(8).unwrap()).unwrap();
        let mut buf = [0u8; 16];
        let n = m.read_at(&mut buf, 4);
        assert_eq!(n, 4);

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn write_at_partial() {
        let path = temp_path("wpartial");
        let _ = std::fs::remove_file(&path);

        let m = MappedFile::create(&path, NonZeroUsize::new(8).unwrap()).unwrap();
        let n = m.write_at(&[1, 2, 3, 4], 6).unwrap();
        assert_eq!(n, 2);
        assert_eq!(&m.as_slice()[6..8], &[1, 2]);

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn read_at_beyond_end() {
        let path = temp_path("beyond");
        let _ = std::fs::remove_file(&path);

        let m = MappedFile::create(&path, NonZeroUsize::new(8).unwrap()).unwrap();
        let mut buf = [0u8; 4];
        let n = m.read_at(&mut buf, 100);
        assert_eq!(n, 0);

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn open_empty_file_fails() {
        let path = temp_path("empty");
        std::fs::write(&path, b"").unwrap();
        assert!(matches!(MappedFile::open(&path), Err(MapError::EmptyFile)));
        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn sync_succeeds() {
        let path = temp_path("sync");
        let _ = std::fs::remove_file(&path);

        let m = MappedFile::create(&path, NonZeroUsize::new(4096).unwrap()).unwrap();
        m.write_at(b"durable", 0).unwrap();
        m.sync().unwrap();

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn advise_succeeds() {
        let path = temp_path("advise");
        let _ = std::fs::remove_file(&path);

        let m = MappedFile::create(&path, NonZeroUsize::new(4096).unwrap()).unwrap();
        m.advise(crate::Advice::Sequential).unwrap();
        m.advise(crate::Advice::Random).unwrap();
        m.advise(crate::Advice::WillNeed).unwrap();
        m.advise(crate::Advice::Normal).unwrap();

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn builder_pretouch() {
        let path = temp_path("pretouch");
        let _ = std::fs::remove_file(&path);

        let m = MappedFile::options()
            .pretouch(true)
            .create(&path, NonZeroUsize::new(4096).unwrap())
            .unwrap();
        assert!(m.is_writable());

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn from_file_with_offset() {
        let path = temp_path("offset");
        let _ = std::fs::remove_file(&path);

        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(&path)
            .unwrap();
        file.set_len(8192).unwrap();

        let full = MappedFile::options()
            .from_file(file, NonZeroUsize::new(8192).unwrap())
            .unwrap();
        full.write_at(b"offset-test", 4096).unwrap();
        drop(full);

        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .open(&path)
            .unwrap();
        let window = MappedFile::options()
            .offset(4096)
            .from_file(file, NonZeroUsize::new(4096).unwrap())
            .unwrap();
        assert_eq!(&window.as_slice()[..11], b"offset-test");

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn write_readonly_returns_error() {
        let path = temp_path("write-ro");
        let _ = std::fs::remove_file(&path);

        let m = MappedFile::create(&path, NonZeroUsize::new(128).unwrap()).unwrap();
        m.write_at(b"setup", 0).unwrap();
        drop(m);

        let m2 = MappedFile::open_readonly(&path).unwrap();
        let err = m2.write_at(b"nope", 0).unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::PermissionDenied);

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn from_file_rejects_out_of_bounds() {
        let path = temp_path("oob");
        let _ = std::fs::remove_file(&path);

        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(&path)
            .unwrap();
        file.set_len(4096).unwrap();

        let result = MappedFile::options().from_file(file, NonZeroUsize::new(8192).unwrap());
        assert!(matches!(result, Err(MapError::OutOfBounds)));

        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .open(&path)
            .unwrap();
        let result = MappedFile::options()
            .offset(4096)
            .from_file(file, NonZeroUsize::new(4096).unwrap());
        assert!(matches!(result, Err(MapError::OutOfBounds)));

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn two_mappings_see_same_data() {
        let path = temp_path("shared");
        let _ = std::fs::remove_file(&path);

        let m1 = MappedFile::create(&path, NonZeroUsize::new(4096).unwrap()).unwrap();
        let m2 = MappedFile::open(&path).unwrap();

        m1.write_at(b"visible", 0).unwrap();
        let mut buf = [0u8; 7];
        m2.read_at(&mut buf, 0);
        assert_eq!(&buf, b"visible");

        std::fs::remove_file(&path).unwrap();
    }
}
