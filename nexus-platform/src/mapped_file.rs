use std::fs::{File, OpenOptions};
use std::num::NonZeroUsize;
use std::os::fd::OwnedFd;
use std::path::Path;

use crate::mapping::{MapError, MapOptions, Mapping, Protection, Sharing};

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
pub struct MappedFile {
    mapping: Mapping,
}

impl MappedFile {
    /// Create or open a file at `path`, set its length to `len`, and map it
    /// as [`Sharing::Shared`] with [`Protection::ReadWrite`].
    ///
    /// This is the common case for IPC segments. The file is created if it
    /// does not exist. If the file already exists, it is resized to `len`
    /// (extending or truncating as needed).
    pub fn create(path: &Path, len: NonZeroUsize, opts: MapOptions) -> Result<Self, MapError> {
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(path)?;
        file.set_len(len.get() as u64)?;
        Self::from_file(file, len, 0, Protection::ReadWrite, Sharing::Shared, opts)
    }

    /// Open an existing file and map it as [`Sharing::Shared`] with
    /// [`Protection::ReadWrite`] at its current length.
    pub fn open(path: &Path, opts: MapOptions) -> Result<Self, MapError> {
        let file = OpenOptions::new().read(true).write(true).open(path)?;
        let len = NonZeroUsize::new(file.metadata()?.len() as usize).ok_or(MapError::EmptyFile)?;
        Self::from_file(file, len, 0, Protection::ReadWrite, Sharing::Shared, opts)
    }

    /// Open an existing file read-only and map it as [`Sharing::Private`].
    pub fn open_readonly(path: &Path, opts: MapOptions) -> Result<Self, MapError> {
        let file = OpenOptions::new().read(true).open(path)?;
        let len = NonZeroUsize::new(file.metadata()?.len() as usize).ok_or(MapError::EmptyFile)?;
        Self::from_file(file, len, 0, Protection::ReadOnly, Sharing::Private, opts)
    }

    /// Map an already-opened file with full control over protection,
    /// sharing mode, and file offset.
    ///
    /// `offset` must be page-aligned (typically 4096 on Linux). The kernel
    /// will return an error if it is not.
    ///
    /// Returns [`MapError::OutOfBounds`] if `offset + len` exceeds the
    /// file size.
    pub fn from_file(
        file: File,
        len: NonZeroUsize,
        offset: u64,
        prot: Protection,
        sharing: Sharing,
        opts: MapOptions,
    ) -> Result<Self, MapError> {
        let file_len = file.metadata()?.len();
        let end = offset
            .checked_add(len.get() as u64)
            .ok_or(MapError::OutOfBounds)?;
        if end > file_len {
            return Err(MapError::OutOfBounds);
        }
        let fd = OwnedFd::from(file);
        let mapping = Mapping::new(fd, len, offset, prot, sharing, opts)?;
        Ok(Self { mapping })
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

        let m = MappedFile::create(
            &path,
            NonZeroUsize::new(4096).unwrap(),
            MapOptions::default(),
        )
        .unwrap();
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

        let m = MappedFile::create(
            &path,
            NonZeroUsize::new(256).unwrap(),
            MapOptions::default(),
        )
        .unwrap();
        m.write_at(b"hello", 10).unwrap();
        drop(m);

        let m2 = MappedFile::open(&path, MapOptions::default()).unwrap();
        let mut buf = [0u8; 5];
        m2.read_at(&mut buf, 10);
        assert_eq!(&buf, b"hello");

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn open_readonly() {
        let path = temp_path("readonly");
        let _ = std::fs::remove_file(&path);

        let m = MappedFile::create(
            &path,
            NonZeroUsize::new(128).unwrap(),
            MapOptions::default(),
        )
        .unwrap();
        m.write_at(b"data", 0).unwrap();
        drop(m);

        let m2 = MappedFile::open_readonly(&path, MapOptions::default()).unwrap();
        assert!(!m2.is_writable());
        assert_eq!(&m2.as_slice()[..4], b"data");

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn as_slice_roundtrip() {
        let path = temp_path("slice");
        let _ = std::fs::remove_file(&path);

        let m = MappedFile::create(&path, NonZeroUsize::new(64).unwrap(), MapOptions::default())
            .unwrap();
        m.write_at(&[1, 2, 3, 4], 0).unwrap();
        assert_eq!(&m.as_slice()[..4], &[1, 2, 3, 4]);

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn read_at_partial() {
        let path = temp_path("partial");
        let _ = std::fs::remove_file(&path);

        let m = MappedFile::create(&path, NonZeroUsize::new(8).unwrap(), MapOptions::default())
            .unwrap();
        let mut buf = [0u8; 16];
        let n = m.read_at(&mut buf, 4);
        assert_eq!(n, 4);

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn write_at_partial() {
        let path = temp_path("wpartial");
        let _ = std::fs::remove_file(&path);

        let m = MappedFile::create(&path, NonZeroUsize::new(8).unwrap(), MapOptions::default())
            .unwrap();
        let n = m.write_at(&[1, 2, 3, 4], 6).unwrap();
        assert_eq!(n, 2);
        assert_eq!(&m.as_slice()[6..8], &[1, 2]);

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn read_at_beyond_end() {
        let path = temp_path("beyond");
        let _ = std::fs::remove_file(&path);

        let m = MappedFile::create(&path, NonZeroUsize::new(8).unwrap(), MapOptions::default())
            .unwrap();
        let mut buf = [0u8; 4];
        let n = m.read_at(&mut buf, 100);
        assert_eq!(n, 0);

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn open_empty_file_fails() {
        let path = temp_path("empty");
        std::fs::write(&path, b"").unwrap();
        assert!(matches!(
            MappedFile::open(&path, MapOptions::default()),
            Err(MapError::EmptyFile)
        ));
        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn sync_succeeds() {
        let path = temp_path("sync");
        let _ = std::fs::remove_file(&path);

        let m = MappedFile::create(
            &path,
            NonZeroUsize::new(4096).unwrap(),
            MapOptions::default(),
        )
        .unwrap();
        m.write_at(b"durable", 0).unwrap();
        m.sync().unwrap();

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn advise_succeeds() {
        let path = temp_path("advise");
        let _ = std::fs::remove_file(&path);

        let m = MappedFile::create(
            &path,
            NonZeroUsize::new(4096).unwrap(),
            MapOptions::default(),
        )
        .unwrap();
        m.advise(crate::Advice::Sequential).unwrap();
        m.advise(crate::Advice::Random).unwrap();
        m.advise(crate::Advice::WillNeed).unwrap();
        m.advise(crate::Advice::Normal).unwrap();

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

        let full = MappedFile::from_file(
            file,
            NonZeroUsize::new(8192).unwrap(),
            0,
            Protection::ReadWrite,
            Sharing::Shared,
            MapOptions::default(),
        )
        .unwrap();
        full.write_at(b"offset-test", 4096).unwrap();
        drop(full);

        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .open(&path)
            .unwrap();
        let window = MappedFile::from_file(
            file,
            NonZeroUsize::new(4096).unwrap(),
            4096,
            Protection::ReadWrite,
            Sharing::Shared,
            MapOptions::default(),
        )
        .unwrap();
        assert_eq!(&window.as_slice()[..11], b"offset-test");

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn write_readonly_returns_error() {
        let path = temp_path("write-ro");
        let _ = std::fs::remove_file(&path);

        let m = MappedFile::create(
            &path,
            NonZeroUsize::new(128).unwrap(),
            MapOptions::default(),
        )
        .unwrap();
        m.write_at(b"setup", 0).unwrap();
        drop(m);

        let m2 = MappedFile::open_readonly(&path, MapOptions::default()).unwrap();
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

        let result = MappedFile::from_file(
            file,
            NonZeroUsize::new(8192).unwrap(),
            0,
            Protection::ReadWrite,
            Sharing::Shared,
            MapOptions::default(),
        );
        assert!(matches!(result, Err(MapError::OutOfBounds)));

        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .open(&path)
            .unwrap();
        let result = MappedFile::from_file(
            file,
            NonZeroUsize::new(4096).unwrap(),
            4096,
            Protection::ReadWrite,
            Sharing::Shared,
            MapOptions::default(),
        );
        assert!(matches!(result, Err(MapError::OutOfBounds)));

        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn two_mappings_see_same_data() {
        let path = temp_path("shared");
        let _ = std::fs::remove_file(&path);

        let m1 = MappedFile::create(
            &path,
            NonZeroUsize::new(4096).unwrap(),
            MapOptions::default(),
        )
        .unwrap();
        let m2 = MappedFile::open(&path, MapOptions::default()).unwrap();

        m1.write_at(b"visible", 0).unwrap();
        let mut buf = [0u8; 7];
        m2.read_at(&mut buf, 0);
        assert_eq!(&buf, b"visible");

        std::fs::remove_file(&path).unwrap();
    }
}
