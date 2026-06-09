use std::ffi::CString;
use std::num::NonZeroUsize;

use crate::mapping::{self, MapError, MapOptions, Mapping, Protection, Sharing};

/// Builder for [`SharedMemory`], following the [`std::fs::OpenOptions`]
/// pattern.
///
/// Obtained via [`SharedMemory::options()`]. Configure protection, sharing
/// mode, and mapping hints, then call a terminal method to create the
/// mapping.
///
/// # Defaults
///
/// | Field | Default |
/// |-------|---------|
/// | protection | [`Protection::ReadWrite`] |
/// | sharing | [`Sharing::Shared`] |
/// | pretouch | `false` |
/// | huge_pages | `false` |
/// | unlink_on_drop | `false` |
///
/// # Examples
///
/// ```no_run
/// use nexus_platform::SharedMemory;
/// use std::num::NonZeroUsize;
///
/// let shm = SharedMemory::options()
///     .pretouch(true)
///     .unlink_on_drop(true)
///     .create("/my-region", NonZeroUsize::new(4096).unwrap())?;
/// # Ok::<_, nexus_platform::MapError>(())
/// ```
#[derive(Debug, Clone, Copy)]
pub struct SharedMemoryOptions {
    protection: Protection,
    sharing: Sharing,
    pretouch: bool,
    huge_pages: bool,
    unlink_on_drop: bool,
}

impl SharedMemoryOptions {
    fn new() -> Self {
        Self {
            protection: Protection::ReadWrite,
            sharing: Sharing::Shared,
            pretouch: false,
            huge_pages: false,
            unlink_on_drop: false,
        }
    }

    /// Set the mapping protection to [`Protection::ReadWrite`].
    pub fn read_write(&mut self) -> &mut Self {
        self.protection = Protection::ReadWrite;
        self
    }

    /// Set the mapping protection to [`Protection::ReadOnly`].
    pub fn read_only(&mut self) -> &mut Self {
        self.protection = Protection::ReadOnly;
        self
    }

    /// Share writes with other mappings ([`Sharing::Shared`], `MAP_SHARED`).
    pub fn shared(&mut self) -> &mut Self {
        self.sharing = Sharing::Shared;
        self
    }

    /// Copy-on-write: writes are private ([`Sharing::Private`], `MAP_PRIVATE`).
    pub fn private(&mut self) -> &mut Self {
        self.sharing = Sharing::Private;
        self
    }

    /// Pre-fault pages into memory on creation (`MAP_POPULATE`).
    pub fn pretouch(&mut self, pretouch: bool) -> &mut Self {
        self.pretouch = pretouch;
        self
    }

    /// Request huge-page backing (`MAP_HUGETLB`).
    pub fn huge_pages(&mut self, huge_pages: bool) -> &mut Self {
        self.huge_pages = huge_pages;
        self
    }

    /// Remove the shm object from the namespace on drop.
    ///
    /// When `true`, dropping the [`SharedMemory`] calls `shm_unlink`.
    /// Existing mappings in other processes remain valid until they are
    /// themselves dropped.
    ///
    /// Default: `false` — the name persists for other processes to attach.
    pub fn unlink_on_drop(&mut self, unlink: bool) -> &mut Self {
        self.unlink_on_drop = unlink;
        self
    }

    /// Create or open a named shared memory object and map it.
    ///
    /// The object is created if it does not exist. If it already exists,
    /// it is extended to `len` if smaller (never truncated).
    pub fn create(&self, name: &str, len: NonZeroUsize) -> Result<SharedMemory, MapError> {
        let cname = validate_name(name)?;
        let fd = mapping::shm_open_create(&cname)?;
        let current = mapping::fd_size(&fd)?;
        if (len.get() as u64) > current {
            mapping::ftruncate(&fd, len.get() as u64)?;
        }
        let opts = MapOptions {
            pretouch: self.pretouch,
            huge_pages: self.huge_pages,
        };
        let mapping = Mapping::new(fd, len, 0, self.protection, self.sharing, opts)?;
        Ok(SharedMemory {
            mapping,
            name: cname,
            unlink_on_drop: self.unlink_on_drop,
        })
    }

    /// Open an existing named shared memory object and map it at its
    /// current size.
    ///
    /// The fd is opened `O_RDWR` only when both `Shared` and `ReadWrite`
    /// are set — that is the only combination where writes propagate to
    /// the backing store. Private (COW) mappings only need read access.
    pub fn open(&self, name: &str) -> Result<SharedMemory, MapError> {
        let cname = validate_name(name)?;
        let write = self.sharing == Sharing::Shared && self.protection == Protection::ReadWrite;
        let fd = mapping::shm_open_existing(&cname, write)?;
        let size: usize = mapping::fd_size(&fd)?
            .try_into()
            .map_err(|_| MapError::OutOfBounds)?;
        let len = NonZeroUsize::new(size).ok_or(MapError::EmptyFile)?;
        let opts = MapOptions {
            pretouch: self.pretouch,
            huge_pages: self.huge_pages,
        };
        let mapping = Mapping::new(fd, len, 0, self.protection, self.sharing, opts)?;
        Ok(SharedMemory {
            mapping,
            name: cname,
            unlink_on_drop: self.unlink_on_drop,
        })
    }
}

/// RAII shared memory region backed by POSIX `shm_open(3)`.
///
/// Creates or opens a named object in the kernel's tmpfs namespace
/// (`/dev/shm` on Linux), then maps it into the process address space.
/// The backing store is RAM — no disk I/O, no filesystem persistence.
///
/// The name persists in the shm namespace until explicitly removed via
/// [`unlink`](Self::unlink) or dropped with
/// [`unlink_on_drop`](SharedMemoryOptions::unlink_on_drop) enabled.
///
/// For full control over protection, sharing, and mapping hints, use
/// [`SharedMemory::options()`]. The convenience methods
/// [`create`](Self::create), [`open`](Self::open), and
/// [`open_readonly`](Self::open_readonly) cover the common cases.
///
/// All operations on the mapped bytes (`as_slice`, `read_at`, `write_at`,
/// `as_ptr`) are delegated to the inner [`Mapping`]. See its documentation
/// for the shared-mapping caveat.
///
/// # Examples
///
/// ```no_run
/// use nexus_platform::SharedMemory;
/// use std::num::NonZeroUsize;
///
/// let shm = SharedMemory::create("/nexus-seg", NonZeroUsize::new(4096).unwrap())?;
/// shm.write_at(b"hello", 0)?;
///
/// let peer = SharedMemory::open("/nexus-seg")?;
/// let mut buf = [0u8; 5];
/// peer.read_at(&mut buf, 0);
/// assert_eq!(&buf, b"hello");
///
/// drop(shm);
/// drop(peer);
/// SharedMemory::unlink("/nexus-seg")?;
/// # Ok::<_, nexus_platform::MapError>(())
/// ```
pub struct SharedMemory {
    mapping: Mapping,
    name: CString,
    unlink_on_drop: bool,
}

impl SharedMemory {
    /// Returns an options builder for configuring and creating a mapping.
    ///
    /// See [`SharedMemoryOptions`] for available settings and examples.
    pub fn options() -> SharedMemoryOptions {
        SharedMemoryOptions::new()
    }

    /// Create or open a named shared memory object with default settings
    /// (read-write, shared, no unlink on drop).
    ///
    /// Convenience for `SharedMemory::options().create(name, len)`.
    pub fn create(name: &str, len: NonZeroUsize) -> Result<Self, MapError> {
        Self::options().create(name, len)
    }

    /// Open an existing named shared memory object with default settings
    /// (read-write, shared).
    ///
    /// Convenience for `SharedMemory::options().open(name)`.
    pub fn open(name: &str) -> Result<Self, MapError> {
        Self::options().open(name)
    }

    /// Open an existing named shared memory object as read-only, private.
    ///
    /// Convenience for
    /// `SharedMemory::options().read_only().private().open(name)`.
    pub fn open_readonly(name: &str) -> Result<Self, MapError> {
        Self::options().read_only().private().open(name)
    }

    /// Remove a named shared memory object from the namespace.
    ///
    /// Existing mappings remain valid until dropped — `shm_unlink` only
    /// removes the name. Returns an error if the name does not exist.
    pub fn unlink(name: &str) -> Result<(), MapError> {
        let cname = validate_name(name)?;
        mapping::shm_unlink(&cname)
    }

    /// The POSIX name of this shared memory object (e.g. `"/nexus-seg"`).
    pub fn name(&self) -> &str {
        self.name.to_str().expect("shm name is valid utf-8")
    }

    /// Access the underlying [`Mapping`].
    pub fn mapping(&self) -> &Mapping {
        &self.mapping
    }
}

impl From<SharedMemory> for Mapping {
    fn from(shm: SharedMemory) -> Mapping {
        let mut shm = std::mem::ManuallyDrop::new(shm);
        // SAFETY: ManuallyDrop prevents SharedMemory's Drop (which may call
        // shm_unlink). We transfer ownership of the inner Mapping — its own
        // Drop (munmap) will still run. We explicitly drop the CString name
        // to avoid leaking it.
        unsafe {
            let mapping = std::ptr::read(&raw const shm.mapping);
            std::ptr::drop_in_place(&raw mut shm.name);
            mapping
        }
    }
}

impl std::ops::Deref for SharedMemory {
    type Target = Mapping;

    fn deref(&self) -> &Mapping {
        &self.mapping
    }
}

impl Drop for SharedMemory {
    fn drop(&mut self) {
        if self.unlink_on_drop {
            let _ = mapping::shm_unlink(&self.name);
        }
    }
}

// ── Name validation ───────────────────────────────────────────────

fn validate_name(name: &str) -> Result<CString, MapError> {
    if name.is_empty() || name == "/" {
        return Err(MapError::Io(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "shared memory name cannot be empty",
        )));
    }

    let normalized = if name.starts_with('/') {
        name.to_string()
    } else {
        format!("/{name}")
    };

    if normalized[1..].contains('/') {
        return Err(MapError::Io(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "shared memory name must not contain '/' after the leading slash",
        )));
    }

    CString::new(normalized).map_err(|_| {
        MapError::Io(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "shared memory name contains null byte",
        ))
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn shm_name(suffix: &str) -> String {
        format!("/nexus-test-{}-{}", std::process::id(), suffix)
    }

    #[test]
    fn create_and_read_write() {
        let name = shm_name("rw");
        let _ = SharedMemory::unlink(&name);

        let shm = SharedMemory::create(&name, NonZeroUsize::new(4096).unwrap()).unwrap();
        assert_eq!(shm.len(), 4096);
        assert!(shm.is_writable());

        shm.write_at(&[0xDE, 0xAD, 0xBE, 0xEF], 0).unwrap();
        let mut buf = [0u8; 4];
        assert_eq!(shm.read_at(&mut buf, 0), 4);
        assert_eq!(buf, [0xDE, 0xAD, 0xBE, 0xEF]);

        drop(shm);
        SharedMemory::unlink(&name).unwrap();
    }

    #[test]
    fn open_existing() {
        let name = shm_name("open");
        let _ = SharedMemory::unlink(&name);

        let shm = SharedMemory::create(&name, NonZeroUsize::new(256).unwrap()).unwrap();
        shm.write_at(b"hello", 10).unwrap();
        drop(shm);

        let shm2 = SharedMemory::open(&name).unwrap();
        let mut buf = [0u8; 5];
        shm2.read_at(&mut buf, 10);
        assert_eq!(&buf, b"hello");

        drop(shm2);
        SharedMemory::unlink(&name).unwrap();
    }

    #[test]
    fn open_readonly() {
        let name = shm_name("readonly");
        let _ = SharedMemory::unlink(&name);

        let shm = SharedMemory::create(&name, NonZeroUsize::new(128).unwrap()).unwrap();
        shm.write_at(b"data", 0).unwrap();
        drop(shm);

        let shm2 = SharedMemory::open_readonly(&name).unwrap();
        assert!(!shm2.is_writable());
        assert_eq!(&shm2.as_slice()[..4], b"data");

        drop(shm2);
        SharedMemory::unlink(&name).unwrap();
    }

    #[test]
    fn two_mappings_share_data() {
        let name = shm_name("shared");
        let _ = SharedMemory::unlink(&name);

        let shm1 = SharedMemory::create(&name, NonZeroUsize::new(4096).unwrap()).unwrap();
        let shm2 = SharedMemory::open(&name).unwrap();

        shm1.write_at(b"visible", 0).unwrap();
        let mut buf = [0u8; 7];
        shm2.read_at(&mut buf, 0);
        assert_eq!(&buf, b"visible");

        drop(shm1);
        drop(shm2);
        SharedMemory::unlink(&name).unwrap();
    }

    #[test]
    fn unlink_on_drop_removes_name() {
        let name = shm_name("unlink-drop");
        let _ = SharedMemory::unlink(&name);

        let shm = SharedMemory::options()
            .unlink_on_drop(true)
            .create(&name, NonZeroUsize::new(64).unwrap())
            .unwrap();
        drop(shm);

        assert!(SharedMemory::open(&name).is_err());
    }

    #[test]
    fn unlink_static_removes_name() {
        let name = shm_name("unlink-static");
        let _ = SharedMemory::unlink(&name);

        let shm = SharedMemory::create(&name, NonZeroUsize::new(64).unwrap()).unwrap();
        SharedMemory::unlink(&name).unwrap();

        // Mapping is still valid after unlink — only the name is gone.
        assert!(shm.is_writable());
        assert!(SharedMemory::open(&name).is_err());

        drop(shm);
    }

    #[test]
    fn open_nonexistent_fails() {
        let name = shm_name("nonexistent");
        let _ = SharedMemory::unlink(&name);
        assert!(SharedMemory::open(&name).is_err());
    }

    #[test]
    fn name_normalization() {
        let name = shm_name("normalize");
        let bare = name.trim_start_matches('/');
        let _ = SharedMemory::unlink(&name);

        let shm = SharedMemory::create(bare, NonZeroUsize::new(64).unwrap()).unwrap();
        assert_eq!(shm.name(), name);

        drop(shm);
        SharedMemory::unlink(&name).unwrap();
    }

    #[test]
    fn empty_name_rejected() {
        assert!(SharedMemory::create("", NonZeroUsize::new(64).unwrap()).is_err());
    }

    #[test]
    fn bare_slash_rejected() {
        assert!(SharedMemory::create("/", NonZeroUsize::new(64).unwrap()).is_err());
    }

    #[test]
    fn embedded_slash_rejected() {
        assert!(SharedMemory::create("foo/bar", NonZeroUsize::new(64).unwrap()).is_err());
    }

    #[test]
    fn write_readonly_returns_error() {
        let name = shm_name("write-ro");
        let _ = SharedMemory::unlink(&name);

        let shm = SharedMemory::create(&name, NonZeroUsize::new(128).unwrap()).unwrap();
        drop(shm);

        let shm2 = SharedMemory::open_readonly(&name).unwrap();
        let err = shm2.write_at(b"nope", 0).unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::PermissionDenied);

        drop(shm2);
        SharedMemory::unlink(&name).unwrap();
    }

    #[test]
    fn create_extends_existing() {
        let name = shm_name("extend");
        let _ = SharedMemory::unlink(&name);

        let shm = SharedMemory::create(&name, NonZeroUsize::new(64).unwrap()).unwrap();
        assert_eq!(shm.len(), 64);
        drop(shm);

        let shm = SharedMemory::create(&name, NonZeroUsize::new(256).unwrap()).unwrap();
        assert_eq!(shm.len(), 256);

        drop(shm);
        SharedMemory::unlink(&name).unwrap();
    }

    #[test]
    fn create_does_not_truncate() {
        let name = shm_name("no-truncate");
        let _ = SharedMemory::unlink(&name);

        let shm = SharedMemory::create(&name, NonZeroUsize::new(256).unwrap()).unwrap();
        shm.write_at(b"preserve", 200).unwrap();
        drop(shm);

        // Smaller request — backing store should not shrink.
        let shm = SharedMemory::create(&name, NonZeroUsize::new(64).unwrap()).unwrap();
        assert_eq!(shm.len(), 64);
        drop(shm);

        // Re-open at full size — data should still be intact.
        let shm = SharedMemory::create(&name, NonZeroUsize::new(256).unwrap()).unwrap();
        let mut buf = [0u8; 8];
        shm.read_at(&mut buf, 200);
        assert_eq!(&buf, b"preserve");

        drop(shm);
        SharedMemory::unlink(&name).unwrap();
    }

    #[test]
    fn builder_pretouch() {
        let name = shm_name("pretouch");
        let _ = SharedMemory::unlink(&name);

        let shm = SharedMemory::options()
            .pretouch(true)
            .create(&name, NonZeroUsize::new(4096).unwrap())
            .unwrap();
        assert_eq!(shm.len(), 4096);
        assert!(shm.is_writable());

        drop(shm);
        SharedMemory::unlink(&name).unwrap();
    }
}
