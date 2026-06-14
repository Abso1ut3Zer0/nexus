use core::sync::atomic::{AtomicU32, AtomicU64, Ordering};
use crossbeam_utils::CachePadded;

use crate::error::ShmError;

pub(crate) const MAGIC: u32 = u32::from_le_bytes(*b"NXSM");
pub(crate) const LAYOUT_VERSION: u16 = 1;

pub(crate) mod status {
    #[cfg(test)]
    pub(crate) const UNINIT: u32 = 0;
    pub(crate) const ALIVE: u32 = 1;
    pub(crate) const DEAD: u32 = 2;
}

#[repr(C)]
pub(crate) struct ControlBlockInner {
    pub(crate) magic: u32,
    pub(crate) layout_ver: u16,
    pub(crate) flags: u16,
    pub(crate) generation: AtomicU64,
    pub(crate) status: AtomicU32,
    pub(crate) owner_pid: AtomicU32,
    pub(crate) data_len: u64,
}

const _: () = {
    assert!(size_of::<ControlBlockInner>() == 32);
    assert!(align_of::<ControlBlockInner>() == 8);
};

impl ControlBlockInner {
    #[cfg(test)]
    pub(crate) const fn zeroed() -> Self {
        Self {
            magic: 0,
            layout_ver: 0,
            flags: 0,
            generation: AtomicU64::new(0),
            status: AtomicU32::new(0),
            owner_pid: AtomicU32::new(0),
            data_len: 0,
        }
    }

    pub(crate) fn write_header(
        &mut self,
        flags: u16,
        generation: u64,
        owner_pid: u32,
        data_len: u64,
    ) {
        self.magic = MAGIC;
        self.layout_ver = LAYOUT_VERSION;
        self.flags = flags;
        self.data_len = data_len;
        *self.generation.get_mut() = generation;
        *self.owner_pid.get_mut() = owner_pid;
        self.status.store(status::ALIVE, Ordering::Release);
    }

    pub(crate) fn validate(&self) -> Result<(), ShmError> {
        if self.magic != MAGIC {
            return Err(ShmError::BadMagic { found: self.magic });
        }
        if self.layout_ver != LAYOUT_VERSION {
            return Err(ShmError::UnsupportedLayout {
                found: self.layout_ver,
                expected: LAYOUT_VERSION,
            });
        }
        Ok(())
    }

    pub(crate) fn status(&self) -> u32 {
        self.status.load(Ordering::Acquire)
    }

    pub(crate) fn mark_dead(&self) {
        self.status.store(status::DEAD, Ordering::Release);
    }

    pub(crate) fn generation(&self) -> u64 {
        self.generation.load(Ordering::Acquire)
    }

    pub(crate) fn owner_pid(&self) -> u32 {
        self.owner_pid.load(Ordering::Acquire)
    }

    pub(crate) const fn data_len(&self) -> u64 {
        self.data_len
    }
}

#[repr(transparent)]
pub(crate) struct ControlBlock(pub(crate) CachePadded<ControlBlockInner>);

impl core::ops::Deref for ControlBlock {
    type Target = ControlBlockInner;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl core::ops::DerefMut for ControlBlock {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

#[cfg(test)]
mod tests {
    use super::{ControlBlock, ControlBlockInner, LAYOUT_VERSION, MAGIC, status};
    use crossbeam_utils::CachePadded;

    fn fresh() -> ControlBlock {
        ControlBlock(CachePadded::new(ControlBlockInner::zeroed()))
    }

    #[test]
    fn control_block_is_cache_line_isolated() {
        let align = align_of::<ControlBlock>();
        assert!(align >= 64, "control block not cache-line aligned: {align}");
        assert_eq!(size_of::<ControlBlock>(), align);
    }

    #[test]
    fn write_then_validate_roundtrips() {
        let mut cb = fresh();
        assert_eq!(cb.status(), status::UNINIT);
        cb.write_header(0b10, 7, 4242, 1 << 20);
        cb.validate().unwrap();
        assert_eq!(cb.magic, MAGIC);
        assert_eq!(cb.layout_ver, LAYOUT_VERSION);
        assert_eq!(cb.flags, 0b10);
        assert_eq!(cb.generation(), 7);
        assert_eq!(cb.status(), status::ALIVE);
        assert_eq!(cb.data_len(), 1 << 20);
    }

    #[test]
    fn rejects_foreign_segment() {
        let cb = fresh();
        assert!(matches!(
            cb.validate(),
            Err(crate::ShmError::BadMagic { found: 0 })
        ));
    }

    #[test]
    fn liveness_transitions() {
        let mut cb = fresh();
        cb.write_header(0, 3, 1, 0);
        assert_eq!(cb.status(), status::ALIVE);
        assert_eq!(cb.generation(), 3);
        cb.mark_dead();
        assert_eq!(cb.status(), status::DEAD);
    }
}
