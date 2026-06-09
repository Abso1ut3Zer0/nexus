mod error;
mod frame;
mod header;
mod reader;
#[cfg(test)]
mod tests;
mod writer;

use std::marker::PhantomData;
use std::num::NonZeroUsize;
use std::path::{Path, PathBuf};
use std::sync::atomic::Ordering;

use nexus_platform::{MapError, MappedFile};

use crate::MapHints;
use crate::segment::Segment;

pub use error::JournalError;
pub use header::{FixHeader, RecordHeader, SeqHeader};
pub use reader::{ReadRange, ReadRecord, Reader};
pub use writer::{WriteClaim, Writer};

use frame::{FRAME_HEADER, TYPE_PAD, align_up, footprint};

const MIN_SEGMENT: usize = 64;

/// Configuration for opening a journal.
#[derive(Clone, Copy)]
pub struct JournalConfig {
    pub segment_size: usize,
    pub hints: MapHints,
}

impl Default for JournalConfig {
    fn default() -> Self {
        Self {
            segment_size: 64 * 1024 * 1024,
            hints: MapHints::default(),
        }
    }
}

/// Entry point for opening a journal over `{base}.{index}` segment files.
pub struct Journal<H>(PhantomData<H>);

impl<H: RecordHeader> Journal<H> {
    /// Open (or recover) a journal, returning its [`Writer`] and [`Reader`].
    pub fn open(
        base: impl AsRef<Path>,
        cfg: JournalConfig,
    ) -> Result<(Writer<H>, Reader<H>), JournalError> {
        let base = base.as_ref().to_path_buf();
        let segment_size = align_up(cfg.segment_size.max(MIN_SEGMENT));

        let mut last = None;
        let mut i = 0u64;
        while segment_path(&base, i).exists() {
            last = Some(i);
            i += 1;
        }

        let index = last.unwrap_or(0);
        let total = Segment::total_size(segment_size)?;
        let active = Segment::create(
            file_create(&segment_path(&base, index), total, cfg.hints)?,
            segment_size,
            cfg.hints,
        )?;
        let tail = recover_tail::<H>(&active, segment_size);

        let writer = Writer {
            base: base.clone(),
            segment_size,
            hints: cfg.hints,
            active,
            index,
            tail,
            _marker: PhantomData,
        };

        let seg0 = Segment::attach(file_open(&segment_path(&base, 0), cfg.hints)?)?;
        let reader = Reader {
            base,
            segment_size,
            hints: cfg.hints,
            segments: vec![seg0],
            seg_idx: 0,
            cursor: 0,
            _marker: PhantomData,
        };

        Ok((writer, reader))
    }
}

fn recover_tail<H: RecordHeader>(seg: &Segment, segment_size: usize) -> usize {
    let hsize = size_of::<H>();
    let mut cur = 0;
    while cur + FRAME_HEADER <= segment_size {
        // SAFETY: `cur` is an 8-aligned offset within the mapped data region.
        let cl = unsafe { seg.commit_len_at(cur) }.load(Ordering::Acquire);
        if cl == 0 {
            break;
        }
        // SAFETY: cl > 0 was Acquire-loaded, so the frame header is published.
        if unsafe { seg.frame_kind_at(cur) } == TYPE_PAD {
            cur += align_up(cl as usize);
            continue;
        }
        let body = cl as usize;
        if body < hsize || cur + footprint(body) > segment_size {
            break;
        }
        cur += footprint(body);
    }
    cur
}

fn segment_path(base: &Path, index: u64) -> PathBuf {
    let mut p = base.as_os_str().to_owned();
    p.push(format!(".{index}"));
    PathBuf::from(p)
}

pub(super) fn file_create(
    path: &Path,
    len: NonZeroUsize,
    hints: MapHints,
) -> Result<MappedFile, MapError> {
    let mut opts = MappedFile::options();
    opts.pretouch(hints.pretouch).huge_pages(hints.huge_pages);
    opts.create(path, len)
}

pub(super) fn file_open(path: &Path, hints: MapHints) -> Result<MappedFile, MapError> {
    let mut opts = MappedFile::options();
    opts.pretouch(hints.pretouch).huge_pages(hints.huge_pages);
    opts.open(path)
}
