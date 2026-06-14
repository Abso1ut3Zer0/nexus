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

use nexus_platform::{MapError, MapHints, MappedFile, Mapping};

pub use error::AppendOnlyJournalError;
pub use header::{FixHeader, RecordHeader, SeqHeader};
pub use reader::{ReadRange, ReadRecord, Reader};
pub use writer::{WriteClaim, Writer};

use frame::{FRAME_HEADER, TYPE_PAD, align_up, footprint, frame_kind, read_commit_len};

const MIN_SEGMENT: usize = 64;

/// Configuration for opening an append-only journal.
#[derive(Clone, Copy)]
pub struct AppendOnlyJournalConfig {
    pub segment_size: usize,
    pub hints: MapHints,
}

impl Default for AppendOnlyJournalConfig {
    fn default() -> Self {
        Self {
            segment_size: 64 * 1024 * 1024,
            hints: MapHints::default(),
        }
    }
}

/// Entry point for opening an append-only journal over `{base}.{index}` segment files.
pub struct AppendOnlyJournal<H>(PhantomData<H>);

impl<H: RecordHeader> AppendOnlyJournal<H> {
    /// Open (or recover) a journal, returning its [`Writer`] and [`Reader`].
    pub fn open(
        base: impl AsRef<Path>,
        cfg: AppendOnlyJournalConfig,
    ) -> Result<(Writer<H>, Reader<H>), AppendOnlyJournalError> {
        let base = base.as_ref().to_path_buf();
        let segment_size = align_up(cfg.segment_size.max(MIN_SEGMENT));
        let total = NonZeroUsize::new(segment_size).expect("segment_size >= MIN_SEGMENT");

        let mut last = None;
        let mut i = 0u64;
        while segment_path(&base, i).exists() {
            last = Some(i);
            i += 1;
        }

        let index = last.unwrap_or(0);
        let active: Mapping = file_create(&segment_path(&base, index), total, cfg.hints)?.into();
        let tail = recover_tail::<H>(active.as_ptr(), segment_size);

        let writer = Writer {
            base: base.clone(),
            segment_size,
            hints: cfg.hints,
            active,
            index,
            tail,
            _marker: PhantomData,
        };

        let seg0: Mapping = file_open(&segment_path(&base, 0), cfg.hints)?.into();
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

fn recover_tail<H: RecordHeader>(base: *mut u8, segment_size: usize) -> usize {
    let hsize = size_of::<H>();
    let mut cur = 0;
    while cur + FRAME_HEADER <= segment_size {
        // SAFETY: `cur` is an 8-aligned offset within the mapped data region.
        let cl = unsafe { read_commit_len(base, cur) };
        if cl == 0 {
            break;
        }
        // SAFETY: cl > 0 means the frame header is written.
        if unsafe { frame_kind(base, cur) } == TYPE_PAD {
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
