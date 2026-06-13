use std::marker::PhantomData;
use std::num::NonZeroUsize;

use nexus_platform::Mapping;

use super::error::AppendOnlyJournalError;
use super::frame::{
    FRAME_HEADER, TYPE_DATA, TYPE_PAD, footprint, write_commit_len, write_frame_kind, write_val,
};
use super::header::RecordHeader;

/// Append half of a journal: claims and commits records to the active segment.
pub struct Writer<H: RecordHeader> {
    pub(super) base: std::path::PathBuf,
    pub(super) segment_size: usize,
    pub(super) hints: nexus_platform::MapHints,
    pub(super) active: Mapping,
    pub(super) index: u64,
    pub(super) tail: usize,
    pub(super) _marker: PhantomData<H>,
}

impl<H: RecordHeader> Writer<H> {
    /// Reserve space for a record carrying `header` and `payload_len` bytes,
    /// rolling to a new segment if it does not fit the current one.
    pub fn try_claim(
        &mut self,
        header: H,
        payload_len: usize,
    ) -> Result<WriteClaim<'_, H>, AppendOnlyJournalError> {
        let body = size_of::<H>() + payload_len;
        if body == 0 {
            return Err(AppendOnlyJournalError::EmptyRecord);
        }
        let foot = footprint(body);
        if body > u32::MAX as usize || foot > self.segment_size {
            return Err(AppendOnlyJournalError::RecordTooLarge {
                frame: foot,
                capacity: self.segment_size,
            });
        }
        if self.tail + foot > self.segment_size {
            self.roll()?;
        }
        Ok(WriteClaim {
            off: self.tail,
            body,
            foot,
            header,
            payload_len,
            writer: self,
        })
    }

    fn roll(&mut self) -> Result<(), AppendOnlyJournalError> {
        let remaining = self.segment_size - self.tail;
        if remaining >= FRAME_HEADER {
            let base = self.active.as_ptr();
            // SAFETY: tail is an 8-aligned offset within the mapped data region.
            unsafe {
                write_frame_kind(base, self.tail, TYPE_PAD);
                write_commit_len(base, self.tail, remaining as u32);
            }
        }
        self.index += 1;
        let path = super::segment_path(&self.base, self.index);
        let total = NonZeroUsize::new(self.segment_size).expect("non-zero segment size");
        self.active = super::file_create(&path, total, self.hints)?.into();
        self.tail = 0;
        Ok(())
    }
}

/// A reserved, not-yet-published record. Fill the payload, then [`commit`].
///
/// [`commit`]: WriteClaim::commit
pub struct WriteClaim<'a, H: RecordHeader> {
    writer: &'a mut Writer<H>,
    off: usize,
    body: usize,
    foot: usize,
    header: H,
    payload_len: usize,
}

impl<H: RecordHeader> WriteClaim<'_, H> {
    /// The payload region to fill before committing.
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        let start = self.off + FRAME_HEADER + size_of::<H>();
        let base = self.writer.active.as_ptr();
        // SAFETY: the region is reserved for this claim, lies within the mapped
        // data, and is exclusively borrowed through `&mut self`.
        unsafe { std::slice::from_raw_parts_mut(base.add(start), self.payload_len) }
    }

    /// Publish the record and return its on-disk position.
    ///
    /// Writes the header and frame kind, then the commit length so readers
    /// observe a fully-written record. The returned [`AppendOffset`] can be
    /// stored in an index for O(1) resend lookup via [`Reader::read_from`].
    pub fn commit(self) -> super::AppendOffset {
        let at = super::AppendOffset {
            segment: self.writer.index,
            offset: self.off,
        };
        let base = self.writer.active.as_ptr();
        // SAFETY: the header slot is reserved for this claim and within the
        // mapped data; `H: Pod`, so an unaligned byte write is valid.
        unsafe {
            write_val(base, self.off + FRAME_HEADER, self.header);
            write_frame_kind(base, self.off, TYPE_DATA);
        }

        let next = self.off + self.foot;
        if next + FRAME_HEADER <= self.writer.segment_size {
            // SAFETY: `next` is an 8-aligned offset within the mapped data.
            unsafe { write_commit_len(base, next, 0) };
        }

        // SAFETY: the commit-length slot is 8-aligned and within the mapped data.
        unsafe { write_commit_len(base, self.off, self.body as u32) };
        self.writer.tail = next;
        at
    }
}
