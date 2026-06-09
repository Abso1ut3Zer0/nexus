use std::marker::PhantomData;
use std::sync::atomic::Ordering;

use crate::segment::Segment;

use super::error::JournalError;
use super::frame::{FRAME_HEADER, TYPE_DATA, TYPE_PAD, footprint};
use super::header::RecordHeader;

/// Append half of a journal: claims and commits records to the active segment.
pub struct Writer<H: RecordHeader> {
    pub(super) base: std::path::PathBuf,
    pub(super) segment_size: usize,
    pub(super) hints: crate::MapHints,
    pub(super) active: Segment,
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
    ) -> Result<WriteClaim<'_, H>, JournalError> {
        let body = size_of::<H>() + payload_len;
        if body == 0 {
            return Err(JournalError::EmptyRecord);
        }
        let foot = footprint(body);
        if body > u32::MAX as usize || foot > self.segment_size {
            return Err(JournalError::RecordTooLarge {
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

    fn roll(&mut self) -> Result<(), JournalError> {
        let remaining = self.segment_size - self.tail;
        if remaining >= FRAME_HEADER {
            // SAFETY: tail is an 8-aligned offset within the mapped data region.
            unsafe {
                self.active.write_frame_kind_at(self.tail, TYPE_PAD);
                self.active
                    .commit_len_at(self.tail)
                    .store(remaining as u32, Ordering::Release);
            }
        }
        self.index += 1;
        let path = super::segment_path(&self.base, self.index);
        self.active = Segment::create(&path, self.segment_size, self.hints)?;
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
        // SAFETY: the region is reserved for this claim, lies within the mapped
        // data, and is exclusively borrowed through `&mut self`.
        unsafe { self.writer.active.slice_mut_at(start, self.payload_len) }
    }

    /// Publish the record: write the header and frame kind, then release the
    /// commit length so readers observe a fully-written record.
    pub fn commit(self) {
        // SAFETY: the header slot is reserved for this claim and within the
        // mapped data; `H: Pod`, so an unaligned byte write is valid.
        unsafe {
            self.writer
                .active
                .write_at(self.off + FRAME_HEADER, self.header);
            self.writer.active.write_frame_kind_at(self.off, TYPE_DATA);
        }

        let next = self.off + self.foot;
        if next + FRAME_HEADER <= self.writer.segment_size {
            // SAFETY: `next` is an 8-aligned offset within the mapped data.
            unsafe {
                self.writer
                    .active
                    .commit_len_at(next)
                    .store(0, Ordering::Relaxed);
            }
        }

        // SAFETY: the commit-length slot is 8-aligned and within the mapped data.
        unsafe {
            self.writer
                .active
                .commit_len_at(self.off)
                .store(self.body as u32, Ordering::Release);
        }
        self.writer.tail = next;
    }
}
