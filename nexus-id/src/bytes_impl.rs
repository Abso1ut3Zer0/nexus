//! Integration with the `bytes` crate.
//!
//! Provides `put_to` methods for writing binary representations directly
//! into a `BufMut` without intermediate stack allocation.

use bytes::BufMut;

use crate::snowflake_id::{SnowflakeId32, SnowflakeId64};
use crate::types::{Ulid, Uuid, UuidCompact};

// =============================================================================
// 128-bit types — write 16 bytes big-endian
// =============================================================================

impl Uuid {
    /// Write the 16-byte big-endian binary representation into a buffer.
    ///
    /// Equivalent to `buf.put_slice(&self.to_be_bytes())` but avoids the
    /// intermediate `[u8; 16]` stack allocation.
    #[inline]
    pub fn put_to<B: BufMut>(&self, buf: &mut B) {
        let (hi, lo) = self.to_raw();
        buf.put_u64(hi);
        buf.put_u64(lo);
    }
}

impl UuidCompact {
    /// Write the 16-byte big-endian binary representation into a buffer.
    #[inline]
    pub fn put_to<B: BufMut>(&self, buf: &mut B) {
        let (hi, lo) = self.to_raw();
        buf.put_u64(hi);
        buf.put_u64(lo);
    }
}

impl Ulid {
    /// Write the 16-byte big-endian binary representation into a buffer.
    ///
    /// Layout: `[timestamp: 6 bytes][rand_hi: 2 bytes][rand_lo: 8 bytes]`
    #[inline]
    pub fn put_to<B: BufMut>(&self, buf: &mut B) {
        let ts = self.timestamp_millis();
        let (rand_hi, rand_lo) = self.random();
        // Timestamp: 48 bits (6 bytes), big-endian
        let ts_bytes = ts.to_be_bytes();
        buf.put_slice(&ts_bytes[2..8]);
        buf.put_u16(rand_hi);
        buf.put_u64(rand_lo);
    }
}

// =============================================================================
// Snowflake types — write native integer
// =============================================================================

impl<const TS: u8, const WK: u8, const SQ: u8> SnowflakeId64<TS, WK, SQ> {
    /// Write the raw u64 as 8 bytes big-endian into a buffer.
    #[inline]
    pub fn put_to<B: BufMut>(&self, buf: &mut B) {
        buf.put_u64(self.0);
    }
}

impl<const TS: u8, const WK: u8, const SQ: u8> SnowflakeId32<TS, WK, SQ> {
    /// Write the raw u32 as 4 bytes big-endian into a buffer.
    #[inline]
    pub fn put_to<B: BufMut>(&self, buf: &mut B) {
        buf.put_u32(self.0);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bytes::BytesMut;

    #[test]
    fn uuid_put_to_matches_to_bytes() {
        let uuid = Uuid::from_raw(0x0123_4567_89AB_CDEF, 0xFEDC_BA98_7654_3210);

        let mut buf = BytesMut::with_capacity(16);
        uuid.put_to(&mut buf);

        assert_eq!(&buf[..], &uuid.to_be_bytes());
    }

    #[test]
    fn uuid_compact_put_to_matches_to_bytes() {
        let uuid = UuidCompact::from_raw(0xDEAD_BEEF_CAFE_BABE, 0x0123_4567_89AB_CDEF);

        let mut buf = BytesMut::with_capacity(16);
        uuid.put_to(&mut buf);

        assert_eq!(&buf[..], &uuid.to_be_bytes());
    }

    #[test]
    fn ulid_put_to_matches_to_bytes() {
        let ulid = Ulid::from_raw(1_700_000_000_000, 0x1234, 0xDEAD_BEEF_CAFE_BABE);

        let mut buf = BytesMut::with_capacity(16);
        ulid.put_to(&mut buf);

        assert_eq!(&buf[..], &ulid.to_be_bytes());
    }

    #[test]
    fn snowflake64_put_to() {
        let id = SnowflakeId64::<42, 6, 16>::from_raw(0xDEAD_BEEF_CAFE_BABE);

        let mut buf = BytesMut::with_capacity(8);
        id.put_to(&mut buf);

        assert_eq!(&buf[..], &0xDEAD_BEEF_CAFE_BABEu64.to_be_bytes());
    }

    #[test]
    fn snowflake32_put_to() {
        let id = SnowflakeId32::<20, 4, 8>::from_raw(0xDEAD_BEEF);

        let mut buf = BytesMut::with_capacity(4);
        id.put_to(&mut buf);

        assert_eq!(&buf[..], &0xDEAD_BEEFu32.to_be_bytes());
    }
}
