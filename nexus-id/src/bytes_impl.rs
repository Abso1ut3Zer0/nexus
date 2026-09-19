//! Integration with the `bytes` crate.
//!
//! Provides `put_to_be` / `put_to_le` methods for writing binary
//! representations directly into a `BufMut` without an intermediate stack
//! allocation. Big-endian is the canonical form for the 128-bit ID types
//! (see [`Uuid::to_be_bytes`](crate::Uuid::to_be_bytes)); little-endian is
//! provided for little-endian wire protocols such as SBE (e.g. CME MDP).

use bytes::BufMut;

use crate::snowflake_id::{SnowflakeId32, SnowflakeId64};
use crate::types::{Ulid, Uuid, UuidCompact};

// =============================================================================
// 128-bit types — write 16 bytes
// =============================================================================

impl Uuid {
    /// Write the **canonical** 16-byte big-endian representation into a buffer.
    ///
    /// Big-endian is RFC 9562 network byte order — the form databases (e.g.
    /// Postgres `uuid`) and wire protocols expect. Equivalent to
    /// `buf.put_slice(&self.to_be_bytes())` but avoids the intermediate
    /// `[u8; 16]` stack allocation.
    #[inline]
    pub fn put_to_be<B: BufMut>(&self, buf: &mut B) {
        let (hi, lo) = self.to_raw();
        buf.put_u64(hi);
        buf.put_u64(lo);
    }

    /// Write the 16-byte little-endian representation into a buffer.
    ///
    /// This is **not** the canonical UUID byte order (see
    /// [`put_to_be`](Self::put_to_be)); it produces exactly
    /// [`to_le_bytes()`](Self::to_le_bytes). Use it for little-endian wire
    /// protocols such as SBE (e.g. CME MDP) and custom little-endian binary
    /// formats.
    #[inline]
    pub fn put_to_le<B: BufMut>(&self, buf: &mut B) {
        let (hi, lo) = self.to_raw();
        buf.put_u64_le(lo);
        buf.put_u64_le(hi);
    }
}

impl UuidCompact {
    /// Write the **canonical** 16-byte big-endian representation into a buffer.
    ///
    /// Big-endian is RFC 9562 network byte order — the form databases (e.g.
    /// Postgres `uuid`) and wire protocols expect.
    #[inline]
    pub fn put_to_be<B: BufMut>(&self, buf: &mut B) {
        let (hi, lo) = self.to_raw();
        buf.put_u64(hi);
        buf.put_u64(lo);
    }

    /// Write the 16-byte little-endian representation into a buffer.
    ///
    /// This is **not** the canonical UUID byte order (see
    /// [`put_to_be`](Self::put_to_be)); it produces exactly
    /// [`to_le_bytes()`](Self::to_le_bytes). Use it for little-endian wire
    /// protocols such as SBE (e.g. CME MDP) and custom little-endian binary
    /// formats.
    #[inline]
    pub fn put_to_le<B: BufMut>(&self, buf: &mut B) {
        let (hi, lo) = self.to_raw();
        buf.put_u64_le(lo);
        buf.put_u64_le(hi);
    }
}

impl Ulid {
    /// Write the **canonical** 16-byte big-endian representation into a buffer.
    ///
    /// Layout: `[timestamp: 6 bytes][rand_hi: 2 bytes][rand_lo: 8 bytes]`.
    /// Big-endian (MSB-first) is the canonical ULID binary form per the spec:
    /// byte-wise ordering equals numeric (and therefore time) ordering.
    #[inline]
    pub fn put_to_be<B: BufMut>(&self, buf: &mut B) {
        let ts = self.timestamp_millis();
        let (rand_hi, rand_lo) = self.random();
        // Timestamp: 48 bits (6 bytes), big-endian
        let ts_bytes = ts.to_be_bytes();
        buf.put_slice(&ts_bytes[2..8]);
        buf.put_u16(rand_hi);
        buf.put_u64(rand_lo);
    }

    /// Write the 16-byte little-endian representation into a buffer.
    ///
    /// This is **not** the canonical ULID byte order (see
    /// [`put_to_be`](Self::put_to_be)) and does **not** preserve the byte-wise
    /// sort property; it produces exactly [`to_le_bytes()`](Self::to_le_bytes)
    /// (the byte-reverse of the big-endian form). Use it for little-endian wire
    /// protocols such as SBE (e.g. CME MDP) and custom little-endian binary
    /// formats.
    #[inline]
    pub fn put_to_le<B: BufMut>(&self, buf: &mut B) {
        let ts = self.timestamp_millis();
        let (rand_hi, rand_lo) = self.random();
        // Byte-reverse of the big-endian layout:
        // [rand_lo LE (8)][rand_hi LE (2)][timestamp low-6 LE].
        buf.put_u64_le(rand_lo);
        buf.put_u16_le(rand_hi);
        let ts_bytes = ts.to_le_bytes();
        buf.put_slice(&ts_bytes[0..6]);
    }
}

// =============================================================================
// Snowflake types — write native integer
// =============================================================================

impl<const TS: u8, const WK: u8, const SQ: u8> SnowflakeId64<TS, WK, SQ> {
    /// Write the raw u64 as 8 bytes big-endian into a buffer.
    ///
    /// A Snowflake has no spec-defined byte order, but big-endian is the
    /// sensible default: it preserves lexicographic == numeric (time) ordering
    /// for these sortable IDs, which matters for database keys and sorted logs.
    #[inline]
    pub fn put_to_be<B: BufMut>(&self, buf: &mut B) {
        buf.put_u64(self.0);
    }

    /// Write the raw u64 as 8 bytes little-endian into a buffer.
    ///
    /// Little-endian serialization for SBE (e.g. CME MDP) and custom
    /// little-endian binary formats.
    #[inline]
    pub fn put_to_le<B: BufMut>(&self, buf: &mut B) {
        buf.put_u64_le(self.0);
    }
}

impl<const TS: u8, const WK: u8, const SQ: u8> SnowflakeId32<TS, WK, SQ> {
    /// Write the raw u32 as 4 bytes big-endian into a buffer.
    ///
    /// A Snowflake has no spec-defined byte order, but big-endian is the
    /// sensible default: it preserves lexicographic == numeric (time) ordering
    /// for these sortable IDs, which matters for database keys and sorted logs.
    #[inline]
    pub fn put_to_be<B: BufMut>(&self, buf: &mut B) {
        buf.put_u32(self.0);
    }

    /// Write the raw u32 as 4 bytes little-endian into a buffer.
    ///
    /// Little-endian serialization for SBE (e.g. CME MDP) and custom
    /// little-endian binary formats.
    #[inline]
    pub fn put_to_le<B: BufMut>(&self, buf: &mut B) {
        buf.put_u32_le(self.0);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bytes::BytesMut;

    #[test]
    fn uuid_put_to_matches_to_bytes() {
        let uuid = Uuid::from_raw(0x0123_4567_89AB_CDEF, 0xFEDC_BA98_7654_3210);

        let mut be = BytesMut::with_capacity(16);
        uuid.put_to_be(&mut be);
        assert_eq!(&be[..], &uuid.to_be_bytes());

        let mut le = BytesMut::with_capacity(16);
        uuid.put_to_le(&mut le);
        assert_eq!(&le[..], &uuid.to_le_bytes());
    }

    #[test]
    fn uuid_compact_put_to_matches_to_bytes() {
        let uuid = UuidCompact::from_raw(0xDEAD_BEEF_CAFE_BABE, 0x0123_4567_89AB_CDEF);

        let mut be = BytesMut::with_capacity(16);
        uuid.put_to_be(&mut be);
        assert_eq!(&be[..], &uuid.to_be_bytes());

        let mut le = BytesMut::with_capacity(16);
        uuid.put_to_le(&mut le);
        assert_eq!(&le[..], &uuid.to_le_bytes());
    }

    #[test]
    fn ulid_put_to_matches_to_bytes() {
        let ulid = Ulid::from_raw(1_700_000_000_000, 0x1234, 0xDEAD_BEEF_CAFE_BABE);

        let mut be = BytesMut::with_capacity(16);
        ulid.put_to_be(&mut be);
        assert_eq!(&be[..], &ulid.to_be_bytes());

        let mut le = BytesMut::with_capacity(16);
        ulid.put_to_le(&mut le);
        assert_eq!(&le[..], &ulid.to_le_bytes());
    }

    #[test]
    fn snowflake64_put_to() {
        let id = SnowflakeId64::<42, 6, 16>::from_raw(0xDEAD_BEEF_CAFE_BABE);

        let mut be = BytesMut::with_capacity(8);
        id.put_to_be(&mut be);
        assert_eq!(&be[..], &0xDEAD_BEEF_CAFE_BABEu64.to_be_bytes());

        let mut le = BytesMut::with_capacity(8);
        id.put_to_le(&mut le);
        assert_eq!(&le[..], &0xDEAD_BEEF_CAFE_BABEu64.to_le_bytes());
    }

    #[test]
    fn snowflake32_put_to() {
        let id = SnowflakeId32::<20, 4, 8>::from_raw(0xDEAD_BEEF);

        let mut be = BytesMut::with_capacity(4);
        id.put_to_be(&mut be);
        assert_eq!(&be[..], &0xDEAD_BEEFu32.to_be_bytes());

        let mut le = BytesMut::with_capacity(4);
        id.put_to_le(&mut le);
        assert_eq!(&le[..], &0xDEAD_BEEFu32.to_le_bytes());
    }
}
