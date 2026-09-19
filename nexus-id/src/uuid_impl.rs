//! Integration with the `uuid` crate.
//!
//! Provides `From` conversions between `nexus_id` UUID types and `uuid::Uuid`.

use crate::types::{Uuid, UuidCompact};

// =============================================================================
// Uuid <-> uuid::Uuid
// =============================================================================

impl From<uuid::Uuid> for Uuid {
    #[inline]
    fn from(u: uuid::Uuid) -> Self {
        let bytes = u.as_bytes();
        let hi = u64::from_be_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ]);
        let lo = u64::from_be_bytes([
            bytes[8], bytes[9], bytes[10], bytes[11], bytes[12], bytes[13], bytes[14], bytes[15],
        ]);
        Self::from_raw(hi, lo)
    }
}

impl From<Uuid> for uuid::Uuid {
    #[inline]
    fn from(u: Uuid) -> Self {
        uuid::Uuid::from_bytes(u.to_be_bytes())
    }
}

// =============================================================================
// UuidCompact <-> uuid::Uuid
// =============================================================================

impl From<uuid::Uuid> for UuidCompact {
    #[inline]
    fn from(u: uuid::Uuid) -> Self {
        let bytes = u.as_bytes();
        let hi = u64::from_be_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ]);
        let lo = u64::from_be_bytes([
            bytes[8], bytes[9], bytes[10], bytes[11], bytes[12], bytes[13], bytes[14], bytes[15],
        ]);
        Self::from_raw(hi, lo)
    }
}

impl From<UuidCompact> for uuid::Uuid {
    #[inline]
    fn from(u: UuidCompact) -> Self {
        uuid::Uuid::from_bytes(u.to_be_bytes())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn uuid_roundtrip() {
        let original = uuid::Uuid::from_bytes([
            0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54,
            0x32, 0x10,
        ]);

        let nexus: Uuid = original.into();
        let back: uuid::Uuid = nexus.into();
        assert_eq!(original, back);
    }

    #[test]
    fn uuid_compact_roundtrip() {
        let original = uuid::Uuid::from_bytes([
            0xde, 0xad, 0xbe, 0xef, 0xca, 0xfe, 0xba, 0xbe, 0x01, 0x23, 0x45, 0x67, 0x89, 0xab,
            0xcd, 0xef,
        ]);

        let nexus: UuidCompact = original.into();
        let back: uuid::Uuid = nexus.into();
        assert_eq!(original, back);
    }

    #[test]
    fn uuid_string_matches() {
        let original = uuid::Uuid::from_bytes([
            0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0x4d, 0xef, 0x8e, 0xdc, 0xba, 0x98, 0x76, 0x54,
            0x32, 0x10,
        ]);

        let nexus: Uuid = original.into();
        assert_eq!(nexus.as_str(), original.to_string());
    }
}
