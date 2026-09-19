//! Snowflake ID newtypes with field extraction and mixing.
//!
//! These types wrap raw integer values produced by snowflake generators,
//! providing methods for field extraction, hash-friendly mixing, and
//! string encoding.

use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};

use crate::types::{Base36Id, Base62Id, HexId64};

/// Fibonacci hashing constant (golden ratio * 2^64, truncated).
/// Bijective permutation for uniform hash distribution.
const GOLDEN_64: u64 = 0x9E37_79B9_7F4A_7C15;

/// Multiplicative inverse of GOLDEN_64 mod 2^64.
/// Satisfies: GOLDEN_64.wrapping_mul(GOLDEN_64_INV) == 1
const GOLDEN_64_INV: u64 = 0xF1DE_83E1_9937_733D;

/// Fibonacci hashing constant for 32-bit (golden ratio * 2^32, truncated).
const GOLDEN_32: u32 = 0x9E37_79B9;

/// Multiplicative inverse of GOLDEN_32 mod 2^32.
const GOLDEN_32_INV: u32 = 0x144C_BC89;

// =============================================================================
// SnowflakeId64
// =============================================================================

/// 64-bit Snowflake ID with compile-time layout.
///
/// Wraps a u64 containing packed `[timestamp: TS][worker: WK][sequence: SQ]` fields.
/// Provides extraction, mixing, and formatting methods.
///
/// # Type Parameters
/// - `TS`: Timestamp bits
/// - `WK`: Worker bits
/// - `SQ`: Sequence bits
///
/// # Example
///
/// ```rust
/// use nexus_id::{Snowflake64, SnowflakeId64};
///
/// let mut generator: Snowflake64<42, 6, 16> = Snowflake64::new(5);
/// let id: SnowflakeId64<42, 6, 16> = generator.next_id(0).unwrap();
/// assert_eq!(id.worker(), 5);
/// assert_eq!(id.sequence(), 0);
/// ```
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct SnowflakeId64<const TS: u8, const WK: u8, const SQ: u8>(pub(crate) u64);

impl<const TS: u8, const WK: u8, const SQ: u8> SnowflakeId64<TS, WK, SQ> {
    const TS_SHIFT: u8 = WK + SQ;
    const WK_SHIFT: u8 = SQ;
    const SEQUENCE_MASK: u64 = (1u64 << SQ) - 1;
    const WORKER_MASK: u64 = if WK == 0 { 0 } else { (1u64 << WK) - 1 };

    /// Create from a raw u64 value.
    #[inline]
    pub const fn from_raw(raw: u64) -> Self {
        Self(raw)
    }

    /// Raw u64 value.
    #[inline]
    pub const fn raw(&self) -> u64 {
        self.0
    }

    /// Extract the tick field (the generic ordering value, not necessarily
    /// milliseconds — see [`Snowflake`](crate::Snowflake)).
    #[inline]
    pub const fn tick(&self) -> u64 {
        self.0 >> Self::TS_SHIFT
    }

    /// Extract the worker field.
    #[inline]
    pub const fn worker(&self) -> u64 {
        (self.0 >> Self::WK_SHIFT) & Self::WORKER_MASK
    }

    /// Extract the sequence field.
    #[inline]
    pub const fn sequence(&self) -> u64 {
        self.0 & Self::SEQUENCE_MASK
    }

    /// Unpack into (tick, worker, sequence).
    #[inline]
    pub const fn unpack(&self) -> (u64, u64, u64) {
        (self.tick(), self.worker(), self.sequence())
    }

    /// Mix bits for uniform hash distribution via Fibonacci multiply.
    ///
    /// Produces output suitable for identity hashers (e.g., `nohash-hasher`).
    /// The mixing is bijective and reversible via [`MixedId64::unmix()`].
    ///
    /// Cost: 1 multiply (~1 cycle).
    #[inline]
    pub const fn mixed(&self) -> MixedId64<TS, WK, SQ> {
        MixedId64(self.0.wrapping_mul(GOLDEN_64))
    }

    /// Encode as 16-char lowercase hex.
    #[inline]
    pub fn to_hex(&self) -> HexId64 {
        HexId64::encode(self.0)
    }

    /// Encode as 11-char base62.
    #[inline]
    pub fn to_base62(&self) -> Base62Id {
        Base62Id::encode(self.0)
    }

    /// Encode as 13-char base36.
    #[inline]
    pub fn to_base36(&self) -> Base36Id {
        Base36Id::encode(self.0)
    }
}

impl<const TS: u8, const WK: u8, const SQ: u8> Ord for SnowflakeId64<TS, WK, SQ> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        // Raw comparison preserves time ordering (timestamp in MSB)
        self.0.cmp(&other.0)
    }
}

impl<const TS: u8, const WK: u8, const SQ: u8> PartialOrd for SnowflakeId64<TS, WK, SQ> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const TS: u8, const WK: u8, const SQ: u8> Hash for SnowflakeId64<TS, WK, SQ> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.0);
    }
}

impl<const TS: u8, const WK: u8, const SQ: u8> fmt::Debug for SnowflakeId64<TS, WK, SQ> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "SnowflakeId64({}, ts={}, w={}, s={})",
            self.0,
            self.tick(),
            self.worker(),
            self.sequence()
        )
    }
}

impl<const TS: u8, const WK: u8, const SQ: u8> fmt::Display for SnowflakeId64<TS, WK, SQ> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

// =============================================================================
// MixedId64
// =============================================================================

/// 64-bit Snowflake ID with Fibonacci-mixed bits.
///
/// Created by [`SnowflakeId64::mixed()`]. The bits have been permuted for
/// uniform distribution with identity hashers. Use [`unmix()`](Self::unmix)
/// to recover the original `SnowflakeId64`.
///
/// # Hash Behavior
///
/// The `Hash` impl writes the mixed value directly, making this type
/// safe for use with identity hashers (e.g., `nohash-hasher`).
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct MixedId64<const TS: u8, const WK: u8, const SQ: u8>(pub(crate) u64);

impl<const TS: u8, const WK: u8, const SQ: u8> MixedId64<TS, WK, SQ> {
    /// Create from a raw mixed value.
    #[inline]
    pub const fn from_raw(raw: u64) -> Self {
        Self(raw)
    }

    /// Raw mixed u64 value.
    #[inline]
    pub const fn raw(&self) -> u64 {
        self.0
    }

    /// Recover the original Snowflake ID by reversing the Fibonacci multiply.
    #[inline]
    pub const fn unmix(&self) -> SnowflakeId64<TS, WK, SQ> {
        SnowflakeId64(self.0.wrapping_mul(GOLDEN_64_INV))
    }
}

impl<const TS: u8, const WK: u8, const SQ: u8> Hash for MixedId64<TS, WK, SQ> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Already mixed — write directly for identity hashers
        state.write_u64(self.0);
    }
}

impl<const TS: u8, const WK: u8, const SQ: u8> fmt::Debug for MixedId64<TS, WK, SQ> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "MixedId64(0x{:016x})", self.0)
    }
}

impl<const TS: u8, const WK: u8, const SQ: u8> fmt::Display for MixedId64<TS, WK, SQ> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

// =============================================================================
// SnowflakeId32
// =============================================================================

/// 32-bit Snowflake ID with compile-time layout.
///
/// Same as [`SnowflakeId64`] but for 32-bit snowflake generators.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct SnowflakeId32<const TS: u8, const WK: u8, const SQ: u8>(pub(crate) u32);

impl<const TS: u8, const WK: u8, const SQ: u8> SnowflakeId32<TS, WK, SQ> {
    const TS_SHIFT: u8 = WK + SQ;
    const WK_SHIFT: u8 = SQ;
    const SEQUENCE_MASK: u32 = (1u32 << SQ) - 1;
    const WORKER_MASK: u32 = if WK == 0 { 0 } else { (1u32 << WK) - 1 };

    /// Create from a raw u32 value.
    #[inline]
    pub const fn from_raw(raw: u32) -> Self {
        Self(raw)
    }

    /// Raw u32 value.
    #[inline]
    pub const fn raw(&self) -> u32 {
        self.0
    }

    /// Extract the tick field (the generic ordering value, not necessarily
    /// milliseconds — see [`Snowflake`](crate::Snowflake)).
    #[inline]
    pub const fn tick(&self) -> u32 {
        self.0 >> Self::TS_SHIFT
    }

    /// Extract the worker field.
    #[inline]
    pub const fn worker(&self) -> u32 {
        (self.0 >> Self::WK_SHIFT) & Self::WORKER_MASK
    }

    /// Extract the sequence field.
    #[inline]
    pub const fn sequence(&self) -> u32 {
        self.0 & Self::SEQUENCE_MASK
    }

    /// Unpack into (tick, worker, sequence).
    #[inline]
    pub const fn unpack(&self) -> (u32, u32, u32) {
        (self.tick(), self.worker(), self.sequence())
    }

    /// Mix bits for uniform hash distribution via Fibonacci multiply (32-bit).
    #[inline]
    pub const fn mixed(&self) -> MixedId32<TS, WK, SQ> {
        MixedId32(self.0.wrapping_mul(GOLDEN_32))
    }

    /// Encode as 16-char lowercase hex (zero-padded u64).
    #[inline]
    pub fn to_hex(&self) -> HexId64 {
        HexId64::encode(self.0 as u64)
    }

    /// Encode as 11-char base62 (zero-padded u64).
    #[inline]
    pub fn to_base62(&self) -> Base62Id {
        Base62Id::encode(self.0 as u64)
    }

    /// Encode as 13-char base36 (zero-padded u64).
    #[inline]
    pub fn to_base36(&self) -> Base36Id {
        Base36Id::encode(self.0 as u64)
    }
}

impl<const TS: u8, const WK: u8, const SQ: u8> Ord for SnowflakeId32<TS, WK, SQ> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl<const TS: u8, const WK: u8, const SQ: u8> PartialOrd for SnowflakeId32<TS, WK, SQ> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const TS: u8, const WK: u8, const SQ: u8> Hash for SnowflakeId32<TS, WK, SQ> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u32(self.0);
    }
}

impl<const TS: u8, const WK: u8, const SQ: u8> fmt::Debug for SnowflakeId32<TS, WK, SQ> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "SnowflakeId32({}, ts={}, w={}, s={})",
            self.0,
            self.tick(),
            self.worker(),
            self.sequence()
        )
    }
}

impl<const TS: u8, const WK: u8, const SQ: u8> fmt::Display for SnowflakeId32<TS, WK, SQ> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

// =============================================================================
// MixedId32
// =============================================================================

/// 32-bit Snowflake ID with Fibonacci-mixed bits.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct MixedId32<const TS: u8, const WK: u8, const SQ: u8>(pub(crate) u32);

impl<const TS: u8, const WK: u8, const SQ: u8> MixedId32<TS, WK, SQ> {
    /// Create from a raw mixed value.
    #[inline]
    pub const fn from_raw(raw: u32) -> Self {
        Self(raw)
    }

    /// Raw mixed u32 value.
    #[inline]
    pub const fn raw(&self) -> u32 {
        self.0
    }

    /// Recover the original Snowflake ID.
    #[inline]
    pub const fn unmix(&self) -> SnowflakeId32<TS, WK, SQ> {
        SnowflakeId32(self.0.wrapping_mul(GOLDEN_32_INV))
    }
}

impl<const TS: u8, const WK: u8, const SQ: u8> Hash for MixedId32<TS, WK, SQ> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u32(self.0);
    }
}

impl<const TS: u8, const WK: u8, const SQ: u8> fmt::Debug for MixedId32<TS, WK, SQ> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "MixedId32(0x{:08x})", self.0)
    }
}

impl<const TS: u8, const WK: u8, const SQ: u8> fmt::Display for MixedId32<TS, WK, SQ> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

// =============================================================================
// From impls — transparent newtype extraction
// =============================================================================

impl<const TS: u8, const WK: u8, const SQ: u8> From<SnowflakeId64<TS, WK, SQ>> for u64 {
    #[inline]
    fn from(id: SnowflakeId64<TS, WK, SQ>) -> Self {
        id.0
    }
}

impl<const TS: u8, const WK: u8, const SQ: u8> From<MixedId64<TS, WK, SQ>> for u64 {
    #[inline]
    fn from(id: MixedId64<TS, WK, SQ>) -> Self {
        id.0
    }
}

impl<const TS: u8, const WK: u8, const SQ: u8> From<SnowflakeId32<TS, WK, SQ>> for u32 {
    #[inline]
    fn from(id: SnowflakeId32<TS, WK, SQ>) -> Self {
        id.0
    }
}

impl<const TS: u8, const WK: u8, const SQ: u8> From<MixedId32<TS, WK, SQ>> for u32 {
    #[inline]
    fn from(id: MixedId32<TS, WK, SQ>) -> Self {
        id.0
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(all(test, feature = "std"))]
mod tests {
    use super::*;

    type Id64 = SnowflakeId64<42, 6, 16>;
    type Id32 = SnowflakeId32<20, 4, 8>;

    #[test]
    fn golden_64_inverse_correct() {
        assert_eq!(GOLDEN_64.wrapping_mul(GOLDEN_64_INV), 1u64);
    }

    #[test]
    fn golden_32_inverse_correct() {
        assert_eq!(GOLDEN_32.wrapping_mul(GOLDEN_32_INV), 1u32);
    }

    #[test]
    fn unpack_64() {
        // ts=100, worker=5, seq=42 for <42, 6, 16>
        let raw = (100u64 << 22) | (5u64 << 16) | 0x2A_u64;
        let id = Id64::from_raw(raw);

        assert_eq!(id.tick(), 100);
        assert_eq!(id.worker(), 5);
        assert_eq!(id.sequence(), 42);
        assert_eq!(id.unpack(), (100, 5, 42));
    }

    #[test]
    fn unpack_32() {
        // ts=50, worker=7, seq=200 for <20, 4, 8>
        let raw = (50u32 << 12) | (7u32 << 8) | 0xC8_u32;
        let id = Id32::from_raw(raw);

        assert_eq!(id.tick(), 50);
        assert_eq!(id.worker(), 7);
        assert_eq!(id.sequence(), 200);
    }

    #[test]
    fn mix_unmix_roundtrip_64() {
        for raw in [0u64, 1, 12345, 0xDEAD_BEEF_CAFE_BABE, u64::MAX] {
            let id = Id64::from_raw(raw);
            let mixed = id.mixed();
            let recovered = mixed.unmix();
            assert_eq!(recovered.raw(), raw);
        }
    }

    #[test]
    fn mix_unmix_roundtrip_32() {
        for raw in [0u32, 1, 12345, 0xDEAD_BEEF, u32::MAX] {
            let id = Id32::from_raw(raw);
            let mixed = id.mixed();
            let recovered = mixed.unmix();
            assert_eq!(recovered.raw(), raw);
        }
    }

    #[test]
    fn mixed_differs_from_raw() {
        let id = Id64::from_raw(12345);
        let mixed = id.mixed();
        assert_ne!(mixed.raw(), id.raw());
    }

    #[test]
    fn ordering_preserves_time() {
        let id1 = Id64::from_raw((100u64 << 22) | (5u64 << 16));
        let id2 = Id64::from_raw((101u64 << 22) | (5u64 << 16));
        let id3 = Id64::from_raw((100u64 << 22) | (5u64 << 16) | 1);

        // Later timestamp > earlier timestamp
        assert!(id2 > id1);
        // Same timestamp, higher sequence > lower sequence
        assert!(id3 > id1);
    }

    #[test]
    fn to_hex_roundtrip() {
        let id = Id64::from_raw(0xDEAD_BEEF_CAFE_BABE);
        let hex = id.to_hex();
        assert_eq!(hex.decode(), id.raw());
    }

    #[test]
    fn to_base62_roundtrip() {
        let id = Id64::from_raw(12_345_678);
        let b62 = id.to_base62();
        assert_eq!(b62.decode(), id.raw());
    }

    #[test]
    fn to_base36_roundtrip() {
        let id = Id64::from_raw(12_345_678);
        let b36 = id.to_base36();
        assert_eq!(b36.decode(), id.raw());
    }

    #[test]
    fn snowflake32_to_hex_roundtrip() {
        let id = Id32::from_raw(0xDEAD_BEEF);
        let hex = id.to_hex();
        assert_eq!(hex.decode(), 0xDEAD_BEEF_u64);
    }

    #[test]
    fn snowflake32_to_base62_roundtrip() {
        let id = Id32::from_raw(12_345_678);
        let b62 = id.to_base62();
        assert_eq!(b62.decode(), 12_345_678_u64);
    }

    #[test]
    fn snowflake32_to_base36_roundtrip() {
        let id = Id32::from_raw(12_345_678);
        let b36 = id.to_base36();
        assert_eq!(b36.decode(), 12_345_678_u64);
    }

    #[test]
    fn display_shows_raw() {
        let id = Id64::from_raw(42);
        assert_eq!(format!("{}", id), "42");
    }

    #[test]
    fn debug_shows_fields() {
        let raw = (100u64 << 22) | (5u64 << 16) | 7u64;
        let id = Id64::from_raw(raw);
        let dbg = format!("{:?}", id);
        assert!(dbg.contains("ts=100"));
        assert!(dbg.contains("w=5"));
        assert!(dbg.contains("s=7"));
    }
}
