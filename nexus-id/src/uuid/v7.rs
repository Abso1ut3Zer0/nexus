//! UUID v7 generator (timestamp + random).
//!
//! UUID v7 embeds a Unix timestamp for time-ordering while maintaining
//! randomness for uniqueness. This implementation follows RFC 9562 and
//! uses the same Instant-based pattern as Snowflake for syscall-free
//! hot path operation.

use std::time::Instant;

use crate::SequenceExhausted;
use crate::prng::WyRand;
use crate::types::{Uuid, UuidCompact};

/// Maximum sequence value (12 bits = 4096 per millisecond).
const SEQUENCE_MAX: u16 = 0xFFF;

/// UUID v7 generator.
///
/// Generates RFC 9562 compliant UUID v7 values with embedded Unix timestamps.
/// Uses a fast PRNG for random bits and sequence counters for monotonicity.
///
/// # Layout (RFC 9562)
///
/// ```text
/// [unix_ts_ms: 48 bits][ver=7: 4 bits][rand_a: 12 bits][var=10: 2 bits][rand_b: 62 bits]
/// ```
///
/// The `rand_a` field is used as a sequence counter, allowing 4096 UUIDs per
/// millisecond before returning `SequenceExhausted`.
///
/// # Performance
///
/// - Construction: one `getrandom` syscall (or explicit seed)
/// - `next()`: ~40-50 cycles (timestamp math + PRNG + formatting)
/// - Zero syscalls on hot path
/// - Zero allocation
///
/// # Example
///
/// ```rust
/// use std::time::{Instant, SystemTime, UNIX_EPOCH};
/// use nexus_id::uuid::UuidV7;
///
/// // Snap both clocks at startup
/// let epoch = Instant::now();
/// let unix_base = SystemTime::now()
///     .duration_since(UNIX_EPOCH)
///     .unwrap()
///     .as_millis() as u64;
///
/// let mut generator = UuidV7::new(epoch, unix_base, 12345);
///
/// // Hot path - just pass current Instant
/// let now = Instant::now();
/// let id = generator.next(now).unwrap();
/// ```
#[derive(Debug, Clone)]
pub struct UuidV7 {
    /// Base instant for timestamp calculation.
    epoch: Instant,
    /// Unix timestamp (ms) at epoch instant.
    unix_base_ms: u64,
    /// PRNG for random bits.
    rng: WyRand,
    /// Last timestamp used (for sequence tracking).
    last_ts_ms: u64,
    /// Sequence counter within current millisecond.
    sequence: u16,
}

impl UuidV7 {
    /// Create a new generator with explicit parameters.
    ///
    /// # Arguments
    ///
    /// * `epoch` - Base instant for timestamp calculation
    /// * `unix_base_ms` - Unix timestamp (ms since Unix epoch) at the epoch instant
    /// * `seed` - PRNG seed for random bits
    ///
    /// # Example
    ///
    /// ```rust
    /// use std::time::{Instant, SystemTime, UNIX_EPOCH};
    /// use nexus_id::uuid::UuidV7;
    ///
    /// let epoch = Instant::now();
    /// let unix_base = SystemTime::now()
    ///     .duration_since(UNIX_EPOCH)
    ///     .unwrap()
    ///     .as_millis() as u64;
    ///
    /// let mut generator = UuidV7::new(epoch, unix_base, 42);
    /// ```
    #[inline]
    pub fn new(epoch: Instant, unix_base_ms: u64, seed: u64) -> Self {
        Self {
            epoch,
            unix_base_ms,
            rng: WyRand::new(seed),
            last_ts_ms: u64::MAX, // Forces sequence reset on first call
            sequence: 0,
        }
    }

    /// Create a new generator seeded from system entropy.
    ///
    /// Makes one `getrandom` syscall.
    pub fn from_entropy(epoch: Instant, unix_base_ms: u64) -> Self {
        Self {
            epoch,
            unix_base_ms,
            rng: WyRand::from_entropy(),
            last_ts_ms: u64::MAX,
            sequence: 0,
        }
    }

    /// Generate raw UUID bytes as (hi, lo) pair.
    ///
    /// Returns the 128-bit UUID as two 64-bit values in big-endian byte order.
    ///
    /// # Errors
    ///
    /// Returns [`SequenceExhausted`] if more than 4096 UUIDs are generated
    /// within the same millisecond.
    #[inline]
    pub fn next_raw(&mut self, now: Instant) -> Result<(u64, u64), SequenceExhausted> {
        // Calculate Unix timestamp from Instant offset
        let offset_ms = now.saturating_duration_since(self.epoch).as_millis() as u64;
        let ts_ms = self.unix_base_ms.wrapping_add(offset_ms);

        // Handle sequence
        if ts_ms == self.last_ts_ms {
            self.sequence = self.sequence.wrapping_add(1);
            if self.sequence > SEQUENCE_MAX {
                return Err(SequenceExhausted {
                    tick: ts_ms,
                    max_sequence: SEQUENCE_MAX as u64,
                });
            }
        } else {
            self.last_ts_ms = ts_ms;
            self.sequence = 0;
        }

        // Generate random bits for rand_b
        let rand_b = self.rng.next_u64();

        // Pack into UUID v7 format
        // hi: [timestamp: 48][version=7: 4][sequence: 12]
        let hi = (ts_ms << 16) | (0x7 << 12) | (self.sequence as u64);

        // lo: [variant=10: 2][rand_b: 62]
        let lo = (0b10 << 62) | (rand_b & 0x3FFF_FFFF_FFFF_FFFF);

        Ok((hi, lo))
    }

    /// Generate a UUID in standard dashed format.
    ///
    /// Returns a 36-character string: `xxxxxxxx-xxxx-7xxx-Nxxx-xxxxxxxxxxxx`
    /// where N is 8, 9, a, or b (RFC variant).
    ///
    /// # Errors
    ///
    /// Returns [`SequenceExhausted`] if more than 4096 UUIDs are generated
    /// within the same millisecond.
    #[inline]
    pub fn next(&mut self, now: Instant) -> Result<Uuid, SequenceExhausted> {
        let (hi, lo) = self.next_raw(now)?;
        Ok(Uuid::from_raw(hi, lo))
    }

    /// Generate a UUID in compact format (no dashes).
    ///
    /// Returns a 32-character hex string.
    ///
    /// # Errors
    ///
    /// Returns [`SequenceExhausted`] if more than 4096 UUIDs are generated
    /// within the same millisecond.
    #[inline]
    pub fn next_compact(&mut self, now: Instant) -> Result<UuidCompact, SequenceExhausted> {
        let (hi, lo) = self.next_raw(now)?;
        Ok(UuidCompact::from_raw(hi, lo))
    }

    /// Epoch instant for this generator.
    #[inline]
    pub fn epoch(&self) -> Instant {
        self.epoch
    }

    /// Unix base timestamp (ms) for this generator.
    #[inline]
    pub const fn unix_base_ms(&self) -> u64 {
        self.unix_base_ms
    }

    /// Current sequence within this millisecond.
    #[inline]
    pub const fn sequence(&self) -> u16 {
        self.sequence
    }

    /// Last timestamp used (ms since Unix epoch).
    #[inline]
    pub const fn last_timestamp(&self) -> u64 {
        self.last_ts_ms
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    fn test_generator() -> UuidV7 {
        let epoch = Instant::now();
        let unix_base = 1_700_000_000_000u64; // Some fixed Unix timestamp
        UuidV7::new(epoch, unix_base, 42)
    }

    #[test]
    fn basic_generation() {
        let epoch = Instant::now();
        let unix_base = 1_700_000_000_000u64;
        let mut generator = UuidV7::new(epoch, unix_base, 42);

        let uuid = generator.next(epoch).unwrap();
        assert_eq!(uuid.len(), 36);
    }

    #[test]
    fn deterministic_with_seed() {
        let epoch = Instant::now();
        let unix_base = 1_700_000_000_000u64;

        let mut gen1 = UuidV7::new(epoch, unix_base, 42);
        let mut gen2 = UuidV7::new(epoch, unix_base, 42);

        for _ in 0..10 {
            assert_eq!(
                gen1.next(epoch).unwrap().as_str(),
                gen2.next(epoch).unwrap().as_str()
            );
        }
    }

    #[test]
    fn version_is_7() {
        let mut generator = test_generator();
        let epoch = generator.epoch();

        for _ in 0..100 {
            let (hi, _lo) = generator.next_raw(epoch).unwrap();
            // Version is in bits 12-15
            let version = (hi >> 12) & 0xF;
            assert_eq!(version, 7);
        }
    }

    #[test]
    fn variant_is_rfc() {
        let mut generator = test_generator();
        let epoch = generator.epoch();

        for _ in 0..100 {
            let (_hi, lo) = generator.next_raw(epoch).unwrap();
            // Variant is in bits 62-63, should be 0b10
            let variant = (lo >> 62) & 0b11;
            assert_eq!(variant, 0b10);
        }
    }

    #[test]
    fn sequence_increments_same_ms() {
        let mut generator = test_generator();
        let epoch = generator.epoch();

        let uuid1 = generator.next(epoch).unwrap();
        let uuid2 = generator.next(epoch).unwrap();
        let uuid3 = generator.next(epoch).unwrap();

        // UUIDs should be different
        assert_ne!(uuid1.as_str(), uuid2.as_str());
        assert_ne!(uuid2.as_str(), uuid3.as_str());

        // After 3 calls: seq 0, 1, 2 - current sequence is 2
        assert_eq!(generator.sequence(), 2);
    }

    #[test]
    fn sequence_resets_new_ms() {
        let mut generator = test_generator();
        let epoch = generator.epoch();

        // Generate at epoch
        let _ = generator.next(epoch).unwrap();
        let _ = generator.next(epoch).unwrap();
        // After 2 calls: seq 0, 1 - current sequence is 1
        assert_eq!(generator.sequence(), 1);

        // Advance 1ms
        let later = epoch + Duration::from_millis(1);
        let _ = generator.next(later).unwrap();

        // Sequence should have reset to 0
        assert_eq!(generator.sequence(), 0);
    }

    #[test]
    fn sequence_exhaustion() {
        let mut generator = test_generator();
        let epoch = generator.epoch();

        // Generate 4096 UUIDs (sequence 0-4095)
        for _ in 0..=SEQUENCE_MAX {
            generator.next(epoch).unwrap();
        }

        // 4097th should fail
        let result = generator.next(epoch);
        assert!(result.is_err());

        let err = result.unwrap_err();
        assert_eq!(err.max_sequence, SEQUENCE_MAX as u64);
    }

    #[test]
    fn timestamp_embedded() {
        let epoch = Instant::now();
        let unix_base = 1_700_000_000_000u64;
        let mut generator = UuidV7::new(epoch, unix_base, 42);

        // Generate at epoch (0ms offset)
        let (hi, _lo) = generator.next_raw(epoch).unwrap();
        let extracted_ts = hi >> 16;
        assert_eq!(extracted_ts, unix_base);

        // Generate 100ms later
        let later = epoch + Duration::from_millis(100);
        let mut generator2 = UuidV7::new(epoch, unix_base, 42);
        let (hi2, _lo2) = generator2.next_raw(later).unwrap();
        let extracted_ts2 = hi2 >> 16;
        assert_eq!(extracted_ts2, unix_base + 100);
    }

    #[test]
    fn format_is_correct() {
        let mut generator = test_generator();
        let uuid = generator.next(generator.epoch()).unwrap();

        assert_eq!(uuid.len(), 36);

        let s = uuid.as_str();
        // Check dashes at correct positions
        assert_eq!(s.as_bytes()[8], b'-');
        assert_eq!(s.as_bytes()[13], b'-');
        assert_eq!(s.as_bytes()[18], b'-');
        assert_eq!(s.as_bytes()[23], b'-');

        // Check version char is '7'
        assert_eq!(s.as_bytes()[14], b'7');

        // Check variant char is 8, 9, a, or b
        let variant_char = s.as_bytes()[19];
        assert!(
            variant_char == b'8'
                || variant_char == b'9'
                || variant_char == b'a'
                || variant_char == b'b'
        );
    }

    #[test]
    fn time_ordering() {
        let mut generator = test_generator();
        let epoch = generator.epoch();

        let mut uuids = Vec::new();
        for i in 0..100 {
            let now = epoch + Duration::from_millis(i);
            uuids.push(generator.next(now).unwrap());
        }

        // UUIDs should be lexicographically ordered (time-ordered property of v7)
        for i in 1..uuids.len() {
            assert!(uuids[i].as_str() > uuids[i - 1].as_str());
        }
    }

    #[test]
    fn from_entropy_works() {
        let epoch = Instant::now();
        let unix_base = 1_700_000_000_000u64;
        let mut generator = UuidV7::from_entropy(epoch, unix_base);

        let uuid = generator.next(epoch).unwrap();
        assert_eq!(uuid.len(), 36);
    }
}
