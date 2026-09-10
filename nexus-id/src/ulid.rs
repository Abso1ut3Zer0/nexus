//! ULID generator (Universally Unique Lexicographically Sortable Identifier).
//!
//! ULIDs are 128-bit identifiers encoded as 26 Crockford Base32 characters.
//! They embed a Unix timestamp for time-ordering while maintaining randomness
//! for uniqueness.
//!
//! # Layout
//!
//! ```text
//! [timestamp: 48 bits][random: 80 bits]
//! ```
//!
//! - Timestamp: milliseconds since Unix epoch (supports dates until 10889 AD)
//! - Random: 80 bits of randomness per millisecond
//!
//! # Monotonicity
//!
//! Within the same millisecond, the random component is incremented to ensure
//! monotonicity. If the random component would overflow (extremely unlikely),
//! generation returns an error.

use std::time::Instant;

use crate::SequenceExhausted;
use crate::prng::WyRand;
use crate::types::Ulid;

/// ULID generator.
///
/// Generates lexicographically sortable 128-bit identifiers encoded as
/// 26 Crockford Base32 characters.
///
/// # Performance
///
/// - Construction: one `getrandom` syscall (or explicit seed)
/// - `next()`: ~40-50 cycles (timestamp math + PRNG + encoding)
/// - Zero syscalls on hot path
/// - Zero allocation
///
/// # Example
///
/// ```rust
/// use std::time::{Instant, SystemTime, UNIX_EPOCH};
/// use nexus_id::ulid::UlidGenerator;
///
/// let epoch = Instant::now();
/// let unix_base = SystemTime::now()
///     .duration_since(UNIX_EPOCH)
///     .unwrap()
///     .as_millis() as u64;
///
/// let mut generator = UlidGenerator::new(epoch, unix_base, 42);
/// let id = generator.next(Instant::now());
/// assert_eq!(id.len(), 26);
/// ```
#[derive(Debug, Clone)]
pub struct UlidGenerator {
    /// Base instant for timestamp calculation.
    epoch: Instant,
    /// Unix timestamp (ms) at epoch instant.
    unix_base_ms: u64,
    /// PRNG for random bits.
    rng: WyRand,
    /// Last timestamp used.
    last_ts_ms: u64,
    /// Last random high bits (for monotonic increment).
    last_rand_hi: u16,
    /// Last random low bits (for monotonic increment).
    last_rand_lo: u64,
}

impl UlidGenerator {
    /// Create a new generator with explicit parameters.
    ///
    /// # Arguments
    ///
    /// * `epoch` - Base instant for timestamp calculation
    /// * `unix_base_ms` - Unix timestamp (ms since Unix epoch) at the epoch instant
    /// * `seed` - PRNG seed for random bits
    #[inline]
    pub fn new(epoch: Instant, unix_base_ms: u64, seed: u64) -> Self {
        Self {
            epoch,
            unix_base_ms,
            rng: WyRand::new(seed),
            last_ts_ms: u64::MAX,
            last_rand_hi: 0,
            last_rand_lo: 0,
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
            last_rand_hi: 0,
            last_rand_lo: 0,
        }
    }

    /// Generate a ULID.
    ///
    /// Returns a 26-character Crockford Base32 string.
    ///
    /// # Monotonicity
    ///
    /// Within the same millisecond, the random component is incremented
    /// to ensure lexicographic ordering. This means ULIDs generated in
    /// the same millisecond will sort correctly.
    ///
    /// In the theoretical case where the 80-bit random component overflows
    /// (requires ~2^80 generations in one millisecond — physically impossible),
    /// the value wraps and monotonicity is violated. Use [`try_next()`](Self::try_next)
    /// if you need overflow detection.
    #[inline]
    pub fn next(&mut self, now: Instant) -> Ulid {
        let offset_ms = now.saturating_duration_since(self.epoch).as_millis() as u64;
        let ts_ms = self.unix_base_ms.wrapping_add(offset_ms);

        let (rand_hi, rand_lo) = if ts_ms == self.last_ts_ms {
            // Same millisecond: increment random for monotonicity
            let (new_lo, carry) = self.last_rand_lo.overflowing_add(1);
            let new_hi = if carry {
                self.last_rand_hi.wrapping_add(1)
            } else {
                self.last_rand_hi
            };
            self.last_rand_hi = new_hi;
            self.last_rand_lo = new_lo;
            (new_hi, new_lo)
        } else {
            // New millisecond: generate fresh random
            self.last_ts_ms = ts_ms;
            let rand_hi = (self.rng.next_u64() & 0xFFFF) as u16;
            let rand_lo = self.rng.next_u64();
            self.last_rand_hi = rand_hi;
            self.last_rand_lo = rand_lo;
            (rand_hi, rand_lo)
        };

        Ulid::from_raw(ts_ms, rand_hi, rand_lo)
    }

    /// Generate a ULID, returning an error if random component would overflow.
    ///
    /// This is extremely unlikely (would require 2^80 generations in one ms).
    #[inline]
    pub fn try_next(&mut self, now: Instant) -> Result<Ulid, SequenceExhausted> {
        let offset_ms = now.saturating_duration_since(self.epoch).as_millis() as u64;
        let ts_ms = self.unix_base_ms.wrapping_add(offset_ms);

        let (rand_hi, rand_lo) = if ts_ms == self.last_ts_ms {
            // Same millisecond: increment random for monotonicity
            let (new_lo, carry) = self.last_rand_lo.overflowing_add(1);
            let new_hi = if carry {
                let (hi, hi_carry) = self.last_rand_hi.overflowing_add(1);
                if hi_carry {
                    return Err(SequenceExhausted {
                        tick: ts_ms,
                        max_sequence: u64::MAX,
                    });
                }
                hi
            } else {
                self.last_rand_hi
            };
            self.last_rand_hi = new_hi;
            self.last_rand_lo = new_lo;
            (new_hi, new_lo)
        } else {
            // New millisecond: generate fresh random
            self.last_ts_ms = ts_ms;
            let rand_hi = (self.rng.next_u64() & 0xFFFF) as u16;
            let rand_lo = self.rng.next_u64();
            self.last_rand_hi = rand_hi;
            self.last_rand_lo = rand_lo;
            (rand_hi, rand_lo)
        };

        Ok(Ulid::from_raw(ts_ms, rand_hi, rand_lo))
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    fn test_generator() -> UlidGenerator {
        let epoch = Instant::now();
        let unix_base = 1_700_000_000_000u64;
        UlidGenerator::new(epoch, unix_base, 42)
    }

    #[test]
    fn basic_generation() {
        let epoch = Instant::now();
        let unix_base = 1_700_000_000_000u64;
        let mut generator = UlidGenerator::new(epoch, unix_base, 42);

        let ulid = generator.next(epoch);
        assert_eq!(ulid.len(), 26);

        // All chars should be valid Crockford Base32
        for c in ulid.as_str().chars() {
            assert!(
                c.is_ascii_digit() || c.is_ascii_uppercase(),
                "Invalid char: {}",
                c
            );
        }
    }

    #[test]
    fn deterministic_with_seed() {
        let epoch = Instant::now();
        let unix_base = 1_700_000_000_000u64;

        let mut gen1 = UlidGenerator::new(epoch, unix_base, 42);
        let mut gen2 = UlidGenerator::new(epoch, unix_base, 42);

        // First ULID at same timestamp should be identical
        assert_eq!(gen1.next(epoch).as_str(), gen2.next(epoch).as_str());
    }

    #[test]
    fn timestamp_encoded() {
        let epoch = Instant::now();
        let unix_base = 1_700_000_000_000u64;
        let mut generator = UlidGenerator::new(epoch, unix_base, 42);

        let ulid = generator.next(epoch);
        assert_eq!(ulid.timestamp_ms(), unix_base);

        // 100ms later
        let later = epoch + Duration::from_millis(100);
        let mut gen2 = UlidGenerator::new(epoch, unix_base, 42);
        let ulid2 = gen2.next(later);
        assert_eq!(ulid2.timestamp_ms(), unix_base + 100);
    }

    #[test]
    fn monotonic_within_ms() {
        let mut generator = test_generator();
        let epoch = generator.epoch();

        let ulid1 = generator.next(epoch);
        let ulid2 = generator.next(epoch);
        let ulid3 = generator.next(epoch);

        // Should be lexicographically ordered
        assert!(ulid1.as_str() < ulid2.as_str());
        assert!(ulid2.as_str() < ulid3.as_str());
    }

    #[test]
    fn random_roundtrip() {
        let epoch = Instant::now();
        let unix_base = 1_700_000_000_000u64;
        let mut generator = UlidGenerator::new(epoch, unix_base, 42);

        let ulid = generator.next(epoch);
        let (rand_hi, rand_lo) = ulid.random();

        // Verify we can reconstruct
        let reconstructed: Ulid = Ulid::from_raw(unix_base, rand_hi, rand_lo);
        assert_eq!(ulid.as_str(), reconstructed.as_str());
    }

    #[test]
    fn time_ordering() {
        let mut generator = test_generator();
        let epoch = generator.epoch();

        let mut ulids = Vec::new();
        for i in 0..100 {
            let now = epoch + Duration::from_millis(i);
            ulids.push(generator.next(now));
        }

        // ULIDs should be lexicographically ordered
        for i in 1..ulids.len() {
            assert!(ulids[i].as_str() > ulids[i - 1].as_str());
        }
    }

    #[test]
    fn from_entropy_works() {
        let epoch = Instant::now();
        let unix_base = 1_700_000_000_000u64;
        let mut generator = UlidGenerator::from_entropy(epoch, unix_base);

        let ulid = generator.next(epoch);
        assert_eq!(ulid.len(), 26);
    }
}
