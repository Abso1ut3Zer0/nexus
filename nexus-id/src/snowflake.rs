//! Snowflake-style ID generation with const generic bit layouts.
//!
//! # Overview
//!
//! `nexus-id` provides high-performance snowflake ID generation with
//! user-configurable bit layouts via const generics. No heap allocation,
//! no dependencies, optimized for trading systems where ID generation
//! is on the critical path.
//!
//! The generator is tick-agnostic: callers provide a raw `u64` tick value
//! (milliseconds, block numbers, logical clocks—whatever fits your domain).
//!
//! # Example
//!
//! ```rust
//! use std::time::Instant;
//! use nexus_id::Snowflake64;
//!
//! // Layout: 42 bits tick, 6 bits worker, 16 bits sequence (65k/tick)
//! type ClOrdId = Snowflake64<42, 6, 16>;
//!
//! let epoch = Instant::now();
//! let mut id_gen = ClOrdId::new(5);
//!
//! // In event loop - snap once per iteration
//! let tick = (Instant::now() - epoch).as_millis() as u64;
//! let id: u64 = id_gen.next(tick).unwrap();
//!
//! // Unpack to inspect
//! let (tick, worker, seq) = ClOrdId::unpack(id);
//! assert_eq!(worker, 5);
//! assert_eq!(seq, 0);
//! ```
//!
//! # Bit Layout
//!
//! IDs are packed MSB to LSB as:
//!
//! ```text
//! [timestamp: TS bits][worker: WK bits][sequence: SQ bits]
//! ```
//!
//! Common configurations:
//!
//! | TS | WK | SQ | Years @ ms | Workers | IDs/ms |
//! |----|----|----|------------|---------|--------|
//! | 41 | 10 | 12 | 69         | 1024    | 4k     |
//! | 42 | 6  | 16 | 139        | 64      | 65k    |
//! | 39 | 9  | 16 | 17         | 512     | 65k    |
//!
//! # Performance
//!
//! The `next()` method is designed for hot-path usage:
//! - No syscalls (caller provides tick)
//! - No allocation
//! - Predictable branches (same-tick case is common)
//! - ~24-26 cycles p50 (~6ns at 4GHz)

use core::fmt;
use core::marker::PhantomData;

use crate::snowflake_id::{MixedId32, MixedId64, SnowflakeId32, SnowflakeId64};

/// Integer types usable as snowflake IDs.
///
/// Implemented for `u32`, `i32`, `u64`, `i64`.
///
/// This trait is sealed and cannot be implemented outside this crate.
pub trait IdInt: Copy + private::Sealed {
    /// Number of bits in this integer type.
    const BITS: u8;

    /// Convert from raw u64 representation.
    fn from_raw(v: u64) -> Self;

    /// Convert to raw u64 representation.
    fn to_raw(self) -> u64;
}

mod private {
    pub trait Sealed {}
    impl Sealed for u32 {}
    impl Sealed for i32 {}
    impl Sealed for u64 {}
    impl Sealed for i64 {}
}

macro_rules! impl_id_int {
    ($($ty:ty => $bits:expr),* $(,)?) => {
        $(
            impl IdInt for $ty {
                const BITS: u8 = $bits;

                #[inline(always)]
                fn from_raw(v: u64) -> Self {
                    v as Self
                }

                #[inline(always)]
                fn to_raw(self) -> u64 {
                    self as u64
                }
            }
        )*
    };
}

impl_id_int!(
    u32 => 32,
    i32 => 32,
    u64 => 64,
    i64 => 64,
);

/// Error returned when a sequence counter is exhausted within a single tick.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SequenceExhausted {
    /// Tick value when exhaustion occurred.
    pub tick: u64,
    /// Maximum sequence value for this generator's layout.
    pub max_sequence: u64,
}

impl fmt::Display for SequenceExhausted {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "sequence exhausted at tick {}: generated {} IDs in one tick",
            self.tick,
            self.max_sequence + 1
        )
    }
}

#[cfg(feature = "std")]
impl std::error::Error for SequenceExhausted {}

/// Error returned by [`Snowflake`] generators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum SnowflakeError {
    /// Sequence counter exhausted for this tick value.
    Exhausted(SequenceExhausted),
    /// Tick exceeds the timestamp field width.
    TimestampOverflow {
        /// The tick value that caused the overflow.
        tick: u64,
        /// Maximum valid tick for this generator's timestamp bit width.
        max: u64,
    },
}

impl fmt::Display for SnowflakeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SnowflakeError::Exhausted(e) => e.fmt(f),
            SnowflakeError::TimestampOverflow { tick, max } => {
                write!(f, "tick {tick} exceeds timestamp maximum {max}")
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for SnowflakeError {}

impl From<SequenceExhausted> for SnowflakeError {
    fn from(e: SequenceExhausted) -> Self {
        SnowflakeError::Exhausted(e)
    }
}

/// Snowflake ID generator.
///
/// # Type Parameters
/// - `T`: Output integer type (`u32`, `i32`, `u64`, `i64`)
/// - `TS`: Tick bits (ordering field)
/// - `WK`: Worker bits (0 for single-worker systems)
/// - `SQ`: Sequence bits
///
/// # Layout (MSB to LSB)
/// ```text
/// [tick: TS bits][worker: WK bits][sequence: SQ bits]
/// ```
///
/// # Compile-Time Validation
/// - `TS + WK + SQ <= T::BITS`
/// - `TS > 0`
/// - `SQ > 0`
///
/// # Tick
///
/// The generator is tick-agnostic. The caller provides a raw `u64` value
/// to `next()` which becomes the ordering field in the ID. Common choices:
/// - Milliseconds since an application epoch (`(now - epoch).as_millis() as u64`)
/// - Block number (blockchain)
/// - Logical clock / Lamport counter
///
/// The only requirement is that the value is monotonically non-decreasing.
///
/// # Example
/// ```rust
/// use std::time::Instant;
/// use nexus_id::Snowflake64;
///
/// // 42 bits tick, 6 bits worker, 16 bits sequence
/// type TradingId = Snowflake64<42, 6, 16>;
///
/// let epoch = Instant::now();
/// let mut id_gen = TradingId::new(5);
///
/// let tick = (Instant::now() - epoch).as_millis() as u64;
/// let id: u64 = id_gen.next(tick).unwrap();
/// ```
pub struct Snowflake<T: IdInt, const TS: u8, const WK: u8, const SQ: u8> {
    worker_shifted: u64,
    last_tick: u64,
    sequence: u64,
    _marker: PhantomData<T>,
}

impl<T: IdInt, const TS: u8, const WK: u8, const SQ: u8> Snowflake<T, TS, WK, SQ> {
    /// Compile-time layout validation.
    const _VALIDATE: () = {
        assert!(
            TS as u16 + WK as u16 + SQ as u16 <= T::BITS as u16,
            "layout exceeds integer bits: TS + WK + SQ > T::BITS"
        );
        assert!(TS > 0, "timestamp bits must be > 0");
        assert!(SQ > 0, "sequence bits must be > 0");
    };

    /// Shift amount for timestamp field.
    const TS_SHIFT: u8 = WK + SQ;

    /// Shift amount for worker field.
    const WK_SHIFT: u8 = SQ;

    /// Maximum sequence value for this layout.
    pub const SEQUENCE_MAX: u64 = (1u64 << SQ) - 1;

    /// Maximum worker value for this layout.
    pub const WORKER_MAX: u64 = if WK == 0 { 0 } else { (1u64 << WK) - 1 };

    /// Maximum timestamp value for this layout.
    pub const TIMESTAMP_MAX: u64 = (1u64 << TS) - 1;

    /// Create a new generator.
    ///
    /// # Arguments
    /// * `worker` - Worker ID, must fit in WK bits
    ///
    /// # Panics
    /// Panics if `worker > WORKER_MAX`.
    ///
    /// # Example
    /// ```rust
    /// use nexus_id::Snowflake64;
    ///
    /// type MyId = Snowflake64<42, 6, 16>;
    ///
    /// let mut id_gen = MyId::new(5);
    /// ```
    pub fn new(worker: u64) -> Self {
        // Trigger compile-time validation
        let () = Self::_VALIDATE;

        assert!(
            worker <= Self::WORKER_MAX,
            "worker {} exceeds max {}",
            worker,
            Self::WORKER_MAX
        );

        Self {
            worker_shifted: worker << Self::WK_SHIFT,
            last_tick: u64::MAX, // Ensures first call takes "new tick" branch
            sequence: 0,
            _marker: PhantomData,
        }
    }

    /// Generate the next ID.
    ///
    /// # Arguments
    /// * `tick` - Monotonically non-decreasing value for the ordering field.
    ///   Typically `(now - epoch).as_millis() as u64` for time-based IDs, but can
    ///   be any u64 sequence (block numbers, logical clocks, etc.).
    ///
    /// # Errors
    /// Returns [`SequenceExhausted`] if more than `SEQUENCE_MAX` IDs are
    /// generated with the same tick value. This is a backpressure signal.
    ///
    /// # Performance
    /// This method is designed for hot-path usage:
    /// - No syscalls (caller provides tick)
    /// - No allocation
    /// - Single predictable branch in the common case
    ///
    /// # Example
    /// ```rust
    /// use std::time::Instant;
    /// use nexus_id::Snowflake64;
    ///
    /// type MyId = Snowflake64<42, 6, 16>;
    ///
    /// let epoch = Instant::now();
    /// let mut id_gen = MyId::new(5);
    ///
    /// // Snap time once per event loop iteration
    /// let tick = (Instant::now() - epoch).as_millis() as u64;
    ///
    /// // Generate IDs using that tick
    /// let id1 = id_gen.next(tick).unwrap();
    /// let id2 = id_gen.next(tick).unwrap();
    /// ```
    pub fn next(&mut self, tick: u64) -> Result<T, SnowflakeError> {
        if tick > Self::TIMESTAMP_MAX {
            return Err(SnowflakeError::TimestampOverflow {
                tick,
                max: Self::TIMESTAMP_MAX,
            });
        }
        if tick == self.last_tick {
            self.sequence += 1;
            if self.sequence > Self::SEQUENCE_MAX {
                return Err(SnowflakeError::Exhausted(SequenceExhausted {
                    tick,
                    max_sequence: Self::SEQUENCE_MAX,
                }));
            }
        } else {
            self.last_tick = tick;
            self.sequence = 0;
        }

        Ok(T::from_raw(
            (tick << Self::TS_SHIFT) | self.worker_shifted | self.sequence,
        ))
    }

    /// Generate a raw ID with Fibonacci-mixed bits for identity hashers.
    ///
    /// Applies a Fibonacci multiply (bijective, ~1 cycle) to the raw ID,
    /// producing output with uniform bit distribution. Use with identity
    /// hashers (e.g., `nohash-hasher`) for optimal HashMap performance.
    ///
    /// The mixing is NOT reversible from this raw integer — use
    /// [`next_id()`](Snowflake::next_id) + [`SnowflakeId64::mixed()`] if you
    /// need to unmix later.
    ///
    /// # Example
    ///
    /// ```rust
    /// use nexus_id::Snowflake64;
    ///
    /// type OrderId = Snowflake64<42, 6, 16>;
    ///
    /// let mut id_gen = OrderId::new(0);
    ///
    /// let id = id_gen.mixed(42).unwrap();
    /// ```
    pub fn mixed(&mut self, tick: u64) -> Result<T, SnowflakeError> {
        let raw = self.next(tick)?;
        Ok(T::from_raw(fibonacci_mix_64(raw.to_raw())))
    }

    /// Unpack an ID into (timestamp, worker, sequence).
    ///
    /// # Example
    /// ```rust
    /// use nexus_id::Snowflake64;
    ///
    /// type MyId = Snowflake64<42, 6, 16>;
    ///
    /// let mut id_gen = MyId::new(5);
    ///
    /// let id = id_gen.next(0).unwrap();
    /// let (ts, worker, seq) = MyId::unpack(id);
    ///
    /// assert_eq!(ts, 0);
    /// assert_eq!(worker, 5);
    /// assert_eq!(seq, 0);
    /// ```
    pub fn unpack(id: T) -> (u64, u64, u64) {
        let raw = id.to_raw();
        (
            raw >> Self::TS_SHIFT,
            (raw >> Self::WK_SHIFT) & Self::WORKER_MAX,
            raw & Self::SEQUENCE_MAX,
        )
    }

    /// Worker ID for this generator.
    #[inline]
    pub const fn worker(&self) -> u64 {
        self.worker_shifted >> Self::WK_SHIFT
    }

    /// Current sequence within this millisecond.
    #[inline]
    pub const fn sequence(&self) -> u64 {
        self.sequence
    }

    /// Last tick value used.
    #[inline]
    pub const fn last_tick(&self) -> u64 {
        self.last_tick
    }
}

// Type aliases for convenience

/// 32-bit snowflake generator.
pub type Snowflake32<const TS: u8, const WK: u8, const SQ: u8> = Snowflake<u32, TS, WK, SQ>;

/// 64-bit snowflake generator.
pub type Snowflake64<const TS: u8, const WK: u8, const SQ: u8> = Snowflake<u64, TS, WK, SQ>;

/// Signed 32-bit snowflake generator.
pub type SnowflakeSigned32<const TS: u8, const WK: u8, const SQ: u8> = Snowflake<i32, TS, WK, SQ>;

/// Signed 64-bit snowflake generator.
pub type SnowflakeSigned64<const TS: u8, const WK: u8, const SQ: u8> = Snowflake<i64, TS, WK, SQ>;

/// Fibonacci multiply for 64-bit hash mixing.
///
/// Bijective permutation (~1 cycle). Spreads structured snowflake bits
/// uniformly across all positions for identity hasher compatibility.
#[inline(always)]
const fn fibonacci_mix_64(x: u64) -> u64 {
    x.wrapping_mul(0x9E37_79B9_7F4A_7C15)
}

// =============================================================================
// Typed ID generation (u64)
// =============================================================================

impl<const TS: u8, const WK: u8, const SQ: u8> Snowflake<u64, TS, WK, SQ> {
    /// Generate the next ID as a typed [`SnowflakeId64`].
    ///
    /// Same as [`next()`](Self::next) but returns the newtype wrapper with
    /// field extraction and mixing methods.
    #[inline]
    pub fn next_id(&mut self, tick: u64) -> Result<SnowflakeId64<TS, WK, SQ>, SnowflakeError> {
        self.next(tick).map(SnowflakeId64::from_raw)
    }

    /// Generate a Fibonacci-mixed ID as a typed [`MixedId64`].
    ///
    /// The mixed ID can be unmixed back to the original via [`MixedId64::unmix()`].
    #[inline]
    pub fn next_mixed(&mut self, tick: u64) -> Result<MixedId64<TS, WK, SQ>, SnowflakeError> {
        self.next_id(tick).map(|id| id.mixed())
    }
}

// =============================================================================
// Typed ID generation (u32)
// =============================================================================

impl<const TS: u8, const WK: u8, const SQ: u8> Snowflake<u32, TS, WK, SQ> {
    /// Generate the next ID as a typed [`SnowflakeId32`].
    #[inline]
    pub fn next_id(&mut self, tick: u64) -> Result<SnowflakeId32<TS, WK, SQ>, SnowflakeError> {
        self.next(tick).map(SnowflakeId32::from_raw)
    }

    /// Generate a Fibonacci-mixed ID as a typed [`MixedId32`].
    #[inline]
    pub fn next_mixed(&mut self, tick: u64) -> Result<MixedId32<TS, WK, SQ>, SnowflakeError> {
        self.next_id(tick).map(|id| id.mixed())
    }
}

#[cfg(all(test, feature = "std"))]
mod tests {
    use super::*;

    type TestId = Snowflake64<42, 6, 16>;

    #[test]
    fn basic_generation() {
        let mut id_gen = TestId::new(5);

        let id = id_gen.next(0).unwrap();
        let (ts, worker, seq) = TestId::unpack(id);

        assert_eq!(ts, 0);
        assert_eq!(worker, 5);
        assert_eq!(seq, 0);
    }

    #[test]
    fn sequence_increments_same_ts() {
        let mut id_gen = TestId::new(5);

        let id1 = id_gen.next(0).unwrap();
        let id2 = id_gen.next(0).unwrap();
        let id3 = id_gen.next(0).unwrap();

        let (_, _, seq1) = TestId::unpack(id1);
        let (_, _, seq2) = TestId::unpack(id2);
        let (_, _, seq3) = TestId::unpack(id3);

        assert_eq!(seq1, 0);
        assert_eq!(seq2, 1);
        assert_eq!(seq3, 2);
    }

    #[test]
    fn sequence_resets_new_ts() {
        let mut id_gen = TestId::new(5);

        // Generate at timestamp 0
        let _ = id_gen.next(0).unwrap();
        let _ = id_gen.next(0).unwrap();

        // Jump to timestamp 1
        let id = id_gen.next(1).unwrap();

        let (ts, _, seq) = TestId::unpack(id);
        assert_eq!(ts, 1);
        assert_eq!(seq, 0);
    }

    #[test]
    fn worker_encoded_correctly() {
        for worker in [0, 1, 31, 63] {
            let mut id_gen = TestId::new(worker);
            let id = id_gen.next(0).unwrap();
            let (_, w, _) = TestId::unpack(id);
            assert_eq!(w, worker);
        }
    }

    #[test]
    fn ids_are_unique() {
        let mut id_gen = TestId::new(5);

        let mut ids = Vec::new();
        for i in 0..1000u64 {
            // Advance timestamp every 100 IDs
            let ts = i / 100;
            ids.push(id_gen.next(ts).unwrap());
        }

        // Check uniqueness
        let mut sorted = ids.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(sorted.len(), ids.len());
    }

    #[test]
    fn sequence_exhaustion() {
        // Tiny sequence: 4 bits = max 15
        type TinySeq = Snowflake64<42, 6, 4>;

        let mut id_gen = TinySeq::new(5);

        // Generate 16 IDs (0-15)
        for _ in 0..16 {
            id_gen.next(0).unwrap();
        }

        // 17th should fail
        let result = id_gen.next(0);
        assert!(result.is_err());

        let SnowflakeError::Exhausted(err) = result.unwrap_err() else {
            panic!("expected Exhausted");
        };
        assert_eq!(err.max_sequence, 15);
    }

    #[test]
    #[should_panic(expected = "worker 100 exceeds max 63")]
    fn worker_overflow_panics() {
        let _id_gen = TestId::new(100); // 6 bits = max 63
    }

    #[test]
    fn signed_output() {
        type SignedId = SnowflakeSigned64<42, 6, 16>;

        let mut id_gen = SignedId::new(5);

        let id: i64 = id_gen.next(0).unwrap();
        let (ts, worker, seq) = SignedId::unpack(id);

        assert_eq!(ts, 0);
        assert_eq!(worker, 5);
        assert_eq!(seq, 0);
    }

    #[test]
    fn small_layout_32bit() {
        // 20 bits timestamp, 4 bits worker, 8 bits sequence
        type SmallId = Snowflake32<20, 4, 8>;

        let mut id_gen = SmallId::new(7);

        let id: u32 = id_gen.next(0).unwrap();
        let (ts, worker, seq) = SmallId::unpack(id);

        assert_eq!(ts, 0);
        assert_eq!(worker, 7);
        assert_eq!(seq, 0);
    }

    #[test]
    fn zero_worker_bits() {
        // Single-worker system: no worker bits
        type SingleWorker = Snowflake64<48, 0, 16>;

        let mut id_gen = SingleWorker::new(0);

        let id = id_gen.next(0).unwrap();
        let (ts, worker, seq) = SingleWorker::unpack(id);

        assert_eq!(ts, 0);
        assert_eq!(worker, 0);
        assert_eq!(seq, 0);
    }

    #[test]
    fn non_time_timestamp() {
        // Use block numbers as timestamp
        type BlockId = Snowflake64<32, 8, 24>;

        let mut id_gen = BlockId::new(1);

        let id1 = id_gen.next(1000).unwrap(); // block 1000
        let id2 = id_gen.next(1000).unwrap(); // same block
        let id3 = id_gen.next(1001).unwrap(); // next block

        let (ts1, _, seq1) = BlockId::unpack(id1);
        let (ts2, _, seq2) = BlockId::unpack(id2);
        let (ts3, _, seq3) = BlockId::unpack(id3);

        assert_eq!(ts1, 1000);
        assert_eq!(seq1, 0);
        assert_eq!(ts2, 1000);
        assert_eq!(seq2, 1);
        assert_eq!(ts3, 1001);
        assert_eq!(seq3, 0);
    }

    #[test]
    fn timestamp_overflow_is_rejected() {
        // Snowflake64<2,0,62>: TIMESTAMP_MAX = 3 (2 TS bits).
        // tick=4 silently truncates to 0 without the check, producing the same
        // raw ID as tick=0.
        type Tiny = Snowflake64<2, 0, 62>;
        let mut g = Tiny::new(0);
        assert!(g.next(3).is_ok());
        assert!(matches!(
            g.next(4),
            Err(SnowflakeError::TimestampOverflow { tick: 4, max: 3 })
        ));
    }
}
