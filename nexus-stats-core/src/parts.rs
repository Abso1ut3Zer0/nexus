//! The parts the statistics are built from: small pieces of state that
//! several types share. Operations on numbers are in [`math`](crate::math).

use core::time::Duration;

use crate::Timestamp;
use crate::math::{MulAdd, alpha_from_span, in_unit_interval};
#[cfg(any(feature = "std", feature = "libm"))]
use crate::math::{alpha_from_halflife, positive_finite, sqrt};

/// An estimate of the rounding error a running total has accumulated.
///
/// Each add to a total is rounded by up to half a unit in the last place
/// of the result, so the error depends on how large the total was at each
/// add. It stays in the total, and matters once the total has become much
/// smaller than it was: this is for totals that are added to and removed
/// from, as over a sliding window.
///
/// This treats each add's error as independent and equally likely to fall
/// either way, with variance `(f64::EPSILON * total)^2 / 12`. The errors
/// then partly cancel, and their sum is close to normal (Higham and Mary,
/// 2019, "A New Approach to Probabilistic Rounding Error Analysis"). It
/// describes the error seen in practice; it is not a guarantee. See
/// [`RoundingBound`] for one.
///
/// # Examples
///
/// ```
/// use nexus_stats_core::parts::RoundingEstimate;
///
/// let mut rounding = RoundingEstimate::new();
/// let mut total = 0.0;
/// for x in [1e8, 2.5, -1e8] {
///     total += x;
///     rounding.record(total);
/// }
/// // Four standard deviations: what `total` may be off by.
/// let error = rounding.error(4.0);
/// assert!(error > 1e-8 && error < 1e-7);
/// ```
#[derive(Debug, Clone, Copy, Default, PartialEq)]
pub struct RoundingEstimate {
    /// Sum over the adds of the total squared.
    squares: f64,
    adds: usize,
}

impl RoundingEstimate {
    /// Creates an estimate with no adds recorded.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            squares: 0.0,
            adds: 0,
        }
    }

    /// Records one add that left the total at `total`.
    #[inline]
    pub fn record(&mut self, total: f64) {
        self.record_n(total, 1);
    }

    /// Records `adds` adds, each of which left a total near `total`.
    #[inline]
    pub fn record_n(&mut self, total: f64, adds: usize) {
        self.squares = (total * adds as f64).fma(total, self.squares);
        self.adds += adds;
    }

    /// The variance of the accumulated rounding error.
    #[inline]
    #[must_use]
    pub fn variance(&self) -> f64 {
        Self::variance_of(1.0, 1) * self.squares
    }

    /// The accumulated rounding error at `confidence` standard deviations.
    ///
    /// At 4, a normal error is larger about once in 16,000.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[inline]
    #[must_use]
    pub fn error(&self, confidence: f64) -> f64 {
        confidence * sqrt(self.variance())
    }

    /// The variance of the rounding error of `adds` adds that each leave a
    /// total near `total`: `adds * (f64::EPSILON * total)^2 / 12`.
    #[inline]
    #[must_use]
    pub fn variance_of(total: f64, adds: usize) -> f64 {
        let rounding = f64::EPSILON * total;
        rounding * rounding * (adds as f64 / 12.0)
    }

    /// The number of adds recorded.
    #[inline]
    #[must_use]
    pub const fn adds(&self) -> usize {
        self.adds
    }

    /// Forgets every add, as when the total is recomputed.
    #[inline]
    pub fn reset(&mut self) {
        *self = Self::new();
    }
}

/// A bound on the rounding error a running total has accumulated.
///
/// The worst case of what [`RoundingEstimate`] estimates: every add is
/// taken to be off by the full half unit in the last place,
/// `f64::EPSILON / 2 * |total|`, all in the same direction. The total's
/// error cannot be larger, as long as no add overflowed or was not a
/// number. It grows with the number of adds where the estimate grows with
/// its square root, so over a long run it is far above the error seen.
///
/// # Examples
///
/// ```
/// use nexus_stats_core::parts::RoundingBound;
///
/// let mut rounding = RoundingBound::new();
/// let mut total = 0.0;
/// for x in [1e8, 2.5, -1e8] {
///     total += x;
///     rounding.record(total);
/// }
/// assert!((total - 2.5).abs() <= rounding.error());
/// ```
#[derive(Debug, Clone, Copy, Default, PartialEq)]
pub struct RoundingBound {
    /// Sum over the adds of the total's size.
    sizes: f64,
    adds: usize,
}

impl RoundingBound {
    /// Creates a bound with no adds recorded.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            sizes: 0.0,
            adds: 0,
        }
    }

    /// Records one add that left the total at `total`.
    #[inline]
    pub fn record(&mut self, total: f64) {
        self.record_n(total, 1);
    }

    /// Records `adds` adds, each of which left a total no larger than
    /// `total` in size.
    #[inline]
    pub fn record_n(&mut self, total: f64, adds: usize) {
        self.sizes = (adds as f64).fma(total.abs(), self.sizes);
        self.adds += adds;
    }

    /// The most the total can be off by.
    #[inline]
    #[must_use]
    pub fn error(&self) -> f64 {
        // Rounded up a little, so that summing the sizes cannot undercut it.
        (0.5 * f64::EPSILON) * self.sizes * (self.adds as f64).fma(f64::EPSILON, 1.0)
    }

    /// The number of adds recorded.
    #[inline]
    #[must_use]
    pub const fn adds(&self) -> usize {
        self.adds
    }

    /// Forgets every add, as when the total is recomputed.
    #[inline]
    pub fn reset(&mut self) {
        *self = Self::new();
    }
}

/// The latest time a clocked type has taken, and the rule that time must
/// not go back.
#[doc(hidden)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LastTime<T: Timestamp> {
    last: Option<T>,
}

impl<T: Timestamp> LastTime<T> {
    /// No time taken yet.
    #[must_use]
    pub const fn new() -> Self {
        Self { last: None }
    }

    /// Starting from `time`, as if it had been taken.
    #[must_use]
    pub const fn starting_at(time: T) -> Self {
        Self { last: Some(time) }
    }

    /// The latest time taken, or `None` before the first.
    #[inline]
    #[must_use]
    pub fn get(self) -> Option<T> {
        self.last
    }

    /// Whether `time` is before the latest time taken, so that taking it
    /// would go back.
    #[inline]
    #[must_use]
    pub fn would_go_back(self, time: T) -> bool {
        self.last.is_some_and(|last| time < last)
    }

    /// `Ok` if `time` may be taken.
    ///
    /// # Errors
    ///
    /// [`DataError::NonMonotonicTime`](crate::DataError::NonMonotonicTime)
    /// if `time` is before the latest time taken.
    #[inline]
    pub fn check(self, time: T) -> Result<(), crate::DataError> {
        if self.would_go_back(time) {
            return Err(crate::DataError::NonMonotonicTime);
        }
        Ok(())
    }

    /// The time from the latest one taken to `time`: zero if `time` is not
    /// after it, `None` before the first.
    #[inline]
    #[must_use]
    pub fn elapsed_to(self, time: T) -> Option<Duration> {
        Some(time.since(self.last?))
    }

    /// Takes `time` as the latest.
    #[inline]
    pub fn set(&mut self, time: T) {
        self.last = Some(time);
    }

    /// Back to no time taken.
    pub fn reset(&mut self) {
        self.last = None;
    }
}

impl<T: Timestamp> Default for LastTime<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// The warm-up of a streaming type: samples fed, and how many are needed
/// before it gives a reading.
#[doc(hidden)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Warmup {
    count: u64,
    prime_at: u64,
}

impl Warmup {
    /// A warm-up of `min_samples` samples. `seeded` types need none: they
    /// have a reading from the start.
    #[must_use]
    pub const fn new(min_samples: u64, seeded: bool) -> Self {
        Self {
            count: 0,
            prime_at: if seeded { 0 } else { min_samples },
        }
    }

    /// Counts one sample and returns the new count.
    #[inline]
    pub fn tick(&mut self) -> u64 {
        self.count += 1;
        self.count
    }

    /// Samples counted since construction or the last reset.
    #[inline]
    #[must_use]
    pub fn count(self) -> u64 {
        self.count
    }

    /// Whether the next sample is the starting value: none counted yet,
    /// and no seed to start from.
    #[inline]
    #[must_use]
    pub fn awaits_first_sample(self) -> bool {
        self.count == 0 && self.prime_at != 0
    }

    /// Whether enough samples have been counted for a reading.
    #[inline]
    #[must_use]
    pub fn is_primed(self) -> bool {
        self.count >= self.prime_at
    }

    /// Back to no samples. The samples needed are unchanged.
    pub fn reset(&mut self) {
        self.count = 0;
    }

    /// Back to no samples, with a seed: a reading is available at once.
    pub fn reset_seeded(&mut self) {
        self.count = 0;
        self.prime_at = 0;
    }
}

/// A smoothing weight with its complement, `1 - alpha`.
#[doc(hidden)]
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Weight {
    alpha: f64,
    complement: f64,
}

impl Weight {
    /// The weight `alpha`. Not validated: resolve an [`EwWeight`] first.
    #[must_use]
    pub fn new(alpha: f64) -> Self {
        Self {
            alpha,
            complement: 1.0 - alpha,
        }
    }

    /// The weight itself.
    #[must_use]
    pub fn alpha(self) -> f64 {
        self.alpha
    }

    /// `1 - alpha`.
    #[inline]
    #[must_use]
    pub fn complement(self) -> f64 {
        self.complement
    }

    /// `alpha * new + (1 - alpha) * old`.
    #[inline]
    #[must_use]
    pub fn blend(self, new: f64, old: f64) -> f64 {
        self.alpha.fma(new, self.complement * old)
    }
}

/// How a builder was told its exponential weight: directly, as a half-life,
/// or as a span. Builders store the knob the caller set and resolve it in
/// `build`, so a bad value is reported under the name the caller used.
#[doc(hidden)]
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum EwWeight {
    /// The weight itself, in `(0, 1)`.
    Alpha(f64),
    /// Samples for a weight to decay by half; positive and finite.
    #[cfg(any(feature = "std", feature = "libm"))]
    Halflife(f64),
    /// Pandas `span`; at least 2.
    Span(u64),
}

impl EwWeight {
    /// The smallest usable weight: half of machine epsilon.
    ///
    /// Our choice. Below it `1 - alpha` rounds to 1 and nothing is ever
    /// forgotten. The `halflife` knob already stops here, by rounding.
    const SMALLEST: f64 = f64::EPSILON / 2.0;

    /// The weight in `(0, 1)`.
    ///
    /// # Errors
    ///
    /// `ConfigError::Invalid` naming the knob that was set: `alpha` outside
    /// `(0, 1)`, a `halflife` that is not positive and finite, a `span`
    /// below 2, or any of the three giving a weight too small to use.
    pub fn resolve(self) -> Result<f64, crate::ConfigError> {
        match self {
            Self::Alpha(alpha) => Self::from_alpha(alpha),
            #[cfg(any(feature = "std", feature = "libm"))]
            Self::Halflife(halflife) => Self::from_halflife(halflife),
            Self::Span(span) => Self::from_span(span),
        }
    }

    /// `alpha` itself, if it is in `(0, 1)` and large enough to use.
    fn from_alpha(alpha: f64) -> Result<f64, crate::ConfigError> {
        if !in_unit_interval(alpha) {
            return Err(crate::ConfigError::Invalid("alpha must be in (0, 1)"));
        }
        if alpha < Self::SMALLEST {
            return Err(crate::ConfigError::Invalid(
                "alpha is too small for a usable weight",
            ));
        }
        Ok(alpha)
    }

    /// The weight for a half-life in samples.
    #[cfg(any(feature = "std", feature = "libm"))]
    fn from_halflife(halflife: f64) -> Result<f64, crate::ConfigError> {
        if !positive_finite(halflife) {
            return Err(crate::ConfigError::Invalid(
                "halflife must be positive and finite",
            ));
        }
        // A half-life so short that `1 - exp(-x)` rounds to one, or so long
        // that it rounds to zero, has no usable weight.
        let alpha = alpha_from_halflife(halflife);
        if !in_unit_interval(alpha) {
            return Err(crate::ConfigError::Invalid(
                "halflife is too small or too large for a usable weight",
            ));
        }
        Ok(alpha)
    }

    /// The weight for a pandas `span`.
    fn from_span(span: u64) -> Result<f64, crate::ConfigError> {
        if span < 2 {
            return Err(crate::ConfigError::Invalid("span must be at least 2"));
        }
        let alpha = alpha_from_span(span);
        if alpha < Self::SMALLEST {
            return Err(crate::ConfigError::Invalid(
                "span is too large for a usable weight",
            ));
        }
        Ok(alpha)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Uniform values in `[-1, 1)`.
    fn noise(state: &mut u64) -> f64 {
        *state ^= *state << 13;
        *state ^= *state >> 7;
        *state ^= *state << 17;
        (*state >> 11) as f64 / (1u64 << 52) as f64 - 1.0
    }

    /// A sliding-window sum of `values * scale(i)`, kept as a running total
    /// in `f64`, against the same window summed exactly: the error at the
    /// end, with the trackers that watched every add.
    fn running_total_error(
        seed: u64,
        steps: usize,
        scale: impl Fn(usize) -> f64,
    ) -> (f64, RoundingEstimate, RoundingBound) {
        extern crate std;
        const WINDOW: usize = 64;
        let mut state = seed;
        let mut window = std::collections::VecDeque::new();
        let mut total = 0.0f64;
        let (mut estimate, mut bound) = (RoundingEstimate::new(), RoundingBound::new());
        for i in 0..steps {
            let x = noise(&mut state) * scale(i);
            if window.len() == WINDOW {
                total -= window.pop_front().unwrap();
                estimate.record(total);
                bound.record(total);
            }
            window.push_back(x);
            total += x;
            estimate.record(total);
            bound.record(total);
        }
        // Every value is a multiple of 2^-80 below 2^10: exact in i128.
        let exact: i128 = window.iter().map(|x| (x * 2f64.powi(80)) as i128).sum();
        let error = (total * 2f64.powi(80)) as i128 - exact;
        (error as f64 / 2f64.powi(80), estimate, bound)
    }

    #[test]
    fn the_rounding_trackers_cover_a_running_total_that_shrinks() {
        // Values near 1 for a long spell, then a million times smaller: the
        // error left from the busy spell is what remains.
        let scale = |i: usize| if i < 50_000 { 1.0 } else { 2f64.powi(-20) };
        let mut within_one_sd = 0;
        for seed in 1..=200u64 {
            let (error, estimate, bound) = running_total_error(seed, 50_200, scale);
            assert!(error != 0.0, "seed {seed}: no rounding to measure");
            assert!(error.abs() <= bound.error(), "seed {seed}");
            assert!(error.abs() <= estimate.error(4.0), "seed {seed}");
            // The bound grows with the adds, the estimate with their root.
            assert!(bound.error() > 50.0 * estimate.error(1.0), "seed {seed}");
            within_one_sd += usize::from(error.abs() <= estimate.error(1.0));
        }
        // The estimate is the right size, not merely large: about 68% of
        // normal errors fall inside one standard deviation.
        assert!((100..=190).contains(&within_one_sd), "{within_one_sd}");
    }

    #[test]
    fn the_rounding_trackers_count_and_reset() {
        let eps = f64::EPSILON;
        let mut estimate = RoundingEstimate::new();
        estimate.record(3.0);
        estimate.record_n(-2.0, 4);
        assert_eq!(estimate.adds(), 5);
        // 3^2 + 4 * 2^2 = 25, over 12.
        let close = |got: f64, want: f64| (got - want).abs() <= 1e-12 * want;
        assert!(close(estimate.variance(), eps * eps * 25.0 / 12.0));
        assert_eq!(estimate.error(2.0), 2.0 * super::sqrt(estimate.variance()));
        assert!(close(
            RoundingEstimate::variance_of(-2.0, 4),
            eps * eps * 16.0 / 12.0
        ));
        estimate.reset();
        assert_eq!(estimate, RoundingEstimate::new());
        assert_eq!((estimate.adds(), estimate.error(4.0)), (0, 0.0));

        let mut bound = RoundingBound::new();
        bound.record(3.0);
        bound.record_n(-2.0, 4);
        assert_eq!(bound.adds(), 5);
        // 3 + 4 * 2 = 11 half units, and never less.
        assert!(bound.error() >= 0.5 * eps * 11.0);
        assert!(close(bound.error(), 0.5 * eps * 11.0));
        bound.reset();
        assert_eq!((bound.adds(), bound.error()), (0, 0.0));
    }

    #[test]
    fn a_weight_too_small_to_use_is_refused_under_every_knob() {
        use super::EwWeight::{Alpha, Span};
        use crate::ConfigError::Invalid;

        let smallest = f64::EPSILON / 2.0;
        assert_eq!(Alpha(smallest).resolve(), Ok(smallest));
        let too_small = Err(Invalid("alpha is too small for a usable weight"));
        assert_eq!(Alpha(smallest / 2.0).resolve(), too_small);
        assert_eq!(Alpha(5e-324).resolve(), too_small);

        assert!(Span(1 << 50).resolve().is_ok());
        assert_eq!(
            Span(u64::MAX).resolve(),
            Err(Invalid("span is too large for a usable weight"))
        );
    }

    #[cfg(any(feature = "std", feature = "libm"))]
    #[test]
    fn a_halflife_too_long_to_use_is_refused() {
        use super::EwWeight::Halflife;
        use crate::ConfigError::Invalid;

        assert!(Halflife(10.0).resolve().is_ok());
        assert_eq!(
            Halflife(1e18).resolve(),
            Err(Invalid(
                "halflife is too small or too large for a usable weight"
            ))
        );
    }
}
