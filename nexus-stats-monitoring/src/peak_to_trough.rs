use core::ops::Sub;

/// The fall from a running high: how far the signal is below the highest
/// value it has reached, and the largest such fall so far.
///
/// Works for any number type that can be compared and subtracted, so a
/// caller's own decimal or fixed-point type fits as well as `f64` and
/// `i64`. The first sample is the first high. Values of either sign are
/// fine. The fall is an amount, and nothing is divided.
///
/// On P&L or equity, the current fall is the drawdown and the largest
/// fall is the maximum drawdown, both as amounts.
///
/// # Weighting clock
///
/// None. The reading depends on the order of the samples only, not on how
/// often they arrive.
///
/// # Examples
///
/// ```
/// use nexus_stats_monitoring::PeakToTrough;
///
/// let mut fall = PeakToTrough::new();
/// for x in [100, 120, 90, 110] {
///     fall.update(x);
/// }
/// let reading = fall.reading().unwrap();
/// assert_eq!((reading.high, reading.current, reading.largest), (120, 10, 30));
/// ```
#[derive(Debug, Clone)]
pub struct PeakToTrough<T> {
    state: Option<Fall<T>>,
    count: u64,
}

/// A [`PeakToTrough`] reading.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Fall<T> {
    /// The highest sample so far.
    pub high: T,
    /// How far the latest sample is below the high. Zero at a new high.
    pub current: T,
    /// The largest fall so far.
    pub largest: T,
}

/// The largest magnitude `PeakToTrough<f64>::checked_update` takes: the
/// fall between any two such samples is finite.
const LARGEST_SAMPLE: f64 = f64::MAX / 2.0;

impl<T> PeakToTrough<T> {
    /// Creates an empty tracker.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            state: None,
            count: 0,
        }
    }

    /// Samples fed since construction or `reset`.
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether at least one sample has been fed.
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count > 0
    }

    /// Forgets the high and both falls.
    pub fn reset(&mut self) {
        self.state = None;
        self.count = 0;
    }
}

impl<T: Copy + PartialOrd + Sub<Output = T>> PeakToTrough<T> {
    /// Feeds a sample and returns the reading: the high, the fall from it
    /// (zero at a new high) and the largest fall.
    ///
    /// Does the arithmetic and nothing else. The subtraction is the
    /// type's own: for `i64` it overflows as `-` does, and for `f64` a NaN
    /// or an infinity follows IEEE 754:
    ///
    /// - An infinite high never comes down.
    /// - A NaN first sample makes every reading NaN until `reset`.
    /// - An infinite first sample leaves the largest fall NaN.
    /// - A later NaN gives a NaN current fall for that sample only.
    ///
    /// `PeakToTrough<f64>` and `PeakToTrough<i64>` have a `checked_update`.
    #[inline]
    pub fn update(&mut self, sample: T) -> Fall<T> {
        self.count += 1;
        let next = self
            .state
            .map_or_else(|| Fall::starting_at(sample), |fall| fall.after(sample));
        self.state = Some(next);
        next
    }

    /// The high, the fall from it and the largest fall, or `None` before
    /// the first sample.
    #[must_use]
    pub fn reading(&self) -> Option<Fall<T>> {
        self.state
    }
}

impl PeakToTrough<f64> {
    /// Checked update. Feeds `sample`, or returns an error and leaves the
    /// tracker unchanged if `sample` is NaN, infinite, or larger in
    /// magnitude than half of `f64::MAX`.
    ///
    /// An infinite high never comes down, and two finite samples further
    /// apart than `f64::MAX` have an infinite fall between them. Either
    /// would last until [`reset`](Self::reset).
    ///
    /// # Errors
    ///
    /// - [`DataError::NotANumber`](nexus_stats_core::DataError::NotANumber)
    ///   if `sample` is NaN.
    /// - [`DataError::Infinite`](nexus_stats_core::DataError::Infinite) if
    ///   `sample` is infinite.
    /// - [`DataError::OutOfRange`](nexus_stats_core::DataError::OutOfRange)
    ///   if `sample` is larger in magnitude than `f64::MAX / 2`.
    #[inline]
    pub fn checked_update(
        &mut self,
        sample: f64,
    ) -> Result<Fall<f64>, nexus_stats_core::DataError> {
        nexus_stats_core::math::check_input(sample, LARGEST_SAMPLE)?;
        Ok(self.update(sample))
    }
}

impl PeakToTrough<i64> {
    /// Checked update. Feeds `sample`, or returns an error and leaves the
    /// tracker unchanged if the fall from the high would overflow.
    ///
    /// # Errors
    ///
    /// [`DataError::OutOfRange`](nexus_stats_core::DataError::OutOfRange)
    /// if `high - sample` does not fit in an `i64`.
    #[inline]
    pub fn checked_update(
        &mut self,
        sample: i64,
    ) -> Result<Fall<i64>, nexus_stats_core::DataError> {
        let high = self.state.map_or(sample, |state| state.high.max(sample));
        if high.checked_sub(sample).is_none() {
            return Err(nexus_stats_core::DataError::OutOfRange);
        }
        Ok(self.update(sample))
    }
}

impl<T: Copy + PartialOrd + Sub<Output = T>> Fall<T> {
    /// The reading after the first sample: it is the high, with no fall.
    #[inline]
    fn starting_at(sample: T) -> Self {
        // Zero in the caller's type, which need not have a constant for it.
        #[allow(clippy::eq_op)]
        let zero = sample - sample;
        Self {
            high: sample,
            current: zero,
            largest: zero,
        }
    }

    /// The reading after one more sample.
    #[inline]
    fn after(self, sample: T) -> Self {
        // PERF: selects, not branches. On a trending signal a new high is
        // a coin flip for the predictor.
        let high = if sample > self.high {
            sample
        } else {
            self.high
        };
        let current = high - sample;
        let largest = if current > self.largest {
            current
        } else {
            self.largest
        };
        Self {
            high,
            current,
            largest,
        }
    }
}

impl<T> Default for PeakToTrough<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use nexus_stats_core::DataError::{Infinite, NotANumber, OutOfRange};

    fn reading<T: Copy + PartialOrd + Sub<Output = T>>(t: &PeakToTrough<T>) -> (T, T, T) {
        let r = t.reading().unwrap();
        (r.high, r.current, r.largest)
    }

    #[test]
    fn nothing_is_read_before_the_first_sample() {
        let t = PeakToTrough::<f64>::new();
        assert_eq!((t.reading(), t.count(), t.is_primed()), (None, 0, false));
        assert_eq!(PeakToTrough::<i64>::default().reading(), None);
    }

    #[test]
    fn the_first_sample_is_the_high_whatever_its_sign() {
        let mut t = PeakToTrough::new();
        assert_eq!(t.update(-50.0).current, 0.0);
        assert_eq!(reading(&t), (-50.0, 0.0, 0.0));
        assert_eq!(t.update(-80.0).current, 30.0);
        assert_eq!(reading(&t), (-50.0, 30.0, 30.0));
    }

    #[test]
    fn the_fall_is_measured_from_the_running_high() {
        let mut t = PeakToTrough::new();
        let falls: Vec<i64> = [100, 120, 90, 110, 130, 125]
            .into_iter()
            .map(|x| t.update(x).current)
            .collect();
        assert_eq!(falls, [0, 0, 30, 10, 0, 5]);
        assert_eq!(reading(&t), (130, 5, 30));
    }

    /// Against the definition, `max over earlier samples of (high - x)`.
    #[test]
    fn matches_the_definition_on_a_random_walk() {
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        let mut t = PeakToTrough::new();
        let (mut x, mut high, mut largest) = (0i64, i64::MIN, 0i64);
        for _ in 0..50_000 {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            x += (state % 201) as i64 - 100;
            high = high.max(x);
            largest = largest.max(high - x);
            assert_eq!(t.update(x).current, high - x);
            assert_eq!(reading(&t), (high, high - x, largest));
        }
    }

    #[test]
    fn a_rising_signal_never_falls() {
        let mut t = PeakToTrough::new();
        for i in 0..100 {
            assert_eq!(t.update(f64::from(i)).current, 0.0);
        }
        assert_eq!(t.reading().unwrap().largest, 0.0);
    }

    #[test]
    fn reset_forgets_everything() {
        let mut t = PeakToTrough::new();
        t.update(100.0);
        t.update(40.0);
        t.reset();
        assert_eq!((t.reading(), t.count()), (None, 0));
        assert_eq!(t.update(10.0).current, 0.0);
        assert_eq!(reading(&t), (10.0, 0.0, 0.0));
    }

    /// Only comparison and subtraction are needed: a caller's own type
    /// works.
    #[test]
    fn a_callers_number_type_works() {
        #[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
        struct Cents(i32);
        impl Sub for Cents {
            type Output = Self;
            fn sub(self, other: Self) -> Self {
                Self(self.0 - other.0)
            }
        }
        let mut t = PeakToTrough::new();
        for c in [500, 700, 450] {
            t.update(Cents(c));
        }
        assert_eq!(reading(&t), (Cents(700), Cents(250), Cents(250)));
    }

    #[test]
    fn checked_update_refuses_nan_and_infinity_and_changes_nothing() {
        let mut t = PeakToTrough::<f64>::new();
        assert_eq!(t.checked_update(f64::INFINITY), Err(Infinite));
        assert_eq!((t.reading(), t.count()), (None, 0));
        t.checked_update(10.0).unwrap();
        t.checked_update(4.0).unwrap();
        let before = (t.reading(), t.count());
        assert_eq!(t.checked_update(f64::NAN), Err(NotANumber));
        assert_eq!(t.checked_update(f64::NEG_INFINITY), Err(Infinite));
        assert_eq!((t.reading(), t.count()), before);
    }

    #[test]
    fn checked_update_refuses_an_integer_fall_that_overflows() {
        let mut t = PeakToTrough::<i64>::new();
        assert_eq!(t.checked_update(i64::MAX).map(|r| r.current), Ok(0));
        let before = (t.reading(), t.count());
        // MAX - (-2) does not fit.
        assert_eq!(t.checked_update(-2), Err(OutOfRange));
        assert_eq!(t.checked_update(i64::MIN), Err(OutOfRange));
        assert_eq!((t.reading(), t.count()), before);
        // The largest fall that fits is taken.
        assert_eq!(t.checked_update(0).map(|r| r.current), Ok(i64::MAX));
        // A new high after a low is measured from the new high.
        let mut t = PeakToTrough::<i64>::new();
        t.checked_update(i64::MIN).unwrap();
        assert_eq!(t.checked_update(i64::MAX).map(|r| r.current), Ok(0));
    }

    #[test]
    fn checked_update_gives_the_same_result_as_update() {
        let (mut checked, mut plain) = (PeakToTrough::<f64>::new(), PeakToTrough::new());
        for x in [
            5.0,
            -2.0,
            1e300,
            -1e300,
            f64::MAX / 2.0,
            f64::MIN / 2.0,
            0.0,
        ] {
            assert_eq!(checked.checked_update(x), Ok(plain.update(x)));
        }
        let (mut checked, mut plain) = (PeakToTrough::<i64>::new(), PeakToTrough::new());
        for x in [5, -2, 900, i64::MAX / 2, -i64::MAX / 2, 0] {
            assert_eq!(checked.checked_update(x), Ok(plain.update(x)));
        }
    }

    /// Two finite samples can be an infinite distance apart. The guarded
    /// form keeps every sample within half the range, so no fall is.
    #[test]
    fn checked_update_refuses_a_sample_too_large_to_measure_from() {
        let mut plain = PeakToTrough::new();
        plain.update(f64::MAX);
        assert_eq!(plain.update(f64::MIN).largest, f64::INFINITY);

        let mut t = PeakToTrough::<f64>::new();
        assert_eq!(t.checked_update(f64::MAX), Err(OutOfRange));
        assert_eq!(t.checked_update(f64::MIN), Err(OutOfRange));
        assert_eq!((t.reading(), t.count()), (None, 0));
        t.checked_update(f64::MAX / 2.0).unwrap();
        let fall = t.checked_update(f64::MIN / 2.0).unwrap();
        assert_eq!(fall.largest, f64::MAX);
    }

    /// What the unchecked form does with what the checked form refuses.
    #[test]
    fn an_infinite_high_never_comes_down() {
        let mut t = PeakToTrough::new();
        t.update(1.0);
        t.update(f64::INFINITY);
        assert_eq!(t.update(5.0).current, f64::INFINITY);
        assert_eq!(t.reading().unwrap().high, f64::INFINITY);
        // As the first sample it also leaves the largest fall undefined.
        let mut t = PeakToTrough::new();
        t.update(f64::INFINITY);
        assert!(t.update(5.0).largest.is_nan());
        // A NaN first sample is never beaten: every reading stays NaN.
        let mut t = PeakToTrough::new();
        t.update(f64::NAN);
        let stuck = t.update(5.0);
        assert!(stuck.high.is_nan() && stuck.current.is_nan() && stuck.largest.is_nan());
        // A later NaN shows for one sample and is not kept.
        let mut t = PeakToTrough::new();
        t.update(5.0);
        assert!(t.update(f64::NAN).current.is_nan());
        let after = t.update(3.0);
        assert_eq!((after.high, after.current, after.largest), (5.0, 2.0, 2.0));
    }
}
