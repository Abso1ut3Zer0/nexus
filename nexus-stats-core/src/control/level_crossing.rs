use crate::{Direction, Sample};

/// Level crossing detector — signals when a value crosses a threshold.
///
/// Reports the sample on which the signal lands on the other side of the
/// threshold, and which way it went: [`Direction::Rising`] for below to
/// above, [`Direction::Falling`] for above to below. Tracks the total
/// crossing count.
///
/// A sample exactly on the threshold is on neither side: it reports nothing
/// and does not change which side the signal is on. So -1, 0, -1 around a
/// threshold of 0 is no crossing, and -1, 0, 1 is one, reported at the 1.
///
/// `LevelCrossing<f64>` rejects NaN and infinity and returns `Result`;
/// `LevelCrossing<i64>` cannot fail.
///
/// # Use Cases
/// - Zero-crossing detection
/// - Alert when metric crosses a boundary
/// - Counting threshold breaches
#[derive(Debug, Clone)]
pub struct LevelCrossing<T: Sample> {
    threshold: T,
    side: Side,
    crossings: u64,
    count: u64,
}

/// Which side of the threshold the signal was last seen on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Side {
    /// No sample off the threshold yet.
    Unknown,
    Below,
    Above,
}

impl<T: Sample> LevelCrossing<T> {
    /// Creates a detector for the given threshold.
    ///
    /// # Errors
    ///
    /// `ConfigError::Invalid` if the threshold is NaN or infinite (a NaN
    /// threshold would never be crossed).
    #[inline]
    pub fn new(threshold: T) -> Result<Self, crate::ConfigError> {
        if !threshold.is_finite() {
            return Err(crate::ConfigError::Invalid("threshold must be finite"));
        }
        Ok(Self {
            threshold,
            side: Side::Unknown,
            crossings: 0,
            count: 0,
        })
    }

    /// Total number of crossings seen.
    #[inline]
    #[must_use]
    pub fn crossing_count(&self) -> u64 {
        self.crossings
    }

    /// Samples processed since construction or `reset`.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether at least one sample has been seen.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count > 0
    }

    /// Resets to uninitialized state. The threshold is kept.
    #[inline]
    pub fn reset(&mut self) {
        self.side = Side::Unknown;
        self.crossings = 0;
        self.count = 0;
    }

    #[inline]
    fn fold(&mut self, sample: T) -> Option<Direction> {
        self.count += 1;
        let side = if sample > self.threshold {
            Side::Above
        } else if sample < self.threshold {
            Side::Below
        } else {
            return None;
        };
        let before = core::mem::replace(&mut self.side, side);
        if before == side || before == Side::Unknown {
            return None;
        }
        self.crossings += 1;
        Some(if side == Side::Above {
            Direction::Rising
        } else {
            Direction::Falling
        })
    }
}

impl LevelCrossing<f64> {
    /// Feeds a sample. Returns the direction if it crossed the threshold,
    /// `None` otherwise (including the first sample and any sample exactly
    /// on the threshold).
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    #[inline]
    pub fn update(&mut self, sample: f64) -> Result<Option<Direction>, crate::DataError> {
        check_finite!(sample);
        Ok(self.fold(sample))
    }
}

impl LevelCrossing<i64> {
    /// Feeds a sample. Returns the direction if it crossed the threshold,
    /// `None` otherwise (including the first sample and any sample exactly
    /// on the threshold).
    #[must_use]
    #[inline]
    pub fn update(&mut self, sample: i64) -> Option<Direction> {
        self.fold(sample)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run(threshold: f64, samples: &[f64]) -> Vec<Option<Direction>> {
        let mut lc = LevelCrossing::<f64>::new(threshold).unwrap();
        samples.iter().map(|&x| lc.update(x).unwrap()).collect()
    }

    #[test]
    fn first_sample_is_never_a_crossing() {
        assert_eq!(run(50.0, &[30.0]), [None]);
        assert_eq!(run(50.0, &[70.0]), [None]);
    }

    #[test]
    fn reports_the_direction_on_the_crossing_sample() {
        assert_eq!(
            run(50.0, &[30.0, 60.0, 70.0, 40.0, 45.0, 55.0]),
            [
                None,
                Some(Direction::Rising),
                None,
                Some(Direction::Falling),
                None,
                Some(Direction::Rising),
            ]
        );
    }

    #[test]
    fn touching_the_threshold_and_returning_is_not_a_crossing() {
        let mut lc = LevelCrossing::<f64>::new(0.0).unwrap();
        for x in [-1.0, 0.0, -1.0, 0.0, 0.0, -2.0] {
            assert_eq!(lc.update(x).unwrap(), None);
        }
        assert_eq!(lc.crossing_count(), 0);
    }

    #[test]
    fn passing_through_the_threshold_is_one_crossing_reported_on_arrival() {
        assert_eq!(
            run(0.0, &[-1.0, 0.0, 1.0]),
            [None, None, Some(Direction::Rising)]
        );
        assert_eq!(
            run(0.0, &[1.0, 0.0, 0.0, -1.0]),
            [None, None, None, Some(Direction::Falling)]
        );
    }

    #[test]
    fn a_stream_that_starts_on_the_threshold_takes_its_side_from_the_first_move() {
        // 0, 0, 1 has never been below: arriving above is not a crossing.
        assert_eq!(
            run(0.0, &[0.0, 0.0, 1.0, -1.0]),
            [None, None, None, Some(Direction::Falling)]
        );
    }

    #[test]
    fn counts_every_crossing() {
        let mut lc = LevelCrossing::<f64>::new(50.0).unwrap();
        for x in [30.0, 60.0, 40.0, 70.0, 50.0, 20.0] {
            let _ = lc.update(x).unwrap();
        }
        assert_eq!(lc.crossing_count(), 4);
        assert_eq!(lc.count(), 6);
    }

    #[test]
    fn i64_matches_the_float_rule() {
        let mut lc = LevelCrossing::<i64>::new(0).unwrap();
        let out: Vec<_> = [-5, 0, 5, 0, -5, i64::MAX, i64::MIN]
            .into_iter()
            .map(|x| lc.update(x))
            .collect();
        assert_eq!(
            out,
            [
                None,
                None,
                Some(Direction::Rising),
                None,
                Some(Direction::Falling),
                Some(Direction::Rising),
                Some(Direction::Falling),
            ]
        );
    }

    #[test]
    fn reset_forgets_the_side_and_the_counts() {
        let mut lc = LevelCrossing::<f64>::new(50.0).unwrap();
        let _ = lc.update(30.0).unwrap();
        let _ = lc.update(60.0).unwrap();
        lc.reset();
        assert_eq!(lc.crossing_count(), 0);
        assert_eq!(lc.count(), 0);
        assert!(!lc.is_primed());
        // Was above before the reset; a first sample below is not a crossing.
        assert_eq!(lc.update(30.0).unwrap(), None);
    }

    #[test]
    fn rejects_nan_and_inf() {
        assert!(LevelCrossing::<f64>::new(f64::NAN).is_err());
        assert!(LevelCrossing::<f64>::new(f64::INFINITY).is_err());
        let mut lc = LevelCrossing::<f64>::new(50.0).unwrap();
        assert_eq!(lc.update(f64::NAN), Err(crate::DataError::NotANumber));
        assert_eq!(lc.update(f64::INFINITY), Err(crate::DataError::Infinite));
        assert_eq!(lc.count(), 0);
    }
}
