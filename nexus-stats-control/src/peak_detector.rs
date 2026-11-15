use nexus_stats_core::Sample;

/// A detected peak.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Peak<T> {
    /// The peak value.
    pub value: T,
    /// Whether this is a local maximum (true) or local minimum (false).
    pub is_maximum: bool,
}

/// Peak detector — identifies local maxima and minima with prominence filtering.
///
/// A peak is reported when the signal reverses direction by more than
/// the prominence threshold. This filters out small oscillations.
/// `PeakDetector<f64>` rejects NaN and infinity and returns `Result`;
/// `PeakDetector<i64>` cannot fail.
///
/// # Use Cases
/// - Finding local highs/lows in price data
/// - Cycle detection in oscillating signals
/// - Inflection point identification
#[derive(Debug, Clone)]
pub struct PeakDetector<T: Sample> {
    prominence: T,
    extreme: T,
    rising: bool,
    count: u64,
}

impl<T: Sample> PeakDetector<T> {
    /// Creates a detector. A reversal must exceed `prominence` to count.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError::Invalid` if `prominence` is negative or NaN.
    #[inline]
    #[allow(clippy::neg_cmp_op_on_partial_ord)]
    pub fn new(prominence: T) -> Result<Self, nexus_stats_core::ConfigError> {
        if !(prominence >= T::ZERO) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "prominence must be non-negative",
            ));
        }
        Ok(Self {
            prominence,
            extreme: T::ZERO,
            rising: true,
            count: 0,
        })
    }

    /// Number of samples processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Resets to the initial state. `prominence` is kept.
    #[inline]
    pub fn reset(&mut self) {
        self.extreme = T::ZERO;
        self.rising = true;
        self.count = 0;
    }

    #[inline]
    fn fold(&mut self, sample: T) -> Option<Peak<T>> {
        self.count += 1;
        if self.count == 1 {
            self.extreme = sample;
            return None;
        }
        if self.rising {
            if sample > self.extreme {
                self.extreme = sample;
                None
            } else if self.extreme - sample >= self.prominence {
                let peak = Peak {
                    value: self.extreme,
                    is_maximum: true,
                };
                self.extreme = sample;
                self.rising = false;
                Some(peak)
            } else {
                None
            }
        } else if sample < self.extreme {
            self.extreme = sample;
            None
        } else if sample - self.extreme >= self.prominence {
            let peak = Peak {
                value: self.extreme,
                is_maximum: false,
            };
            self.extreme = sample;
            self.rising = true;
            Some(peak)
        } else {
            None
        }
    }
}

impl PeakDetector<f64> {
    /// Feeds a sample. Returns a peak when the signal has reversed by more
    /// than the prominence since its last extreme.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    #[inline]
    pub fn update(
        &mut self,
        sample: f64,
    ) -> Result<Option<Peak<f64>>, nexus_stats_core::DataError> {
        check_finite!(sample);
        Ok(self.fold(sample))
    }
}

impl PeakDetector<i64> {
    /// Feeds a sample. Returns a peak when the signal has reversed by more
    /// than the prominence since its last extreme.
    #[inline]
    pub fn update(&mut self, sample: i64) -> Option<Peak<i64>> {
        self.fold(sample)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detects_maximum() {
        let mut pd = PeakDetector::<f64>::new(5.0).unwrap();
        let _ = pd.update(10.0).unwrap();
        let _ = pd.update(20.0).unwrap();
        let _ = pd.update(30.0).unwrap(); // rising
        let peak = pd.update(20.0).unwrap(); // dropped by 10 > prominence 5
        assert_eq!(
            peak,
            Some(Peak {
                value: 30.0,
                is_maximum: true
            })
        );
    }

    #[test]
    fn detects_minimum() {
        let mut pd = PeakDetector::<f64>::new(5.0).unwrap();
        let _ = pd.update(30.0).unwrap();
        let _ = pd.update(20.0).unwrap();
        let _ = pd.update(10.0).unwrap(); // found max at 30, now falling
        // need to trigger the max detection first
        let _ = pd.update(20.0).unwrap(); // reversal from 10 by 10 > 5, minimum at 10

        let mut pd2 = PeakDetector::<f64>::new(5.0).unwrap();
        let _ = pd2.update(10.0).unwrap();
        let _ = pd2.update(20.0).unwrap(); // rising
        let _ = pd2.update(10.0).unwrap(); // max at 20, reversal
        let _ = pd2.update(5.0).unwrap(); // falling
        let peak = pd2.update(15.0).unwrap(); // reversal from 5 by 10 > 5, minimum at 5
        assert_eq!(
            peak,
            Some(Peak {
                value: 5.0,
                is_maximum: false
            })
        );
    }

    #[test]
    fn small_oscillation_filtered() {
        let mut pd = PeakDetector::<f64>::new(10.0).unwrap();
        let _ = pd.update(100.0).unwrap();
        let _ = pd.update(105.0).unwrap();
        assert!(pd.update(102.0).unwrap().is_none()); // only dropped 3, < prominence 10
    }

    #[test]
    fn i64_basic() {
        let mut pd = PeakDetector::<i64>::new(10).unwrap();
        let _ = pd.update(0);
        let _ = pd.update(50);
        let peak = pd.update(30); // dropped 20 > 10
        assert_eq!(
            peak,
            Some(Peak {
                value: 50,
                is_maximum: true
            })
        );
    }

    #[test]
    fn reset() {
        let mut pd = PeakDetector::<f64>::new(5.0).unwrap();
        let _ = pd.update(100.0).unwrap();
        pd.reset();
        assert!(pd.update(50.0).unwrap().is_none()); // re-initialized
    }

    #[test]
    fn rejects_negative_prominence() {
        assert!(matches!(
            PeakDetector::<f64>::new(-1.0),
            Err(nexus_stats_core::ConfigError::Invalid(_))
        ));
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut pd = PeakDetector::<f64>::new(5.0).unwrap();
        assert_eq!(
            pd.update(f64::NAN),
            Err(nexus_stats_core::DataError::NotANumber)
        );
        assert_eq!(
            pd.update(f64::INFINITY),
            Err(nexus_stats_core::DataError::Infinite)
        );
        assert_eq!(
            pd.update(f64::NEG_INFINITY),
            Err(nexus_stats_core::DataError::Infinite)
        );
    }
}
