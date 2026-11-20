use crate::statistics::Moments;

/// Detects distribution shape changes by comparing each completed window of
/// samples against everything before it.
///
/// Samples fill a "fast" window of `fast_window` observations. When the
/// window completes, its skewness and excess kurtosis are compared with
/// those of the baseline (every sample before the window), the difference
/// is reported and latched, and the window is merged into the baseline.
/// A shift in kurtosis or skewness between the two indicates a regime
/// change (fat-tail events, asymmetry shifts) that a mean or variance
/// monitor would not see.
///
/// A reading therefore arrives once per `fast_window` samples, from the
/// second window on (the first window only builds the baseline), and
/// [`last`](Self::last) holds it until the next window completes.
///
/// The baseline is all-time: it weights every past sample equally and
/// adapts more slowly the longer the detector runs. Call
/// [`reset`](Self::reset) to start a new baseline after a confirmed regime
/// change.
///
/// # Examples
///
/// ```
/// use nexus_stats_core::detection::DistributionShift;
///
/// let mut det = DistributionShift::builder()
///     .fast_window(50)
///     .build()
///     .unwrap();
///
/// // Two windows of a symmetric ramp, then one with a heavy right tail.
/// let symmetric = (0..100).map(|i| f64::from(i % 50));
/// let skewed = (0..50).map(|i| if i % 10 == 0 { 500.0 } else { f64::from(i) });
/// let mut readings = Vec::new();
/// for x in symmetric.chain(skewed) {
///     if let Some(shift) = det.update(x) {
///         readings.push(shift);
///     }
/// }
/// // One reading per completed window after the first.
/// assert_eq!(readings.len(), 2);
/// assert!(readings[0].skewness.abs() < 1e-9);
/// assert!(readings[1].skewness > 1.0);
/// // The last reading stays available between windows.
/// assert_eq!(det.last(), Some(readings[1]));
/// ```
#[derive(Debug, Clone)]
pub struct DistributionShift {
    fast: Moments,
    baseline: Moments,
    fast_window: u64,
    count: u64,
    last: Option<ShapeShift>,
}

/// How a completed window's shape differs from the baseline before it:
/// window minus baseline.
///
/// The two fields are on different scales (the sampling noise of kurtosis
/// is about twice that of skewness), so test each against its own
/// threshold: `s.excess_kurtosis > 2.0 || s.skewness.abs() > 1.0`.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ShapeShift {
    /// Skewness difference. Positive: the window is more right-skewed than
    /// the baseline.
    pub skewness: f64,
    /// Excess-kurtosis difference. Positive: the window has heavier tails
    /// than the baseline.
    pub excess_kurtosis: f64,
}

/// Builder for [`DistributionShift`].
#[derive(Debug, Clone)]
pub struct DistributionShiftBuilder {
    fast_window: Option<u64>,
}

impl DistributionShift {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> DistributionShiftBuilder {
        DistributionShiftBuilder { fast_window: None }
    }

    /// Feeds an observation.
    ///
    /// Returns `Some(shift)` on the sample that completes a window, when
    /// both that window and the baseline before it have a defined shape,
    /// and `None` on every other sample. A shape is undefined
    /// for a constant window (zero variance), and there is no baseline
    /// during the first window.
    ///
    /// Unchecked, like `f64` arithmetic: whatever is passed is folded in.
    /// After a NaN, an infinity, or a finite value above
    /// [`INPUT_LIMIT_FOURTH_MOMENT`](crate::INPUT_LIMIT_FOURTH_MOMENT) in magnitude (which can
    /// overflow), the readings carry no meaning until
    /// [`reset`](Self::reset): NaN as a rule, though a comparison inside can
    /// turn that into `None` or a wrong number. Use
    /// [`checked_update`](Self::checked_update) to have such a value refused
    /// instead.
    #[inline]
    pub fn update(&mut self, value: f64) -> Option<ShapeShift> {
        self.fast.update(value);
        self.count += 1;
        if self.fast.count() < self.fast_window {
            return None;
        }
        self.last = Self::compare(&self.fast, &self.baseline);
        self.baseline.merge(&self.fast);
        self.fast.reset();
        self.last
    }

    /// [`update`](Self::update) with the input validated first: refuses a
    /// value that is NaN, infinite, or above [`INPUT_LIMIT_FOURTH_MOMENT`](crate::INPUT_LIMIT_FOURTH_MOMENT) in
    /// magnitude, and leaves the state untouched. Fed only through this
    /// method, no reading is ever NaN, or infinite unless its documentation
    /// says so.
    ///
    /// # Errors
    ///
    /// `DataError::NotANumber`, `DataError::Infinite`, or
    /// `DataError::OutOfRange` for a finite magnitude above the limit.
    #[inline]
    pub fn checked_update(&mut self, value: f64) -> Result<Option<ShapeShift>, crate::DataError> {
        check_magnitude!(value, crate::INPUT_LIMIT_FOURTH_MOMENT);
        Ok(self.update(value))
    }

    /// The reading from the most recently completed window, or `None` if
    /// that window had none (see [`update`](Self::update)) or no window has
    /// completed against a baseline yet.
    #[inline]
    #[must_use]
    pub fn last(&self) -> Option<ShapeShift> {
        self.last
    }

    /// Total number of observations fed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// The configured window length in samples.
    #[inline]
    #[must_use]
    pub fn fast_window(&self) -> u64 {
        self.fast_window
    }

    /// Whether a baseline exists, that is, the first window has completed.
    /// Stays true until [`reset`](Self::reset). It does not say that the
    /// last window produced a reading (a constant window does not); that is
    /// [`last`](Self::last).
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.fast_window
    }

    /// Forgets the baseline, the window in progress and the last reading.
    #[inline]
    pub fn reset(&mut self) {
        self.fast.reset();
        self.baseline.reset();
        self.count = 0;
        self.last = None;
    }

    #[inline]
    fn compare(window: &Moments, baseline: &Moments) -> Option<ShapeShift> {
        Some(ShapeShift {
            skewness: window.skewness()? - baseline.skewness()?,
            excess_kurtosis: window.excess_kurtosis()? - baseline.excess_kurtosis()?,
        })
    }
}

impl DistributionShiftBuilder {
    /// Number of observations per window. At least 4 (excess kurtosis is
    /// undefined below that); in practice tens to hundreds, since the
    /// sample kurtosis of a short window is mostly noise.
    ///
    /// Default: 50.
    #[inline]
    #[must_use]
    pub fn fast_window(mut self, window: u64) -> Self {
        self.fast_window = Some(window);
        self
    }

    /// Build the detector.
    ///
    /// # Errors
    ///
    /// `ConfigError::Invalid` if `fast_window` is below 4.
    #[inline]
    pub fn build(self) -> Result<DistributionShift, crate::ConfigError> {
        let fast_window = self.fast_window.unwrap_or(50);
        if fast_window < 4 {
            return Err(crate::ConfigError::Invalid(
                "fast_window must be at least 4",
            ));
        }
        Ok(DistributionShift {
            fast: Moments::new(),
            baseline: Moments::new(),
            fast_window,
            count: 0,
            last: None,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn moments(xs: &[f64]) -> Moments {
        let mut m = Moments::new();
        for &x in xs {
            m.update(x);
        }
        m
    }

    /// Three windows of 8 with distinct shapes.
    const W1: [f64; 8] = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0];
    const W2: [f64; 8] = [1.0, 1.0, 2.0, 2.0, 3.0, 3.0, 4.0, 30.0];
    const W3: [f64; 8] = [-40.0, 1.0, 2.0, 2.0, 3.0, 3.0, 4.0, 4.0];

    #[test]
    fn a_reading_is_the_completed_window_against_everything_before_it() {
        let mut det = DistributionShift::builder().fast_window(8).build().unwrap();
        let mut readings = Vec::new();
        for (i, &x) in W1.iter().chain(&W2).chain(&W3).enumerate() {
            let r = det.update(x);
            // Only the samples that complete windows 2 and 3 report.
            assert_eq!(r.is_some(), i == 15 || i == 23, "sample {i}");
            readings.extend(r);
        }

        let (w1, w2, w3) = (moments(&W1), moments(&W2), moments(&W3));
        let mut w12 = w1.clone();
        w12.merge(&w2);
        let expected = [
            ShapeShift {
                skewness: w2.skewness().unwrap() - w1.skewness().unwrap(),
                excess_kurtosis: w2.excess_kurtosis().unwrap() - w1.excess_kurtosis().unwrap(),
            },
            ShapeShift {
                skewness: w3.skewness().unwrap() - w12.skewness().unwrap(),
                excess_kurtosis: w3.excess_kurtosis().unwrap() - w12.excess_kurtosis().unwrap(),
            },
        ];
        assert_eq!(readings, expected);
        // Right tail, then left tail.
        assert!(readings[0].skewness > 1.0 && readings[0].excess_kurtosis > 1.0);
        assert!(readings[1].skewness < -1.0);
    }

    #[test]
    fn the_reading_is_latched_between_windows() {
        let mut det = DistributionShift::builder().fast_window(8).build().unwrap();
        for &x in W1.iter().chain(&W2) {
            let _ = det.update(x);
        }
        let reading = det.last().unwrap();
        // A caller polling exactly at a window boundary, or anywhere inside
        // the next window, sees the same completed reading.
        for &x in &W3[..7] {
            assert_eq!(det.update(x), None);
            assert_eq!(det.last(), Some(reading));
        }
        assert!(det.is_primed());
        det.reset();
        assert!(!det.is_primed());
    }

    #[test]
    fn same_shape_reads_no_shift() {
        let mut det = DistributionShift::builder().fast_window(8).build().unwrap();
        for _ in 0..5 {
            for &x in &W1 {
                let _ = det.update(x);
            }
        }
        let r = det.last().unwrap();
        assert!(r.skewness.abs() < 1e-12, "{r:?}");
        // Repeating a window leaves the pooled kurtosis where it was.
        assert!(r.excess_kurtosis.abs() < 1e-12, "{r:?}");
    }

    #[test]
    fn no_reading_without_a_baseline_or_a_shape() {
        let mut det = DistributionShift::builder().fast_window(8).build().unwrap();
        // First window: nothing to compare against.
        for &x in &W1 {
            assert!(!det.is_primed());
            assert_eq!(det.update(x), None);
        }
        // The baseline exists from here on, but there is no reading yet.
        assert!(det.is_primed());
        assert_eq!(det.last(), None);
        // A constant window has no skewness or kurtosis: no reading, and
        // the previous one is not left standing.
        for &x in &W2 {
            let _ = det.update(x);
        }
        assert!(det.last().is_some());
        for _ in 0..8 {
            assert_eq!(det.update(5.0), None);
        }
        assert_eq!(det.last(), None);
        // Still primed: priming does not flap with the readings.
        assert!(det.is_primed());
    }

    #[test]
    fn rejects_nan_and_inf_without_counting_them() {
        let mut det = DistributionShift::builder().fast_window(8).build().unwrap();
        assert_eq!(
            det.checked_update(f64::NAN),
            Err(crate::DataError::NotANumber)
        );
        assert_eq!(
            det.checked_update(f64::INFINITY),
            Err(crate::DataError::Infinite)
        );
        assert_eq!(det.count(), 0);
        // Rejected samples interleaved with two windows of valid ones do
        // not advance the window: the reading still arrives on the 16th
        // valid sample and equals the reading without them.
        let mut reading = None;
        for (i, &x) in W1.iter().chain(&W2).enumerate() {
            assert!(det.checked_update(f64::NAN).is_err());
            let r = det.update(x);
            assert_eq!(r.is_some(), i == 15, "sample {i}");
            reading = reading.or(r);
        }
        assert_eq!(det.count(), 16);
        let (w1, w2) = (moments(&W1), moments(&W2));
        assert_eq!(
            reading.unwrap().skewness,
            w2.skewness().unwrap() - w1.skewness().unwrap()
        );
    }

    #[test]
    fn reset_forgets_baseline_window_and_reading() {
        let mut det = DistributionShift::builder().fast_window(8).build().unwrap();
        for &x in W1.iter().chain(&W2).chain(&W3[..3]) {
            let _ = det.update(x);
        }
        det.reset();
        assert_eq!(det.count(), 0);
        assert_eq!(det.last(), None);
        // A full window after reset is a first window again.
        for &x in &W2 {
            assert_eq!(det.update(x), None);
        }
    }

    #[test]
    fn builder_validates_the_window() {
        for w in [0, 1, 3] {
            assert_eq!(
                DistributionShift::builder()
                    .fast_window(w)
                    .build()
                    .unwrap_err(),
                crate::ConfigError::Invalid("fast_window must be at least 4")
            );
        }
        let det = DistributionShift::builder().build().unwrap();
        assert_eq!(det.fast_window(), 50);
        assert!(DistributionShift::builder().fast_window(4).build().is_ok());
    }
}
