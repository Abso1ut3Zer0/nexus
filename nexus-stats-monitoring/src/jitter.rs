/// Interarrival jitter, as RFC 3550 estimates it.
///
/// Feed each packet's transit time: its arrival time minus the timestamp
/// it carries, in any unit. With `D` the difference between this transit
/// time and the previous one, the estimate moves a sixteenth of the way
/// toward `|D|`:
///
/// ```text
/// J = J + (|D| - J) / 16
/// ```
///
/// The estimate starts at zero, and the gain is the RFC's 1/16. The first
/// packet only sets the previous transit time.
///
/// `Jitter<f64>` is the floating-point form of the RFC's appendix A.8. It
/// returns the estimate as it is, where the RFC truncates it to an integer
/// when it reports. `Jitter<i64>` is the RFC's integer form, which keeps
/// the estimate scaled by 16 and rounds: the same code as a receiver
/// reporting to RTCP.
///
/// # Weighting clock
///
/// Per packet. Every transit time after the first moves the estimate by
/// the same sixteenth.
///
/// See [RFC 3550](https://www.rfc-editor.org/rfc/rfc3550), section 6.4.1
/// and appendix A.8.
///
/// # Examples
///
/// ```
/// use nexus_stats_monitoring::Jitter;
///
/// let mut jitter = Jitter::<f64>::new();
/// assert_eq!(jitter.update(100.0), None); // no difference yet
/// assert_eq!(jitter.update(116.0), Some(1.0)); // 0 + (16 - 0) / 16
/// assert_eq!(jitter.update(116.0), Some(0.9375)); // 1 + (0 - 1) / 16
/// ```
#[derive(Debug, Clone)]
pub struct Jitter<T> {
    /// The estimate. For `i64` it is kept scaled by 16.
    estimate: T,
    /// The previous packet's transit time.
    transit: T,
    count: u64,
}

/// The RFC's gain, as a shift: `2^-4 = 1/16`.
const GAIN_SHIFT: u32 = 4;

/// The largest difference `Jitter<i64>::checked_update` takes. The scaled
/// estimate rests just below 16 times it, which keeps every step in range.
const LARGEST_DIFFERENCE: u64 = (i64::MAX >> (GAIN_SHIFT + 1)) as u64;

impl<T> Jitter<T> {
    /// Samples fed since construction or `reset`.
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether there is an estimate: two transit times have been fed.
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= 2
    }
}

impl Jitter<f64> {
    /// Creates an estimator at zero.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            estimate: 0.0,
            transit: 0.0,
            count: 0,
        }
    }

    /// Feeds a transit time and returns the jitter, or `None` for the
    /// first one.
    ///
    /// Does not validate; arithmetic follows IEEE 754. See
    /// [`checked_update`](Self::checked_update).
    #[inline]
    pub fn update(&mut self, transit: f64) -> Option<f64> {
        self.count += 1;
        if self.count == 1 {
            self.transit = transit;
            return None;
        }
        let difference = (transit - self.transit).abs();
        self.transit = transit;
        self.estimate = float_step(self.estimate, difference);
        Some(self.estimate)
    }

    /// Checked update. Feeds `transit`, or returns an error and leaves the
    /// estimator unchanged if `transit` is NaN, infinite, or larger in
    /// magnitude than half of `f64::MAX`. Two finite transit times further
    /// apart than `f64::MAX` would make the estimate infinite, then NaN.
    ///
    /// # Errors
    ///
    /// - [`DataError::NotANumber`](nexus_stats_core::DataError::NotANumber)
    ///   if `transit` is NaN.
    /// - [`DataError::Infinite`](nexus_stats_core::DataError::Infinite) if
    ///   `transit` is infinite.
    /// - [`DataError::OutOfRange`](nexus_stats_core::DataError::OutOfRange)
    ///   if `transit` is larger in magnitude than `f64::MAX / 2`.
    #[inline]
    pub fn checked_update(
        &mut self,
        transit: f64,
    ) -> Result<Option<f64>, nexus_stats_core::DataError> {
        nexus_stats_core::math::check_input(transit, f64::MAX / 2.0)?;
        Ok(self.update(transit))
    }

    /// The jitter, or `None` until two transit times have been fed.
    #[must_use]
    pub fn jitter(&self) -> Option<f64> {
        if !self.is_primed() {
            return None;
        }
        Some(self.estimate)
    }

    /// Back to zero, with no previous transit time.
    pub fn reset(&mut self) {
        *self = Self::new();
    }
}

impl Jitter<i64> {
    /// Creates an estimator at zero.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            estimate: 0,
            transit: 0,
            count: 0,
        }
    }

    /// Feeds a transit time and returns the jitter, or `None` for the
    /// first one.
    ///
    /// Plain integer arithmetic: a difference too large to hold overflows,
    /// in the subtraction or in its absolute value. See
    /// [`checked_update`](Self::checked_update).
    #[inline]
    pub fn update(&mut self, transit: i64) -> Option<i64> {
        self.count += 1;
        if self.count == 1 {
            self.transit = transit;
            return None;
        }
        let difference = (transit - self.transit).abs();
        self.transit = transit;
        self.estimate = scaled_step(self.estimate, difference);
        Some(reported(self.estimate))
    }

    /// Checked update. Feeds `transit`, or returns an error and leaves the
    /// estimator unchanged if its difference from the previous transit
    /// time is too large for the estimate to hold.
    ///
    /// # Errors
    ///
    /// [`DataError::OutOfRange`](nexus_stats_core::DataError::OutOfRange)
    /// if the difference is above `i64::MAX / 32`.
    #[inline]
    pub fn checked_update(
        &mut self,
        transit: i64,
    ) -> Result<Option<i64>, nexus_stats_core::DataError> {
        if self.count > 0 && transit.abs_diff(self.transit) > LARGEST_DIFFERENCE {
            return Err(nexus_stats_core::DataError::OutOfRange);
        }
        Ok(self.update(transit))
    }

    /// The jitter, or `None` until two transit times have been fed.
    #[must_use]
    pub fn jitter(&self) -> Option<i64> {
        if !self.is_primed() {
            return None;
        }
        Some(reported(self.estimate))
    }

    /// Back to zero, with no previous transit time.
    pub fn reset(&mut self) {
        *self = Self::new();
    }
}

/// RFC 3550 A.8, floating-point form:
/// `jitter += (1./16.) * ((double)d - jitter)`.
// PERF: unfused, as the RFC writes it, so results match its code exactly.
#[inline]
#[allow(clippy::suboptimal_flops)]
fn float_step(estimate: f64, difference: f64) -> f64 {
    estimate + (1.0 / 16.0) * (difference - estimate)
}

/// RFC 3550 A.8, integer form, on the estimate scaled by 16:
/// `jitter += d - ((jitter + 8) >> 4)`.
#[inline]
fn scaled_step(scaled: i64, difference: i64) -> i64 {
    scaled + difference - ((scaled + (1 << (GAIN_SHIFT - 1))) >> GAIN_SHIFT)
}

/// The jitter a scaled estimate stands for: `jitter >> 4`.
#[inline]
fn reported(scaled: i64) -> i64 {
    scaled >> GAIN_SHIFT
}

impl Default for Jitter<f64> {
    fn default() -> Self {
        Self::new()
    }
}

impl Default for Jitter<i64> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
#[allow(clippy::suboptimal_flops)]
mod tests {
    use super::*;
    use nexus_stats_core::DataError::{Infinite, NotANumber, OutOfRange};

    /// RFC 3550 appendix A.8, floating-point form, written as its C code.
    fn rfc_float(transits: &[f64]) -> Vec<f64> {
        let (mut jitter, mut previous) = (0.0f64, transits[0]);
        let mut out = Vec::new();
        for &transit in &transits[1..] {
            let mut d = transit - previous;
            previous = transit;
            if d < 0.0 {
                d = -d;
            }
            jitter += (1. / 16.) * (d - jitter);
            out.push(jitter);
        }
        out
    }

    /// RFC 3550 appendix A.8, integer form: the reported value at each step.
    fn rfc_integer(transits: &[i64]) -> Vec<i64> {
        let (mut jitter, mut previous) = (0i64, transits[0]);
        let mut out = Vec::new();
        for &transit in &transits[1..] {
            let mut d = transit - previous;
            previous = transit;
            if d < 0 {
                d = -d;
            }
            jitter += d - ((jitter + 8) >> 4);
            out.push(jitter >> 4);
        }
        out
    }

    fn transits(count: usize) -> Vec<i64> {
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        (0..count)
            .map(|i| {
                state ^= state << 13;
                state ^= state >> 7;
                state ^= state << 17;
                // A base delay with noise and the odd spike.
                let spike = if state.is_multiple_of(97) { 5_000 } else { 0 };
                40_000 + (state % 2_001) as i64 + spike + (i as i64 % 7)
            })
            .collect()
    }

    #[test]
    fn the_float_form_matches_the_rfc_code_bit_for_bit() {
        let transits: Vec<f64> = transits(20_000).iter().map(|&t| t as f64 * 0.125).collect();
        let want = rfc_float(&transits);
        let mut jitter = Jitter::<f64>::new();
        assert_eq!(jitter.update(transits[0]), None);
        for (i, &transit) in transits[1..].iter().enumerate() {
            let got = jitter.update(transit).unwrap();
            assert_eq!(got.to_bits(), want[i].to_bits(), "packet {i}");
            assert_eq!(jitter.jitter(), Some(got));
        }
    }

    #[test]
    fn the_integer_form_matches_the_rfc_code() {
        let transits = transits(20_000);
        let want = rfc_integer(&transits);
        let mut jitter = Jitter::<i64>::new();
        assert_eq!(jitter.update(transits[0]), None);
        for (i, &transit) in transits[1..].iter().enumerate() {
            assert_eq!(jitter.update(transit), Some(want[i]), "packet {i}");
            assert_eq!(jitter.jitter(), Some(want[i]));
        }
    }

    #[test]
    fn the_estimate_starts_at_zero_and_moves_a_sixteenth() {
        let mut jitter = Jitter::<f64>::new();
        assert_eq!((jitter.jitter(), jitter.is_primed()), (None, false));
        assert_eq!(jitter.update(100.0), None);
        assert_eq!(jitter.update(116.0), Some(1.0));
        assert_eq!(jitter.update(116.0), Some(0.9375));
        assert_eq!(jitter.update(100.0), Some(0.9375 + (16.0 - 0.9375) / 16.0));

        let mut jitter = Jitter::<i64>::new();
        assert_eq!(jitter.update(100), None);
        // Scaled: 0 + 160 - ((0 + 8) >> 4) = 160, reported 160 >> 4.
        assert_eq!(jitter.update(260), Some(10));
        // 160 + 0 - ((160 + 8) >> 4) = 150, reported 9.
        assert_eq!(jitter.update(260), Some(9));
    }

    #[test]
    fn steady_transit_times_have_no_jitter() {
        let (mut float, mut integer) = (Jitter::<f64>::new(), Jitter::<i64>::new());
        for _ in 0..500 {
            float.update(250.0);
            integer.update(250);
        }
        assert_eq!((float.jitter(), integer.jitter()), (Some(0.0), Some(0)));
    }

    /// A constant difference is the level the estimate settles at.
    #[test]
    fn it_settles_at_a_constant_difference() {
        let (mut float, mut integer) = (Jitter::<f64>::new(), Jitter::<i64>::new());
        for i in 0..2_000 {
            let transit = if i % 2 == 0 { 1_000 } else { 1_640 };
            float.update(f64::from(transit));
            integer.update(i64::from(transit));
        }
        assert!((float.jitter().unwrap() - 640.0).abs() < 1e-9);
        // The integer form's rounding stops one short: the scaled estimate
        // rests where `(J + 8) >> 4` first equals the difference.
        assert_eq!(integer.jitter(), Some(639));
    }

    #[test]
    fn reset_starts_over() {
        let mut jitter = Jitter::<i64>::new();
        jitter.update(10);
        jitter.update(500);
        jitter.reset();
        assert_eq!((jitter.jitter(), jitter.count()), (None, 0));
        // The first transit after a reset is not a difference from zero.
        assert_eq!(jitter.update(9_000), None);
        assert_eq!(jitter.update(9_000), Some(0));
        let mut jitter = Jitter::<f64>::default();
        jitter.update(10.0);
        jitter.reset();
        assert_eq!(jitter.update(9_000.0), None);
    }

    #[test]
    fn checked_update_refuses_nan_and_infinity_and_changes_nothing() {
        let mut jitter = Jitter::<f64>::new();
        assert_eq!(jitter.checked_update(f64::NAN), Err(NotANumber));
        assert_eq!(jitter.count(), 0);
        jitter.checked_update(10.0).unwrap();
        jitter.checked_update(30.0).unwrap();
        let before = (jitter.jitter(), jitter.count());
        assert_eq!(jitter.checked_update(f64::INFINITY), Err(Infinite));
        assert_eq!(jitter.checked_update(f64::NEG_INFINITY), Err(Infinite));
        assert_eq!(jitter.checked_update(f64::NAN), Err(NotANumber));
        assert_eq!((jitter.jitter(), jitter.count()), before);
        // Unchanged inside too: the next step is measured from 30.
        assert_eq!(jitter.checked_update(30.0), Ok(Some(1.25 - 1.25 / 16.0)));
    }

    /// Two finite transit times can be an infinite distance apart, which
    /// would make the estimate infinite and then NaN.
    #[test]
    fn checked_update_refuses_a_transit_too_large_to_difference() {
        let mut plain = Jitter::<f64>::new();
        plain.update(f64::MAX);
        assert_eq!(plain.update(-f64::MAX), Some(f64::INFINITY));
        assert!(plain.update(0.0).unwrap().is_nan());

        let mut jitter = Jitter::<f64>::new();
        assert_eq!(jitter.checked_update(f64::MAX), Err(OutOfRange));
        assert_eq!(jitter.checked_update(-f64::MAX), Err(OutOfRange));
        assert_eq!(jitter.count(), 0);
        jitter.checked_update(f64::MAX / 2.0).unwrap();
        // The largest difference there can be: the whole range.
        let estimate = jitter.checked_update(-f64::MAX / 2.0);
        assert_eq!(estimate, Ok(Some(f64::MAX / 16.0)));
        // A refusal once primed changes nothing.
        let before = (jitter.jitter(), jitter.count());
        assert_eq!(jitter.checked_update(f64::MAX), Err(OutOfRange));
        assert_eq!((jitter.jitter(), jitter.count()), before);
        assert!(jitter.checked_update(0.0).unwrap().unwrap().is_finite());
    }

    #[test]
    fn checked_update_refuses_a_difference_too_large_to_hold() {
        let largest = i64::MAX >> 5;
        let mut jitter = Jitter::<i64>::new();
        // The first transit time is not a difference: any value is taken.
        assert_eq!(jitter.checked_update(i64::MIN), Ok(None));
        jitter.reset();
        jitter.checked_update(0).unwrap();
        assert_eq!(jitter.checked_update(largest + 1), Err(OutOfRange));
        assert_eq!(jitter.checked_update(i64::MIN), Err(OutOfRange));
        assert_eq!((jitter.jitter(), jitter.count()), (None, 1));
        // At the limit, forever: the scaled estimate stays in range.
        for i in 0..10_000 {
            let transit = if i % 2 == 0 { largest } else { 0 };
            jitter.checked_update(transit).unwrap();
        }
        // It rests one below the difference, as the RFC's rounding does.
        assert_eq!(jitter.jitter(), Some(largest - 1));
    }

    #[test]
    fn checked_update_gives_the_same_result_as_update() {
        let transits = transits(2_000);
        let (mut checked, mut plain) = (Jitter::<i64>::new(), Jitter::<i64>::new());
        let (mut checked_f, mut plain_f) = (Jitter::<f64>::new(), Jitter::<f64>::new());
        for &t in &transits {
            assert_eq!(checked.checked_update(t), Ok(plain.update(t)));
            assert_eq!(
                checked_f.checked_update(t as f64),
                Ok(plain_f.update(t as f64))
            );
        }
    }
}
