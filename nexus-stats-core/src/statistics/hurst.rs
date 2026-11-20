use crate::storage::Ring;

/// Shortest block the analysis uses. Shorter blocks have too few points for
/// a range or a standard deviation to mean much.
const MIN_BLOCK: usize = 8;

/// Smallest sum of squared deviations treated as a scale: below it the
/// squares have underflowed, partly or wholly, and a ratio built on them is
/// noise or a division by zero.
const RESOLVABLE: f64 = f64::MIN_POSITIVE / f64::EPSILON;

/// Smallest window: three block lengths (32, 16, 8) to fit a line through.
const MIN_WINDOW: usize = 4 * MIN_BLOCK;

/// Rolling Hurst exponent by rescaled range (R/S) analysis.
///
/// The Hurst exponent `H` measures long-range dependence in a stationary
/// series of **increments** (returns, changes), not levels: `H = 0.5` for
/// independent increments, above 0.5 when moves tend to persist, below 0.5
/// when they tend to reverse.
///
/// # Method
///
/// The standard R/S analysis (Hurst, 1951; Mandelbrot & Wallis, 1969) over
/// the last `window_size` samples:
///
/// 1. For a block of `n` samples, take the range `R` of the running sum of
///    deviations from the block's mean, and divide by the block's standard
///    deviation `S`.
/// 2. Average `R / S` over the non-overlapping blocks of length `n` that
///    fit in the window.
/// 3. Repeat for `n = N, N/2, N/4, ...`, halving (and rounding down) while
///    `n` is at least 8, where `N` is the window.
/// 4. `H` is the least-squares slope of `ln(R/S)` against `ln(n)`.
///
/// # Known bias
///
/// For short blocks `R / S` grows faster than its asymptotic power law, so
/// the fitted slope reads **above 0.5 on independent data**: about 0.6 for
/// windows of a few hundred samples, falling slowly toward 0.5 as the
/// window grows. This is a property of the method, not of this
/// implementation, and published corrections exist (Anis & Lloyd, 1976;
/// Peters, 1994). Compare readings with the value the same window gives on
/// shuffled or simulated independent data, not with 0.5.
///
/// # Cost
///
/// `update` is O(1). [`hurst`](Self::hurst) is O(window) per block length,
/// so O(window * log(window)): a per-bar computation, not a per-tick one.
///
/// # Examples
///
/// ```
/// use nexus_stats_core::statistics::Hurst;
///
/// let mut h = Hurst::builder().window_size(256).build().unwrap();
///
/// // Returns that alternate in sign: every move reverses.
/// for i in 0..256 {
///     h.update(if i % 2 == 0 { 0.01 } else { -0.01 });
/// }
/// // The range never grows with the block length, so the slope is zero.
/// assert!(h.hurst().unwrap().abs() < 1e-9);
/// ```
#[derive(Debug, Clone)]
pub struct Hurst {
    window: Ring<f64>,
    count: u64,
}

/// Builder for [`Hurst`].
#[derive(Debug, Clone)]
pub struct HurstBuilder {
    window_size: Option<usize>,
}

impl Hurst {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> HurstBuilder {
        HurstBuilder { window_size: None }
    }

    /// Feeds an increment: a return or a change, not a price level.
    ///
    /// Unchecked, like `f64` arithmetic: whatever is passed is folded in.
    /// After a NaN, an infinity, or a finite value above
    /// [`INPUT_LIMIT`](crate::INPUT_LIMIT) in magnitude (which can
    /// overflow), the readings carry no meaning until
    /// [`reset`](Self::reset): NaN as a rule, though a comparison inside can
    /// turn that into `None` or a wrong number. Here a block holding a NaN
    /// is left out of the fit, so the exponent stays finite and is computed
    /// from fewer blocks; the value also leaves with the window. Use
    /// [`checked_update`](Self::checked_update) to have such a value refused
    /// instead.
    #[inline]
    pub fn update(&mut self, value: f64) {
        self.count += 1;
        self.window.push(value);
    }

    /// [`update`](Self::update) with the input validated first: refuses a
    /// value that is NaN, infinite, or above [`INPUT_LIMIT`](crate::INPUT_LIMIT) in
    /// magnitude, and leaves the state untouched. Fed only through this
    /// method, no reading is ever NaN, or infinite unless its documentation
    /// says so.
    ///
    /// # Errors
    ///
    /// `DataError::NotANumber`, `DataError::Infinite`, or
    /// `DataError::OutOfRange` for a finite magnitude above the limit.
    #[inline]
    pub fn checked_update(&mut self, value: f64) -> Result<(), crate::DataError> {
        check_magnitude!(value, crate::INPUT_LIMIT);
        self.update(value);
        Ok(())
    }

    /// The Hurst exponent of the current window: the slope of `ln(R/S)`
    /// against `ln(n)` over the block lengths `N, N/2, N/4, ...`.
    ///
    /// `None` until the window is full, and when fewer than two block
    /// lengths have a defined `R / S`, which leaves no line to fit: a
    /// window that is constant, or constant within every block, or whose
    /// spread is too small to resolve (under about `1e-146`).
    #[must_use]
    #[allow(clippy::cast_precision_loss)]
    pub fn hurst(&self) -> Option<f64> {
        if !self.window.is_full() {
            return None;
        }
        let (older, newer) = self.window.as_slices();
        let total = self.window.capacity();
        let at = |i: usize| {
            if i < older.len() {
                older[i]
            } else {
                newer[i - older.len()]
            }
        };

        // One (ln block length, ln mean R/S) point per block length; halving
        // from any `usize` gives fewer than 64 of them.
        let mut points = [(0.0f64, 0.0f64); usize::BITS as usize];
        let mut count = 0;
        let mut block = total;
        while block >= MIN_BLOCK {
            let blocks = total / block;
            // The newest samples: any remainder is dropped from the old end.
            let first = total - blocks * block;
            let (mut ratio_sum, mut defined) = (0.0, 0u32);
            for b in 0..blocks {
                let start = first + b * block;
                if let Some(ratio) = rescaled_range((start..start + block).map(at), block) {
                    ratio_sum += ratio;
                    defined += 1;
                }
            }
            if defined > 0 {
                points[count] = (
                    crate::math::ln(block as f64),
                    crate::math::ln(ratio_sum / f64::from(defined)),
                );
                count += 1;
            }
            block /= 2;
        }
        let points = &points[..count];
        if count < 2 {
            return None;
        }
        // Least-squares slope about the means. The block lengths differ, so
        // the denominator is positive.
        let n = count as f64;
        let mean_x = points.iter().map(|p| p.0).sum::<f64>() / n;
        let mean_y = points.iter().map(|p| p.1).sum::<f64>() / n;
        let (mut sxy, mut sxx) = (0.0, 0.0);
        for &(x, y) in points {
            sxy += (x - mean_x) * (y - mean_y);
            sxx += (x - mean_x) * (x - mean_x);
        }
        Some(sxy / sxx)
    }

    /// The configured window length.
    #[inline]
    #[must_use]
    pub fn window_size(&self) -> usize {
        self.window.capacity()
    }

    /// Total number of observations fed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether the window is full.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.window.is_full()
    }

    /// Reset all state.
    #[inline]
    pub fn reset(&mut self) {
        self.window.clear(0.0);
        self.count = 0;
    }
}

impl HurstBuilder {
    /// Rolling window size. Default: 128. At least 32, so that three block
    /// lengths fit; a few hundred or more for a usable estimate.
    #[inline]
    #[must_use]
    pub fn window_size(mut self, size: usize) -> Self {
        self.window_size = Some(size);
        self
    }

    /// Build the Hurst estimator.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError::Invalid` if `window_size` is below 32.
    #[inline]
    pub fn build(self) -> Result<Hurst, crate::ConfigError> {
        let window_size = self.window_size.unwrap_or(128);
        if window_size < MIN_WINDOW {
            return Err(crate::ConfigError::Invalid(
                "window_size must be >= 32: R/S analysis needs three block lengths",
            ));
        }
        Ok(Hurst {
            window: Ring::new(window_size, 0.0)?,
            count: 0,
        })
    }
}

/// `R / S` for one block: the range of the running sum of deviations from
/// the block mean, over the block's (population) standard deviation.
/// `None` for a constant block, which has no scale, and for one whose
/// spread is too small for its squared deviations to be resolved.
#[allow(clippy::cast_precision_loss)]
fn rescaled_range(block: impl Iterator<Item = f64> + Clone, len: usize) -> Option<f64> {
    // Constant is decided by comparing the samples, not by the standard
    // deviation: the mean of `len` copies of a value such as 0.1 is not
    // exactly that value, which leaves every deviation equal to the same
    // rounding residue, a perfect ramp, and `R / S = len`.
    let (mut sum, mut least, mut greatest) = (0.0, f64::INFINITY, f64::NEG_INFINITY);
    for x in block.clone() {
        sum += x;
        least = least.min(x);
        greatest = greatest.max(x);
    }
    #[allow(clippy::float_cmp)]
    if least == greatest {
        return None;
    }
    let mean = sum / len as f64;
    let (mut running, mut low, mut high, mut sum_sq) = (0.0f64, 0.0f64, 0.0f64, 0.0);
    for x in block {
        let deviation = x - mean;
        sum_sq += deviation * deviation;
        running += deviation;
        low = low.min(running);
        high = high.max(running);
    }
    // Not constant, but the squared deviations can still underflow, to
    // zero or into the subnormal range where they carry no precision (a
    // spread below about 1e-146). Such a block has no usable scale either.
    (sum_sq >= RESOLVABLE).then(|| (high - low) / crate::math::sqrt(sum_sq / len as f64))
}

#[cfg(test)]
// Expected values are written as plain arithmetic, independent of the code
// under test.
#[allow(clippy::suboptimal_flops)]
mod tests {
    use super::*;
    use alloc::vec::Vec;

    fn lcg(state: &mut u64) -> f64 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (*state >> 11) as f64 / (1u64 << 53) as f64 - 0.5
    }

    fn fed(window: usize, values: impl IntoIterator<Item = f64>) -> Hurst {
        let mut h = Hurst::builder().window_size(window).build().unwrap();
        for v in values {
            h.update(v);
        }
        h
    }

    /// The method written out on a plain `Vec`, block by block.
    fn reference(samples: &[f64]) -> Option<f64> {
        let total = samples.len();
        let mut points: Vec<(f64, f64)> = Vec::new();
        let mut block = total;
        while block >= 8 {
            let blocks = total / block;
            let tail = &samples[total - blocks * block..];
            let ratios: Vec<f64> = tail
                .chunks_exact(block)
                .filter_map(|c| {
                    let mean = c.iter().sum::<f64>() / block as f64;
                    let sd =
                        (c.iter().map(|x| (x - mean).powi(2)).sum::<f64>() / block as f64).sqrt();
                    let mut cum = 0.0;
                    let (mut lo, mut hi) = (0.0f64, 0.0f64);
                    for x in c {
                        cum += x - mean;
                        lo = lo.min(cum);
                        hi = hi.max(cum);
                    }
                    // A constant block has no scale; decided on the
                    // samples themselves, as the type does.
                    c.iter().any(|x| x != &c[0]).then(|| (hi - lo) / sd)
                })
                .collect();
            if !ratios.is_empty() {
                let mean_ratio = ratios.iter().sum::<f64>() / ratios.len() as f64;
                points.push(((block as f64).ln(), mean_ratio.ln()));
            }
            block /= 2;
        }
        if points.len() < 2 {
            return None;
        }
        let n = points.len() as f64;
        let (sx, sy) = points
            .iter()
            .fold((0.0, 0.0), |a, p| (a.0 + p.0, a.1 + p.1));
        let (sxx, sxy) = points
            .iter()
            .fold((0.0, 0.0), |a, p| (a.0 + p.0 * p.0, a.1 + p.0 * p.1));
        // The textbook raw-sum form of the least-squares slope.
        let (numerator, denominator) = (n * sxy - sx * sy, n * sxx - sx.powi(2));
        Some(numerator / denominator)
    }

    #[test]
    fn matches_the_method_written_out_on_a_vec() {
        let mut state = 17;
        for window in [32usize, 100, 257] {
            let mut h = Hurst::builder().window_size(window).build().unwrap();
            let mut history: Vec<f64> = Vec::new();
            // Past the first wrap of the ring, in several phases.
            for step in 0..3 * window + 5 {
                let x = lcg(&mut state) + if step % 50 < 10 { 0.4 } else { 0.0 };
                h.update(x);
                history.push(x);
                if history.len() < window {
                    assert_eq!(h.hurst(), None);
                    continue;
                }
                let want = reference(&history[history.len() - window..]).unwrap();
                let got = h.hurst().unwrap();
                assert!(
                    (got - want).abs() < 1e-9,
                    "window {window} step {step}: {got} vs {want}"
                );
            }
        }
    }

    #[test]
    fn strict_alternation_has_exponent_zero() {
        // In an even-length block of +1, -1, ... the mean is 0, the
        // deviation is 1 and the running sum only ever visits 0 and 1:
        // R/S = 1 at every block length, a flat line.
        let h = fed(256, (0..256).map(|i| if i % 2 == 0 { 1.0 } else { -1.0 }));
        assert!(h.hurst().unwrap().abs() < 1e-12);
    }

    #[test]
    fn independent_increments_read_a_little_above_one_half() {
        // The method's known small-sample bias: on independent data the
        // slope is above 0.5 and approaches it as the window grows.
        let mean_at = |window: usize| {
            let (mut sum, runs) = (0.0, 200);
            for seed in 0..runs {
                let mut state = 1 + seed;
                let h = fed(window, (0..window).map(|_| lcg(&mut state)));
                sum += h.hurst().unwrap();
            }
            sum / runs as f64
        };
        let (small, large) = (mean_at(128), mean_at(4096));
        assert!(small > 0.55 && small < 0.70, "{small}");
        assert!(large > 0.50 && large < 0.60, "{large}");
        assert!(large < small);
    }

    #[test]
    fn persistence_reads_high_and_reversal_low() {
        let window = 1024;
        // Persistent increments: a slowly decaying average of noise.
        let mut state = 3;
        let mut level = 0.0;
        let persistent = fed(
            window,
            (0..window).map(|_| {
                level = 0.95 * level + lcg(&mut state);
                level
            }),
        );
        // Anti-persistent increments: the change of independent noise.
        let mut state = 3;
        let mut previous = 0.0;
        let reversing = fed(
            window,
            (0..window).map(|_| {
                let x = lcg(&mut state);
                let change = x - previous;
                previous = x;
                change
            }),
        );
        let (high, low) = (persistent.hurst().unwrap(), reversing.hurst().unwrap());
        assert!(high > 0.8, "{high}");
        assert!(low < 0.35, "{low}");
    }

    #[test]
    fn constant_data_has_no_exponent() {
        // 0.1 does not sum exactly: the mean of 8, 16 or 32 copies is a
        // few ulps off 0.1, which a test on the standard deviation alone
        // reads as a perfect trend (exponent 1).
        for value in [5.0, 0.1, -3.3e-7, 1e15 + 0.3, 0.0] {
            for window in [32usize, 64, 100] {
                let h = fed(window, core::iter::repeat_n(value, window));
                assert!(h.is_primed());
                assert_eq!(h.hurst(), None, "value {value} window {window}");
            }
        }
    }

    #[test]
    fn a_spread_too_small_to_square_has_no_exponent() {
        // Not constant, but the squared deviations underflow, to zero or to
        // a subnormal that the division by the block length then rounds to
        // zero: dividing the range by a zero scale would give infinity, and
        // the slope of infinities NaN.
        for (a, b) in [
            (1e-170, 2e-170),
            (0.0, 1e-165),
            (-3e-180, 3e-180),
            (0.0, -7.0e-163),
            (1e-150, 2e-150),
        ] {
            let h = fed(64, (0..64).map(|i| if i % 3 == 0 { a } else { b }));
            assert_eq!(h.hurst(), None, "{a} {b}");
        }
        // Resolvable: a number again, and the same one at any larger scale.
        let at = |scale: f64| {
            fed(
                64,
                (0..64).map(|i| if i % 3 == 0 { scale } else { 2.0 * scale }),
            )
            .hurst()
        };
        let reference = at(1.0).unwrap();
        for scale in [1e-140, 1e-60, 1e60] {
            assert!((at(scale).unwrap() - reference).abs() < 1e-9, "{scale}");
        }
    }

    #[test]
    fn a_stuck_stretch_inside_the_window_is_skipped_not_scored() {
        // The second half of the window is stuck at 0.1. Blocks that fall
        // wholly inside it have no R / S; the estimate comes from the rest
        // and matches the reference, which decides the same way.
        let mut state = 21;
        let mut samples: Vec<f64> = (0..64).map(|_| lcg(&mut state)).collect();
        samples.extend(core::iter::repeat_n(0.1, 64));
        let h = fed(128, samples.iter().copied());
        let got = h.hurst().unwrap();
        assert!((got - reference(&samples).unwrap()).abs() < 1e-9);
        assert!(got < 0.99, "{got}");
    }

    #[test]
    fn primes_when_the_window_fills() {
        let mut h = Hurst::builder().window_size(32).build().unwrap();
        let mut state = 9;
        for _ in 0..31 {
            h.update(lcg(&mut state));
            assert!(!h.is_primed());
            assert_eq!(h.hurst(), None);
        }
        h.update(lcg(&mut state));
        assert!(h.is_primed());
        assert!(h.hurst().is_some());
        assert_eq!(h.count(), 32);
        assert_eq!(h.window_size(), 32);
    }

    #[test]
    fn reset_clears_state() {
        let mut state = 4;
        let mut h = fed(32, (0..100).map(|_| lcg(&mut state)));
        h.reset();
        assert_eq!(h.count(), 0);
        assert!(!h.is_primed());
        assert_eq!(h.hurst(), None);
    }

    #[test]
    fn builder_validation() {
        assert_eq!(
            Hurst::builder().window_size(31).build().unwrap_err(),
            crate::ConfigError::Invalid(
                "window_size must be >= 32: R/S analysis needs three block lengths"
            )
        );
        assert_eq!(Hurst::builder().build().unwrap().window_size(), 128);
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut h = Hurst::builder().build().unwrap();
        assert_eq!(
            h.checked_update(f64::NAN),
            Err(crate::DataError::NotANumber)
        );
        assert_eq!(
            h.checked_update(f64::INFINITY),
            Err(crate::DataError::Infinite)
        );
        assert_eq!(h.count(), 0);
    }
}
