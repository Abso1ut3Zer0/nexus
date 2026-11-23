use alloc::boxed::Box;
use core::marker::PhantomData;

use nexus_stats_core::Float;
use nexus_stats_core::math::MulAdd;

/// Quantile normalizer: a value's approximate rank in `[0, 1]`.
///
/// Ranks a value among the samples seen using a P² histogram (Jain &
/// Chlamtac, "The P² algorithm for dynamic calculation of quantiles and
/// histograms without storing observations", CACM 1985).
///
/// The histogram keeps `resolution + 2` markers: the minimum, the maximum,
/// and `resolution` interior markers tracking the quantiles
/// `1/(resolution+1), ..., resolution/(resolution+1)`. Each marker holds a
/// height (a value) and a position (how many samples lie at or below it);
/// a sample moves the positions and nudges each interior height toward its
/// quantile. The rank of a value is interpolated between the two markers
/// that bracket it, so it is non-decreasing in the value, exactly 0 below
/// the minimum seen and exactly 1 above the maximum. It is continuous
/// except at a value several markers share (a value that makes up a large
/// part of the stream), where it steps from the bottom of that run to the
/// top and reads the middle on the value itself.
///
/// # Accuracy
///
/// Interpolation between markers is linear in the value, so the rank is
/// off by at most the probability in one cell, `1 / (resolution + 1)`,
/// plus the markers' own estimation error. The bound is approached where a
/// cell is far from uniform: one that spans a gap in the distribution, or
/// an end cell of a long-tailed distribution, which runs out to the
/// largest sample seen. Typical error is one to two orders of magnitude
/// smaller. If the tails matter, raise the resolution.
///
/// O(resolution) per update over two contiguous arrays. Fixed memory:
/// `16 * (resolution + 2)` bytes. Requires `alloc`.
///
/// Heights are differences and interpolations of samples, so samples whose
/// spread exceeds `f64::MAX` (for example `-1e308` and `1e308`) overflow
/// them; keep inputs within a range whose differences are finite.
///
/// The histogram is all-time: every sample since construction or
/// [`reset`](Self::reset) counts equally.
///
/// `T` is the sample type at the boundary, `f64` or `f32`; the histogram
/// runs in `f64` either way.
///
/// # Examples
///
/// ```
/// use nexus_stats_normalization::QuantileNorm;
///
/// let mut qn = QuantileNorm::<f64>::builder().resolution(9).build().unwrap();
/// for i in 0..1000 {
///     let _ = qn.update(f64::from(i)).unwrap();
/// }
/// // 0..1000 is uniform, so the rank of a value is close to value / 1000.
/// let r = qn.normalize(250.0).unwrap().unwrap();
/// assert!((r - 0.25).abs() < 0.02);
/// assert_eq!(qn.normalize(-5.0).unwrap(), Some(0.0));
/// assert_eq!(qn.normalize(5000.0).unwrap(), Some(1.0));
/// ```
#[derive(Debug, Clone)]
pub struct QuantileNorm<T: Float> {
    /// Marker heights, non-decreasing. While filling (the first
    /// `heights.len()` samples) the leading `count` entries are the sorted
    /// samples.
    heights: Box<[f64]>,
    /// Marker positions, 1-based and strictly increasing once filled:
    /// `positions[i]` samples lie at or below `heights[i]`. Kept as `f64`
    /// because every use is in floating-point arithmetic.
    positions: Box<[f64]>,
    count: u64,
    min_samples: u64,
    _sample: PhantomData<T>,
}

/// Builder for [`QuantileNorm`].
#[derive(Debug, Clone)]
pub struct QuantileNormBuilder<T: Float> {
    resolution: Option<usize>,
    min_samples: Option<u64>,
    _sample: PhantomData<T>,
}

impl<T: Float> QuantileNorm<T> {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> QuantileNormBuilder<T> {
        QuantileNormBuilder {
            resolution: None,
            min_samples: None,
            _sample: PhantomData,
        }
    }

    /// Folds a sample into the histogram, then returns its rank in
    /// `[0, 1]` among everything seen including itself, or `Ok(None)` until
    /// `min_samples` samples have been fed.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    #[inline]
    pub fn update(&mut self, sample: T) -> Result<Option<T>, nexus_stats_core::DataError> {
        check_finite!(sample);
        let x = sample.to_f64();
        // Compared in `u64`: a `usize` cast would wrap on a 32-bit target
        // after 2^32 samples and re-enter the fill.
        if self.count < self.heights.len() as u64 {
            self.fill(x);
        } else {
            self.fold(x);
        }
        Ok(self.rank(x))
    }

    /// Ranks an arbitrary value against the current histogram without
    /// updating state. `Ok(None)` if not primed.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the value is NaN, or
    /// `DataError::Infinite` if the value is infinite.
    #[inline]
    pub fn normalize(&self, value: T) -> Result<Option<T>, nexus_stats_core::DataError> {
        check_finite!(value);
        Ok(self.rank(value.to_f64()))
    }

    /// Number of interior quantile markers.
    #[inline]
    #[must_use]
    pub fn resolution(&self) -> usize {
        self.heights.len() - 2
    }

    /// Total samples processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether `min_samples` samples have been fed and ranks are available.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.min_samples
    }

    /// Forgets every sample. Resolution and `min_samples` are kept.
    #[inline]
    pub fn reset(&mut self) {
        self.count = 0;
    }

    /// One of the first `heights.len()` samples: insert it into the sorted
    /// prefix. When the prefix fills, every marker is a sample and marker
    /// `i` sits at position `i + 1`.
    fn fill(&mut self, x: f64) {
        let n = self.count as usize;
        let at = self.heights[..n].partition_point(|&h| h <= x);
        self.heights.copy_within(at..n, at + 1);
        self.heights[at] = x;
        self.count += 1;
        if n + 1 == self.heights.len() {
            for (i, p) in self.positions.iter_mut().enumerate() {
                *p = (i + 1) as f64;
            }
        }
    }

    /// The P² histogram step for a sample after the fill.
    #[allow(clippy::cast_precision_loss)]
    fn fold(&mut self, x: f64) {
        let heights = &mut *self.heights;
        let positions = &mut *self.positions;
        let last = heights.len() - 1;

        // The cell the sample falls in; a new extreme moves the end marker.
        let cell = if x < heights[0] {
            heights[0] = x;
            0
        } else if x >= heights[last] {
            heights[last] = x;
            last - 1
        } else {
            heights.partition_point(|&h| h <= x) - 1
        };
        for p in &mut positions[cell + 1..] {
            *p += 1.0;
        }
        self.count += 1;

        // Move each interior marker one position toward where its quantile
        // now sits, `1 + i * (count - 1) / last`, if it is a whole position
        // off and there is room. The height follows by the piecewise
        // parabolic formula, or linearly when the parabola would leave the
        // neighbours' range.
        let step = (self.count - 1) as f64 / last as f64;
        for i in 1..last {
            // Not fused: whether a marker moves is a threshold on this
            // value, and a fused multiply-add would round it differently
            // on targets with and without FMA, giving different markers for
            // the same input.
            #[allow(clippy::suboptimal_flops)]
            let off = i as f64 * step + 1.0 - positions[i];
            let gap_up = positions[i + 1] - positions[i];
            let gap_down = positions[i - 1] - positions[i];
            let s = if off >= 1.0 && gap_up > 1.0 {
                1.0
            } else if off <= -1.0 && gap_down < -1.0 {
                -1.0
            } else {
                continue;
            };
            let (below, here, above) = (heights[i - 1], heights[i], heights[i + 1]);
            let slope_up = (above - here) / gap_up;
            let slope_down = (below - here) / gap_down;
            let parabolic = (s / (gap_up - gap_down)).fma(
                (s - gap_down).fma(slope_up, (gap_up - s) * slope_down),
                here,
            );
            heights[i] = if below < parabolic && parabolic < above {
                parabolic
            } else if s > 0.0 {
                here + slope_up
            } else {
                here - slope_down
            };
            positions[i] += s;
        }
    }

    /// Rank of `value` in `[0, 1]`: 0 below the lowest marker, 1 above the
    /// highest, the marker's own rank on a marker (the middle of the run
    /// when several markers share the value), interpolated between the
    /// bracketing markers otherwise.
    #[allow(clippy::cast_precision_loss)]
    fn rank(&self, value: f64) -> Option<T> {
        if !self.is_primed() {
            return None;
        }
        let heights = &*self.heights;
        let positions = &*self.positions;
        let span = (self.count - 1) as f64;

        let below = heights.partition_point(|&h| h < value);
        let at_or_below = heights.partition_point(|&h| h <= value);
        let rank = if below < at_or_below {
            // On one or more markers.
            f64::midpoint(positions[below], positions[at_or_below - 1]) - 1.0
        } else if below == 0 {
            0.0
        } else if below == heights.len() {
            span
        } else {
            let (lo, hi) = (below - 1, below);
            let t = (value - heights[lo]) / (heights[hi] - heights[lo]);
            t.fma(positions[hi] - positions[lo], positions[lo]) - 1.0
        };
        Some(T::from_f64(rank / span))
    }
}

impl<T: Float> QuantileNormBuilder<T> {
    /// Number of interior quantile markers (required, at least 1).
    ///
    /// Markers track the quantiles `1/(n+1), 2/(n+1), ..., n/(n+1)`:
    /// resolution 9 tracks the deciles. More markers follow the shape of
    /// the distribution more closely and cost proportionally more per
    /// update.
    #[inline]
    #[must_use]
    pub fn resolution(mut self, n: usize) -> Self {
        self.resolution = Some(n);
        self
    }

    /// Minimum samples before ranks are returned. Default and minimum:
    /// `resolution + 2`, the samples needed to place every marker.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, n: u64) -> Self {
        self.min_samples = Some(n);
        self
    }

    /// Builds the quantile normalizer.
    ///
    /// # Errors
    ///
    /// - `Missing("resolution")` if the resolution was not set.
    /// - `Invalid` if the resolution is 0, or `min_samples` is below
    ///   `resolution + 2`.
    #[inline]
    pub fn build(self) -> Result<QuantileNorm<T>, nexus_stats_core::ConfigError> {
        let resolution = self
            .resolution
            .ok_or(nexus_stats_core::ConfigError::Missing("resolution"))?;
        if resolution == 0 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "resolution must be >= 1",
            ));
        }
        let markers = resolution
            .checked_add(2)
            .ok_or(nexus_stats_core::ConfigError::Invalid(
                "resolution is too large",
            ))?;
        let floor = markers as u64;
        let min_samples = self.min_samples.unwrap_or(floor);
        if min_samples < floor {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "min_samples must be at least resolution + 2",
            ));
        }

        Ok(QuantileNorm {
            heights: alloc::vec![0.0; markers].into_boxed_slice(),
            positions: alloc::vec![0.0; markers].into_boxed_slice(),
            count: 0,
            min_samples,
            _sample: PhantomData,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec::Vec;

    type Transform = fn(f64) -> f64;

    /// Deterministic uniform in [0, 1).
    fn lcg(state: &mut u64) -> f64 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (*state >> 11) as f64 / (1u64 << 53) as f64
    }

    /// The histogram's structural invariants, checked after every update:
    /// heights ordered, positions strictly increasing from 1 to count.
    fn assert_invariants(qn: &QuantileNorm<f64>) {
        let n = qn.heights.len();
        if qn.count < n as u64 {
            return;
        }
        assert!(qn.heights.windows(2).all(|w| w[0] <= w[1]), "{qn:?}");
        assert!(qn.positions.windows(2).all(|w| w[0] < w[1]), "{qn:?}");
        assert_eq!(qn.positions[0], 1.0);
        assert_eq!(qn.positions[n - 1], qn.count as f64);
    }

    /// Exact rank by the same convention, from the stored samples.
    fn exact_rank(sorted: &[f64], value: f64) -> f64 {
        let below = sorted.partition_point(|&s| s < value);
        let at_or_below = sorted.partition_point(|&s| s <= value);
        let span = (sorted.len() - 1) as f64;
        if below < at_or_below {
            (below + at_or_below - 1) as f64 / 2.0 / span
        } else if below == 0 {
            0.0
        } else if below == sorted.len() {
            1.0
        } else {
            let t = (value - sorted[below - 1]) / (sorted[below] - sorted[below - 1]);
            (below as f64 - 1.0 + t) / span
        }
    }

    #[test]
    fn exact_while_every_marker_is_a_sample() {
        // resolution 3: five markers. After exactly five samples the
        // histogram is the sorted samples at positions 1..=5.
        let mut qn = QuantileNorm::<f64>::builder()
            .resolution(3)
            .build()
            .unwrap();
        for x in [30.0, 10.0, 50.0, 20.0] {
            assert_eq!(qn.update(x).unwrap(), None);
        }
        // The fifth sample primes; it is the 4th of 5 by value.
        assert_eq!(qn.update(40.0).unwrap(), Some(0.75));
        assert_eq!(&*qn.heights, &[10.0, 20.0, 30.0, 40.0, 50.0]);
        for (v, r) in [
            (5.0, 0.0),
            (10.0, 0.0),
            (15.0, 0.125),
            (30.0, 0.5),
            (45.0, 0.875),
            (50.0, 1.0),
            (99.0, 1.0),
        ] {
            assert_eq!(qn.normalize(v).unwrap(), Some(r), "value {v}");
        }
    }

    /// Worst and mean absolute rank error over 201 evenly spaced sample
    /// quantiles, against the exact rank from the stored samples.
    fn rank_errors(resolution: usize, transform: Transform) -> (f64, f64) {
        let mut qn = QuantileNorm::<f64>::builder()
            .resolution(resolution)
            .build()
            .unwrap();
        let mut state = 7;
        let mut samples = Vec::new();
        for _ in 0..20_000 {
            let x = transform(lcg(&mut state));
            let _ = qn.update(x).unwrap();
            samples.push(x);
            assert_invariants(&qn);
        }
        samples.sort_by(f64::total_cmp);
        let (mut worst, mut sum) = (0.0f64, 0.0);
        for i in 0..=200 {
            let v = samples[i * (samples.len() - 1) / 200];
            let e = (qn.normalize(v).unwrap().unwrap() - exact_rank(&samples, v)).abs();
            worst = worst.max(e);
            sum += e;
        }
        (worst, sum / 201.0)
    }

    #[test]
    fn rank_error_is_about_one_cell_at_worst_and_small_on_average() {
        // Between two markers the rank is interpolated linearly in the
        // value, so the error is bounded by the probability in one cell,
        // 1 / (resolution + 1), reached where a cell holds a gap or a long
        // tail. Resolution 19: cells of 0.05.
        let streams: [(&str, Transform, f64, f64); 3] = [
            // Linear interpolation is exact for a uniform density.
            ("uniform", |u| u, 0.005, 0.001),
            // Long right tail: the last cell runs out to the maximum.
            (
                "exponential",
                |u| -nexus_stats_core::math::ln(1.0 - u),
                0.05,
                0.004,
            ),
            // A gap with no samples in the middle of one cell.
            (
                "bimodal",
                |u| if u < 0.3 { u } else { 10.0 + u },
                0.0525,
                0.006,
            ),
        ];
        for (name, transform, worst_bound, mean_bound) in streams {
            let (worst, mean) = rank_errors(19, transform);
            assert!(worst < worst_bound, "{name}: worst rank error {worst}");
            assert!(mean < mean_bound, "{name}: mean rank error {mean}");
        }
    }

    #[test]
    fn marker_adjustment_matches_the_p2_formulas() {
        // Four markers at positions 1, 4, 5, 6 of six samples. A seventh
        // sample below the minimum shifts the upper three to 5, 6, 7 while
        // the interior targets are 3 and 5, so both interior markers move
        // down one position.
        let mut qn = QuantileNorm::<f64>::builder()
            .resolution(2)
            .build()
            .unwrap();
        qn.heights.copy_from_slice(&[4.9, 5.0, 50.0, 100.0]);
        qn.positions.copy_from_slice(&[1.0, 4.0, 5.0, 6.0]);
        qn.count = 6;
        let _ = qn.update(0.5).unwrap();
        assert_eq!(&*qn.positions, &[1.0, 4.0, 5.0, 7.0]);
        // Marker 1: the parabola through (1, 0.5), (5, 5), (6, 50) at
        // position 4 gives -22.45, below its lower neighbour, so the linear
        // step applies: 5 - (5 - 0.5) / (5 - 1).
        assert_eq!(qn.heights[1], 3.875);
        // Marker 2: the parabola through (4, 3.875), (6, 50), (7, 100) at
        // position 5 stays between its neighbours.
        let expected = 50.0 - (50.0 + (50.0 - 3.875)) / 3.0;
        assert!(
            (qn.heights[2] - expected).abs() < 1e-12,
            "{}",
            qn.heights[2]
        );
        assert_eq!(qn.heights[0], 0.5);
        assert_eq!(qn.heights[3], 100.0);
    }

    #[test]
    fn upward_marker_moves_match_the_p2_formulas() {
        // Positions 1, 2, 3, 6 of six samples; a seventh at or above the
        // maximum moves the top marker to 7. Marker 1 is one position short
        // of its target (3) but has no room below marker 2, so it stays.
        // Marker 2 is two short of its target (5) and moves up one.
        let setup = |heights: [f64; 4]| {
            let mut qn = QuantileNorm::<f64>::builder()
                .resolution(2)
                .build()
                .unwrap();
            qn.heights.copy_from_slice(&heights);
            qn.positions.copy_from_slice(&[1.0, 2.0, 3.0, 6.0]);
            qn.count = 6;
            qn
        };

        // Parabolic: through (2, 50), (3, 95), (7, 200) at position 4:
        // 95 + (1/5) * (2 * 105/4 + 3 * 45) = 132.5.
        let mut qn = setup([0.0, 50.0, 95.0, 100.0]);
        let _ = qn.update(200.0).unwrap();
        assert_eq!(&*qn.positions, &[1.0, 2.0, 4.0, 7.0]);
        assert_eq!(&*qn.heights, &[0.0, 50.0, 132.5, 200.0]);

        // Linear: the parabola through (2, 10), (3, 95), (7, 100) gives
        // 146.5, above the upper neighbour, so step along the upper chord:
        // 95 + (100 - 95) / 4.
        let mut qn = setup([0.0, 10.0, 95.0, 100.0]);
        let _ = qn.update(100.0).unwrap();
        assert_eq!(&*qn.positions, &[1.0, 2.0, 4.0, 7.0]);
        assert_eq!(&*qn.heights, &[0.0, 10.0, 96.25, 100.0]);
    }

    #[test]
    fn rank_steps_across_a_value_several_markers_share() {
        // Five markers on the samples 1, 2, 2, 2, 3: the three 2s are
        // positions 2..=4 of 5.
        let mut qn = QuantileNorm::<f64>::builder()
            .resolution(3)
            .build()
            .unwrap();
        for x in [2.0, 1.0, 2.0, 3.0, 2.0] {
            let _ = qn.update(x).unwrap();
        }
        let rank = |v: f64| qn.normalize(v).unwrap().unwrap();
        assert_eq!(rank(1.5), 0.125);
        // Approaching the run from below reaches its bottom, the value
        // itself reads its middle, and leaving it starts from its top.
        assert!((rank(2.0 - 1e-9) - 0.25).abs() < 1e-8);
        assert_eq!(rank(2.0), 0.5);
        assert!((rank(2.0 + 1e-9) - 0.75).abs() < 1e-8);
        assert_eq!(rank(2.5), 0.875);
    }

    #[test]
    fn rank_is_monotone_and_bounded() {
        let mut qn = QuantileNorm::<f64>::builder()
            .resolution(9)
            .build()
            .unwrap();
        let mut state = 99;
        for _ in 0..5_000 {
            let u = lcg(&mut state);
            let _ = qn.update(u * u * 100.0).unwrap();
        }
        let mut previous = -1.0;
        for i in -50..=1_100 {
            let r = qn.normalize(f64::from(i) * 0.1).unwrap().unwrap();
            assert!((0.0..=1.0).contains(&r));
            assert!(r >= previous, "rank fell at {i}: {previous} -> {r}");
            previous = r;
        }
        assert_eq!(qn.normalize(-1.0).unwrap(), Some(0.0));
        assert_eq!(qn.normalize(1e9).unwrap(), Some(1.0));
    }

    #[test]
    fn update_returns_the_rank_including_the_sample() {
        let mut qn = QuantileNorm::<f64>::builder()
            .resolution(9)
            .build()
            .unwrap();
        for i in 0..1_000 {
            let _ = qn.update(f64::from(i)).unwrap();
        }
        // A new maximum and a new minimum rank at the ends immediately.
        assert_eq!(qn.update(5_000.0).unwrap(), Some(1.0));
        assert_eq!(qn.update(-5_000.0).unwrap(), Some(0.0));
        let r = qn.update(500.0).unwrap().unwrap();
        assert!((r - 0.5).abs() < 0.02, "{r}");
    }

    #[test]
    fn degenerate_streams_keep_the_invariants() {
        #[allow(clippy::type_complexity)]
        let streams: [(&str, fn(u32) -> f64); 4] = [
            ("ascending", f64::from),
            ("descending", |i| -f64::from(i)),
            ("constant", |_| 42.0),
            ("two values", |i| f64::from(i % 2)),
        ];
        for (name, stream) in streams {
            let mut qn = QuantileNorm::<f64>::builder()
                .resolution(5)
                .build()
                .unwrap();
            for i in 0..2_000 {
                let r = qn.update(stream(i)).unwrap();
                assert_invariants(&qn);
                if let Some(r) = r {
                    assert!((0.0..=1.0).contains(&r), "{name}: {r}");
                }
            }
        }
        // A constant stream ranks its one value in the middle.
        let mut qn = QuantileNorm::<f64>::builder()
            .resolution(5)
            .build()
            .unwrap();
        for _ in 0..100 {
            let _ = qn.update(42.0).unwrap();
        }
        assert_eq!(qn.normalize(42.0).unwrap(), Some(0.5));
        assert_eq!(qn.normalize(41.0).unwrap(), Some(0.0));
        assert_eq!(qn.normalize(43.0).unwrap(), Some(1.0));
    }

    #[test]
    fn finer_resolution_follows_the_shape_more_closely() {
        // A two-level distribution: 90% near 0, 10% near 100.
        let two_level: Transform = |u| if u < 0.9 { u } else { 100.0 + u };
        let (coarse_worst, coarse_mean) = rank_errors(3, two_level);
        let (fine_worst, fine_mean) = rank_errors(39, two_level);
        assert!(
            fine_worst < coarse_worst / 3.0,
            "{coarse_worst} {fine_worst}"
        );
        assert!(fine_mean < coarse_mean / 8.0, "{coarse_mean} {fine_mean}");
    }

    #[test]
    fn f32_boundary() {
        let mut qn = QuantileNorm::<f32>::builder()
            .resolution(3)
            .build()
            .unwrap();
        for x in [30.0, 10.0, 50.0, 20.0] {
            assert_eq!(qn.update(x).unwrap(), None);
        }
        assert_eq!(qn.update(40.0).unwrap(), Some(0.75f32));
    }

    #[test]
    fn rejects_nan_inf() {
        let mut qn = QuantileNorm::<f64>::builder()
            .resolution(4)
            .build()
            .unwrap();
        assert_eq!(
            qn.update(f64::NAN),
            Err(nexus_stats_core::DataError::NotANumber)
        );
        assert_eq!(
            qn.update(f64::INFINITY),
            Err(nexus_stats_core::DataError::Infinite)
        );
        assert_eq!(
            qn.normalize(f64::NAN),
            Err(nexus_stats_core::DataError::NotANumber)
        );
        assert_eq!(
            qn.normalize(f64::NEG_INFINITY),
            Err(nexus_stats_core::DataError::Infinite)
        );
        assert_eq!(qn.count(), 0);
    }

    #[test]
    fn builder_validation() {
        use nexus_stats_core::ConfigError::{Invalid, Missing};
        let b = QuantileNorm::<f64>::builder;
        assert_eq!(b().build().unwrap_err(), Missing("resolution"));
        assert_eq!(
            b().resolution(0).build().unwrap_err(),
            Invalid("resolution must be >= 1")
        );
        // One interior marker is the smallest histogram: min, median, max.
        let mut median = b().resolution(1).build().unwrap();
        for x in [3.0, 1.0, 2.0] {
            let _ = median.update(x).unwrap();
        }
        assert_eq!(median.normalize(2.0).unwrap(), Some(0.5));
        assert_eq!(
            b().resolution(9).min_samples(10).build().unwrap_err(),
            Invalid("min_samples must be at least resolution + 2")
        );
        let qn = b().resolution(9).min_samples(11).build().unwrap();
        assert_eq!(qn.resolution(), 9);
        // A larger min_samples withholds the rank past the fill.
        let mut qn = b().resolution(2).min_samples(6).build().unwrap();
        for i in 0..5 {
            assert_eq!(qn.update(f64::from(i)).unwrap(), None);
        }
        assert!(qn.update(5.0).unwrap().is_some());
    }

    #[test]
    fn reset_clears() {
        let mut qn = QuantileNorm::<f64>::builder()
            .resolution(4)
            .build()
            .unwrap();
        for i in 0..200 {
            let _ = qn.update(f64::from(i)).unwrap();
        }
        assert!(qn.is_primed());
        qn.reset();
        assert_eq!(qn.count(), 0);
        assert!(!qn.is_primed());
        assert_eq!(qn.normalize(50.0).unwrap(), None);
        // Refills from scratch: the old heights are not consulted.
        for x in [3.0, 1.0, 2.0, 5.0, 4.0, 6.0] {
            let _ = qn.update(x).unwrap();
        }
        assert_eq!(&*qn.heights, &[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]);
    }
}
