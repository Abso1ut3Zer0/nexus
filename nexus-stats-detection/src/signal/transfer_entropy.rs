// Transfer Entropy — Directed Information Flow
//
// TE(X→Y) = H(Y_t | Y_{t-LAG}) - H(Y_t | Y_{t-LAG}, X_{t-LAG})
//
// "How much does knowing X's past reduce uncertainty about Y's future?"
// Positive TE(X→Y) means X provides predictive information about Y
// beyond Y's own history.
//
// Joint frequency tables are heap-allocated (Box<[u64]>) because
// BINS³ grows cubically. BINS and LAG are runtime-configured via builder.

use alloc::boxed::Box;
use alloc::vec;
use nexus_stats_core::storage::Ring;

/// Directed information flow estimator between two discretized streams.
///
/// Measures transfer entropy in both directions (X→Y and Y→X) from
/// a single instance. Maintains joint frequency tables for the
/// conditional entropy computation.
///
/// Inputs must be pre-discretized into bins `0..bins`. The choice of
/// binning affects results — too few bins loses resolution, too many
/// bins requires more data to populate the joint table.
///
/// BINS and LAG are configured at construction via the builder.
/// LAG controls how far back to look — comparing X_{t-LAG} with Y_t
/// instead of X_{t-1} with Y_t.
///
/// Computes population (not sample-corrected) transfer entropy.
///
/// # Memory
///
/// `2 × bins³ × 8 + 2 × bins² × 8` bytes for the joint and marginal
/// frequency tables (both directions), plus `2 × lag` elements for
/// history buffers.
///
/// | bins | Memory  |
/// |------|---------|
/// | 4    | ~1.3 KB |
/// | 8    | ~9 KB   |
/// | 16   | ~131 KB |
///
/// # Use Cases
/// - "Does metric A predict changes in metric B?"
/// - Granger-causality proxy without regression
/// - Detecting leading/lagging relationships between discretized signals
///
/// # Complexity
/// - O(1) per update, O(bins³) per entropy query.
///
/// # Examples
///
/// ```
/// use nexus_stats_detection::signal::TransferEntropy;
///
/// // X causes Y: Y_t = X_{t-1}, X is pseudo-random
/// let mut te = TransferEntropy::builder()
///     .bins(4)
///     .lag(1)
///     .build()
///     .unwrap();
/// let mut prev_x = 0usize;
/// let mut rng = 42u64;
/// for _ in 0..10000 {
///     rng = rng.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
///     let x_bin = ((rng >> 62) as usize) % 4;
///     let y_bin = prev_x;
///     te.update(x_bin, y_bin);
///     prev_x = x_bin;
/// }
/// let te_xy = te.te_x_to_y().unwrap();
/// let te_yx = te.te_y_to_x().unwrap();
/// assert!(te_xy > te_yx);
/// ```
#[derive(Debug, Clone)]
pub struct TransferEntropy {
    /// Joint counts: P(X_{t-LAG}, Y_{t-LAG}, Y_t) — flat bins³ array.
    joint_xy: Box<[u64]>,
    /// Joint counts: P(Y_{t-LAG}, X_{t-LAG}, X_t) — flat bins³ array.
    joint_yx: Box<[u64]>,
    /// Marginal counts: P(Y_{t-LAG}, Y_t) — flat bins² array.
    marginal_y: Box<[u64]>,
    /// Marginal counts: P(X_{t-LAG}, X_t) — flat bins² array.
    marginal_x: Box<[u64]>,
    /// Circular buffer for X history (LAG elements).
    hist_x: Ring<usize>,
    /// Circular buffer for Y history (LAG elements).
    hist_y: Ring<usize>,
    /// Number of discretization bins.
    bins: usize,
    /// Lookback depth.
    lag: usize,
    /// Total paired transitions observed.
    total: u64,
}

/// Builder for [`TransferEntropy`].
#[derive(Debug, Clone)]
pub struct TransferEntropyBuilder {
    bins: Option<usize>,
    lag: Option<usize>,
}

impl TransferEntropy {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> TransferEntropyBuilder {
        TransferEntropyBuilder {
            bins: Option::None,
            lag: Option::None,
        }
    }

    /// Index into a flat bins³ array: `[a][b][c]`.
    #[inline]
    fn idx3(&self, a: usize, b: usize, c: usize) -> usize {
        a * self.bins * self.bins + b * self.bins + c
    }

    /// Index into a flat bins² array: `[a][b]`.
    #[inline]
    fn idx2(&self, a: usize, b: usize) -> usize {
        a * self.bins + b
    }

    /// Updates with discretized observations from both streams.
    ///
    /// `x_bin` and `y_bin` must be in `0..bins`.
    ///
    /// # Panics
    ///
    /// Panics if `x_bin >= bins` or `y_bin >= bins`.
    #[inline]
    pub fn update(&mut self, x_bin: usize, y_bin: usize) {
        let bins = self.bins;
        assert!(x_bin < bins, "x_bin {x_bin} out of range (bins={bins})");
        assert!(y_bin < bins, "y_bin {y_bin} out of range (bins={bins})");

        // `push` hands back the bins from `lag` steps ago once the rings are full.
        if let (Some(xp), Some(yp)) = (self.hist_x.push(x_bin), self.hist_y.push(y_bin)) {
            // TE(X→Y): joint[x_lagged][y_lagged][y_curr]
            let i = self.idx3(xp, yp, y_bin);
            self.joint_xy[i] += 1;
            // TE(Y→X): joint[y_lagged][x_lagged][x_curr]
            let i = self.idx3(yp, xp, x_bin);
            self.joint_yx[i] += 1;

            // Marginals
            let i = self.idx2(yp, y_bin);
            self.marginal_y[i] += 1;
            let i = self.idx2(xp, x_bin);
            self.marginal_x[i] += 1;

            self.total += 1;
        }
    }

    /// Transfer entropy from X to Y (in nats), or `None` if insufficient data.
    ///
    /// Measures how much knowing X's past reduces uncertainty about Y's future,
    /// beyond what Y's own past provides.
    #[must_use]
    pub fn te_x_to_y(&self) -> Option<f64> {
        if self.total == 0 {
            return Option::None;
        }
        Option::Some(self.compute_te(&self.joint_xy, &self.marginal_y))
    }

    /// Transfer entropy from Y to X (in nats), or `None` if insufficient data.
    ///
    /// Measures how much knowing Y's past reduces uncertainty about X's future,
    /// beyond what X's own past provides.
    #[must_use]
    pub fn te_y_to_x(&self) -> Option<f64> {
        if self.total == 0 {
            return Option::None;
        }
        Option::Some(self.compute_te(&self.joint_yx, &self.marginal_x))
    }

    /// Net information flow: `TE(X→Y) - TE(Y→X)`.
    ///
    /// Positive = X leads Y. Negative = Y leads X.
    /// Returns `None` if insufficient data.
    #[must_use]
    pub fn net_flow(&self) -> Option<f64> {
        let te_xy = self.te_x_to_y()?;
        let te_yx = self.te_y_to_x()?;
        Option::Some(te_xy - te_yx)
    }

    /// Total paired transitions observed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.total
    }

    /// Number of discretization bins.
    #[inline]
    #[must_use]
    pub fn bins(&self) -> usize {
        self.bins
    }

    /// Lookback depth (lag).
    #[inline]
    #[must_use]
    pub fn lag(&self) -> usize {
        self.lag
    }

    /// Primed after at least one transition (LAG + 1 observations).
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.total > 0
    }

    /// Resets to empty state. Heap allocations are preserved.
    pub fn reset(&mut self) {
        self.joint_xy.fill(0);
        self.joint_yx.fill(0);
        self.marginal_y.fill(0);
        self.marginal_x.fill(0);
        self.hist_x.clear(0);
        self.hist_y.clear(0);
        self.total = 0;
    }

    /// Compute TE from joint and marginal tables.
    ///
    /// TE = Σ P(a, b, c) * ln( P(c | b, a) / P(c | b) )
    ///    = Σ P(a, b, c) * ln( P(a, b, c) * P(b) / (P(b, c) * P(a, b)) )
    ///
    /// where a = source_lagged, b = target_lagged, c = target_curr.
    fn compute_te(&self, joint: &[u64], marginal: &[u64]) -> f64 {
        let n = self.total as f64;
        let bins = self.bins;
        let mut te = 0.0;

        // Precompute P(b) = Σ_c marginal[b][c] for all b.
        // Hoisted outside the (a, b) loop — depends only on b.
        let mut marginal_b_sums = [0u64; 32]; // max bins is 32 (validated by builder)
        for b in 0..bins {
            let mut sum = 0u64;
            for c in 0..bins {
                sum += marginal[self.idx2(b, c)];
            }
            marginal_b_sums[b] = sum;
        }

        for a in 0..bins {
            for b in 0..bins {
                // P(a, b) = Σ_c joint[a][b][c]
                let mut joint_ab = 0u64;
                for c in 0..bins {
                    joint_ab += joint[self.idx3(a, b, c)];
                }
                if joint_ab == 0 {
                    continue;
                }

                let marginal_b = marginal_b_sums[b];
                if marginal_b == 0 {
                    continue;
                }

                for c in 0..bins {
                    let joint_abc = joint[self.idx3(a, b, c)];
                    if joint_abc == 0 {
                        continue;
                    }
                    let marginal_bc = marginal[self.idx2(b, c)];
                    if marginal_bc == 0 {
                        continue;
                    }

                    // P(abc) * ln(P(abc) * P(b) / (P(bc) * P(ab)))
                    let p_abc = joint_abc as f64 / n;
                    let ratio = (joint_abc as f64 * marginal_b as f64)
                        / (marginal_bc as f64 * joint_ab as f64);
                    te += p_abc * nexus_stats_core::math::ln(ratio);
                }
            }
        }

        te
    }
}

impl TransferEntropyBuilder {
    /// Number of discretization bins. Required.
    #[inline]
    #[must_use]
    pub fn bins(mut self, bins: usize) -> Self {
        self.bins = Option::Some(bins);
        self
    }

    /// Lookback depth. Required.
    ///
    /// LAG=1 compares X_{t-1} with Y_t. LAG=3 compares X_{t-3} with Y_t.
    #[inline]
    #[must_use]
    pub fn lag(mut self, lag: usize) -> Self {
        self.lag = Option::Some(lag);
        self
    }

    /// Builds the transfer entropy estimator.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError::Missing` if `bins` or `lag` not set.
    /// Returns `ConfigError::Invalid` if `bins < 2` or `lag < 1`.
    #[inline]
    pub fn build(self) -> Result<TransferEntropy, nexus_stats_core::ConfigError> {
        let bins = self
            .bins
            .ok_or(nexus_stats_core::ConfigError::Missing("bins"))?;
        let lag = self
            .lag
            .ok_or(nexus_stats_core::ConfigError::Missing("lag"))?;

        if bins < 2 {
            return Err(nexus_stats_core::ConfigError::Invalid("bins must be >= 2"));
        }
        if bins > 32 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "bins must be <= 32 (bins^3 table growth; 16 or fewer recommended)",
            ));
        }
        if lag < 1 {
            return Err(nexus_stats_core::ConfigError::Invalid("lag must be >= 1"));
        }

        let bins_sq = bins
            .checked_mul(bins)
            .ok_or(nexus_stats_core::ConfigError::Invalid(
                "bins too large (bins² overflows)",
            ))?;
        let bins_cu = bins_sq
            .checked_mul(bins)
            .ok_or(nexus_stats_core::ConfigError::Invalid(
                "bins too large (bins³ overflows)",
            ))?;

        Ok(TransferEntropy {
            joint_xy: vec![0u64; bins_cu].into_boxed_slice(),
            joint_yx: vec![0u64; bins_cu].into_boxed_slice(),
            marginal_y: vec![0u64; bins_sq].into_boxed_slice(),
            marginal_x: vec![0u64; bins_sq].into_boxed_slice(),
            hist_x: Ring::new(lag, 0)?,
            hist_y: Ring::new(lag, 0)?,
            bins,
            lag,
            total: 0,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn te_builder(bins: usize, lag: usize) -> TransferEntropy {
        TransferEntropy::builder()
            .bins(bins)
            .lag(lag)
            .build()
            .unwrap()
    }

    // =========================================================================
    // Basic correctness
    // =========================================================================

    #[test]
    fn x_causes_y_lag1() {
        // Y_t = X_{t-1} with RANDOM X.
        // Y's own history is unpredictable (X is random), but X's past
        // perfectly predicts Y's future. TE(X→Y) should be large.
        let mut te = te_builder(4, 1);
        let mut prev_x = 0usize;
        let mut rng = 12345u64;
        for _ in 0..20000 {
            rng = rng
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let x_bin = ((rng >> 62) as usize) % 4;
            let y_bin = prev_x;
            te.update(x_bin, y_bin);
            prev_x = x_bin;
        }
        let te_xy = te.te_x_to_y().unwrap();
        let te_yx = te.te_y_to_x().unwrap();
        assert!(
            te_xy > 0.5,
            "TE(X→Y) should be large when X causes Y, got {te_xy}"
        );
        assert!(
            te_xy > te_yx * 2.0,
            "TE(X→Y)={te_xy} should dominate TE(Y→X)={te_yx}"
        );
    }

    #[test]
    fn x_causes_y_lag3() {
        // Y_t = X_{t-3} with random X.
        // Using lag=3 should detect this relationship.
        let mut te = te_builder(4, 3);
        let mut hist = [0usize; 3]; // manual 3-step history
        let mut hpos = 0usize;
        let mut rng = 99999u64;
        for i in 0..30000u32 {
            rng = rng
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let x_bin = ((rng >> 62) as usize) % 4;
            let y_bin = if i >= 3 { hist[hpos] } else { 0 };
            te.update(x_bin, y_bin);
            hist[hpos] = x_bin;
            hpos = (hpos + 1) % 3;
        }
        let te_xy = te.te_x_to_y().unwrap();
        let te_yx = te.te_y_to_x().unwrap();
        assert!(
            te_xy > 0.3,
            "lag-3 TE(X→Y) should be significant, got {te_xy}"
        );
        assert!(
            te_xy > te_yx,
            "TE(X→Y)={te_xy} should exceed TE(Y→X)={te_yx} at lag=3"
        );
    }

    #[test]
    fn independent_streams_near_zero() {
        let mut te = te_builder(4, 1);
        // Two independent cycling streams
        for i in 0..10000u32 {
            let x_bin = (i as usize) % 4;
            let y_bin = ((i as usize) * 3 + 1) % 4;
            te.update(x_bin, y_bin);
        }
        let te_xy = te.te_x_to_y().unwrap();
        let te_yx = te.te_y_to_x().unwrap();
        assert!(
            te_xy.abs() < 0.1,
            "independent TE(X→Y) should be near 0, got {te_xy}"
        );
        assert!(
            te_yx.abs() < 0.1,
            "independent TE(Y→X) should be near 0, got {te_yx}"
        );
    }

    #[test]
    fn net_flow_sign() {
        let mut te = te_builder(4, 1);
        let mut prev_x = 0usize;
        let mut rng = 54321u64;
        for _ in 0..20000 {
            rng = rng
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let x_bin = ((rng >> 62) as usize) % 4;
            let y_bin = prev_x;
            te.update(x_bin, y_bin);
            prev_x = x_bin;
        }
        let nf = te.net_flow().unwrap();
        assert!(nf > 0.0, "X→Y should have positive net flow, got {nf}");
    }

    #[test]
    fn symmetric_coupling() {
        let mut te = te_builder(2, 1);
        let mut x = 0usize;
        let mut y = 0usize;
        for _ in 0..10000 {
            let new_x = y;
            let new_y = x;
            te.update(x, y);
            x = new_x % 2;
            y = new_y % 2;
        }
        let nf = te.net_flow().unwrap();
        assert!(
            nf.abs() < 0.3,
            "symmetric coupling should have near-zero net flow, got {nf}"
        );
    }

    // =========================================================================
    // Edge cases
    // =========================================================================

    #[test]
    fn empty_returns_none() {
        let te = te_builder(4, 1);
        assert!(te.te_x_to_y().is_none());
        assert!(te.te_y_to_x().is_none());
        assert!(te.net_flow().is_none());
        assert!(!te.is_primed());
    }

    #[test]
    fn not_primed_until_lag_plus_1() {
        let mut te = te_builder(4, 3);
        // Need LAG observations to fill history, then 1 more to get a transition
        te.update(0, 0);
        assert!(!te.is_primed());
        te.update(1, 1);
        assert!(!te.is_primed());
        te.update(2, 2);
        assert!(!te.is_primed());
        te.update(3, 3); // LAG=3: now have full history + current → first transition
        assert!(te.is_primed());
        assert_eq!(te.count(), 1);
    }

    #[test]
    #[should_panic(expected = "out of range")]
    fn x_out_of_range_panics() {
        let mut te = te_builder(4, 1);
        te.update(4, 0);
    }

    #[test]
    #[should_panic(expected = "out of range")]
    fn y_out_of_range_panics() {
        let mut te = te_builder(4, 1);
        te.update(0, 4);
    }

    // =========================================================================
    // Builder validation
    // =========================================================================

    #[test]
    fn builder_rejects_bins_below_2() {
        let r = TransferEntropy::builder().bins(1).lag(1).build();
        assert!(r.is_err());
    }

    #[test]
    fn builder_rejects_lag_zero() {
        let r = TransferEntropy::builder().bins(4).lag(0).build();
        assert!(r.is_err());
    }

    #[test]
    fn builder_rejects_missing_bins() {
        let r = TransferEntropy::builder().lag(1).build();
        assert!(r.is_err());
    }

    #[test]
    fn builder_rejects_missing_lag() {
        let r = TransferEntropy::builder().bins(4).build();
        assert!(r.is_err());
    }

    // =========================================================================
    // Accessors
    // =========================================================================

    #[test]
    fn accessors() {
        let te = te_builder(8, 3);
        assert_eq!(te.bins(), 8);
        assert_eq!(te.lag(), 3);
        assert_eq!(te.count(), 0);
    }

    // =========================================================================
    // Reset
    // =========================================================================

    #[test]
    fn reset_clears_state() {
        let mut te = te_builder(4, 1);
        let mut prev_x = 0usize;
        for i in 0..1000u32 {
            let x_bin = (i as usize) % 4;
            te.update(x_bin, prev_x);
            prev_x = x_bin;
        }
        te.reset();
        assert_eq!(te.count(), 0);
        assert!(!te.is_primed());
        assert!(te.te_x_to_y().is_none());
    }
}
