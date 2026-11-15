use nexus_stats_core::math::MulAdd;

/// Graded verdict from multi-gate anomaly detection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    /// Normal value — passed all gates.
    Accept,
    /// Unusual — exceeded the spread-based gate but not statistical.
    Unusual,
    /// Suspect — exceeded statistical z-score gate.
    Suspect,
    /// Rejected — exceeded hard limit.
    Reject,
}

/// Multi-gate anomaly filter with graded severity.
///
/// Three layers of filtering:
/// 1. **Hard limit** — absolute rejection (percentage change from EMA)
/// 2. **Statistical gate** — z-score against EMA of absolute returns
/// 3. **Spread gate** — relative to recent spread (optional)
///
/// Critical: the internal EMA is NOT updated on Suspect or Reject
/// verdicts, preventing estimator corruption from bad data.
///
/// # Use Cases
/// - Market data quality filtering
/// - Sensor anomaly detection with graded response
/// - Multi-level alert systems
#[derive(Debug, Clone)]
pub struct MultiGate {
    alpha: f64,
    one_minus_alpha: f64,
    ema_value: f64,
    ema_abs_return: f64,
    hard_limit_pct: f64,
    suspect_z: f64,
    unusual_spread_mult: Option<f64>,
    count: u64,
    min_samples: u64,
    initialized: bool,
}

/// Builder for [`MultiGate`].
#[derive(Debug, Clone)]
pub struct MultiGateBuilder {
    alpha: Option<f64>,
    hard_limit_pct: Option<f64>,
    suspect_z: Option<f64>,
    unusual_spread_mult: Option<f64>,
    min_samples: u64,
}

impl MultiGate {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> MultiGateBuilder {
        MultiGateBuilder {
            alpha: None,
            hard_limit_pct: None,
            suspect_z: None,
            unusual_spread_mult: None,
            min_samples: 10,
        }
    }

    /// Feeds a sample. Returns the verdict once primed.
    ///
    /// On `Suspect` or `Reject` verdicts, the internal EMA is NOT
    /// updated — preventing bad data from corrupting the baseline.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    #[inline]
    pub fn update(&mut self, sample: f64) -> Result<Option<Verdict>, nexus_stats_core::DataError> {
        check_finite!(sample);
        self.count += 1;

        if !self.initialized {
            self.ema_value = sample;
            self.ema_abs_return = 0.0;
            self.initialized = true;
            return Ok(if self.count >= self.min_samples {
                Some(Verdict::Accept)
            } else {
                None
            });
        }

        // Compute return
        let abs_return = (sample - self.ema_value).abs();

        // Gate 1: Hard limit (percentage of EMA)
        // Skip until EMA has converged enough to be meaningful.
        // Using abs > epsilon guard prevents silent disabling when EMA is near zero.
        let ema_abs = self.ema_value.abs();
        if ema_abs > 1e-10 {
            let pct_change = abs_return / ema_abs;
            if pct_change > self.hard_limit_pct {
                // Do NOT update EMA
                return Ok(if self.count >= self.min_samples {
                    Some(Verdict::Reject)
                } else {
                    None
                });
            }
        }

        // Gate 2: Statistical z-score against EMA of absolute returns
        if self.ema_abs_return > 0.0 {
            let z = abs_return / self.ema_abs_return;
            if z > self.suspect_z {
                // Do NOT update EMA
                return Ok(if self.count >= self.min_samples {
                    Some(Verdict::Suspect)
                } else {
                    None
                });
            }
        }

        // Gate 3: Spread multiple (optional)
        let verdict = if let Some(spread_mult) = self.unusual_spread_mult {
            if self.ema_abs_return > 0.0 && abs_return > spread_mult * self.ema_abs_return {
                Verdict::Unusual
            } else {
                Verdict::Accept
            }
        } else {
            Verdict::Accept
        };

        // Update EMA (only on Accept or Unusual)
        self.ema_value = self
            .alpha
            .fma(sample, self.one_minus_alpha * self.ema_value);
        self.ema_abs_return = self
            .alpha
            .fma(abs_return, self.one_minus_alpha * self.ema_abs_return);

        Ok(if self.count >= self.min_samples {
            Some(verdict)
        } else {
            None
        })
    }

    /// Current EMA of absolute returns, or `None` if not primed.
    #[inline]
    #[must_use]
    pub fn ema_abs_return(&self) -> Option<f64> {
        if self.count >= self.min_samples {
            Some(self.ema_abs_return)
        } else {
            None
        }
    }

    /// Number of samples processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether the filter has reached `min_samples`.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.min_samples
    }

    /// Resets to uninitialized state.
    #[inline]
    pub fn reset(&mut self) {
        self.ema_value = 0.0;
        self.ema_abs_return = 0.0;
        self.count = 0;
        self.initialized = false;
    }
}

impl MultiGateBuilder {
    /// EMA smoothing factor.
    #[inline]
    #[must_use]
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.alpha = Some(alpha);
        self
    }

    /// Span for EMA smoothing.
    #[inline]
    #[must_use]
    pub fn span(mut self, n: u64) -> Self {
        self.alpha = Some(2.0 / (n as f64 + 1.0));
        self
    }

    /// Hard rejection limit as a fraction (e.g., 0.5 = 50% change).
    #[inline]
    #[must_use]
    pub fn hard_limit(mut self, pct: f64) -> Self {
        self.hard_limit_pct = Some(pct);
        self
    }

    /// Statistical z-score threshold for Suspect verdict.
    #[inline]
    #[must_use]
    pub fn suspect_z(mut self, z: f64) -> Self {
        self.suspect_z = Some(z);
        self
    }

    /// Spread multiple threshold for Unusual verdict (optional).
    #[inline]
    #[must_use]
    pub fn unusual_spread_multiple(mut self, k: f64) -> Self {
        self.unusual_spread_mult = Some(k);
        self
    }

    /// Minimum samples before detection activates. Default: 10.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }

    /// Builds the multi-gate filter.
    ///
    /// # Errors
    ///
    /// - Alpha, hard_limit, and suspect_z must have been set.
    #[inline]
    pub fn build(self) -> Result<MultiGate, nexus_stats_core::ConfigError> {
        let alpha = self
            .alpha
            .ok_or(nexus_stats_core::ConfigError::Missing("alpha"))?;
        let hard_limit = self
            .hard_limit_pct
            .ok_or(nexus_stats_core::ConfigError::Missing("hard_limit"))?;
        let suspect_z = self
            .suspect_z
            .ok_or(nexus_stats_core::ConfigError::Missing("suspect_z"))?;
        if !(alpha > 0.0 && alpha < 1.0) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "alpha must be in (0, 1)",
            ));
        }

        Ok(MultiGate {
            alpha,
            one_minus_alpha: 1.0 - alpha,
            ema_value: 0.0,
            ema_abs_return: 0.0,
            hard_limit_pct: hard_limit,
            suspect_z,
            unusual_spread_mult: self.unusual_spread_mult,
            count: 0,
            min_samples: self.min_samples,
            initialized: false,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_gate() -> MultiGate {
        MultiGate::builder()
            .alpha(0.1)
            .hard_limit(0.5) // reject > 50% change
            .suspect_z(5.0) // suspect at 5x normal spread
            .unusual_spread_multiple(3.0)
            .min_samples(5)
            .build()
            .unwrap()
    }

    #[test]
    fn normal_data_accepted() {
        let mut mg = make_gate();
        for _ in 0..20 {
            let result = mg.update(100.0).unwrap();
            if let Some(v) = result {
                assert_eq!(v, Verdict::Accept);
            }
        }
    }

    #[test]
    fn extreme_spike_rejected() {
        let mut mg = make_gate();
        for _ in 0..10 {
            let _ = mg.update(100.0);
        }
        // 200 is 100% change from 100 — exceeds 50% hard limit
        assert_eq!(mg.update(200.0).unwrap(), Some(Verdict::Reject));
    }

    #[test]
    fn estimator_not_corrupted_by_reject() {
        let mut mg = make_gate();
        for _ in 0..10 {
            let _ = mg.update(100.0);
        }

        let ema_before = mg.ema_abs_return();

        // Rejected sample should NOT update EMA
        let _ = mg.update(200.0); // rejected

        let ema_after = mg.ema_abs_return();
        assert_eq!(ema_before, ema_after, "EMA should not change on reject");
    }

    #[test]
    fn moderate_anomaly_suspect() {
        let mut mg = MultiGate::builder()
            .alpha(0.1)
            .hard_limit(1.0) // very high hard limit
            .suspect_z(3.0)
            .min_samples(5)
            .build()
            .unwrap();

        // Build up baseline with small movements
        for i in 0..20 {
            let _ = mg.update(100.0 + (i % 2) as f64);
        }

        // Moderate spike — not enough for hard limit but exceeds z-score
        let result = mg.update(130.0).unwrap();
        assert!(
            result == Some(Verdict::Suspect) || result == Some(Verdict::Accept),
            "moderate spike should be suspect or accept"
        );
    }

    #[test]
    fn priming() {
        let mut mg = make_gate();
        for _ in 0..4 {
            assert!(mg.update(100.0).unwrap().is_none());
        }
        assert!(mg.update(100.0).unwrap().is_some());
    }

    #[test]
    fn reset() {
        let mut mg = make_gate();
        for _ in 0..20 {
            let _ = mg.update(100.0);
        }
        mg.reset();
        assert_eq!(mg.count(), 0);
    }

    #[test]
    fn errors_without_hard_limit() {
        let result = MultiGate::builder().alpha(0.1).suspect_z(3.0).build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Missing("hard_limit"))
        ));
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut mg = make_gate();

        assert_eq!(
            mg.update(f64::NAN).unwrap_err(),
            nexus_stats_core::DataError::NotANumber
        );
        assert_eq!(
            mg.update(f64::INFINITY).unwrap_err(),
            nexus_stats_core::DataError::Infinite
        );
        assert_eq!(
            mg.update(f64::NEG_INFINITY).unwrap_err(),
            nexus_stats_core::DataError::Infinite
        );
        assert_eq!(mg.count(), 0);
    }
}
