use nexus_stats_core::math::MulAdd;

/// KAMA — Kaufman Adaptive Moving Average.
///
/// EMA with an efficiency-ratio-driven alpha. In trending markets,
/// the alpha increases (fast response). In noisy/choppy markets,
/// the alpha decreases (slow response).
///
/// The efficiency ratio = |direction| / volatility, where:
/// - direction = price_now - price_N_ago
/// - volatility = sum of |price_i - price_{i-1}| over N periods
///
/// The window size is specified at runtime via the builder. The ring
/// buffer is heap-allocated once during `build()` — no allocation
/// after construction.
///
/// # Use Cases
/// - Adaptive smoothing that auto-tunes to market conditions
/// - Noise-resistant trend following
/// - Signal processing with variable noise levels
pub struct Kama {
    ring: *mut f64,
    window: usize,
    head: usize,
    value: f64,
    fast_sc: f64,
    slow_sc: f64,
    sc_range: f64,
    volatility_sum: f64,
    count: u64,
    min_samples: u64,
}

// SAFETY: buffer is exclusively owned, f64 is Copy + Send
unsafe impl Send for Kama {}

impl Kama {
    #[inline]
    fn ring(&self) -> &[f64] {
        // SAFETY: buffer allocated with capacity `window`, all elements initialized
        unsafe { core::slice::from_raw_parts(self.ring, self.window) }
    }

    #[inline]
    fn ring_mut(&mut self) -> &mut [f64] {
        // SAFETY: buffer exclusively owned, all elements initialized
        unsafe { core::slice::from_raw_parts_mut(self.ring, self.window) }
    }
}

/// Builder for [`Kama`].
#[derive(Debug, Clone)]
pub struct KamaBuilder {
    window: Option<usize>,
    fast_span: u64,
    slow_span: u64,
    min_samples: Option<u64>,
}

impl Kama {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> KamaBuilder {
        KamaBuilder {
            window: None,
            fast_span: 2,
            slow_span: 30,
            min_samples: None,
        }
    }

    /// Feeds a sample. Returns the adaptive smoothed value once primed.
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the sample is NaN, or
    /// `DataError::Infinite` if the sample is infinite.
    #[inline]
    pub fn update(&mut self, sample: f64) -> Result<Option<f64>, nexus_stats_core::DataError> {
        check_finite!(sample);
        let n = self.window;
        let idx = self.head;
        self.ring_mut()[idx] = sample;
        // The slot after the newest sample holds the oldest one.
        self.head = idx + 1;
        if self.head == n {
            self.head = 0;
        }
        self.count += 1;

        if self.count <= n as u64 {
            self.value = sample;
            return if self.count >= self.min_samples {
                Ok(Some(self.value))
            } else {
                Ok(None)
            };
        }

        // Window is full: compute ER from the ring buffer.
        let ring = self.ring();

        // The ring is ordered: oldest at head, newest at idx (just written).
        // Split into two contiguous slices to avoid modular indexing
        // per iteration, enabling SIMD vectorization.
        let oldest = self.head;

        // Compute volatility: sum of |consecutive differences| in ring order
        let mut volatility = 0.0;

        // Slice 1: oldest..end of buffer
        let s1 = &ring[oldest..];
        for w in s1.windows(2) {
            volatility += (w[1] - w[0]).abs();
        }

        // Bridge: last element of s1 to first element of s2
        if oldest > 0 && !s1.is_empty() {
            volatility += (ring[0] - s1[s1.len() - 1]).abs();
        }

        // Slice 2: start..oldest (the wrap-around portion)
        let s2 = &ring[..oldest];
        for w in s2.windows(2) {
            volatility += (w[1] - w[0]).abs();
        }

        // Direction: |newest - oldest|
        let direction = (sample - ring[oldest]).abs();
        self.volatility_sum = volatility;
        let er = if volatility > 0.0 {
            direction / volatility
        } else {
            0.0
        };

        // Smoothing constant: sc = (er * sc_range + slow)^2
        let sc = er * self.sc_range + self.slow_sc;
        let alpha = sc * sc;

        self.value = alpha.fma(sample - self.value, self.value);

        if self.count >= self.min_samples {
            Ok(Some(self.value))
        } else {
            Ok(None)
        }
    }

    /// Current adaptive smoothed value, or `None` if not primed.
    #[inline]
    #[must_use]
    pub fn value(&self) -> Option<f64> {
        if self.count >= self.min_samples {
            Some(self.value)
        } else {
            None
        }
    }

    /// Current efficiency ratio (0 to 1), or `None` if < window samples.
    #[inline]
    #[must_use]
    pub fn efficiency_ratio(&self) -> Option<f64> {
        let n = self.window;
        if self.count <= n as u64 {
            return None;
        }
        let oldest_idx = self.head;
        let newest_idx = if oldest_idx == 0 {
            n - 1
        } else {
            oldest_idx - 1
        };
        let ring = self.ring();
        let direction = (ring[newest_idx] - ring[oldest_idx]).abs();
        if self.volatility_sum > 0.0 {
            Some(direction / self.volatility_sum)
        } else {
            Some(0.0)
        }
    }

    /// Window size.
    #[inline]
    #[must_use]
    pub fn window_size(&self) -> usize {
        self.window
    }

    /// Number of samples processed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether the KAMA has reached `min_samples`.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.min_samples
    }

    /// Resets to uninitialized state.
    #[inline]
    pub fn reset(&mut self) {
        self.ring_mut().fill(0.0);
        self.head = 0;
        self.value = 0.0;
        self.volatility_sum = 0.0;
        self.count = 0;
    }
}

impl KamaBuilder {
    /// Window size (number of samples in the ring buffer).
    #[inline]
    #[must_use]
    pub fn window_size(mut self, n: usize) -> Self {
        self.window = Some(n);
        self
    }

    /// Fast EMA span (most reactive). Default: 2.
    #[inline]
    #[must_use]
    pub fn fast_span(mut self, n: u64) -> Self {
        self.fast_span = n;
        self
    }

    /// Slow EMA span (least reactive). Default: 30.
    #[inline]
    #[must_use]
    pub fn slow_span(mut self, n: u64) -> Self {
        self.slow_span = n;
        self
    }

    /// Minimum samples before value is valid. Default: window size.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = Some(min);
        self
    }

    /// Builds the KAMA.
    ///
    /// # Errors
    ///
    /// - Window size must have been set and > 0.
    /// - `fast_span` must be >= 1.
    /// - `slow_span` must be > `fast_span`.
    #[inline]
    pub fn build(self) -> Result<Kama, nexus_stats_core::ConfigError> {
        let window = self
            .window
            .ok_or(nexus_stats_core::ConfigError::Missing("window_size"))?;
        if window == 0 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "window_size must be > 0",
            ));
        }
        if self.fast_span < 1 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "fast_span must be >= 1",
            ));
        }
        if self.slow_span <= self.fast_span {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "slow_span must be > fast_span",
            ));
        }
        let min_samples = self.min_samples.unwrap_or(window as u64);

        let mut vec = core::mem::ManuallyDrop::new(alloc::vec![0.0f64; window]);
        let ring = vec.as_mut_ptr();

        let fast_sc = 2.0 / (self.fast_span as f64 + 1.0);
        let slow_sc = 2.0 / (self.slow_span as f64 + 1.0);

        Ok(Kama {
            ring,
            window,
            head: 0,
            value: 0.0,
            fast_sc,
            slow_sc,
            sc_range: fast_sc - slow_sc,
            volatility_sum: 0.0,
            count: 0,
            min_samples,
        })
    }
}

impl Drop for Kama {
    fn drop(&mut self) {
        // SAFETY: buffer was allocated by Vec with capacity `window`.
        // f64 is Copy so no element drops needed. Reclaim the allocation.
        unsafe {
            let _ = alloc::vec::Vec::from_raw_parts(self.ring, 0, self.window);
        }
    }
}

impl Clone for Kama {
    fn clone(&self) -> Self {
        let mut vec = alloc::vec![0.0f64; self.window];
        vec.copy_from_slice(self.ring());
        let mut cloned = core::mem::ManuallyDrop::new(vec);
        let ring = cloned.as_mut_ptr();
        Self {
            ring,
            window: self.window,
            head: self.head,
            value: self.value,
            fast_sc: self.fast_sc,
            slow_sc: self.slow_sc,
            sc_range: self.sc_range,
            volatility_sum: self.volatility_sum,
            count: self.count,
            min_samples: self.min_samples,
        }
    }
}

impl core::fmt::Debug for Kama {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Kama")
            .field("window", &self.window)
            .field("count", &self.count)
            .field("value", &self.value)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trending_signal_fast_response() {
        let mut kama = Kama::builder().window_size(10).build().unwrap();

        // Linear trend — ER should be high, KAMA should track closely
        for i in 0..50 {
            kama.update(i as f64).unwrap();
        }

        let er = kama.efficiency_ratio().unwrap();
        assert!(er > 0.5, "trending signal should have high ER, got {er}");
    }

    #[test]
    fn noisy_signal_slow_response() {
        let mut kama = Kama::builder().window_size(10).build().unwrap();

        // Oscillating — ER should be low
        for i in 0..50 {
            let v = if i % 2 == 0 { 100.0 } else { 0.0 };
            kama.update(v).unwrap();
        }

        let er = kama.efficiency_ratio().unwrap();
        assert!(er < 0.3, "noisy signal should have low ER, got {er}");
    }

    #[test]
    fn er_bounds() {
        let mut kama = Kama::builder().window_size(10).build().unwrap();
        for i in 0..20 {
            kama.update(i as f64).unwrap();
        }
        let er = kama.efficiency_ratio().unwrap();
        assert!(
            (0.0..=1.0).contains(&er),
            "ER should be in [0, 1], got {er}"
        );
    }

    #[test]
    fn priming() {
        let mut kama = Kama::builder().window_size(10).build().unwrap();
        for i in 0..9 {
            assert!(kama.update(i as f64).unwrap().is_none());
        }
        assert!(kama.update(9.0).unwrap().is_some());
    }

    #[test]
    fn reset() {
        let mut kama = Kama::builder().window_size(10).build().unwrap();
        for i in 0..20 {
            kama.update(i as f64).unwrap();
        }
        kama.reset();
        assert_eq!(kama.count(), 0);
    }

    #[test]
    fn window_size_accessor() {
        let kama = Kama::builder().window_size(10).build().unwrap();
        assert_eq!(kama.window_size(), 10);
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut kama = Kama::builder().window_size(10).build().unwrap();
        assert!(matches!(
            kama.update(f64::NAN),
            Err(nexus_stats_core::DataError::NotANumber)
        ));
        assert!(matches!(
            kama.update(f64::INFINITY),
            Err(nexus_stats_core::DataError::Infinite)
        ));
        assert!(matches!(
            kama.update(f64::NEG_INFINITY),
            Err(nexus_stats_core::DataError::Infinite)
        ));
        assert_eq!(kama.count(), 0);
    }

    /// Value and efficiency ratio against the formula computed on a plain
    /// history `Vec`, step by step, through several wraps of the ring.
    #[test]
    fn matches_the_formula_on_a_history_vec() {
        let n = 7usize;
        let mut kama = Kama::builder()
            .window_size(n)
            .fast_span(2)
            .slow_span(30)
            .build()
            .unwrap();
        let fast_sc = 2.0 / 3.0;
        let slow_sc = 2.0 / 31.0;
        let mut history: Vec<f64> = Vec::new();
        let mut value = 0.0;
        for t in 0..60u32 {
            let x = (f64::from(t) * 0.7).sin().mul_add(5.0, f64::from(t) * 0.3);
            let got = kama.update(x).unwrap();
            history.push(x);
            if history.len() <= n {
                value = x;
                assert_eq!(kama.efficiency_ratio(), None);
            } else {
                let recent = &history[history.len() - n..];
                let volatility: f64 = recent.windows(2).map(|w| (w[1] - w[0]).abs()).sum();
                let direction = (x - recent[0]).abs();
                let er = if volatility > 0.0 {
                    direction / volatility
                } else {
                    0.0
                };
                let sc = er * (fast_sc - slow_sc) + slow_sc;
                value = (sc * sc).fma(x - value, value);
                let got_er = kama.efficiency_ratio().unwrap();
                assert!((got_er - er).abs() <= 1e-12, "t={t}: er {got_er} vs {er}");
            }
            if history.len() >= n {
                let got = got.unwrap();
                assert!(
                    (got - value).abs() <= 1e-12 * value.abs().max(1.0),
                    "t={t}: value {got} vs {value}"
                );
            } else {
                assert_eq!(got, None);
            }
        }
    }
}
