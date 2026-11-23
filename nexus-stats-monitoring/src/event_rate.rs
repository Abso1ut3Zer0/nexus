use nexus_stats_core::sample::{EmaKernel, ShiftEma};

/// Smoothed event rate tracker (unsigned integer timestamps).
///
/// Uses a fixed-point bit-shift EMA of inter-arrival times, inverted
/// on query to produce a rate (events per unit time). Timestamps are
/// unsigned ticks (e.g. nanoseconds from `Instant`).
///
/// # Use Cases
/// - Message throughput monitoring
/// - Order rate tracking
/// - Adaptive rate limiting input
///
/// # Weighting clock
///
/// Per event, using its timestamp. Each event must carry its own tick: one
/// stamp for a batch of events breaks the estimate (the rate swings or
/// reads `None`). A batch consumer gets its exact rate from `messages_seen`
/// over the period of a `PollSummary` instead.
#[derive(Debug, Clone)]
pub struct EventRate {
    /// Smoothed inter-arrival gap (the kernel's shift EMA).
    ema: ShiftEma,
    last_timestamp: u64,
    count: u64,
    min_samples: u64,
}

/// Builder for [`EventRate`].
#[derive(Debug, Clone)]
pub struct EventRateBuilder {
    span: Option<u64>,
    min_samples: u64,
}

impl EventRate {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> EventRateBuilder {
        EventRateBuilder {
            span: None,
            min_samples: 2,
        }
    }

    /// Updates with an event at the given tick.
    #[inline]
    pub fn update(&mut self, timestamp: u64) {
        self.count += 1;

        if self.count == 1 {
            self.last_timestamp = timestamp;
            return;
        }

        let dt = timestamp.wrapping_sub(self.last_timestamp) as i64;
        self.last_timestamp = timestamp;
        // A backwards step, or one that does not fit in i64, carries no
        // interval information: re-anchor and leave the estimate alone, as
        // Liveness does. Folding it would drive the accumulator negative.
        if dt <= 0 {
            return;
        }
        self.ema.fold(dt);
    }

    /// Current smoothed event rate (events per unit time).
    ///
    /// Returns `None` if not primed or if the smoothed interval is zero.
    #[inline]
    #[must_use]
    pub fn rate(&self) -> Option<f64> {
        let interval = self.interval()?;
        if interval == 0 {
            None
        } else {
            Some(1.0 / interval as f64)
        }
    }

    /// Current smoothed inter-event interval in ticks, or `None` if < 2 events.
    #[inline]
    #[must_use]
    pub fn interval(&self) -> Option<u64> {
        if self.count >= self.min_samples && self.ema.is_initialized() {
            Some(self.ema.value() as u64)
        } else {
            None
        }
    }

    /// Effective span after rounding to `2^k - 1`.
    #[inline]
    #[must_use]
    pub fn effective_span(&self) -> u64 {
        self.ema.span
    }

    /// Number of events recorded.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether the tracker has reached `min_samples`.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.min_samples
    }

    /// Resets to uninitialized state.
    #[inline]
    pub fn reset(&mut self) {
        self.ema.reset();
        self.last_timestamp = 0;
        self.count = 0;
    }
}

impl EventRateBuilder {
    /// Smoothing span. Rounded up to next `2^k - 1`.
    #[inline]
    #[must_use]
    pub fn span(mut self, n: u64) -> Self {
        self.span = Some(n);
        self
    }

    /// Minimum events before rate is valid. Default: 2.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }

    /// Builds the event rate tracker.
    ///
    /// # Errors
    ///
    /// - Span must have been set and >= 1.
    #[inline]
    pub fn build(self) -> Result<EventRate, nexus_stats_core::ConfigError> {
        let requested = self
            .span
            .ok_or(nexus_stats_core::ConfigError::Missing("span"))?;
        if requested < 1 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "EventRate span must be >= 1",
            ));
        }
        if requested > (1u64 << 62) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "EventRate span must be <= 2^62",
            ));
        }

        Ok(EventRate {
            ema: EmaKernel::new(requested)?,
            last_timestamp: 0,
            count: 0,
            min_samples: self.min_samples,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constant_rate_u64() {
        let mut er = EventRate::builder().span(15).build().unwrap();

        for i in 0..100u64 {
            er.update(i * 10);
        }

        let interval = er.interval().unwrap();
        assert_eq!(interval, 10, "interval should converge to 10");
        let rate = er.rate().unwrap();
        assert!(
            (rate - 0.1).abs() < 0.001,
            "rate should be ~0.1, got {rate}"
        );
    }

    #[test]
    fn burst_increases_rate() {
        let mut er = EventRate::builder().span(7).build().unwrap();

        for i in 0..20u64 {
            er.update(i * 1000);
        }
        let normal_rate = er.rate().unwrap();

        for i in 0..20u64 {
            er.update(20_000 + i * 100);
        }
        let burst_rate = er.rate().unwrap();

        assert!(
            burst_rate > normal_rate,
            "burst rate ({burst_rate}) should exceed normal ({normal_rate})"
        );
    }

    #[test]
    fn priming() {
        let mut er = EventRate::builder().span(7).min_samples(5).build().unwrap();

        for i in 0..4u64 {
            er.update(i * 10);
            assert!(!er.is_primed());
            assert!(er.rate().is_none());
        }
        er.update(40);
        assert!(er.is_primed());
        assert!(er.rate().is_some());
    }

    #[test]
    fn reset_u64() {
        let mut er = EventRate::builder().span(7).build().unwrap();
        for i in 0..10u64 {
            er.update(i * 10);
        }
        er.reset();
        assert_eq!(er.count(), 0);
        assert!(er.rate().is_none());
    }

    #[test]
    fn zero_interval_returns_none() {
        let mut er = EventRate::builder().span(7).build().unwrap();
        er.update(100);
        er.update(100);
        assert!(er.rate().is_none());
    }

    #[test]
    fn errors_without_span() {
        let result = EventRate::builder().build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Missing("span"))
        ));
    }

    #[test]
    fn effective_span_rounds_up() {
        let er = EventRate::builder().span(10).build().unwrap();
        assert_eq!(er.effective_span(), 15);
    }

    #[test]
    fn backwards_step_re_anchors_without_folding() {
        let mut er = EventRate::builder().span(3).build().unwrap();
        for t in [0u64, 100, 200, 300, 400] {
            er.update(t);
        }
        let before = er.interval().unwrap();
        er.update(50); // clock went backwards
        assert_eq!(er.interval().unwrap(), before);
        er.update(150); // 100 after the new anchor: the estimate stays sane
        assert_eq!(er.interval().unwrap(), before);
    }
}
