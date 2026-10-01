use std::time::{Duration, Instant};

/// GCRA — Generic Cell Rate Algorithm (single-threaded).
///
/// From the ATM specification. Uses a single timestamp (Theoretical Arrival
/// Time) for O(1) rate limiting with no token tracking.
///
/// # Precision
///
/// The emission interval is computed as `ceil(period / rate)`. Ceiling
/// division guarantees the limiter never exceeds the configured rate — it
/// may be slightly conservative (under-issue by <1 request/period) when
/// `period` is not evenly divisible by `rate`. For typical configurations
/// the division is exact and there is zero error. This is the standard
/// approach used in production rate limiters to bias toward safety.
///
/// # Use Cases
/// - API request rate limiting
/// - Per-client message throttling
/// - Exchange order rate control
#[derive(Debug, Clone)]
pub struct Gcra {
    base: Instant,
    tat: u64,
    emission_interval: u64,
    tau: u64,
}

/// Builder for [`Gcra`].
#[derive(Debug, Clone)]
pub struct GcraBuilder {
    rate: Option<u64>,
    period: Option<Duration>,
    burst: u64,
    now: Option<Instant>,
}

impl Gcra {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> GcraBuilder {
        GcraBuilder {
            rate: None,
            period: None,
            burst: 0,
            now: None,
        }
    }

    /// Converts an `Instant` to nanoseconds relative to the internal base.
    #[inline]
    fn nanos_since_base(&self, now: Instant) -> u64 {
        let nanos = now.saturating_duration_since(self.base).as_nanos();
        if nanos > u64::MAX as u128 {
            u64::MAX
        } else {
            nanos as u64
        }
    }

    /// Attempts to acquire with the given cost.
    ///
    /// Returns `true` if allowed, `false` if rate limited.
    /// `cost = 1` for a standard request. Higher for weighted operations.
    ///
    /// A `cost` whose `cost * emission_interval` exceeds the burst tolerance
    /// `tau` can never be admitted (even from an empty limiter) and always
    /// returns `false`; debug builds trip a `debug_assert!` to surface that
    /// misconfiguration.
    #[inline]
    #[must_use]
    pub fn try_acquire(&mut self, cost: u64, now: Instant) -> bool {
        debug_assert!(
            cost.saturating_mul(self.emission_interval) <= self.tau,
            "try_acquire: cost {cost} exceeds GCRA burst capacity {}; a request \
             larger than the burst can never be admitted",
            self.tau / self.emission_interval.max(1)
        );
        let now = self.nanos_since_base(now);
        let new_tat = self
            .tat
            .max(now)
            .saturating_add(cost.saturating_mul(self.emission_interval));
        if new_tat.saturating_sub(now) <= self.tau {
            self.tat = new_tat;
            true
        } else {
            false
        }
    }

    /// Duration until a request of the given cost would be allowed.
    /// Returns `Duration::ZERO` if allowed now.
    ///
    /// Informational: call this to learn when to retry, not instead of
    /// [`try_acquire`](Self::try_acquire). The same oversized-`cost` rule
    /// applies: a `cost` whose `cost * emission_interval` exceeds `tau` can
    /// never be admitted, so no finite wait is correct; debug builds trip a
    /// `debug_assert!` rather than report one.
    #[inline]
    #[must_use]
    pub fn time_until_allowed(&self, cost: u64, now: Instant) -> Duration {
        debug_assert!(
            cost.saturating_mul(self.emission_interval) <= self.tau,
            "time_until_allowed: cost {cost} exceeds GCRA burst capacity {}; a request \
             larger than the burst can never be admitted",
            self.tau / self.emission_interval.max(1)
        );
        let now = self.nanos_since_base(now);
        let new_tat = self
            .tat
            .max(now)
            .saturating_add(cost.saturating_mul(self.emission_interval));
        let excess = new_tat.saturating_sub(now);
        Duration::from_nanos(excess.saturating_sub(self.tau))
    }

    /// Reconfigure rate and burst at runtime. Takes effect immediately.
    #[inline]
    pub fn reconfigure(
        &mut self,
        rate: u64,
        period: Duration,
        burst: u64,
    ) -> Result<(), crate::ConfigError> {
        if rate == 0 {
            return Err(crate::ConfigError::Invalid("rate must be > 0"));
        }
        let period = u64::try_from(period.as_nanos()).map_err(|_| {
            crate::ConfigError::Invalid("period duration overflows u64 nanoseconds")
        })?;
        if period == 0 {
            return Err(crate::ConfigError::Invalid("period must be > 0"));
        }
        let ei = period.div_ceil(rate);
        if ei == 0 {
            return Err(crate::ConfigError::Invalid("period / rate must be > 0"));
        }
        self.emission_interval = ei;
        self.tau = ei.saturating_mul(burst.saturating_add(1));
        Ok(())
    }

    /// Release capacity back to the limiter.
    ///
    /// Shifts the Theoretical Arrival Time backward by `cost` emission
    /// intervals, but never before `now`. This prevents stockpiling
    /// credits beyond the burst window.
    ///
    /// Use case: exchange rate limits that rebate capacity on fills.
    #[inline]
    pub fn release(&mut self, cost: u64, now: Instant) {
        let now_ns = self.nanos_since_base(now);
        let credit = self.emission_interval.saturating_mul(cost);
        self.tat = self.tat.saturating_sub(credit).max(now_ns);
    }

    /// Resets the limiter with `now` as the new time base.
    ///
    /// After reset, the limiter behaves as if freshly constructed at `now`:
    /// full burst capacity is available.
    #[inline]
    pub fn reset(&mut self, now: Instant) {
        self.base = now;
        self.tat = 0;
    }
}

impl GcraBuilder {
    /// Allowed requests per period (steady-state rate).
    #[inline]
    #[must_use]
    pub fn rate(mut self, n: u64) -> Self {
        self.rate = Some(n);
        self
    }

    /// Period length as a `Duration`.
    #[inline]
    #[must_use]
    pub fn period(mut self, duration: Duration) -> Self {
        self.period = Some(duration);
        self
    }

    /// Burst allowance above steady-state rate. Default: 0.
    #[inline]
    #[must_use]
    pub fn burst(mut self, n: u64) -> Self {
        self.burst = n;
        self
    }

    /// Initial timestamp. If not called, defaults to `Instant::now()` at build time.
    #[inline]
    #[must_use]
    pub fn now(mut self, now: Instant) -> Self {
        self.now = Some(now);
        self
    }

    /// Builds the GCRA limiter.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError::Missing` if rate or period not set.
    /// Returns `ConfigError::Invalid` if rate or period is zero.
    #[inline]
    pub fn build(self) -> Result<Gcra, crate::ConfigError> {
        let rate = self.rate.ok_or(crate::ConfigError::Missing("rate"))?;
        let period = self.period.ok_or(crate::ConfigError::Missing("period"))?;
        let period_nanos = u64::try_from(period.as_nanos()).map_err(|_| {
            crate::ConfigError::Invalid("period duration overflows u64 nanoseconds")
        })?;
        if rate == 0 {
            return Err(crate::ConfigError::Invalid("rate must be > 0"));
        }
        if period_nanos == 0 {
            return Err(crate::ConfigError::Invalid("period must be > 0"));
        }

        let emission_interval = period_nanos.div_ceil(rate);
        if emission_interval == 0 {
            return Err(crate::ConfigError::Invalid(
                "period / rate must be > 0 (rate too high for period)",
            ));
        }
        let tau = emission_interval.saturating_mul(self.burst.saturating_add(1));

        Ok(Gcra {
            base: self.now.unwrap_or_else(Instant::now),
            tat: 0,
            emission_interval,
            tau,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_gcra(start: Instant) -> Gcra {
        // 10 requests per 1000 nanos, burst of 5
        Gcra::builder()
            .rate(10)
            .period(Duration::from_nanos(1000))
            .burst(5)
            .now(start)
            .build()
            .unwrap()
    }

    #[test]
    fn steady_rate_allowed() {
        let start = Instant::now();
        let mut g = make_gcra(start);
        // emission_interval = 100, spacing at 100 nanos should always work
        for i in 0..100u64 {
            assert!(
                g.try_acquire(1, start + Duration::from_nanos(i * 100)),
                "should be allowed at tick {}",
                i * 100
            );
        }
    }

    #[test]
    fn over_rate_rejected() {
        let start = Instant::now();
        let mut g = make_gcra(start);
        // Burst: 5+1 = 6 requests allowed immediately
        for i in 0..6 {
            assert!(
                g.try_acquire(1, start),
                "burst request {i} should be allowed"
            );
        }
        // 7th should be rejected
        assert!(!g.try_acquire(1, start), "should be rate limited");
    }

    #[test]
    fn burst_then_reject() {
        let start = Instant::now();
        let mut g = Gcra::builder()
            .rate(10)
            .period(Duration::from_nanos(1000))
            .burst(3)
            .now(start)
            .build()
            .unwrap();
        // burst + 1 = 4 requests at time 0
        assert!(g.try_acquire(1, start));
        assert!(g.try_acquire(1, start));
        assert!(g.try_acquire(1, start));
        assert!(g.try_acquire(1, start));
        assert!(!g.try_acquire(1, start)); // 5th rejected
    }

    #[test]
    fn time_passes_allows_again() {
        let start = Instant::now();
        let mut g = make_gcra(start);
        // Exhaust burst
        for _ in 0..6 {
            let _ = g.try_acquire(1, start);
        }
        assert!(!g.try_acquire(1, start));

        // After enough time, should be allowed
        assert!(g.try_acquire(1, start + Duration::from_nanos(200)));
    }

    #[test]
    fn weighted_cost() {
        let start = Instant::now();
        let mut g = Gcra::builder()
            .rate(10)
            .period(Duration::from_nanos(1000))
            .burst(5)
            .now(start)
            .build()
            .unwrap();
        // cost=3 consumes 3x the budget
        assert!(g.try_acquire(3, start)); // uses 3 of 6 burst capacity
        assert!(g.try_acquire(3, start)); // uses remaining 3
        assert!(!g.try_acquire(1, start)); // exhausted
    }

    #[test]
    fn time_until_allowed_zero_when_ok() {
        let start = Instant::now();
        let g = make_gcra(start);
        assert_eq!(g.time_until_allowed(1, start), Duration::ZERO);
    }

    #[test]
    fn time_until_allowed_positive_when_limited() {
        let start = Instant::now();
        let mut g = make_gcra(start);
        for _ in 0..6 {
            let _ = g.try_acquire(1, start);
        }
        let wait = g.time_until_allowed(1, start);
        assert!(wait > Duration::ZERO, "should need to wait, got {wait:?}");
    }

    #[test]
    fn reconfigure() {
        let start = Instant::now();
        let mut g = make_gcra(start);
        // Exhaust at original rate
        for _ in 0..6 {
            let _ = g.try_acquire(1, start);
        }
        assert!(!g.try_acquire(1, start));

        // Double the rate — emission_interval halves, more burst
        g.reconfigure(20, Duration::from_nanos(1000), 10).unwrap();
        // Need enough time for new config to allow: TAT=600, new tau=50*11=550
        // At now=100: new_tat=max(600,100)+50=650, excess=550, tau=550 -> allowed
        assert!(g.try_acquire(1, start + Duration::from_nanos(100)));
    }

    #[test]
    fn reset_clears() {
        let start = Instant::now();
        let mut g = make_gcra(start);
        for _ in 0..6 {
            let _ = g.try_acquire(1, start);
        }
        let reset_time = start + Duration::from_nanos(1000);
        g.reset(reset_time);
        // After reset, base=reset_time, tat=0 — full burst available
        assert!(g.try_acquire(1, reset_time));
    }

    #[test]
    fn cost_zero_always_allowed() {
        let start = Instant::now();
        let mut g = make_gcra(start);
        // Exhaust burst
        for _ in 0..6 {
            let _ = g.try_acquire(1, start);
        }
        assert!(!g.try_acquire(1, start));
        // cost=0 should always succeed without consuming
        assert!(g.try_acquire(0, start));
    }

    #[test]
    // Debug builds guard oversized cost with a `debug_assert!`; this validates the
    // release-mode saturation safety-net (huge `cost * ei` saturates, not wraps).
    #[cfg(not(debug_assertions))]
    fn overflow_saturates() {
        let start = Instant::now();
        let mut g = Gcra::builder()
            .rate(1)
            .period(Duration::from_nanos(100))
            .burst(0)
            .now(start)
            .build()
            .unwrap();
        // emission_interval = 100. cost * ei would overflow for huge cost
        assert!(!g.try_acquire(u64::MAX, start)); // should saturate, not wrap
    }

    #[test]
    fn timestamp_backward() {
        let start = Instant::now();
        let mut g = make_gcra(start);
        assert!(g.try_acquire(1, start + Duration::from_nanos(100)));
        // Going backward — should still work (max(tat, now) handles it)
        assert!(g.try_acquire(1, start + Duration::from_nanos(50)));
    }

    #[test]
    fn missing_rate_returns_error() {
        let result = Gcra::builder().period(Duration::from_nanos(1000)).build();
        assert!(matches!(result, Err(crate::ConfigError::Missing("rate"))));
    }

    #[test]
    fn zero_rate_returns_error() {
        let result = Gcra::builder()
            .rate(0)
            .period(Duration::from_nanos(1000))
            .build();
        assert!(matches!(result, Err(crate::ConfigError::Invalid(_))));
    }

    #[test]
    fn release_returns_capacity() {
        let base = Instant::now();
        let mut g = Gcra::builder()
            .rate(10)
            .period(Duration::from_nanos(1000))
            .burst(5)
            .now(base)
            .build()
            .unwrap();
        // Consume some capacity
        assert!(g.try_acquire(3, base));
        // Release 1 unit
        g.release(1, base);
        // Should have more capacity now
        assert!(g.try_acquire(4, base)); // 5 burst + 1 released - 3 consumed = would fail without release
    }

    #[test]
    fn release_saturates_at_now() {
        let base = Instant::now();
        let mut g = Gcra::builder()
            .rate(10)
            .period(Duration::from_nanos(1000))
            .burst(5)
            .now(base)
            .build()
            .unwrap();
        // Release without consuming — should be no-op (TAT already <= now)
        g.release(100, base);
        // Still limited by burst: the burst+1 max (6) is admissible, then the
        // limiter is exhausted. If release had banked the 100, this would not hold.
        assert!(g.try_acquire(6, base));
        assert!(!g.try_acquire(1, base));
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "can never be admitted")]
    fn oversized_cost_panics_in_debug() {
        let base = Instant::now();
        let mut g = Gcra::builder()
            .rate(10)
            .period(Duration::from_nanos(1000))
            .burst(5)
            .now(base)
            .build()
            .unwrap();
        // capacity = burst + 1 = 6; 7 can never be admitted.
        let _ = g.try_acquire(7, base);
    }

    #[test]
    fn acquire_release_roundtrip() {
        let base = Instant::now();
        let mut g = Gcra::builder()
            .rate(1)
            .period(Duration::from_nanos(1000))
            .burst(0)
            .now(base)
            .build()
            .unwrap();
        assert!(g.try_acquire(1, base));
        assert!(!g.try_acquire(1, base)); // exhausted
        g.release(1, base + Duration::from_nanos(1)); // release at slightly later time
        assert!(g.try_acquire(1, base + Duration::from_nanos(1))); // should work now
    }

    #[test]
    fn period_overflow_returns_error() {
        let result = Gcra::builder()
            .rate(1)
            .period(Duration::from_secs(u64::MAX))
            .build();
        assert!(matches!(result, Err(crate::ConfigError::Invalid(_))));
    }

    #[test]
    fn reconfigure_period_overflow_returns_error() {
        let start = Instant::now();
        let mut gcra = Gcra::builder()
            .rate(1)
            .period(Duration::from_secs(1))
            .now(start)
            .build()
            .unwrap();
        let result = gcra.reconfigure(1, Duration::from_secs(u64::MAX), 0);
        assert!(matches!(result, Err(crate::ConfigError::Invalid(_))));
    }
    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "can never be admitted")]
    fn time_until_allowed_oversized_cost_panics_in_debug() {
        let base = Instant::now();
        let g = Gcra::builder()
            .rate(10)
            .period(Duration::from_nanos(1000))
            .burst(5)
            .now(base)
            .build()
            .unwrap();
        // capacity = burst + 1 = 6; 7 can never be admitted, so no wait is correct.
        let _ = g.time_until_allowed(7, base);
    }
}
