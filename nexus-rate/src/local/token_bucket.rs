use std::time::{Duration, Instant};

/// Token Bucket — lazy token computation (single-threaded).
///
/// Folly-style: stores a `zero_time` instead of a token count. Tokens are
/// computed lazily from elapsed time on each call. No timer needed. This is
/// the same pattern used in the Linux kernel (`tbf` qdisc) and production
/// rate limiters at scale.
///
/// # Precision
///
/// Token availability is computed as `elapsed / nanos_per_token` where
/// `nanos_per_token = ceil(period / rate)`. Ceiling division guarantees the
/// limiter never over-issues — it will produce at most `rate` tokens per
/// `period`, never more. When `period` is not evenly divisible by `rate`,
/// the limiter is slightly conservative (under-issues by <1 token/period).
/// For typical configurations (e.g., 100 tokens/sec), the division is exact
/// and there is zero error.
///
/// This is the standard approach used in the Linux kernel (`tbf` qdisc) and
/// production rate limiters at scale. The tradeoff eliminates u128 software
/// division (~40-80 cycles) from the hot path while biasing toward safety:
/// the limiter will never exceed the configured rate.
///
/// # Use Cases
/// - Bandwidth limiting
/// - Request quota enforcement
/// - Metered resource access
#[derive(Debug, Clone)]
pub struct TokenBucket {
    base: Instant,
    zero_time: u64,
    rate: u64,
    period: u64,
    burst: u64,
    nanos_per_token: u64,
}

/// Builder for [`TokenBucket`].
#[derive(Debug, Clone)]
pub struct TokenBucketBuilder {
    rate: Option<u64>,
    period: Option<Duration>,
    burst: Option<u64>,
    now: Option<Instant>,
}

impl TokenBucket {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> TokenBucketBuilder {
        TokenBucketBuilder {
            rate: None,
            period: None,
            burst: None,
            now: None,
        }
    }

    /// Converts an `Instant` to nanoseconds relative to the internal base.
    #[inline]
    fn nanos_since_base(&self, now: Instant) -> u64 {
        let dur = now.saturating_duration_since(self.base);
        dur.as_secs()
            .saturating_mul(1_000_000_000)
            .saturating_add(dur.subsec_nanos() as u64)
    }

    /// Computes available tokens without consuming.
    #[inline]
    fn compute_available(&self, now: u64) -> u64 {
        let elapsed = now.saturating_sub(self.zero_time);
        let tokens = elapsed / self.nanos_per_token;
        tokens.min(self.burst)
    }

    /// Attempts to consume `cost` tokens.
    ///
    /// Returns `true` if enough tokens are available. Tokens accumulate in
    /// whole units only — a token becomes available after `period / rate`
    /// ticks, not fractionally. This is standard for integer rate limiting.
    ///
    /// A `cost` greater than `burst` (the bucket capacity) can never be admitted
    /// and always returns `false`; debug builds trip a `debug_assert!` to surface
    /// that misconfiguration (an oversized request would otherwise starve
    /// silently in a retry loop).
    #[inline]
    #[must_use]
    pub fn try_acquire(&mut self, cost: u64, now: Instant) -> bool {
        debug_assert!(
            cost <= self.burst,
            "try_acquire: cost {cost} exceeds burst capacity {}; a request larger \
             than the bucket can never be admitted",
            self.burst
        );
        let now = self.nanos_since_base(now);
        // An idle gap longer than one burst must not bank credit. `min(.., burst)`
        // only clamps what is reported; consuming from a `zero_time` far behind
        // `now` would hand out a full burst on every call until it caught up.
        // Clamp it to "now minus one burst" first (the Folly bucket does the same).
        let floor = now.saturating_sub(self.burst.saturating_mul(self.nanos_per_token));
        let zero_time = self.zero_time.max(floor);
        let available = (now.saturating_sub(zero_time) / self.nanos_per_token).min(self.burst);
        if available >= cost {
            let consume_ticks = cost.saturating_mul(self.nanos_per_token);
            self.zero_time = zero_time.saturating_add(consume_ticks);
            true
        } else {
            false
        }
    }

    /// Available tokens right now (without consuming).
    #[inline]
    #[must_use]
    pub fn available(&self, now: Instant) -> u64 {
        let now = self.nanos_since_base(now);
        self.compute_available(now)
    }

    /// Reconfigure rate and burst at runtime.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError::Invalid` if rate or period is zero, or if
    /// `period / rate` rounds to zero.
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
        let nanos_per_token = period.div_ceil(rate);
        if nanos_per_token == 0 {
            return Err(crate::ConfigError::Invalid("period / rate must be > 0"));
        }
        self.rate = rate;
        self.period = period;
        self.burst = burst;
        self.nanos_per_token = nanos_per_token;
        Ok(())
    }

    /// Release capacity back to the limiter.
    ///
    /// Adds `cost` tokens back, saturating at `burst` (never exceeds
    /// configured maximum). Implemented by shifting `zero_time` backward.
    #[inline]
    pub fn release(&mut self, cost: u64, now: Instant) {
        let now_ns = self.nanos_since_base(now);
        let available = self.compute_available(now_ns);
        let new_available = available.saturating_add(cost).min(self.burst);
        // Compute new zero_time: the time at which tokens were 0
        // given the new available count.
        let ticks_for_tokens = new_available.saturating_mul(self.nanos_per_token);
        self.zero_time = now_ns.saturating_sub(ticks_for_tokens);
    }

    /// Resets to a fresh state at the given timestamp.
    #[inline]
    pub fn reset(&mut self, now: Instant) {
        self.base = now;
        self.zero_time = 0;
    }
}

impl TokenBucketBuilder {
    /// Token refill rate (tokens per period).
    #[inline]
    #[must_use]
    pub fn rate(mut self, tokens_per_period: u64) -> Self {
        self.rate = Some(tokens_per_period);
        self
    }

    /// Period length as a `Duration`.
    #[inline]
    #[must_use]
    pub fn period(mut self, duration: Duration) -> Self {
        self.period = Some(duration);
        self
    }

    /// Maximum burst size (bucket capacity).
    #[inline]
    #[must_use]
    pub fn burst(mut self, max_tokens: u64) -> Self {
        self.burst = Some(max_tokens);
        self
    }

    /// Initial timestamp. If not called, defaults to `Instant::now()` at build time.
    #[inline]
    #[must_use]
    pub fn now(mut self, now: Instant) -> Self {
        self.now = Some(now);
        self
    }

    /// Builds the token bucket.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError::Missing` if rate, period, or burst not set.
    /// Returns `ConfigError::Invalid` if rate or period is zero.
    #[inline]
    pub fn build(self) -> Result<TokenBucket, crate::ConfigError> {
        let rate = self.rate.ok_or(crate::ConfigError::Missing("rate"))?;
        let period = self.period.ok_or(crate::ConfigError::Missing("period"))?;
        let period_nanos = u64::try_from(period.as_nanos()).map_err(|_| {
            crate::ConfigError::Invalid("period duration overflows u64 nanoseconds")
        })?;
        let burst = self.burst.ok_or(crate::ConfigError::Missing("burst"))?;
        let now = self.now.unwrap_or_else(Instant::now);
        if rate == 0 {
            return Err(crate::ConfigError::Invalid("rate must be > 0"));
        }
        if period_nanos == 0 {
            return Err(crate::ConfigError::Invalid("period must be > 0"));
        }
        let nanos_per_token = period_nanos.div_ceil(rate);
        if nanos_per_token == 0 {
            return Err(crate::ConfigError::Invalid("period / rate must be > 0"));
        }

        Ok(TokenBucket {
            base: now,
            zero_time: 0,
            rate,
            period: period_nanos,
            burst,
            nanos_per_token,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_bucket(start: Instant) -> TokenBucket {
        // 10 tokens per 1000 nanos, burst of 20
        TokenBucket::builder()
            .rate(10)
            .period(Duration::from_nanos(1000))
            .burst(20)
            .now(start)
            .build()
            .unwrap()
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "can never be admitted")]
    fn oversized_cost_panics_in_debug() {
        let start = Instant::now();
        let mut tb = make_bucket(start); // burst 20
        let _ = tb.try_acquire(21, start); // 21 > burst: can never be admitted
    }

    #[test]
    fn initial_burst() {
        let start = Instant::now();
        let mut tb = make_bucket(start);
        // At time 0, zero_time=0, elapsed=0, available=0
        // Need to advance time for tokens
        assert!(!tb.try_acquire(1, start)); // no tokens yet

        // After 1000 nanos, 10 tokens available
        assert!(tb.try_acquire(10, start + Duration::from_nanos(1000)));
        assert!(!tb.try_acquire(1, start + Duration::from_nanos(1000))); // exhausted
    }

    #[test]
    fn steady_rate() {
        let start = Instant::now();
        let mut tb = make_bucket(start);
        // Consume 1 token every 100 nanos (= rate of 10/1000)
        for i in 1..=50u64 {
            assert!(
                tb.try_acquire(1, start + Duration::from_nanos(i * 100)),
                "should be allowed at tick {}",
                i * 100
            );
        }
    }

    #[test]
    fn burst_cap() {
        let start = Instant::now();
        let tb = make_bucket(start);
        // Wait long enough for burst to fill: burst=20, rate=10/1000
        // 20 tokens at 2000 nanos
        assert_eq!(tb.available(start + Duration::from_nanos(2000)), 20);
        // Even at 10000 nanos, still capped at burst=20
        assert_eq!(tb.available(start + Duration::from_nanos(10000)), 20);
    }

    #[test]
    fn token_replenishment() {
        let start = Instant::now();
        let mut tb = make_bucket(start);
        // Consume all tokens
        assert!(tb.try_acquire(10, start + Duration::from_nanos(1000)));
        assert!(!tb.try_acquire(1, start + Duration::from_nanos(1000)));

        // Wait 500 nanos -> 5 tokens
        assert_eq!(tb.available(start + Duration::from_nanos(1500)), 5);
        assert!(tb.try_acquire(5, start + Duration::from_nanos(1500)));
    }

    #[test]
    fn weighted_cost() {
        let start = Instant::now();
        let mut tb = make_bucket(start);
        // 10 tokens at 1000 nanos
        assert!(tb.try_acquire(5, start + Duration::from_nanos(1000))); // consume 5
        assert_eq!(tb.available(start + Duration::from_nanos(1000)), 5); // 5 left
        assert!(tb.try_acquire(5, start + Duration::from_nanos(1000))); // consume remaining 5
        assert!(!tb.try_acquire(1, start + Duration::from_nanos(1000))); // empty
    }

    #[test]
    fn available_does_not_consume() {
        let start = Instant::now();
        let tb = make_bucket(start);
        let a1 = tb.available(start + Duration::from_nanos(1000));
        let a2 = tb.available(start + Duration::from_nanos(1000));
        assert_eq!(a1, a2);
    }

    #[test]
    fn reconfigure() {
        let start = Instant::now();
        let mut tb = make_bucket(start);
        // Double the rate
        tb.reconfigure(20, Duration::from_nanos(1000), 40).unwrap();
        // Now 20 tokens per 1000 nanos
        assert_eq!(tb.available(start + Duration::from_nanos(1000)), 20);
    }

    #[test]
    fn reset() {
        let start = Instant::now();
        let mut tb = make_bucket(start);
        let _ = tb.try_acquire(5, start + Duration::from_nanos(1000));
        let reset_time = start + Duration::from_nanos(2000);
        tb.reset(reset_time);
        // After reset at 2000, available at 2000 = 0 (just reset)
        assert_eq!(tb.available(reset_time), 0);
        // At 3000, 10 tokens
        assert_eq!(tb.available(start + Duration::from_nanos(3000)), 10);
    }

    #[test]
    fn cost_zero_always_allowed() {
        let start = Instant::now();
        let mut tb = make_bucket(start);
        assert!(tb.try_acquire(0, start)); // zero cost, no tokens needed
    }

    #[test]
    fn timestamp_backward() {
        let start = Instant::now();
        let mut tb = make_bucket(start);
        let _ = tb.try_acquire(5, start + Duration::from_nanos(1000));
        // Go backward — saturating_sub produces elapsed=0, no new tokens
        let available = tb.available(start + Duration::from_nanos(500));
        assert_eq!(
            available, 0,
            "backward timestamp should produce 0 available"
        );
    }

    #[test]
    fn missing_rate_returns_error() {
        let start = Instant::now();
        let result = TokenBucket::builder()
            .period(Duration::from_nanos(1000))
            .burst(10)
            .now(start)
            .build();
        assert!(matches!(result, Err(crate::ConfigError::Missing("rate"))));
    }

    #[test]
    fn zero_rate_returns_error() {
        let start = Instant::now();
        let result = TokenBucket::builder()
            .rate(0)
            .period(Duration::from_nanos(1000))
            .burst(10)
            .now(start)
            .build();
        assert!(matches!(result, Err(crate::ConfigError::Invalid(_))));
    }

    #[test]
    fn release_returns_tokens() {
        let base = Instant::now();
        let mut tb = TokenBucket::builder()
            .rate(10)
            .period(Duration::from_nanos(1000))
            .burst(10)
            .now(base)
            .build()
            .unwrap();
        // Advance to 1000ns so 10 tokens are available
        let t = base + Duration::from_nanos(1000);
        assert!(tb.try_acquire(8, t));
        assert_eq!(tb.available(t), 2);
        tb.release(3, t);
        assert_eq!(tb.available(t), 5);
    }

    #[test]
    fn release_saturates_at_burst() {
        let base = Instant::now();
        let mut tb = TokenBucket::builder()
            .rate(10)
            .period(Duration::from_nanos(1000))
            .burst(10)
            .now(base)
            .build()
            .unwrap();
        let t = base + Duration::from_nanos(1000);
        tb.release(100, t); // way more than burst
        assert_eq!(tb.available(t), 10); // capped at burst
    }

    #[test]
    fn release_on_full_is_noop() {
        let base = Instant::now();
        let mut tb = TokenBucket::builder()
            .rate(10)
            .period(Duration::from_nanos(1000))
            .burst(10)
            .now(base)
            .build()
            .unwrap();
        let t = base + Duration::from_nanos(1000);
        assert_eq!(tb.available(t), 10);
        tb.release(5, t);
        assert_eq!(tb.available(t), 10); // still capped
    }

    #[test]
    fn idle_gap_does_not_bank_credit() {
        let start = Instant::now();
        let mut tb = make_bucket(start); // 10 per 1000ns, burst 20
        // Idle for 1ms: 10,000 token intervals elapse, but only `burst` may be banked.
        let now = start + Duration::from_millis(1);
        let mut granted = 0u64;
        while tb.try_acquire(1, now) {
            granted += 1;
            assert!(granted <= 20, "over-admitted after idle gap");
        }
        assert_eq!(granted, 20);
    }

    #[test]
    fn refill_after_idle_drain_is_at_rate() {
        let start = Instant::now();
        let mut tb = make_bucket(start);
        let now = start + Duration::from_millis(1);
        while tb.try_acquire(1, now) {}
        // Drained at `now`: no double credit, one token per 100ns from here.
        assert_eq!(tb.available(now + Duration::from_nanos(99)), 0);
        assert_eq!(tb.available(now + Duration::from_nanos(100)), 1);
        assert_eq!(tb.available(now + Duration::from_nanos(1000)), 10);
        assert_eq!(tb.available(now + Duration::from_nanos(5000)), 20); // capped at burst
    }
}
