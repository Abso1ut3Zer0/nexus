use core::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

/// Token Bucket — lazy token computation (thread-safe).
///
/// Same Folly-style algorithm as [`local::TokenBucket`](crate::local::TokenBucket)
/// but uses `AtomicU64` fields with CAS loops for lock-free concurrent access.
/// See the local variant's documentation for precision characteristics —
/// `nanos_per_token = ceil(period / rate)` guarantees no over-issuance.
///
/// # Thread Safety
///
/// All methods take `&self`. Safe to share via `Arc` or static reference.
pub struct TokenBucket {
    zero_time: AtomicU64,
    rate: AtomicU64,
    period: AtomicU64,
    burst: AtomicU64,
    nanos_per_token: AtomicU64,
    base: Instant,
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

    /// Converts an `Instant` to nanoseconds relative to the base instant.
    #[inline]
    fn nanos_since_base(&self, now: Instant) -> u64 {
        let dur = now.saturating_duration_since(self.base);
        dur.as_secs()
            .saturating_mul(1_000_000_000)
            .saturating_add(dur.subsec_nanos() as u64)
    }

    /// Attempts to consume `cost` tokens (thread-safe).
    ///
    /// Uses a CAS loop on `zero_time`.
    #[inline]
    #[must_use]
    pub fn try_acquire(&self, cost: u64, now: Instant) -> bool {
        let now = self.nanos_since_base(now);
        let nanos_per_token = self.nanos_per_token.load(Ordering::Relaxed);
        let burst = self.burst.load(Ordering::Relaxed);
        // See `local::TokenBucket::try_acquire`: an idle gap longer than one
        // burst must not bank credit, so the stored `zero_time` is clamped to
        // "now minus one burst" before consuming. The CAS still compares
        // against the value actually loaded; comparing against the clamped
        // value could never succeed while the stored value sits below the floor.
        let floor = now.saturating_sub(burst.saturating_mul(nanos_per_token));
        let consume_ticks = cost.saturating_mul(nanos_per_token);
        loop {
            let loaded = self.zero_time.load(Ordering::Relaxed);
            let zero_time = loaded.max(floor);
            let available = (now.saturating_sub(zero_time) / nanos_per_token).min(burst);

            if available < cost {
                return false;
            }

            let new_zero_time = zero_time.saturating_add(consume_ticks);

            if self
                .zero_time
                .compare_exchange_weak(loaded, new_zero_time, Ordering::AcqRel, Ordering::Relaxed)
                .is_ok()
            {
                return true;
            }
        }
    }

    /// Available tokens right now (without consuming).
    #[inline]
    #[must_use]
    pub fn available(&self, now: Instant) -> u64 {
        let nanos_per_token = self.nanos_per_token.load(Ordering::Relaxed);
        let burst = self.burst.load(Ordering::Relaxed);
        let zero_time = self.zero_time.load(Ordering::Relaxed);
        let now = self.nanos_since_base(now);
        let elapsed = now.saturating_sub(zero_time);
        (elapsed / nanos_per_token).min(burst)
    }

    /// Reconfigure rate and burst. Control-plane operation.
    ///
    /// Note: `rate`, `period`, and `burst` are stored sequentially. A
    /// concurrent `try_acquire` may briefly see a partially-updated
    /// triple. This is benign — at most one or two calls will see
    /// slightly wrong limits.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError::Invalid` if rate is zero, period is zero, or if
    /// `period / rate` rounds to zero.
    #[inline]
    pub fn reconfigure(
        &self,
        rate: u64,
        period: Duration,
        burst: u64,
    ) -> Result<(), crate::ConfigError> {
        let period_nanos = u64::try_from(period.as_nanos()).map_err(|_| {
            crate::ConfigError::Invalid("period duration overflows u64 nanoseconds")
        })?;
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
        self.rate.store(rate, Ordering::Release);
        self.period.store(period_nanos, Ordering::Release);
        self.burst.store(burst, Ordering::Release);
        self.nanos_per_token
            .store(nanos_per_token, Ordering::Release);
        Ok(())
    }

    /// Release capacity back to the limiter.
    ///
    /// Adds `cost` tokens back, saturating at `burst`. Uses CAS loop.
    #[inline]
    pub fn release(&self, cost: u64, now: Instant) {
        let now_ns = self.nanos_since_base(now);
        let nanos_per_token = self.nanos_per_token.load(Ordering::Relaxed);
        let burst = self.burst.load(Ordering::Relaxed);
        loop {
            let zero_time = self.zero_time.load(Ordering::Relaxed);
            let elapsed = now_ns.saturating_sub(zero_time);
            let available = (elapsed / nanos_per_token).min(burst);
            let new_available = available.saturating_add(cost).min(burst);
            let ticks_for_tokens = new_available.saturating_mul(nanos_per_token);
            let new_zero_time = now_ns.saturating_sub(ticks_for_tokens);

            if self
                .zero_time
                .compare_exchange_weak(
                    zero_time,
                    new_zero_time,
                    Ordering::AcqRel,
                    Ordering::Relaxed,
                )
                .is_ok()
            {
                return;
            }
        }
    }

    /// Resets to fresh state at the given timestamp.
    #[inline]
    pub fn reset(&self, now: Instant) {
        let now = self.nanos_since_base(now);
        self.zero_time.store(now, Ordering::Release);
    }
}

impl core::fmt::Debug for TokenBucket {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("sync::TokenBucket")
            .field("zero_time", &self.zero_time.load(Ordering::Relaxed))
            .field("rate", &self.rate.load(Ordering::Relaxed))
            .field("period", &self.period.load(Ordering::Relaxed))
            .field("burst", &self.burst.load(Ordering::Relaxed))
            .field(
                "nanos_per_token",
                &self.nanos_per_token.load(Ordering::Relaxed),
            )
            .field("base", &self.base)
            .finish()
    }
}

impl TokenBucketBuilder {
    /// Token refill rate.
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

    /// Maximum burst size.
    #[inline]
    #[must_use]
    pub fn burst(mut self, max_tokens: u64) -> Self {
        self.burst = Some(max_tokens);
        self
    }

    /// Initial timestamp used as the base instant.
    #[inline]
    #[must_use]
    pub fn now(mut self, now: Instant) -> Self {
        self.now = Some(now);
        self
    }

    /// Builds the thread-safe token bucket.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError::Missing` if rate, period, or burst not set.
    /// Returns `ConfigError::Invalid` if rate or period is zero.
    #[inline]
    pub fn build(self) -> Result<TokenBucket, crate::ConfigError> {
        let rate = self.rate.ok_or(crate::ConfigError::Missing("rate"))?;
        let period = self.period.ok_or(crate::ConfigError::Missing("period"))?;
        let burst = self.burst.ok_or(crate::ConfigError::Missing("burst"))?;
        let now = self.now.unwrap_or_else(Instant::now);
        let period_nanos = u64::try_from(period.as_nanos()).map_err(|_| {
            crate::ConfigError::Invalid("period duration overflows u64 nanoseconds")
        })?;
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
            zero_time: AtomicU64::new(0),
            rate: AtomicU64::new(rate),
            period: AtomicU64::new(period_nanos),
            burst: AtomicU64::new(burst),
            nanos_per_token: AtomicU64::new(nanos_per_token),
            base: now,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic() {
        let start = Instant::now();
        let tb = TokenBucket::builder()
            .rate(10)
            .period(Duration::from_nanos(1000))
            .burst(20)
            .now(start)
            .build()
            .unwrap();
        assert_eq!(tb.available(start + Duration::from_nanos(1000)), 10);
        assert!(tb.try_acquire(10, start + Duration::from_nanos(1000)));
        assert!(!tb.try_acquire(1, start + Duration::from_nanos(1000)));
    }

    #[test]
    fn burst_cap() {
        let start = Instant::now();
        let tb = TokenBucket::builder()
            .rate(10)
            .period(Duration::from_nanos(1000))
            .burst(20)
            .now(start)
            .build()
            .unwrap();
        assert_eq!(tb.available(start + Duration::from_nanos(10000)), 20); // capped at burst
    }

    #[test]
    fn reset() {
        let start = Instant::now();
        let tb = TokenBucket::builder()
            .rate(10)
            .period(Duration::from_nanos(1000))
            .burst(20)
            .now(start)
            .build()
            .unwrap();
        let _ = tb.try_acquire(10, start + Duration::from_nanos(1000));
        tb.reset(start + Duration::from_nanos(5000));
        assert_eq!(tb.available(start + Duration::from_nanos(5000)), 0);
    }

    #[test]
    #[allow(clippy::needless_collect)]
    fn concurrent_consumption() {
        use std::sync::Arc;
        use std::thread;

        let start = Instant::now();
        let tb = Arc::new(
            TokenBucket::builder()
                .rate(1000)
                .period(Duration::from_nanos(1000))
                .burst(100)
                .now(start)
                .build()
                .unwrap(),
        );

        let threads: Vec<_> = (0..4)
            .map(|_| {
                let tb = Arc::clone(&tb);
                thread::spawn(move || {
                    let mut allowed = 0u64;
                    for t in 1..=100 {
                        if tb.try_acquire(1, start + Duration::from_nanos(t * 10)) {
                            allowed += 1;
                        }
                    }
                    allowed
                })
            })
            .collect();

        let total: u64 = threads.into_iter().map(|t| t.join().unwrap()).sum();
        assert!(total > 0);
    }

    #[test]
    fn available_query() {
        let start = Instant::now();
        let tb = TokenBucket::builder()
            .rate(10)
            .period(Duration::from_nanos(1000))
            .burst(20)
            .now(start)
            .build()
            .unwrap();
        assert_eq!(tb.available(start + Duration::from_nanos(1000)), 10);
        assert_eq!(tb.available(start + Duration::from_nanos(1000)), 10); // doesn't consume
    }

    #[test]
    fn cost_zero() {
        let start = Instant::now();
        let tb = TokenBucket::builder()
            .rate(10)
            .period(Duration::from_nanos(1000))
            .burst(10)
            .now(start)
            .build()
            .unwrap();
        assert!(tb.try_acquire(0, start));
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
        let tb = TokenBucket::builder()
            .rate(10)
            .period(Duration::from_nanos(1000))
            .burst(10)
            .now(base)
            .build()
            .unwrap();
        let t = base + Duration::from_nanos(1000);
        assert!(tb.try_acquire(8, t));
        assert_eq!(tb.available(t), 2);
        tb.release(3, t);
        assert_eq!(tb.available(t), 5);
    }

    #[test]
    fn release_saturates_at_burst() {
        let base = Instant::now();
        let tb = TokenBucket::builder()
            .rate(10)
            .period(Duration::from_nanos(1000))
            .burst(10)
            .now(base)
            .build()
            .unwrap();
        let t = base + Duration::from_nanos(1000);
        tb.release(100, t);
        assert_eq!(tb.available(t), 10);
    }

    #[test]
    fn idle_gap_does_not_bank_credit() {
        let start = Instant::now();
        let tb = TokenBucket::builder()
            .rate(10)
            .period(Duration::from_nanos(1000))
            .burst(20)
            .now(start)
            .build()
            .unwrap();
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
        let tb = TokenBucket::builder()
            .rate(10)
            .period(Duration::from_nanos(1000))
            .burst(20)
            .now(start)
            .build()
            .unwrap();
        let now = start + Duration::from_millis(1);
        while tb.try_acquire(1, now) {}
        // Drained at `now`: no double credit, one token per 100ns from here.
        assert_eq!(tb.available(now + Duration::from_nanos(99)), 0);
        assert_eq!(tb.available(now + Duration::from_nanos(100)), 1);
        assert_eq!(tb.available(now + Duration::from_nanos(1000)), 10);
        assert_eq!(tb.available(now + Duration::from_nanos(5000)), 20); // capped at burst
    }
}
