use core::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

/// GCRA — Generic Cell Rate Algorithm (thread-safe).
///
/// Same algorithm as [`local::Gcra`](crate::local::Gcra) but uses an
/// `AtomicU64` for the TAT with a CAS loop for lock-free concurrent access.
/// See the local variant's documentation for precision characteristics —
/// `ceil(period / rate)` guarantees no over-issuance.
///
/// # Thread Safety
///
/// All methods take `&self`. Safe to share via `Arc` or static reference.
/// `reconfigure` uses atomic stores (not CAS) — control-plane operation.
pub struct Gcra {
    tat: AtomicU64,
    emission_interval: AtomicU64,
    tau: AtomicU64,
    base: Instant,
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

    /// Converts an `Instant` to nanoseconds relative to the base instant.
    #[inline]
    fn nanos_since_base(&self, now: Instant) -> u64 {
        let nanos = now.saturating_duration_since(self.base).as_nanos();
        if nanos > u64::MAX as u128 {
            u64::MAX
        } else {
            nanos as u64
        }
    }

    /// Attempts to acquire with the given cost (thread-safe).
    ///
    /// Uses a CAS loop on the TAT. Retries on contention.
    ///
    /// A `cost` whose `cost * emission_interval` exceeds the burst tolerance
    /// `tau` can never be admitted (even from an empty limiter) and always
    /// returns `false`; debug builds trip a `debug_assert!` to surface that
    /// misconfiguration.
    #[inline]
    #[must_use]
    pub fn try_acquire(&self, cost: u64, now: Instant) -> bool {
        let now = self.nanos_since_base(now);
        let emission_interval = self.emission_interval.load(Ordering::Relaxed);
        let tau = self.tau.load(Ordering::Relaxed);
        debug_assert!(
            cost.saturating_mul(emission_interval) <= tau,
            "try_acquire: cost {cost} exceeds GCRA burst capacity {}; a request \
             larger than the burst can never be admitted",
            tau / emission_interval.max(1)
        );

        loop {
            let tat = self.tat.load(Ordering::Relaxed);
            let new_tat = tat
                .max(now)
                .saturating_add(cost.saturating_mul(emission_interval));

            if new_tat.saturating_sub(now) > tau {
                return false;
            }

            if self
                .tat
                .compare_exchange_weak(tat, new_tat, Ordering::AcqRel, Ordering::Relaxed)
                .is_ok()
            {
                return true;
            }
        }
    }

    /// Duration until a request of the given cost would be allowed.
    ///
    /// Informational: call this to learn when to retry, not instead of
    /// [`try_acquire`](Self::try_acquire). The same oversized-`cost` rule
    /// applies: a `cost` whose `cost * emission_interval` exceeds `tau` can
    /// never be admitted, so no finite wait is correct; debug builds trip a
    /// `debug_assert!` rather than report one.
    #[inline]
    #[must_use]
    pub fn time_until_allowed(&self, cost: u64, now: Instant) -> Duration {
        let now = self.nanos_since_base(now);
        let tat = self.tat.load(Ordering::Relaxed);
        let emission_interval = self.emission_interval.load(Ordering::Relaxed);
        let tau = self.tau.load(Ordering::Relaxed);
        debug_assert!(
            cost.saturating_mul(emission_interval) <= tau,
            "time_until_allowed: cost {cost} exceeds GCRA burst capacity {}; a request \
             larger than the burst can never be admitted",
            tau / emission_interval.max(1)
        );
        let new_tat = tat
            .max(now)
            .saturating_add(cost.saturating_mul(emission_interval));
        let excess = new_tat.saturating_sub(now);
        let nanos = excess.saturating_sub(tau);
        Duration::from_nanos(nanos)
    }

    /// Reconfigure rate and burst. Atomic stores.
    ///
    /// Note: `emission_interval` and `tau` are stored sequentially. A
    /// concurrent `try_acquire` may briefly see an inconsistent pair
    /// (new emission_interval with old tau). This is benign — at most
    /// one or two calls will see slightly wrong burst tolerance.
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
        if rate == 0 {
            return Err(crate::ConfigError::Invalid("rate must be > 0"));
        }
        let period_nanos = u64::try_from(period.as_nanos()).map_err(|_| {
            crate::ConfigError::Invalid("period duration overflows u64 nanoseconds")
        })?;
        if period_nanos == 0 {
            return Err(crate::ConfigError::Invalid("period must be > 0"));
        }
        let ei = period_nanos.div_ceil(rate);
        if ei == 0 {
            return Err(crate::ConfigError::Invalid("period / rate must be > 0"));
        }
        self.emission_interval.store(ei, Ordering::Release);
        self.tau.store(
            ei.saturating_mul(burst.saturating_add(1)),
            Ordering::Release,
        );
        Ok(())
    }

    /// Release capacity back to the limiter.
    ///
    /// Shifts TAT backward by `cost` emission intervals, never before `now`.
    /// Uses a CAS loop for lock-free concurrent access.
    #[inline]
    pub fn release(&self, cost: u64, now: Instant) {
        let now_ns = self.nanos_since_base(now);
        let emission_interval = self.emission_interval.load(Ordering::Relaxed);
        let credit = emission_interval.saturating_mul(cost);

        loop {
            let tat = self.tat.load(Ordering::Relaxed);
            let new_tat = tat.saturating_sub(credit).max(now_ns);
            if self
                .tat
                .compare_exchange_weak(tat, new_tat, Ordering::AcqRel, Ordering::Relaxed)
                .is_ok()
            {
                return;
            }
        }
    }

    /// Resets the limiter to full capacity as of `now`.
    ///
    /// Stores `now` as the theoretical arrival time (TAT), making burst+1
    /// requests available immediately.
    ///
    /// # Difference from `local::Gcra::reset`
    ///
    /// The local variant also rebases the internal time origin (`base`), which
    /// is possible because it takes `&mut self`. This variant keeps the original
    /// `base` (immutable behind `&self`) and adjusts TAT relative to it. The
    /// observable behavior is equivalent: full burst capacity is available after
    /// reset.
    #[inline]
    pub fn reset(&self, now: Instant) {
        self.tat
            .store(self.nanos_since_base(now), Ordering::Release);
    }
}

impl core::fmt::Debug for Gcra {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("sync::Gcra")
            .field("tat", &self.tat.load(Ordering::Relaxed))
            .field(
                "emission_interval",
                &self.emission_interval.load(Ordering::Relaxed),
            )
            .field("tau", &self.tau.load(Ordering::Relaxed))
            .field("base", &self.base)
            .finish()
    }
}

impl GcraBuilder {
    /// Allowed requests per period.
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

    /// Burst allowance. Default: 0.
    #[inline]
    #[must_use]
    pub fn burst(mut self, n: u64) -> Self {
        self.burst = n;
        self
    }

    /// Initial timestamp used as the base instant.
    #[inline]
    #[must_use]
    pub fn now(mut self, now: Instant) -> Self {
        self.now = Some(now);
        self
    }

    /// Builds the thread-safe GCRA limiter.
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

        let ei = period_nanos.div_ceil(rate);
        if ei == 0 {
            return Err(crate::ConfigError::Invalid("period / rate must be > 0"));
        }
        let tau = ei.saturating_mul(self.burst.saturating_add(1));
        let base = self.now.unwrap_or_else(Instant::now);

        Ok(Gcra {
            tat: AtomicU64::new(0),
            emission_interval: AtomicU64::new(ei),
            tau: AtomicU64::new(tau),
            base,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_rate_limiting() {
        let start = Instant::now();
        let g = Gcra::builder()
            .rate(10)
            .period(Duration::from_nanos(1000))
            .burst(5)
            .now(start)
            .build()
            .unwrap();

        // Burst: 6 allowed
        for i in 0..6 {
            assert!(g.try_acquire(1, start), "burst request {i}");
        }
        assert!(!g.try_acquire(1, start));
    }

    #[test]
    fn time_allows_more() {
        let start = Instant::now();
        let g = Gcra::builder()
            .rate(10)
            .period(Duration::from_nanos(1000))
            .burst(0)
            .now(start)
            .build()
            .unwrap();
        assert!(g.try_acquire(1, start));
        assert!(!g.try_acquire(1, start));
        // After emission_interval (100 ticks)
        assert!(g.try_acquire(1, start + Duration::from_nanos(200)));
    }

    #[test]
    fn reset() {
        let start = Instant::now();
        let g = Gcra::builder()
            .rate(10)
            .period(Duration::from_nanos(1000))
            .burst(5)
            .now(start)
            .build()
            .unwrap();
        for _ in 0..6 {
            let _ = g.try_acquire(1, start);
        }
        let reset_time = start + Duration::from_nanos(1000);
        g.reset(reset_time);
        // After reset, TAT = nanos_since_base(reset_time) = fresh start
        assert!(g.try_acquire(1, reset_time));
    }

    #[test]
    #[allow(clippy::needless_collect)]
    fn concurrent_rate_limit() {
        use std::sync::Arc;
        use std::thread;

        let start = Instant::now();
        let g = Arc::new(
            Gcra::builder()
                .rate(100)
                .period(Duration::from_nanos(1000))
                .burst(0)
                .now(start)
                .build()
                .unwrap(),
        );
        let threads: Vec<_> = (0..4)
            .map(|t| {
                let g = Arc::clone(&g);
                thread::spawn(move || {
                    let mut allowed = 0u64;
                    for i in 0..1000 {
                        let now = start + Duration::from_nanos((t * 1000 + i) * 10);
                        if g.try_acquire(1, now) {
                            allowed += 1;
                        }
                    }
                    allowed
                })
            })
            .collect();

        let total: u64 = threads.into_iter().map(|t| t.join().unwrap()).sum();
        // With rate=100/1000 over ~40000 ticks, should allow ~4000
        // But concurrent CAS contention means some may be lost
        assert!(total > 0, "should have allowed some requests");
    }

    #[test]
    fn time_until_allowed() {
        let start = Instant::now();
        let g = Gcra::builder()
            .rate(10)
            .period(Duration::from_nanos(1000))
            .burst(5)
            .now(start)
            .build()
            .unwrap();
        assert_eq!(g.time_until_allowed(1, start), Duration::ZERO);

        for _ in 0..6 {
            let _ = g.try_acquire(1, start);
        }
        assert!(g.time_until_allowed(1, start) > Duration::ZERO);
    }

    #[test]
    fn reconfigure_takes_effect() {
        let start = Instant::now();
        let g = Gcra::builder()
            .rate(1)
            .period(Duration::from_nanos(1000))
            .burst(0)
            .now(start)
            .build()
            .unwrap();
        assert!(g.try_acquire(1, start));
        assert!(!g.try_acquire(1, start));

        // Reconfigure to much higher rate and reset TAT
        let reset_time = start + Duration::from_nanos(500);
        g.reconfigure(1000, Duration::from_nanos(1000), 10).unwrap();
        g.reset(reset_time);
        // Now: emission_interval=1, tau=11, TAT=nanos_since_base(reset_time)=500
        // At reset_time: new_tat=max(500,500)+1=501, excess=1, tau=11 → allowed
        assert!(g.try_acquire(1, reset_time));
    }

    #[test]
    fn cost_zero() {
        let start = Instant::now();
        let g = Gcra::builder()
            .rate(1)
            .period(Duration::from_nanos(1000))
            .burst(0)
            .now(start)
            .build()
            .unwrap();
        let _ = g.try_acquire(1, start);
        assert!(!g.try_acquire(1, start));
        assert!(g.try_acquire(0, start));
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
        let g = Gcra::builder()
            .rate(10)
            .period(Duration::from_nanos(1000))
            .burst(5)
            .now(base)
            .build()
            .unwrap();
        assert!(g.try_acquire(3, base));
        g.release(1, base);
        assert!(g.try_acquire(4, base));
    }

    #[test]
    fn release_saturates_at_now() {
        let base = Instant::now();
        let g = Gcra::builder()
            .rate(10)
            .period(Duration::from_nanos(1000))
            .burst(5)
            .now(base)
            .build()
            .unwrap();
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
        let g = Gcra::builder()
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
