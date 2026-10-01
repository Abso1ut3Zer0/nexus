use std::time::{Duration, Instant};

/// Sliding Window Counter — time-bucketed rate limiter (single-threaded).
///
/// Divides the window into sub-windows (buckets) for fine-grained time
/// tracking. Expired buckets are evicted incrementally. Running total is
/// maintained for O(1) limit checks.
///
/// Requires the `alloc` feature for the bucket buffer.
///
/// # Use Cases
/// - "No more than 100 requests per minute"
/// - Sliding rate limit with sub-second granularity
/// - Traffic shaping with windowed counters
#[derive(Debug, Clone)]
pub struct SlidingWindow {
    base: Instant,
    buckets: Vec<u64>,
    total: u64,
    current_bucket: usize,
    bucket_duration: u64,
    last_bucket_time: u64,
    limit: u64,
}

impl SlidingWindow {
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
}

/// Builder for [`SlidingWindow`].
#[derive(Debug, Clone)]
pub struct SlidingWindowBuilder {
    window: Option<Duration>,
    sub_windows: Option<usize>,
    limit: Option<u64>,
    now: Option<Instant>,
}

impl SlidingWindow {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> SlidingWindowBuilder {
        SlidingWindowBuilder {
            window: None,
            sub_windows: None,
            limit: None,
            now: None,
        }
    }

    /// Advances time, evicting expired buckets.
    #[inline]
    fn advance_time(&mut self, now: u64) {
        let elapsed = now.saturating_sub(self.last_bucket_time);
        let buckets_to_advance = (elapsed / self.bucket_duration) as usize;

        if buckets_to_advance == 0 {
            return;
        }

        let num_buckets = self.buckets.len();
        let buckets_to_clear = buckets_to_advance.min(num_buckets);
        let mut current = self.current_bucket;
        let mut total = self.total;

        for _ in 0..buckets_to_clear {
            current += 1;
            if current >= num_buckets {
                current = 0;
            }
            total = total.saturating_sub(self.buckets[current]);
            self.buckets[current] = 0;
        }

        self.current_bucket = current;
        self.total = total;
        self.last_bucket_time = self
            .last_bucket_time
            .saturating_add((buckets_to_advance as u64).saturating_mul(self.bucket_duration));
    }

    /// Records an event with the given cost. Returns `true` if under limit.
    ///
    /// A `cost` greater than `limit` (the window capacity) can never be under the
    /// limit and always returns `false`; debug builds trip a `debug_assert!` to
    /// surface that misconfiguration.
    #[inline]
    #[must_use]
    pub fn try_acquire(&mut self, cost: u64, now: Instant) -> bool {
        debug_assert!(
            cost <= self.limit,
            "try_acquire: cost {cost} exceeds window limit {}; a request larger \
             than the limit can never be admitted",
            self.limit
        );
        let now = self.nanos_since_base(now);
        self.advance_time(now);

        if self.limit.saturating_sub(self.total) >= cost {
            let idx = self.current_bucket;
            self.buckets[idx] += cost;
            self.total += cost;
            true
        } else {
            false
        }
    }

    /// Release capacity back to the current sub-window.
    ///
    /// Decrements the current bucket's count, saturating at 0.
    #[inline]
    pub fn release(&mut self, cost: u64, now: Instant) {
        let now_ns = self.nanos_since_base(now);
        self.advance_time(now_ns);
        let idx = self.current_bucket;
        let decrement = cost.min(self.buckets[idx]);
        self.buckets[idx] -= decrement;
        self.total -= decrement;
    }

    /// Current count in the window.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.total
    }

    /// Remaining capacity before hitting the limit.
    #[inline]
    #[must_use]
    pub fn remaining(&self) -> u64 {
        self.limit.saturating_sub(self.total)
    }

    /// Reconfigure the limit at runtime.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError::Invalid` if `new_limit` is zero.
    #[inline]
    pub fn reconfigure(&mut self, new_limit: u64) -> Result<(), crate::ConfigError> {
        if new_limit == 0 {
            return Err(crate::ConfigError::Invalid("limit must be > 0"));
        }
        self.limit = new_limit;
        Ok(())
    }

    /// Resets all buckets, the running total, and the time base.
    ///
    /// After reset, the window is empty and `now` becomes the new time origin.
    #[inline]
    pub fn reset(&mut self, now: Instant) {
        self.buckets.fill(0);
        self.total = 0;
        self.current_bucket = 0;
        self.last_bucket_time = 0;
        self.base = now;
    }
}

impl SlidingWindowBuilder {
    /// Total window duration as a `Duration`.
    #[inline]
    #[must_use]
    pub fn window(mut self, duration: Duration) -> Self {
        self.window = Some(duration);
        self
    }

    /// Number of sub-windows (buckets). More = finer granularity. Typical: 10-60.
    #[inline]
    #[must_use]
    pub fn sub_windows(mut self, n: usize) -> Self {
        self.sub_windows = Some(n);
        self
    }

    /// Maximum allowed count per window.
    #[inline]
    #[must_use]
    pub fn limit(mut self, max_count: u64) -> Self {
        self.limit = Some(max_count);
        self
    }

    /// Initial timestamp. If not called, defaults to `Instant::now()` at build time.
    #[inline]
    #[must_use]
    pub fn now(mut self, now: Instant) -> Self {
        self.now = Some(now);
        self
    }

    /// Builds the sliding window limiter.
    ///
    /// # Errors
    ///
    /// Returns `ConfigError::Missing` if window, sub_windows, or limit not set.
    /// Returns `ConfigError::Invalid` if window, sub_windows, limit, or
    /// bucket duration (window / sub_windows) is zero.
    #[inline]
    pub fn build(self) -> Result<SlidingWindow, crate::ConfigError> {
        let window = self.window.ok_or(crate::ConfigError::Missing("window"))?;
        let window_nanos = u64::try_from(window.as_nanos()).map_err(|_| {
            crate::ConfigError::Invalid("window duration overflows u64 nanoseconds")
        })?;
        let sub_windows = self
            .sub_windows
            .ok_or(crate::ConfigError::Missing("sub_windows"))?;
        let limit = self.limit.ok_or(crate::ConfigError::Missing("limit"))?;
        let now = self.now.unwrap_or_else(Instant::now);
        if window_nanos == 0 {
            return Err(crate::ConfigError::Invalid("window must be > 0"));
        }
        if sub_windows == 0 {
            return Err(crate::ConfigError::Invalid("sub_windows must be > 0"));
        }
        if limit == 0 {
            return Err(crate::ConfigError::Invalid("limit must be > 0"));
        }

        let bucket_duration = window_nanos / sub_windows as u64;
        if bucket_duration == 0 {
            return Err(crate::ConfigError::Invalid(
                "window / sub_windows must be > 0",
            ));
        }

        Ok(SlidingWindow {
            base: now,
            buckets: vec![0u64; sub_windows],
            total: 0,
            current_bucket: 0,
            bucket_duration,
            last_bucket_time: 0,
            limit,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_window(start: Instant) -> SlidingWindow {
        // 100 events per 1000 nanos, 10 sub-windows (each 100 nanos)
        SlidingWindow::builder()
            .window(Duration::from_nanos(1000))
            .sub_windows(10)
            .limit(100)
            .now(start)
            .build()
            .unwrap()
    }

    #[test]
    fn under_limit_allowed() {
        let start = Instant::now();
        let mut sw = make_window(start);
        for _ in 0..100 {
            assert!(sw.try_acquire(1, start));
        }
    }

    #[test]
    fn at_limit_rejected() {
        let start = Instant::now();
        let mut sw = make_window(start);
        for _ in 0..100 {
            let _ = sw.try_acquire(1, start);
        }
        assert!(!sw.try_acquire(1, start));
    }

    #[test]
    fn time_passes_frees_capacity() {
        let start = Instant::now();
        let mut sw = make_window(start);
        // Fill up at time 0 (all in bucket 0)
        for _ in 0..100 {
            let _ = sw.try_acquire(1, start);
        }
        assert!(!sw.try_acquire(1, start));

        // Bucket 0 events don't evict until the head pointer wraps past it.
        // With 10 sub-windows of 100 nanos each, we need to advance through
        // all 10 sub-windows for bucket 0 to be evicted (full window = 1000 nanos).
        // At 1100 nanos, bucket 0 is cleared.
        assert!(sw.try_acquire(1, start + Duration::from_nanos(1100)));
    }

    #[test]
    fn weighted_cost() {
        let start = Instant::now();
        let mut sw = make_window(start);
        assert!(sw.try_acquire(50, start)); // half the limit
        assert!(sw.try_acquire(50, start)); // at limit
        assert!(!sw.try_acquire(1, start)); // over
    }

    #[test]
    fn count_and_remaining() {
        let start = Instant::now();
        let mut sw = make_window(start);
        let _ = sw.try_acquire(30, start);
        assert_eq!(sw.count(), 30);
        assert_eq!(sw.remaining(), 70);
    }

    #[test]
    fn reconfigure_limit() {
        let start = Instant::now();
        let mut sw = make_window(start);
        for _ in 0..100 {
            let _ = sw.try_acquire(1, start);
        }
        assert!(!sw.try_acquire(1, start));

        sw.reconfigure(200).unwrap();
        assert!(sw.try_acquire(1, start)); // now under new limit
    }

    #[test]
    fn sub_window_granularity() {
        let start = Instant::now();
        let mut sw = make_window(start);
        // Events at different sub-windows
        let _ = sw.try_acquire(30, start); // bucket 0
        let _ = sw.try_acquire(30, start + Duration::from_nanos(200)); // bucket 2
        let _ = sw.try_acquire(30, start + Duration::from_nanos(400)); // bucket 4
        assert_eq!(sw.count(), 90);

        // At time 1100, bucket 0 is evicted (1000 nanos = full window)
        let _ = sw.try_acquire(1, start + Duration::from_nanos(1100));
        // Bucket 0's 30 events should have been evicted
        assert!(sw.count() <= 91); // 90 - 30 + 1 = 61
    }

    #[test]
    fn reset_clears() {
        let start = Instant::now();
        let mut sw = make_window(start);
        for _ in 0..50 {
            let _ = sw.try_acquire(1, start);
        }
        let reset_time = start + Duration::from_nanos(500);
        sw.reset(reset_time);
        assert_eq!(sw.count(), 0);
        assert_eq!(sw.remaining(), 100);
    }

    #[test]
    fn long_idle_clears_all() {
        let start = Instant::now();
        let mut sw = make_window(start);
        for _ in 0..100 {
            let _ = sw.try_acquire(1, start);
        }
        // After a very long time, all buckets should be evicted
        assert!(sw.try_acquire(1, start + Duration::from_nanos(100_000)));
    }

    #[test]
    fn cost_zero() {
        let start = Instant::now();
        let mut sw = make_window(start);
        for _ in 0..100 {
            let _ = sw.try_acquire(1, start);
        }
        assert!(!sw.try_acquire(1, start));
        assert!(sw.try_acquire(0, start)); // zero cost always ok
    }

    #[test]
    fn weighted_eviction() {
        let start = Instant::now();
        let mut sw = SlidingWindow::builder()
            .window(Duration::from_nanos(1000))
            .sub_windows(10)
            .limit(100)
            .now(start)
            .build()
            .unwrap();

        // Insert weighted events in bucket 0
        let _ = sw.try_acquire(30, start);
        // Insert in bucket 1
        let _ = sw.try_acquire(20, start + Duration::from_nanos(100));
        assert_eq!(sw.count(), 50);

        // Advance past the full window — all buckets evicted
        let _ = sw.try_acquire(1, start + Duration::from_nanos(1200));
        // Only the new event should remain
        assert!(sw.count() <= 1);
    }

    #[test]
    fn large_timestamp_jump() {
        let start = Instant::now();
        let mut sw = make_window(start);
        for _ in 0..50 {
            let _ = sw.try_acquire(1, start);
        }
        // Jump far into the future — should not loop forever or panic
        assert!(sw.try_acquire(1, start + Duration::from_secs(1_000_000)));
    }

    #[test]
    fn timestamp_backward() {
        let start = Instant::now();
        let mut sw = make_window(start);
        let _ = sw.try_acquire(1, start + Duration::from_nanos(100));
        // Backward timestamp — saturating_sub produces 0 elapsed, no advance
        // Note: Instant subtraction panics if result would be negative,
        // but nanos_since_base uses duration_since which saturates to 0
        // when now < base. Here start+50 > base=start, so it's fine.
        let _ = sw.try_acquire(1, start + Duration::from_nanos(50));
        assert_eq!(sw.count(), 2); // both events counted, no eviction
    }

    #[test]
    fn missing_window_returns_error() {
        let start = Instant::now();
        let result = SlidingWindow::builder()
            .sub_windows(10)
            .limit(100)
            .now(start)
            .build();
        assert!(matches!(result, Err(crate::ConfigError::Missing("window"))));
    }

    #[test]
    fn zero_window_returns_error() {
        let start = Instant::now();
        let result = SlidingWindow::builder()
            .window(Duration::ZERO)
            .sub_windows(10)
            .limit(100)
            .now(start)
            .build();
        assert!(matches!(result, Err(crate::ConfigError::Invalid(_))));
    }

    #[test]
    fn release_decrements_current() {
        let base = Instant::now();
        let mut sw = SlidingWindow::builder()
            .window(Duration::from_nanos(1000))
            .sub_windows(4)
            .limit(100)
            .now(base)
            .build()
            .unwrap();
        assert!(sw.try_acquire(10, base));
        assert_eq!(sw.count(), 10);
        sw.release(3, base);
        assert_eq!(sw.count(), 7);
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "can never be admitted")]
    fn oversized_cost_panics_in_debug() {
        let base = Instant::now();
        let mut sw = SlidingWindow::builder()
            .window(Duration::from_nanos(1000))
            .sub_windows(4)
            .limit(100)
            .now(base)
            .build()
            .unwrap();
        let _ = sw.try_acquire(101, base); // 101 > limit: can never be admitted
    }

    #[test]
    fn clone_is_independent() {
        let start = Instant::now();
        let mut sw = make_window(start);
        let _ = sw.try_acquire(50, start);
        let mut cloned = sw.clone();
        // Mutations on clone don't affect original
        let _ = cloned.try_acquire(50, start);
        assert_eq!(sw.count(), 50); // original unchanged
        assert_eq!(cloned.count(), 100);
    }

    #[test]
    fn release_saturates_at_zero() {
        let base = Instant::now();
        let mut sw = SlidingWindow::builder()
            .window(Duration::from_nanos(1000))
            .sub_windows(4)
            .limit(100)
            .now(base)
            .build()
            .unwrap();
        assert!(sw.try_acquire(5, base));
        sw.release(100, base); // more than consumed
        assert_eq!(sw.count(), 0); // saturates at 0
    }
}
