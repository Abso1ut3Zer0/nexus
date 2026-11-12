/// Liveness detector (integer variant) — fixed-point EMA of inter-arrival ticks.
///
/// Uses kernel-style bit-shift arithmetic for the interval smoothing.
/// Timestamps are integer ticks and should be non-decreasing. A timestamp at
/// or behind the previous one carries no interval information: it re-anchors
/// the last-seen tick, leaves the smoothed interval untouched, and is alive.
///
/// Each gap is judged against the smoothed interval as it stood before the
/// event, then folded in. With both deadlines configured, a gap is dead if
/// it exceeds either one. Until a positive gap has been seen, only the
/// absolute deadline can judge.
///
/// # Weighting clock
///
/// Per event, using its timestamp. Each event must carry its own tick.
#[derive(Debug, Clone)]
pub struct LivenessI64 {
    acc: i128,
    shift: u32,
    span: u64,
    last_timestamp: i64,
    deadline_multiple: Option<u64>,
    deadline_absolute: Option<i64>,
    count: u64,
    min_samples: u64,
    initialized: bool,
}

/// Builder for [`LivenessI64`].
#[derive(Debug, Clone)]
pub struct LivenessI64Builder {
    span: Option<u64>,
    deadline_multiple: Option<u64>,
    deadline_absolute: Option<i64>,
    min_samples: u64,
}

impl LivenessI64 {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> LivenessI64Builder {
        LivenessI64Builder {
            span: None,
            deadline_multiple: None,
            deadline_absolute: None,
            min_samples: 2,
        }
    }

    /// Updates with an event at the given tick. Returns `true` if alive.
    #[inline]
    #[must_use]
    pub fn update(&mut self, timestamp: i64) -> bool {
        self.count += 1;

        if self.count == 1 {
            self.last_timestamp = timestamp;
            return true;
        }

        let dt = timestamp - self.last_timestamp;
        self.last_timestamp = timestamp;

        // A timestamp at or behind the previous one carries no interval
        // information: re-anchor to it, leave the estimate alone, report
        // alive. Folding it would pull the estimate toward or below zero and
        // make the next real gap read dead.
        if dt <= 0 {
            return true;
        }

        // Judge this gap against the interval as it stood before this event,
        // then fold the gap in. Folding first makes the test
        // `dt <= m * (old + (dt - old) / 2^k)`, which is always true once
        // `m >= 2^k`, so the detector could never report dead.
        let alive = if self.initialized {
            let smoothed = (self.acc >> self.shift) as i64;
            let dt_shifted = (dt as i128) << self.shift;
            self.acc += (dt_shifted - self.acc) >> self.shift;
            self.is_alive_with(dt, Some(smoothed))
        } else {
            // First gap: no prior interval to compare against. Only the
            // absolute deadline can judge it.
            self.acc = (dt as i128) << self.shift;
            self.initialized = true;
            self.is_alive_with(dt, None)
        };

        if self.count < self.min_samples {
            return true;
        }
        alive
    }

    /// Checks liveness at the given tick without recording.
    #[inline]
    #[must_use]
    pub fn check(&self, now: i64) -> bool {
        if self.count < self.min_samples {
            return true;
        }

        let dt = now - self.last_timestamp;
        // No positive gap seen yet: only the absolute deadline can judge.
        let smoothed = self.initialized.then(|| (self.acc >> self.shift) as i64);
        self.is_alive_with(dt, smoothed)
    }

    /// Alive only if the gap is within every configured deadline. A gap of
    /// zero or less (an event that just arrived, or a clock that stepped
    /// backwards) is always alive.
    #[inline]
    fn is_alive_with(&self, dt: i64, smoothed: Option<i64>) -> bool {
        if dt <= 0 {
            return true;
        }
        let within_multiple = match (self.deadline_multiple, smoothed) {
            (Some(multiple), Some(smoothed)) => {
                dt <= smoothed.saturating_mul(i64::try_from(multiple).unwrap_or(i64::MAX))
            }
            _ => true,
        };
        let within_absolute = self.deadline_absolute.is_none_or(|absolute| dt <= absolute);
        within_multiple && within_absolute
    }

    /// Current smoothed inter-arrival interval, or `None` if < 2 events.
    #[inline]
    #[must_use]
    pub fn interval(&self) -> Option<i64> {
        if self.count >= 2 && self.initialized {
            Some((self.acc >> self.shift) as i64)
        } else {
            None
        }
    }

    /// Effective span after rounding.
    #[inline]
    #[must_use]
    pub fn effective_span(&self) -> u64 {
        self.span
    }

    /// Number of events recorded.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether the detector has reached `min_samples`.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.min_samples
    }

    /// Resets to uninitialized state.
    #[inline]
    pub fn reset(&mut self) {
        self.acc = 0;
        self.last_timestamp = 0;
        self.count = 0;
        self.initialized = false;
    }
}

impl LivenessI64Builder {
    /// Smoothing span. Rounded up to next `2^k - 1`.
    #[inline]
    #[must_use]
    pub fn span(mut self, n: u64) -> Self {
        self.span = Some(n);
        self
    }

    /// Dead when a gap exceeds `n * smoothed_interval`, the interval as it
    /// stood before that gap. Combines with `deadline_absolute`: either trips.
    #[inline]
    #[must_use]
    pub fn deadline_multiple(mut self, n: u64) -> Self {
        self.deadline_multiple = Some(n);
        self
    }

    /// Dead when a gap exceeds a fixed deadline (in ticks). Combines with
    /// `deadline_multiple`: either trips.
    #[inline]
    #[must_use]
    pub fn deadline_absolute(mut self, t: i64) -> Self {
        self.deadline_absolute = Some(t);
        self
    }

    /// Minimum events before liveness checking activates. Default: 2.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }

    /// Builds the liveness detector.
    ///
    /// # Errors
    ///
    /// - Span must have been set and >= 1.
    /// - At least one deadline must be set.
    #[inline]
    pub fn build(self) -> Result<LivenessI64, crate::ConfigError> {
        let requested = self.span.ok_or(crate::ConfigError::Missing("span"))?;
        if requested < 1 {
            return Err(crate::ConfigError::Invalid("Liveness span must be >= 1"));
        }
        if self.deadline_multiple.is_none() && self.deadline_absolute.is_none() {
            return Err(crate::ConfigError::Invalid("Liveness requires a deadline"));
        }

        let effective = crate::smoothing::ema::next_power_of_two_minus_one(requested);
        let shift = crate::smoothing::ema::log2_of_span_plus_one(effective);

        Ok(LivenessI64 {
            acc: 0,
            shift,
            span: effective,
            last_timestamp: 0,
            deadline_multiple: self.deadline_multiple,
            deadline_absolute: self.deadline_absolute,
            count: 0,
            min_samples: self.min_samples,
            initialized: false,
        })
    }
}

/// Liveness detector (`u64` ticks) — fixed-point EMA of inter-arrival ticks.
///
/// Uses kernel-style bit-shift arithmetic for the interval smoothing.
/// Timestamps are integer ticks and should be non-decreasing. A timestamp at
/// or behind the previous one carries no interval information: it re-anchors
/// the last-seen tick, leaves the smoothed interval untouched, and is alive.
///
/// Each gap is judged against the smoothed interval as it stood before the
/// event, then folded in. With both deadlines configured, a gap is dead if
/// it exceeds either one. Until a positive gap has been seen, only the
/// absolute deadline can judge.
///
/// # Weighting clock
///
/// Per event, using its timestamp. Each event must carry its own tick.
#[derive(Debug, Clone)]
pub struct LivenessU64 {
    acc: i128,
    shift: u32,
    span: u64,
    last_timestamp: u64,
    deadline_multiple: Option<u64>,
    deadline_absolute: Option<u64>,
    count: u64,
    min_samples: u64,
    initialized: bool,
}

/// Builder for [`LivenessU64`].
#[derive(Debug, Clone)]
pub struct LivenessU64Builder {
    span: Option<u64>,
    deadline_multiple: Option<u64>,
    deadline_absolute: Option<u64>,
    min_samples: u64,
}

impl LivenessU64 {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> LivenessU64Builder {
        LivenessU64Builder {
            span: None,
            deadline_multiple: None,
            deadline_absolute: None,
            min_samples: 2,
        }
    }

    /// Updates with an event at the given tick. Returns `true` if alive.
    #[inline]
    #[must_use]
    pub fn update(&mut self, timestamp: u64) -> bool {
        self.count += 1;

        if self.count == 1 {
            self.last_timestamp = timestamp;
            return true;
        }

        let dt = timestamp.wrapping_sub(self.last_timestamp) as i64;
        self.last_timestamp = timestamp;

        // Non-positive gap (a step backwards, or one that does not fit in
        // i64): no interval information. See `LivenessI64::update`.
        if dt <= 0 {
            return true;
        }

        // Judge this gap against the interval as it stood before this event,
        // then fold the gap in. See `LivenessI64::update` for why the order
        // matters.
        let alive = if self.initialized {
            let smoothed = (self.acc >> self.shift) as i64;
            let dt_shifted = (dt as i128) << self.shift;
            self.acc += (dt_shifted - self.acc) >> self.shift;
            self.is_alive_with(dt, Some(smoothed))
        } else {
            self.acc = (dt as i128) << self.shift;
            self.initialized = true;
            self.is_alive_with(dt, None)
        };

        if self.count < self.min_samples {
            return true;
        }
        alive
    }

    /// Checks liveness at the given tick without recording.
    #[inline]
    #[must_use]
    pub fn check(&self, now: u64) -> bool {
        if self.count < self.min_samples {
            return true;
        }

        let dt = now.wrapping_sub(self.last_timestamp) as i64;
        // No positive gap seen yet: only the absolute deadline can judge.
        let smoothed = self.initialized.then(|| (self.acc >> self.shift) as i64);
        self.is_alive_with(dt, smoothed)
    }

    /// Alive only if the gap is within every configured deadline. A gap of
    /// zero or less (an event that just arrived, or a clock that stepped
    /// backwards) is always alive.
    #[inline]
    fn is_alive_with(&self, dt: i64, smoothed: Option<i64>) -> bool {
        if dt <= 0 {
            return true;
        }
        let within_multiple = match (self.deadline_multiple, smoothed) {
            (Some(multiple), Some(smoothed)) => {
                dt <= smoothed.saturating_mul(i64::try_from(multiple).unwrap_or(i64::MAX))
            }
            _ => true,
        };
        let within_absolute = self
            .deadline_absolute
            .is_none_or(|absolute| (dt as u64) <= absolute);
        within_multiple && within_absolute
    }

    /// Current smoothed inter-arrival interval, or `None` if < 2 events.
    #[inline]
    #[must_use]
    pub fn interval(&self) -> Option<i64> {
        if self.count >= 2 && self.initialized {
            Some((self.acc >> self.shift) as i64)
        } else {
            None
        }
    }

    /// Effective span after rounding.
    #[inline]
    #[must_use]
    pub fn effective_span(&self) -> u64 {
        self.span
    }

    /// Number of events recorded.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether the detector has reached `min_samples`.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.min_samples
    }

    /// Resets to uninitialized state.
    #[inline]
    pub fn reset(&mut self) {
        self.acc = 0;
        self.last_timestamp = 0;
        self.count = 0;
        self.initialized = false;
    }
}

impl LivenessU64Builder {
    /// Smoothing span. Rounded up to next `2^k - 1`.
    #[inline]
    #[must_use]
    pub fn span(mut self, n: u64) -> Self {
        self.span = Some(n);
        self
    }

    /// Dead when a gap exceeds `n * smoothed_interval`, the interval as it
    /// stood before that gap. Combines with `deadline_absolute`: either trips.
    #[inline]
    #[must_use]
    pub fn deadline_multiple(mut self, n: u64) -> Self {
        self.deadline_multiple = Some(n);
        self
    }

    /// Dead when a gap exceeds a fixed deadline (in ticks). Combines with
    /// `deadline_multiple`: either trips.
    #[inline]
    #[must_use]
    pub fn deadline_absolute(mut self, t: u64) -> Self {
        self.deadline_absolute = Some(t);
        self
    }

    /// Minimum events before liveness checking activates. Default: 2.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }

    /// Builds the liveness detector.
    ///
    /// # Errors
    ///
    /// - Span must have been set and >= 1.
    /// - At least one deadline must be set.
    #[inline]
    pub fn build(self) -> Result<LivenessU64, crate::ConfigError> {
        let requested = self.span.ok_or(crate::ConfigError::Missing("span"))?;
        if requested < 1 {
            return Err(crate::ConfigError::Invalid("Liveness span must be >= 1"));
        }
        if self.deadline_multiple.is_none() && self.deadline_absolute.is_none() {
            return Err(crate::ConfigError::Invalid("Liveness requires a deadline"));
        }

        let effective = crate::smoothing::ema::next_power_of_two_minus_one(requested);
        let shift = crate::smoothing::ema::log2_of_span_plus_one(effective);

        Ok(LivenessU64 {
            acc: 0,
            shift,
            span: effective,
            last_timestamp: 0,
            deadline_multiple: self.deadline_multiple,
            deadline_absolute: self.deadline_absolute,
            count: 0,
            min_samples: self.min_samples,
            initialized: false,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alive_while_events_arrive_u64() {
        let mut lv = LivenessU64::builder()
            .span(7)
            .deadline_multiple(3)
            .build()
            .unwrap();

        // Regular events every 10 units
        for i in 0..20 {
            assert!(lv.update(i * 10), "should be alive at event {i}");
        }
    }

    #[test]
    fn dead_after_silence_u64() {
        let mut lv = LivenessU64::builder()
            .span(7)
            .deadline_multiple(3)
            .build()
            .unwrap();

        // Regular events every 10 units
        for i in 0..10 {
            let _ = lv.update(i as u64 * 10);
        }

        // Check after long silence — should be dead
        // Smoothed interval ~= 10, deadline = 3 * 10 = 30, silence = 100
        assert!(!lv.check(190), "should be dead after long silence");
    }

    #[test]
    fn recovery_after_resume_u64() {
        let mut lv = LivenessU64::builder()
            .span(7)
            .deadline_multiple(3)
            .build()
            .unwrap();

        for i in 0..10 {
            let _ = lv.update(i as u64 * 10);
        }

        // Dead check
        assert!(!lv.check(200));

        // Resume events — should recover
        assert!(!lv.update(200)); // records, interval updates
        assert!(lv.update(210));
    }

    #[test]
    fn absolute_deadline_u64() {
        let mut lv = LivenessU64::builder()
            .span(7)
            .deadline_absolute(50)
            .build()
            .unwrap();

        let _ = lv.update(0);
        let _ = lv.update(10);

        // Within deadline
        assert!(lv.check(55));
        // Exceeds deadline
        assert!(!lv.check(65));
    }

    #[test]
    fn not_primed_always_alive_u64() {
        let mut lv = LivenessU64::builder()
            .span(7)
            .deadline_multiple(3)
            .min_samples(5)
            .build()
            .unwrap();

        // Even with huge gaps, returns true before primed
        assert!(lv.update(0));
        assert!(lv.update(1000));
        assert!(!lv.is_primed());
    }

    #[test]
    fn i64_basic() {
        let mut lv = LivenessI64::builder()
            .span(7)
            .deadline_multiple(3)
            .build()
            .unwrap();

        for i in 0..10 {
            assert!(lv.update(i * 100));
        }

        // Long silence
        assert!(!lv.check(2000));
    }

    #[test]
    fn reset_clears_state_u64() {
        let mut lv = LivenessU64::builder()
            .span(7)
            .deadline_multiple(3)
            .build()
            .unwrap();

        for i in 0..10 {
            let _ = lv.update(i as u64 * 10);
        }

        lv.reset();
        assert_eq!(lv.count(), 0);
        assert!(lv.interval().is_none());
    }

    #[test]
    fn errors_without_span_u64() {
        let result = LivenessU64::builder().deadline_multiple(3).build();
        assert!(matches!(result, Err(crate::ConfigError::Missing("span"))));
    }

    #[test]
    fn errors_without_deadline_u64() {
        let result = LivenessU64::builder().span(7).build();
        assert!(matches!(result, Err(crate::ConfigError::Invalid(_))));
    }

    #[test]
    fn alive_while_events_arrive_i64() {
        let mut lv = LivenessI64::builder()
            .span(7)
            .deadline_multiple(3)
            .build()
            .unwrap();

        // Regular events every 10 units
        for i in 0..20 {
            assert!(lv.update(i * 10), "should be alive at event {i}");
        }
    }

    #[test]
    fn dead_after_silence_i64() {
        let mut lv = LivenessI64::builder()
            .span(7)
            .deadline_multiple(3)
            .build()
            .unwrap();

        // Regular events every 10 units
        for i in 0..10 {
            let _ = lv.update(i as i64 * 10);
        }

        // Check after long silence — should be dead
        // Smoothed interval ~= 10, deadline = 3 * 10 = 30, silence = 100
        assert!(!lv.check(190), "should be dead after long silence");
    }

    #[test]
    fn recovery_after_resume_i64() {
        let mut lv = LivenessI64::builder()
            .span(7)
            .deadline_multiple(3)
            .build()
            .unwrap();

        for i in 0..10 {
            let _ = lv.update(i as i64 * 10);
        }

        // Dead check
        assert!(!lv.check(200));

        // Resume events — should recover
        assert!(!lv.update(200)); // records, interval updates
        assert!(lv.update(210));
    }

    #[test]
    fn absolute_deadline_i64() {
        let mut lv = LivenessI64::builder()
            .span(7)
            .deadline_absolute(50)
            .build()
            .unwrap();

        let _ = lv.update(0);
        let _ = lv.update(10);

        // Within deadline
        assert!(lv.check(55));
        // Exceeds deadline
        assert!(!lv.check(65));
    }

    #[test]
    fn not_primed_always_alive_i64() {
        let mut lv = LivenessI64::builder()
            .span(7)
            .deadline_multiple(3)
            .min_samples(5)
            .build()
            .unwrap();

        // Even with huge gaps, returns true before primed
        assert!(lv.update(0));
        assert!(lv.update(1000));
        assert!(!lv.is_primed());
    }

    #[test]
    fn reset_clears_state_i64() {
        let mut lv = LivenessI64::builder()
            .span(7)
            .deadline_multiple(3)
            .build()
            .unwrap();

        for i in 0..10 {
            let _ = lv.update(i as i64 * 10);
        }

        lv.reset();
        assert_eq!(lv.count(), 0);
        assert!(lv.interval().is_none());
    }

    #[test]
    fn errors_without_span_i64() {
        let result = LivenessI64::builder().deadline_multiple(3).build();
        assert!(matches!(result, Err(crate::ConfigError::Missing("span"))));
    }

    #[test]
    fn errors_without_deadline_i64() {
        let result = LivenessI64::builder().span(7).build();
        assert!(matches!(result, Err(crate::ConfigError::Invalid(_))));
    }

    // Regression for #760: `update()` folded the gap into the EMA before
    // testing it, so with shift k any `deadline_multiple >= 2^k` could never
    // report dead, and even below that it disagreed with `check()` by one
    // interval. For each (span, multiple) pair, the first dead gap (in
    // intervals) must be the same from both methods, and equal to the first
    // k with k * interval > multiple * interval, i.e. multiple + 1.
    fn first_dead_gap_u64(span: u64, multiple: u64) -> (Option<u64>, Option<u64>) {
        let mut lv = LivenessU64::builder()
            .span(span)
            .deadline_multiple(multiple)
            .build()
            .unwrap();
        let mut t = 0u64;
        for _ in 0..200 {
            t += 1_000;
            assert!(lv.update(t));
        }
        let via_check = (1..=1_000u64).find(|&k| !lv.check(t + k * 1_000));
        let via_update = (1..=1_000u64).find(|&k| {
            let mut probe = lv.clone();
            !probe.update(t + k * 1_000)
        });
        (via_check, via_update)
    }

    #[test]
    fn update_and_check_agree_on_first_dead_gap_u64() {
        for (span, multiple) in [(7u64, 8u64), (15, 16), (3, 4), (1, 2), (7, 3), (31, 5)] {
            let (c, u) = first_dead_gap_u64(span, multiple);
            assert_eq!(
                c,
                Some(multiple + 1),
                "check(): span {span}, multiple {multiple}"
            );
            assert_eq!(
                u,
                Some(multiple + 1),
                "update(): span {span}, multiple {multiple}"
            );
        }
    }

    // The ticket's headline case: span 7 (shift 3), multiple 8, a gap of
    // 100,000 intervals. The old `update()` returned alive forever.
    #[test]
    fn huge_gap_is_dead_from_update_u64() {
        let mut lv = LivenessU64::builder()
            .span(7)
            .deadline_multiple(8)
            .build()
            .unwrap();
        let mut t = 0u64;
        for _ in 0..200 {
            t += 1_000;
            let _ = lv.update(t);
        }
        let gap = t + 100_000 * 1_000;
        assert!(!lv.check(gap));
        assert!(!lv.update(gap));
    }

    #[test]
    fn both_deadlines_either_trips_u64() {
        // Absolute 50 is the binding one: multiple 100 of a 10-tick interval
        // would allow 1,000 ticks.
        let mut lv = LivenessU64::builder()
            .span(3)
            .deadline_multiple(100)
            .deadline_absolute(50)
            .build()
            .unwrap();
        let mut t = 0u64;
        for _ in 0..50 {
            t += 10;
            assert!(lv.update(t));
        }
        assert!(lv.check(t + 50));
        assert!(!lv.check(t + 51));
        assert!(!lv.update(t + 500));

        // Multiple 3 is the binding one: absolute 1,000,000 never trips here.
        let mut lv = LivenessU64::builder()
            .span(3)
            .deadline_multiple(3)
            .deadline_absolute(1_000_000)
            .build()
            .unwrap();
        let mut t = 0u64;
        for _ in 0..50 {
            t += 10;
            assert!(lv.update(t));
        }
        assert!(lv.check(t + 30));
        assert!(!lv.check(t + 31));
    }

    #[test]
    fn first_gap_is_judged_by_absolute_deadline_only_u64() {
        // Second event: no prior interval exists, so the multiple cannot judge
        // it, but a configured absolute deadline still does.
        let mut lv = LivenessU64::builder()
            .span(7)
            .deadline_multiple(3)
            .deadline_absolute(50)
            .build()
            .unwrap();
        assert!(lv.update(0));
        assert!(!lv.update(60)); // 60 > 50
        let mut lv = LivenessU64::builder()
            .span(7)
            .deadline_multiple(3)
            .build()
            .unwrap();
        assert!(lv.update(0));
        assert!(lv.update(60)); // no absolute deadline: nothing to judge the first gap
    }

    // Copilot's finding on #769: a backwards step used to be folded into the
    // EMA, so a large one drove the estimate negative and the next real gap
    // read dead. The step must leave the estimate untouched.
    #[test]
    fn backwards_step_does_not_poison_estimate_u64() {
        let mut lv = LivenessU64::builder()
            .span(7)
            .deadline_multiple(3)
            .build()
            .unwrap();
        let mut t = 1_000_000u64; // headroom for the step back
        for _ in 0..50 {
            t += 1_000;
            assert!(lv.update(t));
        }
        t -= 100_000; // clock steps back 100 intervals
        assert!(lv.update(t));
        for _ in 0..10 {
            t += 1_000; // normal gaps in the new clock domain
            assert!(lv.update(t));
        }
        // Estimate is still exactly 1,000: dead at the fourth missed interval.
        assert!(lv.check(t + 3_000));
        assert!(!lv.check(t + 3_001));
    }

    #[test]
    fn backwards_step_does_not_poison_estimate_i64() {
        let mut lv = LivenessI64::builder()
            .span(7)
            .deadline_multiple(3)
            .build()
            .unwrap();
        let mut t = 0i64;
        for _ in 0..50 {
            t += 1_000;
            assert!(lv.update(t));
        }
        t -= 100_000;
        assert!(lv.update(t));
        for _ in 0..10 {
            t += 1_000;
            assert!(lv.update(t));
        }
        assert!(lv.check(t + 3_000));
        assert!(!lv.check(t + 3_001));
    }

    // Only backwards gaps so far: no estimate exists, so the multiple cannot
    // judge, but the absolute deadline still does, from both methods.
    #[test]
    fn unseeded_estimate_is_judged_by_absolute_only_u64() {
        let mut lv = LivenessU64::builder()
            .span(7)
            .deadline_multiple(3)
            .deadline_absolute(50)
            .build()
            .unwrap();
        assert!(lv.update(100));
        assert!(lv.update(50)); // backwards: re-anchors to 50, no estimate
        assert!(lv.check(100)); // 50 ticks of silence, at the absolute
        assert!(!lv.check(101)); // past it
        assert!(lv.update(60)); // first positive gap (10): seeds the estimate
        assert!(lv.update(70));
        assert!(lv.check(100)); // 30 <= 3 * 10
        assert!(!lv.check(101));
    }

    #[test]
    fn backwards_clock_is_alive_u64() {
        let mut lv = LivenessU64::builder()
            .span(7)
            .deadline_multiple(3)
            .deadline_absolute(50)
            .build()
            .unwrap();
        for i in 1..=10u64 {
            let _ = lv.update(i * 10);
        }
        assert!(lv.check(95)); // behind the last event: nothing has been missed
        assert!(lv.update(90));
    }

    #[test]
    fn update_and_check_agree_on_first_dead_gap_i64() {
        for (span, multiple) in [(7u64, 8u64), (15, 16), (3, 4), (1, 2), (7, 3)] {
            let mut lv = LivenessI64::builder()
                .span(span)
                .deadline_multiple(multiple)
                .build()
                .unwrap();
            let mut t = 0i64;
            for _ in 0..200 {
                t += 1_000;
                assert!(lv.update(t));
            }
            let via_check = (1..=1_000i64).find(|&k| !lv.check(t + k * 1_000));
            let via_update = (1..=1_000i64).find(|&k| {
                let mut probe = lv.clone();
                !probe.update(t + k * 1_000)
            });
            assert_eq!(
                via_check,
                Some(multiple as i64 + 1),
                "check(): {span}/{multiple}"
            );
            assert_eq!(
                via_update,
                Some(multiple as i64 + 1),
                "update(): {span}/{multiple}"
            );
        }
    }

    #[test]
    fn both_deadlines_either_trips_i64() {
        let mut lv = LivenessI64::builder()
            .span(3)
            .deadline_multiple(100)
            .deadline_absolute(50)
            .build()
            .unwrap();
        let mut t = 0i64;
        for _ in 0..50 {
            t += 10;
            assert!(lv.update(t));
        }
        assert!(lv.check(t + 50));
        assert!(!lv.check(t + 51));
    }
}
