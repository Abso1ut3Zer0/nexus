# Changelog

All notable changes to nexus-stats-monitoring are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/),
with the project-specific allowance that a minor bump may carry small,
narrowly-scoped breaking changes when external blast radius is
contained.

## [Unreleased]

### Added

- **`ErrorRate::summary()` and `EventRate::summary(now)`:** the interval
  so far, as `take` would return it, with nothing changed. Every type with
  a `take()` now has a `summary()`. On `EventRate` the summary's
  `load_average()` is what the averages would become if the window closed
  at `now`; the meter's own averages move only at a `take`.

### Changed (breaking)

- **`PollSaturation<T>` takes any `Timestamp`,** in place of `u64` ticks.
  The budget and `behind` are `Duration`s. Pass this thread's own
  monotonic clock, not a message's timestamp.
- **`SojournSaturation` takes the sojourn and the budget as `Duration`s.**
  Compute the sojourn with `dequeued.since(enqueued)`, which is zero on
  clock skew.
- **`summary()` on both** returns the period so far and changes nothing.
  `take()` returns the same and starts a new period.
- **`PollSummary` and `SojournSummary` have private fields,** read through
  methods (`messages_seen()`, `max_behind()`, `min_sojourn()`, ...). The
  `_ticks` suffixes are gone. `min_sojourn()` and `max_sojourn()` are
  `None` for an empty period, and `mean_sojourn()` returns a `Duration`.
  `PollSummary` no longer has a `Default`.
- **`max_backlog_messages()` counts only messages that queued behind
  another.** It no longer includes the first message after an empty poll,
  so a healthy thread reads 0, not 1.
- `count()` and `is_primed()` are removed from both types. The memory
  layout of `PollSaturation` is no longer fixed.
- **`EventRate::load()` is renamed `load_average()`,** and `Load` is
  `LoadAverage`.

### Added

- `PollSaturation::checked_on_work`: returns `NonMonotonicTime` and counts
  nothing when the time is before the floor. `on_work` reads zero behind
  and still counts.

### Changed (breaking)

- **The clocked types take any `Timestamp`,** which now includes `i64`
  nanoseconds, the named types `Nanos`, `Micros`, `Millis` and `Seconds`,
  and a caller's own time type. An unsuffixed integer literal no longer
  infers as a timestamp; write `0_i64`.

### Changed (breaking, time)

- **`WindowedMax`, `WindowedMin` and `CoDel` take time as `i128`
  nanoseconds or `Instant`,** through the `Timestamp` trait, in place of
  `u64` ticks. A window, an interval and a sojourn are each a `Duration`.
  A tick counter that wraps is no longer supported.
- **`WindowedMax<V, T>` and `WindowedMin<V, T>`** have a second type
  parameter, the clock. `new` takes the window as a `Duration`, and a
  window of `Duration::MAX` means forever. The algorithm and its results
  are unchanged.
- **`CoDel<T>` is generic over the clock only.** The sojourn is a
  `Duration`, so the `f64` and `i64` forms, the NaN check and the `Result`
  on `update` are gone. As in RFC 8289 there is no warm-up: `min_samples`
  and `is_primed()` are removed and `update` returns the `Condition`. The
  builder is replaced by `CoDel::new(target, interval)`. `checked_update`
  reports a time that goes back as `NonMonotonicTime`. `condition()`,
  `target()` and `interval()` are added.

### Changed (breaking, time)

- **`Liveness` and `EventRate` take time as `i128` nanoseconds or
  `Instant`,** through the `Timestamp` trait, in place of `u64` ticks.
  `Liveness::update` ignores a time that goes back, and `checked_update`
  reports it as `NonMonotonicTime`. `EventRate::take` refuses a time that
  is not later.
- **`Liveness` reports a suspicion level, not a verdict.** It follows
  Apache Cassandra's failure detector: `check(now)` returns a `Suspicion`
  with the silence as a multiple of the mean gap (`ratio()`), the chance a
  live source would be this quiet (`probability_alive()`), and Cassandra's
  `phi()`. The mean is over the last `window` gaps (default 1,000), kept as
  an exact integer sum, and `longest_recorded_gap` keeps a long outage out
  of it. `span`, `deadline_multiple`, `deadline_absolute`, `min_samples`,
  `interval()`, `effective_span()` and the `bool` results are removed. It
  now needs `alloc`, and `probability_alive()` also needs `std` or `libm`.
- **`EventRate` counts events and reports per window.** `update()` and
  `update_n(n)` read no clock. `take(now)` closes the window and returns a
  `RateSummary`: the events, the exact rate, the mean rate since the start,
  and the load averaged over 1, 5 and 15 minutes as in Dropwizard's `Meter`
  and the UNIX load average. `EventRate::new(start)` takes the start time,
  `take` refuses a time that is not later, and `reset_at(now)` replaces
  `reset()`. `rate()`, `interval()`, `effective_span()` and the builder are
  removed. It now needs `std` or `libm`.

### Removed (moved)

- `HawkesIntensity` is now in `nexus-stats-regression` (`estimation`),
  beside `PoissonEstimator` and the Kalman filters.

### Fixed

- **`EventRate` reported one over an exponentially weighted average of
  the gap between events,** which weighs each event, not each unit of
  time. It now counts events over a window.

### Changed (breaking)

- **`Drawdown` is replaced by `PeakToTrough<T>`:** the fall from a running
  high, for any type that is `Copy + PartialOrd + Sub`, so a caller's own
  decimal type works. `update` returns the reading, `Fall { high, current,
  largest }`, with no `Result`. `reading()` is `None` before the first
  sample, where `drawdown()` and `max_drawdown()` returned zero.
  `checked_update` exists for `f64` (refuses NaN, infinity and a magnitude
  above `f64::MAX / 2`) and `i64` (refuses a fall that overflows).
- **`Jitter` is the RFC 3550 interarrival jitter estimator,** in the two
  forms of the RFC's appendix A.8: `Jitter<f64>` and the scaled-integer
  `Jitter<i64>` with its rounding. The gain is fixed at 1/16 and the
  estimate starts at zero. The builder, the configurable smoothing,
  seeding, `jitter_ratio()`, `last_deviation()` and `effective_span()` are
  removed: none is in the RFC. `update` returns `Option<T>` with no
  `Result`; `checked_update` refuses what would make the estimate
  overflow. Values differ from earlier releases.
- **`ErrorRate` reports three readings and no verdict.** The count of
  errors, in total and per interval (Brendan Gregg's USE method); the
  ratio of events that failed per interval (the SRE book's Errors signal);
  and a smoothed ratio. `take()` returns an interval as an `ErrorSummary`.
  The threshold, the `Condition` returned by `update`,
  `reconfigure_threshold`, `update_weighted` and `error_rate()` are
  removed.

### Removed

- **`RunningMax`, `RunningMin`, `MaxGauge`.** Each is one line of std:
  `max = max.max(x)`, `min = min.min(x)`, and an `Option<T>` read with
  `take()` for the maximum since the last read.

### Changed (breaking)

- **`WindowedMax` and `WindowedMin` have one `update(timestamp, value) ->
  Option<T>`** for `f64` and `i64`, in place of a float form returning
  `Result` and an integer form returning the value. A NaN is ignored, as
  `f64::max` ignores one: the window, the count and the clock stay as they
  were. Infinity is a value like any other.
- **`WindowedMax` and `WindowedMin` gain `checked_update`,** which returns
  an error where `update` skips in silence: `DataError::NotANumber` for a
  NaN, `DataError::NonMonotonicTime` for a timestamp before the last one
  taken. One tick far ahead of the real clock makes every later sample
  late until `reset()`; the error is how a caller finds out.
- **Timestamps are compared plainly, not as a wrapping counter.** A forward
  jump of any size is a long gap (a jump of 2^63 ticks or more used to
  read as late and freeze the tracker). A `u64` counter that wraps is no
  longer followed across the wrap.
- **`PeakHold` is an amplitude tracker.** It tracks the magnitude of each
  sample: `-5` is a level of `5`, and `i64::MIN` counts as `i64::MAX`.
  Fed signed values, it could report a decayed peak above every sample
  seen. A negative-only stream now reports magnitudes (this replaces the
  behavior from #763).
- **`PeakHold` has one `update(sample) -> Option<T>`.** A NaN is ignored.
  An infinite sample becomes a peak that holds until `reset()`;
  `PeakHold<f64>::checked_update` refuses NaN and infinity and leaves the
  tracker unchanged. The integer form has no `checked_update`.
- **`PeakHold::peak()` returns `Option<T>`:** `None` before the first
  sample, where it returned zero.
- **`PeakHold::<i64>::builder().build()` returns the tracker,** not a
  `Result` that could never be an error.

### Fixed

- **`CoDel` counts a sojourn equal to the target as above it**
  ([#791](https://github.com/Abso1ut3Zer0/nexus/issues/791)). RFC 8289
  resets the timer only on `sojourn_time < TARGET`. A sojourn at the
  target used to clear it, so a queue held at the target never read as
  standing; it is now `Degraded` after one interval.
- `WindowedMax` and `WindowedMin` report an infinite first value. The
  starting values were `T::MIN` and `T::MAX`, which an infinity of the
  same sign could not beat.

### Added

- The crate. The fifteen monitors move here from `nexus-stats-core`'s
  `monitoring` module. No change to any of them.
- `Condition`, `ConfigError`, `DataError` and `Sample` are re-exported, so
  the crate can be used without a direct dependency on `nexus-stats-core`.
