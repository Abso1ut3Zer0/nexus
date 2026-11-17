# Monitoring

Health, rate, and envelope tracking primitives. Module path: `nexus_stats_core::monitoring`.

These types all answer "is this system healthy?" questions in O(1) with fixed memory. Most accept either raw `u64`/`i64` timestamps (no_std) or `std::time::Instant` (std).

## At a glance

| Type | What it does |
|------|--------------|
| `Drawdown<f64>` / `Drawdown<i64>` | Peak-to-trough decline, classic P&L metric |
| `RunningMax<f64>` / `RunningMin<f64>` | All-time max/min since last `reset()` |
| `WindowedMax<T>` / `WindowedMin<T>` | Sliding time-window max/min (Nichols' 3-sample algorithm), `f64` or `i64` |
| `PeakHold<f64>` / `PeakHold<i64>` | Peak envelope with exponential decay |
| `MaxGauge<f64>` / `MaxGauge<i64>` | Reset-on-read maximum (classic metric primitive) |
| `Liveness` | "Has anything happened recently?" detector |
| `EventRate` | Smoothed events-per-unit-time |
| `CoDel<i64>` / `CoDel<f64>` | Controlled Delay queue latency monitor |
| `PollSaturation` | Consumer-side saturation from poll outcomes: how many messages waited behind this thread, for how long at most |
| `SojournSaturation` | Consumer saturation from stamped queue sojourn: exact per-message wait, summarized per period |
| `ErrorRate` | Error fraction tracker with alert conditions |
| `Jitter<f64>` / `Jitter<i64>` | Inter-arrival / sample-to-sample variation |

Time-aware types take `u64` ticks in any unit; `clock::MonotonicClock` is the std bridge from `Instant` (nanoseconds since construction).

---

## Drawdown

Tracks the running peak and the maximum observed drop from that peak. Essential P&L metric.

```rust
use nexus_stats_core::monitoring::Drawdown;

let mut dd = Drawdown::<f64>::new();
for equity in equity_curve {
    dd.update(equity).unwrap();
}
let max_dd = dd.max_drawdown();     // largest drop in absolute units
let current = dd.drawdown(); // current drop from peak
```

**Use for:** P&L monitoring, risk limits, drawdown-based circuit breakers.

---

## RunningMax / RunningMin

All-time extrema since construction or last `reset()`.

```rust
use nexus_stats_core::monitoring::RunningMax;
let mut peak = RunningMax::<f64>::new();
for pressure in pressures { peak.update(pressure).unwrap(); }
let p = peak.max();
```

**Use for:** watermark tracking. Shortest, cheapest type in this crate.

---

## WindowedMax / WindowedMin

Sliding time-window max/min with Kathleen Nichols' 3-sample algorithm (the Linux kernel's `win_minmax`, used by BBR): three stored samples, O(1) per update, approximate by design but never on the wrong side of the true extremum. `WindowedMax<T>` / `WindowedMin<T>` for `T` in `f64`, `i64`.

```rust
use nexus_stats_core::monitoring::WindowedMax;

// u64 timestamp-based window, length in timestamp units
let mut w = WindowedMax::<f64>::new(1_000_000).unwrap(); // 1M-tick window
w.update(timestamp, value).unwrap();                       // `WindowedMax<i64>::update` returns the value directly
let max = w.max();                                         // Option<f64>, as of the last update
```

**Use for:** fire-and-forget sliding peak/trough queries; e.g. "what's the max bid change in the last 5s?".

**Caveats:** window size is in *timestamp units*, not sample count. Pass the same units you use in `update(timestamp, ...)`.

---

## PeakHold

Peak envelope with exponential decay. Like a volume meter on a mixing board: spikes jump up, then the level decays back down.

```rust
use nexus_stats_core::monitoring::PeakHold;

let mut hold = PeakHold::<f64>::builder()
    .hold_samples(10)     // hold a peak for 10 samples
    .decay_rate(0.99)     // then decay 1% per sample
    .build()
    .unwrap();
for sample in stream {
    let envelope = hold.update(sample).unwrap();
}
```

**Use for:** volume indicators, burst-aware rate visualization, "recent peak" displays.

---

## MaxGauge

The classic metrics library primitive: latch the maximum, read-and-reset clears it.

```rust
use nexus_stats_core::monitoring::MaxGauge;
let mut gauge = MaxGauge::<f64>::new();
for sample in samples { gauge.update(sample).unwrap(); }

// At end of reporting interval:
let peak = gauge.take();  // returns the max, resets to 0
```

**Use for:** Prometheus-style "max since last scrape" gauges.

---

## Liveness

Detects "source hasn't sent anything in a while". A fixed-point EMA of inter-arrival ticks with a deadline: `update(tick)` on each event, `check(now)` from a timer to catch silence.

```rust
use nexus_stats_core::clock::{Clock, MonotonicClock};
use nexus_stats_core::monitoring::Liveness;

let clock = MonotonicClock::new();                 // nanosecond ticks since construction
let mut live = Liveness::builder()
    .span(15)
    .deadline_multiple(5)                     // dead after 5x the smoothed interval
    .deadline_absolute(5_000_000_000)         // or 5 s, whichever trips first
    .build()
    .unwrap();

let alive = live.update(clock.stamp());       // on each event
let still_alive = live.check(clock.stamp());  // on a timer
```

**Use for:** feed health checks, watchdogs, dead-man switches.

---

## EventRate

Smoothed events-per-unit-time. Each `update(timestamp)` is one event; the type computes and smooths the instantaneous rate.

```rust
use nexus_stats_core::monitoring::EventRate;

let mut rate = EventRate::builder().span(20).build().unwrap();
rate.update(clock.stamp());                    // one call per event, with its own tick
let events_per_tick = rate.rate();             // Option<f64>; divide by ticks-per-second for Hz
```

**Use for:** print rates, tick rates, request rates — any streaming counter where you want a smoothed rate.

---

## CoDel

The Controlled Delay algorithm from Van Jacobson. Monitors queue sojourn time; fires when sojourn is above target for a sustained interval. Used in queue health / backpressure detection.

```rust
use nexus_stats_core::monitoring::CoDel;

let mut codel = CoDel::<i64>::builder()
    .target(50_000)          // 50 µs: sojourn above this is "delayed"
    .interval(100_000_000)     // 100 ms: standing if it stays above target this long
    .build()
    .unwrap();
let condition = codel.update(now, dequeued - enqueued);   // Option<Condition>
```

**Use for:** queue-health signals, AQM-style drop decisions, backpressure-before-loss alerts.

---

## PollSaturation

Saturation of a consumer thread from what each poll returned: no message timestamps, no queue depth, no clock read on an idle spin. An empty poll (or a short batch poll) proves the input empty; every message taken afterwards arrived after that proof, so `now - proof` bounds how long any message in a poll waited for this thread. `take()` returns a `PollSummary` of every poll since the previous take, whenever the caller decides to snap (a timer, a message count, an event): the count form (`max_messages_per_poll`, `max_backlog_messages`), the duration form (`messages_waited`, `messages_over_budget`, `max_behind_ticks`) and the `is_fully_utilized` / `is_backlogged` flags. Summaries merge exactly.

```rust
use nexus_stats_core::monitoring::PollSaturation;

let mut sat = PollSaturation::new(50_000);          // budget: 50 µs in ns ticks
// per poll:
//   nothing returned        -> sat.on_idle()
//   n messages start at now -> let behind = sat.on_work(now, n);
//   short batch poll        -> sat.on_drained(at)
// whenever you decide to snap (timer, count, event):
let summary = sat.take();
```

**Use for:** per-thread saturation beside utilization (USE method), deciding whether a late message waited for this consumer or was late upstream, backlog detection under poll limits.

---

## SojournSaturation

The stamped twin of `PollSaturation`. Feed it each message's queue sojourn (dequeue tick minus enqueue tick, same clock); `take()` returns a `SojournSummary` of the period: `messages_seen`, `messages_over_budget`, `min_sojourn_ticks` (the floor; zero means the clocks disagree), `max_sojourn_ticks`, `total_sojourn_ticks` with an integer `mean_sojourn_ticks()`, and `is_backlogged` (no message within budget all period). No clock, no interval, no smoothing; snap when you decide.

```rust
use nexus_stats_core::monitoring::SojournSaturation;

let mut sat = SojournSaturation::new(50_000);       // budget: 50 µs in ns ticks
sat.update(dequeued_ns.wrapping_sub(enqueued_ns) as i64); // u64 stamps, same clock; negative on skew, clamped inside
let summary = sat.take();                            // timer, count or event
```

**Use for:** exact queue-wait reporting where messages carry an enqueue stamp (our queues and shm, exchange timestamps for upstream lag), beside `PollSaturation` for the count form and the utilization flag.

---

## ErrorRate

Rolling error fraction with alert `Condition` transitions (`Normal`, `Degraded`).

```rust
use nexus_stats_core::monitoring::ErrorRate;

let mut er = ErrorRate::builder()
    // thresholds, halflife, warmup
    .build().unwrap();

if let Some(cond) = er.update(request_succeeded) {
    // state changed - alert
}
```

**Use for:** SLO alerting, reliability dashboards, circuit-breaker backends.

---

## Jitter

Sample-to-sample variation (`|x_t - x_{t-1}|` smoothed), or inter-arrival jitter for event streams.

```rust
use nexus_stats_core::monitoring::Jitter;
let mut j = Jitter::<f64>::builder().halflife(20.0).build().unwrap();
for x in stream { j.update(x).unwrap(); }
let jitter = j.jitter();
```

**Use for:** network quality, clock stability, sensor smoothness checks.

---

## Cross-references

- Percentile-based SLO tracking: [`Percentile`](statistics.md#percentile--online-percentile-p²).
- Adaptive anomaly scoring on top of these gauges: [`AdaptiveThreshold`](../../nexus-stats-detection/docs/INDEX.md).
- Drop/backpressure decisions: combine `CoDel` with `ErrorRate` — see umbrella `use-cases/backpressure.md`.
