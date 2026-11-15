# Monitoring

Health, rate, and envelope tracking primitives. Module path: `nexus_stats_core::monitoring`.

These types all answer "is this system healthy?" questions in O(1) with fixed memory. Most accept either raw `u64`/`i64` timestamps (no_std) or `std::time::Instant` (std).

## At a glance

| Type | What it does |
|------|--------------|
| `DrawdownF64` / `DrawdownI64` | Peak-to-trough decline, classic P&L metric |
| `RunningMaxF64` / `RunningMinF64` | All-time max/min since last `reset()` |
| `WindowedMaxF64` / `WindowedMinF64` | Sliding window max/min (monotone deque) |
| `PeakHoldF64` / `PeakHoldF32` | Peak envelope with exponential decay |
| `MaxGaugeF64` / `MaxGaugeI64` | Reset-on-read maximum (classic metric primitive) |
| `LivenessU64` / `LivenessI64` / `LivenessInstant` | "Has anything happened recently?" detector |
| `EventRateU64` / `EventRateInstant` | Smoothed events-per-unit-time |
| `CoDelU64` / `CoDelInstant` | Controlled Delay queue latency monitor |
| `PollSaturation` | Consumer-side saturation from poll outcomes: how many messages waited behind this thread, for how long at most |
| `SaturationF64` | Resource utilization threshold with hysteresis |
| `ErrorRateF64` | Error fraction tracker with alert conditions |
| `JitterF64` / `JitterF32` | Inter-arrival / sample-to-sample variation |

Each type comes in both the raw-timestamp and `Instant`-based flavors where time is involved. Use `Instant` in normal `std` code; use the raw-timestamp versions when you're in `no_std` or when you want deterministic wall-clock semantics (e.g. replaying a recorded timestamp).

---

## Drawdown

Tracks the running peak and the maximum observed drop from that peak. Essential P&L metric.

```rust
use nexus_stats_core::monitoring::DrawdownF64;

let mut dd = DrawdownF64::new();
for equity in equity_curve {
    dd.update(equity).unwrap();
}
let max_dd = dd.max_drawdown();     // largest drop in absolute units
let current = dd.current_drawdown(); // current drop from peak
```

**Use for:** P&L monitoring, risk limits, drawdown-based circuit breakers.

---

## RunningMax / RunningMin

All-time extrema since construction or last `reset()`.

```rust
use nexus_stats_core::monitoring::RunningMaxF64;
let mut peak = RunningMaxF64::new();
for pressure in pressures { peak.update(pressure).unwrap(); }
let p = peak.value();
```

**Use for:** watermark tracking. Shortest, cheapest type in this crate.

---

## WindowedMax / WindowedMin

Sliding window max/min over a fixed-size history. Uses a monotone deque for O(1) amortized update.

```rust
use nexus_stats_core::monitoring::WindowedMaxU64;

// u64 timestamp-based window, length in timestamp units
let mut w = WindowedMaxU64::new(1_000_000).unwrap(); // 1M-unit window
w.update(timestamp, value).unwrap();
let max = w.value();
```

Variants exist for `Instant`-based windows and `i64` timestamps (useful for signed epochs).

**Use for:** fire-and-forget sliding peak/trough queries; e.g. "what's the max bid change in the last 5s?".

**Caveats:** window size is in *timestamp units*, not sample count. Pass the same units you use in `update(timestamp, ...)`.

---

## PeakHold

Peak envelope with exponential decay. Like a volume meter on a mixing board: spikes jump up, then the level decays back down.

```rust
use nexus_stats_core::monitoring::PeakHoldF64;

let mut hold = PeakHoldF64::builder().halflife(100.0).build().unwrap();
for sample in stream {
    let envelope = hold.update(sample).unwrap();
}
```

**Use for:** volume indicators, burst-aware rate visualization, "recent peak" displays.

---

## MaxGauge

The classic metrics library primitive: latch the maximum, read-and-reset clears it.

```rust
use nexus_stats_core::monitoring::MaxGaugeF64;
let mut gauge = MaxGaugeF64::new();
for sample in samples { gauge.update(sample).unwrap(); }

// At end of reporting interval:
let peak = gauge.take();  // returns the max, resets to 0
```

**Use for:** Prometheus-style "max since last scrape" gauges.

---

## Liveness

Detects "source hasn't sent anything in a while". Maintains last-update timestamp, compares against current time, returns true if alive.

```rust
use nexus_stats_core::monitoring::LivenessInstant;
use std::time::{Duration, Instant};

let mut live = LivenessInstant::builder()
    .timeout(Duration::from_secs(5))
    .build()
    .unwrap();

let alive = live.update(Instant::now());
```

**Use for:** feed health checks, watchdogs, dead-man switches.

---

## EventRate

Smoothed events-per-unit-time. Each `update(timestamp)` is one event; the type computes and smooths the instantaneous rate.

```rust
use nexus_stats_core::monitoring::EventRateInstant;
let mut rate = EventRateInstant::builder().halflife_secs(1.0).build().unwrap();
rate.update(Instant::now());
let events_per_sec = rate.rate();
```

**Use for:** print rates, tick rates, request rates — any streaming counter where you want a smoothed rate.

---

## CoDel

The Controlled Delay algorithm from Van Jacobson. Monitors queue sojourn time; fires when sojourn is above target for a sustained interval. Used in queue health / backpressure detection.

```rust
use nexus_stats_core::monitoring::CoDelInstant;
// ... see source for config API
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

## Saturation

Tracks "is this resource at high utilization?" using a threshold with hysteresis.

```rust
use nexus_stats_core::monitoring::SaturationF64;
// builder API, see source
```

**Use for:** CPU/IO/disk saturation alarms, utilization-based load shedding.

---

## ErrorRate

Rolling error fraction with alert `Condition` transitions (`Normal`, `Warning`, `Critical`).

```rust
use nexus_stats_core::monitoring::ErrorRateF64;

let mut er = ErrorRateF64::builder()
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
use nexus_stats_core::monitoring::JitterF64;
let mut j = JitterF64::builder().halflife(20.0).build().unwrap();
for x in stream { j.update(x).unwrap(); }
let jitter = j.value();
```

**Use for:** network quality, clock stability, sensor smoothness checks.

---

## Cross-references

- Percentile-based SLO tracking: [`PercentileF64`](statistics.md#percentilef64--online-percentile-p).
- Adaptive anomaly scoring on top of these gauges: [`AdaptiveThreshold`](../../nexus-stats-detection/docs/INDEX.md).
- Drop/backpressure decisions: combine `CoDel` with `ErrorRate` — see umbrella `use-cases/backpressure.md`.
