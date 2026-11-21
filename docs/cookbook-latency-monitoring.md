# Cookbook: Latency Monitoring and Alerting

**Goal:** instrument a live trading system so you can (a) know your
tail latency right now, (b) detect shifts before users do, and
(c) postmortem a regression by looking at recent samples.

**Crates used:**
`nexus-stats` (Percentile, EwmVar, CUSUM, Drawdown, Jitter),
`nexus-rt` (instrumentation handlers), `nexus-logbuf` (rolling
sample buffer for postmortem).

This cookbook assumes you already have a strategy handler — see
[cookbook-strategy-handler.md](./cookbook-strategy-handler.md) for
the baseline.

---

## 1. What you are actually measuring

Latency in a trading system breaks into named segments, each with
its own distribution and its own bug modes:

| Segment | Definition | Where to sample |
|---------|------------|-----------------|
| **Wire → decode** | Bytes on socket → decoded frame | Inside the parser |
| **Tick-to-trade (T2T)** | Wire arrival → order bytes on socket | Start: reader task; stop: WS writer |
| **Decision latency** | Parsed tick → intent emitted | Start: handler entry; stop: intent written to queue |
| **Network RTT** | Our order bytes → exchange ack bytes | Match client id in outbound + inbound |
| **Scheduler jitter** | Loop iteration gap | Measured by the loop itself |

You want **separate** `Percentile` instances for each. Mixing them
into one histogram hides the bottleneck.

---

## 2. Resources: one bucket per metric

```rust
use nexus_stats::statistics::{PercentileF64, EwmVar};
use nexus_stats::detection::CusumF64;
use nexus_stats::monitoring::{DrawdownF64, JitterF64};
use nexus_logbuf::spsc as logbuf_spsc;
use nexus_rt::Resource;

/// All latency metrics the app tracks. Owned by the main loop thread.
#[derive(Resource)]
pub struct LatencyMetrics {
    // Per-segment tail trackers. Target p999 so `is_primed()` waits
    // for 1000 samples before reporting.
    pub t2t_p999_ns: PercentileF64,
    pub decision_p999_ns: PercentileF64,
    pub rtt_p999_ns: PercentileF64,

    // Smoothed mean + variance for drift detection.
    pub t2t_mean_var: EwmVar,

    // Shift detector — rings when the distribution steps up.
    pub t2t_shift: CusumF64,

    // Scheduler jitter — gap between successive loop iterations.
    pub loop_jitter: JitterF64,

    // Drawdown of throughput — alerts when msg_rate collapses.
    pub rate_drawdown: DrawdownF64,

    // Rolling sample buffer for postmortem. Every sample goes here
    // as a little fixed-width record, one producer, one consumer
    // (the postmortem dumper thread).
    pub sample_log: logbuf_spsc::Producer,
}
```

Why these types:

- **`PercentileF64` with target 0.999** — P² algorithm, O(1) per
  update, adaptive priming (waits for 1000 samples before
  reporting).
- **`EwmVar`** — running mean and variance, forgetting factor.
  Bounded growth — safe to run for days.
- **`CusumF64`** — the canonical change-point detector. Gives you a
  boolean "did the distribution shift?" with tunable sensitivity.
- **`JitterF64`** — interval-to-interval jitter, not latency. Good
  for "is my event loop smooth?"
- **`DrawdownF64`** — peak-to-trough on any series. Applied to
  throughput it answers "did we fall off a cliff?"

---

## 3. Sampling inside a handler

The trick is to sample **as close to the edges as possible** without
polluting the hot path. Read a timestamp at entry, another at exit,
feed the delta into the resource.

```rust
use nexus_rt::{Res, ResMut};

#[inline(always)]
fn now_ns() -> u64 {
    // Use rdtsc + calibration for sub-20ns. Instant::now() is fine
    // for non-latency-critical code but costs 20-30ns per call.
    unsafe { core::arch::x86_64::_rdtsc() }  // calibrate elsewhere
}

pub fn on_tick_instrumented(
    mut metrics: ResMut<LatencyMetrics>,
    // ... strategy resources ...
    tick: QuoteTick,
) {
    let t0 = now_ns();

    // --- strategy work happens here ---
    // run_strategy(...);
    // --- done ---

    let dt = (now_ns() - t0) as f64;

    // Feed every segment exactly once per event.
    let _ = metrics.decision_p999_ns.update(dt);
    let _ = metrics.t2t_mean_var.update(dt);
    // fixed: CusumF64::update returns Result<Option<Direction>, DataError>.
    if let Ok(Some(direction)) = metrics.t2t_shift.update(dt) {
        // Shift detected — emit an alert event. Reset so we
        // don't keep re-firing on the same shift.
        tracing::warn!(?dt, ?direction, "t2t latency shift detected");
        metrics.t2t_shift.reset();
    }

    // Write the raw sample into the rolling log for postmortem.
    let record = LatencySample {
        ts_ns: t0,
        segment: Segment::Decision as u8,
        _pad: [0; 7],
        dt_ns: dt as u64,
        tick_ts_ns: tick.ts_ns,
    };
    // fixed: Producer method is `try_claim` and returns
    // `Result<WriteClaim, BufferFull>`. WriteClaim derefs to &mut [u8].
    if let Ok(mut claim) = metrics
        .sample_log
        .try_claim(std::mem::size_of::<LatencySample>())
    {
        claim.copy_from_slice(bytemuck::bytes_of(&record));
        claim.commit();
    }
}

#[repr(C)]
#[derive(Clone, Copy, bytemuck::Pod, bytemuck::Zeroable)]
struct LatencySample {
    ts_ns: u64,
    segment: u8,
    _pad: [u8; 7],
    dt_ns: u64,
    tick_ts_ns: u64,
}

#[repr(u8)]
enum Segment { T2T = 0, Decision = 1, Rtt = 2 }
```

Notes:

- **Sample on every event, not on 1/Nth.** Percentile and CUSUM need
  every point. Skipping breaks the detector.
- **Write to the log buffer unconditionally.** The log is SPSC and
  a consumer drains to disk on a cold thread. There's no cost
  beyond a few cycles for the claim.
- **Don't allocate in the sample path.** `LatencySample` is `Pod`;
  `bytemuck::bytes_of` is zero-cost.

---

## 4. Scheduler jitter

The strategy handler measures its own work. But what about the gap
**between** events? That's event-loop jitter, and a scheduler that
hiccups will show up there before it shows up anywhere else.

Instrument the main loop itself:

```rust
fn main() {
    let mut world = build_world();
    // ... setup ...
    let mut last_iter_ns: u64 = now_ns();

    loop {
        let iter_ns = now_ns();
        let gap_ns = iter_ns.saturating_sub(last_iter_ns);
        last_iter_ns = iter_ns;

        // Feed into jitter tracker — does NOT go through a handler,
        // because we want to measure the gap including the dispatch
        // overhead.
        // fixed: `World::resource_mut::<T>()` — panics if missing; there
        // is no `try_get_mut`. Use `contains::<T>()` if you need a check.
        let m = world.resource_mut::<LatencyMetrics>();
        let _ = m.loop_jitter.update(gap_ns as f64);

        // Normal event dispatch
        // ...
    }
}
```

If `loop_jitter.max()` jumps from 5μs to 500μs you've got a context
switch, a GC, a page fault, or someone installed a Slack client on
a production box. It's not the strategy — it's the host.

---

## 5. Alerting

The raw stats are data. Alerting is policy. A simple policy looks
like:

```rust
pub struct AlertPolicy {
    pub t2t_p999_warn_ns: f64,    // e.g. 50_000.0 ( 50μs)
    pub t2t_p999_crit_ns: f64,    // e.g. 200_000.0
    pub rate_drawdown_warn: f64,  // e.g. 0.5 (50% drop from peak)
}

pub fn check_alerts(
    metrics: Res<LatencyMetrics>,
    policy: Res<AlertPolicy>,
) {
    // fixed: PercentileF64 query is `.percentile()`, not `.value()`.
    if let Some(p999) = metrics.t2t_p999_ns.percentile() {
        if p999 > policy.t2t_p999_crit_ns {
            tracing::error!(p999, "t2t p999 CRITICAL");
        } else if p999 > policy.t2t_p999_warn_ns {
            tracing::warn!(p999, "t2t p999 elevated");
        }
    }

    // fixed: DrawdownF64 query is `.drawdown()`, not `.value()`.
    let dd = metrics.rate_drawdown.drawdown();
    if dd > policy.rate_drawdown_warn {
        tracing::error!(
            drawdown = dd,
            "msg rate fell off peak — feed unhealthy",
        );
    }
}
```

This handler runs on a timer (fire once per second from a driver)
or off a dedicated "heartbeat" event type. It is **not** on the
hot path — the hot path just collects samples.

---

## 6. The postmortem dumper

When something goes wrong you want the last N thousand samples on
disk. The sample log buffer is drained by a dedicated thread:

```rust
// fixed: raw queue Consumer has `try_claim()`. For a blocking API with a
// timeout, use `nexus_logbuf::channel::spsc::channel()` and call
// `Receiver::recv(Some(timeout))` instead.
fn postmortem_thread(mut rx: nexus_logbuf::spsc::Consumer) {
    use std::io::Write;
    let mut file = std::fs::OpenOptions::new()
        .create(true).append(true).open("latency.bin").unwrap();
    loop {
        match rx.try_claim() {
            Some(claim) => { file.write_all(&claim).ok(); }
            None => {
                if rx.is_disconnected() { break; }
                std::thread::yield_now();
            }
        }
    }
}
```

If the process crashes, the log still contains the last few seconds
of samples. You can decode it offline with a small tool:

```rust
fn decode(path: &std::path::Path) -> Vec<LatencySample> {
    let bytes = std::fs::read(path).unwrap();
    bytemuck::cast_slice::<u8, LatencySample>(&bytes).to_vec()
}
```

---

## 7. Multiple metrics, one handler

Resist the temptation to write one "god" metric that combines T2T +
decision + RTT. Each has a different distribution and a different
bug mode:

- **T2T blows up** → usually the strategy is doing more work per
  event. Look at `decision_p999`.
- **Decision is fine but T2T blows up** → the gateway or decoder is
  the bottleneck. Look at reader task instrumentation.
- **Decision and T2T are fine but RTT blows up** → the exchange
  is slow or the network path degraded. Not your fault, not your
  fix — but you need to know about it.
- **Everything is fine but jitter blows up** → scheduler, OS,
  other tenants. Page-cache pressure is the usual culprit.

Separate percentiles make these diagnosable. One combined metric
hides all four.

---

## 8. Gotchas

- **Don't feed `NaN` or `Inf`.** `PercentileF64::update` returns a
  `DataError` on bad input — respect it. Feeding NaN into a
  smoother can poison the whole stream.
- **`is_primed()` is target-aware.** `p999` needs 1000 samples;
  querying before priming returns `None`. Don't alert on a bare
  `p999 > threshold` without checking `is_primed()`.
- **CUSUM wants a stable reference.** Reset it when you deploy. A
  CUSUM that has been running for six months through ten regimes
  is a random number generator.
- **rdtsc is per-core.** If your loop migrates cores, deltas can go
  negative. Pin the loop to a physical core (`taskset`).
- **Don't measure with `Instant::now()` on the hot path.** It's
  20-30ns per call; at low nanoseconds-per-event that dominates.
  Use `rdtsc` + startup calibration for anything microsecond-sensitive.

---

## Further reading

- `nexus-stats/docs/` — full algorithm catalog
- `nexus-stats/docs/reference/performance.md` — stats cycle counts and methodology
- `nexus-logbuf/docs/` — claim API, skip markers
- [benchmarking.md](./benchmarking.md) — same ideas applied to
  microbenchmarking rather than live monitoring
