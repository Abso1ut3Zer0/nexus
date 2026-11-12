# Parameter Tuning Guide

How to choose alpha, slack, threshold, and other parameters.

## EMA Alpha / Span

**Start with span, not alpha.** Span is how many samples the EMA
"remembers." Alpha is the math parameter.

| Span | Alpha | Effective memory | Use when |
|------|-------|-----------------|----------|
| 5 | 0.33 | ~5 samples | Very reactive (HFT, frame timing) |
| 20 | 0.095 | ~20 samples | Balanced (general monitoring) |
| 50 | 0.039 | ~50 samples | Smooth (dashboard display) |
| 200 | 0.010 | ~200 samples | Very smooth (capacity planning) |

**Rule of thumb:** span = how many samples of "normal" behavior you want
to average over. If normal behavior varies over ~20 samples, use span=20.

## CUSUM Slack and Threshold

**Slack (k):** Half the minimum shift you want to detect.
- Want to detect a 10μs shift? Set slack = 5μs.
- Smaller slack = more sensitive = more false alarms.

**Threshold (h):** How much accumulated evidence before alerting.
- Lower = faster detection, more false alarms.
- Higher = slower detection, fewer false alarms.

**Starting point:** For a shift of size δ:
- slack = δ/2
- threshold = 4 × σ (where σ is the standard deviation of normal data)

This gives ARL₀ ≈ 1000 (one false alarm per ~1000 samples) and
ARL₁ ≈ 10-15 (detects the shift within ~15 samples).

## Kalman Process Noise (Q) and Measurement Noise (R)

**Q (process noise):** How much the true value changes per sample.
- High Q → filter is reactive (trusts measurements)
- Low Q → filter is smooth (trusts its model)

**R (measurement noise):** How noisy your measurements are.
- High R → filter ignores noisy measurements
- Low R → filter trusts measurements closely

**Q/R ratio is what matters:**
- Q/R = 1 → balanced
- Q/R > 1 → very reactive (almost no filtering)
- Q/R < 0.01 → very smooth (heavy filtering)

**Practical approach:** Set R from measurement variance (you can estimate
this from Welford). Set Q to control how reactive you want the filter.

## AdaptiveThreshold Z-Threshold

| z-threshold | What it catches | False positive rate (normal data) |
|-------------|----------------|----------------------------------|
| 2.0 | ~5% of normal data | High — too noisy for alerting |
| 3.0 | ~0.3% | Good default for monitoring |
| 3.5 | ~0.05% | Conservative |
| 5.0 | ~0.00006% | Almost never — for outlier rejection |

## Liveness Deadline

**`deadline_multiple(n)`:** How many smoothed intervals of silence
before declaring dead.
- n = 2-3 → very aggressive (false alarms on jitter)
- n = 5 → balanced default
- n = 10 → conservative (tolerates long pauses)

**`deadline_absolute(t)`:** Fixed timeout regardless of rate.
Use when the expected rate varies too much for a multiple to work.

Both may be set; a gap is dead when it exceeds either. A multiple plus a
generous absolute is the usual pairing: adaptive in steady state, with a
hard ceiling if the source slows to a crawl.

## General Advice

1. **Start with defaults, then tune.** Most builders have sensible defaults.
2. **Use `min_samples` generously.** Better to miss the first few anomalies
   than to false-alarm during warmup.
3. **Monitor the monitors.** Track false positive rate. If it's too high,
   increase threshold/slack. If detection is too slow, decrease.
4. **Different parameters for different instruments/sources.** A volatile
   crypto feed needs different CUSUM slack than a stable bond feed.
