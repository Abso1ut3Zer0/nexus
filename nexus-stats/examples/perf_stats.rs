//! Cycles-per-update benchmark for all nexus-stats primitives.
//!
//! Batches 64 updates per measurement to amortize rdtsc overhead (~20 cycles).
//!
//! Usage:
//!   cargo build --release --example perf_stats
//!   taskset -c 0 ./target/release/examples/perf_stats

use std::hint::black_box;

use nexus_stats::monitoring::{PollSaturation, SojournSaturation};

use nexus_stats::{
    control::{
        BoolWindow, DeadBand, Debounce, FirstDiff, Hysteresis, LevelCrossing, PeakDetector,
        SecondDiff,
    },
    detection::{
        AdaptiveThreshold, Adwin, Cusum, Mosum, MultiGate, PageHinkley, RobustZScore,
        ShiryaevRoberts, TrendAlert,
    },
    estimation::{
        BetaBinomial, Decision, GammaPoisson, Kalman2d, Kalman3d, SprtBernoulli, SprtGaussian,
    },
    frequency::TopK,
    learning::{
        AdaGrad, Adam, EpsilonGreedy, Exp3, LmsFilter, NlmsFilter, OnlineGd, OnlineKMeans,
        RlsFilter, ThompsonBeta, ThompsonGamma, Ucb1,
    },
    monitoring::{
        CoDel, Drawdown, ErrorRate, EventRate, HawkesIntensity, Jitter, Liveness, MaxGauge,
        PeakHold, RunningMax, RunningMin, WindowedMax, WindowedMin,
    },
    regression::{
        EwLinearRegression, EwPolynomialRegression, ExponentialRegression, LinearRegression,
        LogarithmicRegression, LogisticRegression, PolynomialRegression, PowerRegression,
    },
    signal::{Autocorrelation, CrossCorrelation, Entropy, PredictiveInfoBound, TransferEntropy},
    smoothing::{AsymEma, Ema, Holt, Kalman1d, Kama, Slew, Spring, WindowedMedian},
    statistics::{
        BipowerVariation, Covariance, EwmaVar, HarmonicMean, Moments, RollSpread, TwoScaleRv,
        Welford,
    },
};

// ============================================================================
// Timing
// ============================================================================

#[inline(always)]
fn rdtsc_start() -> u64 {
    // SAFETY: x86_64 intrinsics for serialized timestamp counter read.
    // lfence ensures all prior instructions complete before reading rdtsc.
    unsafe {
        std::arch::x86_64::_mm_lfence();
        std::arch::x86_64::_rdtsc()
    }
}

#[inline(always)]
fn rdtsc_end() -> u64 {
    // SAFETY: rdtscp serializes on the read side (waits for prior instructions).
    // Trailing lfence prevents subsequent instructions from reordering before the read.
    unsafe {
        let mut aux = 0u32;
        let tsc = std::arch::x86_64::__rdtscp(&raw mut aux);
        std::arch::x86_64::_mm_lfence();
        tsc
    }
}

fn percentile(sorted: &[u64], p: f64) -> u64 {
    let idx = ((sorted.len() as f64) * p / 100.0) as usize;
    sorted[idx.min(sorted.len() - 1)]
}

fn print_row(label: &str, samples: &mut [u64]) {
    samples.sort_unstable();
    println!(
        "  {:<34} {:>6} {:>6} {:>6} {:>7} {:>7}",
        label,
        percentile(samples, 50.0),
        percentile(samples, 90.0),
        percentile(samples, 99.0),
        percentile(samples, 99.9),
        samples[samples.len() - 1],
    );
}

fn print_header() {
    println!(
        "  {:<34} {:>6} {:>6} {:>6} {:>7} {:>7}",
        "(cycles/op)", "p50", "p90", "p99", "p99.9", "max"
    );
}

fn section(name: &str) {
    println!("\n  --- {name} ---");
}

const SAMPLES: usize = 100_000;
const WARMUP: usize = 10_000;
const BATCH: u64 = 64;

#[inline(always)]
fn next_val(state: &mut u64) -> u64 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    *state
}

#[inline(always)]
fn next_unit(state: &mut u64) -> f64 {
    (next_val(state) >> 33) as f64 / (1u64 << 31) as f64
}

/// Sawtooth 0.0..128.0 in steps of 0.5: a slowly varying signal, so threshold
/// types take the predictable branch, as a monitored signal does in practice.
#[inline(always)]
fn next_saw(state: &mut u64) -> f64 {
    *state += 1;
    (*state & 0xFF) as f64 * 0.5
}

// ============================================================================
// Phase 1: CUSUM, EMA, Welford
// ============================================================================

fn bench_cusum_f64(samples: &mut [u64]) {
    let mut cusum = Cusum::builder(100.0)
        .slack(5.0)
        .threshold(1e18)
        .build()
        .unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let _ = cusum.update(90.0 + (next_val(&mut rng) % 20) as f64);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = cusum.update(90.0 + (next_val(&mut rng) % 20) as f64);
        }
        let end = rdtsc_end();
        black_box(cusum.upper());
        *s = (end - start) / BATCH;
    }
}

fn bench_ema_f64(samples: &mut [u64]) {
    let mut ema = Ema::builder().alpha(0.1).build().unwrap();
    let mut rng = 12345u64;
    let _ = ema.update(100.0);
    for _ in 0..WARMUP {
        let _ = ema.update(90.0 + (next_val(&mut rng) % 20) as f64);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = ema.update(90.0 + (next_val(&mut rng) % 20) as f64);
        }
        let end = rdtsc_end();
        black_box(ema.value());
        *s = (end - start) / BATCH;
    }
}

fn bench_welford_f64(samples: &mut [u64]) {
    let mut w = Welford::new();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        w.update(90.0 + (next_val(&mut rng) % 20) as f64).unwrap();
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            w.update(black_box(90.0 + (next_val(&mut rng) % 20) as f64))
                .unwrap();
        }
        let end = rdtsc_end();
        black_box(w.mean());
        *s = (end - start) / BATCH;
    }
}

// ============================================================================
// Phase 2: Drawdown, Windowed Min/Max, EWMA Variance
// ============================================================================

fn bench_drawdown_f64(samples: &mut [u64]) {
    let mut dd = Drawdown::<f64>::new();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let _ = dd.update(90.0 + (next_val(&mut rng) % 20) as f64);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = dd.update(90.0 + (next_val(&mut rng) % 20) as f64);
        }
        let end = rdtsc_end();
        black_box(dd.max_drawdown());
        *s = (end - start) / BATCH;
    }
}

fn bench_windowed_max_f64(samples: &mut [u64]) {
    let mut wm = WindowedMax::<f64>::new(1000).unwrap();
    let mut rng = 12345u64;
    for t in 0..WARMUP as u64 {
        let _ = wm.update(t, 90.0 + (next_val(&mut rng) % 20) as f64);
    }
    let mut t = WARMUP as u64;
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = wm.update(t, 90.0 + (next_val(&mut rng) % 20) as f64);
            t += 1;
        }
        let end = rdtsc_end();
        black_box(wm.max());
        *s = (end - start) / BATCH;
    }
}

fn bench_windowed_min_f64(samples: &mut [u64]) {
    let mut wm = WindowedMin::<f64>::new(1000).unwrap();
    let mut rng = 12345u64;
    for t in 0..WARMUP as u64 {
        let _ = wm.update(t, 90.0 + (next_val(&mut rng) % 20) as f64);
    }
    let mut t = WARMUP as u64;
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = wm.update(t, 90.0 + (next_val(&mut rng) % 20) as f64);
            t += 1;
        }
        let end = rdtsc_end();
        black_box(wm.min());
        *s = (end - start) / BATCH;
    }
}

fn bench_ewma_var_f64(samples: &mut [u64]) {
    let mut ev = EwmaVar::builder().alpha(0.1).build().unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let _ = ev.update(90.0 + (next_val(&mut rng) % 20) as f64).unwrap();
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = ev.update(90.0 + (next_val(&mut rng) % 20) as f64).unwrap();
        }
        let end = rdtsc_end();
        black_box(ev.variance());
        *s = (end - start) / BATCH;
    }
}

// ============================================================================
// Phase 3: Liveness, MOSUM
// ============================================================================

fn bench_liveness_u64(samples: &mut [u64]) {
    let mut lv = Liveness::builder()
        .span(7)
        .deadline_multiple(3)
        .build()
        .unwrap();
    let mut rng = 12345u64;
    for i in 0..WARMUP {
        let _ = lv.update(i as u64 * 10 + next_val(&mut rng) % 5);
    }
    let mut t = WARMUP as u64 * 10;
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            t += 10 + next_val(&mut rng) % 5;
            let _ = black_box(lv.update(t));
        }
        let end = rdtsc_end();
        *s = (end - start) / BATCH;
    }
}

/// Steady working polls (the floor is not pending): the full `on_work` path
/// with a compare against `bound`, the maxima and the counters.
fn bench_poll_saturation_on_work(samples: &mut [u64]) {
    let mut sat = PollSaturation::new(50);
    let mut rng = 12345u64;
    let mut t = 0u64;
    for _ in 0..WARMUP {
        t += 10 + next_val(&mut rng) % 5;
        let _ = sat.on_work(t, 1);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            t += 10 + next_val(&mut rng) % 5;
            let _ = black_box(sat.on_work(t, 1));
        }
        let end = rdtsc_end();
        *s = (end - start) / BATCH;
    }
    black_box(sat.take());
}

/// Mixed load: an empty poll before a message at random, so whether the
/// floor is pending is unpredictable. The regime that punishes a branch.
fn bench_poll_saturation_on_work_mixed(samples: &mut [u64]) {
    let mut sat = PollSaturation::new(50);
    let mut rng = 12345u64;
    let mut t = 0u64;
    for _ in 0..WARMUP {
        if next_val(&mut rng) & 1 == 0 {
            sat.on_idle();
        }
        t += 10;
        let _ = sat.on_work(t, 1);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            if next_val(&mut rng) & 1 == 0 {
                sat.on_idle();
            }
            t += 10;
            let _ = black_box(sat.on_work(t, 1));
        }
        let end = rdtsc_end();
        *s = (end - start) / BATCH;
    }
    black_box(sat.take());
}

/// Sojourns around a floor of ~10 with an unpredictable minority over the
/// budget of 50, so the over-budget compare cannot be predicted.
fn bench_sojourn_saturation_update(samples: &mut [u64]) {
    let mut sat = SojournSaturation::new(50);
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let x = next_val(&mut rng);
        sat.update(if x.is_multiple_of(4) { 100 } else { 10 } + (x % 5) as i64);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let x = next_val(&mut rng);
            sat.update(if x.is_multiple_of(4) { 100 } else { 10 } + (x % 5) as i64);
        }
        let end = rdtsc_end();
        *s = (end - start) / BATCH;
    }
    black_box(sat.take());
}

/// The idle spin: one flag store, no clock.
fn bench_poll_saturation_on_idle(samples: &mut [u64]) {
    let mut sat = PollSaturation::new(50);
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            black_box(&mut sat).on_idle();
        }
        let end = rdtsc_end();
        *s = (end - start) / BATCH;
    }
    black_box(sat.take());
}

fn bench_mosum_f64(samples: &mut [u64]) {
    let mut mosum = Mosum::builder(100.0)
        .window_size(64)
        .threshold(1e18)
        .build()
        .unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let _ = mosum.update(90.0 + (next_val(&mut rng) % 20) as f64);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = mosum.update(90.0 + (next_val(&mut rng) % 20) as f64);
        }
        let end = rdtsc_end();
        black_box(mosum.sum());
        *s = (end - start) / BATCH;
    }
}

// ============================================================================
// Phase 4: Covariance, Holt's, Shiryaev-Roberts, TopK
// ============================================================================

fn bench_covariance_f64(samples: &mut [u64]) {
    let mut cov = Covariance::new();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let x = 90.0 + (next_val(&mut rng) % 20) as f64;
        let y = x * 2.0 + (next_val(&mut rng) % 5) as f64;
        cov.update(x, y).unwrap();
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let x = 90.0 + (next_val(&mut rng) % 20) as f64;
            let y = x * 2.0 + (next_val(&mut rng) % 5) as f64;
            cov.update(x, y).unwrap();
        }
        let end = rdtsc_end();
        black_box(cov.correlation());
        *s = (end - start) / BATCH;
    }
}

fn bench_holt_f64(samples: &mut [u64]) {
    let mut h = Holt::builder().alpha(0.3).beta(0.1).build().unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let _ = h.update(90.0 + (next_val(&mut rng) % 20) as f64);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = h.update(90.0 + (next_val(&mut rng) % 20) as f64);
        }
        let end = rdtsc_end();
        black_box(h.level());
        *s = (end - start) / BATCH;
    }
}

fn bench_shiryaev_roberts(samples: &mut [u64]) {
    let mut sr = ShiryaevRoberts::builder()
        .pre_change_mean(100.0)
        .post_change_mean(110.0)
        .variance(25.0)
        .threshold(1e18)
        .build()
        .unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let _ = sr.update(90.0 + (next_val(&mut rng) % 20) as f64);
        if sr.statistic() > 1e15 {
            sr.reset();
        }
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = sr.update(90.0 + (next_val(&mut rng) % 20) as f64);
            if sr.statistic() > 1e15 {
                sr.reset();
            }
        }
        let end = rdtsc_end();
        black_box(sr.statistic());
        *s = (end - start) / BATCH;
    }
}

fn bench_topk(samples: &mut [u64]) {
    let mut tk: TopK<u64, 16> = TopK::new();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        tk.update(next_val(&mut rng) % 100);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            tk.update(next_val(&mut rng) % 100);
        }
        let end = rdtsc_end();
        black_box(tk.total());
        *s = (end - start) / BATCH;
    }
}

// ============================================================================
// New types: RunningMin/Max, EventRate, CoDel
// ============================================================================

fn bench_running_min_f64(samples: &mut [u64]) {
    let mut rm = RunningMin::<f64>::new();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let _ = rm.update(90.0 + (next_val(&mut rng) % 20) as f64);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = rm.update(90.0 + (next_val(&mut rng) % 20) as f64);
        }
        let end = rdtsc_end();
        black_box(rm.min());
        *s = (end - start) / BATCH;
    }
}

fn bench_running_max_f64(samples: &mut [u64]) {
    let mut rm = RunningMax::<f64>::new();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let _ = rm.update(90.0 + (next_val(&mut rng) % 20) as f64);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = rm.update(90.0 + (next_val(&mut rng) % 20) as f64);
        }
        let end = rdtsc_end();
        black_box(rm.max());
        *s = (end - start) / BATCH;
    }
}

fn bench_event_rate_u64(samples: &mut [u64]) {
    let mut er = EventRate::builder().span(15).build().unwrap();
    let mut rng = 12345u64;
    let mut t = 0u64;
    for _ in 0..WARMUP {
        t += 10 + next_val(&mut rng) % 5;
        er.update(t);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            t += 10 + next_val(&mut rng) % 5;
            er.update(t);
        }
        let end = rdtsc_end();
        black_box(er.rate());
        *s = (end - start) / BATCH;
    }
}

fn bench_codel_i64(samples: &mut [u64]) {
    let mut qd = CoDel::<i64>::builder()
        .target(100)
        .window(1000)
        .build()
        .unwrap();
    let mut rng = 12345u64;
    for t in 0..WARMUP as u64 {
        let _ = qd.update(t, 50 + (next_val(&mut rng) % 100) as i64);
    }
    let mut t = WARMUP as u64;
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = qd.update(t, 50 + (next_val(&mut rng) % 100) as i64);
            t += 1;
        }
        let end = rdtsc_end();
        black_box(qd.is_elevated());
        *s = (end - start) / BATCH;
    }
}

// ============================================================================
// Phase 5: Anomaly Detection
// ============================================================================

fn bench_multi_gate_f64(samples: &mut [u64]) {
    let mut mg = MultiGate::builder()
        .alpha(0.1)
        .hard_limit(0.5)
        .suspect_z(5.0)
        .min_samples(5)
        .build()
        .unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let _ = mg.update(90.0 + (next_val(&mut rng) % 20) as f64);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = mg.update(90.0 + (next_val(&mut rng) % 20) as f64);
        }
        let end = rdtsc_end();
        black_box(mg.ema_abs_return());
        *s = (end - start) / BATCH;
    }
}

fn bench_windowed_median_f64(samples: &mut [u64]) {
    let mut wm = WindowedMedian::<f64>::new(32);
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let _ = wm.update(90.0 + (next_val(&mut rng) % 20) as f64);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = wm.update(90.0 + (next_val(&mut rng) % 20) as f64);
        }
        let end = rdtsc_end();
        black_box(wm.median());
        *s = (end - start) / BATCH;
    }
}

fn bench_robust_z_f64(samples: &mut [u64]) {
    let mut rz = RobustZScore::<f64>::builder()
        .alpha(0.1)
        .reject_threshold(10.0)
        .min_samples(5)
        .build()
        .unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let _ = rz.update(90.0 + (next_val(&mut rng) % 20) as f64);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = rz.update(90.0 + (next_val(&mut rng) % 20) as f64);
        }
        let end = rdtsc_end();
        black_box(rz.z_score());
        *s = (end - start) / BATCH;
    }
}

// ============================================================================
// Phase 6: Signal Processing
// ============================================================================

fn bench_spring_f64(samples: &mut [u64]) {
    let mut sp = Spring::new(0.5).unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let _ = sp.update(90.0 + (next_val(&mut rng) % 20) as f64, 0.016);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = sp.update(90.0 + (next_val(&mut rng) % 20) as f64, 0.016);
        }
        let end = rdtsc_end();
        black_box(sp.value());
        *s = (end - start) / BATCH;
    }
}

fn bench_peak_hold_f64(samples: &mut [u64]) {
    let mut ph = PeakHold::<f64>::builder()
        .decay_rate(0.99)
        .hold_samples(10)
        .build()
        .unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let _ = ph.update(90.0 + (next_val(&mut rng) % 20) as f64);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = ph.update(90.0 + (next_val(&mut rng) % 20) as f64);
        }
        let end = rdtsc_end();
        black_box(ph.peak());
        *s = (end - start) / BATCH;
    }
}

fn bench_asym_ema_f64(samples: &mut [u64]) {
    let mut ae = AsymEma::builder()
        .alpha_up(0.9)
        .alpha_down(0.1)
        .build()
        .unwrap();
    let mut rng = 12345u64;
    let _ = ae.update(100.0);
    for _ in 0..WARMUP {
        let _ = ae.update(90.0 + (next_val(&mut rng) % 20) as f64);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = ae.update(90.0 + (next_val(&mut rng) % 20) as f64);
        }
        let end = rdtsc_end();
        black_box(ae.value());
        *s = (end - start) / BATCH;
    }
}

fn bench_kama_f64(samples: &mut [u64]) {
    let mut kama = Kama::builder().window_size(10).build().unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let _ = kama.update(90.0 + (next_val(&mut rng) % 20) as f64);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = kama.update(90.0 + (next_val(&mut rng) % 20) as f64);
        }
        let end = rdtsc_end();
        black_box(kama.value());
        *s = (end - start) / BATCH;
    }
}

fn bench_kalman1d_f64(samples: &mut [u64]) {
    let mut kf = Kalman1d::builder()
        .process_noise(0.01)
        .measurement_noise(1.0)
        .build()
        .unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let _ = kf.update(90.0 + (next_val(&mut rng) % 20) as f64);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = kf.update(90.0 + (next_val(&mut rng) % 20) as f64);
        }
        let end = rdtsc_end();
        black_box(kf.position());
        *s = (end - start) / BATCH;
    }
}

// ============================================================================
// Phase 7: Utilities
// ============================================================================

fn bench_slew_f64(samples: &mut [u64]) {
    let mut sl = Slew::<f64>::new(5.0).unwrap();
    let mut rng = 12345u64;
    let _ = sl.update(100.0);
    for _ in 0..WARMUP {
        let _ = sl.update(90.0 + (next_val(&mut rng) % 20) as f64);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = sl.update(90.0 + (next_val(&mut rng) % 20) as f64);
        }
        let end = rdtsc_end();
        black_box(sl.value());
        *s = (end - start) / BATCH;
    }
}

fn bench_bool_window(samples: &mut [u64]) {
    let mut bw = BoolWindow::new(64).unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        bw.update(!next_val(&mut rng).is_multiple_of(10));
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            bw.update(!next_val(&mut rng).is_multiple_of(10));
        }
        let end = rdtsc_end();
        black_box(bw.failure_rate());
        *s = (end - start) / BATCH;
    }
}

fn bench_hysteresis_f64(samples: &mut [u64]) {
    let mut hy = Hysteresis::<f64>::new(40.0, 60.0).unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let _ = hy.update(next_saw(&mut rng));
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = hy.update(next_saw(&mut rng));
        }
        let end = rdtsc_end();
        black_box(hy.state());
        *s = (end - start) / BATCH;
    }
}

// ============================================================================
// Phase 8: Statistics & Signal Analysis (new types)
// ============================================================================

fn bench_moments_f64(samples: &mut [u64]) {
    let mut m = Moments::new();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        m.update(90.0 + (next_val(&mut rng) % 20) as f64).unwrap();
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            m.update(90.0 + (next_val(&mut rng) % 20) as f64).unwrap();
        }
        let end = rdtsc_end();
        black_box(m.kurtosis());
        *s = (end - start) / BATCH;
    }
}

fn bench_autocorrelation_f64(samples: &mut [u64]) {
    let mut ac = Autocorrelation::builder().lag(1).build().unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let _ = ac.update(90.0 + (next_val(&mut rng) % 20) as f64);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = ac.update(90.0 + (next_val(&mut rng) % 20) as f64);
        }
        let end = rdtsc_end();
        black_box(ac.correlation());
        *s = (end - start) / BATCH;
    }
}

fn bench_cross_correlation_f64(samples: &mut [u64]) {
    let mut cc = CrossCorrelation::builder().lag(10).build().unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let x = 90.0 + (next_val(&mut rng) % 20) as f64;
        let y = x * 2.0 + (next_val(&mut rng) % 5) as f64;
        let _ = cc.update(x, y);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let x = 90.0 + (next_val(&mut rng) % 20) as f64;
            let y = x * 2.0 + (next_val(&mut rng) % 5) as f64;
            let _ = cc.update(x, y);
        }
        let end = rdtsc_end();
        black_box(cc.correlation(0));
        *s = (end - start) / BATCH;
    }
}

fn bench_entropy_f64(samples: &mut [u64]) {
    let mut e = Entropy::builder().bins(8).build().unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        e.update((next_val(&mut rng) % 8) as usize);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            e.update((next_val(&mut rng) % 8) as usize);
        }
        let end = rdtsc_end();
        black_box(e.entropy());
        *s = (end - start) / BATCH;
    }
}

fn bench_transfer_entropy_f64(samples: &mut [u64]) {
    let mut te = TransferEntropy::builder().bins(8).lag(1).build().unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let x = (next_val(&mut rng) % 8) as usize;
        let y = (next_val(&mut rng) % 8) as usize;
        te.update(x, y);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let x = (next_val(&mut rng) % 8) as usize;
            let y = (next_val(&mut rng) % 8) as usize;
            te.update(x, y);
        }
        let end = rdtsc_end();
        black_box(te.count());
        *s = (end - start) / BATCH;
    }
}

// ============================================================================
// Main
// ============================================================================

// ============================================================================
// Phase 9: remaining README rows (7.0 sweep)
// ============================================================================

fn bench_harmonic_mean_f64(samples: &mut [u64]) {
    let mut h = HarmonicMean::new();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        h.update(1.0 + (next_val(&mut rng) % 100) as f64).unwrap();
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            h.update(black_box(1.0 + (next_val(&mut rng) % 100) as f64))
                .unwrap();
        }
        let end = rdtsc_end();
        black_box(h.mean());
        *s = (end - start) / BATCH;
    }
}

fn bench_jitter_f64(samples: &mut [u64]) {
    let mut j = Jitter::<f64>::builder().span(20).build().unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let _ = j.update(90.0 + (next_val(&mut rng) % 20) as f64);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = j.update(black_box(90.0 + (next_val(&mut rng) % 20) as f64));
        }
        let end = rdtsc_end();
        black_box(j.jitter());
        *s = (end - start) / BATCH;
    }
}

fn bench_trend_alert_f64(samples: &mut [u64]) {
    let mut t = TrendAlert::builder()
        .alpha(0.3)
        .beta(0.1)
        .trend_threshold(1e18)
        .build()
        .unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let _ = t.update(90.0 + (next_val(&mut rng) % 20) as f64);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = t.update(black_box(90.0 + (next_val(&mut rng) % 20) as f64));
        }
        let end = rdtsc_end();
        black_box(t.level());
        *s = (end - start) / BATCH;
    }
}

fn bench_adaptive_threshold_f64(samples: &mut [u64]) {
    let mut a = AdaptiveThreshold::builder()
        .span(50)
        .z_threshold(1e9)
        .build()
        .unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let _ = a.update(90.0 + (next_val(&mut rng) % 20) as f64);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = a.update(black_box(90.0 + (next_val(&mut rng) % 20) as f64));
        }
        let end = rdtsc_end();
        black_box(a.baseline());
        *s = (end - start) / BATCH;
    }
}

fn bench_page_hinkley_f64(samples: &mut [u64]) {
    let mut p = PageHinkley::builder()
        .alpha(0.01)
        .threshold(1e18)
        .build()
        .unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let _ = p.update(90.0 + (next_val(&mut rng) % 20) as f64);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = p.update(black_box(90.0 + (next_val(&mut rng) % 20) as f64));
        }
        let end = rdtsc_end();
        black_box(p.count());
        *s = (end - start) / BATCH;
    }
}

fn bench_adwin_f64(samples: &mut [u64]) {
    let mut a = Adwin::builder().delta(0.002).build().unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let _ = a.update(90.0 + (next_val(&mut rng) % 20) as f64);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = a.update(black_box(90.0 + (next_val(&mut rng) % 20) as f64));
        }
        let end = rdtsc_end();
        black_box(a.mean());
        *s = (end - start) / BATCH;
    }
}

fn bench_dead_band_f64(samples: &mut [u64]) {
    let mut d = DeadBand::<f64>::new(5.0).unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let _ = d.update(next_saw(&mut rng));
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = d.update(black_box(next_saw(&mut rng)));
        }
        let end = rdtsc_end();
        black_box(&d);
        *s = (end - start) / BATCH;
    }
}

fn bench_level_crossing_f64(samples: &mut [u64]) {
    let mut l = LevelCrossing::<f64>::new(100.0);
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let _ = l.update(next_saw(&mut rng));
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = l.update(black_box(next_saw(&mut rng)));
        }
        let end = rdtsc_end();
        black_box(&l);
        *s = (end - start) / BATCH;
    }
}

fn bench_first_diff_f64(samples: &mut [u64]) {
    let mut f = FirstDiff::<f64>::new();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let _ = f.update(90.0 + (next_val(&mut rng) % 20) as f64);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = f.update(black_box(90.0 + (next_val(&mut rng) % 20) as f64));
        }
        let end = rdtsc_end();
        black_box(&f);
        *s = (end - start) / BATCH;
    }
}

fn bench_second_diff_f64(samples: &mut [u64]) {
    let mut v = SecondDiff::<f64>::new();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let _ = v.update(90.0 + (next_val(&mut rng) % 20) as f64);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = v.update(black_box(90.0 + (next_val(&mut rng) % 20) as f64));
        }
        let end = rdtsc_end();
        black_box(&v);
        *s = (end - start) / BATCH;
    }
}

fn bench_max_gauge_f64(samples: &mut [u64]) {
    let mut m = MaxGauge::<f64>::new();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        m.update(90.0 + (next_val(&mut rng) % 20) as f64).unwrap();
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            m.update(black_box(90.0 + (next_val(&mut rng) % 20) as f64))
                .unwrap();
        }
        let end = rdtsc_end();
        black_box(m.peek());
        *s = (end - start) / BATCH;
    }
}

fn bench_peak_detector_f64(samples: &mut [u64]) {
    let mut p = PeakDetector::<f64>::new(5.0).unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let _ = p.update(next_saw(&mut rng));
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = p.update(black_box(next_saw(&mut rng)));
        }
        let end = rdtsc_end();
        black_box(p.count());
        *s = (end - start) / BATCH;
    }
}

fn bench_bipower_variation_f64(samples: &mut [u64]) {
    let mut b = BipowerVariation::new();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        b.update(100.0 + (next_val(&mut rng) % 200) as f64 / 100.0)
            .unwrap();
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            b.update(black_box(100.0 + (next_val(&mut rng) % 200) as f64 / 100.0))
                .unwrap();
        }
        let end = rdtsc_end();
        black_box(b.bipower_variation());
        *s = (end - start) / BATCH;
    }
}

fn bench_roll_spread_f64(samples: &mut [u64]) {
    let mut r = RollSpread::builder().alpha(0.05).build().unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        r.update(100.0 + (next_val(&mut rng) % 200) as f64 / 100.0)
            .unwrap();
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            r.update(black_box(100.0 + (next_val(&mut rng) % 200) as f64 / 100.0))
                .unwrap();
        }
        let end = rdtsc_end();
        black_box(r.spread());
        *s = (end - start) / BATCH;
    }
}

fn bench_two_scale_rv_f64(samples: &mut [u64]) {
    let mut t = TwoScaleRv::builder().k(5).build().unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        t.update(100.0 + (next_val(&mut rng) % 200) as f64 / 100.0)
            .unwrap();
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            t.update(black_box(100.0 + (next_val(&mut rng) % 200) as f64 / 100.0))
                .unwrap();
        }
        let end = rdtsc_end();
        black_box(t.realized_variance());
        *s = (end - start) / BATCH;
    }
}

fn bench_linear_regression_f64(samples: &mut [u64]) {
    let mut r = LinearRegression::new();
    let mut rng = 12345u64;
    let mut x = 1.0f64;
    for _ in 0..WARMUP {
        x += 1.0;
        r.update(x, 2.0f64.mul_add(x, (next_val(&mut rng) % 20) as f64))
            .unwrap();
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            x += 1.0;
            r.update(
                black_box(x),
                black_box(2.0f64.mul_add(x, (next_val(&mut rng) % 20) as f64)),
            )
            .unwrap();
        }
        let end = rdtsc_end();
        black_box(r.slope());
        *s = (end - start) / BATCH;
    }
}

fn bench_ew_linear_regression_f64(samples: &mut [u64]) {
    let mut r = EwLinearRegression::builder().alpha(0.01).build().unwrap();
    let mut rng = 12345u64;
    let mut x = 1.0f64;
    for _ in 0..WARMUP {
        x += 1.0;
        r.update(x, 2.0f64.mul_add(x, (next_val(&mut rng) % 20) as f64))
            .unwrap();
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            x += 1.0;
            r.update(
                black_box(x),
                black_box(2.0f64.mul_add(x, (next_val(&mut rng) % 20) as f64)),
            )
            .unwrap();
        }
        let end = rdtsc_end();
        black_box(r.slope());
        *s = (end - start) / BATCH;
    }
}

fn bench_polynomial_regression_f64(samples: &mut [u64]) {
    let mut r = PolynomialRegression::builder().degree(2).build().unwrap();
    let mut rng = 12345u64;
    let mut x = 1.0f64;
    for _ in 0..WARMUP {
        x += 1.0;
        r.update(x, x.mul_add(x, (next_val(&mut rng) % 20) as f64))
            .unwrap();
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            x += 1.0;
            r.update(
                black_box(x),
                black_box(x.mul_add(x, (next_val(&mut rng) % 20) as f64)),
            )
            .unwrap();
        }
        let end = rdtsc_end();
        black_box(r.r_squared());
        *s = (end - start) / BATCH;
    }
}

fn bench_ew_polynomial_regression_f64(samples: &mut [u64]) {
    let mut r = EwPolynomialRegression::builder()
        .degree(2)
        .alpha(0.01)
        .build()
        .unwrap();
    let mut rng = 12345u64;
    let mut x = 1.0f64;
    for _ in 0..WARMUP {
        x += 1.0;
        r.update(x, x.mul_add(x, (next_val(&mut rng) % 20) as f64))
            .unwrap();
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            x += 1.0;
            r.update(
                black_box(x),
                black_box(x.mul_add(x, (next_val(&mut rng) % 20) as f64)),
            )
            .unwrap();
        }
        let end = rdtsc_end();
        black_box(r.r_squared());
        *s = (end - start) / BATCH;
    }
}

fn bench_exponential_regression_f64(samples: &mut [u64]) {
    let mut r = ExponentialRegression::new();
    let mut rng = 12345u64;
    let mut x = 1.0f64;
    for _ in 0..WARMUP {
        x += 1.0;
        r.update(x, 1.0 + (next_val(&mut rng) % 20) as f64).unwrap();
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            x += 1.0;
            r.update(
                black_box(x),
                black_box(1.0 + (next_val(&mut rng) % 20) as f64),
            )
            .unwrap();
        }
        let end = rdtsc_end();
        black_box(r.predict(1.0));
        *s = (end - start) / BATCH;
    }
}

fn bench_logarithmic_regression_f64(samples: &mut [u64]) {
    let mut r = LogarithmicRegression::new();
    let mut rng = 12345u64;
    let mut x = 1.0f64;
    for _ in 0..WARMUP {
        x += 1.0;
        r.update(x, 1.0 + (next_val(&mut rng) % 20) as f64).unwrap();
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            x += 1.0;
            r.update(
                black_box(x),
                black_box(1.0 + (next_val(&mut rng) % 20) as f64),
            )
            .unwrap();
        }
        let end = rdtsc_end();
        black_box(r.predict(1.0));
        *s = (end - start) / BATCH;
    }
}

fn bench_power_regression_f64(samples: &mut [u64]) {
    let mut r = PowerRegression::new();
    let mut rng = 12345u64;
    let mut x = 1.0f64;
    for _ in 0..WARMUP {
        x += 1.0;
        r.update(x, 1.0 + (next_val(&mut rng) % 20) as f64).unwrap();
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            x += 1.0;
            r.update(
                black_box(x),
                black_box(1.0 + (next_val(&mut rng) % 20) as f64),
            )
            .unwrap();
        }
        let end = rdtsc_end();
        black_box(r.predict(1.0));
        *s = (end - start) / BATCH;
    }
}

fn bench_predictive_info_bound_f64(samples: &mut [u64]) {
    let mut p = PredictiveInfoBound::builder()
        .bins(8)
        .x_range(0.0, 1.0)
        .y_range(0.0, 1.0)
        .build()
        .unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        p.update(next_unit(&mut rng), next_unit(&mut rng)).unwrap();
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            p.update(
                black_box(next_unit(&mut rng)),
                black_box(next_unit(&mut rng)),
            )
            .unwrap();
        }
        let end = rdtsc_end();
        black_box(p.mutual_information());
        *s = (end - start) / BATCH;
    }
}

fn bench_error_rate(samples: &mut [u64]) {
    let mut er = ErrorRate::builder()
        .span(100)
        .threshold(0.5)
        .build()
        .unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let _ = er.update(!next_val(&mut rng).is_multiple_of(10));
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = er.update(black_box(!next_val(&mut rng).is_multiple_of(10)));
        }
        let end = rdtsc_end();
        black_box(er.error_rate());
        *s = (end - start) / BATCH;
    }
}

fn bench_debounce(samples: &mut [u64]) {
    let mut d = Debounce::new(5).unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let _ = d.update(!next_val(&mut rng).is_multiple_of(10));
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = black_box(d.update(black_box(!next_val(&mut rng).is_multiple_of(10))));
        }
        let end = rdtsc_end();
        *s = (end - start) / BATCH;
    }
}

fn bench_hawkes_intensity_u64(samples: &mut [u64]) {
    let mut h = HawkesIntensity::builder()
        .mu(0.1)
        .alpha(0.5)
        .beta(1.0)
        .build()
        .unwrap();
    let mut rng = 12345u64;
    let mut t = 0u64;
    for _ in 0..WARMUP {
        t += 10 + next_val(&mut rng) % 5;
        h.update(t);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            t += 10 + next_val(&mut rng) % 5;
            h.update(black_box(t));
        }
        let end = rdtsc_end();
        black_box(h.intensity());
        *s = (end - start) / BATCH;
    }
}

// ============================================================================
// Phase 10: per-page rows (queries, filters, optimizers, estimation)
// ============================================================================

fn bench_kalman2d_predict(samples: &mut [u64]) {
    let mut k = Kalman2d::builder()
        .process_noise([[0.01, 0.0], [0.0, 0.01]])
        .measurement_noise(1.0)
        .build()
        .unwrap();
    for _ in 0..WARMUP {
        k.predict();
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            k.predict();
        }
        let end = rdtsc_end();
        black_box(&k);
        *s = (end - start) / BATCH;
    }
}

fn bench_kalman2d_update(samples: &mut [u64]) {
    let mut k = Kalman2d::builder()
        .process_noise([[0.01, 0.0], [0.0, 0.01]])
        .measurement_noise(1.0)
        .build()
        .unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        k.update(90.0 + (next_val(&mut rng) % 20) as f64, [1.0, 0.0])
            .unwrap();
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            k.update(
                black_box(90.0 + (next_val(&mut rng) % 20) as f64),
                [1.0, 0.0],
            )
            .unwrap();
        }
        let end = rdtsc_end();
        black_box(&k);
        *s = (end - start) / BATCH;
    }
}

fn bench_kalman3d_predict(samples: &mut [u64]) {
    let mut k = Kalman3d::builder()
        .process_noise([[0.01, 0.0, 0.0], [0.0, 0.01, 0.0], [0.0, 0.0, 0.01]])
        .measurement_noise(1.0)
        .build()
        .unwrap();
    for _ in 0..WARMUP {
        k.predict();
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            k.predict();
        }
        let end = rdtsc_end();
        black_box(&k);
        *s = (end - start) / BATCH;
    }
}

fn bench_kalman3d_update(samples: &mut [u64]) {
    let mut k = Kalman3d::builder()
        .process_noise([[0.01, 0.0, 0.0], [0.0, 0.01, 0.0], [0.0, 0.0, 0.01]])
        .measurement_noise(1.0)
        .build()
        .unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        k.update(90.0 + (next_val(&mut rng) % 20) as f64, [1.0, 0.0, 0.0])
            .unwrap();
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            k.update(
                black_box(90.0 + (next_val(&mut rng) % 20) as f64),
                [1.0, 0.0, 0.0],
            )
            .unwrap();
        }
        let end = rdtsc_end();
        black_box(&k);
        *s = (end - start) / BATCH;
    }
}

#[inline(always)]
fn features5(rng: &mut u64) -> [f64; 5] {
    [
        next_unit(rng),
        next_unit(rng),
        next_unit(rng),
        next_unit(rng),
        next_unit(rng),
    ]
}

macro_rules! bench_filter_d5 {
    ($name:ident, $ctor:expr, $target:expr) => {
        fn $name(samples: &mut [u64]) {
            let mut f = $ctor;
            let mut rng = 12345u64;
            for _ in 0..WARMUP {
                let x = features5(&mut rng);
                let _ = f.update(&x, $target(&mut rng));
            }
            for s in samples.iter_mut() {
                let start = rdtsc_start();
                for _ in 0..BATCH {
                    let x = black_box(features5(&mut rng));
                    let _ = f.update(&x, black_box($target(&mut rng)));
                }
                let end = rdtsc_end();
                black_box(&f);
                *s = (end - start) / BATCH;
            }
        }
    };
}

bench_filter_d5!(
    bench_lms_filter_d5,
    LmsFilter::builder()
        .dimensions(5)
        .learning_rate(0.01)
        .build()
        .unwrap(),
    next_unit
);
bench_filter_d5!(
    bench_nlms_filter_d5,
    NlmsFilter::builder()
        .dimensions(5)
        .learning_rate(0.1)
        .build()
        .unwrap(),
    next_unit
);
bench_filter_d5!(
    bench_rls_filter_d5,
    RlsFilter::builder().dimensions(5).build().unwrap(),
    next_unit
);
bench_filter_d5!(
    bench_logistic_regression_d5,
    LogisticRegression::builder()
        .dimensions(5)
        .learning_rate(0.01)
        .build()
        .unwrap(),
    |rng: &mut u64| next_val(rng).is_multiple_of(2)
);

macro_rules! bench_optimizer_d10 {
    ($name:ident, $ctor:expr) => {
        fn $name(samples: &mut [u64]) {
            let mut o = $ctor;
            let mut rng = 12345u64;
            let mut g = [0.0f64; 10];
            for _ in 0..WARMUP {
                for v in &mut g {
                    *v = next_unit(&mut rng) - 0.5;
                }
                o.step(&g).unwrap();
            }
            for s in samples.iter_mut() {
                let start = rdtsc_start();
                for _ in 0..BATCH {
                    for v in &mut g {
                        *v = next_unit(&mut rng) - 0.5;
                    }
                    o.step(black_box(&g)).unwrap();
                }
                let end = rdtsc_end();
                black_box(&o);
                *s = (end - start) / BATCH;
            }
        }
    };
}

bench_optimizer_d10!(
    bench_online_gd_d10,
    OnlineGd::builder()
        .dimensions(10)
        .learning_rate(0.01)
        .build()
        .unwrap()
);
bench_optimizer_d10!(
    bench_adagrad_d10,
    AdaGrad::builder()
        .dimensions(10)
        .learning_rate(0.01)
        .build()
        .unwrap()
);
bench_optimizer_d10!(
    bench_adam_d10,
    Adam::builder()
        .dimensions(10)
        .learning_rate(0.001)
        .build()
        .unwrap()
);

fn bench_moments_merge(samples: &mut [u64]) {
    let mut a = Moments::new();
    let mut b = Moments::new();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        a.update(90.0 + (next_val(&mut rng) % 20) as f64).unwrap();
        b.update(90.0 + (next_val(&mut rng) % 20) as f64).unwrap();
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            a.merge(black_box(&b));
        }
        let end = rdtsc_end();
        black_box(&a);
        *s = (end - start) / BATCH;
    }
}

fn bench_liveness_check(samples: &mut [u64]) {
    let mut lv = Liveness::builder()
        .span(7)
        .deadline_multiple(3)
        .build()
        .unwrap();
    let mut rng = 12345u64;
    let mut t = 0u64;
    for _ in 0..WARMUP {
        t += 10 + next_val(&mut rng) % 5;
        let _ = lv.update(t);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            t += 1;
            let _ = black_box(lv.check(black_box(t)));
        }
        let end = rdtsc_end();
        *s = (end - start) / BATCH;
    }
}

fn bench_max_gauge_update_take(samples: &mut [u64]) {
    let mut g = MaxGauge::<f64>::new();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        g.update(90.0 + (next_val(&mut rng) % 20) as f64).unwrap();
        let _ = g.take();
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            g.update(black_box(90.0 + (next_val(&mut rng) % 20) as f64))
                .unwrap();
            let _ = black_box(g.take());
        }
        let end = rdtsc_end();
        *s = (end - start) / BATCH;
    }
}

fn bench_sprt_bernoulli(samples: &mut [u64]) {
    let mut t = SprtBernoulli::builder()
        .null_rate(0.5)
        .alt_rate(0.6)
        .alpha(0.05)
        .beta(0.1)
        .build()
        .unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        if t.update(next_val(&mut rng) % 100 < 55) != Decision::Continue {
            t.reset();
        }
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            if t.update(black_box(next_val(&mut rng) % 100 < 55)) != Decision::Continue {
                t.reset();
            }
        }
        let end = rdtsc_end();
        black_box(t.log_likelihood_ratio());
        *s = (end - start) / BATCH;
    }
}

fn bench_sprt_gaussian(samples: &mut [u64]) {
    let mut t = SprtGaussian::builder()
        .null_mean(100.0)
        .alt_mean(110.0)
        .variance(25.0)
        .alpha(0.05)
        .beta(0.1)
        .build()
        .unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        if t.update(95.0 + (next_val(&mut rng) % 20) as f64).unwrap() != Decision::Continue {
            t.reset();
        }
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            if t.update(black_box(95.0 + (next_val(&mut rng) % 20) as f64))
                .unwrap()
                != Decision::Continue
            {
                t.reset();
            }
        }
        let end = rdtsc_end();
        black_box(t.log_likelihood_ratio());
        *s = (end - start) / BATCH;
    }
}

fn bench_beta_binomial_update(samples: &mut [u64]) {
    let mut b = BetaBinomial::new();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        b.update(next_val(&mut rng) % 100 < 70);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            b.update(black_box(next_val(&mut rng) % 100 < 70));
        }
        let end = rdtsc_end();
        black_box(b.mean());
        *s = (end - start) / BATCH;
    }
}

fn bench_beta_binomial_queries(samples: &mut [u64], interval: bool) {
    let mut b = BetaBinomial::new();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        b.update(next_val(&mut rng) % 100 < 70);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let bb = black_box(&b);
            if interval {
                black_box(bb.credible_interval(0.95));
            } else {
                black_box(bb.mean());
            }
        }
        let end = rdtsc_end();
        *s = (end - start) / BATCH;
    }
}

fn bench_gamma_poisson_update(samples: &mut [u64]) {
    let mut g = GammaPoisson::new();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        g.update(next_val(&mut rng) % 10, 1.0).unwrap();
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            g.update(black_box(next_val(&mut rng) % 10), 1.0).unwrap();
        }
        let end = rdtsc_end();
        black_box(g.rate());
        *s = (end - start) / BATCH;
    }
}

fn bench_polynomial_update(samples: &mut [u64], degree: usize) {
    let mut r = PolynomialRegression::builder()
        .degree(degree)
        .build()
        .unwrap();
    let mut rng = 12345u64;
    let mut x = 1.0f64;
    for _ in 0..WARMUP {
        x += 1.0;
        r.update(x, x.mul_add(x, (next_val(&mut rng) % 20) as f64))
            .unwrap();
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            x += 1.0;
            r.update(
                black_box(x),
                black_box(x.mul_add(x, (next_val(&mut rng) % 20) as f64)),
            )
            .unwrap();
        }
        let end = rdtsc_end();
        black_box(r.r_squared());
        *s = (end - start) / BATCH;
    }
}

fn bench_polynomial_query(samples: &mut [u64], degree: usize, predict: bool) {
    let mut r = PolynomialRegression::builder()
        .degree(degree)
        .build()
        .unwrap();
    let mut rng = 12345u64;
    let mut x = 1.0f64;
    for _ in 0..WARMUP {
        x += 1.0;
        r.update(x, x.mul_add(x, (next_val(&mut rng) % 20) as f64))
            .unwrap();
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let rr = black_box(&r);
            if predict {
                black_box(rr.predict(black_box(x)));
            } else {
                black_box(rr.coefficients());
            }
        }
        let end = rdtsc_end();
        *s = (end - start) / BATCH;
    }
}

// ============================================================================
// Phase 11: query costs (state warmed once, then the accessor in the loop)
// ============================================================================

fn bench_query<T, R>(samples: &mut [u64], state: &T, query: impl Fn(&T) -> R) {
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            black_box(query(black_box(state)));
        }
        let end = rdtsc_end();
        *s = (end - start) / BATCH;
    }
}

fn warm_autocorrelation(lag: usize) -> Autocorrelation {
    let mut ac = Autocorrelation::builder().lag(lag).build().unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let _ = ac.update(90.0 + (next_val(&mut rng) % 20) as f64);
    }
    ac
}

fn warm_covariance() -> Covariance {
    let mut cov = Covariance::new();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let x = 90.0 + (next_val(&mut rng) % 20) as f64;
        let y = x.mul_add(2.0, (next_val(&mut rng) % 5) as f64);
        cov.update(x, y).unwrap();
    }
    cov
}

fn warm_cross_correlation() -> CrossCorrelation {
    let mut cc = CrossCorrelation::builder().lag(10).build().unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let x = 90.0 + (next_val(&mut rng) % 20) as f64;
        let y = x.mul_add(2.0, (next_val(&mut rng) % 5) as f64);
        let _ = cc.update(x, y);
    }
    cc
}

fn warm_entropy() -> Entropy {
    let mut e = Entropy::builder().bins(8).build().unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        e.update((next_val(&mut rng) % 8) as usize);
    }
    e
}

fn warm_transfer_entropy() -> TransferEntropy {
    let mut te = TransferEntropy::builder().bins(8).lag(1).build().unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let x = (next_val(&mut rng) % 8) as usize;
        let y = (next_val(&mut rng) % 8) as usize;
        te.update(x, y);
    }
    te
}

fn warm_linear_regression() -> LinearRegression {
    let mut r = LinearRegression::new();
    let mut rng = 12345u64;
    let mut x = 1.0f64;
    for _ in 0..WARMUP {
        x += 1.0;
        r.update(x, 2.0f64.mul_add(x, (next_val(&mut rng) % 20) as f64))
            .unwrap();
    }
    r
}

fn warm_moments() -> Moments {
    let mut m = Moments::new();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        m.update(90.0 + (next_val(&mut rng) % 20) as f64).unwrap();
    }
    m
}

fn warm_welford() -> Welford {
    let mut w = Welford::new();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        w.update(90.0 + (next_val(&mut rng) % 20) as f64).unwrap();
    }
    w
}

fn bench_autocorrelation_lag10(samples: &mut [u64]) {
    let mut ac = Autocorrelation::builder().lag(10).build().unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let _ = ac.update(90.0 + (next_val(&mut rng) % 20) as f64);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = ac.update(black_box(90.0 + (next_val(&mut rng) % 20) as f64));
        }
        let end = rdtsc_end();
        black_box(ac.correlation());
        *s = (end - start) / BATCH;
    }
}

fn bench_online_kmeans_k3_d5(samples: &mut [u64]) {
    let mut km = OnlineKMeans::builder()
        .clusters(3)
        .dimensions(5)
        .learning_rate(0.05)
        .build()
        .unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let x = features5(&mut rng);
        let _ = km.update(&x);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let x = black_box(features5(&mut rng));
            let _ = black_box(km.update(&x));
        }
        let end = rdtsc_end();
        black_box(&km);
        *s = (end - start) / BATCH;
    }
}

// ============================================================================
// Bandits — parameterized by K
// ============================================================================

const BANDIT_KS: &[usize] = &[2, 5, 10, 25, 50];

fn bench_bandit_select_sweep(samples: &mut [u64]) {
    println!(
        "\n  {:<34} {:>6} {:>6} {:>6} {:>7} {:>7}",
        "(cycles/op)", "p50", "p90", "p99", "p99.9", "max"
    );

    for &k in BANDIT_KS {
        // UCB1
        let mut b = Ucb1::builder().arms(k).build().unwrap();
        let mut rng = 12345u64;
        for _ in 0..(k * 100) {
            let arm = b.select();
            let _ = b.update(arm, next_unit(&mut rng));
        }
        for s in samples.iter_mut() {
            let start = rdtsc_start();
            for _ in 0..BATCH {
                black_box(b.select());
            }
            let end = rdtsc_end();
            *s = (end - start) / BATCH;
        }
        print_row(&format!("Ucb1::select K={k}"), samples);
    }

    println!();
    for &k in BANDIT_KS {
        // ThompsonBeta
        let mut b = ThompsonBeta::builder().arms(k).build().unwrap();
        let mut rng = 12345u64;
        for _ in 0..(k * 100) {
            let arm = b.select(&mut || next_unit(&mut rng));
            let _ = b.update(arm, next_unit(&mut rng));
        }
        for s in samples.iter_mut() {
            let start = rdtsc_start();
            for _ in 0..BATCH {
                black_box(b.select(&mut || next_unit(&mut rng)));
            }
            let end = rdtsc_end();
            *s = (end - start) / BATCH;
        }
        print_row(&format!("ThompsonBeta::select K={k}"), samples);
    }

    println!();
    for &k in BANDIT_KS {
        // ThompsonGamma
        let mut b = ThompsonGamma::builder().arms(k).build().unwrap();
        let mut rng = 12345u64;
        for _ in 0..(k * 100) {
            let arm = b.select(&mut || next_unit(&mut rng));
            let _ = b.update(arm, next_unit(&mut rng) + 0.01);
        }
        for s in samples.iter_mut() {
            let start = rdtsc_start();
            for _ in 0..BATCH {
                black_box(b.select(&mut || next_unit(&mut rng)));
            }
            let end = rdtsc_end();
            *s = (end - start) / BATCH;
        }
        print_row(&format!("ThompsonGamma::select K={k}"), samples);
    }

    println!();
    for &k in BANDIT_KS {
        // EpsilonGreedy
        let mut b = EpsilonGreedy::builder()
            .arms(k)
            .epsilon(0.1)
            .build()
            .unwrap();
        let mut rng = 12345u64;
        for _ in 0..(k * 100) {
            let arm = b.select(&mut || next_unit(&mut rng));
            let _ = b.update(arm, next_unit(&mut rng));
        }
        for s in samples.iter_mut() {
            let start = rdtsc_start();
            for _ in 0..BATCH {
                black_box(b.select(&mut || next_unit(&mut rng)));
            }
            let end = rdtsc_end();
            *s = (end - start) / BATCH;
        }
        print_row(&format!("EpsGreedy::select K={k}"), samples);
    }

    println!();
    for &k in BANDIT_KS {
        // EXP3
        let mut b = Exp3::builder().arms(k).gamma(0.1).build().unwrap();
        let mut rng = 12345u64;
        for _ in 0..(k * 100) {
            let (arm, prob) = b.select(&mut || next_unit(&mut rng));
            let _ = b.update(arm, next_unit(&mut rng), prob);
        }
        for s in samples.iter_mut() {
            let start = rdtsc_start();
            for _ in 0..BATCH {
                black_box(b.select(&mut || next_unit(&mut rng)));
            }
            let end = rdtsc_end();
            *s = (end - start) / BATCH;
        }
        print_row(&format!("Exp3::select K={k}"), samples);
    }
}

fn bench_bandit_update_sweep(samples: &mut [u64]) {
    println!(
        "\n  {:<34} {:>6} {:>6} {:>6} {:>7} {:>7}",
        "(cycles/op)", "p50", "p90", "p99", "p99.9", "max"
    );

    for &k in BANDIT_KS {
        // UCB1 stationary
        let mut b = Ucb1::builder().arms(k).build().unwrap();
        let mut rng = 12345u64;
        for _ in 0..(k * 100) {
            let arm = b.select();
            let _ = b.update(arm, next_unit(&mut rng));
        }
        let mut arm_cycle: usize = 0;
        for s in samples.iter_mut() {
            let start = rdtsc_start();
            for _ in 0..BATCH {
                arm_cycle = (arm_cycle + 1) % k;
                let _ = b.update(black_box(arm_cycle), black_box(next_unit(&mut rng)));
            }
            let end = rdtsc_end();
            *s = (end - start) / BATCH;
        }
        print_row(&format!("Ucb1::update K={k}"), samples);
    }

    println!();
    for &k in BANDIT_KS {
        // UCB1 decay
        let mut b = Ucb1::builder().arms(k).decay(0.99).build().unwrap();
        let mut rng = 12345u64;
        for _ in 0..(k * 100) {
            let arm = b.select();
            let _ = b.update(arm, next_unit(&mut rng));
        }
        let mut arm_cycle: usize = 0;
        for s in samples.iter_mut() {
            let start = rdtsc_start();
            for _ in 0..BATCH {
                arm_cycle = (arm_cycle + 1) % k;
                let _ = b.update(black_box(arm_cycle), black_box(next_unit(&mut rng)));
            }
            let end = rdtsc_end();
            *s = (end - start) / BATCH;
        }
        print_row(&format!("Ucb1::update(decay) K={k}"), samples);
    }
}

fn main() {
    println!("\nnexus-stats benchmark — cycles per operation (batch={BATCH})");
    println!("=========================================================");

    let mut buf = vec![0u64; SAMPLES];

    section("Change Detection");
    print_header();
    bench_cusum_f64(&mut buf);
    print_row("Cusum::update", &mut buf);
    bench_mosum_f64(&mut buf);
    print_row("Mosum(64)::update", &mut buf);
    bench_shiryaev_roberts(&mut buf);
    print_row("ShiryaevRoberts::update", &mut buf);
    bench_page_hinkley_f64(&mut buf);
    print_row("PageHinkley::update", &mut buf);
    bench_adwin_f64(&mut buf);
    print_row("Adwin::update", &mut buf);
    bench_adaptive_threshold_f64(&mut buf);
    print_row("AdaptiveThreshold::update", &mut buf);

    section("Smoothing");
    print_header();
    bench_ema_f64(&mut buf);
    print_row("Ema::update", &mut buf);
    bench_holt_f64(&mut buf);
    print_row("Holt::update", &mut buf);

    section("Variance & Correlation");
    print_header();
    bench_welford_f64(&mut buf);
    print_row("Welford::update", &mut buf);
    bench_ewma_var_f64(&mut buf);
    print_row("EwmaVar::update", &mut buf);
    bench_covariance_f64(&mut buf);
    print_row("Covariance::update", &mut buf);

    section("Monitoring");
    print_header();
    bench_drawdown_f64(&mut buf);
    print_row("Drawdown::<f64>::update", &mut buf);
    bench_windowed_max_f64(&mut buf);
    print_row("WindowedMax::<f64>::update", &mut buf);
    bench_windowed_min_f64(&mut buf);
    print_row("WindowedMin::<f64>::update", &mut buf);
    bench_poll_saturation_on_work(&mut buf);
    print_row("PollSaturation::on_work", &mut buf);
    bench_poll_saturation_on_work_mixed(&mut buf);
    print_row("PollSaturation::on_work (mixed)", &mut buf);
    bench_poll_saturation_on_idle(&mut buf);
    print_row("PollSaturation::on_idle", &mut buf);
    bench_sojourn_saturation_update(&mut buf);
    print_row("SojournSaturation::update", &mut buf);
    bench_liveness_u64(&mut buf);
    print_row("Liveness::update", &mut buf);
    bench_running_min_f64(&mut buf);
    print_row("RunningMin::<f64>::update", &mut buf);
    bench_running_max_f64(&mut buf);
    print_row("RunningMax::<f64>::update", &mut buf);
    bench_event_rate_u64(&mut buf);
    print_row("EventRate::update", &mut buf);
    bench_codel_i64(&mut buf);
    print_row("CoDel::<i64>::update", &mut buf);
    bench_max_gauge_f64(&mut buf);
    print_row("MaxGauge::<f64>::update", &mut buf);
    bench_jitter_f64(&mut buf);
    print_row("Jitter::<f64>::update", &mut buf);
    bench_error_rate(&mut buf);
    print_row("ErrorRate::update", &mut buf);
    bench_trend_alert_f64(&mut buf);
    print_row("TrendAlert::update", &mut buf);
    bench_hawkes_intensity_u64(&mut buf);
    print_row("HawkesIntensity::update", &mut buf);

    section("Anomaly Detection");
    print_header();
    bench_multi_gate_f64(&mut buf);
    print_row("MultiGate::update", &mut buf);
    bench_windowed_median_f64(&mut buf);
    print_row("WindowedMedian(32)::update", &mut buf);
    bench_robust_z_f64(&mut buf);
    print_row("RobustZScore::<f64>::update", &mut buf);

    section("Signal Processing");
    print_header();
    bench_spring_f64(&mut buf);
    print_row("Spring::update", &mut buf);
    bench_peak_hold_f64(&mut buf);
    print_row("PeakHold::<f64>::update", &mut buf);
    bench_asym_ema_f64(&mut buf);
    print_row("AsymEma::update", &mut buf);
    bench_kama_f64(&mut buf);
    print_row("Kama(10)::update", &mut buf);
    bench_kalman1d_f64(&mut buf);
    print_row("Kalman1d::update", &mut buf);

    section("Utilities");
    print_header();
    bench_slew_f64(&mut buf);
    print_row("Slew::<f64>::update", &mut buf);
    bench_bool_window(&mut buf);
    print_row("BoolWindow(64)::update", &mut buf);
    bench_hysteresis_f64(&mut buf);
    print_row("Hysteresis::<f64>::update", &mut buf);
    bench_debounce(&mut buf);
    print_row("Debounce::update", &mut buf);
    bench_dead_band_f64(&mut buf);
    print_row("DeadBand::<f64>::update", &mut buf);
    bench_level_crossing_f64(&mut buf);
    print_row("LevelCrossing::<f64>::update", &mut buf);
    bench_first_diff_f64(&mut buf);
    print_row("FirstDiff::<f64>::update", &mut buf);
    bench_second_diff_f64(&mut buf);
    print_row("SecondDiff::<f64>::update", &mut buf);
    bench_peak_detector_f64(&mut buf);
    print_row("PeakDetector::<f64>::update", &mut buf);

    section("Frequency");
    print_header();
    bench_topk(&mut buf);
    print_row("TopK<u64,16>::update", &mut buf);

    section("Statistics & Signal Analysis");
    print_header();
    bench_moments_f64(&mut buf);
    print_row("Moments::update", &mut buf);
    bench_autocorrelation_f64(&mut buf);
    print_row("Autocorrelation<1>::update", &mut buf);
    bench_autocorrelation_lag10(&mut buf);
    print_row("Autocorrelation<10>::update", &mut buf);
    bench_cross_correlation_f64(&mut buf);
    print_row("CrossCorrelation<10>::update", &mut buf);
    bench_entropy_f64(&mut buf);
    print_row("Entropy<8>::update", &mut buf);
    bench_transfer_entropy_f64(&mut buf);
    print_row("TransferEntropy(8,1)::update", &mut buf);
    bench_predictive_info_bound_f64(&mut buf);
    print_row("PredictiveInfoBound(8)::update", &mut buf);
    bench_harmonic_mean_f64(&mut buf);
    print_row("HarmonicMean::update", &mut buf);
    bench_bipower_variation_f64(&mut buf);
    print_row("BipowerVariation::update", &mut buf);
    bench_roll_spread_f64(&mut buf);
    print_row("RollSpread::update", &mut buf);
    bench_two_scale_rv_f64(&mut buf);
    print_row("TwoScaleRv::update", &mut buf);

    section("Regression");
    print_header();
    bench_linear_regression_f64(&mut buf);
    print_row("LinearRegression::update", &mut buf);
    bench_ew_linear_regression_f64(&mut buf);
    print_row("EwLinearRegression::update", &mut buf);
    bench_polynomial_regression_f64(&mut buf);
    print_row("PolynomialRegression(2)::update", &mut buf);
    bench_ew_polynomial_regression_f64(&mut buf);
    print_row("EwPolynomialRegression(2)::update", &mut buf);
    bench_exponential_regression_f64(&mut buf);
    print_row("ExponentialRegression::update", &mut buf);
    bench_logarithmic_regression_f64(&mut buf);
    print_row("LogarithmicRegression::update", &mut buf);
    bench_power_regression_f64(&mut buf);
    print_row("PowerRegression::update", &mut buf);
    bench_polynomial_update(&mut buf, 1);
    print_row("PolynomialRegression(1)::update", &mut buf);
    bench_polynomial_update(&mut buf, 4);
    print_row("PolynomialRegression(4)::update", &mut buf);
    bench_polynomial_query(&mut buf, 1, false);
    print_row("PolynomialRegression(1)::coefficients", &mut buf);
    bench_polynomial_query(&mut buf, 2, false);
    print_row("PolynomialRegression(2)::coefficients", &mut buf);
    bench_polynomial_query(&mut buf, 2, true);
    print_row("PolynomialRegression(2)::predict", &mut buf);

    section("Queries & merges");
    print_header();
    bench_liveness_check(&mut buf);
    print_row("Liveness::check", &mut buf);
    bench_max_gauge_update_take(&mut buf);
    print_row("MaxGauge::<f64>::update + take", &mut buf);
    bench_moments_merge(&mut buf);
    print_row("Moments::merge", &mut buf);
    let ac = warm_autocorrelation(1);
    bench_query(&mut buf, &ac, Autocorrelation::correlation);
    print_row("Autocorrelation<1>::correlation", &mut buf);
    let cov = warm_covariance();
    bench_query(&mut buf, &cov, Covariance::correlation);
    print_row("Covariance::correlation", &mut buf);
    let cc = warm_cross_correlation();
    bench_query(&mut buf, &cc, |c| c.correlation(5));
    print_row("CrossCorrelation<10>::correlation", &mut buf);
    bench_query(&mut buf, &cc, CrossCorrelation::peak_lag);
    print_row("CrossCorrelation<10>::peak_lag", &mut buf);
    let e = warm_entropy();
    bench_query(&mut buf, &e, Entropy::entropy);
    print_row("Entropy<8>::entropy", &mut buf);
    bench_query(&mut buf, &e, |e| e.surprise(3));
    print_row("Entropy<8>::surprise", &mut buf);
    let te = warm_transfer_entropy();
    bench_query(&mut buf, &te, TransferEntropy::te_x_to_y);
    print_row("TransferEntropy(8,1)::te_x_to_y", &mut buf);
    bench_query(&mut buf, &te, TransferEntropy::net_flow);
    print_row("TransferEntropy(8,1)::net_flow", &mut buf);
    let lr = warm_linear_regression();
    bench_query(&mut buf, &lr, LinearRegression::slope);
    print_row("LinearRegression::slope", &mut buf);
    bench_query(&mut buf, &lr, LinearRegression::r_squared);
    print_row("LinearRegression::r_squared", &mut buf);
    bench_query(&mut buf, &lr, |r| r.predict(5.0));
    print_row("LinearRegression::predict", &mut buf);
    let m = warm_moments();
    bench_query(&mut buf, &m, Moments::skewness);
    print_row("Moments::skewness", &mut buf);
    let w = warm_welford();
    bench_query(&mut buf, &w, Welford::std_dev);
    print_row("Welford::std_dev", &mut buf);

    section("Estimation");
    print_header();
    bench_kalman2d_predict(&mut buf);
    print_row("Kalman2d::predict", &mut buf);
    bench_kalman2d_update(&mut buf);
    print_row("Kalman2d::update", &mut buf);
    bench_kalman3d_predict(&mut buf);
    print_row("Kalman3d::predict", &mut buf);
    bench_kalman3d_update(&mut buf);
    print_row("Kalman3d::update", &mut buf);
    bench_beta_binomial_update(&mut buf);
    print_row("BetaBinomial::update", &mut buf);
    bench_beta_binomial_queries(&mut buf, false);
    print_row("BetaBinomial::mean", &mut buf);
    bench_beta_binomial_queries(&mut buf, true);
    print_row("BetaBinomial::credible_interval", &mut buf);
    bench_gamma_poisson_update(&mut buf);
    print_row("GammaPoisson::update", &mut buf);
    bench_sprt_bernoulli(&mut buf);
    print_row("SprtBernoulli::update", &mut buf);
    bench_sprt_gaussian(&mut buf);
    print_row("SprtGaussian::update", &mut buf);

    section("Adaptive filters (d=5) & optimizers (d=10)");
    print_header();
    bench_lms_filter_d5(&mut buf);
    print_row("LmsFilter::update d=5", &mut buf);
    bench_nlms_filter_d5(&mut buf);
    print_row("NlmsFilter::update d=5", &mut buf);
    bench_rls_filter_d5(&mut buf);
    print_row("RlsFilter::update d=5", &mut buf);
    bench_logistic_regression_d5(&mut buf);
    print_row("LogisticRegression::update d=5", &mut buf);
    bench_online_kmeans_k3_d5(&mut buf);
    print_row("OnlineKMeans::update k=3 d=5", &mut buf);
    bench_online_gd_d10(&mut buf);
    print_row("OnlineGd::step d=10", &mut buf);
    bench_adagrad_d10(&mut buf);
    print_row("AdaGrad::step d=10", &mut buf);
    bench_adam_d10(&mut buf);
    print_row("Adam::step d=10", &mut buf);

    section("Bandits — select() scaling");
    bench_bandit_select_sweep(&mut buf);

    section("Bandits — update() scaling");
    bench_bandit_update_sweep(&mut buf);

    println!();
}
