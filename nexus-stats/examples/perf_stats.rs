//! Cycles-per-update benchmark for all nexus-stats primitives.
//!
//! Batches 64 updates per measurement to amortize rdtsc overhead (~20 cycles).
//!
//! Usage:
//!   cargo build --release --example perf_stats
//!   taskset -c 0 ./target/release/examples/perf_stats

use std::hint::black_box;

use nexus_stats::{
    control::{BoolWindow, HysteresisF64},
    detection::{CusumF64, MosumF64, MultiGateF64, RobustZScoreF64, ShiryaevRobertsF64},
    frequency::TopK,
    learning::{EpsilonGreedyF64, Exp3F64, ThompsonBetaF64, ThompsonGammaF64, Ucb1F64},
    monitoring::{
        CoDelI64, DrawdownF64, EventRateU64, LivenessU64, PeakHoldF64, RunningMaxF64,
        RunningMinF64, WindowedMaxF64, WindowedMinF64,
    },
    signal::{AutocorrelationF64, CrossCorrelationF64, EntropyF64, TransferEntropyF64},
    smoothing::{
        AsymEmaF64, EmaF64, HoltF64, Kalman1dF64, KamaF64, SlewF64, SpringF64, WindowedMedianF64,
    },
    statistics::{CovarianceF64, EwmaVarF64, MomentsF64, WelfordF64},
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
        "  {:<28} {:>6} {:>6} {:>6} {:>7} {:>7}",
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
        "  {:<28} {:>6} {:>6} {:>6} {:>7} {:>7}",
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

// ============================================================================
// Phase 1: CUSUM, EMA, Welford
// ============================================================================

fn bench_cusum_f64(samples: &mut [u64]) {
    let mut cusum = CusumF64::builder(100.0)
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
    let mut ema = EmaF64::builder().alpha(0.1).build().unwrap();
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
    let mut w = WelfordF64::new();
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
    let mut dd = DrawdownF64::new();
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
    let mut wm = WindowedMaxF64::new(1000).unwrap();
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
    let mut wm = WindowedMinF64::new(1000).unwrap();
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
    let mut ev = EwmaVarF64::builder().alpha(0.1).build().unwrap();
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
    let mut lv = LivenessU64::builder()
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

fn bench_mosum_f64(samples: &mut [u64]) {
    let mut mosum = MosumF64::builder(100.0)
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
    let mut cov = CovarianceF64::new();
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
    let mut h = HoltF64::builder().alpha(0.3).beta(0.1).build().unwrap();
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
    let mut sr = ShiryaevRobertsF64::builder()
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
    let mut rm = RunningMinF64::new();
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
    let mut rm = RunningMaxF64::new();
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
    let mut er = EventRateU64::builder().span(15).build().unwrap();
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
    let mut qd = CoDelI64::builder()
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
    let mut mg = MultiGateF64::builder()
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
    let mut wm = WindowedMedianF64::new(32);
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
    let mut rz = RobustZScoreF64::builder()
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
    let mut sp = SpringF64::new(0.5).unwrap();
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
    let mut ph = PeakHoldF64::builder()
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
    let mut ae = AsymEmaF64::builder()
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
    let mut kama = KamaF64::builder().window_size(10).build().unwrap();
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
    let mut kf = Kalman1dF64::builder()
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
    let mut sl = SlewF64::new(5.0).unwrap();
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
    let mut hy = HysteresisF64::new(40.0, 60.0).unwrap();
    let mut rng = 12345u64;
    for _ in 0..WARMUP {
        let _ = hy.update((next_val(&mut rng) % 100) as f64);
    }
    for s in samples.iter_mut() {
        let start = rdtsc_start();
        for _ in 0..BATCH {
            let _ = hy.update((next_val(&mut rng) % 100) as f64);
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
    let mut m = MomentsF64::new();
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
    let mut ac = AutocorrelationF64::builder().lag(1).build().unwrap();
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
    let mut cc = CrossCorrelationF64::builder().lag(10).build().unwrap();
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
    let mut e = EntropyF64::builder().bins(8).build().unwrap();
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
    let mut te = TransferEntropyF64::builder()
        .bins(8)
        .lag(1)
        .build()
        .unwrap();
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
// Bandits — parameterized by K
// ============================================================================

const BANDIT_KS: &[usize] = &[2, 5, 10, 25, 50];

fn bench_bandit_select_sweep(samples: &mut [u64]) {
    println!(
        "\n  {:<28} {:>6} {:>6} {:>6} {:>7} {:>7}",
        "(cycles/op)", "p50", "p90", "p99", "p99.9", "max"
    );

    for &k in BANDIT_KS {
        // UCB1
        let mut b = Ucb1F64::builder().arms(k).build().unwrap();
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
        let mut b = ThompsonBetaF64::builder().arms(k).build().unwrap();
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
        let mut b = ThompsonGammaF64::builder().arms(k).build().unwrap();
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
        let mut b = EpsilonGreedyF64::builder()
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
        let mut b = Exp3F64::builder().arms(k).gamma(0.1).build().unwrap();
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
        "\n  {:<28} {:>6} {:>6} {:>6} {:>7} {:>7}",
        "(cycles/op)", "p50", "p90", "p99", "p99.9", "max"
    );

    for &k in BANDIT_KS {
        // UCB1 stationary
        let mut b = Ucb1F64::builder().arms(k).build().unwrap();
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
        let mut b = Ucb1F64::builder().arms(k).decay(0.99).build().unwrap();
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
    print_row("CusumF64::update", &mut buf);
    bench_mosum_f64(&mut buf);
    print_row("MosumF64(64)::update", &mut buf);
    bench_shiryaev_roberts(&mut buf);
    print_row("ShiryaevRoberts::update", &mut buf);

    section("Smoothing");
    print_header();
    bench_ema_f64(&mut buf);
    print_row("EmaF64::update", &mut buf);
    bench_holt_f64(&mut buf);
    print_row("HoltF64::update", &mut buf);

    section("Variance & Correlation");
    print_header();
    bench_welford_f64(&mut buf);
    print_row("WelfordF64::update", &mut buf);
    bench_ewma_var_f64(&mut buf);
    print_row("EwmaVarF64::update", &mut buf);
    bench_covariance_f64(&mut buf);
    print_row("CovarianceF64::update", &mut buf);

    section("Monitoring");
    print_header();
    bench_drawdown_f64(&mut buf);
    print_row("DrawdownF64::update", &mut buf);
    bench_windowed_max_f64(&mut buf);
    print_row("WindowedMaxF64::update", &mut buf);
    bench_windowed_min_f64(&mut buf);
    print_row("WindowedMinF64::update", &mut buf);
    bench_liveness_u64(&mut buf);
    print_row("LivenessU64::update", &mut buf);
    bench_running_min_f64(&mut buf);
    print_row("RunningMinF64::update", &mut buf);
    bench_running_max_f64(&mut buf);
    print_row("RunningMaxF64::update", &mut buf);
    bench_event_rate_u64(&mut buf);
    print_row("EventRateU64::update", &mut buf);
    bench_codel_i64(&mut buf);
    print_row("CoDelI64::update", &mut buf);

    section("Anomaly Detection");
    print_header();
    bench_multi_gate_f64(&mut buf);
    print_row("MultiGateF64::update", &mut buf);
    bench_windowed_median_f64(&mut buf);
    print_row("WindowedMedian(32)::update", &mut buf);
    bench_robust_z_f64(&mut buf);
    print_row("RobustZScoreF64::update", &mut buf);

    section("Signal Processing");
    print_header();
    bench_spring_f64(&mut buf);
    print_row("SpringF64::update", &mut buf);
    bench_peak_hold_f64(&mut buf);
    print_row("PeakHoldF64::update", &mut buf);
    bench_asym_ema_f64(&mut buf);
    print_row("AsymEmaF64::update", &mut buf);
    bench_kama_f64(&mut buf);
    print_row("KamaF64(10)::update", &mut buf);
    bench_kalman1d_f64(&mut buf);
    print_row("Kalman1dF64::update", &mut buf);

    section("Utilities");
    print_header();
    bench_slew_f64(&mut buf);
    print_row("SlewF64::update", &mut buf);
    bench_bool_window(&mut buf);
    print_row("BoolWindow<1>::update", &mut buf);
    bench_hysteresis_f64(&mut buf);
    print_row("HysteresisF64::update", &mut buf);

    section("Frequency");
    print_header();
    bench_topk(&mut buf);
    print_row("TopK<u64,16>::update", &mut buf);

    section("Statistics & Signal Analysis");
    print_header();
    bench_moments_f64(&mut buf);
    print_row("MomentsF64::update", &mut buf);
    bench_autocorrelation_f64(&mut buf);
    print_row("Autocorrelation<1>::update", &mut buf);
    bench_cross_correlation_f64(&mut buf);
    print_row("CrossCorrelation<10>::update", &mut buf);
    bench_entropy_f64(&mut buf);
    print_row("Entropy<8>::update", &mut buf);
    bench_transfer_entropy_f64(&mut buf);
    print_row("TransferEntropy(8,1)::update", &mut buf);

    section("Bandits — select() scaling");
    bench_bandit_select_sweep(&mut buf);

    section("Bandits — update() scaling");
    bench_bandit_update_sweep(&mut buf);

    println!();
}
