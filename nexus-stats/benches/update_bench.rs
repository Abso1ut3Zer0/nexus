#![allow(unused_must_use)]
//! Criterion benchmarks for nexus-stats hot-path update methods.
//!
//! Each benchmark primes the type with 1000 samples, then measures the
//! steady-state update cost. Uses `black_box` to prevent dead code elimination.
//!
//! Run on controlled system for meaningful results:
//! ```bash
//! echo 1 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo
//! taskset -c 0 cargo bench -p nexus-stats --bench update_bench
//! echo 0 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo
//! ```

use criterion::{Criterion, black_box, criterion_group, criterion_main};
use nexus_stats::{
    control::{DeadBand, FirstDiff, Hysteresis, LevelCrossing, SecondDiff},
    detection::{
        AdaptiveThreshold, Bocpd, Cusum, DistDrift, RobustZScore, ShiryaevRoberts, TrendAlert,
    },
    estimation::{Kalman2d, Kalman3d},
    learning::{
        AdaGrad, Adam, EpsilonGreedy, Exp3, LmsFilter, NlmsFilter, OnlineGd, OnlineKMeans,
        RlsFilter, ThompsonBeta, ThompsonGamma, Ucb1,
    },
    monitoring::{Drawdown, ErrorRate, Jitter, RunningMax, RunningMin},
    normalization::{MinMaxNorm, ZScoreNorm},
    regression::{EwLinearRegression, LinearRegression, LogisticRegression, PolynomialRegression},
    signal::{Autocorrelation, CrossCorrelation, Entropy, TransferEntropy},
    smoothing::{AsymEma, Ema, Holt, Kalman1d, Slew, Spring},
    statistics::{Covariance, Cvar, EwmaVar, HarmonicMean, Lpm, Moments, Percentile, Welford},
};

// Simple LCG for deterministic pseudo-random data in benchmarks.
// Not crypto-quality — just needs to defeat constant propagation.
struct Lcg(u64);

impl Lcg {
    fn new(seed: u64) -> Self {
        Self(seed)
    }
    fn next_f64(&mut self) -> f64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        // Map to [0, 100) range — realistic for most stats
        (self.0 >> 33) as f64 * (100.0 / (1u64 << 31) as f64)
    }
    fn next_feature(&mut self) -> f64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        // Map to [-1, 1) range — realistic for feature vectors
        ((self.0 >> 33) as f64 / (1u64 << 31) as f64).mul_add(2.0, -1.0)
    }
    fn next_unit(&mut self) -> f64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        (self.0 >> 33) as f64 / (1u64 << 31) as f64
    }
}

// ============================================================
// Group 1: Core statistics
// ============================================================

fn bench_welford(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut w = Welford::new();
    for _ in 0..1000 {
        w.update(rng.next_f64());
    }
    c.bench_function("Welford::update", |b| {
        b.iter(|| w.update(black_box(rng.next_f64())))
    });
}

fn bench_moments(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut m = Moments::new();
    for _ in 0..1000 {
        m.update(rng.next_f64());
    }
    c.bench_function("Moments::update", |b| {
        b.iter(|| m.update(black_box(rng.next_f64())))
    });
}

fn bench_ema(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut e = Ema::builder().span(20).min_samples(1).build().unwrap();
    for _ in 0..1000 {
        let _ = e.update(rng.next_f64());
    }
    c.bench_function("Ema::update (span=20)", |b| {
        b.iter(|| e.update(black_box(rng.next_f64())).unwrap())
    });
}

fn bench_asym_ema(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut e = AsymEma::builder()
        .alpha_up(0.3)
        .alpha_down(0.1)
        .build()
        .unwrap();
    for _ in 0..1000 {
        let _ = e.update(rng.next_f64());
    }
    c.bench_function("AsymEma::update", |b| {
        b.iter(|| e.update(black_box(rng.next_f64())).unwrap())
    });
}

fn bench_holt(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut h = Holt::builder()
        .alpha(0.3)
        .beta(0.1)
        .min_samples(2)
        .build()
        .unwrap();
    for _ in 0..1000 {
        let _ = h.update(rng.next_f64());
    }
    c.bench_function("Holt::update", |b| {
        b.iter(|| h.update(black_box(rng.next_f64())).unwrap())
    });
}

fn bench_ewma_var(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut e = EwmaVar::builder().alpha(0.1).build().unwrap();
    for _ in 0..1000 {
        let _ = e.update(rng.next_f64());
    }
    c.bench_function("EwmaVar::update", |b| {
        b.iter(|| e.update(black_box(rng.next_f64())).unwrap())
    });
}

fn bench_covariance(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut cov = Covariance::new();
    for _ in 0..1000 {
        cov.update(rng.next_f64(), rng.next_f64());
    }
    c.bench_function("Covariance::update", |b| {
        b.iter(|| cov.update(black_box(rng.next_f64()), black_box(rng.next_f64())))
    });
}

fn bench_harmonic_mean(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut h = HarmonicMean::new();
    for _ in 0..1000 {
        h.update(rng.next_f64() + 1.0);
    }
    c.bench_function("HarmonicMean::update", |b| {
        b.iter(|| h.update(black_box(rng.next_f64() + 1.0)))
    });
}

fn bench_percentile_p50(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut p = Percentile::builder().percentile(0.5).build().unwrap();
    for _ in 0..1000 {
        let _ = p.update(rng.next_f64());
    }
    c.bench_function("Percentile::update (p50)", |b| {
        b.iter(|| p.update(black_box(rng.next_f64())).unwrap())
    });
}

fn bench_percentile_p99(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut p = Percentile::builder().percentile(0.99).build().unwrap();
    for _ in 0..1000 {
        let _ = p.update(rng.next_f64());
    }
    c.bench_function("Percentile::update (p99)", |b| {
        b.iter(|| p.update(black_box(rng.next_f64())).unwrap())
    });
}

fn bench_jitter(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut j = Jitter::<f64>::builder().alpha(0.1).build().unwrap();
    for _ in 0..1000 {
        let _ = j.update(rng.next_f64());
    }
    c.bench_function("Jitter::<f64>::update", |b| {
        b.iter(|| j.update(black_box(rng.next_f64())).unwrap())
    });
}

fn bench_drawdown(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut d = Drawdown::<f64>::new();
    for _ in 0..1000 {
        let _ = d.update(rng.next_f64());
    }
    c.bench_function("Drawdown::<f64>::update", |b| {
        b.iter(|| d.update(black_box(rng.next_f64())).unwrap())
    });
}

fn bench_running_min(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut r = RunningMin::<f64>::new();
    for _ in 0..1000 {
        r.update(rng.next_f64());
    }
    c.bench_function("RunningMin::<f64>::update", |b| {
        b.iter(|| r.update(black_box(rng.next_f64())))
    });
}

fn bench_running_max(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut r = RunningMax::<f64>::new();
    for _ in 0..1000 {
        r.update(rng.next_f64());
    }
    c.bench_function("RunningMax::<f64>::update", |b| {
        b.iter(|| r.update(black_box(rng.next_f64())))
    });
}

fn bench_slew(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut s = Slew::<f64>::new(5.0).unwrap();
    for _ in 0..1000 {
        s.update(rng.next_f64());
    }
    c.bench_function("Slew::<f64>::update", |b| {
        b.iter(|| s.update(black_box(rng.next_f64())))
    });
}

fn bench_spring(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut s = Spring::new(0.1).unwrap();
    for _ in 0..1000 {
        let _ = s.update(rng.next_f64(), 1.0);
    }
    c.bench_function("Spring::update", |b| {
        b.iter(|| s.update(black_box(rng.next_f64()), black_box(1.0)))
    });
}

fn bench_dead_band(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut d = DeadBand::<f64>::new(1.0).unwrap();
    for _ in 0..1000 {
        d.update(rng.next_f64());
    }
    c.bench_function("DeadBand::<f64>::update", |b| {
        b.iter(|| d.update(black_box(rng.next_f64())))
    });
}

fn bench_hysteresis(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut h = Hysteresis::<f64>::new(40.0, 60.0).unwrap();
    for _ in 0..1000 {
        h.update(rng.next_f64());
    }
    c.bench_function("Hysteresis::<f64>::update", |b| {
        b.iter(|| h.update(black_box(rng.next_f64())))
    });
}

fn bench_level_crossing(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut l = LevelCrossing::<f64>::new(50.0).unwrap();
    for _ in 0..1000 {
        l.update(rng.next_f64());
    }
    c.bench_function("LevelCrossing::<f64>::update", |b| {
        b.iter(|| l.update(black_box(rng.next_f64())))
    });
}

fn bench_first_diff(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut d = FirstDiff::<f64>::new();
    for _ in 0..1000 {
        d.update(rng.next_f64());
    }
    c.bench_function("FirstDiff::<f64>::update", |b| {
        b.iter(|| d.update(black_box(rng.next_f64())))
    });
}

fn bench_second_diff(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut d = SecondDiff::<f64>::new();
    for _ in 0..1000 {
        d.update(rng.next_f64());
    }
    c.bench_function("SecondDiff::<f64>::update", |b| {
        b.iter(|| d.update(black_box(rng.next_f64())))
    });
}

fn bench_cusum(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut cs = Cusum::builder(50.0)
        .threshold(10.0)
        .slack(0.5)
        .build()
        .unwrap();
    for _ in 0..1000 {
        let _ = cs.update(rng.next_f64());
    }
    c.bench_function("Cusum::update", |b| {
        b.iter(|| cs.update(black_box(rng.next_f64())).unwrap())
    });
}

fn bench_shiryaev_roberts(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut sr = ShiryaevRoberts::builder()
        .pre_change_mean(50.0)
        .post_change_mean(51.0)
        .variance(1.0)
        .threshold(100.0)
        .build()
        .unwrap();
    for _ in 0..1000 {
        let _ = sr.update(rng.next_f64());
    }
    c.bench_function("ShiryaevRoberts::update", |b| {
        b.iter(|| sr.update(black_box(rng.next_f64())).unwrap())
    });
}

fn bench_trend_alert(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut ta = TrendAlert::builder()
        .alpha(0.3)
        .beta(0.1)
        .trend_threshold(5.0)
        .build()
        .unwrap();
    for _ in 0..1000 {
        let _ = ta.update(rng.next_f64());
    }
    c.bench_function("TrendAlert::update", |b| {
        b.iter(|| ta.update(black_box(rng.next_f64())).unwrap())
    });
}

fn bench_adaptive_threshold(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut at = AdaptiveThreshold::builder()
        .alpha(0.1)
        .z_threshold(3.0)
        .min_samples(20)
        .build()
        .unwrap();
    for _ in 0..1000 {
        let _ = at.update(rng.next_f64());
    }
    c.bench_function("AdaptiveThreshold::update", |b| {
        b.iter(|| at.update(black_box(rng.next_f64())).unwrap())
    });
}

fn bench_robust_z(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut rz = RobustZScore::<f64>::builder()
        .alpha(0.1)
        .reject_threshold(3.0)
        .min_samples(5)
        .build()
        .unwrap();
    for _ in 0..1000 {
        let _ = rz.update(rng.next_f64());
    }
    c.bench_function("RobustZScore::<f64>::update", |b| {
        b.iter(|| rz.update(black_box(rng.next_f64())).unwrap())
    });
}

fn bench_error_rate(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut er = ErrorRate::builder()
        .alpha(0.1)
        .threshold(0.5)
        .build()
        .unwrap();
    for _ in 0..1000 {
        er.update(rng.next_f64() > 50.0);
    }
    c.bench_function("ErrorRate::update", |b| {
        b.iter(|| er.update(black_box(rng.next_f64() > 50.0)))
    });
}

// ============================================================
// Group 2: Const-generic types
// ============================================================

fn bench_autocorrelation(c: &mut Criterion) {
    let mut rng = Lcg::new(42);

    let mut ac1 = Autocorrelation::builder().lag(1).build().unwrap();
    for _ in 0..1000 {
        let _ = ac1.update(rng.next_f64());
    }
    c.bench_function("Autocorrelation::update (lag=1)", |b| {
        b.iter(|| ac1.update(black_box(rng.next_f64())).unwrap())
    });

    let mut ac10 = Autocorrelation::builder().lag(10).build().unwrap();
    for _ in 0..1000 {
        let _ = ac10.update(rng.next_f64());
    }
    c.bench_function("Autocorrelation::update (lag=10)", |b| {
        b.iter(|| ac10.update(black_box(rng.next_f64())).unwrap())
    });
}

fn bench_cross_correlation(c: &mut Criterion) {
    let mut rng = Lcg::new(42);

    let mut cc1 = CrossCorrelation::builder().lag(1).build().unwrap();
    for _ in 0..1000 {
        let _ = cc1.update(rng.next_f64(), rng.next_f64());
    }
    c.bench_function("CrossCorrelation::update (lag=1)", |b| {
        b.iter(|| {
            cc1.update(black_box(rng.next_f64()), black_box(rng.next_f64()))
                .unwrap()
        })
    });

    let mut cc10 = CrossCorrelation::builder().lag(10).build().unwrap();
    for _ in 0..1000 {
        let _ = cc10.update(rng.next_f64(), rng.next_f64());
    }
    c.bench_function("CrossCorrelation::update (lag=10)", |b| {
        b.iter(|| {
            cc10.update(black_box(rng.next_f64()), black_box(rng.next_f64()))
                .unwrap()
        })
    });
}

fn bench_entropy(c: &mut Criterion) {
    let mut rng = Lcg::new(42);

    let mut e4 = Entropy::builder().bins(4).build().unwrap();
    for _ in 0..1000 {
        e4.update((rng.next_f64() as usize) % 4);
    }
    c.bench_function("Entropy::update (bins=4)", |b| {
        b.iter(|| e4.update(black_box((rng.next_f64() as usize) % 4)))
    });

    let mut e16 = Entropy::builder().bins(16).build().unwrap();
    for _ in 0..1000 {
        e16.update((rng.next_f64() as usize) % 16);
    }
    c.bench_function("Entropy::update (bins=16)", |b| {
        b.iter(|| e16.update(black_box((rng.next_f64() as usize) % 16)))
    });
}

// ============================================================
// Group 3: Runtime-configured types
// ============================================================

fn bench_linear_regression(c: &mut Criterion) {
    let mut rng = Lcg::new(42);

    let mut lr = LinearRegression::builder().intercept(true).build().unwrap();
    for i in 0..1000 {
        let _ = lr.update(i as f64, rng.next_f64());
    }
    c.bench_function("LinearRegression::update (intercept)", |b| {
        let mut x = 1000.0;
        b.iter(|| {
            x += 1.0;
            lr.update(black_box(x), black_box(rng.next_f64())).unwrap()
        })
    });

    let mut lr_no = LinearRegression::builder()
        .intercept(false)
        .build()
        .unwrap();
    for i in 0..1000 {
        let _ = lr_no.update(i as f64, rng.next_f64());
    }
    c.bench_function("LinearRegression::update (no intercept)", |b| {
        let mut x = 1000.0;
        b.iter(|| {
            x += 1.0;
            lr_no
                .update(black_box(x), black_box(rng.next_f64()))
                .unwrap()
        })
    });
}

fn bench_ew_linear_regression(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut lr = EwLinearRegression::builder()
        .alpha(0.05)
        .intercept(true)
        .build()
        .unwrap();
    for i in 0..1000 {
        let _ = lr.update(i as f64, rng.next_f64());
    }
    c.bench_function("EwLinearRegression::update (alpha=0.05)", |b| {
        let mut x = 1000.0;
        b.iter(|| {
            x += 1.0;
            lr.update(black_box(x), black_box(rng.next_f64())).unwrap()
        })
    });
}

fn bench_polynomial_regression(c: &mut Criterion) {
    let mut rng = Lcg::new(42);

    for degree in [2, 3, 5] {
        let mut pr = PolynomialRegression::builder()
            .degree(degree)
            .intercept(true)
            .build()
            .unwrap();
        for i in 0..1000 {
            let _ = pr.update(i as f64 * 0.01, rng.next_f64());
        }
        c.bench_function(
            &format!("PolynomialRegression::update (deg={degree})"),
            |b| {
                let mut x = 10.0;
                b.iter(|| {
                    x += 0.01;
                    pr.update(black_box(x), black_box(rng.next_f64())).unwrap()
                })
            },
        );
    }
}

fn bench_transfer_entropy(c: &mut Criterion) {
    let mut rng = Lcg::new(42);

    for bins in [4usize, 8] {
        let mut te = TransferEntropy::builder()
            .bins(bins)
            .lag(1)
            .build()
            .unwrap();
        for _ in 0..1000 {
            te.update(
                (rng.next_f64() as usize) % bins,
                (rng.next_f64() as usize) % bins,
            );
        }
        c.bench_function(&format!("TransferEntropy::update (bins={bins})"), |b| {
            b.iter(|| {
                te.update(
                    black_box((rng.next_f64() as usize) % bins),
                    black_box((rng.next_f64() as usize) % bins),
                )
            })
        });
    }
}

// ============================================================
// Group 4: Adaptive filters
// ============================================================

fn bench_lms_filter(c: &mut Criterion) {
    let mut rng = Lcg::new(42);

    for dims in [3, 10] {
        let mut f = LmsFilter::builder()
            .dimensions(dims)
            .learning_rate(0.01)
            .build()
            .unwrap();
        let mut features: Vec<f64> = (0..dims).map(|_| rng.next_feature()).collect();
        for _ in 0..1000 {
            for v in &mut features {
                *v = rng.next_feature();
            }
            let _ = f.update(&features, rng.next_f64());
        }
        c.bench_function(&format!("LmsFilter::update (d={dims})"), |b| {
            b.iter(|| {
                for v in &mut features {
                    *v = rng.next_feature();
                }
                f.update(black_box(&features), black_box(rng.next_f64()))
                    .unwrap()
            })
        });
    }
}

fn bench_nlms_filter(c: &mut Criterion) {
    let mut rng = Lcg::new(42);

    for dims in [3, 10] {
        let mut f = NlmsFilter::builder()
            .dimensions(dims)
            .learning_rate(0.5)
            .build()
            .unwrap();
        let mut features: Vec<f64> = (0..dims).map(|_| rng.next_feature()).collect();
        for _ in 0..1000 {
            for v in &mut features {
                *v = rng.next_feature();
            }
            let _ = f.update(&features, rng.next_f64());
        }
        c.bench_function(&format!("NlmsFilter::update (d={dims})"), |b| {
            b.iter(|| {
                for v in &mut features {
                    *v = rng.next_feature();
                }
                f.update(black_box(&features), black_box(rng.next_f64()))
                    .unwrap()
            })
        });
    }
}

fn bench_rls_filter(c: &mut Criterion) {
    let mut rng = Lcg::new(42);

    for dims in [3, 5, 10] {
        let mut f = RlsFilter::builder()
            .dimensions(dims)
            .forgetting_factor(0.99)
            .build()
            .unwrap();
        let mut features: Vec<f64> = (0..dims).map(|_| rng.next_feature()).collect();
        for _ in 0..1000 {
            for v in &mut features {
                *v = rng.next_feature();
            }
            let _ = f.update(&features, rng.next_f64());
        }
        c.bench_function(&format!("RlsFilter::update (d={dims})"), |b| {
            b.iter(|| {
                for v in &mut features {
                    *v = rng.next_feature();
                }
                f.update(black_box(&features), black_box(rng.next_f64()))
                    .unwrap()
            })
        });
    }
}

fn bench_logistic_regression(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let dims = 5;
    let mut lr = LogisticRegression::builder()
        .dimensions(dims)
        .learning_rate(0.1)
        .build()
        .unwrap();
    let mut features: Vec<f64> = (0..dims).map(|_| rng.next_feature()).collect();
    for _ in 0..1000 {
        for v in &mut features {
            *v = rng.next_feature();
        }
        lr.update(&features, rng.next_f64() > 50.0);
    }
    c.bench_function("LogisticRegression::update (d=5)", |b| {
        b.iter(|| {
            for v in &mut features {
                *v = rng.next_feature();
            }
            lr.update(black_box(&features), black_box(rng.next_f64() > 50.0))
        })
    });
}

fn bench_online_kmeans(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let dims = 5;
    let mut km = OnlineKMeans::builder()
        .dimensions(dims)
        .clusters(3)
        .learning_rate(0.1)
        .build()
        .unwrap();
    let mut features: Vec<f64> = (0..dims).map(|_| rng.next_feature()).collect();
    for _ in 0..1000 {
        for v in &mut features {
            *v = rng.next_feature();
        }
        km.update(&features);
    }
    c.bench_function("OnlineKMeans::update (k=3, d=5)", |b| {
        b.iter(|| {
            for v in &mut features {
                *v = rng.next_feature();
            }
            km.update(black_box(&features))
        })
    });
}

// ============================================================
// Group 5: State estimation
// ============================================================

fn bench_kalman1d(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut k = Kalman1d::builder()
        .process_noise(0.01)
        .measurement_noise(1.0)
        .build()
        .unwrap();
    for _ in 0..1000 {
        let _ = k.update(rng.next_f64());
    }
    c.bench_function("Kalman1d::update", |b| {
        b.iter(|| k.update(black_box(rng.next_f64())).unwrap())
    });
}

fn bench_kalman2d(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut k = Kalman2d::builder()
        .process_noise([[0.01, 0.0], [0.0, 0.01]])
        .measurement_noise(1.0)
        .build()
        .unwrap();
    for _ in 0..1000 {
        k.predict();
        let _ = k.update(rng.next_f64(), [1.0, 0.0]);
    }

    c.bench_function("Kalman2d::predict+update", |b| {
        b.iter(|| {
            k.predict();
            k.update(black_box(rng.next_f64()), black_box([1.0, 0.0]))
                .unwrap()
        })
    });

    c.bench_function("Kalman2d::predict_with_dynamics", |b| {
        b.iter(|| {
            k.predict_with_dynamics(black_box([[1.0, 1.0], [0.0, 1.0]]));
            k.update(black_box(rng.next_f64()), black_box([1.0, 0.0]))
                .unwrap()
        })
    });
}

fn bench_kalman3d(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut k = Kalman3d::builder()
        .process_noise([[0.01, 0.0, 0.0], [0.0, 0.01, 0.0], [0.0, 0.0, 0.01]])
        .measurement_noise(1.0)
        .build()
        .unwrap();
    for _ in 0..1000 {
        k.predict();
        let _ = k.update(rng.next_f64(), [1.0, 0.0, 0.0]);
    }
    c.bench_function("Kalman3d::predict+update", |b| {
        b.iter(|| {
            k.predict();
            k.update(black_box(rng.next_f64()), black_box([1.0, 0.0, 0.0]))
                .unwrap()
        })
    });
}

// ============================================================
// Group 6: Optimizers
// ============================================================

fn bench_online_gd(c: &mut Criterion) {
    let mut rng = Lcg::new(42);

    for dims in [5, 20] {
        let mut opt = OnlineGd::builder()
            .dimensions(dims)
            .learning_rate(0.01)
            .build()
            .unwrap();
        let mut grad: Vec<f64> = (0..dims).map(|_| rng.next_feature()).collect();
        for _ in 0..1000 {
            for v in &mut grad {
                *v = rng.next_feature();
            }
            let _ = opt.step(&grad);
        }
        c.bench_function(&format!("OnlineGd::step (d={dims})"), |b| {
            b.iter(|| {
                for v in &mut grad {
                    *v = rng.next_feature();
                }
                opt.step(black_box(&grad)).unwrap()
            })
        });
    }
}

fn bench_adagrad(c: &mut Criterion) {
    let mut rng = Lcg::new(42);

    for dims in [5, 20] {
        let mut opt = AdaGrad::builder()
            .dimensions(dims)
            .learning_rate(0.1)
            .build()
            .unwrap();
        let mut grad: Vec<f64> = (0..dims).map(|_| rng.next_feature()).collect();
        for _ in 0..1000 {
            for v in &mut grad {
                *v = rng.next_feature();
            }
            let _ = opt.step(&grad);
        }
        c.bench_function(&format!("AdaGrad::step (d={dims})"), |b| {
            b.iter(|| {
                for v in &mut grad {
                    *v = rng.next_feature();
                }
                opt.step(black_box(&grad)).unwrap()
            })
        });
    }
}

fn bench_adam(c: &mut Criterion) {
    let mut rng = Lcg::new(42);

    for dims in [5, 20] {
        let mut opt = Adam::builder()
            .dimensions(dims)
            .learning_rate(0.001)
            .build()
            .unwrap();
        let mut grad: Vec<f64> = (0..dims).map(|_| rng.next_feature()).collect();
        for _ in 0..1000 {
            for v in &mut grad {
                *v = rng.next_feature();
            }
            let _ = opt.step(&grad);
        }
        c.bench_function(&format!("Adam::step (d={dims})"), |b| {
            b.iter(|| {
                for v in &mut grad {
                    *v = rng.next_feature();
                }
                opt.step(black_box(&grad)).unwrap()
            })
        });
    }
}

// ============================================================
// Group 7: Query methods (cold path, reference)
// ============================================================

fn bench_polynomial_coefficients(c: &mut Criterion) {
    let mut rng = Lcg::new(42);

    for degree in [2, 3, 5] {
        let mut pr = PolynomialRegression::builder()
            .degree(degree)
            .intercept(true)
            .build()
            .unwrap();
        for i in 0..1000 {
            let _ = pr.update(i as f64 * 0.01, rng.next_f64());
        }
        c.bench_function(
            &format!("PolynomialRegression::coefficients (deg={degree})"),
            |b| b.iter(|| pr.coefficients()),
        );
    }
}

fn bench_transfer_entropy_query(c: &mut Criterion) {
    let mut rng = Lcg::new(42);

    for bins in [4usize, 8] {
        let mut te = TransferEntropy::builder()
            .bins(bins)
            .lag(1)
            .build()
            .unwrap();
        for _ in 0..1000 {
            te.update(
                (rng.next_f64() as usize) % bins,
                (rng.next_f64() as usize) % bins,
            );
        }
        c.bench_function(&format!("TransferEntropy::te_x_to_y (bins={bins})"), |b| {
            b.iter(|| te.te_x_to_y())
        });
    }
}

fn bench_entropy_query(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut e = Entropy::builder().bins(8).build().unwrap();
    for _ in 0..1000 {
        e.update((rng.next_f64() as usize) % 8);
    }
    c.bench_function("Entropy::entropy (bins=8)", |b| b.iter(|| e.entropy()));
}

// ============================================================
// Group 8: Bandits
// ============================================================

fn bench_ucb1_select(c: &mut Criterion) {
    for k in [2, 5, 10, 25, 50] {
        let mut rng = Lcg::new(42);
        let mut b = Ucb1::builder().arms(k).build().unwrap();
        for _ in 0..(k * 100) {
            let arm = b.select();
            let _ = b.update(arm, rng.next_unit());
        }
        c.bench_function(&format!("Ucb1::select (K={k})"), |bench| {
            bench.iter(|| black_box(b.select()))
        });
    }
}

fn bench_ucb1_update(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    for k in [2, 5, 10, 25, 50] {
        let mut b = Ucb1::builder().arms(k).build().unwrap();
        for _ in 0..(k * 100) {
            let arm = b.select();
            let _ = b.update(arm, rng.next_unit());
        }
        c.bench_function(&format!("Ucb1::update (K={k})"), |bench| {
            let mut arm = 0;
            bench.iter(|| {
                arm = (arm + 1) % k;
                b.update(black_box(arm), black_box(rng.next_unit()))
                    .unwrap()
            })
        });
    }
}

fn bench_ucb1_update_decay(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    for k in [2, 5, 10, 25, 50] {
        let mut b = Ucb1::builder().arms(k).decay(0.99).build().unwrap();
        for _ in 0..(k * 100) {
            let arm = b.select();
            let _ = b.update(arm, rng.next_unit());
        }
        c.bench_function(&format!("Ucb1::update decay=0.99 (K={k})"), |bench| {
            let mut arm = 0;
            bench.iter(|| {
                arm = (arm + 1) % k;
                b.update(black_box(arm), black_box(rng.next_unit()))
                    .unwrap()
            })
        });
    }
}

fn bench_thompson_beta_select(c: &mut Criterion) {
    for k in [2, 5, 10, 25, 50] {
        let mut rng = Lcg::new(42);
        let mut b = ThompsonBeta::builder().arms(k).build().unwrap();
        for _ in 0..(k * 100) {
            let arm = b.select(&mut || rng.next_unit());
            let _ = b.update(arm, rng.next_unit());
        }
        c.bench_function(&format!("ThompsonBeta::select (K={k})"), |bench| {
            bench.iter(|| black_box(b.select(&mut || rng.next_unit())))
        });
    }
}

fn bench_thompson_beta_update(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    for k in [2, 5, 10, 25, 50] {
        let mut b = ThompsonBeta::builder().arms(k).build().unwrap();
        for _ in 0..(k * 100) {
            let arm = b.select(&mut || rng.next_unit());
            let _ = b.update(arm, rng.next_unit());
        }
        c.bench_function(&format!("ThompsonBeta::update (K={k})"), |bench| {
            let mut arm = 0;
            bench.iter(|| {
                arm = (arm + 1) % k;
                b.update(black_box(arm), black_box(rng.next_unit()))
                    .unwrap()
            })
        });
    }
}

fn bench_thompson_gamma_select(c: &mut Criterion) {
    for k in [2, 5, 10, 25, 50] {
        let mut rng = Lcg::new(42);
        let mut b = ThompsonGamma::builder().arms(k).build().unwrap();
        for _ in 0..(k * 100) {
            let arm = b.select(&mut || rng.next_unit());
            let _ = b.update(arm, rng.next_unit() + 0.01);
        }
        c.bench_function(&format!("ThompsonGamma::select (K={k})"), |bench| {
            bench.iter(|| black_box(b.select(&mut || rng.next_unit())))
        });
    }
}

fn bench_epsilon_greedy_select(c: &mut Criterion) {
    for k in [2, 5, 10, 25, 50] {
        let mut rng = Lcg::new(42);
        let mut b = EpsilonGreedy::builder()
            .arms(k)
            .epsilon(0.1)
            .build()
            .unwrap();
        for _ in 0..(k * 100) {
            let arm = b.select(&mut || rng.next_unit());
            let _ = b.update(arm, rng.next_unit());
        }
        c.bench_function(&format!("EpsilonGreedy::select (K={k})"), |bench| {
            bench.iter(|| black_box(b.select(&mut || rng.next_unit())))
        });
    }
}

fn bench_exp3_select(c: &mut Criterion) {
    for k in [2, 5, 10, 25, 50] {
        let mut rng = Lcg::new(42);
        let mut b = Exp3::builder().arms(k).gamma(0.1).build().unwrap();
        for _ in 0..(k * 100) {
            let (arm, prob) = b.select(&mut || rng.next_unit());
            let _ = b.update(arm, rng.next_unit(), prob);
        }
        c.bench_function(&format!("Exp3::select (K={k})"), |bench| {
            bench.iter(|| black_box(b.select(&mut || rng.next_unit())))
        });
    }
}

// ============================================================
// Risk metrics + normalization
// ============================================================

fn bench_lpm(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut lpm = Lpm::builder().target(0.0).order(2).build().unwrap();
    for _ in 0..1000 {
        lpm.update(rng.next_f64() - 50.0);
    }
    c.bench_function("Lpm::update (order=2)", |b| {
        b.iter(|| lpm.update(black_box(rng.next_f64() - 50.0)))
    });
}

fn bench_cvar(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut cv = Cvar::builder().alpha(0.05).build().unwrap();
    for _ in 0..1000 {
        let _ = cv.update(rng.next_f64());
    }
    c.bench_function("Cvar::update (alpha=0.05)", |b| {
        b.iter(|| cv.update(black_box(rng.next_f64())).unwrap())
    });
}

fn bench_zscore_norm(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut zs = ZScoreNorm::<f64>::builder().span(20).build().unwrap();
    for _ in 0..1000 {
        let _ = zs.update(rng.next_f64());
    }
    c.bench_function("ZScoreNorm::<f64>::update", |b| {
        b.iter(|| zs.update(black_box(rng.next_f64())).unwrap())
    });
}

fn bench_minmax_norm(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut mm = MinMaxNorm::<f64>::builder().window(100).build().unwrap();
    for i in 0..1000u64 {
        let _ = mm.update(i, rng.next_f64());
    }
    let mut ts = 1000u64;
    c.bench_function("MinMaxNorm::<f64>::update", |b| {
        b.iter(|| {
            ts += 1;
            mm.update(black_box(ts), black_box(rng.next_f64())).unwrap()
        })
    });
}

// ============================================================
// Distribution drift + BOCPD
// ============================================================

fn bench_dist_drift_update(c: &mut Criterion) {
    let mut rng = Lcg::new(42);
    let mut drift = DistDrift::builder()
        .num_bins(50)
        .min_val(0.0)
        .max_val(100.0)
        .build()
        .unwrap();
    for i in 0..1000u64 {
        drift.update_reference((i % 100) as f64).unwrap();
    }
    c.bench_function("DistDrift::update (50 bins)", |b| {
        b.iter(|| {
            drift.update(black_box(rng.next_f64())).unwrap();
        });
    });
}

fn bench_bocpd_update(c: &mut Criterion) {
    let mut bocpd = Bocpd::builder()
        .max_run_length(200)
        .hazard_lambda(100.0)
        .build()
        .unwrap();
    for i in 0..50 {
        bocpd.update(i as f64).unwrap();
    }
    let mut rng = Lcg::new(42);
    c.bench_function("Bocpd::update (W=200)", |b| {
        b.iter(|| {
            bocpd.update(black_box(rng.next_f64())).unwrap();
        });
    });
}

// ============================================================
// Criterion groups and main
// ============================================================

criterion_group!(
    core_stats,
    bench_welford,
    bench_moments,
    bench_ema,
    bench_asym_ema,
    bench_holt,
    bench_ewma_var,
    bench_covariance,
    bench_harmonic_mean,
    bench_percentile_p50,
    bench_percentile_p99,
    bench_jitter,
    bench_drawdown,
    bench_running_min,
    bench_running_max,
    bench_slew,
    bench_spring,
    bench_dead_band,
    bench_hysteresis,
    bench_level_crossing,
    bench_first_diff,
    bench_second_diff,
    bench_cusum,
    bench_shiryaev_roberts,
    bench_trend_alert,
    bench_adaptive_threshold,
    bench_robust_z,
    bench_error_rate,
);

criterion_group!(
    const_generic,
    bench_autocorrelation,
    bench_cross_correlation,
    bench_entropy,
);

criterion_group!(
    runtime_configured,
    bench_linear_regression,
    bench_ew_linear_regression,
    bench_polynomial_regression,
    bench_transfer_entropy,
);

criterion_group!(
    adaptive_filters,
    bench_lms_filter,
    bench_nlms_filter,
    bench_rls_filter,
    bench_logistic_regression,
    bench_online_kmeans,
);

criterion_group!(
    state_estimation,
    bench_kalman1d,
    bench_kalman2d,
    bench_kalman3d,
);

criterion_group!(optimizers, bench_online_gd, bench_adagrad, bench_adam,);

criterion_group!(
    queries,
    bench_polynomial_coefficients,
    bench_transfer_entropy_query,
    bench_entropy_query,
);

criterion_group!(
    risk_norm,
    bench_lpm,
    bench_cvar,
    bench_zscore_norm,
    bench_minmax_norm,
);

criterion_group!(drift_bocpd, bench_dist_drift_update, bench_bocpd_update,);

criterion_group!(
    bandits,
    bench_ucb1_select,
    bench_ucb1_update,
    bench_ucb1_update_decay,
    bench_thompson_beta_select,
    bench_thompson_beta_update,
    bench_thompson_gamma_select,
    bench_epsilon_greedy_select,
    bench_exp3_select,
);

criterion_main!(
    core_stats,
    const_generic,
    runtime_configured,
    adaptive_filters,
    state_estimation,
    optimizers,
    queries,
    bandits,
    risk_norm,
    drift_bocpd,
);
