//! The number contract, checked by property: fed through `checked_update`
//! (`update` itself is unchecked, like `f64` arithmetic),
//! no reader returns NaN, and none returns infinity except where its
//! documentation says it can. See the crate-level docs.
//!
//! Streams are built from segments chosen to reach the cases that produce
//! `0 / 0` or overflow in naive arithmetic: constant runs, repeats, zeros,
//! strict alternation, and noise at magnitudes from `1e-300` to `1e300`.
//! That is far past the input limits on purpose: `checked_update` must
//! refuse what would overflow and leave the state sound, so the readings
//! are checked after every sample whether it was accepted or not.

use nexus_stats_core::detection::DistributionShift;
use nexus_stats_core::normalization::ZScoreNorm;
use nexus_stats_core::statistics::{
    Amihud, BipowerVariation, Covariance, EwmaVar, HalfLife, HarmonicMean, Hurst, Lpm, Moments,
    Reversion, RollSpread, TwoScaleRv, VarianceRatio, Welford,
};
use nexus_stats_core::{INPUT_LIMIT, INPUT_LIMIT_FOURTH_MOMENT};

/// Upper end of the magnitudes generated: well beyond both input limits.
const WIDE: f64 = 1e300;
use proptest::prelude::*;

/// One stretch of a stream.
#[derive(Debug, Clone)]
enum Segment {
    Constant {
        value: f64,
        len: usize,
    },
    Alternating {
        a: f64,
        b: f64,
        len: usize,
    },
    Noise {
        center: f64,
        scale: f64,
        seed: u64,
        len: usize,
    },
    Ramp {
        start: f64,
        step: f64,
        len: usize,
    },
}

/// A magnitude spread log-uniformly over nearly the whole accepted range,
/// with either sign, and exact zero now and then.
fn magnitude(limit: f64) -> impl Strategy<Value = f64> {
    let top = limit.log10() - 0.5;
    prop_oneof![
        1 => Just(0.0),
        // Down to where squares, then the values themselves, underflow.
        1 => (-300.0..-150.0f64, any::<bool>())
            .prop_map(|(e, neg)| if neg { -(10f64.powf(e)) } else { 10f64.powf(e) }),
        8 => (-150.0..top, any::<bool>())
            .prop_map(|(e, neg): (f64, bool)| if neg { -(10f64.powf(e)) } else { 10f64.powf(e) }),
        3 => (-3.0..6.0f64, any::<bool>())
            .prop_map(|(e, neg)| if neg { -(10f64.powf(e)) } else { 10f64.powf(e) }),
    ]
}

fn segment(limit: f64) -> impl Strategy<Value = Segment> {
    let len = 1usize..40;
    prop_oneof![
        (magnitude(limit), len.clone()).prop_map(|(value, len)| Segment::Constant { value, len }),
        (magnitude(limit), magnitude(limit), len.clone())
            .prop_map(|(a, b, len)| Segment::Alternating { a, b, len }),
        (
            magnitude(limit),
            magnitude(limit),
            any::<u64>(),
            len.clone()
        )
            .prop_map(|(center, scale, seed, len)| Segment::Noise {
                center,
                scale,
                seed,
                len
            }),
        (magnitude(limit), magnitude(limit), len).prop_map(|(start, step, len)| Segment::Ramp {
            start,
            step,
            len
        }),
    ]
}

/// A stream of up to a few hundred samples, every one within `limit`.
fn stream(limit: f64) -> impl Strategy<Value = Vec<f64>> {
    prop::collection::vec(segment(limit), 1..8).prop_map(move |segments| {
        let mut out = Vec::new();
        for s in segments {
            match s {
                Segment::Constant { value, len } => out.extend(std::iter::repeat_n(value, len)),
                Segment::Alternating { a, b, len } => {
                    out.extend((0..len).map(|i| if i % 2 == 0 { a } else { b }));
                }
                Segment::Noise {
                    center,
                    scale,
                    mut seed,
                    len,
                } => out.extend((0..len).map(|_| {
                    seed = seed
                        .wrapping_mul(6_364_136_223_846_793_005)
                        .wrapping_add(1_442_695_040_888_963_407);
                    let u = (seed >> 11) as f64 / (1u64 << 53) as f64 - 0.5;
                    scale.mul_add(u, center)
                })),
                Segment::Ramp { start, step, len } => {
                    out.extend((0..len).map(|i| step.mul_add(i as f64, start)));
                }
            }
        }
        for x in &mut out {
            *x = x.clamp(-limit, limit);
        }
        out
    })
}

/// A smoothing weight: mostly ordinary, sometimes at either edge of what a
/// builder accepts, where `1 - alpha` is one rounding step from 1 or 0.
fn weight() -> impl Strategy<Value = f64> {
    prop_oneof![
        8 => 0.001..0.999f64,
        1 => Just(f64::EPSILON),
        1 => Just(1.0 - f64::EPSILON),
        1 => Just(1e-9),
        1 => Just(1.0 - 1e-9),
    ]
}

/// A finite number.
fn number(x: f64, what: &str) -> Result<(), TestCaseError> {
    prop_assert!(x.is_finite(), "{what} = {x}");
    Ok(())
}

/// A finite number that is not negative.
fn amount(x: f64, what: &str) -> Result<(), TestCaseError> {
    prop_assert!(x.is_finite() && x >= 0.0, "{what} = {x}");
    Ok(())
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(400))]

    #[test]
    fn ewma_var(
        xs in stream(WIDE),
        alpha in weight(),
        seed in prop::option::of((magnitude(INPUT_LIMIT), magnitude(INPUT_LIMIT))),
    ) {
        let mut builder = EwmaVar::builder().alpha(alpha);
        if let Some((mean, spread)) = seed {
            // Any mean within the limit, any variance within its square.
            builder = builder.seed(mean, spread * spread);
        }
        let mut ew = builder.build().unwrap();
        if seed.is_some() {
            let r = ew.last().unwrap();
            number(r.mean, "seeded mean")?;
            amount(r.variance, "seeded variance")?;
        }
        for &x in &xs {
            if let Ok(Some(r)) = ew.checked_update(x) {
                number(r.mean, "mean")?;
                amount(r.variance, "variance")?;
                amount(r.std_dev(), "std_dev")?;
                prop_assert_eq!(ew.last(), Some(r));
            }
        }
    }

    #[test]
    fn zscore_norm(
        xs in stream(WIDE),
        alpha in weight(),
        seed in prop::option::of((magnitude(INPUT_LIMIT), magnitude(INPUT_LIMIT))),
    ) {
        let mut builder = ZScoreNorm::<f64>::builder().alpha(alpha);
        if let Some((mean, spread)) = seed {
            builder = builder.seed(mean, spread * spread);
        }
        let mut zs = builder.build().unwrap();
        for &x in &xs {
            // Documented: infinite against zero scale. Never NaN.
            if let Ok(Some(z)) = zs.checked_update(x) {
                prop_assert!(!z.is_nan(), "z of {x}");
            }
            if let Ok(Some(z)) = zs.checked_normalize(x) {
                prop_assert!(!z.is_nan(), "normalize of {x}");
            }
        }
    }

    #[test]
    fn welford(xs in stream(WIDE)) {
        let mut w = Welford::new();
        for &x in &xs {
            let _ = w.checked_update(x);
            if let Some(m) = w.mean() { number(m, "mean")?; }
            if let Some(v) = w.variance() { amount(v, "variance")?; }
            if let Some(v) = w.population_variance() { amount(v, "population variance")?; }
            if let Some(s) = w.std_dev() { amount(s, "std_dev")?; }
        }
    }

    #[test]
    fn moments(xs in stream(WIDE)) {
        let mut m = Moments::new();
        for &x in &xs {
            let _ = m.checked_update(x);
            if let Some(v) = m.mean() { number(v, "mean")?; }
            if let Some(v) = m.variance() { amount(v, "variance")?; }
            if let Some(v) = m.skewness() { number(v, "skewness")?; }
            if let Some(v) = m.excess_kurtosis() { number(v, "excess kurtosis")?; }
            if let Some(v) = m.kurtosis() { amount(v, "kurtosis")?; }
        }
    }

    #[test]
    fn distribution_shift(xs in stream(WIDE)) {
        let mut d = DistributionShift::builder().fast_window(8).build().unwrap();
        for &x in &xs {
            if let Ok(Some(s)) = d.checked_update(x) {
                number(s.skewness, "skewness shift")?;
                number(s.excess_kurtosis, "kurtosis shift")?;
            }
        }
    }

    #[test]
    fn covariance(xs in stream(WIDE), ys in stream(WIDE)) {
        let mut c = Covariance::new();
        for (&x, &y) in xs.iter().zip(&ys) {
            let _ = c.checked_update(x, y);
            if let Some(v) = c.covariance() { number(v, "covariance")?; }
            if let Some(v) = c.variance_x() { amount(v, "variance x")?; }
            if let Some(v) = c.variance_y() { amount(v, "variance y")?; }
            if let Some(r) = c.correlation() {
                prop_assert!((-1.0..=1.0).contains(&r), "correlation = {r}");
            }
        }
    }

    #[test]
    fn half_life(xs in stream(WIDE)) {
        let mut h = HalfLife::new();
        for &x in &xs {
            let _ = h.checked_update(x);
            if let Some(phi) = h.ar1_coefficient() { number(phi, "phi")?; }
            if let Some(Reversion::Reverting { half_life }) = h.reversion() {
                amount(half_life, "half life")?;
            }
        }
    }

    #[test]
    fn roll_spread(xs in stream(WIDE), alpha in weight()) {
        let mut r = RollSpread::builder().alpha(alpha).min_samples(3).build().unwrap();
        for &x in &xs {
            if let Ok(Some(e)) = r.checked_update(x) {
                amount(e.spread, "spread")?;
                number(e.autocovariance, "autocovariance")?;
                // A spread exactly when the autocovariance is negative; the
                // model is contradicted exactly when it is positive.
                prop_assert_eq!(e.spread > 0.0, e.autocovariance < 0.0);
                prop_assert_eq!(e.model_fits(), e.autocovariance <= 0.0);
            }
        }
    }

    #[test]
    fn bipower_variation(xs in stream(WIDE)) {
        let mut b = BipowerVariation::builder().min_samples(3).build().unwrap();
        for &x in &xs {
            if let Ok(Some(r)) = b.checked_update(x) {
                amount(r.realized_variance, "realized variance")?;
                amount(r.bipower_variation, "bipower variation")?;
                amount(r.jump_variation(), "jump variation")?;
                if let Some(share) = r.jump_ratio() {
                    prop_assert!((0.0..=1.0).contains(&share), "jump ratio = {share}");
                }
            }
        }
    }

    #[test]
    fn two_scale_rv(xs in stream(WIDE), k in 2usize..9) {
        let mut t = TwoScaleRv::builder().k(k).min_samples(2 * k as u64).build().unwrap();
        for &x in &xs {
            if let Ok(Some(e)) = t.checked_update(x) {
                amount(e.two_scale_variance, "two-scale variance")?;
                amount(e.realized_variance, "realized variance")?;
                amount(e.noise_variance, "noise variance")?;
                amount(e.two_scale_volatility(), "two-scale volatility")?;
            }
        }
    }

    #[test]
    fn variance_ratio(xs in stream(WIDE), q in 2usize..40, share in 0.0005..1.0f64) {
        // Up to the largest alpha the builder accepts for this q.
        let alpha = (share * 2.0 / q as f64).min(1.0 - f64::EPSILON);
        let mut v = VarianceRatio::builder().q(q).alpha(alpha).build().unwrap();
        for &x in &xs {
            if let Ok(Some(ratio)) = v.checked_update(x) {
                amount(ratio, "variance ratio")?;
            }
        }
    }

    #[test]
    fn hurst(xs in stream(WIDE), window in prop_oneof![Just(32usize), Just(47), Just(64), Just(100)]) {
        let mut h = Hurst::builder().window_size(window).build().unwrap();
        let mut accepted = Vec::new();
        for &x in &xs {
            if h.checked_update(x).is_ok() {
                accepted.push(x);
            }
            let estimate = h.hurst();
            if let Some(e) = estimate { number(e, "hurst")?; }
            // A window of one repeated value has no exponent, whatever the
            // value: not the 1.0 that rounding residue would suggest.
            if accepted.len() >= window {
                let recent = &accepted[accepted.len() - window..];
                if recent.iter().all(|v| v == &recent[0]) {
                    prop_assert_eq!(estimate, None, "constant window of {}", recent[0]);
                }
            }
        }
    }

    #[test]
    fn hurst_of_a_stuck_feed_is_undefined(value in magnitude(INPUT_LIMIT), window in 32usize..200) {
        let mut h = Hurst::builder().window_size(window).build().unwrap();
        for _ in 0..window {
            h.checked_update(value).unwrap();
        }
        prop_assert_eq!(h.hurst(), None);
    }

    #[test]
    fn harmonic_mean(xs in stream(WIDE)) {
        let mut h = HarmonicMean::new();
        for &x in &xs {
            // Non-positive, vanishing and oversized samples are rejected; the
            // rest must leave a finite positive mean.
            let _ = h.checked_update(x);
            if let Some(m) = h.mean() {
                prop_assert!(m.is_finite() && m > 0.0, "harmonic mean = {m}");
            }
        }
    }

    #[test]
    fn lower_partial_moment(xs in stream(WIDE), target in magnitude(WIDE), order in 0u32..17) {
        let mut l = Lpm::builder().target(target).order(order).build().unwrap();
        for &x in &xs {
            // A term that would overflow the sum is rejected, not folded.
            let _ = l.checked_update(x);
            if let Some(v) = l.lpm() { amount(v, "lpm")?; }
        }
    }

    #[test]
    fn amihud(rets in stream(WIDE), vols in stream(WIDE), alpha in weight()) {
        let mut a = Amihud::builder().alpha(alpha).build().unwrap();
        for (&r, &v) in rets.iter().zip(&vols) {
            // Negative volume and a ratio too large to represent are
            // refused.
            let _ = a.checked_update(r, v);
            if let Some(i) = a.illiq() { amount(i, "illiq")?; }
        }
    }
}

/// `checked_update` enforces the limits, inclusively and with the right
/// error, and a rejected sample changes nothing.
#[test]
fn checked_update_rejects_what_would_overflow() {
    use nexus_stats_core::DataError::{Infinite, NotANumber, OutOfRange};

    let over = INPUT_LIMIT * 2.0;
    let mut ew = EwmaVar::builder().alpha(0.1).build().unwrap();
    assert_eq!(ew.checked_update(over), Err(OutOfRange));
    assert_eq!(ew.checked_update(-over), Err(OutOfRange));
    assert_eq!(ew.checked_update(f64::NAN), Err(NotANumber));
    assert_eq!(ew.checked_update(f64::NEG_INFINITY), Err(Infinite));
    assert_eq!(ew.count(), 0);
    assert!(ew.checked_update(INPUT_LIMIT).is_ok());
    assert!(ew.checked_update(-INPUT_LIMIT).is_ok());
    assert_eq!(ew.count(), 2);

    let mut zs = ZScoreNorm::<f64>::builder().alpha(0.1).build().unwrap();
    assert_eq!(zs.checked_update(over), Err(OutOfRange));
    assert_eq!(zs.count(), 0);

    assert_eq!(Welford::new().checked_update(over), Err(OutOfRange));
    assert_eq!(Covariance::new().checked_update(1.0, over), Err(OutOfRange));
    assert_eq!(Covariance::new().checked_update(over, 1.0), Err(OutOfRange));
    assert_eq!(HalfLife::new().checked_update(over), Err(OutOfRange));
    assert_eq!(
        BipowerVariation::new().checked_update(over),
        Err(OutOfRange)
    );
    assert_eq!(
        RollSpread::builder()
            .alpha(0.1)
            .build()
            .unwrap()
            .checked_update(over),
        Err(OutOfRange)
    );
    assert_eq!(
        TwoScaleRv::builder()
            .k(2)
            .build()
            .unwrap()
            .checked_update(over),
        Err(OutOfRange)
    );
    assert_eq!(
        VarianceRatio::builder()
            .q(2)
            .alpha(0.1)
            .build()
            .unwrap()
            .checked_update(over),
        Err(OutOfRange)
    );
    assert_eq!(
        Hurst::builder().build().unwrap().checked_update(over),
        Err(OutOfRange)
    );

    // The fourth-moment types have the tighter limit.
    let mut m = Moments::new();
    assert_eq!(
        m.checked_update(INPUT_LIMIT_FOURTH_MOMENT * 2.0),
        Err(OutOfRange)
    );
    assert_eq!(m.count(), 0);
    assert!(m.checked_update(INPUT_LIMIT_FOURTH_MOMENT).is_ok());
    let mut d = DistributionShift::builder().build().unwrap();
    assert_eq!(
        d.checked_update(INPUT_LIMIT_FOURTH_MOMENT * 2.0),
        Err(OutOfRange)
    );
    assert_eq!(d.count(), 0);

    // A reciprocal must stay within the limit too.
    let mut h = HarmonicMean::new();
    assert_eq!(h.checked_update(1e-121), Err(OutOfRange));
    assert_eq!(h.checked_update(0.0), Err(OutOfRange));
    assert_eq!(h.checked_update(-1.0), Err(OutOfRange));
    assert_eq!(h.checked_update(over), Err(OutOfRange));
    assert_eq!(h.count(), 0);
    assert!(h.checked_update(1e-119).is_ok());

    // A high order is checked on the result; a rejected sample is not
    // counted.
    let mut l = Lpm::builder().target(0.0).order(8).build().unwrap();
    assert_eq!(l.checked_update(-1e100), Err(OutOfRange));
    assert_eq!(l.count(), 0);
    assert!(l.checked_update(-1e30).is_ok());
}

/// `update` is unchecked, like `f64` arithmetic: it takes whatever it is
/// given and returns its reading directly. A NaN stays in the state until
/// `reset`; a value too large to square overflows. `checked_update` refuses
/// both and leaves the state alone.
#[test]
fn update_is_unchecked_and_reset_recovers() {
    use nexus_stats_core::DataError::{Infinite, NotANumber, OutOfRange};

    // A NaN poisons the running mean and variance for good...
    let mut w = Welford::new();
    w.update(1.0);
    w.update(3.0);
    assert_eq!(w.mean(), Some(2.0));
    w.update(f64::NAN);
    w.update(5.0);
    assert!(w.mean().unwrap().is_nan());
    assert!(w.variance().unwrap().is_nan());
    // ...until the caller resets.
    w.reset();
    w.update(1.0);
    w.update(3.0);
    assert_eq!(w.mean(), Some(2.0));

    // The checked path refuses it and the reading is untouched.
    let mut w = Welford::new();
    w.checked_update(1.0).unwrap();
    w.checked_update(3.0).unwrap();
    assert_eq!(w.checked_update(f64::NAN), Err(NotANumber));
    assert_eq!(w.checked_update(f64::INFINITY), Err(Infinite));
    assert_eq!(w.checked_update(1e200), Err(OutOfRange));
    assert_eq!((w.count(), w.mean()), (2, Some(2.0)));

    // A finite value too large to square: IEEE overflow, as in NumPy.
    let mut w = Welford::new();
    w.update(1e200);
    w.update(-1e200);
    assert_eq!(w.variance(), Some(f64::INFINITY));
    // Within the limit the same stream shape is an ordinary number.
    let mut w = Welford::new();
    w.update(INPUT_LIMIT);
    w.update(-INPUT_LIMIT);
    assert!(w.variance().unwrap().is_finite());

    // A type that returns its reading from `update` hands it back directly.
    let mut ew = EwmaVar::builder().alpha(0.5).build().unwrap();
    assert_eq!(ew.update(0.0), None);
    assert!(ew.update(2.0).is_some());
    let reading = ew.update(f64::NAN).unwrap();
    assert!(reading.mean.is_nan());
    ew.reset();
    assert_eq!(ew.update(0.0), None);
    assert!((ew.update(2.0).unwrap().variance - 2.0).abs() < 1e-12);

    // Domain checks are on the checked side only: a non-positive sample is
    // folded into a harmonic mean as its (meaningless) reciprocal.
    let mut h = HarmonicMean::new();
    h.update(-4.0);
    assert_eq!(h.mean(), Some(-4.0));
    assert_eq!(HarmonicMean::new().checked_update(-4.0), Err(OutOfRange));
}
