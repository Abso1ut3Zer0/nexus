//! The unchecked side of the `update` / `checked_update` split, checked by
//! property. `update` validates nothing, so it must stay safe on anything:
//! it may leave the readings without meaning, but it must never panic, and
//! `reset()` must put the type back exactly where a fresh one starts.
//!
//! Each type is fed a hostile stream (NaN, infinities, the largest and
//! smallest floats, signed zeros) with every reader called after every
//! sample, then reset and fed a clean stream, and its readings compared
//! with those of a fresh instance fed the same clean stream.

use nexus_stats_core::detection::DistributionShift;
use nexus_stats_core::normalization::ZScoreNorm;
use nexus_stats_core::statistics::{
    Amihud, BipowerVariation, Covariance, EwmaVar, HalfLife, HarmonicMean, HitRate, Hurst, Lpm,
    Moments, RollSpread, TwoScaleRv, VarianceRatio, Welford,
};
use proptest::prelude::*;

/// Anything an `f64` can be, weighted towards the values that break
/// arithmetic.
fn hostile() -> impl Strategy<Value = f64> {
    prop_oneof![
        3 => Just(f64::NAN),
        2 => Just(f64::INFINITY),
        2 => Just(f64::NEG_INFINITY),
        1 => Just(f64::MAX),
        1 => Just(f64::MIN),
        1 => Just(1e300),
        1 => Just(-1e300),
        1 => Just(0.0),
        1 => Just(-0.0),
        1 => Just(f64::MIN_POSITIVE),
        1 => Just(5e-324),
        6 => -1e3..1e3f64,
        2 => any::<f64>(),
    ]
}

fn hostile_stream() -> impl Strategy<Value = Vec<f64>> {
    prop::collection::vec(hostile(), 1..300)
}

/// Ordinary positive data, the same for every case.
fn clean() -> impl Iterator<Item = f64> {
    let mut seed = 0x9E37_79B9_7F4A_7C15u64;
    (0..400).map(move |_| {
        seed = seed
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        100.0 + (seed >> 11) as f64 / (1u64 << 53) as f64
    })
}

/// Feeds `bad` through `feed` reading after every sample, resets, then
/// requires the readings on clean data to match a fresh instance's.
fn survives_and_resets<T>(
    make: impl Fn() -> T,
    feed: impl Fn(&mut T, f64, f64),
    reset: impl Fn(&mut T),
    read: impl Fn(&T) -> String,
    bad: &[f64],
) -> Result<(), TestCaseError> {
    let mut used = make();
    let mut previous = 1.0;
    for &x in bad {
        feed(&mut used, x, previous);
        let _ = read(&used);
        previous = x;
    }
    reset(&mut used);
    let mut fresh = make();
    let mut previous = 1.0;
    for x in clean() {
        feed(&mut used, x, previous);
        feed(&mut fresh, x, previous);
        prop_assert_eq!(read(&used), read(&fresh));
        previous = x;
    }
    Ok(())
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]

    #[test]
    fn update_never_panics_and_reset_restores(bad in hostile_stream()) {
        survives_and_resets(
            Welford::new,
            |t, x, _| t.update(x),
            Welford::reset,
            |t| format!("{:?}", (t.count(), t.mean(), t.variance(), t.std_dev(), t.m2())),
            &bad,
        )?;
        survives_and_resets(
            Moments::new,
            |t, x, _| t.update(x),
            Moments::reset,
            |t| format!(
                "{:?}",
                (t.count(), t.mean(), t.variance(), t.skewness(), t.kurtosis(), t.excess_kurtosis())
            ),
            &bad,
        )?;
        survives_and_resets(
            Covariance::new,
            Covariance::update,
            Covariance::reset,
            |t| format!(
                "{:?}",
                (t.count(), t.mean_x(), t.variance_y(), t.covariance(), t.correlation())
            ),
            &bad,
        )?;
        survives_and_resets(
            || EwmaVar::builder().alpha(0.1).build().unwrap(),
            |t, x, _| { let _ = t.update(x); },
            EwmaVar::reset,
            |t| format!("{:?}", (t.count(), t.last(), t.last().map(|r| r.std_dev()))),
            &bad,
        )?;
        survives_and_resets(
            || ZScoreNorm::<f64>::builder().alpha(0.1).build().unwrap(),
            |t, x, y| { let _ = t.update(x); let _ = t.normalize(y); },
            ZScoreNorm::reset,
            |t| format!("{:?}", (t.count(), t.baseline(), t.normalize(100.5))),
            &bad,
        )?;
        survives_and_resets(
            HalfLife::new,
            |t, x, _| t.update(x),
            HalfLife::reset,
            |t| format!("{:?}", (t.count(), t.ar1_coefficient(), t.reversion())),
            &bad,
        )?;
        survives_and_resets(
            || RollSpread::builder().alpha(0.1).build().unwrap(),
            |t, x, _| { let _ = t.update(x); },
            RollSpread::reset,
            |t| format!("{:?}", (t.count(), t.last(), t.last().map(|r| r.model_fits()))),
            &bad,
        )?;
        survives_and_resets(
            BipowerVariation::new,
            |t, x, _| { let _ = t.update(x); },
            BipowerVariation::reset,
            |t| format!(
                "{:?}",
                (t.count(), t.last(), t.last().map(|r| (r.jump_variation(), r.jump_ratio())))
            ),
            &bad,
        )?;
        survives_and_resets(
            || TwoScaleRv::builder().k(5).build().unwrap(),
            |t, x, _| { let _ = t.update(x); },
            TwoScaleRv::reset,
            |t| format!(
                "{:?}",
                (t.count(), t.last(), t.last().map(|r| r.two_scale_volatility()))
            ),
            &bad,
        )?;
        survives_and_resets(
            || VarianceRatio::builder().q(5).alpha(0.05).build().unwrap(),
            |t, x, _| { let _ = t.update(x); },
            VarianceRatio::reset,
            |t| format!("{:?}", (t.count(), t.variance_ratio())),
            &bad,
        )?;
        survives_and_resets(
            || Hurst::builder().window_size(64).build().unwrap(),
            |t, x, _| t.update(x),
            Hurst::reset,
            |t| format!("{:?}", (t.count(), t.hurst())),
            &bad,
        )?;
        survives_and_resets(
            HarmonicMean::new,
            |t, x, _| t.update(x),
            HarmonicMean::reset,
            |t| format!("{:?}", (t.count(), t.mean())),
            &bad,
        )?;
        for order in [0, 1, 2, 16] {
            survives_and_resets(
                || Lpm::builder().target(100.5).order(order).build().unwrap(),
                |t, x, _| t.update(x),
                Lpm::reset,
                |t| format!("{:?}", (t.count(), t.lpm())),
                &bad,
            )?;
        }
        survives_and_resets(
            || Amihud::builder().alpha(0.1).build().unwrap(),
            |t, x, y| { let _ = t.update(x, y); },
            Amihud::reset,
            |t| format!("{:?}", (t.count(), t.illiq())),
            &bad,
        )?;
        survives_and_resets(
            || HitRate::builder().alpha(0.1).build().unwrap(),
            |t, x, y| t.update(x - 100.5, y - 100.5),
            HitRate::reset,
            |t| format!("{:?}", (t.count(), t.hit_rate(), t.ew_hit_rate())),
            &bad,
        )?;
        survives_and_resets(
            || DistributionShift::builder().build().unwrap(),
            |t, x, _| { let _ = t.update(x); },
            DistributionShift::reset,
            |t| format!("{:?}", (t.count(), t.last(), t.is_primed())),
            &bad,
        )?;
    }
}

/// Where the arithmetic carries a NaN, the reading shows it: a poisoned
/// state must not read as a clean zero.
#[test]
fn a_nan_is_not_reported_as_zero() {
    let mut lpm = Lpm::semivariance(0.0).unwrap();
    lpm.update(-1.0);
    lpm.update(f64::NAN);
    assert!(lpm.lpm().unwrap().is_nan());

    let mut tsrv = TwoScaleRv::builder().k(2).min_samples(4).build().unwrap();
    for price in [100.0, 101.0, 100.0, 101.0, f64::NAN, 100.0, 101.0] {
        let _ = tsrv.update(price);
    }
    assert!(tsrv.last().unwrap().two_scale_variance.is_nan());

    let mut roll = RollSpread::builder()
        .alpha(0.1)
        .min_samples(3)
        .build()
        .unwrap();
    for price in [100.0, 101.0, 100.0, f64::NAN, 100.0, 101.0] {
        let _ = roll.update(price);
    }
    assert!(roll.last().unwrap().spread.is_nan());

    let mut bv = BipowerVariation::builder().min_samples(3).build().unwrap();
    for price in [100.0, 101.0, 100.5, f64::NAN, 100.0] {
        let _ = bv.update(price);
    }
    assert!(bv.last().unwrap().jump_variation().is_nan());
}
