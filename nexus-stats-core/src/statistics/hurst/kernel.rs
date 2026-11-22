//! The inner loop of the rescaled range, in scalar and vector forms.
//!
//! One pass over a stretch of log prices gives the three sums the rescaled
//! range is made of. The vector forms do the same arithmetic two (SSE2) or
//! four (AVX2) returns at a time, so their sums differ from the scalar ones
//! only in rounding: the squares are added in a different order, and AVX2
//! fuses its multiply-adds. AVX2 is used when the build enables `avx2` and
//! `fma`; SSE2 is part of every x86-64 build.

use crate::math::MulAdd;

/// What one pass over a stretch yields.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(super) struct StretchSums {
    /// Sum of squared deviations of the returns from their mean.
    pub(super) squares: f64,
    /// The highest value of the returns' running sum about the mean. Never
    /// below zero: the sum starts there.
    pub(super) highest: f64,
    /// The lowest value of that running sum. Never above zero.
    pub(super) lowest: f64,
}

/// The sums over the returns between consecutive `log_prices`, whose mean
/// is `mean`. `log_prices` must not be empty.
#[inline]
pub(super) fn stretch_sums(log_prices: &[f64], mean: f64) -> StretchSums {
    // Internal: the one caller always passes a stretch of several prices.
    debug_assert!(!log_prices.is_empty());
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "avx2",
        target_feature = "fma"
    ))]
    {
        // SAFETY: this branch is compiled only when the build enables AVX2
        // and FMA, so every CPU the build targets has them.
        unsafe { avx2(log_prices, mean) }
    }
    #[cfg(all(
        target_arch = "x86_64",
        not(all(target_feature = "avx2", target_feature = "fma"))
    ))]
    {
        // SAFETY: SSE2 is part of the x86-64 baseline.
        unsafe { sse2(log_prices, mean) }
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        let start = StretchSums {
            squares: 0.0,
            highest: 0.0,
            lowest: 0.0,
        };
        scalar(log_prices, mean, 0, start)
    }
}

/// Continues `sums` over the returns from index `from` to the end. With
/// `from` zero and zeroed sums, it is the whole computation.
fn scalar(log_prices: &[f64], mean: f64, from: usize, mut sums: StretchSums) -> StretchSums {
    let first = log_prices[0];
    for index in from..log_prices.len() - 1 {
        let log_price = log_prices[index + 1];
        let deviation = log_price - log_prices[index] - mean;
        sums.squares += deviation * deviation;

        let running = ((index + 1) as f64).fma(-mean, log_price - first);
        // PERF: plain compares compile to one max and one min.
        if running > sums.highest {
            sums.highest = running;
        }
        if running < sums.lowest {
            sums.lowest = running;
        }
    }
    sums
}

#[cfg(all(
    target_arch = "x86_64",
    not(all(target_feature = "avx2", target_feature = "fma"))
))]
#[target_feature(enable = "sse2")]
fn sse2(log_prices: &[f64], mean: f64) -> StretchSums {
    use core::arch::x86_64::{
        _mm_add_pd, _mm_cvtsd_f64, _mm_loadu_pd, _mm_max_pd, _mm_min_pd, _mm_mul_pd, _mm_set_pd,
        _mm_set1_pd, _mm_setzero_pd, _mm_sub_pd, _mm_unpackhi_pd,
    };
    const WIDTH: usize = 2;

    let returns = log_prices.len() - 1;
    let whole = returns - returns % (2 * WIDTH);
    let (mean_lanes, first) = (_mm_set1_pd(mean), _mm_set1_pd(log_prices[0]));
    // PERF: two sets of sums, so two blocks are in flight at once.
    let mut squares = [_mm_setzero_pd(); 2];
    let mut highest = [_mm_setzero_pd(); 2];
    let mut lowest = [_mm_setzero_pd(); 2];
    // Each lane's position in the stretch, as a float.
    let mut step = [_mm_set_pd(2.0, 1.0), _mm_set_pd(4.0, 3.0)];
    let advance = _mm_set1_pd(2.0 * WIDTH as f64);

    let start = log_prices.as_ptr();
    for index in (0..whole).step_by(2 * WIDTH) {
        for set in 0..2 {
            let at = index + set * WIDTH;
            // SAFETY: `at + WIDTH <= whole`, and `whole` is at most one less
            // than the slice's length, so both loads stay inside it.
            let (from, to) =
                unsafe { (_mm_loadu_pd(start.add(at)), _mm_loadu_pd(start.add(at + 1))) };
            let deviation = _mm_sub_pd(_mm_sub_pd(to, from), mean_lanes);
            squares[set] = _mm_add_pd(squares[set], _mm_mul_pd(deviation, deviation));

            let running = _mm_sub_pd(_mm_sub_pd(to, first), _mm_mul_pd(step[set], mean_lanes));
            highest[set] = _mm_max_pd(running, highest[set]);
            lowest[set] = _mm_min_pd(running, lowest[set]);
            step[set] = _mm_add_pd(step[set], advance);
        }
    }

    // Fold the two sets, then two lanes to one.
    let squares = _mm_add_pd(squares[0], squares[1]);
    let highest = _mm_max_pd(highest[0], highest[1]);
    let lowest = _mm_min_pd(lowest[0], lowest[1]);
    let sums = StretchSums {
        squares: _mm_cvtsd_f64(squares) + _mm_cvtsd_f64(_mm_unpackhi_pd(squares, squares)),
        highest: _mm_cvtsd_f64(_mm_max_pd(highest, _mm_unpackhi_pd(highest, highest))),
        lowest: _mm_cvtsd_f64(_mm_min_pd(lowest, _mm_unpackhi_pd(lowest, lowest))),
    };
    scalar(log_prices, mean, whole, sums)
}

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx2",
    target_feature = "fma"
))]
#[target_feature(enable = "avx2,fma")]
fn avx2(log_prices: &[f64], mean: f64) -> StretchSums {
    use core::arch::x86_64::{
        _mm_add_pd, _mm_cvtsd_f64, _mm_max_pd, _mm_min_pd, _mm_unpackhi_pd, _mm256_add_pd,
        _mm256_castpd256_pd128, _mm256_extractf128_pd, _mm256_fmadd_pd, _mm256_fnmadd_pd,
        _mm256_loadu_pd, _mm256_max_pd, _mm256_min_pd, _mm256_set_pd, _mm256_set1_pd,
        _mm256_setzero_pd, _mm256_sub_pd,
    };
    const WIDTH: usize = 4;

    let returns = log_prices.len() - 1;
    let whole = returns - returns % (2 * WIDTH);
    let (mean_lanes, first) = (_mm256_set1_pd(mean), _mm256_set1_pd(log_prices[0]));
    // PERF: two sets of sums, so two blocks are in flight at once.
    let mut squares = [_mm256_setzero_pd(); 2];
    let mut highest = [_mm256_setzero_pd(); 2];
    let mut lowest = [_mm256_setzero_pd(); 2];
    // Each lane's position in the stretch, as a float.
    let mut step = [
        _mm256_set_pd(4.0, 3.0, 2.0, 1.0),
        _mm256_set_pd(8.0, 7.0, 6.0, 5.0),
    ];
    let advance = _mm256_set1_pd(2.0 * WIDTH as f64);

    let start = log_prices.as_ptr();
    for index in (0..whole).step_by(2 * WIDTH) {
        for set in 0..2 {
            let at = index + set * WIDTH;
            // SAFETY: `at + WIDTH <= whole`, and `whole` is at most one less
            // than the slice's length, so both loads stay inside it.
            let (from, to) = unsafe {
                (
                    _mm256_loadu_pd(start.add(at)),
                    _mm256_loadu_pd(start.add(at + 1)),
                )
            };
            let deviation = _mm256_sub_pd(_mm256_sub_pd(to, from), mean_lanes);
            squares[set] = _mm256_fmadd_pd(deviation, deviation, squares[set]);

            let running = _mm256_fnmadd_pd(step[set], mean_lanes, _mm256_sub_pd(to, first));
            highest[set] = _mm256_max_pd(running, highest[set]);
            lowest[set] = _mm256_min_pd(running, lowest[set]);
            step[set] = _mm256_add_pd(step[set], advance);
        }
    }

    // Fold the two sets, then four lanes to two, then two to one.
    let squares = _mm256_add_pd(squares[0], squares[1]);
    let highest = _mm256_max_pd(highest[0], highest[1]);
    let lowest = _mm256_min_pd(lowest[0], lowest[1]);
    let squares = _mm_add_pd(
        _mm256_castpd256_pd128(squares),
        _mm256_extractf128_pd::<1>(squares),
    );
    let highest = _mm_max_pd(
        _mm256_castpd256_pd128(highest),
        _mm256_extractf128_pd::<1>(highest),
    );
    let lowest = _mm_min_pd(
        _mm256_castpd256_pd128(lowest),
        _mm256_extractf128_pd::<1>(lowest),
    );
    let sums = StretchSums {
        squares: _mm_cvtsd_f64(squares) + _mm_cvtsd_f64(_mm_unpackhi_pd(squares, squares)),
        highest: _mm_cvtsd_f64(_mm_max_pd(highest, _mm_unpackhi_pd(highest, highest))),
        lowest: _mm_cvtsd_f64(_mm_min_pd(lowest, _mm_unpackhi_pd(lowest, lowest))),
    };
    scalar(log_prices, mean, whole, sums)
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec::Vec;

    fn log_prices(len: usize) -> Vec<f64> {
        let mut x = 0.3f64;
        let mut log_price = 100.0f64.ln();
        (0..len)
            .map(|_| {
                x = 3.99 * x * (1.0 - x);
                log_price += 0.01 * (x - 0.5);
                log_price
            })
            .collect()
    }

    fn mean_of(log_prices: &[f64]) -> f64 {
        (log_prices[log_prices.len() - 1] - log_prices[0]) / (log_prices.len() - 1) as f64
    }

    fn close(a: f64, b: f64) -> bool {
        (a - b).abs() <= 1e-12 * a.abs().max(b.abs()).max(1e-300)
    }

    #[test]
    fn the_kernel_in_use_agrees_with_the_scalar_one_at_every_length() {
        // Every length from 1 return up: whole blocks, leftovers, and none.
        let series = log_prices(300);
        for len in 2..=series.len() {
            for offset in [0, 1, 7] {
                if offset + len > series.len() {
                    continue;
                }
                let stretch = &series[offset..offset + len];
                let mean = mean_of(stretch);
                let start = StretchSums {
                    squares: 0.0,
                    highest: 0.0,
                    lowest: 0.0,
                };
                let (got, want) = (stretch_sums(stretch, mean), scalar(stretch, mean, 0, start));
                assert!(
                    close(got.squares, want.squares)
                        && close(got.highest, want.highest)
                        && close(got.lowest, want.lowest),
                    "len {len} offset {offset}: {got:?} vs {want:?}"
                );
            }
        }
    }

    /// The sums from the definitions, with no code shared with the kernels:
    /// the returns, then their deviations, then the running sum.
    fn reference(log_prices: &[f64], mean: f64) -> StretchSums {
        let returns: Vec<f64> = log_prices
            .windows(2)
            .map(|pair| pair[1] - pair[0])
            .collect();
        let deviations: Vec<f64> = returns.iter().map(|r| r - mean).collect();
        let mut running = 0.0;
        let (mut highest, mut lowest) = (0.0f64, 0.0f64);
        for deviation in &deviations {
            running += deviation;
            highest = highest.max(running);
            lowest = lowest.min(running);
        }
        StretchSums {
            squares: deviations.iter().map(|d| d * d).sum(),
            highest,
            lowest,
        }
    }

    #[test]
    fn agrees_with_the_definitions() {
        // The running sum here accumulates rounding the kernels do not, so
        // the tolerance is looser than between kernels.
        let series = log_prices(200);
        for len in [2, 3, 5, 8, 9, 16, 17, 33, 64, 100, 200] {
            let stretch = &series[..len];
            let mean = mean_of(stretch);
            let (got, want) = (stretch_sums(stretch, mean), reference(stretch, mean));
            let near = |a: f64, b: f64| (a - b).abs() <= 1e-9 * a.abs().max(b.abs()).max(1e-12);
            assert!(
                near(got.squares, want.squares)
                    && near(got.highest, want.highest)
                    && near(got.lowest, want.lowest),
                "len {len}: {got:?} vs {want:?}"
            );
        }
    }

    #[test]
    fn zero_is_always_within_the_range() {
        // A stretch that only rises about its mean, and one that only falls.
        for stretch in [[0.0, 3.0, 4.0, 4.5, 4.6], [0.0, -3.0, -4.0, -4.5, -4.6]] {
            let sums = stretch_sums(&stretch, mean_of(&stretch));
            assert!(sums.highest >= 0.0 && sums.lowest <= 0.0, "{sums:?}");
        }
    }

    #[test]
    fn a_nan_price_reaches_the_squares_and_is_skipped_by_the_range() {
        // A comparison with NaN is false, so the highest and lowest pass it
        // by, in every version. The squares carry it.
        let mut series = log_prices(40);
        series[17] = f64::NAN;
        let sums = stretch_sums(&series, 0.0);
        assert!(sums.squares.is_nan());
        assert!(
            sums.highest.is_finite() && sums.lowest.is_finite(),
            "{sums:?}"
        );
    }
}
