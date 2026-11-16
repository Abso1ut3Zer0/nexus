//! Vectorized math for BOCPD inner loops.
//!
//! Dispatches to AVX2 (4 f64 at a time) when compiled with `+avx2,+fma`,
//! otherwise falls back to scalar. Same fdlibm/musl coefficients,
//! same ~15-digit precision, just in packed form.

#[allow(dead_code)]
mod scalar;

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx2",
    target_feature = "fma"
))]
mod avx2;

/// Compute ln(x) in-place for each element. All values must be positive.
#[inline]
pub fn ln_inplace(buf: &mut [f64]) {
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "avx2",
        target_feature = "fma"
    ))]
    {
        avx2::ln_inplace(buf);
    }

    #[cfg(not(all(
        target_arch = "x86_64",
        target_feature = "avx2",
        target_feature = "fma"
    )))]
    {
        scalar::ln_inplace(buf);
    }
}

/// Compute sum of exp(x - offset) for each element.
#[inline]
pub fn exp_sum(buf: &[f64], offset: f64) -> f64 {
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "avx2",
        target_feature = "fma"
    ))]
    {
        avx2::exp_sum(buf, offset)
    }

    #[cfg(not(all(
        target_arch = "x86_64",
        target_feature = "avx2",
        target_feature = "fma"
    )))]
    {
        scalar::exp_sum(buf, offset)
    }
}

/// The AVX2 kernels against the scalar ones they replace, over lengths that
/// exercise the 16-wide, 4-wide and scalar tails and over the full finite
/// range each kernel accepts. Compiled only on an `+avx2,+fma` build.
#[cfg(all(
    test,
    target_arch = "x86_64",
    target_feature = "avx2",
    target_feature = "fma"
))]
mod parity {
    use super::{avx2, scalar};

    const LENS: [usize; 8] = [0, 1, 3, 4, 7, 16, 21, 37];

    fn uniform(seed: &mut u64) -> f64 {
        *seed ^= *seed << 13;
        *seed ^= *seed >> 7;
        *seed ^= *seed << 17;
        (*seed >> 11) as f64 / (1u64 << 53) as f64
    }

    fn close(a: f64, b: f64, rel: f64) -> bool {
        (a - b).abs() <= rel.mul_add(b.abs(), 1e-14)
    }

    #[test]
    fn ln_inplace_matches_scalar_across_the_positive_range() {
        let mut seed = 0x9E37_79B9_7F4A_7C15u64;
        for &len in &LENS {
            // 1e-300 ..= 1e300, log-uniform, plus the exact 1.0 that lands on ln = 0.
            let mut buf: Vec<f64> = (0..len)
                .map(|_| 10f64.powf(uniform(&mut seed).mul_add(600.0, -300.0)))
                .collect();
            if len > 2 {
                buf[2] = 1.0;
            }
            let mut want = buf.clone();
            scalar::ln_inplace(&mut want);
            avx2::ln_inplace(&mut buf);
            for (i, (&got, &w)) in buf.iter().zip(&want).enumerate() {
                assert!(close(got, w, 1e-13), "len {len} idx {i}: {got} vs {w}");
            }
        }
    }

    /// The exp kernel lane by lane: four copies of one value go through the
    /// 4-wide path, so the sum is 4·exp(x) and any lane error is visible
    /// without the accumulation in the way.
    #[test]
    fn exp_kernel_matches_scalar_per_element() {
        let mut seed = 0x2545_F491_4F6C_DD1Du64;
        let mut worst = (0.0f64, 0.0f64, 0.0f64, 0.0f64);
        for _ in 0..4096 {
            let x = uniform(&mut seed).mul_add(700.0, -700.0);
            let got = avx2::exp_sum(&[x, x, x, x], 0.0) / 4.0;
            let want = nexus_stats_core::math::exp(x);
            let err = (got - want).abs() / want.abs().max(1e-300);
            if err > worst.0 {
                worst = (err, x, got, want);
            }
        }
        assert!(
            worst.0 <= 1e-13,
            "worst relative error {} at x = {}: {} vs {}",
            worst.0,
            worst.1,
            worst.2,
            worst.3
        );
    }

    #[test]
    fn exp_sum_matches_scalar_across_the_finite_range() {
        let mut seed = 0x2545_F491_4F6C_DD1Du64;
        // Two spans: the full range the kernel accepts (where the largest term
        // dominates the sum) and a narrow one where every term is comparable,
        // so a per-lane error cannot hide behind exp(0) = 1.
        for &span in &[700.0, 5.0] {
            for &len in &LENS {
                // Offsets relative to the max, as BOCPD uses it: x - offset in [-span, 0].
                let buf: Vec<f64> = (0..len)
                    .map(|_| uniform(&mut seed).mul_add(span, -span))
                    .collect();
                let offset = buf
                    .iter()
                    .copied()
                    .fold(f64::NEG_INFINITY, f64::max)
                    .max(0.0);
                let want = scalar::exp_sum(&buf, offset);
                let got = avx2::exp_sum(&buf, offset);
                assert!(
                    close(got, want, 1e-12),
                    "span {span} len {len}: {got} vs {want}"
                );
            }
        }
    }
}
