//! MLP compute kernels: scalar fast inverse-sqrt + SIMD-tiled GEMV and
//! LayerNorm. The orchestration (layer loop, scratch ping-pong) lives in
//! `crate::mlp`.

#[cfg(all(
    target_arch = "x86_64",
    any(
        target_feature = "avx512f",
        all(target_feature = "avx2", target_feature = "fma"),
    )
))]
use crate::Activation;

/// Fast f32 inverse sqrt via bit manipulation + Newton-Raphson.
/// Used by the scalar LayerNorm fallback on non-SIMD platforms.
#[inline(always)]
pub(crate) fn rsqrt(x: f32) -> f32 {
    let mut y = f32::from_bits(0x5f37_5a86 - (x.to_bits() >> 1));
    y *= (0.5 * x * y).mul_add(-y, 1.5);
    y *= (0.5 * x * y).mul_add(-y, 1.5);
    y
}

#[cfg(all(
    target_arch = "x86_64",
    any(
        target_feature = "avx512f",
        all(target_feature = "avx2", target_feature = "fma"),
    )
))]
#[inline(never)]
#[allow(clippy::many_single_char_names)]
pub(crate) fn layer_norm(
    data: &mut [f32],
    gamma: &[f32],
    beta: &[f32],
    activation: Activation,
) -> bool {
    use crate::kernel::activate::activate_f32;
    use crate::kernel::activate::simd::activate_8wide;
    use core::arch::x86_64::*;

    let n = data.len();
    if n < 8 {
        return false;
    }

    // SAFETY: cfg guarantees AVX2+FMA. All pointer arithmetic stays within
    // slice bounds: i < n_8 <= n, loads/stores of 8 f32 (32 bytes) at
    // offset i are valid because i + 8 <= n_8 + 8 <= n (n_8 = n & !7).
    unsafe {
        let n_8 = n & !7;

        // Pass 1: mean (f32 accumulation, 8-wide)
        let mut sum_v = _mm256_setzero_ps();
        let mut i = 0;
        while i < n_8 {
            sum_v = _mm256_add_ps(sum_v, _mm256_loadu_ps(data.as_ptr().add(i)));
            i += 8;
        }
        let mut sum = hsum256(sum_v);
        while i < n {
            sum += data[i];
            i += 1;
        }
        let mean = sum / n as f32;

        // Pass 2: variance (f32 accumulation, 8-wide FMA)
        let mean_v = _mm256_set1_ps(mean);
        let mut var_v = _mm256_setzero_ps();
        i = 0;
        while i < n_8 {
            let x = _mm256_loadu_ps(data.as_ptr().add(i));
            let d = _mm256_sub_ps(x, mean_v);
            var_v = _mm256_fmadd_ps(d, d, var_v);
            i += 8;
        }
        let mut var = hsum256(var_v);
        while i < n {
            let d = data[i] - mean;
            var = d.mul_add(d, var);
            i += 1;
        }
        let inv_std = {
            let v = _mm_sqrt_ss(_mm_set_ss(var / n as f32 + 1e-5));
            1.0_f32 / _mm_cvtss_f32(v)
        };

        // Pass 3: normalize + affine + activation (8-wide FMA)
        let inv_std_v = _mm256_set1_ps(inv_std);
        i = 0;
        while i < n_8 {
            let x = _mm256_loadu_ps(data.as_ptr().add(i));
            let norm = _mm256_mul_ps(_mm256_sub_ps(x, mean_v), inv_std_v);
            let g = _mm256_loadu_ps(gamma.as_ptr().add(i));
            let b = _mm256_loadu_ps(beta.as_ptr().add(i));
            let val = _mm256_fmadd_ps(g, norm, b);
            match activate_8wide(val, activation) {
                Some(activated) => _mm256_storeu_ps(data.as_mut_ptr().add(i), activated),
                None => return false,
            }
            i += 8;
        }
        while i < n {
            let norm = (data[i] - mean) * inv_std;
            let val = gamma[i].mul_add(norm, beta[i]);
            data[i] = activate_f32(val, activation);
            i += 1;
        }
    }

    true
}

#[cfg(all(
    target_arch = "x86_64",
    any(
        target_feature = "avx512f",
        all(target_feature = "avx2", target_feature = "fma"),
    )
))]
/// Horizontal sum of an 8-lane AVX2 vector.
///
/// # Safety
/// Caller must run on a target with AVX2 enabled.
#[inline(always)]
pub(crate) unsafe fn hsum256(v: core::arch::x86_64::__m256) -> f32 {
    use core::arch::x86_64::*;
    // SAFETY: caller guarantees AVX2 (safety contract on this fn).
    unsafe {
        let hi = _mm256_extractf128_ps(v, 1);
        let lo = _mm256_castps256_ps128(v);
        let sum128 = _mm_add_ps(lo, hi);
        let shuf = _mm_movehdup_ps(sum128);
        let sums = _mm_add_ps(sum128, shuf);
        let shuf2 = _mm_movehl_ps(sums, sums);
        _mm_cvtss_f32(_mm_add_ss(sums, shuf2))
    }
}
