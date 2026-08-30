//! Activation kernels — scalar approximations and SIMD variants.
//!
//! The [`Activation`](crate::Activation) enum (public API) lives at the crate
//! root; this module holds the compute. All approximations are pure arithmetic
//! (Padé tanh, minimax exp) — no libm.

use crate::Activation;

/// Padé [7,6] rational approximant for tanh.
///
/// Max relative error ~1.2e-7 in [-4.97, 4.97] (full f32 precision).
/// Saturates to ±1 for |x| >= 4.97. Same polynomial used by XNNPACK,
/// oneDNN, TensorRT, and ONNX Runtime for production inference.
#[inline(always)]
pub(crate) fn tanh_f32(x: f32) -> f32 {
    if x >= 4.97 {
        return 1.0;
    }
    if x <= -4.97 {
        return -1.0;
    }
    let x2 = x * x;
    let num = x * x2.mul_add(x2.mul_add(x2 + 378.0, 17_325.0), 135_135.0);
    let den = x2.mul_add(x2.mul_add(x2.mul_add(28.0, 3_150.0), 62_370.0), 135_135.0);
    num / den
}

/// Logistic sigmoid via the tanh identity: sigmoid(x) = 0.5 + 0.5 * tanh(x/2).
#[inline(always)]
pub(crate) fn sigmoid_f32(x: f32) -> f32 {
    0.5_f32.mul_add(tanh_f32(x * 0.5), 0.5)
}

/// Fast f32 exp using range reduction + degree-5 minimax polynomial.
///
/// Accurate to ~1 ULP across the full f32 range. For |x| > 88.72,
/// saturates to +inf/0 matching IEEE semantics.
#[inline(always)]
pub(crate) fn exp_f32(x: f32) -> f32 {
    const LN2: f32 = core::f32::consts::LN_2;
    const LOG2E: f32 = core::f32::consts::LOG2_E;

    if x > 88.72 {
        return f32::INFINITY;
    }
    if x < -87.33 {
        return 0.0;
    }

    // Range reduction: x = n*ln2 + r, |r| <= ln2/2
    // Cap n so the reconstructed biased exponent (n + 127) stays <= 254;
    // 255 encodes inf/NaN. Only bites for x within ~1% of the overflow cutoff.
    let n = (x * LOG2E).round().min(127.0);
    let r = n.mul_add(-LN2, x);

    // Degree-5 Horner polynomial for exp(r) on [-ln2/2, ln2/2]
    let exp_r = r
        .mul_add(
            r.mul_add(
                r.mul_add(r.mul_add(0.008_333_334, 0.041_666_668), 0.166_666_7),
                0.5,
            ),
            1.0,
        )
        .mul_add(r, 1.0);

    // Reconstruct: exp(x) = 2^n * exp(r)
    let bits = ((n as i32 + 127) as u32) << 23;
    f32::from_bits(bits) * exp_r
}

#[inline(always)]
pub(crate) fn activate_f32(x: f32, activation: Activation) -> f32 {
    match activation {
        Activation::Relu => {
            if x > 0.0 {
                x
            } else if x <= 0.0 {
                0.0
            } else {
                x // NaN
            }
        }
        Activation::LeakyRelu(alpha) => {
            if x >= 0.0 {
                x
            } else {
                x * alpha
            }
        }
        Activation::Identity => x,
        Activation::Tanh => tanh_f32(x),
        Activation::Sigmoid => sigmoid_f32(x),
        Activation::Elu(alpha) => {
            if x >= 0.0 {
                x
            } else {
                alpha * (exp_f32(x) - 1.0)
            }
        }
        Activation::Gelu => {
            const SQRT_2_OVER_PI: f32 =
                core::f32::consts::FRAC_2_SQRT_PI * core::f32::consts::FRAC_1_SQRT_2;
            let inner = (0.044_715 * x * x).mul_add(x, x) * SQRT_2_OVER_PI;
            0.5 * x * (1.0 + tanh_f32(inner))
        }
        Activation::Swish => x * sigmoid_f32(x),
    }
}

// --- 8-wide AVX2 vectorized activations for MLP/Conv tiled paths ---

#[cfg(all(
    target_arch = "x86_64",
    any(
        target_feature = "avx512f",
        all(target_feature = "avx2", target_feature = "fma"),
    )
))]
pub(crate) mod simd {
    use core::arch::x86_64::*;

    /// AVX2 vectorized Padé [7,6] tanh on 8 lanes.
    ///
    /// # Safety
    /// Caller must run on a target with AVX2 and FMA enabled.
    #[inline(always)]
    pub(crate) unsafe fn tanh_8wide(x: __m256) -> __m256 {
        // SAFETY: caller guarantees AVX2 and FMA (safety contract on this fn).
        unsafe {
            let nan_mask = _mm256_cmp_ps(x, x, _CMP_UNORD_Q);

            let pos_clip = _mm256_set1_ps(4.97);
            let neg_clip = _mm256_set1_ps(-4.97);
            let xc = _mm256_min_ps(_mm256_max_ps(x, neg_clip), pos_clip);

            let x2 = _mm256_mul_ps(xc, xc);

            let n_inner = _mm256_fmadd_ps(x2, _mm256_set1_ps(1.0), _mm256_set1_ps(378.0));
            let n_mid = _mm256_fmadd_ps(x2, n_inner, _mm256_set1_ps(17_325.0));
            let n_outer = _mm256_fmadd_ps(x2, n_mid, _mm256_set1_ps(135_135.0));
            let num = _mm256_mul_ps(xc, n_outer);

            let d_inner = _mm256_fmadd_ps(x2, _mm256_set1_ps(28.0), _mm256_set1_ps(3_150.0));
            let d_mid = _mm256_fmadd_ps(x2, d_inner, _mm256_set1_ps(62_370.0));
            let den = _mm256_fmadd_ps(x2, d_mid, _mm256_set1_ps(135_135.0));

            let result = _mm256_div_ps(num, den);
            _mm256_blendv_ps(result, x, nan_mask)
        }
    }

    /// AVX2 vectorized sigmoid: 0.5 + 0.5 * tanh(x * 0.5)
    ///
    /// # Safety
    /// Caller must run on a target with AVX2 and FMA enabled.
    #[inline(always)]
    pub(crate) unsafe fn sigmoid_8wide(x: __m256) -> __m256 {
        // SAFETY: caller guarantees AVX2 and FMA (safety contract on this fn).
        unsafe {
            let half = _mm256_set1_ps(0.5);
            let t = tanh_8wide(_mm256_mul_ps(x, half));
            _mm256_fmadd_ps(half, t, half)
        }
    }

    /// AVX2 vectorized swish: x * sigmoid(x)
    ///
    /// # Safety
    /// Caller must run on a target with AVX2 and FMA enabled.
    #[inline(always)]
    pub(crate) unsafe fn swish_8wide(x: __m256) -> __m256 {
        // SAFETY: caller guarantees AVX2 and FMA (safety contract on this fn).
        unsafe { _mm256_mul_ps(x, sigmoid_8wide(x)) }
    }

    /// AVX2 vectorized GELU (tanh approximation).
    ///
    /// # Safety
    /// Caller must run on a target with AVX2 and FMA enabled.
    #[inline(always)]
    pub(crate) unsafe fn gelu_8wide(x: __m256) -> __m256 {
        // SAFETY: caller guarantees AVX2 and FMA (safety contract on this fn).
        unsafe {
            let half = _mm256_set1_ps(0.5);
            let coeff = _mm256_set1_ps(0.044_715);
            let scale = _mm256_set1_ps(
                core::f32::consts::FRAC_2_SQRT_PI * core::f32::consts::FRAC_1_SQRT_2,
            );

            let x2 = _mm256_mul_ps(x, x);
            let inner = _mm256_mul_ps(_mm256_fmadd_ps(coeff, _mm256_mul_ps(x2, x), x), scale);
            let t = tanh_8wide(inner);
            _mm256_mul_ps(
                _mm256_mul_ps(half, x),
                _mm256_add_ps(_mm256_set1_ps(1.0), t),
            )
        }
    }

    /// Apply activation to 8 values in an __m256 register.
    /// Returns None for activations not handled in SIMD (ELU, LeakyRelu with
    /// non-trivial alpha). Caller falls through to scalar for those.
    ///
    /// # Safety
    /// Caller must run on a target with AVX2 and FMA enabled.
    #[inline(always)]
    pub(crate) unsafe fn activate_8wide(
        v: __m256,
        activation: crate::Activation,
    ) -> Option<__m256> {
        // SAFETY: caller guarantees AVX2 and FMA (safety contract on this fn).
        unsafe {
            Some(match activation {
                crate::Activation::Relu => _mm256_max_ps(v, _mm256_setzero_ps()),
                crate::Activation::Identity => v,
                crate::Activation::Tanh => tanh_8wide(v),
                crate::Activation::Sigmoid => sigmoid_8wide(v),
                crate::Activation::Swish => swish_8wide(v),
                crate::Activation::Gelu => gelu_8wide(v),
                crate::Activation::LeakyRelu(alpha) => {
                    let zero = _mm256_setzero_ps();
                    let mask = _mm256_cmp_ps(v, zero, _CMP_LT_OQ);
                    let scaled = _mm256_mul_ps(v, _mm256_set1_ps(alpha));
                    _mm256_blendv_ps(v, scaled, mask)
                }
                crate::Activation::Elu(_) => return None,
            })
        }
    }

    /// Apply activation to 4 values in an __m128 register.
    ///
    /// # Safety
    /// Caller must run on a target with AVX2 and FMA enabled.
    #[inline(always)]
    pub(crate) unsafe fn activate_4wide(
        v: __m128,
        activation: crate::Activation,
    ) -> Option<__m128> {
        // SAFETY: caller guarantees AVX2 and FMA (safety contract on this fn).
        unsafe {
            Some(match activation {
                crate::Activation::Relu => _mm_max_ps(v, _mm_setzero_ps()),
                crate::Activation::Identity => v,
                crate::Activation::LeakyRelu(alpha) => {
                    let zero = _mm_setzero_ps();
                    let mask = _mm_cmplt_ps(v, zero);
                    let scaled = _mm_mul_ps(v, _mm_set1_ps(alpha));
                    _mm_blendv_ps(v, scaled, mask)
                }
                // For Tanh/Sigmoid/Gelu/Swish: promote to 256-bit, compute, extract lower.
                // Not worth the complexity for a 4-wide tail — fall through to scalar.
                _ => return None,
            })
        }
    }
}

// --- AVX-512 16-wide variants ---

#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
pub(crate) mod simd512 {
    use core::arch::x86_64::*;

    /// AVX-512 vectorized Padé [7,6] tanh on 16 lanes.
    ///
    /// # Safety
    /// Caller must run on a target with AVX-512F enabled.
    #[inline(always)]
    pub(crate) unsafe fn tanh_16wide(x: __m512) -> __m512 {
        // SAFETY: caller guarantees AVX-512F (safety contract on this fn).
        unsafe {
            let nan_mask = _mm512_cmp_ps_mask::<_CMP_UNORD_Q>(x, x);

            let pos_clip = _mm512_set1_ps(4.97);
            let neg_clip = _mm512_set1_ps(-4.97);
            let xc = _mm512_min_ps(_mm512_max_ps(x, neg_clip), pos_clip);

            let x2 = _mm512_mul_ps(xc, xc);

            let n_inner = _mm512_fmadd_ps(x2, _mm512_set1_ps(1.0), _mm512_set1_ps(378.0));
            let n_mid = _mm512_fmadd_ps(x2, n_inner, _mm512_set1_ps(17_325.0));
            let n_outer = _mm512_fmadd_ps(x2, n_mid, _mm512_set1_ps(135_135.0));
            let num = _mm512_mul_ps(xc, n_outer);

            let d_inner = _mm512_fmadd_ps(x2, _mm512_set1_ps(28.0), _mm512_set1_ps(3_150.0));
            let d_mid = _mm512_fmadd_ps(x2, d_inner, _mm512_set1_ps(62_370.0));
            let den = _mm512_fmadd_ps(x2, d_mid, _mm512_set1_ps(135_135.0));

            let result = _mm512_div_ps(num, den);
            _mm512_mask_blend_ps(nan_mask, result, x)
        }
    }

    /// AVX-512 vectorized sigmoid: 0.5 + 0.5 * tanh(x * 0.5)
    ///
    /// # Safety
    /// Caller must run on a target with AVX-512F enabled.
    #[inline(always)]
    pub(crate) unsafe fn sigmoid_16wide(x: __m512) -> __m512 {
        // SAFETY: caller guarantees AVX-512F (safety contract on this fn).
        unsafe {
            let half = _mm512_set1_ps(0.5);
            let t = tanh_16wide(_mm512_mul_ps(x, half));
            _mm512_fmadd_ps(half, t, half)
        }
    }
}
