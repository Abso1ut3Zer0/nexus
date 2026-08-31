//! AVX2+FMA vectorized ln/exp for packed f64x4.
//!
//! Available when compiled with `-C target-feature=+avx2,+fma` (or `-C target-cpu=native`
//! on any CPU since Haswell / Zen1). Algorithms match fdlibm/musl coefficients.
//! FMA Horner evaluation gives strictly better precision (single rounding per step)
//! and lower latency than separate mul+add.

#![allow(clippy::excessive_precision)]

#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::*;

use nexus_stats_core::math::{exp as scalar_exp, ln as scalar_ln};

// fdlibm ln polynomial coefficients (Remez on [0, 0.1716])
const LG1: f64 = 6.666_666_666_666_735_13e-01;
const LG2: f64 = 3.999_999_999_940_941_9e-01;
const LG3: f64 = 2.857_142_874_366_239_1e-01;
const LG4: f64 = 2.222_219_843_214_978_4e-01;
const LG5: f64 = 1.818_357_216_161_805e-01;
const LG6: f64 = 1.531_383_769_920_937_3e-01;
const LG7: f64 = 1.479_819_860_511_658_6e-01;

const LN2_HI: f64 = 6.931_471_803_691_238e-01;
const LN2_LO: f64 = 1.908_214_929_270_585e-10;

// musl/Cephes exp range reduction constants
const LN2_INV: f64 = core::f64::consts::LOG2_E;
const EXP_C1: f64 = 6.931_457_519_531_25e-01; // ln(2) high (Cody-Waite)
const EXP_C2: f64 = 1.428_606_820_309_417_2e-06; // ln(2) low

// musl exp polynomial (minimax on [-ln(2)/2, ln(2)/2])
const EP1: f64 = 1.666_666_666_666_666_6e-01;
const EP2: f64 = -2.777_777_777_701_559_3e-03;
const EP3: f64 = 6.613_756_321_437_934_4e-05;
const EP4: f64 = -1.653_390_220_546_525_2e-06;
const EP5: f64 = 4.138_136_797_057_238_5e-08;

/// Compute ln(x) for 4 packed f64 values using the fdlibm algorithm.
///
/// # Safety
///
/// Requires AVX2+FMA. All inputs must be positive finite f64.
#[inline]
#[cfg(target_arch = "x86_64")]
#[allow(clippy::many_single_char_names)]
unsafe fn ln_f64x4(x: __m256d) -> __m256d {
    // SAFETY: caller guarantees AVX2+FMA (safety contract on this fn).
    unsafe {
        let one = _mm256_set1_pd(1.0);
        let half = _mm256_set1_pd(0.5);
        let two = _mm256_set1_pd(2.0);
        let sqrt2 = _mm256_set1_pd(core::f64::consts::SQRT_2);
        let ln2_hi = _mm256_set1_pd(LN2_HI);
        let ln2_lo = _mm256_set1_pd(LN2_LO);

        let mantissa_mask = _mm256_set1_epi64x(0x000F_FFFF_FFFF_FFFFu64 as i64);
        let one_bits = _mm256_set1_epi64x(0x3FF0_0000_0000_0000u64 as i64);
        let bias = _mm256_set1_epi64x(1023);

        let bits = _mm256_castpd_si256(x);

        // Extract mantissa ∈ [1, 2)
        let m = _mm256_castsi256_pd(_mm256_or_si256(
            _mm256_and_si256(bits, mantissa_mask),
            one_bits,
        ));

        // Exponent as i64
        let k_i = _mm256_sub_epi64(_mm256_srli_epi64(bits, 52), bias);

        // i64 → f64 via magic number trick (valid for |k| < 2^51)
        let magic = _mm256_set1_pd(6_755_399_441_055_744.0); // 2^52 + 2^51
        let magic_i = _mm256_castpd_si256(magic);
        let k = _mm256_sub_pd(_mm256_castsi256_pd(_mm256_add_epi64(k_i, magic_i)), magic);

        // If m > sqrt(2): m *= 0.5, k += 1
        let gt = _mm256_cmp_pd(m, sqrt2, _CMP_GT_OQ);
        let m = _mm256_blendv_pd(m, _mm256_mul_pd(m, half), gt);
        let k = _mm256_blendv_pd(k, _mm256_add_pd(k, one), gt);

        // f = m - 1, s = f / (2 + f)
        let f = _mm256_sub_pd(m, one);
        let s = _mm256_div_pd(f, _mm256_add_pd(two, f));
        let s2 = _mm256_mul_pd(s, s);

        // FMA Horner: R(s²) = s² * (Lg1 + s²*(Lg2 + ...))
        let mut r = _mm256_set1_pd(LG7);
        r = _mm256_fmadd_pd(r, s2, _mm256_set1_pd(LG6));
        r = _mm256_fmadd_pd(r, s2, _mm256_set1_pd(LG5));
        r = _mm256_fmadd_pd(r, s2, _mm256_set1_pd(LG4));
        r = _mm256_fmadd_pd(r, s2, _mm256_set1_pd(LG3));
        r = _mm256_fmadd_pd(r, s2, _mm256_set1_pd(LG2));
        r = _mm256_fmadd_pd(r, s2, _mm256_set1_pd(LG1));
        r = _mm256_mul_pd(r, s2);

        // hfsq = 0.5 * f * f
        let hfsq = _mm256_mul_pd(half, _mm256_mul_pd(f, f));

        // result = k*ln2_hi + (f - hfsq + s*(hfsq + R) + k*ln2_lo)
        let sr = _mm256_mul_pd(s, _mm256_add_pd(hfsq, r));
        _mm256_add_pd(
            _mm256_fmadd_pd(k, ln2_lo, sr),
            _mm256_fmadd_pd(k, ln2_hi, _mm256_sub_pd(f, hfsq)),
        )
    }
}

/// Compute exp(x) for 4 packed f64 values using the musl/Cephes algorithm.
///
/// # Safety
///
/// Requires AVX2+FMA. Inputs should be in a reasonable range (not ±huge).
#[inline]
#[cfg(target_arch = "x86_64")]
unsafe fn exp_f64x4(x: __m256d) -> __m256d {
    // SAFETY: caller guarantees AVX2+FMA (safety contract on this fn).
    unsafe {
        let ln2_inv = _mm256_set1_pd(LN2_INV);
        let c1 = _mm256_set1_pd(EXP_C1);
        let c2 = _mm256_set1_pd(EXP_C2);
        let one = _mm256_set1_pd(1.0);
        let two = _mm256_set1_pd(2.0);

        // Range reduction: k = round(x / ln(2)), r = x - k*ln(2)
        let kf = _mm256_round_pd(_mm256_mul_pd(x, ln2_inv), _MM_FROUND_TO_NEAREST_INT);
        // Clamp: k < -1023 produces invalid exponent bits (NaN/negative).
        // k = -1023 → scale = 0.0 → exp(x) = 0, correct for x < -708.
        let kf = _mm256_max_pd(kf, _mm256_set1_pd(-1023.0));

        // Cody-Waite: r = x - k*C1 - k*C2
        // FMA: r = -(k*C1 - x) then r = -(k*C2 - r) = r - k*C2
        let r = _mm256_fnmadd_pd(kf, c2, _mm256_fnmadd_pd(kf, c1, x));

        // FMA Horner: t = r² * (P1 + r*(P2 + r*(P3 + r*(P4 + r*P5))))
        let r2 = _mm256_mul_pd(r, r);
        let mut p = _mm256_set1_pd(EP5);
        p = _mm256_fmadd_pd(p, r, _mm256_set1_pd(EP4));
        p = _mm256_fmadd_pd(p, r, _mm256_set1_pd(EP3));
        p = _mm256_fmadd_pd(p, r, _mm256_set1_pd(EP2));
        p = _mm256_fmadd_pd(p, r, _mm256_set1_pd(EP1));
        let t = _mm256_mul_pd(r2, p);

        // musl reconstruction: exp(r) = 1 - ((r*t)/(t-2) - r)
        let denom = _mm256_sub_pd(t, two);
        let frac = _mm256_div_pd(_mm256_mul_pd(r, t), denom);
        let exp_r = _mm256_sub_pd(one, _mm256_sub_pd(frac, r));

        // Scale by 2^k: set exponent bits
        let k_i = _mm256_cvtpd_epi32(kf);
        let k_i64 = _mm256_cvtepi32_epi64(k_i);
        let bias = _mm256_set1_epi64x(1023);
        let exp_bits = _mm256_slli_epi64(_mm256_add_epi64(k_i64, bias), 52);
        let scale = _mm256_castsi256_pd(exp_bits);

        _mm256_mul_pd(exp_r, scale)
    }
}

#[inline]
#[cfg(target_arch = "x86_64")]
pub fn ln_inplace(buf: &mut [f64]) {
    let len = buf.len();
    let mut i = 0;

    // SAFETY: AVX2+FMA availability guaranteed by target_feature cfg.
    // All values in buf are positive (guaranteed by BOCPD: a > 0, b > 0).
    unsafe {
        while i + 4 <= len {
            let v = _mm256_loadu_pd(buf.as_ptr().add(i));
            let result = ln_f64x4(v);
            _mm256_storeu_pd(buf.as_mut_ptr().add(i), result);
            i += 4;
        }
    }

    for v in &mut buf[i..] {
        *v = scalar_ln(*v);
    }
}

#[inline]
#[cfg(target_arch = "x86_64")]
pub fn exp_sum(buf: &[f64], offset: f64) -> f64 {
    let len = buf.len();
    let mut i = 0;
    let mut sum: f64;

    // SAFETY: AVX2+FMA availability guaranteed by target_feature cfg.
    unsafe {
        let offset_v = _mm256_set1_pd(offset);
        // 4 independent accumulators to hide exp latency (~20 cycle throughput).
        let mut acc0 = _mm256_setzero_pd();
        let mut acc1 = _mm256_setzero_pd();
        let mut acc2 = _mm256_setzero_pd();
        let mut acc3 = _mm256_setzero_pd();

        while i + 16 <= len {
            let v0 = _mm256_loadu_pd(buf.as_ptr().add(i));
            let v1 = _mm256_loadu_pd(buf.as_ptr().add(i + 4));
            let v2 = _mm256_loadu_pd(buf.as_ptr().add(i + 8));
            let v3 = _mm256_loadu_pd(buf.as_ptr().add(i + 12));
            acc0 = _mm256_add_pd(acc0, exp_f64x4(_mm256_sub_pd(v0, offset_v)));
            acc1 = _mm256_add_pd(acc1, exp_f64x4(_mm256_sub_pd(v1, offset_v)));
            acc2 = _mm256_add_pd(acc2, exp_f64x4(_mm256_sub_pd(v2, offset_v)));
            acc3 = _mm256_add_pd(acc3, exp_f64x4(_mm256_sub_pd(v3, offset_v)));
            i += 16;
        }

        // Drain remaining 4-wide chunks
        while i + 4 <= len {
            let v = _mm256_loadu_pd(buf.as_ptr().add(i));
            acc0 = _mm256_add_pd(acc0, exp_f64x4(_mm256_sub_pd(v, offset_v)));
            i += 4;
        }

        // Reduce 4 accumulators → 1
        acc0 = _mm256_add_pd(_mm256_add_pd(acc0, acc1), _mm256_add_pd(acc2, acc3));

        // Horizontal sum
        let hi = _mm256_extractf128_pd(acc0, 1);
        let lo = _mm256_castpd256_pd128(acc0);
        let pair = _mm_add_pd(lo, hi);
        let high_lane = _mm_unpackhi_pd(pair, pair);
        sum = _mm_cvtsd_f64(_mm_add_sd(pair, high_lane));
    }

    for &v in &buf[i..] {
        sum += scalar_exp(v - offset);
    }

    sum
}
