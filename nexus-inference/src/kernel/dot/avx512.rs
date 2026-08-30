#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::*;

use super::scalar;

/// Horizontal sum of a 16-lane AVX-512 vector.
///
/// # Safety
/// Caller must run on a target with AVX-512F enabled.
#[inline]
#[cfg(target_arch = "x86_64")]
unsafe fn hsum_f32(v: __m512) -> f32 {
    // SAFETY: caller guarantees AVX-512F (safety contract on this fn).
    unsafe {
        let lo = _mm512_castps512_ps256(v);
        let hi = _mm256_castpd_ps(_mm512_extractf64x4_pd(_mm512_castps_pd(v), 1));
        let sum = _mm256_add_ps(lo, hi);
        let hi128 = _mm256_extractf128_ps(sum, 1);
        let lo128 = _mm256_castps256_ps128(sum);
        let sum128 = _mm_add_ps(lo128, hi128);
        let shuf = _mm_movehdup_ps(sum128);
        let sums = _mm_add_ps(sum128, shuf);
        let shuf2 = _mm_movehl_ps(sums, sums);
        _mm_cvtss_f32(_mm_add_ss(sums, shuf2))
    }
}

#[inline]
#[cfg(target_arch = "x86_64")]
pub fn dot_f32(a: &[f32], b: &[f32]) -> f32 {
    let len = a.len();
    let mut i = 0;

    // SAFETY: AVX-512F guaranteed by target_feature cfg on parent module.
    // All pointer offsets satisfy i + N <= len before access.
    let sum = unsafe {
        let mut acc0 = _mm512_setzero_ps();
        let mut acc1 = _mm512_setzero_ps();
        let mut acc2 = _mm512_setzero_ps();
        let mut acc3 = _mm512_setzero_ps();

        while i + 64 <= len {
            let a0 = _mm512_loadu_ps(a.as_ptr().add(i));
            let b0 = _mm512_loadu_ps(b.as_ptr().add(i));
            let a1 = _mm512_loadu_ps(a.as_ptr().add(i + 16));
            let b1 = _mm512_loadu_ps(b.as_ptr().add(i + 16));
            let a2 = _mm512_loadu_ps(a.as_ptr().add(i + 32));
            let b2 = _mm512_loadu_ps(b.as_ptr().add(i + 32));
            let a3 = _mm512_loadu_ps(a.as_ptr().add(i + 48));
            let b3 = _mm512_loadu_ps(b.as_ptr().add(i + 48));
            acc0 = _mm512_fmadd_ps(a0, b0, acc0);
            acc1 = _mm512_fmadd_ps(a1, b1, acc1);
            acc2 = _mm512_fmadd_ps(a2, b2, acc2);
            acc3 = _mm512_fmadd_ps(a3, b3, acc3);
            i += 64;
        }

        while i + 16 <= len {
            let av = _mm512_loadu_ps(a.as_ptr().add(i));
            let bv = _mm512_loadu_ps(b.as_ptr().add(i));
            acc0 = _mm512_fmadd_ps(av, bv, acc0);
            i += 16;
        }

        acc0 = _mm512_add_ps(_mm512_add_ps(acc0, acc1), _mm512_add_ps(acc2, acc3));

        hsum_f32(acc0)
    };

    sum + scalar::dot_f32(&a[i..], &b[i..])
}

/// 4 simultaneous f32 dot products sharing input loads.
/// 2 accumulators per neuron (8 total) to hide FMA latency.
#[inline]
#[cfg(target_arch = "x86_64")]
pub fn dot4_f32(rows: &[f32], input: &[f32]) -> [f32; 4] {
    let in_size = input.len();
    let mut i = 0;

    // SAFETY: AVX-512F guaranteed by target_feature cfg on parent module.
    // Row pointers: rows.len() == 4 * in_size, offsets k * in_size + i where k < 4.
    // Input pointer: i + N <= in_size before every access.
    let sums = unsafe {
        let mut a0a = _mm512_setzero_ps();
        let mut a0b = _mm512_setzero_ps();
        let mut a1a = _mm512_setzero_ps();
        let mut a1b = _mm512_setzero_ps();
        let mut a2a = _mm512_setzero_ps();
        let mut a2b = _mm512_setzero_ps();
        let mut a3a = _mm512_setzero_ps();
        let mut a3b = _mm512_setzero_ps();

        let r0 = rows.as_ptr();
        let r1 = r0.add(in_size);
        let r2 = r1.add(in_size);
        let r3 = r2.add(in_size);
        let inp = input.as_ptr();

        while i + 32 <= in_size {
            let x0 = _mm512_loadu_ps(inp.add(i));
            let x1 = _mm512_loadu_ps(inp.add(i + 16));

            a0a = _mm512_fmadd_ps(_mm512_loadu_ps(r0.add(i)), x0, a0a);
            a0b = _mm512_fmadd_ps(_mm512_loadu_ps(r0.add(i + 16)), x1, a0b);
            a1a = _mm512_fmadd_ps(_mm512_loadu_ps(r1.add(i)), x0, a1a);
            a1b = _mm512_fmadd_ps(_mm512_loadu_ps(r1.add(i + 16)), x1, a1b);
            a2a = _mm512_fmadd_ps(_mm512_loadu_ps(r2.add(i)), x0, a2a);
            a2b = _mm512_fmadd_ps(_mm512_loadu_ps(r2.add(i + 16)), x1, a2b);
            a3a = _mm512_fmadd_ps(_mm512_loadu_ps(r3.add(i)), x0, a3a);
            a3b = _mm512_fmadd_ps(_mm512_loadu_ps(r3.add(i + 16)), x1, a3b);

            i += 32;
        }

        if i + 16 <= in_size {
            let x = _mm512_loadu_ps(inp.add(i));
            a0a = _mm512_fmadd_ps(_mm512_loadu_ps(r0.add(i)), x, a0a);
            a1a = _mm512_fmadd_ps(_mm512_loadu_ps(r1.add(i)), x, a1a);
            a2a = _mm512_fmadd_ps(_mm512_loadu_ps(r2.add(i)), x, a2a);
            a3a = _mm512_fmadd_ps(_mm512_loadu_ps(r3.add(i)), x, a3a);
            i += 16;
        }

        a0a = _mm512_add_ps(a0a, a0b);
        a1a = _mm512_add_ps(a1a, a1b);
        a2a = _mm512_add_ps(a2a, a2b);
        a3a = _mm512_add_ps(a3a, a3b);

        [hsum_f32(a0a), hsum_f32(a1a), hsum_f32(a2a), hsum_f32(a3a)]
    };

    let mut out = sums;
    for k in i..in_size {
        let x = input[k];
        out[0] += rows[k] * x;
        out[1] += rows[in_size + k] * x;
        out[2] += rows[2 * in_size + k] * x;
        out[3] += rows[3 * in_size + k] * x;
    }
    out
}

/// 8 simultaneous f32 dot products returning batched `__m256`.
/// 2 accumulators per row (16 total, fits in 32 ZMM registers).
#[inline]
#[cfg(target_arch = "x86_64")]
pub fn dot8_f32_m256(rows: &[f32], input: &[f32]) -> __m256 {
    let in_size = input.len();
    let mut i = 0;

    // SAFETY: AVX-512F guaranteed by target_feature cfg on parent module.
    // Row pointers: rows.len() == 8 * in_size, offsets k * in_size + i where k < 8.
    // Input pointer: i + N <= in_size before every access.
    unsafe {
        let mut a0a = _mm512_setzero_ps();
        let mut a0b = _mm512_setzero_ps();
        let mut a1a = _mm512_setzero_ps();
        let mut a1b = _mm512_setzero_ps();
        let mut a2a = _mm512_setzero_ps();
        let mut a2b = _mm512_setzero_ps();
        let mut a3a = _mm512_setzero_ps();
        let mut a3b = _mm512_setzero_ps();
        let mut a4a = _mm512_setzero_ps();
        let mut a4b = _mm512_setzero_ps();
        let mut a5a = _mm512_setzero_ps();
        let mut a5b = _mm512_setzero_ps();
        let mut a6a = _mm512_setzero_ps();
        let mut a6b = _mm512_setzero_ps();
        let mut a7a = _mm512_setzero_ps();
        let mut a7b = _mm512_setzero_ps();

        let r0 = rows.as_ptr();
        let r1 = r0.add(in_size);
        let r2 = r1.add(in_size);
        let r3 = r2.add(in_size);
        let r4 = r3.add(in_size);
        let r5 = r4.add(in_size);
        let r6 = r5.add(in_size);
        let r7 = r6.add(in_size);
        let inp = input.as_ptr();

        while i + 32 <= in_size {
            let x0 = _mm512_loadu_ps(inp.add(i));
            let x1 = _mm512_loadu_ps(inp.add(i + 16));

            a0a = _mm512_fmadd_ps(_mm512_loadu_ps(r0.add(i)), x0, a0a);
            a0b = _mm512_fmadd_ps(_mm512_loadu_ps(r0.add(i + 16)), x1, a0b);
            a1a = _mm512_fmadd_ps(_mm512_loadu_ps(r1.add(i)), x0, a1a);
            a1b = _mm512_fmadd_ps(_mm512_loadu_ps(r1.add(i + 16)), x1, a1b);
            a2a = _mm512_fmadd_ps(_mm512_loadu_ps(r2.add(i)), x0, a2a);
            a2b = _mm512_fmadd_ps(_mm512_loadu_ps(r2.add(i + 16)), x1, a2b);
            a3a = _mm512_fmadd_ps(_mm512_loadu_ps(r3.add(i)), x0, a3a);
            a3b = _mm512_fmadd_ps(_mm512_loadu_ps(r3.add(i + 16)), x1, a3b);
            a4a = _mm512_fmadd_ps(_mm512_loadu_ps(r4.add(i)), x0, a4a);
            a4b = _mm512_fmadd_ps(_mm512_loadu_ps(r4.add(i + 16)), x1, a4b);
            a5a = _mm512_fmadd_ps(_mm512_loadu_ps(r5.add(i)), x0, a5a);
            a5b = _mm512_fmadd_ps(_mm512_loadu_ps(r5.add(i + 16)), x1, a5b);
            a6a = _mm512_fmadd_ps(_mm512_loadu_ps(r6.add(i)), x0, a6a);
            a6b = _mm512_fmadd_ps(_mm512_loadu_ps(r6.add(i + 16)), x1, a6b);
            a7a = _mm512_fmadd_ps(_mm512_loadu_ps(r7.add(i)), x0, a7a);
            a7b = _mm512_fmadd_ps(_mm512_loadu_ps(r7.add(i + 16)), x1, a7b);

            i += 32;
        }

        if i + 16 <= in_size {
            let x = _mm512_loadu_ps(inp.add(i));
            a0a = _mm512_fmadd_ps(_mm512_loadu_ps(r0.add(i)), x, a0a);
            a1a = _mm512_fmadd_ps(_mm512_loadu_ps(r1.add(i)), x, a1a);
            a2a = _mm512_fmadd_ps(_mm512_loadu_ps(r2.add(i)), x, a2a);
            a3a = _mm512_fmadd_ps(_mm512_loadu_ps(r3.add(i)), x, a3a);
            a4a = _mm512_fmadd_ps(_mm512_loadu_ps(r4.add(i)), x, a4a);
            a5a = _mm512_fmadd_ps(_mm512_loadu_ps(r5.add(i)), x, a5a);
            a6a = _mm512_fmadd_ps(_mm512_loadu_ps(r6.add(i)), x, a6a);
            a7a = _mm512_fmadd_ps(_mm512_loadu_ps(r7.add(i)), x, a7a);
            i += 16;
        }

        a0a = _mm512_add_ps(a0a, a0b);
        a1a = _mm512_add_ps(a1a, a1b);
        a2a = _mm512_add_ps(a2a, a2b);
        a3a = _mm512_add_ps(a3a, a3b);
        a4a = _mm512_add_ps(a4a, a4b);
        a5a = _mm512_add_ps(a5a, a5b);
        a6a = _mm512_add_ps(a6a, a6b);
        a7a = _mm512_add_ps(a7a, a7b);

        // Stage 1: __m512 → __m256
        let r0_256 = _mm256_add_ps(
            _mm512_castps512_ps256(a0a),
            _mm256_castpd_ps(_mm512_extractf64x4_pd(_mm512_castps_pd(a0a), 1)),
        );
        let r1_256 = _mm256_add_ps(
            _mm512_castps512_ps256(a1a),
            _mm256_castpd_ps(_mm512_extractf64x4_pd(_mm512_castps_pd(a1a), 1)),
        );
        let r2_256 = _mm256_add_ps(
            _mm512_castps512_ps256(a2a),
            _mm256_castpd_ps(_mm512_extractf64x4_pd(_mm512_castps_pd(a2a), 1)),
        );
        let r3_256 = _mm256_add_ps(
            _mm512_castps512_ps256(a3a),
            _mm256_castpd_ps(_mm512_extractf64x4_pd(_mm512_castps_pd(a3a), 1)),
        );
        let r4_256 = _mm256_add_ps(
            _mm512_castps512_ps256(a4a),
            _mm256_castpd_ps(_mm512_extractf64x4_pd(_mm512_castps_pd(a4a), 1)),
        );
        let r5_256 = _mm256_add_ps(
            _mm512_castps512_ps256(a5a),
            _mm256_castpd_ps(_mm512_extractf64x4_pd(_mm512_castps_pd(a5a), 1)),
        );
        let r6_256 = _mm256_add_ps(
            _mm512_castps512_ps256(a6a),
            _mm256_castpd_ps(_mm512_extractf64x4_pd(_mm512_castps_pd(a6a), 1)),
        );
        let r7_256 = _mm256_add_ps(
            _mm512_castps512_ps256(a7a),
            _mm256_castpd_ps(_mm512_extractf64x4_pd(_mm512_castps_pd(a7a), 1)),
        );

        // Stage 2: __m256 → __m128
        let lo0 = _mm_add_ps(
            _mm256_castps256_ps128(r0_256),
            _mm256_extractf128_ps(r0_256, 1),
        );
        let lo1 = _mm_add_ps(
            _mm256_castps256_ps128(r1_256),
            _mm256_extractf128_ps(r1_256, 1),
        );
        let lo2 = _mm_add_ps(
            _mm256_castps256_ps128(r2_256),
            _mm256_extractf128_ps(r2_256, 1),
        );
        let lo3 = _mm_add_ps(
            _mm256_castps256_ps128(r3_256),
            _mm256_extractf128_ps(r3_256, 1),
        );
        let lo4 = _mm_add_ps(
            _mm256_castps256_ps128(r4_256),
            _mm256_extractf128_ps(r4_256, 1),
        );
        let lo5 = _mm_add_ps(
            _mm256_castps256_ps128(r5_256),
            _mm256_extractf128_ps(r5_256, 1),
        );
        let lo6 = _mm_add_ps(
            _mm256_castps256_ps128(r6_256),
            _mm256_extractf128_ps(r6_256, 1),
        );
        let lo7 = _mm_add_ps(
            _mm256_castps256_ps128(r7_256),
            _mm256_extractf128_ps(r7_256, 1),
        );

        // Stage 3: paired hadd
        let h01 = _mm_hadd_ps(lo0, lo1);
        let h23 = _mm_hadd_ps(lo2, lo3);
        let h45 = _mm_hadd_ps(lo4, lo5);
        let h67 = _mm_hadd_ps(lo6, lo7);

        let r0123 = _mm_hadd_ps(h01, h23);
        let r4567 = _mm_hadd_ps(h45, h67);

        // Scalar tail
        let mut t = [0.0_f32; 8];
        for k in i..in_size {
            let x = input[k];
            t[0] += rows[k] * x;
            t[1] += rows[in_size + k] * x;
            t[2] += rows[2 * in_size + k] * x;
            t[3] += rows[3 * in_size + k] * x;
            t[4] += rows[4 * in_size + k] * x;
            t[5] += rows[5 * in_size + k] * x;
            t[6] += rows[6 * in_size + k] * x;
            t[7] += rows[7 * in_size + k] * x;
        }
        let sums_lo = _mm_add_ps(r0123, _mm_loadu_ps(t.as_ptr()));
        let sums_hi = _mm_add_ps(r4567, _mm_loadu_ps(t.as_ptr().add(4)));

        _mm256_insertf128_ps(_mm256_castps128_ps256(sums_lo), sums_hi, 1)
    }
}

/// 4 simultaneous f32 dot products returning batched `__m128`.
/// Same accumulation as [`dot4_f32`] but uses 3-stage reduction
/// (__m512 → __m256 → __m128 → hadd) to produce all 4 sums in
/// fewer instructions.
#[inline]
#[cfg(target_arch = "x86_64")]
pub fn dot4_f32_m128(rows: &[f32], input: &[f32]) -> __m128 {
    let in_size = input.len();
    let mut i = 0;

    // SAFETY: AVX-512F guaranteed by target_feature cfg on parent module.
    // Row pointers: rows.len() == 4 * in_size, offsets k * in_size + i where k < 4.
    // Input pointer: i + N <= in_size before every access.
    unsafe {
        let mut a0a = _mm512_setzero_ps();
        let mut a0b = _mm512_setzero_ps();
        let mut a1a = _mm512_setzero_ps();
        let mut a1b = _mm512_setzero_ps();
        let mut a2a = _mm512_setzero_ps();
        let mut a2b = _mm512_setzero_ps();
        let mut a3a = _mm512_setzero_ps();
        let mut a3b = _mm512_setzero_ps();

        let r0 = rows.as_ptr();
        let r1 = r0.add(in_size);
        let r2 = r1.add(in_size);
        let r3 = r2.add(in_size);
        let inp = input.as_ptr();

        while i + 32 <= in_size {
            let x0 = _mm512_loadu_ps(inp.add(i));
            let x1 = _mm512_loadu_ps(inp.add(i + 16));

            a0a = _mm512_fmadd_ps(_mm512_loadu_ps(r0.add(i)), x0, a0a);
            a0b = _mm512_fmadd_ps(_mm512_loadu_ps(r0.add(i + 16)), x1, a0b);
            a1a = _mm512_fmadd_ps(_mm512_loadu_ps(r1.add(i)), x0, a1a);
            a1b = _mm512_fmadd_ps(_mm512_loadu_ps(r1.add(i + 16)), x1, a1b);
            a2a = _mm512_fmadd_ps(_mm512_loadu_ps(r2.add(i)), x0, a2a);
            a2b = _mm512_fmadd_ps(_mm512_loadu_ps(r2.add(i + 16)), x1, a2b);
            a3a = _mm512_fmadd_ps(_mm512_loadu_ps(r3.add(i)), x0, a3a);
            a3b = _mm512_fmadd_ps(_mm512_loadu_ps(r3.add(i + 16)), x1, a3b);

            i += 32;
        }

        if i + 16 <= in_size {
            let x = _mm512_loadu_ps(inp.add(i));
            a0a = _mm512_fmadd_ps(_mm512_loadu_ps(r0.add(i)), x, a0a);
            a1a = _mm512_fmadd_ps(_mm512_loadu_ps(r1.add(i)), x, a1a);
            a2a = _mm512_fmadd_ps(_mm512_loadu_ps(r2.add(i)), x, a2a);
            a3a = _mm512_fmadd_ps(_mm512_loadu_ps(r3.add(i)), x, a3a);
            i += 16;
        }

        a0a = _mm512_add_ps(a0a, a0b);
        a1a = _mm512_add_ps(a1a, a1b);
        a2a = _mm512_add_ps(a2a, a2b);
        a3a = _mm512_add_ps(a3a, a3b);

        // Stage 1: __m512 → __m256
        let r0_256 = _mm256_add_ps(
            _mm512_castps512_ps256(a0a),
            _mm256_castpd_ps(_mm512_extractf64x4_pd(_mm512_castps_pd(a0a), 1)),
        );
        let r1_256 = _mm256_add_ps(
            _mm512_castps512_ps256(a1a),
            _mm256_castpd_ps(_mm512_extractf64x4_pd(_mm512_castps_pd(a1a), 1)),
        );
        let r2_256 = _mm256_add_ps(
            _mm512_castps512_ps256(a2a),
            _mm256_castpd_ps(_mm512_extractf64x4_pd(_mm512_castps_pd(a2a), 1)),
        );
        let r3_256 = _mm256_add_ps(
            _mm512_castps512_ps256(a3a),
            _mm256_castpd_ps(_mm512_extractf64x4_pd(_mm512_castps_pd(a3a), 1)),
        );

        // Stage 2: __m256 → __m128
        let lo0 = _mm_add_ps(
            _mm256_castps256_ps128(r0_256),
            _mm256_extractf128_ps(r0_256, 1),
        );
        let lo1 = _mm_add_ps(
            _mm256_castps256_ps128(r1_256),
            _mm256_extractf128_ps(r1_256, 1),
        );
        let lo2 = _mm_add_ps(
            _mm256_castps256_ps128(r2_256),
            _mm256_extractf128_ps(r2_256, 1),
        );
        let lo3 = _mm_add_ps(
            _mm256_castps256_ps128(r3_256),
            _mm256_extractf128_ps(r3_256, 1),
        );

        // Stage 3: paired hadd
        let h01 = _mm_hadd_ps(lo0, lo1);
        let h23 = _mm_hadd_ps(lo2, lo3);
        let mut sums = _mm_hadd_ps(h01, h23);

        let mut t = [0.0_f32; 4];
        for k in i..in_size {
            let x = input[k];
            t[0] += rows[k] * x;
            t[1] += rows[in_size + k] * x;
            t[2] += rows[2 * in_size + k] * x;
            t[3] += rows[3 * in_size + k] * x;
        }
        sums = _mm_add_ps(sums, _mm_loadu_ps(t.as_ptr()));

        sums
    }
}
