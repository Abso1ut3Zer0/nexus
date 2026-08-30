#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::*;

use super::scalar;

/// Horizontal sum of an 8-lane AVX2 vector.
///
/// # Safety
/// Caller must run on a target with AVX2 enabled.
#[inline]
#[cfg(target_arch = "x86_64")]
unsafe fn hsum_f32(v: __m256) -> f32 {
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

#[inline]
#[cfg(target_arch = "x86_64")]
pub fn dot_f32(a: &[f32], b: &[f32]) -> f32 {
    let len = a.len();
    let mut i = 0;

    // SAFETY: AVX2+FMA guaranteed by target_feature cfg on parent module.
    // All pointer offsets satisfy i + N <= len before access.
    let sum = unsafe {
        let mut acc0 = _mm256_setzero_ps();
        let mut acc1 = _mm256_setzero_ps();
        let mut acc2 = _mm256_setzero_ps();
        let mut acc3 = _mm256_setzero_ps();

        while i + 32 <= len {
            let a0 = _mm256_loadu_ps(a.as_ptr().add(i));
            let b0 = _mm256_loadu_ps(b.as_ptr().add(i));
            let a1 = _mm256_loadu_ps(a.as_ptr().add(i + 8));
            let b1 = _mm256_loadu_ps(b.as_ptr().add(i + 8));
            let a2 = _mm256_loadu_ps(a.as_ptr().add(i + 16));
            let b2 = _mm256_loadu_ps(b.as_ptr().add(i + 16));
            let a3 = _mm256_loadu_ps(a.as_ptr().add(i + 24));
            let b3 = _mm256_loadu_ps(b.as_ptr().add(i + 24));
            acc0 = _mm256_fmadd_ps(a0, b0, acc0);
            acc1 = _mm256_fmadd_ps(a1, b1, acc1);
            acc2 = _mm256_fmadd_ps(a2, b2, acc2);
            acc3 = _mm256_fmadd_ps(a3, b3, acc3);
            i += 32;
        }

        while i + 8 <= len {
            let av = _mm256_loadu_ps(a.as_ptr().add(i));
            let bv = _mm256_loadu_ps(b.as_ptr().add(i));
            acc0 = _mm256_fmadd_ps(av, bv, acc0);
            i += 8;
        }

        acc0 = _mm256_add_ps(_mm256_add_ps(acc0, acc1), _mm256_add_ps(acc2, acc3));

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

    // SAFETY: AVX2+FMA guaranteed by target_feature cfg on parent module.
    // Row pointers: rows.len() == 4 * in_size, offsets k * in_size + i where k < 4.
    // Input pointer: i + N <= in_size before every access.
    let sums = unsafe {
        let mut a0a = _mm256_setzero_ps();
        let mut a0b = _mm256_setzero_ps();
        let mut a1a = _mm256_setzero_ps();
        let mut a1b = _mm256_setzero_ps();
        let mut a2a = _mm256_setzero_ps();
        let mut a2b = _mm256_setzero_ps();
        let mut a3a = _mm256_setzero_ps();
        let mut a3b = _mm256_setzero_ps();

        let r0 = rows.as_ptr();
        let r1 = r0.add(in_size);
        let r2 = r1.add(in_size);
        let r3 = r2.add(in_size);
        let inp = input.as_ptr();

        while i + 16 <= in_size {
            let x0 = _mm256_loadu_ps(inp.add(i));
            let x1 = _mm256_loadu_ps(inp.add(i + 8));

            a0a = _mm256_fmadd_ps(_mm256_loadu_ps(r0.add(i)), x0, a0a);
            a0b = _mm256_fmadd_ps(_mm256_loadu_ps(r0.add(i + 8)), x1, a0b);
            a1a = _mm256_fmadd_ps(_mm256_loadu_ps(r1.add(i)), x0, a1a);
            a1b = _mm256_fmadd_ps(_mm256_loadu_ps(r1.add(i + 8)), x1, a1b);
            a2a = _mm256_fmadd_ps(_mm256_loadu_ps(r2.add(i)), x0, a2a);
            a2b = _mm256_fmadd_ps(_mm256_loadu_ps(r2.add(i + 8)), x1, a2b);
            a3a = _mm256_fmadd_ps(_mm256_loadu_ps(r3.add(i)), x0, a3a);
            a3b = _mm256_fmadd_ps(_mm256_loadu_ps(r3.add(i + 8)), x1, a3b);

            i += 16;
        }

        if i + 8 <= in_size {
            let x = _mm256_loadu_ps(inp.add(i));
            a0a = _mm256_fmadd_ps(_mm256_loadu_ps(r0.add(i)), x, a0a);
            a1a = _mm256_fmadd_ps(_mm256_loadu_ps(r1.add(i)), x, a1a);
            a2a = _mm256_fmadd_ps(_mm256_loadu_ps(r2.add(i)), x, a2a);
            a3a = _mm256_fmadd_ps(_mm256_loadu_ps(r3.add(i)), x, a3a);
            i += 8;
        }

        a0a = _mm256_add_ps(a0a, a0b);
        a1a = _mm256_add_ps(a1a, a1b);
        a2a = _mm256_add_ps(a2a, a2b);
        a3a = _mm256_add_ps(a3a, a3b);

        [hsum_f32(a0a), hsum_f32(a1a), hsum_f32(a2a), hsum_f32(a3a)]
    };

    // Scalar tail (0-7 remaining elements)
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
/// 1 accumulator per row (8 independent FMA chains hide latency).
#[inline]
#[cfg(target_arch = "x86_64")]
pub fn dot8_f32_m256(rows: &[f32], input: &[f32]) -> __m256 {
    let in_size = input.len();
    let mut i = 0;

    // SAFETY: AVX2+FMA guaranteed by target_feature cfg on parent module.
    // Row pointers: rows.len() == 8 * in_size, offsets k * in_size + i where k < 8.
    // Input pointer: i + 8 <= in_size before every access.
    unsafe {
        let mut a0 = _mm256_setzero_ps();
        let mut a1 = _mm256_setzero_ps();
        let mut a2 = _mm256_setzero_ps();
        let mut a3 = _mm256_setzero_ps();
        let mut a4 = _mm256_setzero_ps();
        let mut a5 = _mm256_setzero_ps();
        let mut a6 = _mm256_setzero_ps();
        let mut a7 = _mm256_setzero_ps();

        let r0 = rows.as_ptr();
        let r1 = r0.add(in_size);
        let r2 = r1.add(in_size);
        let r3 = r2.add(in_size);
        let r4 = r3.add(in_size);
        let r5 = r4.add(in_size);
        let r6 = r5.add(in_size);
        let r7 = r6.add(in_size);
        let inp = input.as_ptr();

        while i + 8 <= in_size {
            let x = _mm256_loadu_ps(inp.add(i));
            a0 = _mm256_fmadd_ps(_mm256_loadu_ps(r0.add(i)), x, a0);
            a1 = _mm256_fmadd_ps(_mm256_loadu_ps(r1.add(i)), x, a1);
            a2 = _mm256_fmadd_ps(_mm256_loadu_ps(r2.add(i)), x, a2);
            a3 = _mm256_fmadd_ps(_mm256_loadu_ps(r3.add(i)), x, a3);
            a4 = _mm256_fmadd_ps(_mm256_loadu_ps(r4.add(i)), x, a4);
            a5 = _mm256_fmadd_ps(_mm256_loadu_ps(r5.add(i)), x, a5);
            a6 = _mm256_fmadd_ps(_mm256_loadu_ps(r6.add(i)), x, a6);
            a7 = _mm256_fmadd_ps(_mm256_loadu_ps(r7.add(i)), x, a7);
            i += 8;
        }

        // Cross-lane fold: __m256 → __m128
        let lo0 = _mm_add_ps(_mm256_castps256_ps128(a0), _mm256_extractf128_ps(a0, 1));
        let lo1 = _mm_add_ps(_mm256_castps256_ps128(a1), _mm256_extractf128_ps(a1, 1));
        let lo2 = _mm_add_ps(_mm256_castps256_ps128(a2), _mm256_extractf128_ps(a2, 1));
        let lo3 = _mm_add_ps(_mm256_castps256_ps128(a3), _mm256_extractf128_ps(a3, 1));
        let lo4 = _mm_add_ps(_mm256_castps256_ps128(a4), _mm256_extractf128_ps(a4, 1));
        let lo5 = _mm_add_ps(_mm256_castps256_ps128(a5), _mm256_extractf128_ps(a5, 1));
        let lo6 = _mm_add_ps(_mm256_castps256_ps128(a6), _mm256_extractf128_ps(a6, 1));
        let lo7 = _mm_add_ps(_mm256_castps256_ps128(a7), _mm256_extractf128_ps(a7, 1));

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
/// Same accumulation as [`dot4_f32`] but uses paired `hadd` to
/// reduce all 4 sums in 11 instructions instead of 28.
#[inline]
#[cfg(target_arch = "x86_64")]
pub fn dot4_f32_m128(rows: &[f32], input: &[f32]) -> __m128 {
    let in_size = input.len();
    let mut i = 0;

    // SAFETY: AVX2+FMA guaranteed by target_feature cfg on parent module.
    // Row pointers: rows.len() == 4 * in_size, offsets k * in_size + i where k < 4.
    // Input pointer: i + N <= in_size before every access.
    unsafe {
        let mut a0a = _mm256_setzero_ps();
        let mut a0b = _mm256_setzero_ps();
        let mut a1a = _mm256_setzero_ps();
        let mut a1b = _mm256_setzero_ps();
        let mut a2a = _mm256_setzero_ps();
        let mut a2b = _mm256_setzero_ps();
        let mut a3a = _mm256_setzero_ps();
        let mut a3b = _mm256_setzero_ps();

        let r0 = rows.as_ptr();
        let r1 = r0.add(in_size);
        let r2 = r1.add(in_size);
        let r3 = r2.add(in_size);
        let inp = input.as_ptr();

        while i + 16 <= in_size {
            let x0 = _mm256_loadu_ps(inp.add(i));
            let x1 = _mm256_loadu_ps(inp.add(i + 8));

            a0a = _mm256_fmadd_ps(_mm256_loadu_ps(r0.add(i)), x0, a0a);
            a0b = _mm256_fmadd_ps(_mm256_loadu_ps(r0.add(i + 8)), x1, a0b);
            a1a = _mm256_fmadd_ps(_mm256_loadu_ps(r1.add(i)), x0, a1a);
            a1b = _mm256_fmadd_ps(_mm256_loadu_ps(r1.add(i + 8)), x1, a1b);
            a2a = _mm256_fmadd_ps(_mm256_loadu_ps(r2.add(i)), x0, a2a);
            a2b = _mm256_fmadd_ps(_mm256_loadu_ps(r2.add(i + 8)), x1, a2b);
            a3a = _mm256_fmadd_ps(_mm256_loadu_ps(r3.add(i)), x0, a3a);
            a3b = _mm256_fmadd_ps(_mm256_loadu_ps(r3.add(i + 8)), x1, a3b);

            i += 16;
        }

        if i + 8 <= in_size {
            let x = _mm256_loadu_ps(inp.add(i));
            a0a = _mm256_fmadd_ps(_mm256_loadu_ps(r0.add(i)), x, a0a);
            a1a = _mm256_fmadd_ps(_mm256_loadu_ps(r1.add(i)), x, a1a);
            a2a = _mm256_fmadd_ps(_mm256_loadu_ps(r2.add(i)), x, a2a);
            a3a = _mm256_fmadd_ps(_mm256_loadu_ps(r3.add(i)), x, a3a);
            i += 8;
        }

        a0a = _mm256_add_ps(a0a, a0b);
        a1a = _mm256_add_ps(a1a, a1b);
        a2a = _mm256_add_ps(a2a, a2b);
        a3a = _mm256_add_ps(a3a, a3b);

        let lo0 = _mm_add_ps(_mm256_castps256_ps128(a0a), _mm256_extractf128_ps(a0a, 1));
        let lo1 = _mm_add_ps(_mm256_castps256_ps128(a1a), _mm256_extractf128_ps(a1a, 1));
        let lo2 = _mm_add_ps(_mm256_castps256_ps128(a2a), _mm256_extractf128_ps(a2a, 1));
        let lo3 = _mm_add_ps(_mm256_castps256_ps128(a3a), _mm256_extractf128_ps(a3a, 1));
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
