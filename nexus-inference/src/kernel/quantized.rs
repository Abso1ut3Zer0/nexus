//! Int8 quantized-MLP kernels: i8 GEMV (AVX2 `maddubs`) and f32-to-i8
//! quantization. Self-contained integer compute; the dequant/correction
//! orchestration lives in `crate::quantized_mlp`.

#[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
#[inline]
pub(crate) fn dot_i8_i32(a: &[i8], b: &[i8]) -> i32 {
    debug_assert_eq!(a.len(), b.len());
    let mut s0 = 0_i32;
    let mut s1 = 0_i32;
    let mut s2 = 0_i32;
    let mut s3 = 0_i32;
    let n4 = a.len() & !3;
    for i in (0..n4).step_by(4) {
        s0 += a[i] as i32 * b[i] as i32;
        s1 += a[i + 1] as i32 * b[i + 1] as i32;
        s2 += a[i + 2] as i32 * b[i + 2] as i32;
        s3 += a[i + 3] as i32 * b[i + 3] as i32;
    }
    for i in n4..a.len() {
        s0 += a[i] as i32 * b[i] as i32;
    }
    (s0 + s2) + (s1 + s3)
}

#[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
#[inline]
pub(crate) fn dot4_i8_i32(rows: &[i8], input: &[i8]) -> [i32; 4] {
    let n = input.len();
    [
        dot_i8_i32(&rows[..n], input),
        dot_i8_i32(&rows[n..2 * n], input),
        dot_i8_i32(&rows[2 * n..3 * n], input),
        dot_i8_i32(&rows[3 * n..4 * n], input),
    ]
}

// `_mm256_maddubs_epi16` saturates its i16 pairwise sums. With the XOR trick
// (i8→u8 via +128), two adjacent large products can exceed i16 range. This is
// accepted — matches FBGEMM/oneDNN/TVM behavior. Quantized inference is
// inherently approximate; the saturation delta is negligible vs quantization
// error for well-calibrated models (PyTorch torch.ao.quantization output).
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
#[inline(never)]
pub(crate) fn matvec_i8_i32(
    weights: &[i8],
    input: &[i8],
    output: &mut [i32],
    out_size: usize,
    in_size: usize,
) -> usize {
    use core::arch::x86_64::*;

    /// Horizontal sum of an 8-lane i32 AVX2 vector.
    ///
    /// # Safety
    /// Caller must run on a target with AVX2 enabled.
    #[inline(always)]
    unsafe fn hsum_i32(acc: core::arch::x86_64::__m256i) -> i32 {
        // SAFETY: caller guarantees AVX2 (safety contract on this fn).
        unsafe {
            let hi128 = _mm256_extracti128_si256(acc, 1);
            let lo128 = _mm256_castsi256_si128(acc);
            let sum128 = _mm_add_epi32(lo128, hi128);
            let hi64 = _mm_unpackhi_epi64(sum128, sum128);
            let sum64 = _mm_add_epi32(sum128, hi64);
            let hi32 = _mm_shuffle_epi32(sum64, 0x01);
            let sum32 = _mm_add_epi32(sum64, hi32);
            _mm_cvtsi128_si32(sum32)
        }
    }

    let mut j = 0;
    let in_32 = in_size & !31;

    // SAFETY: cfg guarantees AVX2 availability.
    // All pointer accesses are bounded by out_size * in_size (weights),
    // in_size (input), and out_size (output).
    unsafe {
        let flip = _mm256_set1_epi8(-128);
        let ones_16 = _mm256_set1_epi16(1);

        // 4-row tiled: load input once, apply to 4 weight rows.
        // Amortizes input memory traffic across 4 maddubs per iteration.
        while j + 4 <= out_size {
            let mut acc0 = _mm256_setzero_si256();
            let mut acc1 = _mm256_setzero_si256();
            let mut acc2 = _mm256_setzero_si256();
            let mut acc3 = _mm256_setzero_si256();

            let w_base = weights.as_ptr().add(j * in_size);
            let mut i = 0;
            while i < in_32 {
                let x_i8 = _mm256_loadu_si256(input.as_ptr().add(i) as *const _);
                let x_u8 = _mm256_xor_si256(x_i8, flip);

                let w0 = _mm256_loadu_si256(w_base.add(i) as *const _);
                let w1 = _mm256_loadu_si256(w_base.add(in_size + i) as *const _);
                let w2 = _mm256_loadu_si256(w_base.add(2 * in_size + i) as *const _);
                let w3 = _mm256_loadu_si256(w_base.add(3 * in_size + i) as *const _);

                acc0 = _mm256_add_epi32(
                    acc0,
                    _mm256_madd_epi16(_mm256_maddubs_epi16(x_u8, w0), ones_16),
                );
                acc1 = _mm256_add_epi32(
                    acc1,
                    _mm256_madd_epi16(_mm256_maddubs_epi16(x_u8, w1), ones_16),
                );
                acc2 = _mm256_add_epi32(
                    acc2,
                    _mm256_madd_epi16(_mm256_maddubs_epi16(x_u8, w2), ones_16),
                );
                acc3 = _mm256_add_epi32(
                    acc3,
                    _mm256_madd_epi16(_mm256_maddubs_epi16(x_u8, w3), ones_16),
                );
                i += 32;
            }

            let mut dot0 = hsum_i32(acc0);
            let mut dot1 = hsum_i32(acc1);
            let mut dot2 = hsum_i32(acc2);
            let mut dot3 = hsum_i32(acc3);

            // Scalar remainder for in_size % 32
            let mut i = in_32;
            while i < in_size {
                let x = input[i] as i32 + 128;
                dot0 += x * *w_base.add(i) as i32;
                dot1 += x * *w_base.add(in_size + i) as i32;
                dot2 += x * *w_base.add(2 * in_size + i) as i32;
                dot3 += x * *w_base.add(3 * in_size + i) as i32;
                i += 1;
            }

            output[j] = dot0;
            output[j + 1] = dot1;
            output[j + 2] = dot2;
            output[j + 3] = dot3;
            j += 4;
        }

        // Remainder rows (out_size % 4)
        while j < out_size {
            let row = weights.as_ptr().add(j * in_size);
            let mut acc = _mm256_setzero_si256();

            let mut i = 0;
            while i < in_32 {
                let x_i8 = _mm256_loadu_si256(input.as_ptr().add(i) as *const _);
                let x_u8 = _mm256_xor_si256(x_i8, flip);
                let w = _mm256_loadu_si256(row.add(i) as *const _);
                let prod16 = _mm256_maddubs_epi16(x_u8, w);
                acc = _mm256_add_epi32(acc, _mm256_madd_epi16(prod16, ones_16));
                i += 32;
            }

            let mut dot = hsum_i32(acc);
            while i < in_size {
                dot += (input[i] as i32 + 128) * *row.add(i) as i32;
                i += 1;
            }

            output[j] = dot;
            j += 1;
        }
    }
    j
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
#[inline]
pub(crate) fn quantize_f32_to_i8(src: &[f32], dst: &mut [i8], inv_scale: f32, zero_point: i8) {
    use core::arch::x86_64::*;

    let n = src.len();
    let n_8 = n & !7;
    let zp = zero_point as i32;

    // SAFETY: cfg guarantees AVX2+SSE4.1 availability.
    // Pointer accesses bounded by src.len() and dst.len() (caller asserts equal).
    unsafe {
        let inv_scale_v = _mm256_set1_ps(inv_scale);
        let zp_v = _mm256_set1_epi32(zp);

        let mut i = 0;
        while i < n_8 {
            let f = _mm256_loadu_ps(src.as_ptr().add(i));
            let scaled = _mm256_mul_ps(f, inv_scale_v);
            // cvtps uses banker's rounding (round-to-nearest-even), matching
            // PyTorch's torch.quantize_per_tensor (nearbyint).
            let i32s = _mm256_cvtps_epi32(scaled);
            let with_zp = _mm256_add_epi32(i32s, zp_v);

            // Pack 8×i32 → 8×i8 via 128-bit path (no lane-crossing issues).
            let lo = _mm256_castsi256_si128(with_zp);
            let hi = _mm256_extracti128_si256(with_zp, 1);
            let packed16 = _mm_packs_epi32(lo, hi);
            let packed8 = _mm_packs_epi16(packed16, packed16);
            _mm_storel_epi64(dst.as_mut_ptr().add(i) as *mut _, packed8);

            i += 8;
        }

        // Scalar remainder for n % 8
        while i < n {
            let v = (src[i] * inv_scale).round() as i32 + zp;
            dst[i] = v.clamp(-128, 127) as i8;
            i += 1;
        }
    }
}

#[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
#[inline]
pub(crate) fn quantize_f32_to_i8(src: &[f32], dst: &mut [i8], inv_scale: f32, zero_point: i8) {
    let zp = zero_point as i32;
    for (x, q) in src.iter().zip(dst.iter_mut()) {
        let v = (*x * inv_scale).round() as i32 + zp;
        *q = v.clamp(-128, 127) as i8;
    }
}
