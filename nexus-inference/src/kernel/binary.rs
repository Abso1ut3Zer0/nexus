//! Binary neural-network kernels: f32→sign-bit packing, the binarized fp32
//! input projection, XNOR+popcount hidden layers, and the fp32 output readout.
//! Threshold precompute (`bias_to_int_threshold`) and weight packing (`pack_i8`)
//! are construction-time and stay in `crate::bnn`.

#[cfg(not(all(
    target_arch = "x86_64",
    any(
        target_feature = "avx512f",
        all(target_feature = "avx2", target_feature = "fma")
    )
)))]
pub(crate) fn binarize(values: &[f32], bits: &mut [u64]) {
    debug_assert_eq!(values.len(), bits.len() * 64);
    for (w, word) in bits.iter_mut().enumerate() {
        let mut val = 0_u64;
        let base = w * 64;
        for b in 0..64 {
            if values[base + b] >= 0.0 {
                val |= 1 << b;
            }
        }
        *word = val;
    }
}

#[cfg(all(
    target_arch = "x86_64",
    any(
        target_feature = "avx512f",
        all(target_feature = "avx2", target_feature = "fma")
    )
))]
#[inline(never)]
pub(crate) fn matvec_bias_binarize(
    weight: &[f32],
    input: &[f32],
    bias: &[f32],
    bits: &mut [u64],
    out_size: usize,
    in_size: usize,
) {
    use crate::kernel::dot::{dot4_f32_m128, dot8_f32_m256};
    use core::arch::x86_64::*;

    let wpr = out_size / 64;
    debug_assert_eq!(out_size, wpr * 64);
    debug_assert_eq!(bits.len(), wpr);

    // SAFETY: cfg guarantees AVX2+FMA or AVX-512F; all pointer offsets stay within weight/input/bias slice bounds.
    unsafe {
        for word_idx in 0..wpr {
            let base = word_idx * 64;
            let mut bit_word = 0_u64;
            let mut k = 0_usize;

            if in_size >= 32 {
                let zero_256 = _mm256_setzero_ps();
                while k + 8 <= 64 {
                    let j = base + k;
                    let rows = &weight[j * in_size..(j + 8) * in_size];
                    let dots = dot8_f32_m256(rows, input);
                    let bias_v = _mm256_loadu_ps(bias.as_ptr().add(j));
                    let result = _mm256_add_ps(dots, bias_v);
                    let cmp = _mm256_cmp_ps(result, zero_256, _CMP_GE_OQ);
                    let mask = _mm256_movemask_ps(cmp) as u64;
                    bit_word |= mask << k;
                    k += 8;
                }
            }

            let zero_128 = _mm_setzero_ps();
            while k + 4 <= 64 {
                let j = base + k;
                let rows = &weight[j * in_size..(j + 4) * in_size];
                let dots = dot4_f32_m128(rows, input);
                let bias_v = _mm_loadu_ps(bias.as_ptr().add(j));
                let result = _mm_add_ps(dots, bias_v);
                let cmp = _mm_cmpge_ps(result, zero_128);
                let mask = _mm_movemask_ps(cmp) as u64;
                bit_word |= mask << k;
                k += 4;
            }

            bits[word_idx] = bit_word;
        }
    }
}

#[cfg(not(all(
    target_arch = "x86_64",
    any(
        target_feature = "avx512f",
        all(target_feature = "avx2", target_feature = "fma")
    )
)))]
pub(crate) fn output_from_bits(
    weights: &[f32],
    bits: &[u64],
    row_sum: f32,
    bias: f32,
    hidden_size: usize,
) -> f32 {
    let mut pos_sum = 0.0_f32;
    for (w, &word) in bits.iter().enumerate() {
        let base = w * 64;
        let count = 64.min(hidden_size - base);
        for b in 0..count {
            if (word >> b) & 1 == 1 {
                pos_sum += weights[base + b];
            }
        }
    }
    2.0f32.mul_add(pos_sum, -row_sum + bias)
}

#[cfg(all(
    target_arch = "x86_64",
    any(
        target_feature = "avx512f",
        all(target_feature = "avx2", target_feature = "fma")
    )
))]
#[inline(never)]
pub(crate) fn output_from_bits_simd(weights: &[f32], bits: &[u64], row_sum: f32, bias: f32) -> f32 {
    use core::arch::x86_64::*;
    // SAFETY: cfg guarantees AVX2+FMA or AVX-512F; all pointer offsets stay within weights slice bounds.
    unsafe {
        let bit_positions = _mm256_setr_epi32(1, 2, 4, 8, 16, 32, 64, 128);
        let mut acc = _mm256_setzero_ps();

        for (w_idx, &word) in bits.iter().enumerate() {
            let base = w_idx * 64;
            for byte_idx in 0..8 {
                let byte = ((word >> (byte_idx * 8)) & 0xFF) as i32;
                let offset = base + byte_idx * 8;

                let w = _mm256_loadu_ps(weights.as_ptr().add(offset));
                let byte_broadcast = _mm256_set1_epi32(byte);
                let masked = _mm256_and_si256(byte_broadcast, bit_positions);
                let cmp = _mm256_cmpeq_epi32(masked, bit_positions);
                acc = _mm256_add_ps(acc, _mm256_and_ps(w, _mm256_castsi256_ps(cmp)));
            }
        }

        let hi = _mm256_extractf128_ps(acc, 1);
        let lo = _mm256_castps256_ps128(acc);
        let sum128 = _mm_add_ps(lo, hi);
        let hi64 = _mm_movehl_ps(sum128, sum128);
        let sum64 = _mm_add_ps(sum128, hi64);
        let hi32 = _mm_shuffle_ps(sum64, sum64, 0x55);
        let sum32 = _mm_add_ss(sum64, hi32);
        let pos_sum = _mm_cvtss_f32(sum32);

        2.0f32.mul_add(pos_sum, -row_sum + bias)
    }
}

pub(crate) fn binary_layer_forward(
    w_packed: &[u64],
    int_threshold: &[u32],
    input_bits: &[u64],
    output_bits: &mut [u64],
    hidden_size: usize,
    words_per_row: usize,
) {
    debug_assert_eq!(w_packed.len(), hidden_size * words_per_row);
    debug_assert_eq!(int_threshold.len(), hidden_size);
    debug_assert_eq!(input_bits.len(), words_per_row);
    debug_assert_eq!(output_bits.len(), words_per_row);

    for w in 0..output_bits.len() {
        let mut word = 0_u64;
        let base = w * 64;
        let count = 64.min(hidden_size - base);
        for b in 0..count {
            let j = base + b;
            let row = &w_packed[j * words_per_row..(j + 1) * words_per_row];
            let mut popcount = 0_u32;
            for k in 0..words_per_row {
                popcount += (!(row[k] ^ input_bits[k])).count_ones();
            }
            if popcount >= int_threshold[j] {
                word |= 1 << b;
            }
        }
        output_bits[w] = word;
    }
}
