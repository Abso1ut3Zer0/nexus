//! XXH3 with AVX2 acceleration.
//!
//! Uses AVX2 SIMD for large inputs (>240 bytes), scalar for smaller inputs.
//! Compile with `RUSTFLAGS="-C target-feature=+avx2"`.

#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::*;

use super::xxh3::{
    PRIME32_1, PRIME32_2, PRIME64_1, PRIME64_2, SECRET,
    hash_bounded_with_seed as scalar_hash_bounded_with_seed, merge_accs,
};

/// Hash with compile-time capacity bound using AVX2 for large inputs.
#[inline]
pub fn hash_bounded_with_seed<const CAP: usize>(data: &[u8], seed: u64) -> u64 {
    // For CAP <= 240, SIMD never helps - use scalar directly
    if CAP <= 240 {
        return scalar_hash_bounded_with_seed::<CAP>(data, seed);
    }

    // CAP > 240: check actual length
    let len = data.len();
    if len <= 240 {
        return scalar_hash_bounded_with_seed::<CAP>(data, seed);
    }

    // Large input - use AVX2
    #[cfg(target_arch = "x86_64")]
    {
        // SAFETY: This module only compiles when target_feature = "avx2"
        unsafe { hash_long_avx2(data, seed) }
    }

    #[cfg(not(target_arch = "x86_64"))]
    {
        scalar_hash_bounded_with_seed::<CAP>(data, seed)
    }
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn hash_long_avx2(data: &[u8], seed: u64) -> u64 {
    // SAFETY: #[target_feature(enable = "avx2")] on this function guarantees AVX2 is available.
    unsafe {
        let len = data.len();

        // Initialize accumulators (2 x 256-bit = 8 x 64-bit)
        let init0 = _mm256_set_epi64x(
            (0_u64.wrapping_sub(PRIME64_1)) as i64,
            PRIME64_2 as i64,
            PRIME64_1 as i64,
            PRIME32_1 as i64,
        );
        let init1 = _mm256_set_epi64x(
            PRIME32_1 as i64,
            (0_u64.wrapping_sub(PRIME64_2)) as i64,
            PRIME64_2 as i64,
            PRIME32_2 as i64,
        );

        let seed_add = _mm256_set_epi64x(-(seed as i64), seed as i64, -(seed as i64), seed as i64);

        let mut acc0 = _mm256_add_epi64(init0, seed_add);
        let mut acc1 = _mm256_add_epi64(init1, seed_add);

        let block_len = 1024;
        let stripe_len = 64;
        let nb_stripes_per_block = block_len / stripe_len;
        let nb_blocks = (len - 1) / block_len;

        // Process full blocks
        for n in 0..nb_blocks {
            for s in 0..nb_stripes_per_block {
                let stripe_offset = n * block_len + s * stripe_len;
                let stripe = data.as_ptr().add(stripe_offset);
                let secret_offset = s * 8;

                accumulate_stripe_avx2(&mut acc0, &mut acc1, stripe, secret_offset);
            }
            scramble_acc_avx2(&mut acc0, &mut acc1);
        }

        // Process remaining stripes
        let last_block_offset = nb_blocks * block_len;
        let nb_stripes = ((len - 1) - last_block_offset) / stripe_len;

        for s in 0..nb_stripes {
            let stripe_offset = last_block_offset + s * stripe_len;
            let stripe = data.as_ptr().add(stripe_offset);
            let secret_offset = s * 8;

            accumulate_stripe_avx2(&mut acc0, &mut acc1, stripe, secret_offset);
        }

        // Final stripe
        let final_stripe = data.as_ptr().add(len - 64);
        accumulate_stripe_avx2(&mut acc0, &mut acc1, final_stripe, 121);

        // Extract accumulators
        let mut acc = [0u64; 8];
        _mm256_storeu_si256(acc.as_mut_ptr() as *mut __m256i, acc0);
        _mm256_storeu_si256(acc.as_mut_ptr().add(4) as *mut __m256i, acc1);

        merge_accs(&acc, len as u64)
    }
}

#[cfg(target_arch = "x86_64")]
#[inline]
#[target_feature(enable = "avx2")]
unsafe fn accumulate_stripe_avx2(
    acc0: &mut __m256i,
    acc1: &mut __m256i,
    stripe: *const u8,
    secret_offset: usize,
) {
    // SAFETY: #[target_feature(enable = "avx2")] on this function guarantees AVX2 is available.
    unsafe {
        let secret_ptr = SECRET.as_ptr().add(secret_offset);

        // Load stripe data (2 x 32 bytes = 64 bytes)
        let d0 = _mm256_loadu_si256(stripe as *const __m256i);
        let d1 = _mm256_loadu_si256(stripe.add(32) as *const __m256i);

        // Load secret
        let s0 = _mm256_loadu_si256(secret_ptr as *const __m256i);
        let s1 = _mm256_loadu_si256(secret_ptr.add(32) as *const __m256i);

        // XOR data with secret
        let k0 = _mm256_xor_si256(d0, s0);
        let k1 = _mm256_xor_si256(d1, s1);

        // Mask keeps low 32 bits of each 64-bit lane
        let mask = _mm256_set_epi32(0, -1, 0, -1, 0, -1, 0, -1);

        let lo0 = _mm256_and_si256(d0, mask);
        let hi0 = _mm256_srli_epi64(d0, 32);
        let prod0 = _mm256_mul_epu32(lo0, hi0);
        *acc0 = _mm256_add_epi64(*acc0, k0);
        *acc0 = _mm256_add_epi64(*acc0, prod0);

        let lo1 = _mm256_and_si256(d1, mask);
        let hi1 = _mm256_srli_epi64(d1, 32);
        let prod1 = _mm256_mul_epu32(lo1, hi1);
        *acc1 = _mm256_add_epi64(*acc1, k1);
        *acc1 = _mm256_add_epi64(*acc1, prod1);
    }
}

#[cfg(target_arch = "x86_64")]
#[inline]
#[target_feature(enable = "avx2")]
unsafe fn scramble_acc_avx2(acc0: &mut __m256i, acc1: &mut __m256i) {
    // SAFETY: #[target_feature(enable = "avx2")] on this function guarantees AVX2 is available.
    unsafe {
        let prime = _mm256_set1_epi32(PRIME32_1 as i32);
        let secret_ptr = SECRET.as_ptr().add(128);

        // Load scramble secrets
        let s0 = _mm256_loadu_si256(secret_ptr as *const __m256i);
        let s1 = _mm256_loadu_si256(secret_ptr.add(32) as *const __m256i);

        // acc ^= acc >> 47
        *acc0 = _mm256_xor_si256(*acc0, _mm256_srli_epi64(*acc0, 47));
        *acc1 = _mm256_xor_si256(*acc1, _mm256_srli_epi64(*acc1, 47));

        // acc ^= secret
        *acc0 = _mm256_xor_si256(*acc0, s0);
        *acc1 = _mm256_xor_si256(*acc1, s1);

        // acc *= prime (32-bit multiply pattern)
        let lo0 = _mm256_mul_epu32(*acc0, prime);
        let hi0 = _mm256_mul_epu32(_mm256_srli_epi64(*acc0, 32), prime);
        *acc0 = _mm256_add_epi64(lo0, _mm256_slli_epi64(hi0, 32));

        let lo1 = _mm256_mul_epu32(*acc1, prime);
        let hi1 = _mm256_mul_epu32(_mm256_srli_epi64(*acc1, 32), prime);
        *acc1 = _mm256_add_epi64(lo1, _mm256_slli_epi64(hi1, 32));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hash::xxh3::hash_with_seed as xxh3_scalar;

    fn hash(data: &[u8]) -> u64 {
        hash_bounded_with_seed::<4096>(data, 0)
    }

    #[test]
    fn matches_scalar_small() {
        for len in 0..=240 {
            let data: Vec<u8> = (0..len).map(|i| i as u8).collect();
            let h_avx2 = hash(&data);
            let h_scalar = xxh3_scalar(&data, 0);
            assert_eq!(h_avx2, h_scalar, "mismatch at len={}", len);
        }
    }

    #[test]
    fn deterministic() {
        let data = vec![0u8; 1024];
        let h1 = hash(&data);
        let h2 = hash(&data);
        assert_eq!(h1, h2);
    }

    #[test]
    fn large_input() {
        let data = vec![0u8; 4096];
        let _ = hash(&data);
    }

    #[test]
    fn matches_scalar_large() {
        for &len in &[256, 512, 1024, 2048, 4096, 8192] {
            let data: Vec<u8> = (0..len).map(|i| (i % 256) as u8).collect();
            let h_avx2 = hash(&data);
            let h_scalar = xxh3_scalar(&data, 0);
            assert_eq!(h_avx2, h_scalar, "mismatch at len={}", len);
        }
    }
}
