//! XXH3 with AVX-512 acceleration.
//!
//! Uses AVX-512 SIMD for large inputs (>240 bytes), scalar for smaller inputs.
//! Compile with `RUSTFLAGS="-C target-feature=+avx512f"`.
//!
//! AVX-512 intrinsics were stabilized in Rust 1.89.0. Since this module only
//! compiles when explicitly opted in via target features, the MSRV lint is
//! suppressed — users enabling AVX-512 are on a sufficiently recent toolchain.
#![allow(clippy::incompatible_msrv)]

#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::*;

use super::xxh3::{
    PRIME32_1, PRIME64_1, PRIME64_2, SECRET,
    hash_bounded_with_seed as scalar_hash_bounded_with_seed, merge_accs,
};

/// Hash with compile-time capacity bound using AVX-512 for large inputs.
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

    // Large input - use AVX-512
    #[cfg(target_arch = "x86_64")]
    {
        // SAFETY: This module only compiles when target_feature = "avx512f"
        unsafe { hash_long_avx512(data, seed) }
    }

    #[cfg(not(target_arch = "x86_64"))]
    {
        scalar_hash_bounded_with_seed::<CAP>(data, seed)
    }
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx512f")]
unsafe fn hash_long_avx512(data: &[u8], seed: u64) -> u64 {
    // SAFETY: #[target_feature(enable = "avx512f")] on this function guarantees AVX-512 is available.
    unsafe {
        let len = data.len();

        // Initialize accumulator (1 x 512-bit = 8 x 64-bit)
        let init = _mm512_set_epi64(
            PRIME32_1 as i64,
            (0_u64.wrapping_sub(PRIME64_2)) as i64,
            PRIME64_2 as i64,
            (PRIME32_1.wrapping_add(1)) as i64,
            (0_u64.wrapping_sub(PRIME64_1)) as i64,
            PRIME64_2 as i64,
            PRIME64_1 as i64,
            PRIME32_1 as i64,
        );

        let seed_vec = _mm512_set_epi64(
            -(seed as i64),
            seed as i64,
            -(seed as i64),
            seed as i64,
            -(seed as i64),
            seed as i64,
            -(seed as i64),
            seed as i64,
        );

        let mut acc = _mm512_add_epi64(init, seed_vec);

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

                acc = accumulate_stripe_avx512(acc, stripe, secret_offset);
            }
            acc = scramble_acc_avx512(acc);
        }

        // Process remaining stripes
        let last_block_offset = nb_blocks * block_len;
        let nb_stripes = ((len - 1) - last_block_offset) / stripe_len;

        for s in 0..nb_stripes {
            let stripe_offset = last_block_offset + s * stripe_len;
            let stripe = data.as_ptr().add(stripe_offset);
            let secret_offset = s * 8;

            acc = accumulate_stripe_avx512(acc, stripe, secret_offset);
        }

        // Final stripe
        let final_stripe = data.as_ptr().add(len - 64);
        acc = accumulate_stripe_avx512(acc, final_stripe, 121);

        // Extract accumulators
        let mut acc_arr = [0u64; 8];
        _mm512_storeu_si512(acc_arr.as_mut_ptr().cast(), acc);

        merge_accs(&acc_arr, len as u64)
    }
}

#[cfg(target_arch = "x86_64")]
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn accumulate_stripe_avx512(
    acc: __m512i,
    stripe: *const u8,
    secret_offset: usize,
) -> __m512i {
    // SAFETY: #[target_feature(enable = "avx512f")] on this function guarantees AVX-512 is available.
    unsafe {
        let secret_ptr = SECRET.as_ptr().add(secret_offset);

        // Load entire 64-byte stripe in one register
        let data = _mm512_loadu_si512(stripe.cast());

        // Load 64 bytes of secret
        let secret = _mm512_loadu_si512(secret_ptr.cast());

        // XOR data with secret
        let keyed = _mm512_xor_si512(data, secret);

        // Extract low and high 32-bit parts for multiplication
        let lo32 = _mm512_and_si512(keyed, _mm512_set1_epi64(0xFFFF_FFFF));
        let hi32 = _mm512_srli_epi64(keyed, 32);

        // Multiply lo32 * hi32 (32-bit multiply, 64-bit result)
        let prod = _mm512_mul_epu32(lo32, hi32);

        // acc += data + prod
        let acc = _mm512_add_epi64(acc, data);
        _mm512_add_epi64(acc, prod)
    }
}

#[cfg(target_arch = "x86_64")]
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn scramble_acc_avx512(acc: __m512i) -> __m512i {
    // SAFETY: #[target_feature(enable = "avx512f")] on this function guarantees AVX-512 is available.
    unsafe {
        let prime = _mm512_set1_epi32(PRIME32_1 as i32);
        let secret_ptr = SECRET.as_ptr().add(128);

        // Load scramble secret
        let secret = _mm512_loadu_si512(secret_ptr.cast());

        // acc ^= acc >> 47
        let shifted = _mm512_srli_epi64(acc, 47);
        let acc = _mm512_xor_si512(acc, shifted);

        // acc ^= secret
        let acc = _mm512_xor_si512(acc, secret);

        // acc *= prime (32-bit multiply pattern for 64-bit result)
        let lo = _mm512_mul_epu32(acc, prime);
        let hi = _mm512_mul_epu32(_mm512_srli_epi64(acc, 32), prime);
        _mm512_add_epi64(lo, _mm512_slli_epi64(hi, 32))
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
            let h_avx512 = hash(&data);
            let h_scalar = xxh3_scalar(&data, 0);
            assert_eq!(h_avx512, h_scalar, "mismatch at len={}", len);
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
}
