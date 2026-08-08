//! SSE2 hex decode implementation.
//!
//! Decodes 16 or 32 hex ASCII characters to binary in parallel using
//! 128-bit SIMD operations. Available on all x86_64 targets.

#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::*;

#[cfg(test)]
use super::scalar;

/// Decode 16 hex chars to u64 using SSE2 parallel range classification.
///
/// Each byte is classified into one of three valid ranges ('0'-'9', 'A'-'F', 'a'-'f')
/// simultaneously. Invalid characters are detected via a single movemask check.
#[inline]
pub fn hex_decode_16(bytes: &[u8; 16]) -> Result<u64, usize> {
    hex_decode_16_inner(bytes)
}

/// Decode 32 hex chars to (hi, lo) u64 pair.
#[inline]
pub fn hex_decode_32(bytes: &[u8; 32]) -> Result<(u64, u64), usize> {
    // Process each half with SSE2
    // SAFETY: `bytes` is &[u8; 32], so bytes[0..16] and bytes[16..32] are both
    // valid. The pointer casts reinterpret contiguous sub-slices as &[u8; 16]
    // references with the same lifetime as `bytes`. Alignment is irrelevant
    // because [u8; 16] has align 1.
    let hi_bytes: &[u8; 16] = unsafe { &*(bytes.as_ptr().cast::<[u8; 16]>()) };
    // SAFETY: same as above.
    let lo_bytes: &[u8; 16] = unsafe { &*(bytes.as_ptr().add(16).cast::<[u8; 16]>()) };

    let hi = hex_decode_16(hi_bytes)?;
    let lo = hex_decode_16(lo_bytes).map_err(|pos| pos + 16)?;

    Ok((hi, lo))
}

/// Core SSE2 hex decode operating on a pre-loaded XMM register.
///
/// Classifies all 16 bytes in parallel into digit/upper/lower ranges,
/// validates via movemask, blends per-range nibble values, and packs to u64.
///
/// Returns `Err(position)` on first invalid hex character.
#[inline]
pub(crate) fn hex_decode_16_reg(input: __m128i) -> Result<u64, usize> {
    // SAFETY: All operations are SSE2 intrinsics, available on all x86_64 targets.
    unsafe {
        // Range classification using signed byte comparisons.
        // For ASCII (0x00-0x7F), signed comparison works correctly since
        // all values are non-negative in signed interpretation.

        // Digits: byte in ['0' (0x30), '9' (0x39)]
        let ge_0 = _mm_cmpgt_epi8(input, _mm_set1_epi8(0x2F)); // byte > 0x2F
        let le_9 = _mm_cmpgt_epi8(_mm_set1_epi8(0x3A), input); // 0x3A > byte
        let is_digit = _mm_and_si128(ge_0, le_9);

        // Uppercase: byte in ['A' (0x41), 'F' (0x46)]
        let ge_a_upper = _mm_cmpgt_epi8(input, _mm_set1_epi8(0x40)); // byte > 0x40
        let le_f_upper = _mm_cmpgt_epi8(_mm_set1_epi8(0x47), input); // 0x47 > byte
        let is_upper = _mm_and_si128(ge_a_upper, le_f_upper);

        // Lowercase: byte in ['a' (0x61), 'f' (0x66)]
        let ge_a_lower = _mm_cmpgt_epi8(input, _mm_set1_epi8(0x60)); // byte > 0x60
        let le_f_lower = _mm_cmpgt_epi8(_mm_set1_epi8(0x67), input); // 0x67 > byte
        let is_lower = _mm_and_si128(ge_a_lower, le_f_lower);

        // Validate: every byte must be in at least one valid range.
        // is_* masks are 0xFF where true, 0x00 where false.
        // movemask extracts bit 7 of each byte: 1 = valid, 0 = invalid.
        let valid = _mm_or_si128(_mm_or_si128(is_digit, is_upper), is_lower);
        let valid_mask = _mm_movemask_epi8(valid) as u32;
        if valid_mask != 0xFFFF {
            let invalid_bits = !valid_mask & 0xFFFF;
            return Err(invalid_bits.trailing_zeros() as usize);
        }

        // Compute nibble values for each range, then blend.
        // Only the correct range contributes (others masked to 0).
        let digit_val = _mm_sub_epi8(input, _mm_set1_epi8(0x30)); // byte - '0'
        let upper_val = _mm_sub_epi8(input, _mm_set1_epi8(55)); // byte - 'A' + 10
        let lower_val = _mm_sub_epi8(input, _mm_set1_epi8(87)); // byte - 'a' + 10

        let nibbles = _mm_or_si128(
            _mm_or_si128(
                _mm_and_si128(is_digit, digit_val),
                _mm_and_si128(is_upper, upper_val),
            ),
            _mm_and_si128(is_lower, lower_val),
        );

        // Pack 16 nibbles into 8 bytes.
        // Register layout (16-bit words, LE): each word = [even_nibble, odd_nibble]
        // Result byte = even_nibble << 4 | odd_nibble

        // Isolate even-position nibbles (low byte of each 16-bit word)
        let even = _mm_and_si128(nibbles, _mm_set1_epi16(0x00FF));
        // Shift even nibbles to high nibble position
        let even_shifted = _mm_slli_epi16(even, 4);
        // Isolate odd-position nibbles (high byte of each word → move to low byte)
        let odd = _mm_srli_epi16(nibbles, 8);
        // Combine: each 16-bit word now has the packed byte in its low byte
        let combined = _mm_or_si128(even_shifted, odd);

        // Pack 8 × 16-bit words to 8 × 8-bit bytes (saturating, but values are 0-255)
        let packed = _mm_packus_epi16(combined, _mm_setzero_si128());

        // Extract low 64 bits and byte-swap (register is LE, we want BE interpretation)
        let raw = _mm_cvtsi128_si64(packed) as u64;
        Ok(raw.swap_bytes())
    }
}

#[inline]
fn hex_decode_16_inner(bytes: &[u8; 16]) -> Result<u64, usize> {
    // SAFETY: loadu handles any alignment. Pointer valid because bytes is &[u8; 16].
    let input = unsafe { _mm_loadu_si128(bytes.as_ptr().cast()) };
    hex_decode_16_reg(input)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decode_16_matches_scalar() {
        let cases: &[&[u8; 16]] = &[
            b"0000000000000000",
            b"ffffffffffffffff",
            b"deadbeefcafebabe",
            b"DEADBEEFCAFEBABE",
            b"DeAdBeEfCaFeBaBe",
            b"0123456789abcdef",
            b"FEDCBA9876543210",
        ];

        for &input in cases {
            let sse2_result = hex_decode_16(input);
            let scalar_result = scalar::hex_decode_16(input);
            assert_eq!(
                sse2_result,
                scalar_result,
                "mismatch for {:?}",
                core::str::from_utf8(input)
            );
        }
    }

    #[test]
    fn decode_16_invalid_positions() {
        // Test invalid char at every position
        for pos in 0..16 {
            let mut input = *b"0123456789abcdef";
            input[pos] = b'g';
            let result = hex_decode_16(&input);
            assert_eq!(result, Err(pos), "expected error at pos {}", pos);
        }
    }

    #[test]
    fn decode_16_rejects_near_miss_chars() {
        // Characters just outside valid ranges
        let near_misses: &[u8] = &[
            b'/', // 0x2F, just below '0'
            b':', // 0x3A, just above '9'
            b'@', // 0x40, just below 'A'
            b'G', // 0x47, just above 'F'
            b'`', // 0x60, just below 'a'
            b'g', // 0x67, just above 'f'
            0x00, 0x10, 0x20, 0x7F, // control/misc
        ];
        for &bad in near_misses {
            let mut input = *b"0000000000000000";
            input[5] = bad;
            assert_eq!(hex_decode_16(&input), Err(5), "should reject 0x{:02x}", bad);
        }
    }

    #[test]
    fn decode_32_matches_scalar() {
        let input = b"0123456789abcdeffedcba9876543210";
        let sse2_result = hex_decode_32(input);
        let scalar_result = scalar::hex_decode_32(input);
        assert_eq!(sse2_result, scalar_result);
    }

    #[test]
    fn decode_32_error_in_second_half() {
        let mut input = *b"0123456789abcdef0123456789abcdef";
        input[20] = b'x';
        assert_eq!(hex_decode_32(&input), Err(20));
    }
}
