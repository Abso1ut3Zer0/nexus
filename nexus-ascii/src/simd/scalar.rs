//! Scalar SWAR (SIMD Within A Register) validation.
//!
//! Processes 8 bytes at a time using u64 arithmetic. This is the fallback
//! implementation for non-x86_64 architectures and serves as the reference
//! implementation for testing SIMD versions.

// =============================================================================
// ASCII Validation
// =============================================================================

/// Validate that all bytes are non-null ASCII (0x01-0x7F) using SWAR.
///
/// Processes 8 bytes at a time. Rejects both null bytes (0x00) and non-ASCII
/// bytes (> 0x7F).
#[inline]
pub fn validate_ascii(bytes: &[u8]) -> Result<(), (u8, usize)> {
    const HI: u64 = 0x8080_8080_8080_8080;
    const LO: u64 = 0x0101_0101_0101_0101;
    let mut i = 0;

    // Process 8 bytes at a time
    while i + 8 <= bytes.len() {
        // SAFETY: We just checked that i + 8 <= bytes.len()
        let chunk: [u8; 8] = unsafe { bytes.as_ptr().add(i).cast::<[u8; 8]>().read_unaligned() };
        let word = u64::from_ne_bytes(chunk);

        // High-bit check: any byte > 0x7F sets the high bit
        let hi_mask = word & HI;

        // Null check: SWAR null detection — (word - 0x0101...) & ~word & 0x8080...
        // Sets the high bit of any byte lane that was zero
        let null_mask = word.wrapping_sub(LO) & !word & HI;

        let mask = hi_mask | null_mask;
        if mask != 0 {
            let offset = (mask.trailing_zeros() / 8) as usize;
            let pos = i + offset;
            return Err((bytes[pos], pos));
        }
        i += 8;
    }

    // Handle remainder byte by byte
    while i < bytes.len() {
        if bytes[i] == 0 || bytes[i] > 127 {
            return Err((bytes[i], i));
        }
        i += 1;
    }

    Ok(())
}

// =============================================================================
// Printable Validation
// =============================================================================

/// Check if any byte in a u64 is outside printable ASCII range (0x20-0x7E).
/// Returns a non-zero mask if any byte is non-printable.
///
/// Uses SWAR technique:
/// - Catches bytes < 0x20 (control characters)
/// - Catches bytes >= 0x7F (DEL and non-ASCII)
#[inline(always)]
const fn has_non_printable(word: u64) -> u64 {
    const LO: u64 = 0x2020_2020_2020_2020; // 0x20 in each byte
    const HI: u64 = 0x7F7F_7F7F_7F7F_7F7F; // 0x7F in each byte
    const MASK: u64 = 0x8080_8080_8080_8080; // high bit of each byte

    // Check for bytes < 0x20:
    // Set high bit to prevent cross-byte borrows, then subtract 0x20.
    // If result's high bit is clear, byte was < 0x20.
    let tmp_lo = (word | MASK).wrapping_sub(LO);
    let low_violation = !tmp_lo & MASK;

    // Check for bytes >= 0x7F:
    // Set high bit to prevent cross-byte borrows, then subtract 0x7F.
    // If result's high bit is set, byte was >= 0x7F.
    let tmp_hi = (word | MASK).wrapping_sub(HI);
    let high_violation = tmp_hi & MASK;

    low_violation | high_violation
}

/// Validate that all bytes are printable ASCII (0x20-0x7E) using SWAR.
///
/// Processes 8 bytes at a time using range checking.
#[inline]
pub fn validate_printable(bytes: &[u8]) -> Result<(), (u8, usize)> {
    let mut i = 0;

    // Process 8 bytes at a time
    while i + 8 <= bytes.len() {
        // SAFETY: We just checked that i + 8 <= bytes.len()
        let chunk: [u8; 8] = unsafe { bytes.as_ptr().add(i).cast::<[u8; 8]>().read_unaligned() };
        let word = u64::from_ne_bytes(chunk);
        let mask = has_non_printable(word);
        if mask != 0 {
            // Found non-printable - use trailing_zeros to find first invalid byte
            let offset = (mask.trailing_zeros() / 8) as usize;
            let pos = i + offset;
            return Err((bytes[pos], pos));
        }
        i += 8;
    }

    // Handle remainder byte by byte
    while i < bytes.len() {
        let b = bytes[i];
        if b < 0x20 || b > 0x7E {
            return Err((b, i));
        }
        i += 1;
    }

    Ok(())
}

// =============================================================================
// Case-Insensitive Comparison
// =============================================================================

/// Compare two 8-byte words for case-insensitive ASCII equality.
///
/// Returns true if the words are equal when ignoring ASCII case.
/// Two bytes are case-insensitively equal if:
/// - They are identical, OR
/// - They differ by exactly 0x20 (bit 5) AND at least one is an ASCII letter
#[inline(always)]
const fn eq_ignore_ascii_case_word(a: u64, b: u64) -> bool {
    let xor = a ^ b;

    // Fast path: already equal
    if xor == 0 {
        return true;
    }

    // All differences must be exactly in bit 5 (0x20)
    // If any other bit differs, bytes can't be case-equivalent
    if xor & !0x2020_2020_2020_2020 != 0 {
        return false;
    }

    // For differing bytes, verify they're ASCII letters.
    // Force to lowercase, then check if in 'a'-'z' range.
    let lower_a = a | 0x2020_2020_2020_2020;

    // SWAR range check [0x61, 0x7A] (letters 'a'-'z'):
    // A byte is NOT in range if: byte < 0x61 OR byte > 0x7A
    // We detect this by checking if subtraction wraps (sets high bit)
    let below = lower_a.wrapping_sub(0x6161_6161_6161_6161);
    let above = 0x7a7a_7a7a_7a7a_7a7a_u64.wrapping_sub(lower_a);

    // High bit set in either means byte is not a letter
    let not_letter = (below | above) & 0x8080_8080_8080_8080;

    // Convert diff mask: 0x20 -> 0x80, 0x00 -> 0x00
    // This marks bytes that actually differ
    let diff_mask = (xor << 2) & 0x8080_8080_8080_8080;

    // If any differing byte is not a letter, fail
    (not_letter & diff_mask) == 0
}

/// Compare two byte slices for case-insensitive ASCII equality using SWAR.
///
/// Processes 8 bytes at a time. For ASCII letters (A-Z, a-z), case is ignored.
/// Non-letter ASCII characters must match exactly.
///
/// # Example
///
/// ```ignore
/// assert!(eq_ignore_ascii_case(b"Hello", b"HELLO"));
/// assert!(eq_ignore_ascii_case(b"BTC-USD", b"btc-usd"));
/// assert!(!eq_ignore_ascii_case(b"Hello", b"World"));
/// ```
#[inline]
#[allow(clippy::many_single_char_names)]
pub fn eq_ignore_ascii_case(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }

    let len = a.len();
    let mut i = 0;

    // Process 8 bytes at a time
    while i + 8 <= len {
        // SAFETY: We just checked that i + 8 <= len
        let word_a = unsafe { a.as_ptr().add(i).cast::<[u8; 8]>().read_unaligned() };
        // SAFETY: We just checked that i + 8 <= len
        let word_b = unsafe { b.as_ptr().add(i).cast::<[u8; 8]>().read_unaligned() };

        if !eq_ignore_ascii_case_word(u64::from_ne_bytes(word_a), u64::from_ne_bytes(word_b)) {
            return false;
        }
        i += 8;
    }

    // Handle remainder with branchless comparison
    // This avoids branch misprediction on case-differing letter bytes
    let mut valid_acc: u8 = 1;
    while i < len {
        let x = a[i];
        let y = b[i];
        let xor = x ^ y;

        // same = 1 if bytes are identical
        let same = (xor == 0) as u8;

        // case_diff_only = 1 if bytes differ by exactly 0x20 (bit 5)
        let case_diff_only = (xor == 0x20) as u8;

        // is_letter = 1 if (x | 0x20) is in 'a'..'z'
        let lower = x | 0x20;
        let is_letter = (lower.wrapping_sub(b'a') < 26) as u8;

        // valid = same OR (case_diff_only AND is_letter)
        // Branchless: use bitwise OR/AND instead of || / &&
        let valid = same | (case_diff_only & is_letter);

        valid_acc &= valid;
        i += 1;
    }

    valid_acc != 0
}

// =============================================================================
// Branchless Case Conversion
// =============================================================================

/// Convert a byte to lowercase using branchless arithmetic.
///
/// Only ASCII letters (A-Z) are affected; all other bytes pass through unchanged.
#[inline(always)]
pub const fn to_lowercase_branchless(byte: u8) -> u8 {
    // is_upper = 1 if byte in A-Z, 0 otherwise
    // A-Z range: 0x41-0x5A
    // (byte - 0x41) < 26 means byte is in A-Z
    let in_range = (byte.wrapping_sub(b'A') < 26) as u8;
    byte | (in_range << 5) // Add 0x20 if uppercase
}

/// Convert a byte to uppercase using branchless arithmetic.
///
/// Only ASCII letters (a-z) are affected; all other bytes pass through unchanged.
#[inline(always)]
pub const fn to_uppercase_branchless(byte: u8) -> u8 {
    // is_lower = 1 if byte in a-z, 0 otherwise
    // a-z range: 0x61-0x7A
    let in_range = (byte.wrapping_sub(b'a') < 26) as u8;
    byte & !(in_range << 5) // Clear bit 5 if lowercase
}

/// Convert a u64 word to lowercase using SWAR.
///
/// All ASCII uppercase letters (A-Z) become lowercase (a-z).
/// Non-letter bytes are unchanged.
#[inline(always)]
pub const fn to_lowercase_word(word: u64) -> u64 {
    // For each byte, set bit 5 (OR with 0x20) if it's in A-Z range [0x41, 0x5A]
    //
    // SWAR range check technique:
    // - Add (0x80 - 'A') = 0x3F: if byte >= 'A', result has high bit set
    // - Add (0x80 - 'Z' - 1) = 0x25: if byte > 'Z', result has high bit set
    // - is_upper = (ge_a) AND NOT(gt_z)

    let ge_a = word.wrapping_add(0x3F3F_3F3F_3F3F_3F3F); // High bit set if >= 'A'
    let gt_z = word.wrapping_add(0x2525_2525_2525_2525); // High bit set if > 'Z'

    // Byte is uppercase if: high bit set in ge_a AND high bit clear in gt_z
    let is_upper = ge_a & !gt_z & 0x8080_8080_8080_8080;

    // Convert 0x80 -> 0x20 for the mask
    let mask = is_upper >> 2;

    word | mask
}

/// Convert a u64 word to uppercase using SWAR.
///
/// All ASCII lowercase letters (a-z) become uppercase (A-Z).
/// Non-letter bytes are unchanged.
#[inline(always)]
pub const fn to_uppercase_word(word: u64) -> u64 {
    // For each byte, clear bit 5 (AND with ~0x20) if it's in a-z range [0x61, 0x7A]
    //
    // SWAR range check technique:
    // - Add (0x80 - 'a') = 0x1F: if byte >= 'a', result has high bit set
    // - Add (0x80 - 'z' - 1) = 0x05: if byte > 'z', result has high bit set
    // - is_lower = (ge_a) AND NOT(gt_z)

    let ge_a = word.wrapping_add(0x1F1F_1F1F_1F1F_1F1F); // High bit set if >= 'a'
    let gt_z = word.wrapping_add(0x0505_0505_0505_0505); // High bit set if > 'z'

    // Byte is lowercase if: high bit set in ge_a AND high bit clear in gt_z
    let is_lower = ge_a & !gt_z & 0x8080_8080_8080_8080;

    // Convert 0x80 -> 0x20 for the mask, then clear bit 5 for lowercase letters
    let mask = is_lower >> 2;

    word & !mask
}

/// Convert byte slice to lowercase in-place using SWAR.
#[inline]
pub fn make_lowercase(bytes: &mut [u8]) {
    let len = bytes.len();
    if len == 0 {
        return;
    }

    // Short strings: byte-by-byte (at most 7 iterations)
    if len < 8 {
        for b in bytes.iter_mut() {
            *b = to_lowercase_branchless(*b);
        }
        return;
    }

    // Process 8 bytes at a time
    let mut i = 0;
    while i + 8 <= len {
        // SAFETY: We just checked that i + 8 <= len
        let chunk: [u8; 8] = unsafe { bytes.as_ptr().add(i).cast::<[u8; 8]>().read_unaligned() };
        let word = u64::from_ne_bytes(chunk);
        let lower = to_lowercase_word(word);

        // Write back
        // SAFETY: Same bounds as read
        unsafe {
            bytes
                .as_mut_ptr()
                .add(i)
                .cast::<[u8; 8]>()
                .write_unaligned(lower.to_ne_bytes());
        }
        i += 8;
    }

    // Handle remainder by processing last 8 bytes (overlapping with previous)
    // This is branchless for the common case and safe because:
    // 1. len >= 8 (checked above)
    // 2. Lowercase conversion is idempotent
    if i < len {
        // SAFETY: len >= 8, so len - 8 is valid, and we can read 8 bytes ending at len
        let chunk: [u8; 8] = unsafe {
            bytes
                .as_ptr()
                .add(len - 8)
                .cast::<[u8; 8]>()
                .read_unaligned()
        };
        let word = u64::from_ne_bytes(chunk);
        let lower = to_lowercase_word(word);
        // SAFETY: len >= 8, so len - 8 is valid; write to last 8 bytes.
        unsafe {
            bytes
                .as_mut_ptr()
                .add(len - 8)
                .cast::<[u8; 8]>()
                .write_unaligned(lower.to_ne_bytes());
        }
    }
}

/// Convert byte slice to uppercase in-place using SWAR.
#[inline]
pub fn make_uppercase(bytes: &mut [u8]) {
    let len = bytes.len();
    if len == 0 {
        return;
    }

    // Short strings: byte-by-byte (at most 7 iterations)
    if len < 8 {
        for b in bytes.iter_mut() {
            *b = to_uppercase_branchless(*b);
        }
        return;
    }

    // Process 8 bytes at a time
    let mut i = 0;
    while i + 8 <= len {
        // SAFETY: We just checked that i + 8 <= len
        let chunk: [u8; 8] = unsafe { bytes.as_ptr().add(i).cast::<[u8; 8]>().read_unaligned() };
        let word = u64::from_ne_bytes(chunk);
        let upper = to_uppercase_word(word);

        // Write back
        // SAFETY: We just checked that i + 8 <= len
        unsafe {
            bytes
                .as_mut_ptr()
                .add(i)
                .cast::<[u8; 8]>()
                .write_unaligned(upper.to_ne_bytes());
        }
        i += 8;
    }

    // Handle remainder by processing last 8 bytes (overlapping with previous)
    // This is branchless for the common case and safe because:
    // 1. len >= 8 (checked above)
    // 2. Uppercase conversion is idempotent
    if i < len {
        // SAFETY: len >= 8, so len - 8 is valid, and we can read 8 bytes ending at len
        let chunk: [u8; 8] = unsafe {
            bytes
                .as_ptr()
                .add(len - 8)
                .cast::<[u8; 8]>()
                .read_unaligned()
        };
        let word = u64::from_ne_bytes(chunk);
        let upper = to_uppercase_word(word);
        // SAFETY: len >= 8, so len - 8 is valid; write to last 8 bytes.
        unsafe {
            bytes
                .as_mut_ptr()
                .add(len - 8)
                .cast::<[u8; 8]>()
                .write_unaligned(upper.to_ne_bytes());
        }
    }
}

// =============================================================================
// Control Character Detection
// =============================================================================

/// Check if a u64 word contains any control characters (< 0x20 or == 0x7F).
///
/// Returns non-zero if any byte is a control character.
#[allow(dead_code)]
#[inline(always)]
const fn has_control_chars_word(word: u64) -> u64 {
    const MASK: u64 = 0x8080_8080_8080_8080;

    // Check for bytes < 0x20:
    // Set high bit to prevent cross-byte borrows, then subtract 0x20.
    // If result's high bit is clear, byte was < 0x20.
    let tmp = (word | MASK).wrapping_sub(0x2020_2020_2020_2020);
    let below_space = !tmp & MASK;

    // Check for 0x7F (DEL):
    // XOR with 0x7F, then check if any byte is zero.
    // (byte ^ 0x7F) == 0 means byte was 0x7F
    let del_xor = word ^ 0x7F7F_7F7F_7F7F_7F7F;
    // Standard SWAR zero-byte detection: ((v - 0x01) & ~v & 0x80) is set if v has a zero byte
    let has_del = del_xor.wrapping_sub(0x0101_0101_0101_0101) & !del_xor & MASK;

    below_space | has_del
}

/// Check if the byte slice contains any control characters using SWAR.
///
/// Control characters are bytes < 0x20 or == 0x7F.
/// Returns true if any control character is found.
#[allow(dead_code)]
#[inline]
pub fn contains_control_chars(bytes: &[u8]) -> bool {
    let len = bytes.len();
    if len == 0 {
        return false;
    }

    // Short strings: byte-by-byte with branchless accumulation
    if len < 8 {
        let mut found: u8 = 0;
        for &b in bytes {
            #[allow(clippy::needless_bitwise_bool)]
            let is_ctrl = ((b < 0x20) | (b == 0x7F)) as u8;
            found |= is_ctrl;
        }
        return found != 0;
    }

    // Process 8 bytes at a time
    let mut i = 0;
    while i + 8 <= len {
        // SAFETY: We just checked that i + 8 <= len
        let chunk: [u8; 8] = unsafe { bytes.as_ptr().add(i).cast::<[u8; 8]>().read_unaligned() };
        let word = u64::from_ne_bytes(chunk);
        if has_control_chars_word(word) != 0 {
            return true;
        }
        i += 8;
    }

    // Handle remainder by checking last 8 bytes (overlapping with previous)
    // This is safe because:
    // 1. len >= 8 (checked above)
    // 2. Re-checking bytes is harmless for OR operation
    if i < len {
        // SAFETY: len >= 8 (checked above), so len - 8 is valid.
        let chunk: [u8; 8] = unsafe {
            bytes
                .as_ptr()
                .add(len - 8)
                .cast::<[u8; 8]>()
                .read_unaligned()
        };
        let word = u64::from_ne_bytes(chunk);
        return has_control_chars_word(word) != 0;
    }

    false
}

/// Check if all bytes are printable ASCII (0x20-0x7E) using SWAR.
///
/// Returns true if all bytes are printable, false otherwise.
#[allow(dead_code)]
#[inline]
pub fn is_all_printable(bytes: &[u8]) -> bool {
    let len = bytes.len();
    if len == 0 {
        return true;
    }

    // Short strings: byte-by-byte with branchless accumulation
    if len < 8 {
        let mut valid_acc: u8 = 1;
        for &b in bytes {
            #[allow(clippy::needless_bitwise_bool)]
            let is_printable = ((b >= 0x20) & (b <= 0x7E)) as u8;
            valid_acc &= is_printable;
        }
        return valid_acc != 0;
    }

    // Process 8 bytes at a time
    let mut i = 0;
    while i + 8 <= len {
        // SAFETY: We just checked that i + 8 <= len
        let chunk: [u8; 8] = unsafe { bytes.as_ptr().add(i).cast::<[u8; 8]>().read_unaligned() };
        let word = u64::from_ne_bytes(chunk);
        if has_non_printable(word) != 0 {
            return false;
        }
        i += 8;
    }

    // Handle remainder by checking last 8 bytes (overlapping with previous)
    // This is safe because:
    // 1. len >= 8 (checked above)
    // 2. Re-checking bytes is harmless for AND operation
    if i < len {
        // SAFETY: len >= 8 (checked above), so len - 8 is valid.
        let chunk: [u8; 8] = unsafe {
            bytes
                .as_ptr()
                .add(len - 8)
                .cast::<[u8; 8]>()
                .read_unaligned()
        };
        let word = u64::from_ne_bytes(chunk);
        return has_non_printable(word) == 0;
    }

    true
}

// =============================================================================
// Numeric Validation
// =============================================================================

/// Check if any byte in a u64 is outside digit range ('0'-'9' / 0x30-0x39).
/// Returns a non-zero mask if any byte is non-digit.
///
/// Uses SWAR technique similar to has_non_printable:
/// - Set high bit to prevent cross-byte borrows
/// - Check if byte < '0' or byte > '9'
#[inline(always)]
const fn has_non_digit(word: u64) -> u64 {
    const MASK: u64 = 0x8080_8080_8080_8080;
    const ZERO: u64 = 0x3030_3030_3030_3030; // '0'
    const NINE_PLUS_1: u64 = 0x3A3A_3A3A_3A3A_3A3A; // '9' + 1 = ':'

    // Check byte < '0': Set high bit, subtract '0'.
    // If result's high bit is clear, byte was < '0'.
    let tmp_lo = (word | MASK).wrapping_sub(ZERO);
    let too_low = !tmp_lo & MASK;

    // Check byte >= ':' (i.e., byte > '9'): Set high bit, subtract ':'.
    // If result's high bit is set, byte was >= ':'.
    let tmp_hi = (word | MASK).wrapping_sub(NINE_PLUS_1);
    let too_high = tmp_hi & MASK;

    too_low | too_high
}

/// Check if all bytes are ASCII digits ('0'-'9') using SWAR.
///
/// Returns true if all bytes are digits, false otherwise.
/// An empty slice returns true.
#[inline]
pub fn is_all_numeric(bytes: &[u8]) -> bool {
    let len = bytes.len();
    if len == 0 {
        return true;
    }

    // Short strings: byte-by-byte with branchless accumulation
    if len < 8 {
        let mut valid_acc: u8 = 1;
        for &b in bytes {
            let is_digit = (b.wrapping_sub(b'0') < 10) as u8;
            valid_acc &= is_digit;
        }
        return valid_acc != 0;
    }

    // Process 8 bytes at a time
    let mut i = 0;
    while i + 8 <= len {
        // SAFETY: We just checked that i + 8 <= len
        let chunk: [u8; 8] = unsafe { bytes.as_ptr().add(i).cast::<[u8; 8]>().read_unaligned() };
        let word = u64::from_ne_bytes(chunk);
        if has_non_digit(word) != 0 {
            return false;
        }
        i += 8;
    }

    // Handle remainder by checking last 8 bytes (overlapping)
    if i < len {
        // SAFETY: len >= 8 (checked above), so len - 8 is valid.
        let chunk: [u8; 8] = unsafe {
            bytes
                .as_ptr()
                .add(len - 8)
                .cast::<[u8; 8]>()
                .read_unaligned()
        };
        let word = u64::from_ne_bytes(chunk);
        return has_non_digit(word) == 0;
    }

    true
}

// =============================================================================
// Alphanumeric Validation
// =============================================================================

/// Check if any byte in a u64 is outside alphanumeric range.
/// Returns a non-zero mask if any byte is non-alphanumeric.
///
/// Alphanumeric = digits ('0'-'9') OR uppercase ('A'-'Z') OR lowercase ('a'-'z').
/// Uses SWAR range checking for each range, then combines.
#[inline(always)]
const fn has_non_alphanumeric(word: u64) -> u64 {
    const MASK: u64 = 0x8080_8080_8080_8080;

    // For each range [L, H], a byte is in range if NOT(byte < L) AND NOT(byte > H)
    // Using the standard SWAR technique with high bit set to prevent borrows.

    // Digit range ['0', '9'] = [0x30, 0x39]
    let d_lo = (word | MASK).wrapping_sub(0x3030_3030_3030_3030);
    let d_hi = (word | MASK).wrapping_sub(0x3A3A_3A3A_3A3A_3A3A);
    // is_digit: NOT(below '0') AND NOT(above '9')
    // below '0' = high bit clear in d_lo, above '9' = high bit set in d_hi
    let is_digit = d_lo & !d_hi & MASK;

    // Uppercase range ['A', 'Z'] = [0x41, 0x5A]
    let u_lo = (word | MASK).wrapping_sub(0x4141_4141_4141_4141);
    let u_hi = (word | MASK).wrapping_sub(0x5B5B_5B5B_5B5B_5B5B);
    let is_upper = u_lo & !u_hi & MASK;

    // Lowercase range ['a', 'z'] = [0x61, 0x7A]
    let l_lo = (word | MASK).wrapping_sub(0x6161_6161_6161_6161);
    let l_hi = (word | MASK).wrapping_sub(0x7B7B_7B7B_7B7B_7B7B);
    let is_lower = l_lo & !l_hi & MASK;

    // Byte is alphanumeric if any of the three ranges match
    // is_alnum has high bit SET for alphanumeric bytes
    let is_alnum = is_digit | is_upper | is_lower;

    // Return mask with high bit SET for NON-alphanumeric bytes
    !is_alnum & MASK
}

/// Check if all bytes are ASCII alphanumeric (0-9, A-Z, a-z) using SWAR.
///
/// Returns true if all bytes are alphanumeric, false otherwise.
/// An empty slice returns true.
#[inline]
pub fn is_all_alphanumeric(bytes: &[u8]) -> bool {
    let len = bytes.len();
    if len == 0 {
        return true;
    }

    // Short strings: byte-by-byte with branchless accumulation
    if len < 8 {
        let mut valid_acc: u8 = 1;
        for &b in bytes {
            let is_alnum = b.is_ascii_alphanumeric() as u8;
            valid_acc &= is_alnum;
        }
        return valid_acc != 0;
    }

    // Process 8 bytes at a time
    let mut i = 0;
    while i + 8 <= len {
        // SAFETY: We just checked that i + 8 <= len
        let chunk: [u8; 8] = unsafe { bytes.as_ptr().add(i).cast::<[u8; 8]>().read_unaligned() };
        let word = u64::from_ne_bytes(chunk);
        if has_non_alphanumeric(word) != 0 {
            return false;
        }
        i += 8;
    }

    // Handle remainder by checking last 8 bytes (overlapping)
    if i < len {
        // SAFETY: len >= 8 (checked above), so len - 8 is valid.
        let chunk: [u8; 8] = unsafe {
            bytes
                .as_ptr()
                .add(len - 8)
                .cast::<[u8; 8]>()
                .read_unaligned()
        };
        let word = u64::from_ne_bytes(chunk);
        return has_non_alphanumeric(word) == 0;
    }

    true
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_validate_ascii_valid() {
        assert!(validate_ascii(b"Hello, World!").is_ok());
        assert!(validate_ascii(b"").is_ok());
        assert!(validate_ascii(&[1u8]).is_ok());
        assert!(validate_ascii(&[127u8]).is_ok());
    }

    #[test]
    fn test_validate_ascii_null_rejected() {
        assert_eq!(validate_ascii(&[0u8]), Err((0, 0)));
    }

    #[test]
    fn test_validate_ascii_invalid() {
        assert_eq!(validate_ascii(&[128u8]), Err((128, 0)));
        assert_eq!(validate_ascii(&[255u8]), Err((255, 0)));
        assert_eq!(validate_ascii(b"Hello\x80"), Err((0x80, 5)));
    }

    #[test]
    fn test_validate_printable_valid() {
        assert!(validate_printable(b"Hello, World!").is_ok());
        assert!(validate_printable(b"").is_ok());
        assert!(validate_printable(b" ").is_ok());
        assert!(validate_printable(b"~").is_ok());
    }

    #[test]
    fn test_validate_printable_invalid() {
        assert_eq!(validate_printable(&[0x00]), Err((0x00, 0)));
        assert_eq!(validate_printable(&[0x1F]), Err((0x1F, 0)));
        assert_eq!(validate_printable(&[0x7F]), Err((0x7F, 0)));
        assert_eq!(validate_printable(&[0x80]), Err((0x80, 0)));
    }

    #[test]
    fn test_has_non_printable_boundaries() {
        // Test the SWAR function directly
        let all_space = 0x2020_2020_2020_2020u64;
        assert_eq!(has_non_printable(all_space), 0);

        let all_tilde = 0x7E7E_7E7E_7E7E_7E7Eu64;
        assert_eq!(has_non_printable(all_tilde), 0);

        // 0x1F in first byte (control char)
        let with_control = 0x2020_2020_2020_201Fu64;
        assert_ne!(has_non_printable(with_control), 0);

        // 0x7F in first byte (DEL)
        let with_del = 0x2020_2020_2020_207Fu64;
        assert_ne!(has_non_printable(with_del), 0);
    }

    // -------------------------------------------------------------------------
    // Case-insensitive comparison tests
    // -------------------------------------------------------------------------

    #[test]
    fn test_eq_ignore_ascii_case_equal() {
        assert!(eq_ignore_ascii_case(b"hello", b"hello"));
        assert!(eq_ignore_ascii_case(b"HELLO", b"HELLO"));
        assert!(eq_ignore_ascii_case(b"", b""));
    }

    #[test]
    fn test_eq_ignore_ascii_case_different_case() {
        assert!(eq_ignore_ascii_case(b"hello", b"HELLO"));
        assert!(eq_ignore_ascii_case(b"HELLO", b"hello"));
        assert!(eq_ignore_ascii_case(b"HeLLo", b"hEllO"));
    }

    #[test]
    fn test_eq_ignore_ascii_case_with_symbols() {
        assert!(eq_ignore_ascii_case(b"BTC-USD", b"btc-usd"));
        assert!(eq_ignore_ascii_case(b"Hello, World!", b"HELLO, WORLD!"));
        assert!(eq_ignore_ascii_case(b"abc123xyz", b"ABC123XYZ"));
    }

    #[test]
    fn test_eq_ignore_ascii_case_different() {
        assert!(!eq_ignore_ascii_case(b"hello", b"world"));
        assert!(!eq_ignore_ascii_case(b"abc", b"abd"));
        assert!(!eq_ignore_ascii_case(b"hello", b"hell"));
    }

    #[test]
    fn test_eq_ignore_ascii_case_non_letter_differs_by_0x20() {
        // '@' (0x40) and '`' (0x60) differ by 0x20 but neither is a letter
        assert!(!eq_ignore_ascii_case(b"@", b"`"));
        // '!' (0x21) and '!' (0x21) are equal
        assert!(eq_ignore_ascii_case(b"!", b"!"));
        // '1' and '1' are equal
        assert!(eq_ignore_ascii_case(b"1", b"1"));
        // But '1' (0x31) and 'Q' (0x51) differ by 0x20, '1' is not a letter
        // Actually wait: 0x51 - 0x31 = 0x20, but 'Q' is a letter, '1' is not
        // eq_ignore_ascii_case should return false because '1' is not a letter
        assert!(!eq_ignore_ascii_case(b"1", b"Q"));
    }

    #[test]
    fn test_eq_ignore_ascii_case_long_strings() {
        // Test SWAR path (> 8 bytes)
        assert!(eq_ignore_ascii_case(
            b"The Quick Brown Fox",
            b"THE QUICK BROWN FOX"
        ));
        assert!(eq_ignore_ascii_case(
            b"abcdefghijklmnopqrstuvwxyz",
            b"ABCDEFGHIJKLMNOPQRSTUVWXYZ"
        ));
    }

    #[test]
    fn test_eq_ignore_ascii_case_boundary_letters() {
        // Test boundary letters A/a and Z/z
        assert!(eq_ignore_ascii_case(b"A", b"a"));
        assert!(eq_ignore_ascii_case(b"Z", b"z"));
        assert!(eq_ignore_ascii_case(b"AZ", b"az"));
        assert!(eq_ignore_ascii_case(b"za", b"ZA"));
    }

    // -------------------------------------------------------------------------
    // Branchless case conversion tests
    // -------------------------------------------------------------------------

    #[test]
    fn test_to_lowercase_branchless() {
        assert_eq!(to_lowercase_branchless(b'A'), b'a');
        assert_eq!(to_lowercase_branchless(b'Z'), b'z');
        assert_eq!(to_lowercase_branchless(b'M'), b'm');
        // Already lowercase
        assert_eq!(to_lowercase_branchless(b'a'), b'a');
        // Non-letters unchanged
        assert_eq!(to_lowercase_branchless(b'1'), b'1');
        assert_eq!(to_lowercase_branchless(b'@'), b'@');
        assert_eq!(to_lowercase_branchless(b' '), b' ');
    }

    #[test]
    fn test_to_uppercase_branchless() {
        assert_eq!(to_uppercase_branchless(b'a'), b'A');
        assert_eq!(to_uppercase_branchless(b'z'), b'Z');
        assert_eq!(to_uppercase_branchless(b'm'), b'M');
        // Already uppercase
        assert_eq!(to_uppercase_branchless(b'A'), b'A');
        // Non-letters unchanged
        assert_eq!(to_uppercase_branchless(b'1'), b'1');
        assert_eq!(to_uppercase_branchless(b'@'), b'@');
        assert_eq!(to_uppercase_branchless(b' '), b' ');
    }

    #[test]
    fn test_make_lowercase() {
        let mut bytes = *b"Hello, World!";
        make_lowercase(&mut bytes);
        assert_eq!(&bytes, b"hello, world!");

        let mut bytes = *b"BTC-USD";
        make_lowercase(&mut bytes);
        assert_eq!(&bytes, b"btc-usd");

        // Long string to test SWAR path
        let mut bytes = *b"ABCDEFGHIJKLMNOPQRSTUVWXYZ";
        make_lowercase(&mut bytes);
        assert_eq!(&bytes, b"abcdefghijklmnopqrstuvwxyz");
    }

    #[test]
    fn test_make_uppercase() {
        let mut bytes = *b"Hello, World!";
        make_uppercase(&mut bytes);
        assert_eq!(&bytes, b"HELLO, WORLD!");

        let mut bytes = *b"btc-usd";
        make_uppercase(&mut bytes);
        assert_eq!(&bytes, b"BTC-USD");

        // Long string to test SWAR path
        let mut bytes = *b"abcdefghijklmnopqrstuvwxyz";
        make_uppercase(&mut bytes);
        assert_eq!(&bytes, b"ABCDEFGHIJKLMNOPQRSTUVWXYZ");
    }

    #[test]
    fn test_case_conversion_all_ascii() {
        // Verify all ASCII bytes are handled correctly
        for b in 0u8..=127 {
            let lower = to_lowercase_branchless(b);
            let upper = to_uppercase_branchless(b);

            if b.is_ascii_uppercase() {
                assert_eq!(lower, b + 32);
                assert_eq!(upper, b);
            } else if b.is_ascii_lowercase() {
                assert_eq!(lower, b);
                assert_eq!(upper, b - 32);
            } else {
                assert_eq!(lower, b);
                assert_eq!(upper, b);
            }
        }
    }

    // -------------------------------------------------------------------------
    // Control character detection tests
    // -------------------------------------------------------------------------

    #[test]
    fn test_contains_control_chars_none() {
        assert!(!contains_control_chars(b"Hello, World!"));
        assert!(!contains_control_chars(b"BTC-USD"));
        assert!(!contains_control_chars(b""));
        assert!(!contains_control_chars(b" ")); // Space is 0x20, not control
        assert!(!contains_control_chars(b"~")); // 0x7E is printable
    }

    #[test]
    fn test_contains_control_chars_found() {
        assert!(contains_control_chars(b"\x00")); // NUL
        assert!(contains_control_chars(b"\x01")); // SOH
        assert!(contains_control_chars(b"\x1F")); // Unit separator
        assert!(contains_control_chars(b"\x7F")); // DEL
        assert!(contains_control_chars(b"Hello\x00World"));
        assert!(contains_control_chars(b"\nNewline"));
        assert!(contains_control_chars(b"Tab\there"));
    }

    #[test]
    fn test_contains_control_chars_long() {
        // Test SWAR path (> 8 bytes)
        assert!(!contains_control_chars(
            b"This is a long string without control chars"
        ));
        assert!(contains_control_chars(b"This has a\x00null in the middle"));
        // DEL at position > 8
        assert!(contains_control_chars(b"12345678\x7F"));
    }

    #[test]
    fn test_has_control_chars_word() {
        // All printable
        let printable = u64::from_ne_bytes(*b"ABCDEFGH");
        assert_eq!(has_control_chars_word(printable), 0);

        // With NUL
        let with_nul = u64::from_ne_bytes(*b"\x00BCDEFGH");
        assert_ne!(has_control_chars_word(with_nul), 0);

        // With DEL (0x7F)
        let with_del = u64::from_ne_bytes(*b"ABCDEFG\x7F");
        assert_ne!(has_control_chars_word(with_del), 0);

        // With newline
        let with_newline = u64::from_ne_bytes(*b"ABC\nEFGH");
        assert_ne!(has_control_chars_word(with_newline), 0);
    }

    // -------------------------------------------------------------------------
    // is_all_printable tests
    // -------------------------------------------------------------------------

    #[test]
    fn test_is_all_printable_true() {
        assert!(is_all_printable(b"Hello, World!"));
        assert!(is_all_printable(b"BTC-USD"));
        assert!(is_all_printable(b""));
        assert!(is_all_printable(b" ")); // Space is printable
        assert!(is_all_printable(b"~")); // 0x7E is printable
        assert!(is_all_printable(b" ~")); // Boundaries
    }

    #[test]
    fn test_is_all_printable_false() {
        assert!(!is_all_printable(b"\x00")); // NUL
        assert!(!is_all_printable(b"\x1F")); // Control
        assert!(!is_all_printable(b"\x7F")); // DEL
        assert!(!is_all_printable(b"\x80")); // Non-ASCII
        assert!(!is_all_printable(b"Hello\nWorld")); // Newline
    }

    #[test]
    fn test_is_all_printable_long() {
        // Test SWAR path (> 8 bytes)
        assert!(is_all_printable(
            b"This is a long string of printable chars"
        ));
        assert!(!is_all_printable(b"This has a\x00null in the middle"));
        // Non-printable at position > 8
        assert!(!is_all_printable(b"12345678\x7F"));
        assert!(!is_all_printable(b"12345678\x80"));
    }

    // -------------------------------------------------------------------------
    // Exhaustive correctness tests (compare against stdlib/naive)
    // -------------------------------------------------------------------------

    /// Reference implementation for eq_ignore_ascii_case
    fn eq_ignore_ascii_case_naive(a: &[u8], b: &[u8]) -> bool {
        a.eq_ignore_ascii_case(b)
    }

    /// Reference implementation for contains_control_chars
    fn contains_control_chars_naive(bytes: &[u8]) -> bool {
        bytes.iter().any(|&b| b < 0x20 || b == 0x7F)
    }

    /// Reference implementation for is_all_printable
    fn is_all_printable_naive(bytes: &[u8]) -> bool {
        bytes.iter().all(|&b| (0x20..=0x7E).contains(&b))
    }

    #[test]
    fn test_eq_ignore_ascii_case_exhaustive_single_byte() {
        // Test all possible single-byte pairs
        for a in 0u8..=127 {
            for b in 0u8..=127 {
                let expected = eq_ignore_ascii_case_naive(&[a], &[b]);
                let actual = eq_ignore_ascii_case(&[a], &[b]);
                assert_eq!(
                    actual, expected,
                    "mismatch for bytes {:02x} ({:?}) vs {:02x} ({:?})",
                    a, a as char, b, b as char
                );
            }
        }
    }

    #[test]
    fn test_eq_ignore_ascii_case_exhaustive_lengths() {
        // Test various lengths with all-letter content
        for len in 0..=40 {
            let a: Vec<u8> = (0..len).map(|i| b'A' + (i % 26) as u8).collect();
            let b: Vec<u8> = (0..len).map(|i| b'a' + (i % 26) as u8).collect();

            let expected = eq_ignore_ascii_case_naive(&a, &b);
            let actual = eq_ignore_ascii_case(&a, &b);
            assert_eq!(actual, expected, "mismatch at len={}", len);

            // Also test same case
            let expected_same = eq_ignore_ascii_case_naive(&a, &a);
            let actual_same = eq_ignore_ascii_case(&a, &a);
            assert_eq!(
                actual_same, expected_same,
                "same-case mismatch at len={}",
                len
            );
        }
    }

    #[test]
    fn test_eq_ignore_ascii_case_non_letter_0x20_diff() {
        // Critical edge case: non-letters that differ by exactly 0x20
        // These should NOT be considered equal
        let pairs: &[(u8, u8)] = &[
            (b'@', b'`'),  // 0x40 vs 0x60
            (b'[', b'{'),  // 0x5B vs 0x7B
            (b'\\', b'|'), // 0x5C vs 0x7C
            (b']', b'}'),  // 0x5D vs 0x7D
            (b'^', b'~'),  // 0x5E vs 0x7E
            (b'!', b'A'),  // 0x21 vs 0x41 - but 'A' IS a letter
            (b'1', b'Q'),  // 0x31 vs 0x51 - 'Q' is letter, '1' is not
            (b' ', b'@'),  // 0x20 vs 0x40
        ];

        for &(a, b) in pairs {
            let expected = eq_ignore_ascii_case_naive(&[a], &[b]);
            let actual = eq_ignore_ascii_case(&[a], &[b]);
            assert_eq!(
                actual, expected,
                "0x20-diff pair: {:02x} ({:?}) vs {:02x} ({:?})",
                a, a as char, b, b as char
            );
        }
    }

    #[test]
    fn test_contains_control_chars_exhaustive_single_byte() {
        // Test all possible single bytes
        for b in 0u8..=255 {
            let expected = contains_control_chars_naive(&[b]);
            let actual = contains_control_chars(&[b]);
            assert_eq!(actual, expected, "mismatch for byte {:02x}", b);
        }
    }

    #[test]
    fn test_contains_control_chars_exhaustive_positions() {
        // Test control char at every position in strings of various lengths
        for len in 1..=40 {
            for pos in 0..len {
                for ctrl in [0x00u8, 0x01, 0x0A, 0x1F, 0x7F] {
                    let mut bytes: Vec<u8> = vec![b'A'; len];
                    bytes[pos] = ctrl;

                    let expected = contains_control_chars_naive(&bytes);
                    let actual = contains_control_chars(&bytes);
                    assert_eq!(
                        actual, expected,
                        "mismatch: len={}, pos={}, ctrl={:02x}",
                        len, pos, ctrl
                    );
                }
            }
        }
    }

    #[test]
    fn test_is_all_printable_exhaustive_single_byte() {
        // Test all possible single bytes
        for b in 0u8..=255 {
            let expected = is_all_printable_naive(&[b]);
            let actual = is_all_printable(&[b]);
            assert_eq!(actual, expected, "mismatch for byte {:02x}", b);
        }
    }

    #[test]
    fn test_is_all_printable_exhaustive_positions() {
        // Test non-printable at every position in strings of various lengths
        for len in 1..=40 {
            for pos in 0..len {
                for non_print in [0x00u8, 0x1F, 0x7F, 0x80, 0xFF] {
                    let mut bytes: Vec<u8> = vec![b'A'; len];
                    bytes[pos] = non_print;

                    let expected = is_all_printable_naive(&bytes);
                    let actual = is_all_printable(&bytes);
                    assert_eq!(
                        actual, expected,
                        "mismatch: len={}, pos={}, byte={:02x}",
                        len, pos, non_print
                    );
                }
            }
        }
    }

    #[test]
    fn test_is_all_printable_boundary_bytes() {
        // Test exact boundaries
        assert!(!is_all_printable(&[0x1F])); // Just below printable
        assert!(is_all_printable(&[0x20])); // First printable (space)
        assert!(is_all_printable(&[0x7E])); // Last printable (tilde)
        assert!(!is_all_printable(&[0x7F])); // DEL - not printable
        assert!(!is_all_printable(&[0x80])); // First non-ASCII

        // Verify against naive
        for b in [0x1F, 0x20, 0x7E, 0x7F, 0x80] {
            assert_eq!(
                is_all_printable(&[b]),
                is_all_printable_naive(&[b]),
                "boundary mismatch at {:02x}",
                b
            );
        }
    }

    #[test]
    fn test_contains_control_chars_boundary_bytes() {
        // Test exact boundaries
        assert!(contains_control_chars(&[0x1F])); // Last control char before space
        assert!(!contains_control_chars(&[0x20])); // Space - not control
        assert!(!contains_control_chars(&[0x7E])); // Tilde - not control
        assert!(contains_control_chars(&[0x7F])); // DEL - is control
        assert!(!contains_control_chars(&[0x80])); // Non-ASCII, but not "control" by our def

        // Verify against naive
        for b in [0x1F, 0x20, 0x7E, 0x7F, 0x80] {
            assert_eq!(
                contains_control_chars(&[b]),
                contains_control_chars_naive(&[b]),
                "boundary mismatch at {:02x}",
                b
            );
        }
    }

    // -------------------------------------------------------------------------
    // is_all_numeric tests
    // -------------------------------------------------------------------------

    fn is_all_numeric_naive(bytes: &[u8]) -> bool {
        bytes.iter().all(|&b| b.is_ascii_digit())
    }

    #[test]
    fn test_is_all_numeric_valid() {
        assert!(is_all_numeric(b""));
        assert!(is_all_numeric(b"0"));
        assert!(is_all_numeric(b"9"));
        assert!(is_all_numeric(b"0123456789"));
        assert!(is_all_numeric(b"12345678901234567890")); // > 8 bytes
    }

    #[test]
    fn test_is_all_numeric_invalid() {
        assert!(!is_all_numeric(b"a"));
        assert!(!is_all_numeric(b"12a45"));
        assert!(!is_all_numeric(b"123456789a")); // > 8 bytes with invalid
        assert!(!is_all_numeric(b" ")); // space
        assert!(!is_all_numeric(b"12 34"));
    }

    #[test]
    fn test_is_all_numeric_boundaries() {
        // Test boundaries around digits
        assert!(!is_all_numeric(b"/")); // Just below '0'
        assert!(is_all_numeric(b"0"));
        assert!(is_all_numeric(b"9"));
        assert!(!is_all_numeric(b":")); // Just above '9'
    }

    #[test]
    fn test_is_all_numeric_exhaustive_single_byte() {
        for b in 0u8..=255 {
            let expected = is_all_numeric_naive(&[b]);
            let actual = is_all_numeric(&[b]);
            assert_eq!(actual, expected, "mismatch for byte {:02x}", b);
        }
    }

    #[test]
    fn test_is_all_numeric_exhaustive_lengths() {
        for len in 0..=40 {
            let bytes: Vec<u8> = (0..len).map(|i| b'0' + (i % 10) as u8).collect();
            let expected = is_all_numeric_naive(&bytes);
            let actual = is_all_numeric(&bytes);
            assert_eq!(actual, expected, "mismatch at len={}", len);
        }
    }

    #[test]
    fn test_is_all_numeric_with_invalid_at_positions() {
        for len in 1..=20 {
            for pos in 0..len {
                let mut bytes: Vec<u8> = vec![b'5'; len];
                bytes[pos] = b'x';
                let expected = is_all_numeric_naive(&bytes);
                let actual = is_all_numeric(&bytes);
                assert_eq!(actual, expected, "len={}, pos={}", len, pos);
            }
        }
    }

    // -------------------------------------------------------------------------
    // is_all_alphanumeric tests
    // -------------------------------------------------------------------------

    fn is_all_alphanumeric_naive(bytes: &[u8]) -> bool {
        bytes.iter().all(|&b| b.is_ascii_alphanumeric())
    }

    #[test]
    fn test_is_all_alphanumeric_valid() {
        assert!(is_all_alphanumeric(b""));
        assert!(is_all_alphanumeric(b"0"));
        assert!(is_all_alphanumeric(b"a"));
        assert!(is_all_alphanumeric(b"Z"));
        assert!(is_all_alphanumeric(b"ABC123xyz"));
        assert!(is_all_alphanumeric(b"abcdefghijklmnopqrstuvwxyz")); // > 8 bytes
        assert!(is_all_alphanumeric(b"ABCDEFGHIJKLMNOPQRSTUVWXYZ"));
        assert!(is_all_alphanumeric(b"0123456789"));
    }

    #[test]
    fn test_is_all_alphanumeric_invalid() {
        assert!(!is_all_alphanumeric(b"-"));
        assert!(!is_all_alphanumeric(b"BTC-USD"));
        assert!(!is_all_alphanumeric(b"hello world")); // space
        assert!(!is_all_alphanumeric(b"test@example"));
        assert!(!is_all_alphanumeric(b"abcdefghijklmnop!")); // > 8 bytes with invalid
    }

    #[test]
    fn test_is_all_alphanumeric_boundaries() {
        // Test boundaries around each range
        // Digits: '/' < '0' <= digit <= '9' < ':'
        assert!(!is_all_alphanumeric(b"/"));
        assert!(is_all_alphanumeric(b"0"));
        assert!(is_all_alphanumeric(b"9"));
        assert!(!is_all_alphanumeric(b":"));

        // Uppercase: '@' < 'A' <= upper <= 'Z' < '['
        assert!(!is_all_alphanumeric(b"@"));
        assert!(is_all_alphanumeric(b"A"));
        assert!(is_all_alphanumeric(b"Z"));
        assert!(!is_all_alphanumeric(b"["));

        // Lowercase: '`' < 'a' <= lower <= 'z' < '{'
        assert!(!is_all_alphanumeric(b"`"));
        assert!(is_all_alphanumeric(b"a"));
        assert!(is_all_alphanumeric(b"z"));
        assert!(!is_all_alphanumeric(b"{"));
    }

    #[test]
    fn test_is_all_alphanumeric_exhaustive_single_byte() {
        for b in 0u8..=255 {
            let expected = is_all_alphanumeric_naive(&[b]);
            let actual = is_all_alphanumeric(&[b]);
            assert_eq!(actual, expected, "mismatch for byte {:02x}", b);
        }
    }

    #[test]
    fn test_is_all_alphanumeric_exhaustive_lengths() {
        for len in 0..=40 {
            // Mix of digits and letters
            let bytes: Vec<u8> = (0..len)
                .map(|i| match i % 3 {
                    0 => b'0' + (i % 10) as u8,
                    1 => b'A' + (i % 26) as u8,
                    _ => b'a' + (i % 26) as u8,
                })
                .collect();
            let expected = is_all_alphanumeric_naive(&bytes);
            let actual = is_all_alphanumeric(&bytes);
            assert_eq!(actual, expected, "mismatch at len={}", len);
        }
    }

    #[test]
    fn test_is_all_alphanumeric_with_invalid_at_positions() {
        for len in 1..=20 {
            for pos in 0..len {
                let mut bytes: Vec<u8> = vec![b'A'; len];
                bytes[pos] = b'-';
                let expected = is_all_alphanumeric_naive(&bytes);
                let actual = is_all_alphanumeric(&bytes);
                assert_eq!(actual, expected, "len={}, pos={}", len, pos);
            }
        }
    }
}
