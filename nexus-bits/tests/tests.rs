use nexus_bits::{BitField, Flag, Overflow};

// =============================================================================
// BitField - Construction
// =============================================================================

#[test]
fn bitfield_new_basic() {
    const FIELD: BitField<u64> = BitField::<u64>::new(0, 8);
    assert_eq!(FIELD.start(), 0);
    assert_eq!(FIELD.len(), 8);
    assert_eq!(FIELD.mask(), 0xFF);
    assert_eq!(FIELD.max_value(), 255);
}

#[test]
fn bitfield_new_offset() {
    const FIELD: BitField<u64> = BitField::<u64>::new(4, 8);
    assert_eq!(FIELD.start(), 4);
    assert_eq!(FIELD.len(), 8);
    assert_eq!(FIELD.mask(), 0xFF0);
    assert_eq!(FIELD.max_value(), 255);
}

#[test]
fn bitfield_new_high_bits() {
    const FIELD: BitField<u64> = BitField::<u64>::new(56, 8);
    assert_eq!(FIELD.start(), 56);
    assert_eq!(FIELD.len(), 8);
    assert_eq!(FIELD.mask(), 0xFF00_0000_0000_0000);
    assert_eq!(FIELD.max_value(), 255);
}

#[test]
fn bitfield_new_single_bit() {
    const FIELD: BitField<u64> = BitField::<u64>::new(0, 1);
    assert_eq!(FIELD.max_value(), 1);
    assert_eq!(FIELD.mask(), 1);
}

#[test]
fn bitfield_new_full_width() {
    const FIELD: BitField<u64> = BitField::<u64>::new(0, 64);
    assert_eq!(FIELD.max_value(), u64::MAX);
    assert_eq!(FIELD.mask(), u64::MAX);
}

#[test]
fn bitfield_new_full_width_u8() {
    const FIELD: BitField<u8> = BitField::<u8>::new(0, 8);
    assert_eq!(FIELD.max_value(), u8::MAX);
    assert_eq!(FIELD.mask(), u8::MAX);
}

#[test]
#[should_panic(expected = "field length must be > 0")]
fn bitfield_new_zero_len_panics() {
    let _ = BitField::<u64>::new(0, 0);
}

#[test]
#[should_panic(expected = "field exceeds integer bounds")]
fn bitfield_new_exceeds_bounds_panics() {
    let _ = BitField::<u64>::new(60, 8); // 60 + 8 = 68 > 64
}

#[test]
#[should_panic(expected = "field exceeds integer bounds")]
fn bitfield_new_exceeds_bounds_u8_panics() {
    let _ = BitField::<u8>::new(4, 8); // 4 + 8 = 12 > 8
}

// =============================================================================
// BitField - Get
// =============================================================================

#[test]
fn bitfield_get_low_bits() {
    const FIELD: BitField<u64> = BitField::<u64>::new(0, 8);
    assert_eq!(FIELD.get(0x12345678), 0x78);
}

#[test]
fn bitfield_get_middle_bits() {
    const FIELD: BitField<u64> = BitField::<u64>::new(8, 8);
    assert_eq!(FIELD.get(0x12345678), 0x56);
}

#[test]
fn bitfield_get_high_bits() {
    const FIELD: BitField<u64> = BitField::<u64>::new(24, 8);
    assert_eq!(FIELD.get(0x12345678), 0x12);
}

#[test]
fn bitfield_get_zero() {
    const FIELD: BitField<u64> = BitField::<u64>::new(0, 8);
    assert_eq!(FIELD.get(0), 0);
}

#[test]
fn bitfield_get_max() {
    const FIELD: BitField<u64> = BitField::<u64>::new(0, 8);
    assert_eq!(FIELD.get(u64::MAX), 255);
}

#[test]
fn bitfield_get_unaligned() {
    const FIELD: BitField<u64> = BitField::<u64>::new(3, 5);
    // bits 3-7: extract 5 bits starting at bit 3
    // 0b11111000 = 0xF8, shifted right by 3 = 0x1F = 31
    assert_eq!(FIELD.get(0xF8), 31);
}

// =============================================================================
// BitField - Set
// =============================================================================

#[test]
fn bitfield_set_basic() {
    const FIELD: BitField<u64> = BitField::<u64>::new(0, 8);
    let result = FIELD.set(0, 42).unwrap();
    assert_eq!(result, 42);
    assert_eq!(FIELD.get(result), 42);
}

#[test]
fn bitfield_set_offset() {
    const FIELD: BitField<u64> = BitField::<u64>::new(8, 8);
    let result = FIELD.set(0, 42).unwrap();
    assert_eq!(result, 42 << 8);
    assert_eq!(FIELD.get(result), 42);
}

#[test]
fn bitfield_set_preserves_other_bits() {
    const FIELD: BitField<u64> = BitField::<u64>::new(8, 8);
    let initial = 0xFF00FF;
    let result = FIELD.set(initial, 0x42).unwrap();
    // Bits 0-7 preserved: 0xFF
    // Bits 8-15 replaced: 0x42
    // Bits 16-23 preserved: 0xFF
    assert_eq!(result, 0xFF42FF);
}

#[test]
fn bitfield_set_clears_existing() {
    const FIELD: BitField<u64> = BitField::<u64>::new(0, 8);
    let initial = 0xFF;
    let result = FIELD.set(initial, 0x42).unwrap();
    assert_eq!(result, 0x42);
}

#[test]
fn bitfield_set_max_value() {
    const FIELD: BitField<u64> = BitField::<u64>::new(0, 8);
    let result = FIELD.set(0, 255).unwrap();
    assert_eq!(result, 255);
}

#[test]
fn bitfield_set_zero() {
    const FIELD: BitField<u64> = BitField::<u64>::new(0, 8);
    let result = FIELD.set(0xFF, 0).unwrap();
    assert_eq!(result, 0);
}

#[test]
fn bitfield_set_overflow_error() {
    const FIELD: BitField<u64> = BitField::<u64>::new(0, 8);
    let result = FIELD.set(0, 256);
    assert_eq!(
        result,
        Err(Overflow {
            value: 256,
            max: 255
        })
    );
}

#[test]
fn bitfield_set_overflow_large() {
    const FIELD: BitField<u64> = BitField::<u64>::new(0, 4);
    let result = FIELD.set(0, 1000);
    assert_eq!(
        result,
        Err(Overflow {
            value: 1000,
            max: 15
        })
    );
}

// =============================================================================
// BitField - Set Unchecked
// =============================================================================

#[test]
fn bitfield_set_unchecked_basic() {
    const FIELD: BitField<u64> = BitField::<u64>::new(0, 8);
    let result = FIELD.set_unchecked(0, 42);
    assert_eq!(result, 42);
}

#[test]
fn bitfield_set_unchecked_truncates() {
    const FIELD: BitField<u64> = BitField::<u64>::new(0, 8);
    // 0x1FF = 511, but only 8 bits, so upper bits spill into bit 8
    let result = FIELD.set_unchecked(0, 0x1FF);
    // This will set bits 0-8, mask only covers 0-7
    // cleared = 0 & !0xFF = 0
    // result = 0 | (0x1FF << 0) = 0x1FF
    // The overflow bits leak!
    assert_eq!(result, 0x1FF);
}

// =============================================================================
// BitField - Clear
// =============================================================================

#[test]
fn bitfield_clear_basic() {
    const FIELD: BitField<u64> = BitField::<u64>::new(0, 8);
    let result = FIELD.clear(0xFF);
    assert_eq!(result, 0);
}

#[test]
fn bitfield_clear_preserves_other_bits() {
    const FIELD: BitField<u64> = BitField::<u64>::new(8, 8);
    let result = FIELD.clear(0xFFFFFF);
    assert_eq!(result, 0xFF00FF);
}

#[test]
fn bitfield_clear_already_zero() {
    const FIELD: BitField<u64> = BitField::<u64>::new(0, 8);
    let result = FIELD.clear(0);
    assert_eq!(result, 0);
}

// =============================================================================
// BitField - Multiple Fields
// =============================================================================

#[test]
fn bitfield_multiple_fields_pack_unpack() {
    const KIND: BitField<u64> = BitField::<u64>::new(0, 4);
    const EXCHANGE: BitField<u64> = BitField::<u64>::new(4, 8);
    const SYMBOL: BitField<u64> = BitField::<u64>::new(12, 20);

    let mut id: u64 = 0;
    id = KIND.set(id, 3).unwrap();
    id = EXCHANGE.set(id, 42).unwrap();
    id = SYMBOL.set(id, 123456).unwrap();

    assert_eq!(KIND.get(id), 3);
    assert_eq!(EXCHANGE.get(id), 42);
    assert_eq!(SYMBOL.get(id), 123456);
}

#[test]
fn bitfield_adjacent_fields_no_overlap() {
    const LOW: BitField<u64> = BitField::<u64>::new(0, 32);
    const HIGH: BitField<u64> = BitField::<u64>::new(32, 32);

    let mut val: u64 = 0;
    val = LOW.set(val, 0xDEADBEEF).unwrap();
    val = HIGH.set(val, 0xCAFEBABE).unwrap();

    assert_eq!(LOW.get(val), 0xDEADBEEF);
    assert_eq!(HIGH.get(val), 0xCAFEBABE);
    assert_eq!(val, 0xCAFEBABE_DEADBEEF);
}

// =============================================================================
// BitField - Different Integer Types
// =============================================================================

#[test]
fn bitfield_u8() {
    const FIELD: BitField<u8> = BitField::<u8>::new(0, 4);
    let result = FIELD.set(0, 15).unwrap();
    assert_eq!(result, 15);
    assert_eq!(FIELD.get(result), 15);
    assert!(FIELD.set(0, 16).is_err());
}

#[test]
fn bitfield_u16() {
    const FIELD: BitField<u16> = BitField::<u16>::new(4, 8);
    let result = FIELD.set(0, 255).unwrap();
    assert_eq!(FIELD.get(result), 255);
}

#[test]
fn bitfield_u32() {
    const FIELD: BitField<u32> = BitField::<u32>::new(0, 20);
    let result = FIELD.set(0, 0xFFFFF).unwrap();
    assert_eq!(FIELD.get(result), 0xFFFFF);
}

#[test]
fn bitfield_u128() {
    const FIELD: BitField<u128> = BitField::<u128>::new(64, 48);
    let result = FIELD.set(0, 0xFFFF_FFFF_FFFF).unwrap();
    assert_eq!(FIELD.get(result), 0xFFFF_FFFF_FFFF);
}

#[test]
fn bitfield_i64() {
    const FIELD: BitField<i64> = BitField::<i64>::new(0, 8);
    let result = FIELD.set(0, 127).unwrap();
    assert_eq!(FIELD.get(result), 127);
}

// =============================================================================
// Flag - Construction
// =============================================================================

#[test]
fn flag_new_basic() {
    const FLAG: Flag<u64> = Flag::<u64>::new(0);
    assert_eq!(FLAG.bit(), 0);
    assert_eq!(FLAG.mask(), 1);
}

#[test]
fn flag_new_high_bit() {
    const FLAG: Flag<u64> = Flag::<u64>::new(63);
    assert_eq!(FLAG.bit(), 63);
    assert_eq!(FLAG.mask(), 1 << 63);
}

#[test]
fn flag_new_middle_bit() {
    const FLAG: Flag<u64> = Flag::<u64>::new(31);
    assert_eq!(FLAG.bit(), 31);
    assert_eq!(FLAG.mask(), 1 << 31);
}

#[test]
#[should_panic(expected = "bit position exceeds integer bounds")]
fn flag_new_exceeds_bounds_panics() {
    let _ = Flag::<u64>::new(64);
}

#[test]
#[should_panic(expected = "bit position exceeds integer bounds")]
fn flag_new_exceeds_bounds_u8_panics() {
    let _ = Flag::<u8>::new(8);
}

// =============================================================================
// Flag - Is Set
// =============================================================================

#[test]
fn flag_is_set_true() {
    const FLAG: Flag<u64> = Flag::<u64>::new(0);
    assert!(FLAG.is_set(1));
}

#[test]
fn flag_is_set_false() {
    const FLAG: Flag<u64> = Flag::<u64>::new(0);
    assert!(!FLAG.is_set(0));
}

#[test]
fn flag_is_set_among_others() {
    const FLAG: Flag<u64> = Flag::<u64>::new(4);
    assert!(FLAG.is_set(0b10000));
    assert!(!FLAG.is_set(0b01111));
}

#[test]
fn flag_is_set_high_bit() {
    const FLAG: Flag<u64> = Flag::<u64>::new(63);
    assert!(FLAG.is_set(1u64 << 63));
    assert!(!FLAG.is_set((1u64 << 63) - 1));
}

// =============================================================================
// Flag - Set
// =============================================================================

#[test]
fn flag_set_basic() {
    const FLAG: Flag<u64> = Flag::<u64>::new(0);
    assert_eq!(FLAG.set(0), 1);
}

#[test]
fn flag_set_idempotent() {
    const FLAG: Flag<u64> = Flag::<u64>::new(0);
    assert_eq!(FLAG.set(1), 1);
}

#[test]
fn flag_set_preserves_other_bits() {
    const FLAG: Flag<u64> = Flag::<u64>::new(4);
    assert_eq!(FLAG.set(0b1111), 0b11111);
}

#[test]
fn flag_set_high_bit() {
    const FLAG: Flag<u64> = Flag::<u64>::new(63);
    assert_eq!(FLAG.set(0), 1u64 << 63);
}

// =============================================================================
// Flag - Clear
// =============================================================================

#[test]
fn flag_clear_basic() {
    const FLAG: Flag<u64> = Flag::<u64>::new(0);
    assert_eq!(FLAG.clear(1), 0);
}

#[test]
fn flag_clear_idempotent() {
    const FLAG: Flag<u64> = Flag::<u64>::new(0);
    assert_eq!(FLAG.clear(0), 0);
}

#[test]
fn flag_clear_preserves_other_bits() {
    const FLAG: Flag<u64> = Flag::<u64>::new(4);
    assert_eq!(FLAG.clear(0b11111), 0b01111);
}

// =============================================================================
// Flag - Toggle
// =============================================================================

#[test]
fn flag_toggle_off_to_on() {
    const FLAG: Flag<u64> = Flag::<u64>::new(0);
    assert_eq!(FLAG.toggle(0), 1);
}

#[test]
fn flag_toggle_on_to_off() {
    const FLAG: Flag<u64> = Flag::<u64>::new(0);
    assert_eq!(FLAG.toggle(1), 0);
}

#[test]
fn flag_toggle_preserves_other_bits() {
    const FLAG: Flag<u64> = Flag::<u64>::new(4);
    assert_eq!(FLAG.toggle(0b01111), 0b11111);
    assert_eq!(FLAG.toggle(0b11111), 0b01111);
}

#[test]
fn flag_toggle_twice_restores() {
    const FLAG: Flag<u64> = Flag::<u64>::new(7);
    let original = 0x12345678u64;
    let toggled = FLAG.toggle(original);
    let restored = FLAG.toggle(toggled);
    assert_eq!(restored, original);
}

// =============================================================================
// Flag - Set To
// =============================================================================

#[test]
fn flag_set_to_true() {
    const FLAG: Flag<u64> = Flag::<u64>::new(0);
    assert_eq!(FLAG.set_to(0, true), 1);
}

#[test]
fn flag_set_to_false() {
    const FLAG: Flag<u64> = Flag::<u64>::new(0);
    assert_eq!(FLAG.set_to(1, false), 0);
}

#[test]
fn flag_set_to_true_already_set() {
    const FLAG: Flag<u64> = Flag::<u64>::new(0);
    assert_eq!(FLAG.set_to(1, true), 1);
}

#[test]
fn flag_set_to_false_already_clear() {
    const FLAG: Flag<u64> = Flag::<u64>::new(0);
    assert_eq!(FLAG.set_to(0, false), 0);
}

#[test]
fn flag_set_to_from_bool() {
    const FLAG: Flag<u64> = Flag::<u64>::new(4);
    let is_buy = true;
    let is_ioc = false;

    let mut flags = 0u64;
    flags = FLAG.set_to(flags, is_buy);
    assert!(FLAG.is_set(flags));

    flags = FLAG.set_to(flags, is_ioc);
    assert!(!FLAG.is_set(flags));
}

// =============================================================================
// Flag - Different Integer Types
// =============================================================================

#[test]
fn flag_u8() {
    const FLAG: Flag<u8> = Flag::<u8>::new(7);
    assert_eq!(FLAG.set(0), 0x80);
    assert!(FLAG.is_set(0x80));
}

#[test]
fn flag_u16() {
    const FLAG: Flag<u16> = Flag::<u16>::new(15);
    assert_eq!(FLAG.set(0), 0x8000);
}

#[test]
fn flag_u128() {
    const FLAG: Flag<u128> = Flag::<u128>::new(127);
    assert_eq!(FLAG.set(0), 1u128 << 127);
}

#[test]
fn flag_i64() {
    const FLAG: Flag<i64> = Flag::<i64>::new(63);
    // Setting bit 63 on i64 gives negative number (sign bit)
    assert_eq!(FLAG.set(0), i64::MIN);
}

// =============================================================================
// Flag - Multiple Flags
// =============================================================================

#[test]
fn flag_multiple_flags() {
    const IS_BUY: Flag<u64> = Flag::<u64>::new(0);
    const IS_IOC: Flag<u64> = Flag::<u64>::new(1);
    const IS_POST_ONLY: Flag<u64> = Flag::<u64>::new(2);
    const IS_REDUCE_ONLY: Flag<u64> = Flag::<u64>::new(3);

    let mut flags = 0u64;
    flags = IS_BUY.set(flags);
    flags = IS_IOC.set(flags);
    flags = IS_REDUCE_ONLY.set(flags);

    assert!(IS_BUY.is_set(flags));
    assert!(IS_IOC.is_set(flags));
    assert!(!IS_POST_ONLY.is_set(flags));
    assert!(IS_REDUCE_ONLY.is_set(flags));
    assert_eq!(flags, 0b1011);
}

// =============================================================================
// Combined - BitField and Flag
// =============================================================================

#[test]
fn combined_bitfield_and_flag() {
    const KIND: BitField<u64> = BitField::<u64>::new(0, 4);
    const EXCHANGE: BitField<u64> = BitField::<u64>::new(4, 8);
    const SYMBOL: BitField<u64> = BitField::<u64>::new(12, 20);
    const IS_TEST: Flag<u64> = Flag::<u64>::new(63);

    let mut id = 0u64;
    id = KIND.set(id, 2).unwrap();
    id = EXCHANGE.set(id, 5).unwrap();
    id = SYMBOL.set(id, 99999).unwrap();
    id = IS_TEST.set(id);

    assert_eq!(KIND.get(id), 2);
    assert_eq!(EXCHANGE.get(id), 5);
    assert_eq!(SYMBOL.get(id), 99999);
    assert!(IS_TEST.is_set(id));
}

// =============================================================================
// Error Display
// =============================================================================

#[test]
fn overflow_display() {
    let err: Overflow<u64> = Overflow {
        value: 256,
        max: 255,
    };
    let msg = format!("{}", err);
    assert_eq!(msg, "value 256 exceeds max 255");
}

#[test]
fn overflow_debug() {
    let err: Overflow<u64> = Overflow {
        value: 256,
        max: 255,
    };
    let msg = format!("{:?}", err);
    assert!(msg.contains("256"));
    assert!(msg.contains("255"));
}

// =============================================================================
// Const Context
// =============================================================================

#[test]
fn const_construction() {
    // Verify these can be constructed in const context
    const FIELD: BitField<u64> = BitField::<u64>::new(0, 8);
    const FLAG: Flag<u64> = Flag::<u64>::new(0);

    // And used in const context
    const MASK: u64 = FIELD.mask();
    const FLAG_MASK: u64 = FLAG.mask();

    assert_eq!(MASK, 0xFF);
    assert_eq!(FLAG_MASK, 1);
}

#[test]
fn const_get() {
    const FIELD: BitField<u64> = BitField::<u64>::new(0, 8);
    const VAL: u64 = FIELD.get(0x1234);
    assert_eq!(VAL, 0x34);
}

#[test]
fn const_flag_is_set() {
    const FLAG: Flag<u64> = Flag::<u64>::new(0);
    const IS_SET: bool = FLAG.is_set(1);
    const IS_CLEAR: bool = FLAG.is_set(0);
    assert!(IS_SET);
    assert!(!IS_CLEAR);
}
