//! Tests for BitPacked derive macro on structs.

use nexus_bits::{BitPacked, FieldOverflow, IntEnum, Overflow, UnknownDiscriminant};

// =============================================================================
// Basic primitive fields
// =============================================================================

#[derive(BitPacked, Debug, Clone, Copy, PartialEq, Eq)]
#[packed(repr = u64)]
pub struct BasicFields {
    #[field(start = 0, len = 8)]
    a: u8,
    #[field(start = 8, len = 16)]
    b: u16,
    #[field(start = 24, len = 32)]
    c: u32,
}

#[test]
fn basic_fields_pack() {
    let s = BasicFields { a: 1, b: 2, c: 3 };
    let packed = s.pack().unwrap();

    // a at bits 0-7: 1
    // b at bits 8-23: 2 << 8 = 0x200
    // c at bits 24-55: 3 << 24 = 0x3000000
    assert_eq!(packed, 1 | (2 << 8) | (3 << 24));
}

#[test]
fn basic_fields_unpack() {
    let raw: u64 = 1 | (2 << 8) | (3 << 24);
    let s = BasicFields::unpack(raw);

    assert_eq!(s.a, 1);
    assert_eq!(s.b, 2);
    assert_eq!(s.c, 3);
}

#[test]
fn basic_fields_roundtrip() {
    let original = BasicFields {
        a: 255,
        b: 65535,
        c: 0xFFFFFFFF,
    };
    let packed = original.pack().unwrap();
    let unpacked = BasicFields::unpack(packed);
    assert_eq!(original, unpacked);
}

#[test]
fn basic_fields_roundtrip_zero() {
    let original = BasicFields { a: 0, b: 0, c: 0 };
    let packed = original.pack().unwrap();
    assert_eq!(packed, 0);
    let unpacked = BasicFields::unpack(packed);
    assert_eq!(original, unpacked);
}

#[test]
fn basic_fields_overflow_a() {
    // a is u8 stored in 8 bits - max is 255
    // This can't overflow since u8 max == 8-bit max
    // Let's make a struct where overflow is possible
}

// =============================================================================
// Overflow detection
// =============================================================================

#[derive(BitPacked, Debug, Clone, Copy, PartialEq, Eq)]
#[packed(repr = u64)]
pub struct NarrowFields {
    #[field(start = 0, len = 4)]
    narrow: u8, // u8 can hold 0-255, but field only holds 0-15
    #[field(start = 4, len = 8)]
    normal: u8,
}

#[test]
fn narrow_field_valid() {
    let s = NarrowFields {
        narrow: 15,
        normal: 255,
    };
    let packed = s.pack().unwrap();
    let unpacked = NarrowFields::unpack(packed);
    assert_eq!(s, unpacked);
}

#[test]
fn narrow_field_overflow() {
    let s = NarrowFields {
        narrow: 16,
        normal: 0,
    }; // 16 > 15 (4-bit max)
    let err = s.pack().unwrap_err();
    assert_eq!(err.field, "narrow");
    assert_eq!(err.overflow.value, 16);
    assert_eq!(err.overflow.max, 15);
}

#[test]
fn narrow_field_overflow_large() {
    let s = NarrowFields {
        narrow: 255,
        normal: 0,
    };
    let err = s.pack().unwrap_err();
    assert_eq!(err.field, "narrow");
    assert_eq!(err.overflow.value, 255);
    assert_eq!(err.overflow.max, 15);
}

// =============================================================================
// Flags
// =============================================================================

#[derive(BitPacked, Debug, Clone, Copy, PartialEq, Eq)]
#[packed(repr = u64)]
pub struct FlagsOnly {
    #[flag(0)]
    a: bool,
    #[flag(1)]
    b: bool,
    #[flag(63)]
    high: bool,
}

#[test]
fn flags_all_false() {
    let s = FlagsOnly {
        a: false,
        b: false,
        high: false,
    };
    let packed = s.pack().unwrap();
    assert_eq!(packed, 0);
}

#[test]
fn flags_all_true() {
    let s = FlagsOnly {
        a: true,
        b: true,
        high: true,
    };
    let packed = s.pack().unwrap();
    assert_eq!(packed, 1 | 2 | (1u64 << 63));
}

#[test]
fn flags_unpack() {
    let raw: u64 = 1 | (1 << 63);
    let s = FlagsOnly::unpack(raw);
    assert!(s.a);
    assert!(!s.b);
    assert!(s.high);
}

#[test]
fn flags_roundtrip() {
    let original = FlagsOnly {
        a: true,
        b: false,
        high: true,
    };
    let packed = original.pack().unwrap();
    let unpacked = FlagsOnly::unpack(packed);
    assert_eq!(original, unpacked);
}

// =============================================================================
// Mixed fields and flags
// =============================================================================

#[derive(BitPacked, Debug, Clone, Copy, PartialEq, Eq)]
#[packed(repr = u64)]
pub struct Mixed {
    #[field(start = 0, len = 8)]
    value: u8,
    #[flag(8)]
    enabled: bool,
    #[field(start = 16, len = 16)]
    count: u16,
    #[flag(63)]
    high_flag: bool,
}

#[test]
fn mixed_pack() {
    let s = Mixed {
        value: 42,
        enabled: true,
        count: 1000,
        high_flag: false,
    };
    let packed = s.pack().unwrap();

    assert_eq!(packed & 0xFF, 42);
    assert_eq!((packed >> 8) & 1, 1);
    assert_eq!((packed >> 16) & 0xFFFF, 1000);
    assert_eq!((packed >> 63) & 1, 0);
}

#[test]
fn mixed_unpack() {
    let raw: u64 = 42 | (1 << 8) | (1000 << 16);
    let s = Mixed::unpack(raw);

    assert_eq!(s.value, 42);
    assert!(s.enabled);
    assert_eq!(s.count, 1000);
    assert!(!s.high_flag);
}

#[test]
fn mixed_roundtrip() {
    let original = Mixed {
        value: 255,
        enabled: true,
        count: 65535,
        high_flag: true,
    };
    let packed = original.pack().unwrap();
    let unpacked = Mixed::unpack(packed);
    assert_eq!(original, unpacked);
}

// =============================================================================
// IntEnum fields
// =============================================================================

#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Side {
    Buy = 0,
    Sell = 1,
}

#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum TimeInForce {
    Day = 0,
    Gtc = 1,
    Ioc = 2,
    Fok = 3,
}

#[derive(BitPacked, Debug, Clone, Copy, PartialEq, Eq)]
#[packed(repr = u64)]
pub struct OrderFlags {
    #[field(start = 0, len = 1)]
    side: Side,
    #[field(start = 1, len = 2)]
    tif: TimeInForce,
    #[field(start = 3, len = 16)]
    quantity: u16,
}

#[test]
fn enum_fields_pack() {
    let s = OrderFlags {
        side: Side::Buy,
        tif: TimeInForce::Ioc,
        quantity: 100,
    };
    let packed = s.pack().unwrap();

    // side=0 at bit 0
    // tif=2 at bits 1-2
    // quantity=100 at bits 3-18
    assert_eq!(packed, 0 | (2 << 1) | (100 << 3));
}

#[test]
fn enum_fields_unpack_valid() {
    let raw: u64 = 1 | (3 << 1) | (500 << 3); // Sell, Fok, 500
    let s = OrderFlags::unpack(raw).unwrap();

    assert_eq!(s.side, Side::Sell);
    assert_eq!(s.tif, TimeInForce::Fok);
    assert_eq!(s.quantity, 500);
}

#[test]
fn enum_fields_roundtrip() {
    let original = OrderFlags {
        side: Side::Sell,
        tif: TimeInForce::Gtc,
        quantity: 12345,
    };
    let packed = original.pack().unwrap();
    let unpacked = OrderFlags::unpack(packed).unwrap();
    assert_eq!(original, unpacked);
}

#[test]
fn enum_fields_unknown_variant() {
    // tif field is 2 bits at position 1, valid values 0-3
    // Let's put an invalid side value (side is 1 bit, only 0 or 1 valid)
    // Actually Side has both 0 and 1 as valid, so that won't fail

    // TimeInForce has 0-3 valid. In 2 bits, all values are valid.
    // So this test needs an enum with gaps
}

// =============================================================================
// IntEnum with gaps (for unknown variant testing)
// =============================================================================

#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum SparseEnum {
    A = 0,
    B = 2,
    C = 5,
}

#[derive(BitPacked, Debug, Clone, Copy, PartialEq, Eq)]
#[packed(repr = u64)]
pub struct WithSparseEnum {
    #[field(start = 0, len = 4)]
    sparse: SparseEnum,
    #[field(start = 4, len = 8)]
    value: u8,
}

#[test]
fn sparse_enum_valid() {
    let s = WithSparseEnum {
        sparse: SparseEnum::B,
        value: 42,
    };
    let packed = s.pack().unwrap();
    let unpacked = WithSparseEnum::unpack(packed).unwrap();
    assert_eq!(s, unpacked);
}

#[test]
fn sparse_enum_unknown_variant() {
    // Put value 1 in the sparse field (not a valid variant)
    let raw: u64 = 1 | (42 << 4); // sparse=1 (invalid), value=42
    let err = WithSparseEnum::unpack(raw).unwrap_err();
    assert_eq!(err.field, "sparse");
}

#[test]
fn sparse_enum_unknown_variant_3() {
    // Value 3 is also invalid for SparseEnum
    let raw: u64 = 3 | (100 << 4);
    let err = WithSparseEnum::unpack(raw).unwrap_err();
    assert_eq!(err.field, "sparse");
}

// =============================================================================
// Different repr types
// =============================================================================

#[derive(BitPacked, Debug, Clone, Copy, PartialEq, Eq)]
#[packed(repr = u8)]
pub struct TinyPacked {
    #[field(start = 0, len = 4)]
    low: u8,
    #[field(start = 4, len = 4)]
    high: u8,
}

#[test]
fn u8_repr_pack() {
    let s = TinyPacked {
        low: 0xA,
        high: 0xB,
    };
    let packed = s.pack().unwrap();
    assert_eq!(packed, 0xBA);
}

#[test]
fn u8_repr_unpack() {
    let s = TinyPacked::unpack(0xBA);
    assert_eq!(s.low, 0xA);
    assert_eq!(s.high, 0xB);
}

#[derive(BitPacked, Debug, Clone, Copy, PartialEq, Eq)]
#[packed(repr = u16)]
pub struct U16Packed {
    #[field(start = 0, len = 8)]
    low: u8,
    #[field(start = 8, len = 8)]
    high: u8,
}

#[test]
fn u16_repr_roundtrip() {
    let original = U16Packed {
        low: 0xAB,
        high: 0xCD,
    };
    let packed = original.pack().unwrap();
    assert_eq!(packed, 0xCDAB);
    let unpacked = U16Packed::unpack(packed);
    assert_eq!(original, unpacked);
}

#[derive(BitPacked, Debug, Clone, Copy, PartialEq, Eq)]
#[packed(repr = u32)]
pub struct U32Packed {
    #[field(start = 0, len = 16)]
    low: u16,
    #[field(start = 16, len = 16)]
    high: u16,
}

#[test]
fn u32_repr_roundtrip() {
    let original = U32Packed {
        low: 0x1234,
        high: 0x5678,
    };
    let packed = original.pack().unwrap();
    assert_eq!(packed, 0x56781234);
    let unpacked = U32Packed::unpack(packed);
    assert_eq!(original, unpacked);
}

#[derive(BitPacked, Debug, Clone, Copy, PartialEq, Eq)]
#[packed(repr = i64)]
pub struct SignedRepr {
    #[field(start = 0, len = 32)]
    a: u32,
    #[field(start = 32, len = 32)]
    b: u32,
}

#[test]
fn i64_repr_roundtrip() {
    let original = SignedRepr {
        a: 0xDEADBEEF,
        b: 0xCAFEBABE,
    };
    let packed = original.pack().unwrap();
    let unpacked = SignedRepr::unpack(packed);
    assert_eq!(original, unpacked);
}

// =============================================================================
// Adjacent fields (no gaps)
// =============================================================================

#[derive(BitPacked, Debug, Clone, Copy, PartialEq, Eq)]
#[packed(repr = u64)]
pub struct Adjacent {
    #[field(start = 0, len = 16)]
    a: u16,
    #[field(start = 16, len = 16)]
    b: u16,
    #[field(start = 32, len = 16)]
    c: u16,
    #[field(start = 48, len = 16)]
    d: u16,
}

#[test]
fn adjacent_roundtrip() {
    let original = Adjacent {
        a: 0x1111,
        b: 0x2222,
        c: 0x3333,
        d: 0x4444,
    };
    let packed = original.pack().unwrap();
    assert_eq!(packed, 0x4444_3333_2222_1111);
    let unpacked = Adjacent::unpack(packed);
    assert_eq!(original, unpacked);
}

// =============================================================================
// Sparse fields (with gaps)
// =============================================================================

#[derive(BitPacked, Debug, Clone, Copy, PartialEq, Eq)]
#[packed(repr = u64)]
pub struct Sparse {
    #[field(start = 0, len = 8)]
    a: u8,
    // gap at bits 8-15
    #[field(start = 16, len = 8)]
    b: u8,
    // gap at bits 24-55
    #[field(start = 56, len = 8)]
    c: u8,
}

#[test]
fn sparse_pack() {
    let s = Sparse {
        a: 0xAA,
        b: 0xBB,
        c: 0xCC,
    };
    let packed = s.pack().unwrap();
    assert_eq!(packed, 0xCC00_0000_00BB_00AA);
}

#[test]
fn sparse_unpack() {
    // Put garbage in the gaps - should be ignored
    let raw: u64 = 0xCC12_3456_78BB_99AA;
    let s = Sparse::unpack(raw);
    assert_eq!(s.a, 0xAA);
    assert_eq!(s.b, 0xBB);
    assert_eq!(s.c, 0xCC);
}

// =============================================================================
// Single field
// =============================================================================

#[derive(BitPacked, Debug, Clone, Copy, PartialEq, Eq)]
#[packed(repr = u64)]
pub struct SingleField {
    #[field(start = 0, len = 64)]
    value: u64,
}

#[test]
fn single_field_full_width() {
    let original = SingleField { value: u64::MAX };
    let packed = original.pack().unwrap();
    assert_eq!(packed, u64::MAX);
    let unpacked = SingleField::unpack(packed);
    assert_eq!(original, unpacked);
}

#[test]
fn single_field_zero() {
    let original = SingleField { value: 0 };
    let packed = original.pack().unwrap();
    assert_eq!(packed, 0);
}

// =============================================================================
// Single flag
// =============================================================================

#[derive(BitPacked, Debug, Clone, Copy, PartialEq, Eq)]
#[packed(repr = u64)]
pub struct SingleFlag {
    #[flag(0)]
    flag: bool,
}

#[test]
fn single_flag_true() {
    let s = SingleFlag { flag: true };
    let packed = s.pack().unwrap();
    assert_eq!(packed, 1);
}

#[test]
fn single_flag_false() {
    let s = SingleFlag { flag: false };
    let packed = s.pack().unwrap();
    assert_eq!(packed, 0);
}

// =============================================================================
// Real-world-ish: Snowflake ID
// =============================================================================

#[derive(BitPacked, Debug, Clone, Copy, PartialEq, Eq)]
#[packed(repr = u64)]
pub struct SnowflakeId {
    #[field(start = 0, len = 12)]
    sequence: u16,
    #[field(start = 12, len = 10)]
    worker: u16,
    #[field(start = 22, len = 42)]
    timestamp: u64,
}

#[test]
fn snowflake_roundtrip() {
    let original = SnowflakeId {
        sequence: 4095,              // max 12 bits
        worker: 1023,                // max 10 bits
        timestamp: (1u64 << 42) - 1, // max 42 bits
    };
    let packed = original.pack().unwrap();
    let unpacked = SnowflakeId::unpack(packed);
    assert_eq!(original, unpacked);
}

#[test]
fn snowflake_sequence_overflow() {
    let s = SnowflakeId {
        sequence: 4096, // > 4095
        worker: 0,
        timestamp: 0,
    };
    let err = s.pack().unwrap_err();
    assert_eq!(err.field, "sequence");
}

#[test]
fn snowflake_worker_overflow() {
    let s = SnowflakeId {
        sequence: 0,
        worker: 1024, // > 1023
        timestamp: 0,
    };
    let err = s.pack().unwrap_err();
    assert_eq!(err.field, "worker");
}

// =============================================================================
// Real-world-ish: Instrument ID with enums
// =============================================================================

#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum AssetClass {
    Equity = 0,
    Future = 1,
    Option = 2,
    Forex = 3,
}

#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Exchange {
    Nasdaq = 0,
    Nyse = 1,
    Cboe = 2,
    Cme = 3,
}

#[derive(BitPacked, Debug, Clone, Copy, PartialEq, Eq)]
#[packed(repr = u64)]
pub struct InstrumentId {
    #[field(start = 0, len = 4)]
    asset_class: AssetClass,
    #[field(start = 4, len = 4)]
    exchange: Exchange,
    #[field(start = 8, len = 24)]
    symbol: u32,
    #[flag(63)]
    is_test: bool,
}

#[test]
fn instrument_id_roundtrip() {
    let original = InstrumentId {
        asset_class: AssetClass::Option,
        exchange: Exchange::Cboe,
        symbol: 123456,
        is_test: true,
    };
    let packed = original.pack().unwrap();
    let unpacked = InstrumentId::unpack(packed).unwrap();
    assert_eq!(original, unpacked);
}

#[test]
fn instrument_id_all_variants() {
    for &ac in &[
        AssetClass::Equity,
        AssetClass::Future,
        AssetClass::Option,
        AssetClass::Forex,
    ] {
        for &ex in &[
            Exchange::Nasdaq,
            Exchange::Nyse,
            Exchange::Cboe,
            Exchange::Cme,
        ] {
            for &test in &[false, true] {
                let original = InstrumentId {
                    asset_class: ac,
                    exchange: ex,
                    symbol: 999999,
                    is_test: test,
                };
                let packed = original.pack().unwrap();
                let unpacked = InstrumentId::unpack(packed).unwrap();
                assert_eq!(original, unpacked);
            }
        }
    }
}

// =============================================================================
// Error display
// =============================================================================

#[test]
fn field_overflow_display() {
    let err = FieldOverflow {
        field: "test_field",
        overflow: Overflow {
            value: 100u64,
            max: 15u64,
        },
    };
    let msg = format!("{}", err);
    assert!(msg.contains("test_field"));
    assert!(msg.contains("100"));
    assert!(msg.contains("15"));
}

#[test]
fn unknown_variant_display() {
    let err = UnknownDiscriminant::<u64> {
        field: "my_enum",
        value: 42,
    };
    let msg = format!("{}", err);
    assert!(msg.contains("my_enum"));
    assert!(msg.contains("42"));
}

// =============================================================================
// Weird offset edge cases
// =============================================================================

/// Field that spans multiple byte boundaries
#[derive(BitPacked, Debug, Clone, Copy, PartialEq, Eq)]
#[packed(repr = u64)]
pub struct CrossesByteBoundary {
    #[field(start = 4, len = 24)] // bits 4-27, spans bytes 0-3
    value: u32,
}

/// Single bit fields scattered across the integer
#[derive(BitPacked, Debug, Clone, Copy, PartialEq, Eq)]
#[packed(repr = u64)]
pub struct ScatteredBits {
    #[flag(0)]
    bit0: bool,
    #[flag(7)]
    bit7: bool,
    #[flag(8)]
    bit8: bool,
    #[flag(15)]
    bit15: bool,
    #[flag(31)]
    bit31: bool,
    #[flag(32)]
    bit32: bool,
}

/// Odd-sized fields at odd offsets
#[derive(BitPacked, Debug, Clone, Copy, PartialEq, Eq)]
#[packed(repr = u64)]
pub struct OddOffsets {
    #[field(start = 0, len = 3)] // bits 0-2
    a: u8,
    #[field(start = 3, len = 5)] // bits 3-7
    b: u8,
    #[field(start = 8, len = 7)] // bits 8-14
    c: u8,
    #[field(start = 15, len = 11)] // bits 15-25
    d: u16,
    #[field(start = 26, len = 13)] // bits 26-38
    e: u16,
}

/// IntEnum in 1 bit with following field at bit 1
#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum OneBitEnum {
    Zero = 0,
    One = 1,
}

#[derive(BitPacked, Debug, Clone, Copy, PartialEq, Eq)]
#[packed(repr = u8)]
pub struct TightPacking {
    #[field(start = 0, len = 1)]
    a: OneBitEnum,
    #[field(start = 1, len = 1)]
    b: OneBitEnum,
    #[field(start = 2, len = 3)]
    c: u8,
    #[field(start = 5, len = 3)]
    d: u8,
}

#[test]
fn crosses_byte_boundary() {
    let s = CrossesByteBoundary { value: 0xABCDEF };
    let packed = s.pack().unwrap();
    // value 0xABCDEF shifted left 4 bits
    assert_eq!(packed, 0xABCDEF << 4);

    let unpacked = CrossesByteBoundary::unpack(packed);
    assert_eq!(unpacked.value, 0xABCDEF);
}

#[test]
fn scattered_bits_all_set() {
    let s = ScatteredBits {
        bit0: true,
        bit7: true,
        bit8: true,
        bit15: true,
        bit31: true,
        bit32: true,
    };
    let packed = s.pack().unwrap();
    assert_eq!(
        packed,
        (1 << 0) | (1 << 7) | (1 << 8) | (1 << 15) | (1 << 31) | (1 << 32)
    );

    let unpacked = ScatteredBits::unpack(packed);
    assert_eq!(s, unpacked);
}

#[test]
fn scattered_bits_alternating() {
    let s = ScatteredBits {
        bit0: true,
        bit7: false,
        bit8: true,
        bit15: false,
        bit31: true,
        bit32: false,
    };
    let packed = s.pack().unwrap();
    let unpacked = ScatteredBits::unpack(packed);
    assert_eq!(s, unpacked);
}

#[test]
fn odd_offsets_roundtrip() {
    let s = OddOffsets {
        a: 0b111,           // max 3 bits = 7
        b: 0b11111,         // max 5 bits = 31
        c: 0b1111111,       // max 7 bits = 127
        d: 0b11111111111,   // max 11 bits = 2047
        e: 0b1111111111111, // max 13 bits = 8191
    };
    let packed = s.pack().unwrap();
    let unpacked = OddOffsets::unpack(packed);
    assert_eq!(s, unpacked);
}

#[test]
fn odd_offsets_specific_values() {
    let s = OddOffsets {
        a: 5,
        b: 17,
        c: 99,
        d: 1234,
        e: 5678,
    };
    let packed = s.pack().unwrap();
    let unpacked = OddOffsets::unpack(packed);
    assert_eq!(unpacked.a, 5);
    assert_eq!(unpacked.b, 17);
    assert_eq!(unpacked.c, 99);
    assert_eq!(unpacked.d, 1234);
    assert_eq!(unpacked.e, 5678);
}

#[test]
fn tight_packing_all_combos() {
    for a in [OneBitEnum::Zero, OneBitEnum::One] {
        for b in [OneBitEnum::Zero, OneBitEnum::One] {
            for c in 0..8u8 {
                // 3 bits max = 7
                for d in 0..8u8 {
                    let original = TightPacking { a, b, c, d };
                    let packed = original.pack().unwrap();
                    let unpacked = TightPacking::unpack(packed).unwrap();
                    assert_eq!(original, unpacked);
                }
            }
        }
    }
}

#[test]
fn tight_packing_manual_verify() {
    let s = TightPacking {
        a: OneBitEnum::One,  // bit 0 = 1
        b: OneBitEnum::Zero, // bit 1 = 0
        c: 0b101,            // bits 2-4 = 5
        d: 0b110,            // bits 5-7 = 6
    };
    let packed = s.pack().unwrap();
    // bit 0: 1
    // bit 1: 0
    // bits 2-4: 101
    // bits 5-7: 110
    // = 0b110_101_0_1 = 0b11010101 = 0xD5
    assert_eq!(packed, 0b11010101);
}
