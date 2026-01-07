//! Tests for BitStorage derive macro on structs.

use nexus_bits::{FieldOverflow, IntEnum, Overflow, UnknownDiscriminant, bit_storage};

// =============================================================================
// Basic primitive fields
// =============================================================================

#[bit_storage(repr = u64)]
pub struct BasicFields {
    #[field(start = 0, len = 8)]
    a: u8,
    #[field(start = 8, len = 16)]
    b: u16,
    #[field(start = 24, len = 32)]
    c: u32,
}

#[test]
fn basic_fields_build() {
    let s = BasicFields::builder().a(1).b(2).c(3).build().unwrap();

    // a at bits 0-7: 1
    // b at bits 8-23: 2 << 8 = 0x200
    // c at bits 24-55: 3 << 24 = 0x3000000
    assert_eq!(s.raw(), 1 | (2 << 8) | (3 << 24));
}

#[test]
fn basic_fields_accessors() {
    let raw: u64 = 1 | (2 << 8) | (3 << 24);
    let s = BasicFields::from_raw(raw);

    assert_eq!(s.a(), 1);
    assert_eq!(s.b(), 2);
    assert_eq!(s.c(), 3);
}

#[test]
fn basic_fields_roundtrip() {
    let original = BasicFields::builder()
        .a(255)
        .b(65535)
        .c(0xFFFFFFFF)
        .build()
        .unwrap();

    let s = BasicFields::from_raw(original.raw());
    assert_eq!(s.a(), 255);
    assert_eq!(s.b(), 65535);
    assert_eq!(s.c(), 0xFFFFFFFF);
}

#[test]
fn basic_fields_roundtrip_zero() {
    let original = BasicFields::builder().a(0).b(0).c(0).build().unwrap();

    assert_eq!(original.raw(), 0);
    let s = BasicFields::from_raw(original.raw());
    assert_eq!(s.a(), 0);
    assert_eq!(s.b(), 0);
    assert_eq!(s.c(), 0);
}

// =============================================================================
// Overflow detection
// =============================================================================

#[bit_storage(repr = u64)]
pub struct NarrowFields {
    #[field(start = 0, len = 4)]
    narrow: u8, // u8 can hold 0-255, but field only holds 0-15
    #[field(start = 4, len = 8)]
    normal: u8,
}

#[test]
fn narrow_field_valid() {
    let s = NarrowFields::builder()
        .narrow(15)
        .normal(255)
        .build()
        .unwrap();

    let unpacked = NarrowFields::from_raw(s.raw());
    assert_eq!(unpacked.narrow(), 15);
    assert_eq!(unpacked.normal(), 255);
}

#[test]
fn narrow_field_overflow() {
    let result = NarrowFields::builder()
        .narrow(16) // 16 > 15 (4-bit max)
        .normal(0)
        .build();

    let err = result.unwrap_err();
    assert_eq!(err.field, "narrow");
}

#[test]
fn narrow_field_overflow_large() {
    let result = NarrowFields::builder().narrow(255).normal(0).build();

    let err = result.unwrap_err();
    assert_eq!(err.field, "narrow");
}

// =============================================================================
// Flags
// =============================================================================

#[bit_storage(repr = u64)]
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
    let s = FlagsOnly::builder()
        .a(false)
        .b(false)
        .high(false)
        .build()
        .unwrap();

    assert_eq!(s.raw(), 0);
}

#[test]
fn flags_all_true() {
    let s = FlagsOnly::builder()
        .a(true)
        .b(true)
        .high(true)
        .build()
        .unwrap();

    assert_eq!(s.raw(), 1 | 2 | (1u64 << 63));
}

#[test]
fn flags_accessors() {
    let raw: u64 = 1 | (1 << 63);
    let s = FlagsOnly::from_raw(raw);

    assert!(s.a());
    assert!(!s.b());
    assert!(s.high());
}

#[test]
fn flags_roundtrip() {
    let original = FlagsOnly::builder()
        .a(true)
        .b(false)
        .high(true)
        .build()
        .unwrap();

    let unpacked = FlagsOnly::from_raw(original.raw());
    assert_eq!(original, unpacked);
}

// =============================================================================
// Mixed fields and flags
// =============================================================================

#[bit_storage(repr = u64)]
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
fn mixed_build() {
    let s = Mixed::builder()
        .value(42)
        .enabled(true)
        .count(1000)
        .high_flag(false)
        .build()
        .unwrap();

    let raw = s.raw();
    assert_eq!(raw & 0xFF, 42);
    assert_eq!((raw >> 8) & 1, 1);
    assert_eq!((raw >> 16) & 0xFFFF, 1000);
    assert_eq!((raw >> 63) & 1, 0);
}

#[test]
fn mixed_accessors() {
    let raw: u64 = 42 | (1 << 8) | (1000 << 16);
    let s = Mixed::from_raw(raw);

    assert_eq!(s.value(), 42);
    assert!(s.enabled());
    assert_eq!(s.count(), 1000);
    assert!(!s.high_flag());
}

#[test]
fn mixed_roundtrip() {
    let original = Mixed::builder()
        .value(255)
        .enabled(true)
        .count(65535)
        .high_flag(true)
        .build()
        .unwrap();

    let unpacked = Mixed::from_raw(original.raw());
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

#[bit_storage(repr = u64)]
pub struct OrderFlags {
    #[field(start = 0, len = 1)]
    side: Side,
    #[field(start = 1, len = 2)]
    tif: TimeInForce,
    #[field(start = 3, len = 16)]
    quantity: u16,
}

#[test]
fn enum_fields_build() {
    let s = OrderFlags::builder()
        .side(Side::Buy)
        .tif(TimeInForce::Ioc)
        .quantity(100)
        .build()
        .unwrap();

    // side=0 at bit 0
    // tif=2 at bits 1-2
    // quantity=100 at bits 3-18
    assert_eq!(s.raw(), 0 | (2 << 1) | (100 << 3));
}

#[test]
fn enum_fields_accessors_valid() {
    let raw: u64 = 1 | (3 << 1) | (500 << 3); // Sell, Fok, 500
    let s = OrderFlags::from_raw(raw);

    assert_eq!(s.side().unwrap(), Side::Sell);
    assert_eq!(s.tif().unwrap(), TimeInForce::Fok);
    assert_eq!(s.quantity(), 500);
}

#[test]
fn enum_fields_roundtrip() {
    let original = OrderFlags::builder()
        .side(Side::Sell)
        .tif(TimeInForce::Gtc)
        .quantity(12345)
        .build()
        .unwrap();

    let unpacked = OrderFlags::from_raw(original.raw());
    assert_eq!(unpacked.side().unwrap(), Side::Sell);
    assert_eq!(unpacked.tif().unwrap(), TimeInForce::Gtc);
    assert_eq!(unpacked.quantity(), 12345);
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

#[bit_storage(repr = u64)]
pub struct WithSparseEnum {
    #[field(start = 0, len = 4)]
    sparse: SparseEnum,
    #[field(start = 4, len = 8)]
    value: u8,
}

#[test]
fn sparse_enum_valid() {
    let s = WithSparseEnum::builder()
        .sparse(SparseEnum::B)
        .value(42)
        .build()
        .unwrap();

    let unpacked = WithSparseEnum::from_raw(s.raw());
    assert_eq!(unpacked.sparse().unwrap(), SparseEnum::B);
    assert_eq!(unpacked.value(), 42);
}

#[test]
fn sparse_enum_unknown_variant() {
    // Put value 1 in the sparse field (not a valid variant)
    let raw: u64 = 1 | (42 << 4); // sparse=1 (invalid), value=42
    let s = WithSparseEnum::from_raw(raw);
    let err = s.sparse().unwrap_err();
    assert_eq!(err.field, "sparse");
}

#[test]
fn sparse_enum_unknown_variant_3() {
    // Value 3 is also invalid for SparseEnum
    let raw: u64 = 3 | (100 << 4);
    let s = WithSparseEnum::from_raw(raw);
    let err = s.sparse().unwrap_err();
    assert_eq!(err.field, "sparse");
}

// =============================================================================
// Different repr types
// =============================================================================

#[bit_storage(repr = u8)]
pub struct TinyStorage {
    #[field(start = 0, len = 4)]
    low: u8,
    #[field(start = 4, len = 4)]
    high: u8,
}

#[test]
fn u8_repr_build() {
    let s = TinyStorage::builder().low(0xA).high(0xB).build().unwrap();

    assert_eq!(s.raw(), 0xBA);
}

#[test]
fn u8_repr_accessors() {
    let s = TinyStorage::from_raw(0xBA);
    assert_eq!(s.low(), 0xA);
    assert_eq!(s.high(), 0xB);
}

#[bit_storage(repr = u16)]
pub struct U16Storage {
    #[field(start = 0, len = 8)]
    low: u8,
    #[field(start = 8, len = 8)]
    high: u8,
}

#[test]
fn u16_repr_roundtrip() {
    let original = U16Storage::builder().low(0xAB).high(0xCD).build().unwrap();

    assert_eq!(original.raw(), 0xCDAB);
    let unpacked = U16Storage::from_raw(original.raw());
    assert_eq!(unpacked.low(), 0xAB);
    assert_eq!(unpacked.high(), 0xCD);
}

#[bit_storage(repr = u32)]
pub struct U32Storage {
    #[field(start = 0, len = 16)]
    low: u16,
    #[field(start = 16, len = 16)]
    high: u16,
}

#[test]
fn u32_repr_roundtrip() {
    let original = U32Storage::builder()
        .low(0x1234)
        .high(0x5678)
        .build()
        .unwrap();

    assert_eq!(original.raw(), 0x56781234);
    let unpacked = U32Storage::from_raw(original.raw());
    assert_eq!(unpacked.low(), 0x1234);
    assert_eq!(unpacked.high(), 0x5678);
}

#[bit_storage(repr = i64)]
pub struct SignedRepr {
    #[field(start = 0, len = 32)]
    a: u32,
    #[field(start = 32, len = 32)]
    b: u32,
}

#[test]
fn i64_repr_roundtrip() {
    let original = SignedRepr::builder()
        .a(0xDEADBEEF)
        .b(0xCAFEBABE)
        .build()
        .unwrap();

    let unpacked = SignedRepr::from_raw(original.raw());
    assert_eq!(unpacked.a(), 0xDEADBEEF);
    assert_eq!(unpacked.b(), 0xCAFEBABE);
}

// =============================================================================
// Adjacent fields (no gaps)
// =============================================================================

#[bit_storage(repr = u64)]
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
    let original = Adjacent::builder()
        .a(0x1111)
        .b(0x2222)
        .c(0x3333)
        .d(0x4444)
        .build()
        .unwrap();

    assert_eq!(original.raw(), 0x4444_3333_2222_1111);
    let unpacked = Adjacent::from_raw(original.raw());
    assert_eq!(unpacked.a(), 0x1111);
    assert_eq!(unpacked.b(), 0x2222);
    assert_eq!(unpacked.c(), 0x3333);
    assert_eq!(unpacked.d(), 0x4444);
}

// =============================================================================
// Sparse fields (with gaps)
// =============================================================================

#[bit_storage(repr = u64)]
pub struct SparseFields {
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
fn sparse_build() {
    let s = SparseFields::builder()
        .a(0xAA)
        .b(0xBB)
        .c(0xCC)
        .build()
        .unwrap();

    assert_eq!(s.raw(), 0xCC00_0000_00BB_00AA);
}

#[test]
fn sparse_accessors() {
    // Put garbage in the gaps - should be ignored
    let raw: u64 = 0xCC12_3456_78BB_99AA;
    let s = SparseFields::from_raw(raw);
    assert_eq!(s.a(), 0xAA);
    assert_eq!(s.b(), 0xBB);
    assert_eq!(s.c(), 0xCC);
}

// =============================================================================
// Single field
// =============================================================================

#[bit_storage(repr = u64)]
pub struct SingleField {
    #[field(start = 0, len = 64)]
    value: u64,
}

#[test]
fn single_field_full_width() {
    let original = SingleField::builder().value(u64::MAX).build().unwrap();

    assert_eq!(original.raw(), u64::MAX);
    let unpacked = SingleField::from_raw(original.raw());
    assert_eq!(unpacked.value(), u64::MAX);
}

#[test]
fn single_field_zero() {
    let original = SingleField::builder().value(0).build().unwrap();

    assert_eq!(original.raw(), 0);
}

// =============================================================================
// Single flag
// =============================================================================

#[bit_storage(repr = u64)]
pub struct SingleFlag {
    #[flag(0)]
    flag: bool,
}

#[test]
fn single_flag_true() {
    let s = SingleFlag::builder().flag(true).build().unwrap();

    assert_eq!(s.raw(), 1);
}

#[test]
fn single_flag_false() {
    let s = SingleFlag::builder().flag(false).build().unwrap();

    assert_eq!(s.raw(), 0);
}

// =============================================================================
// Real-world-ish: Snowflake ID
// =============================================================================

#[bit_storage(repr = u64)]
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
    let original = SnowflakeId::builder()
        .sequence(4095) // max 12 bits
        .worker(1023) // max 10 bits
        .timestamp((1u64 << 42) - 1) // max 42 bits
        .build()
        .unwrap();

    let unpacked = SnowflakeId::from_raw(original.raw());
    assert_eq!(unpacked.sequence(), 4095);
    assert_eq!(unpacked.worker(), 1023);
    assert_eq!(unpacked.timestamp(), (1u64 << 42) - 1);
}

#[test]
fn snowflake_sequence_overflow() {
    let result = SnowflakeId::builder()
        .sequence(4096) // > 4095
        .worker(0)
        .timestamp(0)
        .build();

    let err = result.unwrap_err();
    assert_eq!(err.field, "sequence");
}

#[test]
fn snowflake_worker_overflow() {
    let result = SnowflakeId::builder()
        .sequence(0)
        .worker(1024) // > 1023
        .timestamp(0)
        .build();

    let err = result.unwrap_err();
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

#[bit_storage(repr = u64)]
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
    let original = InstrumentId::builder()
        .asset_class(AssetClass::Option)
        .exchange(Exchange::Cboe)
        .symbol(123456)
        .is_test(true)
        .build()
        .unwrap();

    let unpacked = InstrumentId::from_raw(original.raw());
    assert_eq!(unpacked.asset_class().unwrap(), AssetClass::Option);
    assert_eq!(unpacked.exchange().unwrap(), Exchange::Cboe);
    assert_eq!(unpacked.symbol(), 123456);
    assert!(unpacked.is_test());
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
                let original = InstrumentId::builder()
                    .asset_class(ac)
                    .exchange(ex)
                    .symbol(999999)
                    .is_test(test)
                    .build()
                    .unwrap();

                let unpacked = InstrumentId::from_raw(original.raw());
                assert_eq!(unpacked.asset_class().unwrap(), ac);
                assert_eq!(unpacked.exchange().unwrap(), ex);
                assert_eq!(unpacked.symbol(), 999999);
                assert_eq!(unpacked.is_test(), test);
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
fn unknown_discriminant_display() {
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
#[bit_storage(repr = u64)]
pub struct CrossesByteBoundary {
    #[field(start = 4, len = 24)] // bits 4-27, spans bytes 0-3
    value: u32,
}

/// Single bit fields scattered across the integer
#[bit_storage(repr = u64)]
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
#[bit_storage(repr = u64)]
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

#[bit_storage(repr = u8)]
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
    let s = CrossesByteBoundary::builder()
        .value(0xABCDEF)
        .build()
        .unwrap();

    // value 0xABCDEF shifted left 4 bits
    assert_eq!(s.raw(), 0xABCDEF << 4);

    let unpacked = CrossesByteBoundary::from_raw(s.raw());
    assert_eq!(unpacked.value(), 0xABCDEF);
}

#[test]
fn scattered_bits_all_set() {
    let s = ScatteredBits::builder()
        .bit0(true)
        .bit7(true)
        .bit8(true)
        .bit15(true)
        .bit31(true)
        .bit32(true)
        .build()
        .unwrap();

    assert_eq!(
        s.raw(),
        (1 << 0) | (1 << 7) | (1 << 8) | (1 << 15) | (1 << 31) | (1 << 32)
    );

    let unpacked = ScatteredBits::from_raw(s.raw());
    assert!(unpacked.bit0());
    assert!(unpacked.bit7());
    assert!(unpacked.bit8());
    assert!(unpacked.bit15());
    assert!(unpacked.bit31());
    assert!(unpacked.bit32());
}

#[test]
fn scattered_bits_alternating() {
    let s = ScatteredBits::builder()
        .bit0(true)
        .bit7(false)
        .bit8(true)
        .bit15(false)
        .bit31(true)
        .bit32(false)
        .build()
        .unwrap();

    let unpacked = ScatteredBits::from_raw(s.raw());
    assert!(unpacked.bit0());
    assert!(!unpacked.bit7());
    assert!(unpacked.bit8());
    assert!(!unpacked.bit15());
    assert!(unpacked.bit31());
    assert!(!unpacked.bit32());
}

#[test]
fn odd_offsets_roundtrip() {
    let s = OddOffsets::builder()
        .a(0b111) // max 3 bits = 7
        .b(0b11111) // max 5 bits = 31
        .c(0b1111111) // max 7 bits = 127
        .d(0b11111111111) // max 11 bits = 2047
        .e(0b1111111111111) // max 13 bits = 8191
        .build()
        .unwrap();

    let unpacked = OddOffsets::from_raw(s.raw());
    assert_eq!(unpacked.a(), 0b111);
    assert_eq!(unpacked.b(), 0b11111);
    assert_eq!(unpacked.c(), 0b1111111);
    assert_eq!(unpacked.d(), 0b11111111111);
    assert_eq!(unpacked.e(), 0b1111111111111);
}

#[test]
fn odd_offsets_specific_values() {
    let s = OddOffsets::builder()
        .a(5)
        .b(17)
        .c(99)
        .d(1234)
        .e(5678)
        .build()
        .unwrap();

    let unpacked = OddOffsets::from_raw(s.raw());
    assert_eq!(unpacked.a(), 5);
    assert_eq!(unpacked.b(), 17);
    assert_eq!(unpacked.c(), 99);
    assert_eq!(unpacked.d(), 1234);
    assert_eq!(unpacked.e(), 5678);
}

#[test]
fn tight_packing_all_combos() {
    for a in [OneBitEnum::Zero, OneBitEnum::One] {
        for b in [OneBitEnum::Zero, OneBitEnum::One] {
            for c in 0..8u8 {
                // 3 bits max = 7
                for d in 0..8u8 {
                    let original = TightPacking::builder().a(a).b(b).c(c).d(d).build().unwrap();

                    let unpacked = TightPacking::from_raw(original.raw());
                    assert_eq!(unpacked.a().unwrap(), a);
                    assert_eq!(unpacked.b().unwrap(), b);
                    assert_eq!(unpacked.c(), c);
                    assert_eq!(unpacked.d(), d);
                }
            }
        }
    }
}

#[test]
fn tight_packing_manual_verify() {
    let s = TightPacking::builder()
        .a(OneBitEnum::One) // bit 0 = 1
        .b(OneBitEnum::Zero) // bit 1 = 0
        .c(0b101) // bits 2-4 = 5
        .d(0b110) // bits 5-7 = 6
        .build()
        .unwrap();

    // bit 0: 1
    // bit 1: 0
    // bits 2-4: 101
    // bits 5-7: 110
    // = 0b110_101_0_1 = 0b11010101 = 0xD5
    assert_eq!(s.raw(), 0b11010101);
}

// =============================================================================
// Builder default behavior
// =============================================================================

#[test]
fn builder_defaults_to_zero() {
    // Builder should start with all zeros
    let s = BasicFields::builder().build().unwrap();
    assert_eq!(s.raw(), 0);
    assert_eq!(s.a(), 0);
    assert_eq!(s.b(), 0);
    assert_eq!(s.c(), 0);
}

#[test]
fn builder_partial_set() {
    // Only set some fields
    let s = BasicFields::builder().b(1000).build().unwrap();

    assert_eq!(s.a(), 0);
    assert_eq!(s.b(), 1000);
    assert_eq!(s.c(), 0);
}

// =============================================================================
// Type existence checks
// =============================================================================

#[test]
fn types_exist() {
    // Verify the generated types exist and have expected traits
    fn assert_copy<T: Copy>() {}
    fn assert_clone<T: Clone>() {}
    fn assert_debug<T: std::fmt::Debug>() {}
    fn assert_eq<T: Eq>() {}

    assert_copy::<BasicFields>();
    assert_clone::<BasicFields>();
    assert_debug::<BasicFields>();
    assert_eq::<BasicFields>();

    assert_copy::<BasicFieldsBuilder>();
    assert_clone::<BasicFieldsBuilder>();
    assert_debug::<BasicFieldsBuilder>();

    assert_copy::<SnowflakeId>();
    assert_copy::<SnowflakeIdBuilder>();
}

#[test]
fn from_raw_and_raw_are_inverses() {
    let raw: u64 = 0x1234_5678_9ABC_DEF0;
    let s = BasicFields::from_raw(raw);
    assert_eq!(s.raw(), raw);
}

// =============================================================================
// u128 repr
// =============================================================================

#[bit_storage(repr = u128)]
pub struct U128Storage {
    #[field(start = 0, len = 64)]
    low: u64,
    #[field(start = 64, len = 64)]
    high: u64,
}

#[test]
fn u128_repr_roundtrip() {
    let original = U128Storage::builder()
        .low(0xDEADBEEF_CAFEBABE)
        .high(0x12345678_9ABCDEF0)
        .build()
        .unwrap();

    let unpacked = U128Storage::from_raw(original.raw());
    assert_eq!(unpacked.low(), 0xDEADBEEF_CAFEBABE);
    assert_eq!(unpacked.high(), 0x12345678_9ABCDEF0);
}

#[test]
fn u128_full_width() {
    #[bit_storage(repr = u128)]
    pub struct FullU128 {
        #[field(start = 0, len = 128)]
        value: u128,
    }

    let original = FullU128::builder().value(u128::MAX).build().unwrap();
    assert_eq!(original.raw(), u128::MAX);
    assert_eq!(original.value(), u128::MAX);
}

// =============================================================================
// i128 repr
// =============================================================================

#[bit_storage(repr = i128)]
pub struct I128Storage {
    #[field(start = 0, len = 64)]
    a: u64,
    #[field(start = 64, len = 64)]
    b: u64,
}

#[test]
fn i128_repr_roundtrip() {
    let original = I128Storage::builder()
        .a(u64::MAX)
        .b(u64::MAX)
        .build()
        .unwrap();

    let unpacked = I128Storage::from_raw(original.raw());
    assert_eq!(unpacked.a(), u64::MAX);
    assert_eq!(unpacked.b(), u64::MAX);
}

// =============================================================================
// Signed field types
// =============================================================================

#[bit_storage(repr = u32)]
pub struct SignedFields {
    #[field(start = 0, len = 8)]
    signed_byte: i8,
    #[field(start = 8, len = 16)]
    signed_short: i16,
}

#[test]
fn signed_fields_positive() {
    let s = SignedFields::builder()
        .signed_byte(127)
        .signed_short(32767)
        .build()
        .unwrap();

    let unpacked = SignedFields::from_raw(s.raw());
    assert_eq!(unpacked.signed_byte(), 127);
    assert_eq!(unpacked.signed_short(), 32767);
}

#[test]
fn signed_fields_negative() {
    // Note: negative values get truncated to their bit pattern
    // -1i8 = 0xFF, which fits in 8 bits
    let s = SignedFields::builder()
        .signed_byte(-1)
        .signed_short(-1)
        .build()
        .unwrap();

    let unpacked = SignedFields::from_raw(s.raw());
    // When we read back, we interpret as signed
    assert_eq!(unpacked.signed_byte(), -1);
    assert_eq!(unpacked.signed_short(), -1);
}

#[test]
fn signed_fields_min_values() {
    let s = SignedFields::builder()
        .signed_byte(i8::MIN) // -128
        .signed_short(i16::MIN) // -32768
        .build()
        .unwrap();

    let unpacked = SignedFields::from_raw(s.raw());
    assert_eq!(unpacked.signed_byte(), i8::MIN);
    assert_eq!(unpacked.signed_short(), i16::MIN);
}

// =============================================================================
// Builder overwrite behavior
// =============================================================================

#[test]
fn builder_overwrite() {
    let s = BasicFields::builder()
        .a(100)
        .a(200) // Should overwrite
        .build()
        .unwrap();
    assert_eq!(s.a(), 200);
}

#[test]
fn builder_overwrite_multiple_fields() {
    let s = BasicFields::builder()
        .a(1)
        .b(2)
        .c(3)
        .a(10) // Overwrite a
        .b(20) // Overwrite b
        .build()
        .unwrap();

    assert_eq!(s.a(), 10);
    assert_eq!(s.b(), 20);
    assert_eq!(s.c(), 3);
}

#[test]
fn builder_overwrite_flag() {
    let s = FlagsOnly::builder()
        .a(true)
        .a(false) // Overwrite
        .build()
        .unwrap();

    assert!(!s.a());
}

// =============================================================================
// Hash trait
// =============================================================================

#[test]
fn hash_works() {
    use std::collections::HashSet;

    let mut set = HashSet::new();
    set.insert(BasicFields::from_raw(123));
    set.insert(BasicFields::from_raw(456));
    set.insert(BasicFields::from_raw(123)); // Duplicate

    assert_eq!(set.len(), 2);
    assert!(set.contains(&BasicFields::from_raw(123)));
    assert!(set.contains(&BasicFields::from_raw(456)));
    assert!(!set.contains(&BasicFields::from_raw(789)));
}

#[test]
fn hash_as_map_key() {
    use std::collections::HashMap;

    let mut map = HashMap::new();
    let id1 = SnowflakeId::builder()
        .sequence(1)
        .worker(1)
        .timestamp(1000)
        .build()
        .unwrap();
    let id2 = SnowflakeId::builder()
        .sequence(2)
        .worker(1)
        .timestamp(1000)
        .build()
        .unwrap();

    map.insert(id1, "first");
    map.insert(id2, "second");

    assert_eq!(map.get(&id1), Some(&"first"));
    assert_eq!(map.get(&id2), Some(&"second"));
}

// =============================================================================
// IntEnum overflow in builder (BUG: currently not validated!)
// =============================================================================

#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum LargeEnum {
    Small = 0,
    Medium = 15, // Max that fits in 4 bits
    Big = 255,   // Won't fit in 4 bits
}

#[bit_storage(repr = u64)]
pub struct WithLargeEnum {
    #[field(start = 0, len = 4)] // max value is 15
    val: LargeEnum,
}

#[test]
fn enum_field_valid_values() {
    // Small = 0, fits fine
    let s = WithLargeEnum::builder()
        .val(LargeEnum::Small)
        .build()
        .unwrap();
    assert_eq!(s.val().unwrap(), LargeEnum::Small);

    // Medium = 15, exactly at max
    let s = WithLargeEnum::builder()
        .val(LargeEnum::Medium)
        .build()
        .unwrap();
    assert_eq!(s.val().unwrap(), LargeEnum::Medium);
}

#[test]
fn enum_field_overflow() {
    // Big = 255, should NOT fit in 4 bits (max 15)
    // This test documents the expected behavior: should return error
    let result = WithLargeEnum::builder().val(LargeEnum::Big).build();

    // BUG: Currently this passes but silently truncates!
    // After fix, this should be an error:
    let err = result.unwrap_err();
    assert_eq!(err.field, "val");
}

// =============================================================================
// Timestamp overflow (validates large field overflow detection)
// =============================================================================

#[test]
fn snowflake_timestamp_overflow() {
    // timestamp field is 42 bits, max value is (1 << 42) - 1
    let result = SnowflakeId::builder()
        .sequence(0)
        .worker(0)
        .timestamp(1u64 << 42) // One more than max
        .build();

    let err = result.unwrap_err();
    assert_eq!(err.field, "timestamp");
}

#[test]
fn snowflake_timestamp_at_max() {
    // Exactly at max should work
    let max_ts = (1u64 << 42) - 1;
    let s = SnowflakeId::builder()
        .sequence(0)
        .worker(0)
        .timestamp(max_ts)
        .build()
        .unwrap();

    assert_eq!(s.timestamp(), max_ts);
}

// =============================================================================
// Visibility preservation
// =============================================================================

mod inner {
    use nexus_bits::bit_storage;

    #[bit_storage(repr = u32)]
    pub struct PublicStorage {
        #[field(start = 0, len = 16)]
        value: u16,
    }

    #[bit_storage(repr = u32)]
    struct PrivateStorage {
        #[field(start = 0, len = 16)]
        value: u16,
    }

    #[test]
    fn private_storage_works() {
        let s = PrivateStorage::builder().value(123).build().unwrap();
        assert_eq!(s.value(), 123);
    }
}

#[test]
fn public_storage_accessible() {
    let s = inner::PublicStorage::builder().value(456).build().unwrap();
    assert_eq!(s.value(), 456);
}
