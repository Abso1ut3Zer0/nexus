//! Tests for bit_storage attribute macro on tagged enums.

use nexus_bits::{IntEnum, bit_storage};

// =============================================================================
// Basic tagged enum
// =============================================================================

#[bit_storage(repr = u64, discriminant(start = 0, len = 4))]
pub enum BasicEnum {
    #[variant(0)]
    Empty,
    #[variant(1)]
    WithU8 {
        #[field(start = 4, len = 8)]
        value: u8,
    },
    #[variant(2)]
    WithU16 {
        #[field(start = 4, len = 16)]
        value: u16,
    },
}

#[test]
fn basic_enum_empty_variant() {
    let empty = BasicEnum::empty().build().unwrap();
    assert_eq!(empty.raw(), 0);

    let parent = empty.as_parent();
    assert_eq!(parent.raw(), 0);
    assert!(parent.is_empty());
    assert!(!parent.is_with_u8());
    assert!(!parent.is_with_u16());
}

#[test]
fn basic_enum_with_u8() {
    let with_u8 = BasicEnum::with_u8().value(42).build().unwrap();

    // discriminant = 1 at bits 0-3
    // value = 42 at bits 4-11
    assert_eq!(with_u8.raw(), 1 | (42 << 4));
    assert_eq!(with_u8.value(), 42);

    let parent = with_u8.as_parent();
    assert!(parent.is_with_u8());

    let unpacked = parent.as_with_u8().unwrap();
    assert_eq!(unpacked.value(), 42);
}

#[test]
fn basic_enum_with_u16() {
    let with_u16 = BasicEnum::with_u16().value(1000).build().unwrap();

    assert_eq!(with_u16.raw(), 2 | (1000 << 4));
    assert_eq!(with_u16.value(), 1000);

    let parent = with_u16.as_parent();
    let unpacked = parent.as_with_u16().unwrap();
    assert_eq!(unpacked.value(), 1000);
}

#[test]
fn basic_enum_unknown_discriminant() {
    let raw: u64 = 15; // discriminant 15 not defined
    let parent = BasicEnum::from_raw(raw);

    assert!(parent.kind().is_err());
    assert!(!parent.is_empty());
    assert!(!parent.is_with_u8());
    assert!(!parent.is_with_u16());
    assert!(parent.as_empty().is_err());
}

#[test]
fn basic_enum_kind() {
    let empty = BasicEnum::empty().build().unwrap().as_parent();
    let with_u8 = BasicEnum::with_u8().value(1).build().unwrap().as_parent();
    let with_u16 = BasicEnum::with_u16().value(2).build().unwrap().as_parent();

    assert_eq!(empty.kind().unwrap(), BasicEnumKind::Empty);
    assert_eq!(with_u8.kind().unwrap(), BasicEnumKind::WithU8);
    assert_eq!(with_u16.kind().unwrap(), BasicEnumKind::WithU16);
}

// =============================================================================
// Multiple fields per variant
// =============================================================================

#[bit_storage(repr = u64, discriminant(start = 0, len = 4))]
pub enum MultiField {
    #[variant(0)]
    Pair {
        #[field(start = 4, len = 16)]
        a: u16,
        #[field(start = 20, len = 16)]
        b: u16,
    },
    #[variant(1)]
    Triple {
        #[field(start = 4, len = 8)]
        x: u8,
        #[field(start = 12, len = 8)]
        y: u8,
        #[field(start = 20, len = 8)]
        z: u8,
    },
}

#[test]
fn multi_field_pair() {
    let pair = MultiField::pair().a(1000).b(2000).build().unwrap();

    assert_eq!(pair.a(), 1000);
    assert_eq!(pair.b(), 2000);

    let parent = pair.as_parent();
    let unpacked = parent.as_pair().unwrap();
    assert_eq!(unpacked.a(), 1000);
    assert_eq!(unpacked.b(), 2000);
}

#[test]
fn multi_field_triple() {
    let triple = MultiField::triple().x(10).y(20).z(30).build().unwrap();

    assert_eq!(triple.x(), 10);
    assert_eq!(triple.y(), 20);
    assert_eq!(triple.z(), 30);

    let parent = triple.as_parent();
    let unpacked = parent.as_triple().unwrap();
    assert_eq!(unpacked.x(), 10);
    assert_eq!(unpacked.y(), 20);
    assert_eq!(unpacked.z(), 30);
}

// =============================================================================
// With flags
// =============================================================================

#[bit_storage(repr = u64, discriminant(start = 0, len = 2))]
pub enum WithFlags {
    #[variant(0)]
    FlagsOnly {
        #[flag(2)]
        a: bool,
        #[flag(3)]
        b: bool,
    },
    #[variant(1)]
    Mixed {
        #[field(start = 4, len = 8)]
        value: u8,
        #[flag(63)]
        high: bool,
    },
}

#[test]
fn with_flags_only() {
    let flags = WithFlags::flags_only().a(true).b(false).build().unwrap();

    assert!(flags.a());
    assert!(!flags.b());
    assert_eq!(flags.raw(), 0 | (1 << 2));

    let parent = flags.as_parent();
    let unpacked = parent.as_flags_only().unwrap();
    assert!(unpacked.a());
    assert!(!unpacked.b());
}

#[test]
fn with_flags_mixed() {
    let mixed = WithFlags::mixed().value(255).high(true).build().unwrap();

    assert_eq!(mixed.value(), 255);
    assert!(mixed.high());
    assert_eq!(mixed.raw(), 1 | (255 << 4) | (1u64 << 63));

    let parent = mixed.as_parent();
    let unpacked = parent.as_mixed().unwrap();
    assert_eq!(unpacked.value(), 255);
    assert!(unpacked.high());
}

// =============================================================================
// With IntEnum fields
// =============================================================================

#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Side {
    Buy = 0,
    Sell = 1,
}

#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Exchange {
    Nasdaq = 0,
    Nyse = 1,
    Cboe = 2,
}

#[bit_storage(repr = u64, discriminant(start = 0, len = 4))]
pub enum Order {
    #[variant(0)]
    Market {
        #[field(start = 4, len = 1)]
        side: Side,
        #[field(start = 5, len = 8)]
        exchange: Exchange,
        #[field(start = 16, len = 32)]
        quantity: u32,
    },
    #[variant(1)]
    Limit {
        #[field(start = 4, len = 1)]
        side: Side,
        #[field(start = 5, len = 8)]
        exchange: Exchange,
        #[field(start = 16, len = 16)]
        quantity: u16,
        #[field(start = 32, len = 32)]
        price: u32,
    },
}

#[test]
fn order_market() {
    let market = Order::market()
        .side(Side::Buy)
        .exchange(Exchange::Nasdaq)
        .quantity(100)
        .build()
        .unwrap();

    assert_eq!(market.side(), Side::Buy);
    assert_eq!(market.exchange(), Exchange::Nasdaq);
    assert_eq!(market.quantity(), 100);

    let parent = market.as_parent();
    assert!(parent.is_market());
    let unpacked = parent.as_market().unwrap();
    assert_eq!(unpacked.side(), Side::Buy);
}

#[test]
fn order_limit() {
    let limit = Order::limit()
        .side(Side::Sell)
        .exchange(Exchange::Cboe)
        .quantity(500)
        .price(10050)
        .build()
        .unwrap();

    assert_eq!(limit.side(), Side::Sell);
    assert_eq!(limit.exchange(), Exchange::Cboe);
    assert_eq!(limit.quantity(), 500);
    assert_eq!(limit.price(), 10050);

    let parent = limit.as_parent();
    let unpacked = parent.as_limit().unwrap();
    assert_eq!(unpacked.price(), 10050);
}

// =============================================================================
// Real-world: Instrument ID
// =============================================================================

#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum PutCall {
    Call = 0,
    Put = 1,
}

#[bit_storage(repr = i64, discriminant(start = 0, len = 4))]
pub enum InstrumentId {
    #[variant(0)]
    Equity {
        #[field(start = 4, len = 8)]
        exchange: Exchange,
        #[field(start = 12, len = 20)]
        symbol: u32,
    },
    #[variant(1)]
    Future {
        #[field(start = 4, len = 8)]
        exchange: Exchange,
        #[field(start = 12, len = 16)]
        underlying: u16,
        #[field(start = 28, len = 16)]
        expiry: u16,
    },
    #[variant(2)]
    Option {
        #[field(start = 4, len = 8)]
        exchange: Exchange,
        #[field(start = 12, len = 16)]
        underlying: u16,
        #[field(start = 28, len = 16)]
        expiry: u16,
        #[field(start = 44, len = 16)]
        strike: u16,
        #[field(start = 60, len = 1)]
        put_call: PutCall,
    },
}

#[test]
fn instrument_equity() {
    let equity = InstrumentId::equity()
        .exchange(Exchange::Nyse)
        .symbol(123456)
        .build()
        .unwrap();

    assert_eq!(equity.exchange(), Exchange::Nyse);
    assert_eq!(equity.symbol(), 123456);

    let parent = equity.as_parent();
    assert!(parent.is_equity());
    assert_eq!(parent.kind().unwrap(), InstrumentIdKind::Equity);

    let unpacked = parent.as_equity().unwrap();
    assert_eq!(unpacked.symbol(), 123456);
}

#[test]
fn instrument_future() {
    let future = InstrumentId::future()
        .exchange(Exchange::Cboe)
        .underlying(5000)
        .expiry(2512)
        .build()
        .unwrap();

    assert_eq!(future.exchange(), Exchange::Cboe);
    assert_eq!(future.underlying(), 5000);
    assert_eq!(future.expiry(), 2512);

    let parent = future.as_parent();
    let unpacked = parent.as_future().unwrap();
    assert_eq!(unpacked.underlying(), 5000);
}

#[test]
fn instrument_option() {
    let option = InstrumentId::option()
        .exchange(Exchange::Nasdaq)
        .underlying(1234)
        .expiry(2506)
        .strike(15000)
        .put_call(PutCall::Put)
        .build()
        .unwrap();

    assert_eq!(option.exchange(), Exchange::Nasdaq);
    assert_eq!(option.underlying(), 1234);
    assert_eq!(option.expiry(), 2506);
    assert_eq!(option.strike(), 15000);
    assert_eq!(option.put_call(), PutCall::Put);

    let parent = option.as_parent();
    let unpacked = parent.as_option().unwrap();
    assert_eq!(unpacked.put_call(), PutCall::Put);
}

#[test]
fn instrument_all_variants_roundtrip() {
    // Build each variant, convert to parent, then back
    let equity = InstrumentId::equity()
        .exchange(Exchange::Nasdaq)
        .symbol(0xFFFFF)
        .build()
        .unwrap();

    let future = InstrumentId::future()
        .exchange(Exchange::Cboe)
        .underlying(0xFFFF)
        .expiry(0xFFFF)
        .build()
        .unwrap();

    let option = InstrumentId::option()
        .exchange(Exchange::Nyse)
        .underlying(1000)
        .expiry(2512)
        .strike(5000)
        .put_call(PutCall::Call)
        .build()
        .unwrap();

    // Roundtrip through raw
    let equity2 = InstrumentId::from_raw(equity.raw()).as_equity().unwrap();
    assert_eq!(equity.raw(), equity2.raw());

    let future2 = InstrumentId::from_raw(future.raw()).as_future().unwrap();
    assert_eq!(future.raw(), future2.raw());

    let option2 = InstrumentId::from_raw(option.raw()).as_option().unwrap();
    assert_eq!(option.raw(), option2.raw());
}

// =============================================================================
// Overflow detection
// =============================================================================

#[bit_storage(repr = u64, discriminant(start = 0, len = 4))]
pub enum Narrow {
    #[variant(0)]
    Small {
        #[field(start = 4, len = 4)]
        value: u8, // u8 but only 4 bits
    },
}

#[test]
fn enum_field_valid() {
    let small = Narrow::small().value(15).build().unwrap();
    assert_eq!(small.value(), 15);
}

#[test]
fn enum_field_overflow() {
    let result = Narrow::small().value(16).build(); // 16 > 15 (4-bit max)
    let err = result.unwrap_err();
    assert_eq!(err.field, "value");
}

// =============================================================================
// Sparse discriminants
// =============================================================================

#[bit_storage(repr = u64, discriminant(start = 0, len = 8))]
pub enum Sparse {
    #[variant(0)]
    Zero,
    #[variant(10)]
    Ten {
        #[field(start = 8, len = 8)]
        value: u8,
    },
    #[variant(200)]
    TwoHundred {
        #[field(start = 8, len = 16)]
        value: u16,
    },
}

#[test]
fn sparse_discriminants() {
    let zero = Sparse::zero().build().unwrap();
    let ten = Sparse::ten().value(42).build().unwrap();
    let two_hundred = Sparse::two_hundred().value(1000).build().unwrap();

    assert_eq!(zero.raw() & 0xFF, 0);
    assert_eq!(ten.raw() & 0xFF, 10);
    assert_eq!(two_hundred.raw() & 0xFF, 200);

    // Roundtrip
    let z = Sparse::from_raw(zero.raw());
    let t = Sparse::from_raw(ten.raw());
    let th = Sparse::from_raw(two_hundred.raw());

    assert!(z.is_zero());
    assert!(t.is_ten());
    assert!(th.is_two_hundred());

    assert_eq!(t.as_ten().unwrap().value(), 42);
    assert_eq!(th.as_two_hundred().unwrap().value(), 1000);
}

#[test]
fn sparse_invalid_discriminant() {
    // Values between defined discriminants should fail
    let raw_5: u64 = 5;
    let parent = Sparse::from_raw(raw_5);

    assert!(parent.kind().is_err());
    assert!(!parent.is_zero());
    assert!(!parent.is_ten());
    assert!(!parent.is_two_hundred());
}

// =============================================================================
// Different repr types
// =============================================================================

#[bit_storage(repr = u8, discriminant(start = 0, len = 2))]
pub enum TinyEnum {
    #[variant(0)]
    A {
        #[field(start = 2, len = 6)]
        value: u8,
    },
    #[variant(1)]
    B {
        #[flag(2)]
        flag: bool,
    },
}

#[test]
fn tiny_enum_u8() {
    let a = TinyEnum::a().value(63).build().unwrap(); // max 6-bit
    let b = TinyEnum::b().flag(true).build().unwrap();

    assert_eq!(a.raw(), 0 | (63 << 2));
    assert_eq!(b.raw(), 1 | (1 << 2));

    assert_eq!(a.value(), 63);
    assert!(b.flag());
}

#[bit_storage(repr = i32, discriminant(start = 0, len = 4))]
pub enum SignedEnum {
    #[variant(0)]
    Positive {
        #[field(start = 4, len = 16)]
        value: u16,
    },
}

#[test]
fn signed_repr_enum() {
    let pos = SignedEnum::positive().value(12345).build().unwrap();
    assert_eq!(pos.value(), 12345);

    let parent = pos.as_parent();
    let unpacked = parent.as_positive().unwrap();
    assert_eq!(unpacked.value(), 12345);
}

// =============================================================================
// From impl
// =============================================================================

#[test]
fn from_variant_to_parent() {
    let equity = InstrumentId::equity()
        .exchange(Exchange::Nasdaq)
        .symbol(100)
        .build()
        .unwrap();

    // From trait
    let parent: InstrumentId = equity.into();
    assert!(parent.is_equity());

    // as_parent method
    let parent2 = equity.as_parent();
    assert_eq!(parent.raw(), parent2.raw());
}

// =============================================================================
// Builder accessed from variant type
// =============================================================================

#[test]
fn builder_from_variant_type() {
    // Can also access builder from the variant type itself
    let equity = InstrumentIdEquity::builder()
        .exchange(Exchange::Cboe)
        .symbol(999)
        .build()
        .unwrap();

    assert_eq!(equity.exchange(), Exchange::Cboe);
    assert_eq!(equity.symbol(), 999);
}

// =============================================================================
// build_parent convenience
// =============================================================================

#[test]
fn build_parent_direct() {
    // Build directly to parent type
    let parent = InstrumentId::equity()
        .exchange(Exchange::Nasdaq)
        .symbol(42)
        .build_parent()
        .unwrap();

    assert!(parent.is_equity());
    assert_eq!(parent.as_equity().unwrap().symbol(), 42);
}

// =============================================================================
// IntEnum validation in as_variant
// =============================================================================

#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum SparseIntEnum {
    A = 0,
    B = 5,
    C = 10,
}

#[bit_storage(repr = u64, discriminant(start = 0, len = 4))]
pub enum WithSparseIntEnum {
    #[variant(0)]
    Foo {
        #[field(start = 4, len = 4)]
        value: SparseIntEnum,
    },
}

#[test]
fn as_variant_validates_int_enum() {
    // Construct valid raw
    let foo = WithSparseIntEnum::foo()
        .value(SparseIntEnum::B)
        .build()
        .unwrap();
    let parent = foo.as_parent();

    // This should work
    let unpacked = parent.as_foo().unwrap();
    assert_eq!(unpacked.value(), SparseIntEnum::B);
}

#[test]
fn as_variant_rejects_invalid_int_enum() {
    // Manually construct raw with valid discriminant but invalid IntEnum
    // discriminant = 0, value = 3 (not a valid SparseIntEnum)
    let raw: u64 = 0 | (3 << 4);
    let parent = WithSparseIntEnum::from_raw(raw);

    // Discriminant is correct
    assert!(parent.is_foo());

    // But as_foo should fail because IntEnum is invalid
    assert!(parent.as_foo().is_err());
}

// =============================================================================
// Hash and equality
// =============================================================================

#[test]
fn variant_types_hashable() {
    use std::collections::HashSet;

    let mut set = HashSet::new();

    let e1 = InstrumentId::equity()
        .exchange(Exchange::Nasdaq)
        .symbol(1)
        .build()
        .unwrap();
    let e2 = InstrumentId::equity()
        .exchange(Exchange::Nasdaq)
        .symbol(2)
        .build()
        .unwrap();
    let e1_dup = InstrumentId::equity()
        .exchange(Exchange::Nasdaq)
        .symbol(1)
        .build()
        .unwrap();

    set.insert(e1);
    set.insert(e2);
    set.insert(e1_dup); // duplicate

    assert_eq!(set.len(), 2);
}

#[test]
fn parent_types_hashable() {
    use std::collections::HashSet;

    let mut set = HashSet::new();

    let p1 = InstrumentId::equity()
        .exchange(Exchange::Nasdaq)
        .symbol(1)
        .build_parent()
        .unwrap();
    let p2 = InstrumentId::future()
        .exchange(Exchange::Nyse)
        .underlying(100)
        .expiry(2512)
        .build_parent()
        .unwrap();

    set.insert(p1);
    set.insert(p2);

    assert_eq!(set.len(), 2);
}

// =============================================================================
// Traits exist
// =============================================================================

#[test]
fn types_have_expected_traits() {
    fn assert_traits<T: Copy + Clone + std::fmt::Debug + Eq + std::hash::Hash>() {}

    // Parent type
    assert_traits::<InstrumentId>();

    // Variant types
    assert_traits::<InstrumentIdEquity>();
    assert_traits::<InstrumentIdFuture>();
    assert_traits::<InstrumentIdOption>();

    // Kind enum
    assert_traits::<InstrumentIdKind>();
}

#[test]
fn builders_have_expected_traits() {
    fn assert_traits<T: Copy + Clone + std::fmt::Debug + Default>() {}

    assert_traits::<InstrumentIdEquityBuilder>();
    assert_traits::<InstrumentIdFutureBuilder>();
    assert_traits::<InstrumentIdOptionBuilder>();
}

// =============================================================================
// Unit variant (no fields)
// =============================================================================

#[bit_storage(repr = u32, discriminant(start = 0, len = 8))]
pub enum WithUnitVariants {
    #[variant(0)]
    Empty,
    #[variant(1)]
    AlsoEmpty,
    #[variant(2)]
    HasField {
        #[field(start = 8, len = 16)]
        value: u16,
    },
}

#[test]
fn unit_variants() {
    let empty = WithUnitVariants::empty().build().unwrap();
    let also_empty = WithUnitVariants::also_empty().build().unwrap();
    let has_field = WithUnitVariants::has_field().value(42).build().unwrap();

    assert_eq!(empty.raw(), 0);
    assert_eq!(also_empty.raw(), 1);
    assert_eq!(has_field.raw(), 2 | (42 << 8));

    let p1 = WithUnitVariants::from_raw(0);
    let p2 = WithUnitVariants::from_raw(1);

    assert!(p1.is_empty());
    assert!(p2.is_also_empty());
    assert_eq!(p1.kind().unwrap(), WithUnitVariantsKind::Empty);
    assert_eq!(p2.kind().unwrap(), WithUnitVariantsKind::AlsoEmpty);
}

// =============================================================================
// STRESS TEST - The Monster Enum
// =============================================================================

#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum StressSide {
    Buy = 0,
    Sell = 1,
}

#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum StressTif {
    Day = 0,
    Gtc = 1,
    Ioc = 2,
    Fok = 3,
    Gtd = 4,
    Opg = 5,
    Cls = 6,
    Ato = 7,
}

#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum StressVenue {
    Nasdaq = 0,
    Nyse = 1,
    Arca = 2,
    Bats = 3,
    Iex = 4,
    Edgx = 5,
    Edga = 6,
    Byx = 7,
    Bzx = 8,
    Memx = 9,
    Ltse = 10,
    Phlx = 11,
    Amex = 12,
    Cboe = 13,
    C2 = 14,
    Miax = 15,
}

#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum StressAsset {
    Equity = 0,
    Etf = 1,
    Index = 2,
    Future = 3,
    Option = 4,
    Forex = 5,
    Crypto = 6,
    Bond = 7,
}

#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum OneBit {
    Zero = 0,
    One = 1,
}

#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum TwoBit {
    A = 0,
    B = 1,
    C = 2,
    D = 3,
}

/// The monster enum - 16 variants, mix of everything
#[bit_storage(repr = u128, discriminant(start = 0, len = 4))]
pub enum Monster {
    /// Empty variant
    #[variant(0)]
    Empty,

    /// Just flags
    #[variant(1)]
    FlagsOnly {
        #[flag(4)]
        a: bool,
        #[flag(5)]
        b: bool,
        #[flag(6)]
        c: bool,
        #[flag(7)]
        d: bool,
        #[flag(64)]
        e: bool,
        #[flag(127)]
        f: bool,
    },

    /// Just one primitive
    #[variant(2)]
    SinglePrimitive {
        #[field(start = 4, len = 64)]
        big: u64,
    },

    /// Just one IntEnum
    #[variant(3)]
    SingleEnum {
        #[field(start = 4, len = 4)]
        venue: StressVenue,
    },

    /// Mix of primitives at weird offsets
    #[variant(4)]
    WeirdOffsets {
        #[field(start = 4, len = 3)]
        three_bits: u8,
        #[field(start = 7, len = 5)]
        five_bits: u8,
        #[field(start = 12, len = 7)]
        seven_bits: u8,
        #[field(start = 19, len = 11)]
        eleven_bits: u16,
        #[field(start = 30, len = 13)]
        thirteen_bits: u16,
        #[field(start = 43, len = 17)]
        seventeen_bits: u32,
        #[field(start = 60, len = 19)]
        nineteen_bits: u32,
    },

    /// Many IntEnums
    #[variant(5)]
    ManyEnums {
        #[field(start = 4, len = 1)]
        side: StressSide,
        #[field(start = 5, len = 3)]
        tif: StressTif,
        #[field(start = 8, len = 4)]
        venue: StressVenue,
        #[field(start = 12, len = 3)]
        asset: StressAsset,
        #[field(start = 15, len = 1)]
        bit1: OneBit,
        #[field(start = 16, len = 2)]
        bit2: TwoBit,
    },

    /// Mix of everything
    #[variant(6)]
    Kitchen {
        #[field(start = 4, len = 1)]
        side: StressSide,
        #[flag(5)]
        is_hidden: bool,
        #[field(start = 6, len = 4)]
        venue: StressVenue,
        #[flag(10)]
        is_routed: bool,
        #[field(start = 11, len = 32)]
        quantity: u32,
        #[flag(43)]
        is_test: bool,
        #[field(start = 44, len = 20)]
        symbol: u32,
        #[field(start = 64, len = 48)]
        price: u64,
        #[flag(112)]
        high_bit: bool,
    },

    /// Fields spanning byte boundaries
    #[variant(7)]
    ByteSpanners {
        #[field(start = 4, len = 12)]
        spans_0_1: u16,
        #[field(start = 16, len = 24)]
        spans_2_4: u32,
        #[field(start = 40, len = 36)]
        spans_5_9: u64,
        #[field(start = 76, len = 44)]
        spans_9_14: u64,
    },

    /// Maximum values for small widths
    #[variant(8)]
    MaxValues {
        #[field(start = 4, len = 1)]
        max1: u8,
        #[field(start = 5, len = 2)]
        max2: u8,
        #[field(start = 7, len = 3)]
        max3: u8,
        #[field(start = 10, len = 4)]
        max4: u8,
        #[field(start = 14, len = 5)]
        max5: u8,
        #[field(start = 19, len = 6)]
        max6: u8,
        #[field(start = 25, len = 7)]
        max7: u8,
        #[field(start = 32, len = 8)]
        max8: u8,
    },

    /// Sparse bit positions
    #[variant(9)]
    SparseBits {
        #[flag(4)]
        bit4: bool,
        #[flag(16)]
        bit16: bool,
        #[flag(32)]
        bit32: bool,
        #[flag(48)]
        bit48: bool,
        #[flag(64)]
        bit64: bool,
        #[flag(80)]
        bit80: bool,
        #[flag(96)]
        bit96: bool,
        #[flag(112)]
        bit112: bool,
    },

    /// High bits only
    #[variant(10)]
    HighBits {
        #[field(start = 64, len = 32)]
        upper_mid: u32,
        #[field(start = 96, len = 31)]
        upper: u32,
    },

    /// Single bit IntEnums packed tight
    #[variant(11)]
    TightEnums {
        #[field(start = 4, len = 1)]
        e0: OneBit,
        #[field(start = 5, len = 1)]
        e1: OneBit,
        #[field(start = 6, len = 1)]
        e2: OneBit,
        #[field(start = 7, len = 1)]
        e3: OneBit,
        #[field(start = 8, len = 2)]
        t0: TwoBit,
        #[field(start = 10, len = 2)]
        t1: TwoBit,
        #[field(start = 12, len = 2)]
        t2: TwoBit,
        #[field(start = 14, len = 2)]
        t3: TwoBit,
    },

    /// All zeros should work
    #[variant(12)]
    AllZeros {
        #[field(start = 4, len = 32)]
        zero1: u32,
        #[field(start = 36, len = 32)]
        zero2: u32,
        #[flag(68)]
        false_flag: bool,
    },

    /// Almost full 128 bits
    #[variant(13)]
    AlmostFull {
        #[field(start = 4, len = 60)]
        chunk1: u64,
        #[field(start = 64, len = 63)]
        chunk2: u64,
    },

    /// Discriminant at edge
    #[variant(14)]
    EdgeDiscriminant {
        #[field(start = 4, len = 4)]
        small: u8,
    },

    /// Max discriminant value (15 for 4-bit)
    #[variant(15)]
    MaxDiscriminant {
        #[field(start = 4, len = 8)]
        value: u8,
        #[field(start = 12, len = 16)]
        other: u16,
    },
}

#[test]
fn monster_empty() {
    let m = Monster::empty().build().unwrap();
    assert_eq!(m.raw(), 0u128);

    let parent = m.as_parent();
    assert!(parent.is_empty());
    assert_eq!(parent.kind().unwrap(), MonsterKind::Empty);
}

#[test]
fn monster_flags_only() {
    let m = Monster::flags_only()
        .a(true)
        .b(false)
        .c(true)
        .d(false)
        .e(true)
        .f(true)
        .build()
        .unwrap();

    assert!(m.a());
    assert!(!m.b());
    assert!(m.c());
    assert!(!m.d());
    assert!(m.e());
    assert!(m.f());

    let raw = m.raw();
    assert_eq!(raw & (1 << 0), 1); // discriminant
    assert_ne!(raw & (1 << 4), 0); // a
    assert_eq!(raw & (1 << 5), 0); // b
    assert_ne!(raw & (1 << 6), 0); // c
    assert_eq!(raw & (1 << 7), 0); // d
    assert_ne!(raw & (1 << 64), 0); // e
    assert_ne!(raw & (1 << 127), 0); // f

    let parent = m.as_parent();
    let unpacked = parent.as_flags_only().unwrap();
    assert!(unpacked.a());
    assert!(!unpacked.b());
}

#[test]
fn monster_single_primitive() {
    let m = Monster::single_primitive()
        .big(0xDEAD_BEEF_CAFE_BABE)
        .build()
        .unwrap();

    assert_eq!(m.big(), 0xDEAD_BEEF_CAFE_BABE);

    let parent = m.as_parent();
    let unpacked = parent.as_single_primitive().unwrap();
    assert_eq!(unpacked.big(), 0xDEAD_BEEF_CAFE_BABE);
}

#[test]
fn monster_single_enum() {
    for venue in [
        StressVenue::Nasdaq,
        StressVenue::Nyse,
        StressVenue::Memx,
        StressVenue::Miax,
    ] {
        let m = Monster::single_enum().venue(venue).build().unwrap();
        assert_eq!(m.venue(), venue);

        let parent = m.as_parent();
        let unpacked = parent.as_single_enum().unwrap();
        assert_eq!(unpacked.venue(), venue);
    }
}

#[test]
fn monster_weird_offsets() {
    let m = Monster::weird_offsets()
        .three_bits(7) // max 3-bit
        .five_bits(31) // max 5-bit
        .seven_bits(127) // max 7-bit
        .eleven_bits(2047) // max 11-bit
        .thirteen_bits(8191) // max 13-bit
        .seventeen_bits((1 << 17) - 1)
        .nineteen_bits((1 << 19) - 1)
        .build()
        .unwrap();

    assert_eq!(m.three_bits(), 7);
    assert_eq!(m.five_bits(), 31);
    assert_eq!(m.seven_bits(), 127);
    assert_eq!(m.eleven_bits(), 2047);
    assert_eq!(m.thirteen_bits(), 8191);
    assert_eq!(m.seventeen_bits(), (1 << 17) - 1);
    assert_eq!(m.nineteen_bits(), (1 << 19) - 1);

    let parent = m.as_parent();
    let unpacked = parent.as_weird_offsets().unwrap();
    assert_eq!(unpacked.three_bits(), 7);
}

#[test]
fn monster_many_enums() {
    let m = Monster::many_enums()
        .side(StressSide::Sell)
        .tif(StressTif::Fok)
        .venue(StressVenue::Cboe)
        .asset(StressAsset::Option)
        .bit1(OneBit::One)
        .bit2(TwoBit::C)
        .build()
        .unwrap();

    assert_eq!(m.side(), StressSide::Sell);
    assert_eq!(m.tif(), StressTif::Fok);
    assert_eq!(m.venue(), StressVenue::Cboe);
    assert_eq!(m.asset(), StressAsset::Option);
    assert_eq!(m.bit1(), OneBit::One);
    assert_eq!(m.bit2(), TwoBit::C);

    let parent = m.as_parent();
    let unpacked = parent.as_many_enums().unwrap();
    assert_eq!(unpacked.side(), StressSide::Sell);
}

#[test]
fn monster_kitchen_sink() {
    let m = Monster::kitchen()
        .side(StressSide::Buy)
        .is_hidden(true)
        .venue(StressVenue::Iex)
        .is_routed(false)
        .quantity(1_000_000)
        .is_test(true)
        .symbol(0xABCDE)
        .price(0x1234_5678_9ABC)
        .high_bit(true)
        .build()
        .unwrap();

    assert_eq!(m.side(), StressSide::Buy);
    assert!(m.is_hidden());
    assert_eq!(m.venue(), StressVenue::Iex);
    assert!(!m.is_routed());
    assert_eq!(m.quantity(), 1_000_000);
    assert!(m.is_test());
    assert_eq!(m.symbol(), 0xABCDE);
    assert_eq!(m.price(), 0x1234_5678_9ABC);
    assert!(m.high_bit());

    let parent = m.as_parent();
    let unpacked = parent.as_kitchen().unwrap();
    assert_eq!(unpacked.quantity(), 1_000_000);
}

#[test]
fn monster_byte_spanners() {
    let m = Monster::byte_spanners()
        .spans_0_1(0xFFF)
        .spans_2_4(0xFF_FFFF)
        .spans_5_9((1u64 << 36) - 1)
        .spans_9_14((1u64 << 44) - 1)
        .build()
        .unwrap();

    assert_eq!(m.spans_0_1(), 0xFFF);
    assert_eq!(m.spans_2_4(), 0xFF_FFFF);
    assert_eq!(m.spans_5_9(), (1u64 << 36) - 1);
    assert_eq!(m.spans_9_14(), (1u64 << 44) - 1);

    let parent = m.as_parent();
    let unpacked = parent.as_byte_spanners().unwrap();
    assert_eq!(unpacked.spans_0_1(), 0xFFF);
}

#[test]
fn monster_max_values() {
    let m = Monster::max_values()
        .max1(1)
        .max2(3)
        .max3(7)
        .max4(15)
        .max5(31)
        .max6(63)
        .max7(127)
        .max8(255)
        .build()
        .unwrap();

    assert_eq!(m.max1(), 1);
    assert_eq!(m.max2(), 3);
    assert_eq!(m.max3(), 7);
    assert_eq!(m.max4(), 15);
    assert_eq!(m.max5(), 31);
    assert_eq!(m.max6(), 63);
    assert_eq!(m.max7(), 127);
    assert_eq!(m.max8(), 255);

    let parent = m.as_parent();
    let unpacked = parent.as_max_values().unwrap();
    assert_eq!(unpacked.max8(), 255);
}

#[test]
fn monster_sparse_bits_all_set() {
    let m = Monster::sparse_bits()
        .bit4(true)
        .bit16(true)
        .bit32(true)
        .bit48(true)
        .bit64(true)
        .bit80(true)
        .bit96(true)
        .bit112(true)
        .build()
        .unwrap();

    assert!(m.bit4());
    assert!(m.bit16());
    assert!(m.bit32());
    assert!(m.bit48());
    assert!(m.bit64());
    assert!(m.bit80());
    assert!(m.bit96());
    assert!(m.bit112());

    let parent = m.as_parent();
    let unpacked = parent.as_sparse_bits().unwrap();
    assert!(unpacked.bit112());
}

#[test]
fn monster_sparse_bits_alternating() {
    let m = Monster::sparse_bits()
        .bit4(true)
        .bit16(false)
        .bit32(true)
        .bit48(false)
        .bit64(true)
        .bit80(false)
        .bit96(true)
        .bit112(false)
        .build()
        .unwrap();

    assert!(m.bit4());
    assert!(!m.bit16());
    assert!(m.bit32());
    assert!(!m.bit48());
    assert!(m.bit64());
    assert!(!m.bit80());
    assert!(m.bit96());
    assert!(!m.bit112());
}

#[test]
fn monster_high_bits() {
    let m = Monster::high_bits()
        .upper_mid(0xFFFF_FFFF)
        .upper(0x7FFF_FFFF) // 31 bits max
        .build()
        .unwrap();

    assert_eq!(m.upper_mid(), 0xFFFF_FFFF);
    assert_eq!(m.upper(), 0x7FFF_FFFF);

    let parent = m.as_parent();
    let unpacked = parent.as_high_bits().unwrap();
    assert_eq!(unpacked.upper(), 0x7FFF_FFFF);
}

#[test]
fn monster_tight_enums() {
    let m = Monster::tight_enums()
        .e0(OneBit::One)
        .e1(OneBit::Zero)
        .e2(OneBit::One)
        .e3(OneBit::Zero)
        .t0(TwoBit::A)
        .t1(TwoBit::B)
        .t2(TwoBit::C)
        .t3(TwoBit::D)
        .build()
        .unwrap();

    assert_eq!(m.e0(), OneBit::One);
    assert_eq!(m.e1(), OneBit::Zero);
    assert_eq!(m.e2(), OneBit::One);
    assert_eq!(m.e3(), OneBit::Zero);
    assert_eq!(m.t0(), TwoBit::A);
    assert_eq!(m.t1(), TwoBit::B);
    assert_eq!(m.t2(), TwoBit::C);
    assert_eq!(m.t3(), TwoBit::D);

    let parent = m.as_parent();
    let unpacked = parent.as_tight_enums().unwrap();
    assert_eq!(unpacked.t3(), TwoBit::D);
}

#[test]
fn monster_all_zeros() {
    let m = Monster::all_zeros()
        .zero1(0)
        .zero2(0)
        .false_flag(false)
        .build()
        .unwrap();

    // Only discriminant should be set
    assert_eq!(m.raw(), 12u128);
    assert_eq!(m.zero1(), 0);
    assert_eq!(m.zero2(), 0);
    assert!(!m.false_flag());
}

#[test]
fn monster_almost_full() {
    let m = Monster::almost_full()
        .chunk1((1u64 << 60) - 1)
        .chunk2((1u64 << 63) - 1)
        .build()
        .unwrap();

    assert_eq!(m.chunk1(), (1u64 << 60) - 1);
    assert_eq!(m.chunk2(), (1u64 << 63) - 1);

    let parent = m.as_parent();
    let unpacked = parent.as_almost_full().unwrap();
    assert_eq!(unpacked.chunk1(), (1u64 << 60) - 1);
}

#[test]
fn monster_edge_discriminant() {
    let m = Monster::edge_discriminant().small(15).build().unwrap();
    assert_eq!(m.small(), 15);

    let parent = m.as_parent();
    assert!(parent.is_edge_discriminant());
}

#[test]
fn monster_max_discriminant() {
    let m = Monster::max_discriminant()
        .value(255)
        .other(65535)
        .build()
        .unwrap();

    // Discriminant should be 15 (0xF)
    assert_eq!(m.raw() & 0xF, 15);
    assert_eq!(m.value(), 255);
    assert_eq!(m.other(), 65535);

    let parent = m.as_parent();
    assert!(parent.is_max_discriminant());
}

#[test]
fn monster_all_variants_kind_check() {
    // Verify all 16 discriminants are recognized
    for disc in 0u128..16 {
        let raw = disc;
        let parent = Monster::from_raw(raw);
        assert!(
            parent.kind().is_ok(),
            "Discriminant {} should be valid",
            disc
        );
    }
}

#[test]
fn monster_all_variants_roundtrip() {
    // Build one of each variant and verify roundtrip
    let variants: Vec<Monster> = vec![
        Monster::empty().build().unwrap().as_parent(),
        Monster::flags_only()
            .a(true)
            .b(true)
            .c(true)
            .d(true)
            .e(true)
            .f(true)
            .build()
            .unwrap()
            .as_parent(),
        Monster::single_primitive()
            .big(u64::MAX)
            .build()
            .unwrap()
            .as_parent(),
        Monster::single_enum()
            .venue(StressVenue::Miax)
            .build()
            .unwrap()
            .as_parent(),
        Monster::weird_offsets()
            .three_bits(5)
            .five_bits(20)
            .seven_bits(100)
            .eleven_bits(1500)
            .thirteen_bits(7000)
            .seventeen_bits(100000)
            .nineteen_bits(400000)
            .build()
            .unwrap()
            .as_parent(),
        Monster::many_enums()
            .side(StressSide::Buy)
            .tif(StressTif::Ato)
            .venue(StressVenue::Ltse)
            .asset(StressAsset::Crypto)
            .bit1(OneBit::Zero)
            .bit2(TwoBit::D)
            .build()
            .unwrap()
            .as_parent(),
        Monster::kitchen()
            .side(StressSide::Sell)
            .is_hidden(false)
            .venue(StressVenue::Memx)
            .is_routed(true)
            .quantity(999999)
            .is_test(false)
            .symbol(0x12345)
            .price(0xABCD_EF01_2345)
            .high_bit(false)
            .build()
            .unwrap()
            .as_parent(),
        Monster::byte_spanners()
            .spans_0_1(0x123)
            .spans_2_4(0x456789)
            .spans_5_9(0x1_2345_6789)
            .spans_9_14(0xABC_DEF0_1234)
            .build()
            .unwrap()
            .as_parent(),
        Monster::max_values()
            .max1(1)
            .max2(3)
            .max3(7)
            .max4(15)
            .max5(31)
            .max6(63)
            .max7(127)
            .max8(255)
            .build()
            .unwrap()
            .as_parent(),
        Monster::sparse_bits()
            .bit4(false)
            .bit16(true)
            .bit32(false)
            .bit48(true)
            .bit64(false)
            .bit80(true)
            .bit96(false)
            .bit112(true)
            .build()
            .unwrap()
            .as_parent(),
        Monster::high_bits()
            .upper_mid(0x1234_5678)
            .upper(0x7ABC_DEF0)
            .build()
            .unwrap()
            .as_parent(),
        Monster::tight_enums()
            .e0(OneBit::Zero)
            .e1(OneBit::One)
            .e2(OneBit::Zero)
            .e3(OneBit::One)
            .t0(TwoBit::D)
            .t1(TwoBit::C)
            .t2(TwoBit::B)
            .t3(TwoBit::A)
            .build()
            .unwrap()
            .as_parent(),
        Monster::all_zeros()
            .zero1(0)
            .zero2(0)
            .false_flag(false)
            .build()
            .unwrap()
            .as_parent(),
        Monster::almost_full()
            .chunk1(0x0FFF_FFFF_FFFF_FFFF)
            .chunk2(0x7FFF_FFFF_FFFF_FFFF)
            .build()
            .unwrap()
            .as_parent(),
        Monster::edge_discriminant()
            .small(0)
            .build()
            .unwrap()
            .as_parent(),
        Monster::max_discriminant()
            .value(128)
            .other(32768)
            .build()
            .unwrap()
            .as_parent(),
    ];

    for (i, parent) in variants.iter().enumerate() {
        // Roundtrip through raw
        let raw = parent.raw();
        let reconstructed = Monster::from_raw(raw);
        assert_eq!(
            parent.raw(),
            reconstructed.raw(),
            "Variant {} failed roundtrip",
            i
        );
        assert_eq!(parent.kind().unwrap(), reconstructed.kind().unwrap());
    }
}

// =============================================================================
// Additional edge case tests
// =============================================================================

// Builder overwrite behavior for enums
#[test]
fn enum_builder_overwrite() {
    let m = Monster::single_primitive()
        .big(100)
        .big(200) // Should overwrite
        .build()
        .unwrap();

    assert_eq!(m.big(), 200);
}

#[test]
fn enum_builder_overwrite_enum_field() {
    let m = Monster::single_enum()
        .venue(StressVenue::Nasdaq)
        .venue(StressVenue::Cboe) // Should overwrite
        .build()
        .unwrap();

    assert_eq!(m.venue(), StressVenue::Cboe);
}

#[test]
fn enum_builder_overwrite_flag() {
    let m = Monster::flags_only()
        .a(true)
        .a(false) // Should overwrite
        .b(false)
        .c(false)
        .d(false)
        .e(false)
        .f(false)
        .build()
        .unwrap();

    assert!(!m.a());
}

// IntEnum overflow in enum variant builder
#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum LargeVariantEnum {
    Small = 0,
    Medium = 7, // Max that fits in 3 bits
    Big = 255,  // Won't fit in 3 bits
}

#[bit_storage(repr = u64, discriminant(start = 0, len = 4))]
pub enum EnumWithLargeIntEnum {
    #[variant(0)]
    Foo {
        #[field(start = 4, len = 3)] // max value is 7
        val: LargeVariantEnum,
    },
}

#[test]
fn enum_variant_int_enum_valid() {
    let foo = EnumWithLargeIntEnum::foo()
        .val(LargeVariantEnum::Small)
        .build()
        .unwrap();
    assert_eq!(foo.val(), LargeVariantEnum::Small);

    let foo = EnumWithLargeIntEnum::foo()
        .val(LargeVariantEnum::Medium)
        .build()
        .unwrap();
    assert_eq!(foo.val(), LargeVariantEnum::Medium);
}

#[test]
fn enum_variant_int_enum_overflow() {
    // Big = 255, should NOT fit in 3 bits (max 7)
    let result = EnumWithLargeIntEnum::foo()
        .val(LargeVariantEnum::Big)
        .build();

    let err = result.unwrap_err();
    assert_eq!(err.field, "val");
}

// Signed fields in enum variants
#[bit_storage(repr = i64, discriminant(start = 0, len = 4))]
pub enum EnumWithSignedFields {
    #[variant(0)]
    Signed {
        #[field(start = 4, len = 8)]
        signed_byte: i8,
        #[field(start = 12, len = 16)]
        signed_short: i16,
    },
}

#[test]
fn enum_signed_fields_positive() {
    let s = EnumWithSignedFields::signed()
        .signed_byte(127)
        .signed_short(32767)
        .build()
        .unwrap();

    assert_eq!(s.signed_byte(), 127);
    assert_eq!(s.signed_short(), 32767);
}

#[test]
fn enum_signed_fields_negative() {
    let s = EnumWithSignedFields::signed()
        .signed_byte(-1)
        .signed_short(-1)
        .build()
        .unwrap();

    assert_eq!(s.signed_byte(), -1);
    assert_eq!(s.signed_short(), -1);
}

#[test]
fn enum_signed_fields_min_values() {
    let s = EnumWithSignedFields::signed()
        .signed_byte(i8::MIN)
        .signed_short(i16::MIN)
        .build()
        .unwrap();

    assert_eq!(s.signed_byte(), i8::MIN);
    assert_eq!(s.signed_short(), i16::MIN);
}

// Single variant enum
#[bit_storage(repr = u32, discriminant(start = 0, len = 2))]
pub enum SingleVariant {
    #[variant(0)]
    Only {
        #[field(start = 2, len = 16)]
        value: u16,
    },
}

#[test]
fn single_variant_enum() {
    let only = SingleVariant::only().value(12345).build().unwrap();
    assert_eq!(only.value(), 12345);

    let parent = only.as_parent();
    assert!(parent.is_only());
    assert_eq!(parent.kind().unwrap(), SingleVariantKind::Only);

    // Invalid discriminants
    let invalid = SingleVariant::from_raw(1); // discriminant 1 not defined
    assert!(invalid.kind().is_err());
    assert!(!invalid.is_only());
}

// Builder defaults to zero
#[test]
fn enum_builder_defaults_to_zero() {
    let m = Monster::max_values().build().unwrap();

    assert_eq!(m.max1(), 0);
    assert_eq!(m.max2(), 0);
    assert_eq!(m.max3(), 0);
    assert_eq!(m.max4(), 0);
    assert_eq!(m.max5(), 0);
    assert_eq!(m.max6(), 0);
    assert_eq!(m.max7(), 0);
    assert_eq!(m.max8(), 0);
}

#[test]
fn enum_builder_partial_set() {
    let m = Monster::max_values().max4(10).build().unwrap();

    assert_eq!(m.max1(), 0);
    assert_eq!(m.max2(), 0);
    assert_eq!(m.max3(), 0);
    assert_eq!(m.max4(), 10);
    assert_eq!(m.max5(), 0);
    assert_eq!(m.max6(), 0);
    assert_eq!(m.max7(), 0);
    assert_eq!(m.max8(), 0);
}

// Wrong variant access
#[test]
fn wrong_variant_access() {
    let empty = Monster::empty().build().unwrap().as_parent();

    // Try to access as different variant
    assert!(empty.as_empty().is_ok());
    assert!(empty.as_flags_only().is_err());
    assert!(empty.as_single_primitive().is_err());
    assert!(empty.as_kitchen().is_err());
}

// Hash usage for enum types
#[test]
fn enum_variant_hash_in_set() {
    use std::collections::HashSet;

    let mut set = HashSet::new();

    let v1 = Monster::single_primitive().big(100).build().unwrap();
    let v2 = Monster::single_primitive().big(200).build().unwrap();
    let v1_dup = Monster::single_primitive().big(100).build().unwrap();

    set.insert(v1);
    set.insert(v2);
    set.insert(v1_dup); // duplicate

    assert_eq!(set.len(), 2);
}

#[test]
fn enum_parent_hash_in_map() {
    use std::collections::HashMap;

    let mut map = HashMap::new();

    let p1 = Monster::empty().build_parent().unwrap();
    let p2 = Monster::single_primitive().big(42).build_parent().unwrap();

    map.insert(p1, "empty");
    map.insert(p2, "primitive");

    assert_eq!(map.get(&p1), Some(&"empty"));
    assert_eq!(map.get(&p2), Some(&"primitive"));
}
