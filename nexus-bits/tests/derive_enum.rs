////! Tests for BitPacked derive macro on tagged enums.

//use nexus_bits::{BitPacked, IntEnum};

//// =============================================================================
//// Basic tagged enum
//// =============================================================================

//#[derive(BitPacked, Debug, Clone, Copy, PartialEq, Eq)]
//#[packed(repr = u64, discriminant(start = 0, len = 4))]
//pub enum BasicEnum {
//    #[variant(0)]
//    Empty,
//    #[variant(1)]
//    WithU8 {
//        #[field(start = 4, len = 8)]
//        value: u8,
//    },
//    #[variant(2)]
//    WithU16 {
//        #[field(start = 4, len = 16)]
//        value: u16,
//    },
//}

//#[test]
//fn basic_enum_empty_variant() {
//    let e = BasicEnum::Empty;
//    let packed = e.pack().unwrap();
//    assert_eq!(packed, 0);

//    let unpacked = BasicEnum::unpack(packed).unwrap();
//    assert_eq!(unpacked, BasicEnum::Empty);
//}

//#[test]
//fn basic_enum_with_u8() {
//    let e = BasicEnum::WithU8 { value: 42 };
//    let packed = e.pack().unwrap();

//    // discriminant = 1 at bits 0-3
//    // value = 42 at bits 4-11
//    assert_eq!(packed, 1 | (42 << 4));

//    let unpacked = BasicEnum::unpack(packed).unwrap();
//    assert_eq!(unpacked, BasicEnum::WithU8 { value: 42 });
//}

//#[test]
//fn basic_enum_with_u16() {
//    let e = BasicEnum::WithU16 { value: 1000 };
//    let packed = e.pack().unwrap();

//    assert_eq!(packed, 2 | (1000 << 4));

//    let unpacked = BasicEnum::unpack(packed).unwrap();
//    assert_eq!(unpacked, BasicEnum::WithU16 { value: 1000 });
//}

//#[test]
//fn basic_enum_unknown_discriminant() {
//    let raw: u64 = 15; // discriminant 15 not defined
//    let result = BasicEnum::unpack(raw);
//    assert!(result.is_err());
//}

//// =============================================================================
//// Multiple fields per variant
//// =============================================================================

//#[derive(BitPacked, Debug, Clone, Copy, PartialEq, Eq)]
//#[packed(repr = u64, discriminant(start = 0, len = 4))]
//pub enum MultiField {
//    #[variant(0)]
//    Pair {
//        #[field(start = 4, len = 16)]
//        a: u16,
//        #[field(start = 20, len = 16)]
//        b: u16,
//    },
//    #[variant(1)]
//    Triple {
//        #[field(start = 4, len = 8)]
//        x: u8,
//        #[field(start = 12, len = 8)]
//        y: u8,
//        #[field(start = 20, len = 8)]
//        z: u8,
//    },
//}

//#[test]
//fn multi_field_pair() {
//    let e = MultiField::Pair { a: 1000, b: 2000 };
//    let packed = e.pack().unwrap();
//    let unpacked = MultiField::unpack(packed).unwrap();
//    assert_eq!(unpacked, MultiField::Pair { a: 1000, b: 2000 });
//}

//#[test]
//fn multi_field_triple() {
//    let e = MultiField::Triple {
//        x: 10,
//        y: 20,
//        z: 30,
//    };
//    let packed = e.pack().unwrap();
//    let unpacked = MultiField::unpack(packed).unwrap();
//    assert_eq!(
//        unpacked,
//        MultiField::Triple {
//            x: 10,
//            y: 20,
//            z: 30
//        }
//    );
//}

//// =============================================================================
//// With flags
//// =============================================================================

//#[derive(BitPacked, Debug, Clone, Copy, PartialEq, Eq)]
//#[packed(repr = u64, discriminant(start = 0, len = 2))]
//pub enum WithFlags {
//    #[variant(0)]
//    FlagsOnly {
//        #[flag(2)]
//        a: bool,
//        #[flag(3)]
//        b: bool,
//    },
//    #[variant(1)]
//    Mixed {
//        #[field(start = 4, len = 8)]
//        value: u8,
//        #[flag(63)]
//        high: bool,
//    },
//}

//#[test]
//fn with_flags_only() {
//    let e = WithFlags::FlagsOnly { a: true, b: false };
//    let packed = e.pack().unwrap();
//    assert_eq!(packed, 0 | (1 << 2));

//    let unpacked = WithFlags::unpack(packed).unwrap();
//    assert_eq!(unpacked, WithFlags::FlagsOnly { a: true, b: false });
//}

//#[test]
//fn with_flags_mixed() {
//    let e = WithFlags::Mixed {
//        value: 255,
//        high: true,
//    };
//    let packed = e.pack().unwrap();
//    assert_eq!(packed, 1 | (255 << 4) | (1u64 << 63));

//    let unpacked = WithFlags::unpack(packed).unwrap();
//    assert_eq!(
//        unpacked,
//        WithFlags::Mixed {
//            value: 255,
//            high: true
//        }
//    );
//}

//// =============================================================================
//// With IntEnum fields
//// =============================================================================

//#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
//#[repr(u8)]
//pub enum Side {
//    Buy = 0,
//    Sell = 1,
//}

//#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
//#[repr(u8)]
//pub enum Exchange {
//    Nasdaq = 0,
//    Nyse = 1,
//    Cboe = 2,
//}

//#[derive(BitPacked, Debug, Clone, Copy, PartialEq, Eq)]
//#[packed(repr = u64, discriminant(start = 0, len = 4))]
//pub enum Order {
//    #[variant(0)]
//    Market {
//        #[field(start = 4, len = 1)]
//        side: Side,
//        #[field(start = 5, len = 8)]
//        exchange: Exchange,
//        #[field(start = 16, len = 32)]
//        quantity: u32,
//    },
//    #[variant(1)]
//    Limit {
//        #[field(start = 4, len = 1)]
//        side: Side,
//        #[field(start = 5, len = 8)]
//        exchange: Exchange,
//        #[field(start = 16, len = 16)]
//        quantity: u16,
//        #[field(start = 32, len = 32)]
//        price: u32,
//    },
//}

//#[test]
//fn order_market() {
//    let e = Order::Market {
//        side: Side::Buy,
//        exchange: Exchange::Nasdaq,
//        quantity: 100,
//    };
//    let packed = e.pack().unwrap();
//    let unpacked = Order::unpack(packed).unwrap();
//    assert_eq!(unpacked, e);
//}

//#[test]
//fn order_limit() {
//    let e = Order::Limit {
//        side: Side::Sell,
//        exchange: Exchange::Cboe,
//        quantity: 500,
//        price: 10050,
//    };
//    let packed = e.pack().unwrap();
//    let unpacked = Order::unpack(packed).unwrap();
//    assert_eq!(unpacked, e);
//}

//// =============================================================================
//// Real-world: Instrument ID
//// =============================================================================

//#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
//#[repr(u8)]
//pub enum PutCall {
//    Call = 0,
//    Put = 1,
//}

//#[derive(BitPacked, Debug, Clone, Copy, PartialEq, Eq)]
//#[packed(repr = i64, discriminant(start = 0, len = 4))]
//pub enum InstrumentId {
//    #[variant(0)]
//    Equity {
//        #[field(start = 4, len = 8)]
//        exchange: Exchange,
//        #[field(start = 12, len = 20)]
//        symbol: u32,
//    },
//    #[variant(1)]
//    Future {
//        #[field(start = 4, len = 8)]
//        exchange: Exchange,
//        #[field(start = 12, len = 16)]
//        underlying: u16,
//        #[field(start = 28, len = 16)]
//        expiry: u16,
//    },
//    #[variant(2)]
//    Option {
//        #[field(start = 4, len = 8)]
//        exchange: Exchange,
//        #[field(start = 12, len = 16)]
//        underlying: u16,
//        #[field(start = 28, len = 16)]
//        expiry: u16,
//        #[field(start = 44, len = 16)]
//        strike: u16,
//        #[field(start = 60, len = 1)]
//        put_call: PutCall,
//    },
//}

//#[test]
//fn instrument_equity() {
//    let id = InstrumentId::Equity {
//        exchange: Exchange::Nyse,
//        symbol: 123456,
//    };
//    let packed = id.pack().unwrap();
//    let unpacked = InstrumentId::unpack(packed).unwrap();
//    assert_eq!(unpacked, id);
//}

//#[test]
//fn instrument_future() {
//    let id = InstrumentId::Future {
//        exchange: Exchange::Cboe,
//        underlying: 5000,
//        expiry: 2512,
//    };
//    let packed = id.pack().unwrap();
//    let unpacked = InstrumentId::unpack(packed).unwrap();
//    assert_eq!(unpacked, id);
//}

//#[test]
//fn instrument_option() {
//    let id = InstrumentId::Option {
//        exchange: Exchange::Nasdaq,
//        underlying: 1234,
//        expiry: 2506,
//        strike: 15000,
//        put_call: PutCall::Put,
//    };
//    let packed = id.pack().unwrap();
//    let unpacked = InstrumentId::unpack(packed).unwrap();
//    assert_eq!(unpacked, id);
//}

//#[test]
//fn instrument_all_variants_roundtrip() {
//    let variants = [
//        InstrumentId::Equity {
//            exchange: Exchange::Nasdaq,
//            symbol: 0,
//        },
//        InstrumentId::Equity {
//            exchange: Exchange::Nyse,
//            symbol: 0xFFFFF,
//        },
//        InstrumentId::Future {
//            exchange: Exchange::Cboe,
//            underlying: 0,
//            expiry: 0,
//        },
//        InstrumentId::Future {
//            exchange: Exchange::Nasdaq,
//            underlying: 0xFFFF,
//            expiry: 0xFFFF,
//        },
//        InstrumentId::Option {
//            exchange: Exchange::Nyse,
//            underlying: 1000,
//            expiry: 2512,
//            strike: 5000,
//            put_call: PutCall::Call,
//        },
//        InstrumentId::Option {
//            exchange: Exchange::Cboe,
//            underlying: 2000,
//            expiry: 2606,
//            strike: 10000,
//            put_call: PutCall::Put,
//        },
//    ];

//    for original in variants {
//        let packed = original.pack().unwrap();
//        let unpacked = InstrumentId::unpack(packed).unwrap();
//        assert_eq!(original, unpacked, "roundtrip failed for {:?}", original);
//    }
//}

//// =============================================================================
//// Overflow detection
//// =============================================================================

//#[derive(BitPacked, Debug, Clone, Copy, PartialEq, Eq)]
//#[packed(repr = u64, discriminant(start = 0, len = 4))]
//pub enum Narrow {
//    #[variant(0)]
//    Small {
//        #[field(start = 4, len = 4)]
//        value: u8, // u8 but only 4 bits
//    },
//}

//#[test]
//fn enum_field_overflow() {
//    let e = Narrow::Small { value: 16 }; // 16 > 15 (4-bit max)
//    let result = e.pack();
//    assert!(result.is_err());
//}

//// =============================================================================
//// Sparse discriminants
//// =============================================================================

//#[derive(BitPacked, Debug, Clone, Copy, PartialEq, Eq)]
//#[packed(repr = u64, discriminant(start = 0, len = 8))]
//pub enum Sparse {
//    #[variant(0)]
//    Zero,
//    #[variant(10)]
//    Ten {
//        #[field(start = 8, len = 8)]
//        value: u8,
//    },
//    #[variant(200)]
//    TwoHundred {
//        #[field(start = 8, len = 16)]
//        value: u16,
//    },
//}

//#[test]
//fn sparse_discriminants() {
//    let zero = Sparse::Zero;
//    let ten = Sparse::Ten { value: 42 };
//    let two_hundred = Sparse::TwoHundred { value: 1000 };

//    assert_eq!(Sparse::unpack(zero.pack().unwrap()).unwrap(), zero);
//    assert_eq!(Sparse::unpack(ten.pack().unwrap()).unwrap(), ten);
//    assert_eq!(
//        Sparse::unpack(two_hundred.pack().unwrap()).unwrap(),
//        two_hundred
//    );

//    // Values between defined discriminants should fail
//    let raw_5: u64 = 5;
//    assert!(Sparse::unpack(raw_5).is_err());
//}

//// =============================================================================
//// Different repr types
//// =============================================================================

//#[derive(BitPacked, Debug, Clone, Copy, PartialEq, Eq)]
//#[packed(repr = u8, discriminant(start = 0, len = 2))]
//pub enum TinyEnum {
//    #[variant(0)]
//    A {
//        #[field(start = 2, len = 6)]
//        value: u8,
//    },
//    #[variant(1)]
//    B {
//        #[flag(2)]
//        flag: bool,
//    },
//}

//#[test]
//fn tiny_enum_u8() {
//    let a = TinyEnum::A { value: 63 }; // max 6-bit
//    let b = TinyEnum::B { flag: true };

//    let packed_a = a.pack().unwrap();
//    let packed_b = b.pack().unwrap();

//    assert_eq!(packed_a, 0 | (63 << 2));
//    assert_eq!(packed_b, 1 | (1 << 2));

//    assert_eq!(TinyEnum::unpack(packed_a).unwrap(), a);
//    assert_eq!(TinyEnum::unpack(packed_b).unwrap(), b);
//}

//#[derive(BitPacked, Debug, Clone, Copy, PartialEq, Eq)]
//#[packed(repr = i32, discriminant(start = 0, len = 4))]
//pub enum SignedEnum {
//    #[variant(0)]
//    Positive {
//        #[field(start = 4, len = 16)]
//        value: u16,
//    },
//}

//#[test]
//fn signed_repr_enum() {
//    let e = SignedEnum::Positive { value: 12345 };
//    let packed: i32 = e.pack().unwrap();
//    let unpacked = SignedEnum::unpack(packed).unwrap();
//    assert_eq!(unpacked, e);
//}

//// =============================================================================
//// STRESS TEST - The Monster Enum
//// =============================================================================

//#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
//#[repr(u8)]
//pub enum StressSide {
//    Buy = 0,
//    Sell = 1,
//}

//#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
//#[repr(u8)]
//pub enum StressTif {
//    Day = 0,
//    Gtc = 1,
//    Ioc = 2,
//    Fok = 3,
//    Gtd = 4,
//    Opg = 5,
//    Cls = 6,
//    Ato = 7,
//}

//#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
//#[repr(u8)]
//pub enum StressVenue {
//    Nasdaq = 0,
//    Nyse = 1,
//    Arca = 2,
//    Bats = 3,
//    Iex = 4,
//    Edgx = 5,
//    Edga = 6,
//    Byx = 7,
//    Bzx = 8,
//    Memx = 9,
//    Ltse = 10,
//    Phlx = 11,
//    Amex = 12,
//    Cboe = 13,
//    C2 = 14,
//    Miax = 15,
//}

//#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
//#[repr(u8)]
//pub enum StressAsset {
//    Equity = 0,
//    Etf = 1,
//    Index = 2,
//    Future = 3,
//    Option = 4,
//    Forex = 5,
//    Crypto = 6,
//    Bond = 7,
//}

//#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
//#[repr(u8)]
//pub enum OneBit {
//    Zero = 0,
//    One = 1,
//}

//#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
//#[repr(u8)]
//pub enum TwoBit {
//    A = 0,
//    B = 1,
//    C = 2,
//    D = 3,
//}

///// The monster enum - 16 variants, mix of everything
//#[derive(BitPacked, Debug, Clone, Copy, PartialEq, Eq)]
//#[packed(repr = u128, discriminant(start = 0, len = 4))]
//pub enum Monster {
//    /// Empty variant
//    #[variant(0)]
//    Empty,

//    /// Just flags
//    #[variant(1)]
//    FlagsOnly {
//        #[flag(4)]
//        a: bool,
//        #[flag(5)]
//        b: bool,
//        #[flag(6)]
//        c: bool,
//        #[flag(7)]
//        d: bool,
//        #[flag(64)]
//        e: bool,
//        #[flag(127)]
//        f: bool,
//    },

//    /// Just one primitive
//    #[variant(2)]
//    SinglePrimitive {
//        #[field(start = 4, len = 64)]
//        big: u64,
//    },

//    /// Just one IntEnum
//    #[variant(3)]
//    SingleEnum {
//        #[field(start = 4, len = 4)]
//        venue: StressVenue,
//    },

//    /// Mix of primitives at weird offsets
//    #[variant(4)]
//    WeirdOffsets {
//        #[field(start = 4, len = 3)]
//        three_bits: u8,
//        #[field(start = 7, len = 5)]
//        five_bits: u8,
//        #[field(start = 12, len = 7)]
//        seven_bits: u8,
//        #[field(start = 19, len = 11)]
//        eleven_bits: u16,
//        #[field(start = 30, len = 13)]
//        thirteen_bits: u16,
//        #[field(start = 43, len = 17)]
//        seventeen_bits: u32,
//        #[field(start = 60, len = 19)]
//        nineteen_bits: u32,
//    },

//    /// Many IntEnums
//    #[variant(5)]
//    ManyEnums {
//        #[field(start = 4, len = 1)]
//        side: StressSide,
//        #[field(start = 5, len = 3)]
//        tif: StressTif,
//        #[field(start = 8, len = 4)]
//        venue: StressVenue,
//        #[field(start = 12, len = 3)]
//        asset: StressAsset,
//        #[field(start = 15, len = 1)]
//        bit1: OneBit,
//        #[field(start = 16, len = 2)]
//        bit2: TwoBit,
//    },

//    /// Mix of everything
//    #[variant(6)]
//    Kitchen {
//        #[field(start = 4, len = 1)]
//        side: StressSide,
//        #[flag(5)]
//        is_hidden: bool,
//        #[field(start = 6, len = 4)]
//        venue: StressVenue,
//        #[flag(10)]
//        is_routed: bool,
//        #[field(start = 11, len = 32)]
//        quantity: u32,
//        #[flag(43)]
//        is_test: bool,
//        #[field(start = 44, len = 20)]
//        symbol: u32,
//        #[field(start = 64, len = 48)]
//        price: u64,
//        #[flag(112)]
//        high_bit: bool,
//    },

//    /// Fields spanning byte boundaries
//    #[variant(7)]
//    ByteSpanners {
//        #[field(start = 4, len = 12)]
//        spans_0_1: u16,
//        #[field(start = 16, len = 24)]
//        spans_2_4: u32,
//        #[field(start = 40, len = 36)]
//        spans_5_9: u64,
//        #[field(start = 76, len = 44)]
//        spans_9_14: u64,
//    },

//    /// Maximum values for small widths
//    #[variant(8)]
//    MaxValues {
//        #[field(start = 4, len = 1)]
//        max1: u8,
//        #[field(start = 5, len = 2)]
//        max2: u8,
//        #[field(start = 7, len = 3)]
//        max3: u8,
//        #[field(start = 10, len = 4)]
//        max4: u8,
//        #[field(start = 14, len = 5)]
//        max5: u8,
//        #[field(start = 19, len = 6)]
//        max6: u8,
//        #[field(start = 25, len = 7)]
//        max7: u8,
//        #[field(start = 32, len = 8)]
//        max8: u8,
//    },

//    /// Sparse bit positions
//    #[variant(9)]
//    SparseBits {
//        #[flag(4)]
//        bit4: bool,
//        #[flag(16)]
//        bit16: bool,
//        #[flag(32)]
//        bit32: bool,
//        #[flag(48)]
//        bit48: bool,
//        #[flag(64)]
//        bit64: bool,
//        #[flag(80)]
//        bit80: bool,
//        #[flag(96)]
//        bit96: bool,
//        #[flag(112)]
//        bit112: bool,
//    },

//    /// High bits only
//    #[variant(10)]
//    HighBits {
//        #[field(start = 64, len = 32)]
//        upper_mid: u32,
//        #[field(start = 96, len = 31)]
//        upper: u32,
//    },

//    /// Single bit IntEnums packed tight
//    #[variant(11)]
//    TightEnums {
//        #[field(start = 4, len = 1)]
//        e0: OneBit,
//        #[field(start = 5, len = 1)]
//        e1: OneBit,
//        #[field(start = 6, len = 1)]
//        e2: OneBit,
//        #[field(start = 7, len = 1)]
//        e3: OneBit,
//        #[field(start = 8, len = 2)]
//        t0: TwoBit,
//        #[field(start = 10, len = 2)]
//        t1: TwoBit,
//        #[field(start = 12, len = 2)]
//        t2: TwoBit,
//        #[field(start = 14, len = 2)]
//        t3: TwoBit,
//    },

//    /// All zeros should work
//    #[variant(12)]
//    AllZeros {
//        #[field(start = 4, len = 32)]
//        zero1: u32,
//        #[field(start = 36, len = 32)]
//        zero2: u32,
//        #[flag(68)]
//        false_flag: bool,
//    },

//    /// Almost full 128 bits
//    #[variant(13)]
//    AlmostFull {
//        #[field(start = 4, len = 60)]
//        chunk1: u64,
//        #[field(start = 64, len = 63)]
//        chunk2: u64,
//    },

//    /// Discriminant at edge
//    #[variant(14)]
//    EdgeDiscriminant {
//        #[field(start = 4, len = 4)]
//        small: u8,
//    },

//    /// Max discriminant value (15 for 4-bit)
//    #[variant(15)]
//    MaxDiscriminant {
//        #[field(start = 4, len = 8)]
//        value: u8,
//        #[field(start = 12, len = 16)]
//        other: u16,
//    },
//}

//#[test]
//fn monster_empty() {
//    let m = Monster::Empty;
//    let packed = m.pack().unwrap();
//    assert_eq!(packed, 0u128);
//    assert_eq!(Monster::unpack(packed).unwrap(), m);
//}

//#[test]
//fn monster_flags_only() {
//    let m = Monster::FlagsOnly {
//        a: true,
//        b: false,
//        c: true,
//        d: false,
//        e: true,
//        f: true,
//    };
//    let packed = m.pack().unwrap();
//    assert_eq!(Monster::unpack(packed).unwrap(), m);

//    // Verify specific bits
//    assert_eq!(packed & (1 << 0), 1); // discriminant
//    assert_ne!(packed & (1 << 4), 0); // a
//    assert_eq!(packed & (1 << 5), 0); // b
//    assert_ne!(packed & (1 << 6), 0); // c
//    assert_eq!(packed & (1 << 7), 0); // d
//    assert_ne!(packed & (1 << 64), 0); // e
//    assert_ne!(packed & (1 << 127), 0); // f
//}

//#[test]
//fn monster_single_primitive() {
//    let m = Monster::SinglePrimitive {
//        big: 0xDEAD_BEEF_CAFE_BABE,
//    };
//    let packed = m.pack().unwrap();
//    assert_eq!(Monster::unpack(packed).unwrap(), m);
//}

//#[test]
//fn monster_single_enum() {
//    for venue in [
//        StressVenue::Nasdaq,
//        StressVenue::Nyse,
//        StressVenue::Memx,
//        StressVenue::Miax,
//    ] {
//        let m = Monster::SingleEnum { venue };
//        let packed = m.pack().unwrap();
//        assert_eq!(Monster::unpack(packed).unwrap(), m);
//    }
//}

//#[test]
//fn monster_weird_offsets() {
//    let m = Monster::WeirdOffsets {
//        three_bits: 7,       // max 3-bit
//        five_bits: 31,       // max 5-bit
//        seven_bits: 127,     // max 7-bit
//        eleven_bits: 2047,   // max 11-bit
//        thirteen_bits: 8191, // max 13-bit
//        seventeen_bits: (1 << 17) - 1,
//        nineteen_bits: (1 << 19) - 1,
//    };
//    let packed = m.pack().unwrap();
//    assert_eq!(Monster::unpack(packed).unwrap(), m);
//}

//#[test]
//fn monster_many_enums() {
//    let m = Monster::ManyEnums {
//        side: StressSide::Sell,
//        tif: StressTif::Fok,
//        venue: StressVenue::Cboe,
//        asset: StressAsset::Option,
//        bit1: OneBit::One,
//        bit2: TwoBit::C,
//    };
//    let packed = m.pack().unwrap();
//    assert_eq!(Monster::unpack(packed).unwrap(), m);
//}

//#[test]
//fn monster_kitchen_sink() {
//    let m = Monster::Kitchen {
//        side: StressSide::Buy,
//        is_hidden: true,
//        venue: StressVenue::Iex,
//        is_routed: false,
//        quantity: 1_000_000,
//        is_test: true,
//        symbol: 0xABCDE,
//        price: 0x1234_5678_9ABC,
//        high_bit: true,
//    };
//    let packed = m.pack().unwrap();
//    assert_eq!(Monster::unpack(packed).unwrap(), m);
//}

//#[test]
//fn monster_byte_spanners() {
//    let m = Monster::ByteSpanners {
//        spans_0_1: 0xFFF,
//        spans_2_4: 0xFF_FFFF,
//        spans_5_9: (1u64 << 36) - 1,
//        spans_9_14: (1u64 << 44) - 1,
//    };
//    let packed = m.pack().unwrap();
//    assert_eq!(Monster::unpack(packed).unwrap(), m);
//}

//#[test]
//fn monster_max_values() {
//    let m = Monster::MaxValues {
//        max1: 1,
//        max2: 3,
//        max3: 7,
//        max4: 15,
//        max5: 31,
//        max6: 63,
//        max7: 127,
//        max8: 255,
//    };
//    let packed = m.pack().unwrap();
//    assert_eq!(Monster::unpack(packed).unwrap(), m);
//}

//#[test]
//fn monster_sparse_bits_all_set() {
//    let m = Monster::SparseBits {
//        bit4: true,
//        bit16: true,
//        bit32: true,
//        bit48: true,
//        bit64: true,
//        bit80: true,
//        bit96: true,
//        bit112: true,
//    };
//    let packed = m.pack().unwrap();
//    assert_eq!(Monster::unpack(packed).unwrap(), m);
//}

//#[test]
//fn monster_sparse_bits_alternating() {
//    let m = Monster::SparseBits {
//        bit4: true,
//        bit16: false,
//        bit32: true,
//        bit48: false,
//        bit64: true,
//        bit80: false,
//        bit96: true,
//        bit112: false,
//    };
//    let packed = m.pack().unwrap();
//    assert_eq!(Monster::unpack(packed).unwrap(), m);
//}

//#[test]
//fn monster_high_bits() {
//    let m = Monster::HighBits {
//        upper_mid: 0xFFFF_FFFF,
//        upper: 0x7FFF_FFFF, // 31 bits max
//    };
//    let packed = m.pack().unwrap();
//    assert_eq!(Monster::unpack(packed).unwrap(), m);
//}

//#[test]
//fn monster_tight_enums() {
//    let m = Monster::TightEnums {
//        e0: OneBit::One,
//        e1: OneBit::Zero,
//        e2: OneBit::One,
//        e3: OneBit::Zero,
//        t0: TwoBit::A,
//        t1: TwoBit::B,
//        t2: TwoBit::C,
//        t3: TwoBit::D,
//    };
//    let packed = m.pack().unwrap();
//    assert_eq!(Monster::unpack(packed).unwrap(), m);
//}

//#[test]
//fn monster_all_zeros() {
//    let m = Monster::AllZeros {
//        zero1: 0,
//        zero2: 0,
//        false_flag: false,
//    };
//    let packed = m.pack().unwrap();
//    // Only discriminant should be set
//    assert_eq!(packed, 12u128);
//    assert_eq!(Monster::unpack(packed).unwrap(), m);
//}

//#[test]
//fn monster_almost_full() {
//    let m = Monster::AlmostFull {
//        chunk1: (1u64 << 60) - 1,
//        chunk2: (1u64 << 63) - 1,
//    };
//    let packed = m.pack().unwrap();
//    assert_eq!(Monster::unpack(packed).unwrap(), m);
//}

//#[test]
//fn monster_edge_discriminant() {
//    let m = Monster::EdgeDiscriminant { small: 15 };
//    let packed = m.pack().unwrap();
//    assert_eq!(Monster::unpack(packed).unwrap(), m);
//}

//#[test]
//fn monster_max_discriminant() {
//    let m = Monster::MaxDiscriminant {
//        value: 255,
//        other: 65535,
//    };
//    let packed = m.pack().unwrap();
//    // Discriminant should be 15 (0xF)
//    assert_eq!(packed & 0xF, 15);
//    assert_eq!(Monster::unpack(packed).unwrap(), m);
//}

//#[test]
//fn monster_all_variants_roundtrip() {
//    let variants: Vec<Monster> = vec![
//        Monster::Empty,
//        Monster::FlagsOnly {
//            a: true,
//            b: true,
//            c: true,
//            d: true,
//            e: true,
//            f: true,
//        },
//        Monster::SinglePrimitive { big: u64::MAX },
//        Monster::SingleEnum {
//            venue: StressVenue::Miax,
//        },
//        Monster::WeirdOffsets {
//            three_bits: 5,
//            five_bits: 20,
//            seven_bits: 100,
//            eleven_bits: 1500,
//            thirteen_bits: 7000,
//            seventeen_bits: 100000,
//            nineteen_bits: 400000,
//        },
//        Monster::ManyEnums {
//            side: StressSide::Buy,
//            tif: StressTif::Ato,
//            venue: StressVenue::Ltse,
//            asset: StressAsset::Crypto,
//            bit1: OneBit::Zero,
//            bit2: TwoBit::D,
//        },
//        Monster::Kitchen {
//            side: StressSide::Sell,
//            is_hidden: false,
//            venue: StressVenue::Memx,
//            is_routed: true,
//            quantity: 999999,
//            is_test: false,
//            symbol: 0x12345,
//            price: 0xABCD_EF01_2345,
//            high_bit: false,
//        },
//        Monster::ByteSpanners {
//            spans_0_1: 0x123,
//            spans_2_4: 0x456789,
//            spans_5_9: 0x1_2345_6789,
//            spans_9_14: 0xABC_DEF0_1234,
//        },
//        Monster::MaxValues {
//            max1: 1,
//            max2: 3,
//            max3: 7,
//            max4: 15,
//            max5: 31,
//            max6: 63,
//            max7: 127,
//            max8: 255,
//        },
//        Monster::SparseBits {
//            bit4: false,
//            bit16: true,
//            bit32: false,
//            bit48: true,
//            bit64: false,
//            bit80: true,
//            bit96: false,
//            bit112: true,
//        },
//        Monster::HighBits {
//            upper_mid: 0x1234_5678,
//            upper: 0x7ABC_DEF0,
//        },
//        Monster::TightEnums {
//            e0: OneBit::Zero,
//            e1: OneBit::One,
//            e2: OneBit::Zero,
//            e3: OneBit::One,
//            t0: TwoBit::D,
//            t1: TwoBit::C,
//            t2: TwoBit::B,
//            t3: TwoBit::A,
//        },
//        Monster::AllZeros {
//            zero1: 0,
//            zero2: 0,
//            false_flag: false,
//        },
//        Monster::AlmostFull {
//            chunk1: 0x0FFF_FFFF_FFFF_FFFF,
//            chunk2: 0x7FFF_FFFF_FFFF_FFFF,
//        },
//        Monster::EdgeDiscriminant { small: 0 },
//        Monster::MaxDiscriminant {
//            value: 128,
//            other: 32768,
//        },
//    ];

//    for (i, original) in variants.iter().enumerate() {
//        let packed = original.pack().unwrap();
//        let unpacked = Monster::unpack(packed).unwrap();
//        assert_eq!(
//            *original, unpacked,
//            "Variant {} failed roundtrip: {:?}",
//            i, original
//        );
//    }
//}

//#[test]
//fn monster_invalid_discriminants() {
//    // All values 0-15 are valid discriminants, so we can't test invalid
//    // But we can test that all 16 discriminants decode to the right variant
//    for disc in 0u128..16 {
//        let raw = disc; // Just the discriminant, no fields
//        let result = Monster::unpack(raw);
//        assert!(result.is_ok(), "Discriminant {} should be valid", disc);
//    }
//}
