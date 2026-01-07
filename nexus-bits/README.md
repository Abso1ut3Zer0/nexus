# nexus-bits

## Overview

nexus-bits provides derive macros for packing and unpacking integers as bit fields. Unlike other bitfield libraries that generate structs containing integers, nexus-bits generates newtypes that *are* the integer—ideal for wire protocols, database IDs, and trading systems where the packed integer is the canonical representation.

## Installation
```toml
[dependencies]
nexus-bits = "0.3"
```

## Features

- **Structs**: Flat bit-packed storage with builder pattern
- **Enums**: Tagged unions with discriminant and per-variant fields
- **IntEnum**: Simple integer-backed enums
- Compile-time validation (overlaps, bounds)
- Runtime overflow detection via `Result`
- Zero-cost `#[repr(transparent)]` newtypes
- Supports `u8`, `u16`, `u32`, `u64`, `u128` and signed variants

## Usage

### Structs

Pack multiple fields into a single integer:
```rust
use nexus_bits::bit_storage;

#[bit_storage(repr = u64)]
pub struct SnowflakeId {
    #[field(start = 0, len = 12)]
    sequence: u16,
    #[field(start = 12, len = 10)]
    worker: u16,
    #[field(start = 22, len = 42)]
    timestamp: u64,
}

// Build with validation
let id = SnowflakeId::builder()
    .sequence(100)
    .worker(5)
    .timestamp(1234567890)
    .build()?;

// Accessors
assert_eq!(id.sequence(), 100);
assert_eq!(id.worker(), 5);
assert_eq!(id.timestamp(), 1234567890);

// Wire conversion
let raw: u64 = id.raw();
let parsed = SnowflakeId::from_raw(raw);
```

### Flags

Single-bit boolean fields:
```rust
use nexus_bits::bit_storage;

#[bit_storage(repr = u8)]
pub struct OrderFlags {
    #[flag(0)]
    is_buy: bool,
    #[flag(1)]
    is_hidden: bool,
    #[flag(2)]
    is_post_only: bool,
    #[field(start = 4, len = 4)]
    priority: u8,
}

let flags = OrderFlags::builder()
    .is_buy(true)
    .is_hidden(false)
    .is_post_only(true)
    .priority(7)
    .build()?;

assert!(flags.is_buy());
assert!(!flags.is_hidden());
assert!(flags.is_post_only());
assert_eq!(flags.priority(), 7);
```

### IntEnum

Integer-backed enums for use in bit fields:
```rust
use nexus_bits::IntEnum;

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

// Use in bit_storage
#[bit_storage(repr = u32)]
pub struct OrderInfo {
    #[field(start = 0, len = 1)]
    side: Side,
    #[field(start = 1, len = 2)]
    tif: TimeInForce,
    #[field(start = 3, len = 16)]
    quantity: u16,
}

let order = OrderInfo::builder()
    .side(Side::Buy)
    .tif(TimeInForce::Ioc)
    .quantity(100)
    .build()?;

// IntEnum accessors return Result (discriminant might be invalid from wire)
assert_eq!(order.side()?, Side::Buy);
assert_eq!(order.tif()?, TimeInForce::Ioc);
assert_eq!(order.quantity(), 100);  // Primitives are infallible
```

### Tagged Enums

Different interpretations of the same bits based on a discriminant:
```rust
use nexus_bits::{bit_storage, IntEnum};

#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Exchange { Nasdaq = 0, Nyse = 1, Cboe = 2 }

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
        #[flag(60)]
        is_call: bool,
    },
}

// Build a variant
let equity = InstrumentId::equity()
    .exchange(Exchange::Nasdaq)
    .symbol(12345)
    .build()?;

// Variant accessors are infallible (pre-validated at build time)
assert_eq!(equity.exchange(), Exchange::Nasdaq);
assert_eq!(equity.symbol(), 12345);

// Convert to wire type
let wire: InstrumentId = equity.into();
let raw: i64 = wire.raw();

// Parse from wire and dispatch by kind
let parsed = InstrumentId::from_raw(raw);

// Check variant
assert!(parsed.is_equity());
assert!(!parsed.is_future());

// Match on kind
match parsed.kind()? {
    InstrumentIdKind::Equity => {
        let e = parsed.as_equity()?;
        println!("Equity symbol: {}", e.symbol());
    }
    InstrumentIdKind::Future => {
        let f = parsed.as_future()?;
        println!("Future expiry: {}", f.expiry());
    }
    InstrumentIdKind::Option => {
        let o = parsed.as_option()?;
        println!("Option strike: {}", o.strike());
    }
}
```

## Generated Types

### For Structs

Given `#[bit_storage(repr = u64)] struct Foo { ... }`:

| Type | Description |
|------|-------------|
| `Foo` | `#[repr(transparent)]` newtype with `from_raw()`, `raw()`, field accessors |
| `FooBuilder` | Builder with setters and `build() -> Result<Foo, FieldOverflow<u64>>` |

### For Enums

Given `#[bit_storage(repr = i64, discriminant(...))] enum Foo { Bar { ... }, Baz { ... } }`:

| Type | Description |
|------|-------------|
| `Foo` | Parent wire type with `from_raw()`, `raw()`, `kind()`, `is_*()`, `as_*()` |
| `FooBar` | Validated variant type with infallible accessors |
| `FooBaz` | Validated variant type with infallible accessors |
| `FooBarBuilder` | Builder with `build()` and `build_parent()` |
| `FooBazBuilder` | Builder with `build()` and `build_parent()` |
| `FooKind` | Discriminant enum (`FooKind::Bar`, `FooKind::Baz`) |

## Error Types
```rust
use nexus_bits::{FieldOverflow, UnknownDiscriminant, Overflow};

// Returned by builders when a value exceeds field capacity
let err: FieldOverflow<u64> = FieldOverflow {
    field: "sequence",
    overflow: Overflow { value: 5000, max: 4095 },
};

// Returned by kind() / as_*() for invalid discriminant or IntEnum
let err: UnknownDiscriminant<u64> = UnknownDiscriminant {
    field: "__discriminant",
    value: 0x1234567890,
};
```

## Compile-Time Validation

The macro rejects invalid configurations at compile time:

| Error | Example | Message |
|-------|---------|---------|
| Overlapping fields | Two fields both use bits 0-7 | "field 'b' overlaps with 'a'" |
| Field exceeds repr | 16-bit field at bit 60 in u64 | "field exceeds 64 bits (start 60 + len 16 = 76)" |
| Flag out of bounds | `#[flag(64)]` in u64 | "flag bit 64 exceeds 64 bits" |
| Zero-length field | `len = 0` | "len must be > 0" |
| Discriminant overflow | 4-bit discriminant with `#[variant(20)]` | "variant discriminant 20 exceeds max 15" |
| Duplicate discriminant | Two variants with `#[variant(0)]` | "duplicate discriminant 0: already used by 'Foo'" |
| Field overlaps discriminant | Field at bits 0-7, discriminant at bits 0-3 | "field 'x' overlaps with discriminant" |

Gaps between fields are allowed (reserved bits, padding).

## Comparison with Existing Libraries

| Feature | nexus-bits | modular-bitfield | bitfield-struct | packed_struct |
|---------|------------|------------------|-----------------|---------------|
| Flat structs | ✅ | ✅ | ✅ | ✅ |
| Tagged enums | ✅ | ❌ | ❌ | Partial |
| Validated variant types | ✅ | N/A | N/A | ❌ |
| IntEnum in fields | ✅ | ❌ | ❌ | ✅ |
| Builder pattern | ✅ | ❌ | ❌ | ❌ |
| Overflow detection | `Result` | Silent truncation | Silent truncation | Varies |
| Zero-cost newtype | ✅ | ❌ (generates struct) | ❌ | ❌ |

### When to use nexus-bits

**Wire protocols / message formats**: The integer IS the data. You receive an `i64` instrument ID over the wire and need to interpret its bits differently based on a discriminant.
```rust
// nexus-bits: the i64 is your type
let id = InstrumentId::from_raw(wire_value);
match id.kind()? { ... }

// Other libraries: wrapper around storage
let id = InstrumentId::from_bytes(&wire_value.to_le_bytes());
```

**Trading systems**: Packing order flags, instrument IDs, snowflake IDs where:
- Stable integer representation matters for databases/serialization
- Sub-microsecond parsing overhead matters
- Tagged unions distinguish asset classes, order types, etc.

**ID generation**: Snowflake-style IDs where you pack timestamp, worker, sequence into a single integer and need both packing and unpacking.

### When to use alternatives

**modular-bitfield**: Hardware registers, memory-mapped I/O where you're manipulating a struct in place and don't need tagged unions.

**bitvec**: Arbitrary-length bit arrays, bit-level slicing, when you need more than 128 bits.

**packed_struct**: Byte-oriented serialization with endianness control, protocol buffers style packing.

### Design Philosophy

Most bitfield libraries generate a struct that *contains* an integer:
```rust
// modular-bitfield style
#[bitfield]
struct Flags {
    a: B4,
    b: B4,
}
let f = Flags::new().with_a(1).with_b(2);
let raw: u8 = f.into_bytes()[0];  // Extract the integer
```

nexus-bits generates a newtype that *is* the integer:
```rust
// nexus-bits style
#[bit_storage(repr = u8)]
struct Flags {
    #[field(start = 0, len = 4)] a: u8,
    #[field(start = 4, len = 4)] b: u8,
}
let f = Flags::builder().a(1).b(2).build()?;
let raw: u8 = f.raw();            // It's already the integer
let f2 = Flags::from_raw(raw);    // Zero-cost conversion
```

This matters when your domain *thinks* in integers—database columns, wire protocols, hash keys—rather than structured data that happens to be packed.

## Minimum Supported Rust Version

This crate requires Rust 1.70 or later.

## License

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or <http://www.apache.org/licenses/LICENSE-2.0>)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

at your option.

## Contributing

Contributions are welcome! Please feel free to submit a Pull Request.

## Related Crates

- [nexus-queue](https://crates.io/crates/nexus-queue) - High-performance SPSC queue
- [nexus-channel](https://crates.io/crates/nexus-channel) - Lock-free SPSC channel
- [nexus-slot](https://crates.io/crates/nexus-slot) - Single-value container
- [nexus-slab](https://crates.io/crates/nexus-slab) - Pre-allocated object pool
