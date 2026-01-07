# nexus-bits

Ergonomic bit-field packing for Rust. Zero-cost newtypes with type-safe accessors.

## Features

- **Structs**: Flat bit-packed storage with builder pattern
- **Enums**: Tagged unions with discriminant and per-variant fields
- **IntEnum**: Simple integer-backed enums
- Compile-time validation (overlaps, bounds)
- Runtime overflow detection via `Result`

## Usage

### Structs
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

let id = SnowflakeId::builder()
    .sequence(100)
    .worker(5)
    .timestamp(1234567890)
    .build()?;

assert_eq!(id.sequence(), 100);
assert_eq!(id.raw(), /* packed u64 */);
```

### Tagged Enums
```rust
use nexus_bits::{bit_storage, IntEnum};

#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Exchange { Nasdaq = 0, Nyse = 1 }

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
    Option {
        #[field(start = 4, len = 8)]
        exchange: Exchange,
        #[field(start = 12, len = 32)]
        underlying: u32,
        #[field(start = 44, len = 16)]
        strike: u16,
    },
}

// Build variant
let equity = InstrumentId::equity()
    .exchange(Exchange::Nasdaq)
    .symbol(12345)
    .build()?;

// Variant accessors are infallible (pre-validated)
assert_eq!(equity.exchange(), Exchange::Nasdaq);
assert_eq!(equity.symbol(), 12345);

// Convert to wire type
let wire: InstrumentId = equity.into();

// Parse from wire
let parsed = InstrumentId::from_raw(wire.raw());
match parsed.kind()? {
    InstrumentIdKind::Equity => {
        let e = parsed.as_equity()?;
        println!("symbol: {}", e.symbol());
    }
    InstrumentIdKind::Option => { /* ... */ }
}
```

### IntEnum
```rust
use nexus_bits::IntEnum;

#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Side {
    Buy = 0,
    Sell = 1,
}

let side = Side::Buy;
let repr: u8 = side.into_repr();
let back: Option<Side> = Side::try_from_repr(repr);
```

## Generated Types

### For Structs
- `Foo` - newtype wrapper with `from_raw()`, `raw()`, accessors
- `FooBuilder` - builder with setters and `build() -> Result<Foo, FieldOverflow>`

### For Enums
- `Foo` - parent wire type with `from_raw()`, `raw()`, `kind()`, `is_*()`, `as_*()`, builder shortcuts
- `FooVariant` - validated variant type with infallible accessors
- `FooVariantBuilder` - builder with `build()` and `build_parent()`
- `FooKind` - discriminant enum for matching

## Error Types

- `FieldOverflow<T>` - value exceeds field bit width
- `UnknownDiscriminant<T>` - invalid discriminant or IntEnum value

## Compile-Time Validation

The macro rejects:
- Overlapping fields
- Fields exceeding repr bounds
- Discriminant conflicts
- Invalid bit ranges
