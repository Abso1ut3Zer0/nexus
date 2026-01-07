# nexus-bits

Bit field packing for integer IDs.

`nexus-bits` provides ergonomic bit field manipulation for packing multiple values into integers — common in trading systems for instrument IDs, order IDs, and wire protocols.

## Why nexus-bits?

Several excellent bitfield crates exist (`bitfield-struct`, `modular-bitfield`, `bitfield`). `nexus-bits` targets a different use case:

| Feature | nexus-bits | Others |
|---------|------------|--------|
| **Bit positions** | Explicit `#[field(start = 4, len = 8)]` | Auto-sequential |
| **Storage** | Pack to/from raw integers (`u64`, `i64`) | Wrapped in struct |
| **Overflow** | `Result<T, FieldOverflow>` | Silent truncation |
| **Tagged enums** | Discriminant-based variant layouts | Not supported |

**When to use nexus-bits:**

- Matching existing wire formats or ID schemes with specific bit layouts
- Working with IDs that must be plain integers (database keys, protocol fields)
- Trading systems where silent truncation is unacceptable
- Packing different data into the same integer based on a discriminant

**When to use other crates:**

- Auto-layouting fields sequentially is fine
- You want the bitfield wrapped in a type (not a raw integer)
- Truncation on overflow is acceptable

## Features

- **`BitField<T>`** — Extract and set multi-bit fields at arbitrary positions
- **`Flag<T>`** — Single-bit boolean flags
- **`IntEnum`** — Derive macro for `#[repr(u8)]` enums to convert to/from integers
- **`BitPacked`** — Derive macro for structs with automatic pack/unpack generation
- **`no_std`** compatible
- **Compile-time validation** — Field overlap and bounds checking at compile time
- **Runtime overflow detection** — Returns `Result` on pack if values exceed field capacity

## Usage

### Manual bit field manipulation
```rust
use nexus_bits::{BitField, Flag};

const KIND: BitField<u64> = BitField::<u64>::new(0, 4);
const EXCHANGE: BitField<u64> = BitField::<u64>::new(4, 8);
const SYMBOL: BitField<u64> = BitField::<u64>::new(12, 20);
const IS_TEST: Flag<u64> = Flag::<u64>::new(63);

// Pack
let mut id: u64 = 0;
id = KIND.set(id, 1).unwrap();
id = EXCHANGE.set(id, 5).unwrap();
id = SYMBOL.set(id, 12345).unwrap();
id = IS_TEST.set(id);

// Unpack
assert_eq!(KIND.get(id), 1);
assert_eq!(EXCHANGE.get(id), 5);
assert_eq!(SYMBOL.get(id), 12345);
assert!(IS_TEST.is_set(id));
```

### Derive macros (recommended)
```rust
use nexus_bits::{BitPacked, IntEnum};

#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Exchange {
    Nasdaq = 0,
    Nyse = 1,
    Cboe = 2,
}

#[derive(BitPacked, Debug, Clone, Copy, PartialEq, Eq)]
#[packed(repr = u64)]
pub struct InstrumentId {
    #[field(start = 0, len = 4)]
    kind: u8,
    #[field(start = 4, len = 8)]
    exchange: Exchange,
    #[field(start = 12, len = 20)]
    symbol: u32,
    #[flag(63)]
    is_test: bool,
}

let id = InstrumentId {
    kind: 2,
    exchange: Exchange::Cboe,
    symbol: 123456,
    is_test: true,
};

// Pack to integer
let packed: u64 = id.pack().unwrap();

// Unpack from integer
let unpacked = InstrumentId::unpack(packed).unwrap();
assert_eq!(id, unpacked);
```

### Snowflake-style IDs
```rust
use nexus_bits::BitPacked;

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
```

## Error Handling

**Pack** returns `Result<T, FieldOverflow<T>>` if a value exceeds its field capacity:
```rust
let id = InstrumentId {
    kind: 255,  // Exceeds 4-bit field (max 15)
    ..
};
assert!(id.pack().is_err());
```

**Unpack** for structs with `IntEnum` fields returns `Result<Self, UnknownDiscriminant<T>>`:
```rust
let raw: u64 = 0xFF;  // Invalid exchange value
let result = InstrumentId::unpack(raw);
assert!(result.is_err());
```

Structs with only primitive fields have infallible unpack returning `Self` directly.

## Features

| Feature | Default | Description |
|---------|---------|-------------|
| `derive` | Yes | Enables `#[derive(BitPacked)]` and `#[derive(IntEnum)]` |

Disable derive macros for a minimal `no_std` build:
```toml
[dependencies]
nexus-bits = { version = "0.1", default-features = false }
```

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or [MIT license](LICENSE-MIT) at your option.
