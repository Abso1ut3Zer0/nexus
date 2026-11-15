# nexus-decimal

Fixed-point decimal arithmetic with compile-time precision.

`Decimal<B, DECIMALS>` is a generic fixed-point type parameterized by backing
integer and decimal places. Operations are `const fn` where possible,
zero-allocation, and designed for financial workloads.

## Quick Start

```rust
use nexus_decimal::Decimal;
use core::str::FromStr;

type D64 = Decimal<i64, 8>;

let price = D64::from_str("123.45").unwrap();
let qty = D64::from_i32(10).unwrap();

let notional = price * qty;
assert_eq!(notional.to_string(), "1234.5");
```

## Choosing Your Type

Define type aliases that match your domain:

```rust
use nexus_decimal::Decimal;

type Price = Decimal<i64, 8>;          // 8dp, range ±92B — traditional finance
type Quantity = Decimal<i64, 4>;       // 4dp, range ±922T
type CryptoPrice = Decimal<i128, 12>; // 12dp, range ±39T — DeFi
type Usd = Decimal<i64, 2>;           // 2dp cents
```

| Backing | Max Decimals | Use case |
|---------|-------------|----------|
| `i32` | 9 | Embedded, space-constrained |
| `i64` | 18 | Traditional finance |
| `i128` | 38 | Cryptocurrency, DeFi |

## Features

- **Compile-time constants** — `const fn` constructors and checked arithmetic
- **Zero allocation** — all operations are stack-based
- **Checked, saturating, and wrapping** arithmetic variants
- **Parsing** — `FromStr` with strict validation
- **Display** — configurable precision, scientific notation
- **Serialization** — optional `serde` support

## Wide Division (i128)

For i128 backing types, multiplication of two `Decimal<i128, D>` values requires 256-bit intermediate results. nexus-decimal uses Knuth Algorithm D (TAOCP Vol 2, Section 4.3.1) for correct 256/128-bit wide division, avoiding the need for compiler-provided `__divti3` or external bignum libraries. This enables high-precision financial math (up to 38 decimal places) with correct rounding.

## Feature Flags

| Flag | Default | Description |
|------|---------|-------------|
| `std` | yes | Standard library support |
| `serde` | no | Serialize/deserialize support |
| `num-traits` | no | `num-traits` trait implementations |

## License

See [LICENSE-APACHE](../LICENSE-APACHE) or [LICENSE-MIT](../LICENSE-MIT).
