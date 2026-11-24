# nexus-stats-normalization

Normalizers for [nexus-stats](https://crates.io/crates/nexus-stats): each puts a stream on a common scale, one sample at a time in fixed memory.

## Guarantees

- **Fixed memory.** A type allocates only when it is built. `update` never allocates.
- **Configuration is checked once, when the type is built,** and reported as a `ConfigError`.
- **`update` does the arithmetic and nothing else.** No validation, no `Result`. Floats follow IEEE 754, as `+` does. After an input the type cannot use, it promises nothing unless its docs say otherwise.
- **`checked_update` protects the state.** A type has one when some input does damage that outlasts the sample, or when `update` drops a sample you should be told about (a NaN it ignores, a timestamp that goes back). It refuses exactly those inputs, its docs list them, and a refusal leaves the type unchanged. A type without one has no such input.
- **A reader reports what the arithmetic gives,** NaN included where the true answer is undefined. It never substitutes a number. The library protects the state. It does not promise a reading is never NaN.
- **A reading is an `Option`.** `None` until there is enough data, never a placeholder value.
- **A published algorithm is implemented as published.** A type that comes from a paper or a standard follows it. Where floating point needs more care than the source gives (cancellation, overflow, a divisor near zero), the type adds the guard practitioners use, and its docs say which.

**Not yet migrated:** `MinMaxNorm`, `QuantileNorm`. They have not been moved to these guarantees. Most still validate in `update` and return a `Result`.

## Which type do I use?

- **ZScoreNorm**: how many standard deviations a sample is from the recent mean. Not bounded, so it also serves as an outlier score (requires `std` or `libm`)
- **MinMaxNorm**: where a sample sits between the recent minimum and maximum, from 0 to 1
- **QuantileNorm**: a sample's rank among those seen, from 0 to 1, whatever the shape of the distribution (requires `alloc`)

Each type's docs give its definition, how to read it, and an example.

## Example

```rust
use nexus_stats_normalization::ZScoreNorm;

let mut zs = ZScoreNorm::<f64>::builder().span(20).build().unwrap();
for i in 0..100 {
    zs.update(100.0 + f64::from(i % 5));
}
// In-range samples score small; an outlier is not capped.
assert!(zs.normalize(102.0).unwrap().abs() < 1.0);
assert!(zs.update(1_000.0).unwrap() > 100.0);
```

## Features

| Feature | Default | Enables |
|---------|---------|---------|
| `std` | yes | `sqrt` from the standard library, for `ZScoreNorm`; implies `alloc` |
| `alloc` | no (implied by `std`) | `QuantileNorm` |
| `libm` | no | pure Rust `sqrt` for `no_std` |

`ConfigError`, `DataError` and `Float` are re-exported, so this crate can be used without depending on `nexus-stats-core` directly.

## Usage

Enable the `normalization` feature on `nexus-stats` for unified import paths:

```rust,ignore
use nexus_stats::normalization::ZScoreNorm;
```

Or depend on this crate directly:

```rust
use nexus_stats_normalization::ZScoreNorm;
```

## License

Licensed under either of [Apache License, Version 2.0](../LICENSE-APACHE) or
[MIT license](../LICENSE-MIT) at your option.
