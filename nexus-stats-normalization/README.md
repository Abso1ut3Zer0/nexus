# nexus-stats-normalization

Normalizers for [nexus-stats](https://crates.io/crates/nexus-stats): each puts a stream on a common scale, one sample at a time in fixed memory.

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
