# nexus-stats-control

Advanced control and frequency primitives for [nexus-stats](https://crates.io/crates/nexus-stats).

## Control Types

- **PeakDetector<f64>** — Peak detection with hysteresis
- **BoolWindow** — Sliding boolean window with bit-packed storage (requires `alloc`)

## Frequency Types

- **TopK** — Top-K frequency tracking
- **FlexProportion** — Flexible proportion tracking
- **DecayAccum** — Exponential decay accumulator, `u64` ticks (requires `std` or `libm`)

## Usage

Enable the `control` feature on `nexus-stats` for unified import paths:

```rust
use nexus_stats::control::PeakDetector;
use nexus_stats::frequency::TopK;
```

## License

Licensed under either of [Apache License, Version 2.0](../LICENSE-APACHE) or
[MIT license](../LICENSE-MIT) at your option.
