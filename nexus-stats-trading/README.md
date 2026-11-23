# nexus-stats-trading

Trading and market-microstructure statistics for [nexus-stats](https://crates.io/crates/nexus-stats).

This is not a technical-analysis library: there are no chart indicators here. It covers what a trading system needs to measure, market microstructure included.

## Types

- **VarianceRatio**: Lo and MacKinlay's variance ratio and test statistic (requires `alloc` + (`std` or `libm`))
- **TwoScaleRv**: realized variance with tick noise taken out (requires `alloc` + (`std` or `libm`))
- **BipowerVariation**: realized variance split into a continuous part and jumps (requires `std` or `libm`)
- **Amihud**: illiquidity, the price move per unit traded
- **RollSpread**: the effective spread, from trade prices alone (requires `std` or `libm`)
- **KyleLambda**: price impact per unit of signed volume (requires the `regression` feature, on by default)
- **Lpm**: lower partial moments, such as semivariance
- **Cvar**: conditional value at risk (expected shortfall)

The crate docs say which type to use for what.

## Usage

Enable the `trading` feature on `nexus-stats` for unified import paths:

```rust
use nexus_stats::trading::VarianceRatio;
```

Or depend on this crate directly:

```rust
use nexus_stats_trading::VarianceRatio;
```

## License

Licensed under either of [Apache License, Version 2.0](../LICENSE-APACHE) or
[MIT license](../LICENSE-MIT) at your option.
