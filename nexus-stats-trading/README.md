# nexus-stats-trading

Trading and market-microstructure statistics for [nexus-stats](https://crates.io/crates/nexus-stats).

Streaming measures of how a market is behaving, each fed one price, return or trade at a time in fixed memory. Every type follows its published definition, and is checked against a reference implementation where one exists.

This is not a technical-analysis library: there are no chart indicators here. It covers what a trading system needs to measure, market microstructure included.

## Which type do I use?

**Is the price trending or reverting?**

- **VarianceRatio**: Lo and MacKinlay's ratio, with a test statistic that says whether the departure from a random walk could be chance (requires `alloc` + (`std` or `libm`))

**How volatile is it?**

- **TwoScaleRv**: realized variance from tick data, with the noise of bid-ask bounce taken out (requires `alloc` + (`std` or `libm`))
- **BipowerVariation**: realized variance split into a continuous part and a jump part (requires `std` or `libm`)

**What does it cost to trade?**

- **Amihud**: illiquidity, the price move per unit traded
- **RollSpread**: the effective spread, from trade prices alone (requires `std` or `libm`)
- **KyleLambda**: price impact per unit of signed volume (requires the `regression` feature, on by default)

**How much risk is in the tail?**

- **Lpm**: lower partial moments, such as semivariance
- **Cvar**: conditional value at risk, the expected loss beyond a quantile

Each type's docs give its definition, how to read it, and an example.

## Example

```rust
use nexus_stats_trading::{Accuracy, VarianceRatio};

// Compare 5-period with 1-period variance over the last 200 returns.
let mut vr = VarianceRatio::builder().horizon(5).window(200).build().unwrap();

let mut price = 100.0_f64;
for i in 0..500_i32 {
    price *= 1.0 + 0.001 * f64::from(i % 7 - 3);
    // `update` says when rounding in its running totals needs clearing.
    // Until `resync` is called there is no reading.
    if let Accuracy::ResyncRequired { .. } = vr.update(price) {
        vr.resync(); // costs the window: schedule it off the hot path
    }
}

if let Some(estimate) = vr.estimate() {
    // A ratio near 1 is a random walk. `|z|` above about 2 says the
    // departure is unlikely to be chance.
    println!("ratio {:.3}, z {:.2}", estimate.ratio, estimate.z_statistic);
}
```

## Features

| Feature | Default | Enables |
|---------|---------|---------|
| `std` | yes | `sqrt` and `ln` from the standard library; implies `alloc` |
| `alloc` | no (implied by `std`) | the windowed types, `VarianceRatio` and `TwoScaleRv` (with `std` or `libm`) |
| `libm` | no | pure Rust `sqrt` and `ln` for `no_std` |
| `regression` | yes | `KyleLambda`, and with it the `nexus-stats-regression` crate |

`Accuracy`, `ConfigError` and `DataError` are re-exported, so this crate can be used without depending on `nexus-stats-core` directly.

## Usage

Enable the `trading` feature on `nexus-stats` for unified import paths:

```rust,ignore
use nexus_stats::trading::VarianceRatio;
```

Or depend on this crate directly:

```rust
use nexus_stats_trading::VarianceRatio;
```

## License

Licensed under either of [Apache License, Version 2.0](../LICENSE-APACHE) or
[MIT license](../LICENSE-MIT) at your option.
