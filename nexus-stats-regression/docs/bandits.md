# Multi-Armed Bandits

Sequential decision algorithms that balance exploration (trying uncertain
options) with exploitation (using the best-known option). All five types
live in `nexus_stats::learning` (requires `regression` feature) or
`nexus_stats_regression::learning`.

Feature gate: `alloc` + (`std` or `libm`).

---

## What bandits solve

You have K options (arms) and must choose one on each round. After
choosing, you observe a reward. The goal: maximize cumulative reward
over time by learning which arms are best while not spending too many
rounds on bad arms.

The core tension is explore vs exploit. Pure exploitation locks onto
whatever looked best early and misses better options. Pure exploration
gathers information but never uses it. Bandits formalize the tradeoff
with provable regret bounds.

Trading examples: which exchange fills fastest, which spread parameter
yields the best P&L, which order size captures the most edge. The
environment is often non-stationary — venue performance shifts, market
regimes change, competitors adapt. Four types (UCB1, ThompsonBeta,
ThompsonGamma, EpsilonGreedy) support exponential discounting via
the `decay` builder parameter. EXP3 handles non-stationarity through
its `gamma` exploration mixing rate.

---

## When to use what

| Your situation | Use | Why |
|----------------|-----|-----|
| Binary outcome (fill / no fill) | `ThompsonBetaF64` | Natural conjugate for Bernoulli rewards. Explores proportional to uncertainty. |
| Positive continuous reward (latency, P&L) | `ThompsonGammaF64` | Gamma prior handles unbounded positive rewards. Posterior mean tracks sample mean. |
| Bounded reward, want deterministic selection | `Ucb1F64` | No RNG needed. Deterministic upper confidence bound. Good for auditing. |
| Want the simplest possible thing | `EpsilonGreedyF64` | One parameter (ε). Easy to reason about. Good baseline. |
| Adversarial environment (competitors adapt) | `Exp3F64` | No stochastic assumption. Robust when reward distributions shift arbitrarily. |
| Need to explain decisions to compliance | `Ucb1F64` | Deterministic: same state always selects the same arm. Auditable. |
| Few arms (2-5), fast convergence matters | `ThompsonBetaF64` / `ThompsonGammaF64` | Thompson converges faster than UCB1 empirically, especially for few arms. |
| Many arms (50+), concerned about cost | `EpsilonGreedyF64` | O(K) select is cheap. ε controls exploration budget directly. |

### Decision tree

```
Is the reward binary (success/failure)?
├─ Yes → ThompsonBetaF64
└─ No → Is the reward always positive?
    ├─ Yes → ThompsonGammaF64
    └─ No → Can you normalize to [0, 1]?
        ├─ Yes, and you want deterministic → Ucb1F64
        ├─ Yes, and environment is adversarial → Exp3F64
        └─ Yes, and you want simplicity → EpsilonGreedyF64
```

---

## Discounting and non-stationarity

Four types (UCB1, ThompsonBeta, ThompsonGamma, EpsilonGreedy) support
`decay` in the builder. Default is `1.0` (stationary — all observations
weighted equally). Set `decay < 1.0` to exponentially discount old
observations. EXP3 handles non-stationarity differently — its `gamma`
parameter controls exploration mixing, ensuring continued exploration
without explicit discounting.

### Why discount

A stationary bandit converges to the best arm and stays there. If
the best arm changes (venue latency degrades, competitor enters a
market, regime shifts), the bandit has accumulated so much evidence
for the old best that it takes an unreasonable number of rounds to
switch. This is the "converge fast then become wrong fast" failure
mode.

With `decay = 0.99`, each observation's effective weight halves
every ~69 rounds (`ln(2) / ln(1/0.99) ≈ 69`). With `decay = 0.95`,
the half-life is ~14 rounds.

### Choosing a decay value

| Regime change speed | Decay | Half-life |
|---------------------|-------|-----------|
| Slow (daily) | 0.999 | ~693 rounds |
| Moderate (hourly) | 0.99 | ~69 rounds |
| Fast (minutes) | 0.95 | ~14 rounds |
| Very fast | 0.9 | ~7 rounds |

Start with `0.99` and tune based on how quickly your environment
changes. Too aggressive (low decay) and the bandit never converges.
Too conservative (high decay) and it can't track shifts.

### How it works internally

Before each `update()`, all per-arm statistics are multiplied by
`decay`. For UCB1 and EpsilonGreedy, this means counts and reward
sums shrink. For Thompson variants, the prior parameters (α/β or
shape/rate) shrink toward zero, widening the posterior and
encouraging re-exploration of arms that haven't been pulled recently.

EXP3 does not use `decay`. Its exploration is governed by `gamma`,
which mixes uniform exploration into every selection. This provides
inherent adaptivity without discounting — the multiplicative weight
updates naturally track shifting reward distributions.

---

## Reward normalization

The caller is responsible for normalizing rewards before feeding
them to the bandit. Each algorithm has different requirements:

| Algorithm | Valid rewards | Notes |
|-----------|-------------|-------|
| `Ucb1F64` | Any finite value | Regret bound assumes [0,1]. Scale `c` if using wider range. |
| `ThompsonBetaF64` | [0, 1] | Returns `DataError` outside this range. |
| `ThompsonGammaF64` | (0, ∞) | Returns `DataError` for zero or negative. |
| `EpsilonGreedyF64` | Any finite value | No range assumption. |
| `Exp3F64` | [0, 1] | Returns `DataError` outside this range. |

### Normalization strategies

**Z-score normalization** (for UCB1, EpsilonGreedy):
Track a running `Welford` on raw rewards. Normalize as
`(reward - mean) / std_dev`, then shift to [0,1] if needed.

**Min-max normalization** (for Exp3):
`(reward - min) / (max - min)`. Use `RunningMin<f64>` /
`RunningMax<f64>` from nexus-stats monitoring, or windowed variants
for non-stationary data.

**Natural [0,1] rewards** (for ThompsonBeta):
Fill rates, success rates, and binary outcomes are already in range.

**Positive rewards** (for ThompsonGamma):
Latency inverse (1/latency_us), P&L per unit risk, fill quality
scores. If your reward can be zero, add a small epsilon or use
a different algorithm.

---

## Code examples

### Venue selection with Thompson Beta

Four exchanges, binary fill/no-fill outcome. Non-stationary because
venue performance shifts with market conditions.

```rust
use nexus_stats_regression::learning::ThompsonBetaF64;

let mut venue_bandit = ThompsonBetaF64::builder()
    .arms(4)               // 4 exchanges
    .decay(0.99)           // half-life ~69 orders
    .build()
    .unwrap();

// Your RNG source (any closure returning uniform [0, 1))
let mut rng_state: u64 = 12345;
let mut rng = || -> f64 {
    // xorshift64 for illustration — use a proper RNG in production
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    (rng_state >> 11) as f64 / (1u64 << 53) as f64
};

// On each order:
let venue = venue_bandit.select(&mut rng);
// ... send order to venue[venue] ...
// ... observe fill (1.0) or no fill (0.0) ...
let filled = 1.0_f64;
venue_bandit.update(venue, filled).unwrap();

// After warmup, check which venue is winning:
for i in 0..4 {
    let fill_rate = venue_bandit.mean_reward(i);
    // fill_rate = alpha / (alpha + beta), the posterior mean
}
```

### Parameter A/B with UCB1

Two spread parameters, reward = normalized P&L per trade.
Deterministic selection for auditability.

```rust
use nexus_stats_regression::learning::Ucb1F64;
use nexus_stats::statistics::Welford;

let mut spread_bandit = Ucb1F64::builder()
    .arms(2)               // 2 spread settings
    .exploration(1.0)      // slightly less than default sqrt(2)
    .decay(0.995)          // slow decay, spreads are stable
    .build()
    .unwrap();

// Normalize rewards with running stats
let mut reward_stats = Welford::new();

// On each trade:
let spread_idx = spread_bandit.select();
// ... use spread_settings[spread_idx] ...
// ... observe P&L ...
let pnl = 0.5_f64;

// Normalize to roughly [0,1]
reward_stats.update(pnl);
let normalized = if let (Some(mean), Some(std)) =
    (reward_stats.mean(), reward_stats.std_dev())
{
    if std > 0.0 { ((pnl - mean) / (4.0 * std) + 0.5).clamp(0.0, 1.0) }
    else { 0.5 }
} else { 0.5 };

spread_bandit.update(spread_idx, normalized).unwrap();
```

### Adversarial setting with EXP3

Market adapts to your strategy. Reward distributions shift
unpredictably. EXP3 provides worst-case guarantees.

```rust
use nexus_stats_regression::learning::Exp3F64;

let mut strategy_bandit = Exp3F64::builder()
    .arms(3)               // 3 strategy variants
    .gamma(0.2)            // 20% exploration mixing
    .build()
    .unwrap();

let mut rng_state: u64 = 42;
let mut rng = || -> f64 {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    (rng_state >> 11) as f64 / (1u64 << 53) as f64
};

// EXP3 returns both the arm and the selection probability
let (strategy, prob) = strategy_bandit.select(&mut rng);
// ... execute strategy[strategy] ...
// ... observe reward in [0, 1] ...
let reward = 0.7_f64;

// Must pass prob back — EXP3 uses importance weighting
strategy_bandit.update(strategy, reward, prob).unwrap();

// Inspect current probability distribution
let mut probs = vec![0.0_f64; 3];
strategy_bandit.probabilities(&mut probs);
// probs[i] shows how much weight each strategy has
```

---

## API summary

All types share a common pattern:

| Method | UCB1 | ThompsonBeta | ThompsonGamma | EpsilonGreedy | EXP3 |
|--------|------|-------------|--------------|--------------|------|
| `select` | `-> usize` | `(rng) -> usize` | `(rng) -> usize` | `(rng) -> usize` | `(rng) -> (usize, prob)` |
| `update` | `(arm, reward)` | `(arm, reward)` | `(arm, reward)` | `(arm, reward)` | `(arm, reward, prob)` |
| `mean_reward` | `Option<f64>` | `f64` | `f64` | `Option<f64>` | — |
| `is_primed` | yes | yes | yes | yes | yes |
| `reset` | yes | yes | yes | yes | yes |
| `num_arms` | yes | yes | yes | yes | yes |
| `total_pulls` | yes | yes | yes | yes | yes |

UCB1 is the only type that doesn't need an RNG for selection.

Thompson `mean_reward` always returns a value (prior provides a
baseline). UCB1 and EpsilonGreedy return `None` for unpulled arms.

EXP3 doesn't track per-arm means — it maintains weights. Use
`probabilities()` to see the current distribution.
