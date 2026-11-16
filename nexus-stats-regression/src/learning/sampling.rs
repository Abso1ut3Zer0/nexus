pub(super) mod f64_impl {
    /// Marsaglia polar method. Returns one standard normal sample.
    /// Consumes at least two calls to `rng` per sample.
    #[allow(clippy::suboptimal_flops)]
    pub fn normal_sample(rng: &mut impl FnMut() -> f64) -> f64 {
        loop {
            let u = 2.0 * rng() - 1.0;
            let v = 2.0 * rng() - 1.0;
            let s = u * u + v * v;
            if s > 0.0 && s < 1.0 {
                let ln_s = nexus_stats_core::math::ln(s);
                let factor = nexus_stats_core::math::sqrt(-2.0 * ln_s / s);
                return u * factor;
            }
        }
    }

    /// Marsaglia-Tsang method for Gamma(shape, 1). Shape must be > 0.
    /// For shape < 1: Gamma(shape) = Gamma(shape+1) * U^(1/shape).
    #[allow(clippy::many_single_char_names, clippy::suboptimal_flops)]
    pub fn gamma_sample(shape: f64, rng: &mut impl FnMut() -> f64) -> f64 {
        if shape < 1.0 {
            let g = gamma_sample(shape + 1.0, rng);
            let u = rng();
            let pow = nexus_stats_core::math::exp(nexus_stats_core::math::ln(u) / shape);
            return g * pow;
        }

        let d = shape - 1.0 / 3.0;
        let c = 1.0 / nexus_stats_core::math::sqrt(9.0 * d);

        loop {
            let x = normal_sample(rng);
            let v_base = 1.0 + c * x;
            if v_base <= 0.0 {
                continue;
            }
            let v = v_base * v_base * v_base;
            let u = rng();
            let x2 = x * x;

            if u < 1.0 - 0.0331 * x2 * x2 {
                return d * v;
            }

            let ln_u = nexus_stats_core::math::ln(u);
            let ln_v = nexus_stats_core::math::ln(v);
            if ln_u < 0.5 * x2 + d * (1.0 - v + ln_v) {
                return d * v;
            }
        }
    }

    /// Beta(alpha, beta) via ratio of two Gamma samples.
    #[allow(clippy::float_cmp)]
    pub fn beta_sample(alpha: f64, beta: f64, rng: &mut impl FnMut() -> f64) -> f64 {
        let x = gamma_sample(alpha, rng);
        let y = gamma_sample(beta, rng);
        let sum = x + y;
        // Both gamma draws underflowing to zero needs shapes far below any
        // prior this crate accepts; if it ever happens, the posterior mean is
        // the honest answer, not a constant.
        if sum == 0.0 {
            return alpha / (alpha + beta);
        }
        x / sum
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_rng_f64(seed: u64) -> impl FnMut() -> f64 {
        let mut state = seed;
        move || {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            (state >> 33) as f64 / (1u64 << 31) as f64
        }
    }

    #[test]
    fn normal_sample_distribution() {
        let mut rng = make_rng_f64(42);
        let n = 10_000;
        let mut sum = 0.0;
        let mut sum_sq = 0.0;
        for _ in 0..n {
            let x = f64_impl::normal_sample(&mut rng);
            sum += x;
            sum_sq += x * x;
        }
        let mean = sum / n as f64;
        let var = sum_sq / n as f64 - mean * mean;
        assert!(mean.abs() < 0.05, "mean={mean}, expected ~0");
        assert!((var - 1.0).abs() < 0.1, "var={var}, expected ~1");
    }

    #[test]
    fn gamma_sample_mean() {
        let mut rng = make_rng_f64(123);
        let shape = 5.0;
        let n = 10_000;
        let mut sum = 0.0;
        for _ in 0..n {
            let x = f64_impl::gamma_sample(shape, &mut rng);
            assert!(x > 0.0, "gamma sample must be positive");
            sum += x;
        }
        let mean = sum / n as f64;
        assert!((mean - shape).abs() < 0.3, "mean={mean}, expected ~{shape}");
    }

    #[test]
    fn gamma_sample_shape_less_than_one() {
        let mut rng = make_rng_f64(77);
        let shape = 0.5;
        let n = 5_000;
        let mut sum = 0.0;
        for _ in 0..n {
            let x = f64_impl::gamma_sample(shape, &mut rng);
            assert!(x >= 0.0, "gamma sample must be non-negative");
            sum += x;
        }
        let mean = sum / n as f64;
        assert!((mean - shape).abs() < 0.1, "mean={mean}, expected ~{shape}");
    }

    #[test]
    fn beta_sample_range() {
        let mut rng = make_rng_f64(99);
        for _ in 0..1_000 {
            let x = f64_impl::beta_sample(2.0, 5.0, &mut rng);
            assert!((0.0..=1.0).contains(&x), "beta sample {x} out of [0,1]");
        }
    }

    #[test]
    fn beta_sample_mean() {
        let mut rng = make_rng_f64(55);
        let alpha = 2.0;
        let beta = 5.0;
        let n = 10_000;
        let mut sum = 0.0;
        for _ in 0..n {
            sum += f64_impl::beta_sample(alpha, beta, &mut rng);
        }
        let mean = sum / n as f64;
        let expected = alpha / (alpha + beta);
        assert!(
            (mean - expected).abs() < 0.02,
            "mean={mean}, expected ~{expected}"
        );
    }
}
