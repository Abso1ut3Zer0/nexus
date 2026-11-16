#![allow(clippy::suboptimal_flops, clippy::float_cmp)]

/// 2-state Kalman filter with configurable observation model.
///
/// Tracks a 2-element state vector from noisy scalar measurements.
/// The observation model H is provided at each update, allowing
/// the measurement to be any linear combination of the state.
///
/// The predict step adds process noise Q to the covariance.
/// The update step applies the standard Kalman correction.
///
/// # Use Cases
/// - Position + velocity tracking from noisy position measurements
/// - Level + trend estimation
/// - Any 2-state linear system
#[derive(Debug, Clone)]
pub struct Kalman2d {
    state: [f64; 2],
    p: [f64; 4],
    q: [f64; 4],
    r: f64,
    last_innovation: Option<f64>,
    last_innovation_var: Option<f64>,
    count: u64,
    initial_state: [f64; 2],
    initial_p: [f64; 4],
}

/// Builder for [`Kalman2d`].
#[derive(Debug, Clone)]
pub struct Kalman2dBuilder {
    process_noise: Option<[[f64; 2]; 2]>,
    measurement_noise: Option<f64>,
    initial_state: [f64; 2],
    initial_covariance: [[f64; 2]; 2],
}

impl Kalman2d {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> Kalman2dBuilder {
        Kalman2dBuilder {
            process_noise: None,
            measurement_noise: None,
            initial_state: [0.0; 2],
            initial_covariance: [[1.0, 0.0], [0.0, 1.0]],
        }
    }

    /// Adds process noise to the covariance: P = P + Q.
    ///
    /// Call this before `update` to model the passage of time
    /// and the associated uncertainty growth.
    #[inline]
    pub fn predict(&mut self) {
        self.p[0] += self.q[0];
        self.p[1] += self.q[1];
        self.p[2] += self.q[2];
        self.p[3] += self.q[3];
    }

    /// Predict with custom state transition matrix F.
    ///
    /// Propagates state as `x = F * x` and covariance as `P = F * P * F' + Q`.
    /// The existing `predict()` uses identity dynamics (F = I).
    pub fn predict_with_dynamics(&mut self, f: [[f64; 2]; 2]) {
        // x_new = F * x
        let x0 = f[0][0] * self.state[0] + f[0][1] * self.state[1];
        let x1 = f[1][0] * self.state[0] + f[1][1] * self.state[1];
        self.state = [x0, x1];

        // P_new = F * P * F' + Q
        // FP[i][j] = Σ_k F[i][k] * P[k*2+j]
        let fp00 = f[0][0] * self.p[0] + f[0][1] * self.p[2];
        let fp01 = f[0][0] * self.p[1] + f[0][1] * self.p[3];
        let fp10 = f[1][0] * self.p[0] + f[1][1] * self.p[2];
        let fp11 = f[1][0] * self.p[1] + f[1][1] * self.p[3];

        // (FP) * F' + Q
        self.p[0] = fp00 * f[0][0] + fp01 * f[0][1] + self.q[0];
        self.p[1] = fp00 * f[1][0] + fp01 * f[1][1] + self.q[1];
        self.p[2] = fp10 * f[0][0] + fp11 * f[0][1] + self.q[2];
        self.p[3] = fp10 * f[1][0] + fp11 * f[1][1] + self.q[3];
    }

    /// Incorporates a scalar observation with observation model H.
    ///
    /// The observation is modeled as: `z = h[0]*state[0] + h[1]*state[1] + noise`.
    ///
    /// # Arguments
    /// - `observation` — the measured scalar value
    /// - `h` — the 2-element observation vector [h0, h1]
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the observation is NaN, or
    /// `DataError::Infinite` if the observation is infinite.
    #[inline]
    pub fn update(
        &mut self,
        observation: f64,
        h: [f64; 2],
    ) -> Result<(), nexus_stats_core::DataError> {
        check_finite!(observation);
        debug_assert!(h.iter().all(|v| v.is_finite()), "h must be finite");
        // Innovation: y = obs - H*x
        let y = observation - h[0] * self.state[0] - h[1] * self.state[1];

        // Innovation covariance: S = H*P*H' + R. With P positive semi-definite
        // and R > 0 this is at least R; anything else means P has degraded (or a
        // NaN got in): restore P and skip the measurement rather than apply a
        // gain of 1/EPSILON.
        let s = h[0] * h[0] * self.p[0]
            + h[0] * h[1] * self.p[1]
            + h[1] * h[0] * self.p[2]
            + h[1] * h[1] * self.p[3]
            + self.r;
        if !nexus_stats_core::math::positive_finite(s) {
            self.p = self.initial_p;
            return Ok(());
        }

        // Kalman gain: K = P*H' / S
        let s_inv = 1.0 / s;
        let k0 = (self.p[0] * h[0] + self.p[1] * h[1]) * s_inv;
        let k1 = (self.p[2] * h[0] + self.p[3] * h[1]) * s_inv;

        // State update: x = x + K*y
        self.state[0] += k0 * y;
        self.state[1] += k1 * y;

        // Covariance update: P = (I - K*H) * P
        let old_p = self.p;
        self.p[0] = (1.0 - k0 * h[0]) * old_p[0] + (-k0 * h[1]) * old_p[2];
        self.p[1] = (1.0 - k0 * h[0]) * old_p[1] + (-k0 * h[1]) * old_p[3];
        self.p[2] = (-k1 * h[0]) * old_p[0] + (1.0 - k1 * h[1]) * old_p[2];
        self.p[3] = (-k1 * h[0]) * old_p[1] + (1.0 - k1 * h[1]) * old_p[3];
        // Keep P symmetric: the (I - KH)P form drifts asymmetric under rounding.
        let off = 0.5 * (self.p[1] + self.p[2]);
        self.p[1] = off;
        self.p[2] = off;

        self.last_innovation = Some(y);
        self.last_innovation_var = Some(s);
        self.count += 1;
        Ok(())
    }

    /// Returns the current state estimate [x0, x1].
    #[inline]
    #[must_use]
    pub fn state(&self) -> [f64; 2] {
        self.state
    }

    /// Returns the current covariance as a 2x2 matrix.
    #[inline]
    #[must_use]
    pub fn covariance(&self) -> [[f64; 2]; 2] {
        [[self.p[0], self.p[1]], [self.p[2], self.p[3]]]
    }

    /// Returns the last innovation (measurement residual), or `None`
    /// if no updates have been performed.
    #[inline]
    #[must_use]
    pub fn innovation(&self) -> Option<f64> {
        self.last_innovation
    }

    /// Returns the last innovation variance (S), or `None`
    /// if no updates have been performed.
    #[inline]
    #[must_use]
    pub fn innovation_variance(&self) -> Option<f64> {
        self.last_innovation_var
    }

    /// Override measurement noise (R) for subsequent updates.
    ///
    /// Use this to increase R when an observation looks like an outlier
    /// (innovation > 3σ) — the Kalman will trust the observation less.
    /// Set back to baseline when done.
    ///
    /// # Panics
    ///
    /// Panics if `r` is negative, NaN, or infinite.
    #[inline]
    pub fn set_measurement_noise(&mut self, r: f64) {
        assert!(
            r > 0.0 && r.is_finite(),
            "measurement noise R must be positive and finite, got {r}"
        );
        self.r = r;
    }

    /// Override process noise (Q) for subsequent updates.
    ///
    /// Use this to increase Q when CUSUM detects a regime shift —
    /// the Kalman will adapt faster to the new level.
    ///
    /// # Panics
    ///
    /// Panics if any element is NaN or infinite.
    #[inline]
    pub fn set_process_noise(&mut self, q: [[f64; 2]; 2]) {
        assert!(
            q.iter().flat_map(|r| r.iter()).all(|v| v.is_finite()),
            "process noise Q elements must be finite"
        );
        self.q = [q[0][0], q[0][1], q[1][0], q[1][1]];
    }

    /// Returns the current measurement noise (R).
    #[inline]
    #[must_use]
    pub fn measurement_noise(&self) -> f64 {
        self.r
    }

    /// Returns the current process noise (Q) as a 2x2 matrix.
    #[inline]
    #[must_use]
    pub fn process_noise(&self) -> [[f64; 2]; 2] {
        [[self.q[0], self.q[1]], [self.q[2], self.q[3]]]
    }

    /// Number of updates performed.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Resets to initial state and covariance.
    #[inline]
    pub fn reset(&mut self) {
        self.state = self.initial_state;
        self.p = self.initial_p;
        self.last_innovation = None;
        self.last_innovation_var = None;
        self.count = 0;
    }
}

impl Kalman2dBuilder {
    /// Sets the 2x2 process noise matrix Q (required).
    #[inline]
    #[must_use]
    pub fn process_noise(mut self, q: [[f64; 2]; 2]) -> Self {
        self.process_noise = Some(q);
        self
    }

    /// Sets the scalar measurement noise variance R (required, must be > 0).
    #[inline]
    #[must_use]
    pub fn measurement_noise(mut self, r: f64) -> Self {
        self.measurement_noise = Some(r);
        self
    }

    /// Sets the initial state estimate. Default: [0, 0].
    #[inline]
    #[must_use]
    pub fn initial_state(mut self, state: [f64; 2]) -> Self {
        self.initial_state = state;
        self
    }

    /// Sets the initial covariance matrix. Default: identity.
    #[inline]
    #[must_use]
    pub fn initial_covariance(mut self, p: [[f64; 2]; 2]) -> Self {
        self.initial_covariance = p;
        self
    }

    /// Builds the filter.
    ///
    /// # Errors
    ///
    /// - `process_noise` and `measurement_noise` must be set.
    /// - `measurement_noise` must be positive.
    #[inline]
    pub fn build(self) -> Result<Kalman2d, nexus_stats_core::ConfigError> {
        let q_mat = self
            .process_noise
            .ok_or(nexus_stats_core::ConfigError::Missing("process_noise"))?;
        let r = self
            .measurement_noise
            .ok_or(nexus_stats_core::ConfigError::Missing("measurement_noise"))?;

        if !nexus_stats_core::math::positive_finite(r) {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "measurement_noise must be positive",
            ));
        }
        let finite = |m: &[[f64; 2]; 2]| m.iter().flatten().all(|v| v.is_finite());
        if !finite(&q_mat)
            || !finite(&self.initial_covariance)
            || !self.initial_state.iter().all(|v| v.is_finite())
        {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "process_noise, initial_covariance and initial_state must be finite",
            ));
        }

        let q = [q_mat[0][0], q_mat[0][1], q_mat[1][0], q_mat[1][1]];
        let p0 = self.initial_covariance;
        let p = [p0[0][0], p0[0][1], p0[1][0], p0[1][1]];

        Ok(Kalman2d {
            state: self.initial_state,
            p,
            q,
            r,
            last_innovation: None,
            last_innovation_var: None,
            count: 0,
            initial_state: self.initial_state,
            initial_p: p,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constant_signal_converges() {
        let mut kf = Kalman2d::builder()
            .process_noise([[0.01, 0.0], [0.0, 0.01]])
            .measurement_noise(1.0)
            .build()
            .unwrap();

        for _ in 0..100 {
            kf.predict();
            kf.update(50.0, [1.0, 0.0]).unwrap();
        }

        let s = kf.state();
        assert!(
            (s[0] - 50.0).abs() < 1.0,
            "state[0] = {}, expected ~50.0",
            s[0]
        );
    }

    #[test]
    fn covariance_shrinks() {
        let mut kf = Kalman2d::builder()
            .process_noise([[0.01, 0.0], [0.0, 0.01]])
            .measurement_noise(1.0)
            .initial_covariance([[100.0, 0.0], [0.0, 100.0]])
            .build()
            .unwrap();

        kf.predict();
        let _ = kf.update(50.0, [1.0, 0.0]);
        let cov1 = kf.covariance();
        let trace1 = cov1[0][0] + cov1[1][1];

        for _ in 0..50 {
            kf.predict();
            kf.update(50.0, [1.0, 0.0]).unwrap();
        }

        let cov2 = kf.covariance();
        let trace2 = cov2[0][0] + cov2[1][1];

        assert!(
            trace2 < trace1,
            "covariance trace should decrease: {trace1} -> {trace2}"
        );
    }

    #[test]
    fn innovation_stored() {
        let mut kf = Kalman2d::builder()
            .process_noise([[0.01, 0.0], [0.0, 0.01]])
            .measurement_noise(1.0)
            .build()
            .unwrap();

        assert!(kf.innovation().is_none());
        assert!(kf.innovation_variance().is_none());

        kf.predict();
        kf.update(10.0, [1.0, 0.0]).unwrap();

        assert!(kf.innovation().is_some());
        assert!(kf.innovation_variance().is_some());
        assert!(kf.innovation_variance().unwrap() > 0.0);
    }

    #[test]
    fn reset_restores_initial() {
        let mut kf = Kalman2d::builder()
            .process_noise([[0.01, 0.0], [0.0, 0.01]])
            .measurement_noise(1.0)
            .initial_state([5.0, 3.0])
            .build()
            .unwrap();

        for _ in 0..50 {
            kf.predict();
            kf.update(100.0, [1.0, 0.0]).unwrap();
        }

        kf.reset();
        assert_eq!(kf.count(), 0);
        assert_eq!(kf.state(), [5.0, 3.0]);
        assert!(kf.innovation().is_none());
    }

    #[test]
    fn builder_missing_process_noise() {
        let result = Kalman2d::builder().measurement_noise(1.0).build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Missing("process_noise"))
        ));
    }

    #[test]
    fn builder_missing_measurement_noise() {
        let result = Kalman2d::builder()
            .process_noise([[0.01, 0.0], [0.0, 0.01]])
            .build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Missing("measurement_noise"))
        ));
    }

    #[test]
    fn builder_invalid_measurement_noise() {
        let result = Kalman2d::builder()
            .process_noise([[0.01, 0.0], [0.0, 0.01]])
            .measurement_noise(0.0)
            .build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Invalid(_))
        ));

        let result = Kalman2d::builder()
            .process_noise([[0.01, 0.0], [0.0, 0.01]])
            .measurement_noise(-1.0)
            .build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Invalid(_))
        ));
    }

    #[test]
    fn two_state_tracking() {
        // Track position and velocity. Observe position only.
        // True velocity = 1.0 per step.
        let mut kf = Kalman2d::builder()
            .process_noise([[0.1, 0.0], [0.0, 0.1]])
            .measurement_noise(1.0)
            .build()
            .unwrap();

        for i in 0..200 {
            kf.predict();
            // Simulate constant velocity: position = i
            kf.update(i as f64, [1.0, 0.0]).unwrap();
        }

        let s = kf.state();
        assert!(
            (s[0] - 199.0).abs() < 5.0,
            "position = {}, expected ~199",
            s[0]
        );
    }

    #[test]
    fn noise_setter_getters() {
        let mut kf = Kalman2d::builder()
            .process_noise([[0.01, 0.0], [0.0, 0.01]])
            .measurement_noise(1.0)
            .build()
            .unwrap();

        assert_eq!(kf.measurement_noise(), 1.0);
        kf.set_measurement_noise(10.0);
        assert_eq!(kf.measurement_noise(), 10.0);

        let q = kf.process_noise();
        assert_eq!(q[0][0], 0.01);
        kf.set_process_noise([[1.0, 0.0], [0.0, 1.0]]);
        assert_eq!(kf.process_noise()[0][0], 1.0);
    }

    #[test]
    fn high_r_trusts_observation_less() {
        // Two Kalmans: one with normal R, one with high R.
        // Feed same outlier — high R should move state less.
        let mut kf_normal = Kalman2d::builder()
            .process_noise([[0.01, 0.0], [0.0, 0.01]])
            .measurement_noise(1.0)
            .build()
            .unwrap();
        let mut kf_high_r = kf_normal.clone();

        // Converge both to ~50
        for _ in 0..50 {
            kf_normal.predict();
            kf_normal.update(50.0, [1.0, 0.0]).unwrap();
            kf_high_r.predict();
            kf_high_r.update(50.0, [1.0, 0.0]).unwrap();
        }

        let before = kf_normal.state()[0];

        // Feed outlier
        kf_normal.predict();
        kf_normal.update(200.0, [1.0, 0.0]).unwrap();

        kf_high_r.set_measurement_noise(1000.0);
        kf_high_r.predict();
        kf_high_r.update(200.0, [1.0, 0.0]).unwrap();

        let move_normal = (kf_normal.state()[0] - before).abs();
        let move_high_r = (kf_high_r.state()[0] - before).abs();

        assert!(
            move_high_r < move_normal,
            "high R should move less: normal={move_normal}, high_r={move_high_r}"
        );
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut kf = Kalman2d::builder()
            .process_noise([[0.01, 0.0], [0.0, 0.01]])
            .measurement_noise(1.0)
            .build()
            .unwrap();
        assert_eq!(
            kf.update(f64::NAN, [1.0, 0.0]),
            Err(nexus_stats_core::DataError::NotANumber)
        );
        assert_eq!(
            kf.update(f64::INFINITY, [1.0, 0.0]),
            Err(nexus_stats_core::DataError::Infinite)
        );
        assert_eq!(kf.count(), 0);
    }
}
