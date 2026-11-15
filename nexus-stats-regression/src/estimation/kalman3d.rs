#![allow(clippy::suboptimal_flops, clippy::float_cmp)]

/// 3-state Kalman filter with configurable observation model.
///
/// Tracks a 3-element state vector from noisy scalar measurements.
/// The observation model H is provided at each update, allowing
/// the measurement to be any linear combination of the state.
///
/// The predict step adds process noise Q to the covariance.
/// The update step applies the standard Kalman correction.
///
/// # Use Cases
/// - Position + velocity + acceleration tracking
/// - Level + trend + curvature estimation
/// - Any 3-state linear system
#[derive(Debug, Clone)]
pub struct Kalman3d {
    state: [f64; 3],
    p: [f64; 9],
    q: [f64; 9],
    r: f64,
    last_innovation: Option<f64>,
    last_innovation_var: Option<f64>,
    count: u64,
    initial_state: [f64; 3],
    initial_p: [f64; 9],
}

/// Builder for [`Kalman3d`].
#[derive(Debug, Clone)]
pub struct Kalman3dBuilder {
    process_noise: Option<[[f64; 3]; 3]>,
    measurement_noise: Option<f64>,
    initial_state: [f64; 3],
    initial_covariance: [[f64; 3]; 3],
}

impl Kalman3d {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> Kalman3dBuilder {
        Kalman3dBuilder {
            process_noise: None,
            measurement_noise: None,
            initial_state: [0.0; 3],
            initial_covariance: [[1.0, 0.0, 0.0], [0.0, 1.0, 0.0], [0.0, 0.0, 1.0]],
        }
    }

    /// Adds process noise to the covariance: P = P + Q.
    ///
    /// Call this before `update` to model the passage of time
    /// and the associated uncertainty growth.
    #[inline]
    pub fn predict(&mut self) {
        for i in 0..3 {
            for j in 0..3 {
                self.p[i * 3 + j] += self.q[i * 3 + j];
            }
        }
    }

    /// Predict with custom state transition matrix F.
    pub fn predict_with_dynamics(&mut self, f: [[f64; 3]; 3]) {
        // x_new = F * x
        let mut new_state = [0.0; 3];
        for i in 0..3 {
            for k in 0..3 {
                new_state[i] += f[i][k] * self.state[k];
            }
        }
        self.state = new_state;

        // FP = F * P
        let mut fp = [0.0; 9];
        for i in 0..3 {
            for j in 0..3 {
                for k in 0..3 {
                    fp[i * 3 + j] += f[i][k] * self.p[k * 3 + j];
                }
            }
        }

        // P_new = FP * F' + Q
        let mut new_p = [0.0; 9];
        for i in 0..3 {
            for j in 0..3 {
                for k in 0..3 {
                    new_p[i * 3 + j] += fp[i * 3 + k] * f[j][k];
                }
                new_p[i * 3 + j] += self.q[i * 3 + j];
            }
        }
        self.p = new_p;
    }

    /// Incorporates a scalar observation with observation model H.
    ///
    /// The observation is modeled as:
    /// `z = h[0]*state[0] + h[1]*state[1] + h[2]*state[2] + noise`.
    ///
    /// # Arguments
    /// - `observation` — the measured scalar value
    /// - `h` — the 3-element observation vector [h0, h1, h2]
    ///
    /// # Errors
    ///
    /// Returns `DataError::NotANumber` if the observation is NaN, or
    /// `DataError::Infinite` if the observation is infinite.
    #[inline]
    pub fn update(
        &mut self,
        observation: f64,
        h: [f64; 3],
    ) -> Result<(), nexus_stats_core::DataError> {
        check_finite!(observation);
        debug_assert!(h.iter().all(|v| v.is_finite()), "h must be finite");
        // Innovation: y = obs - H*x
        let mut hx = 0.0;
        for i in 0..3 {
            hx += h[i] * self.state[i];
        }
        let y = observation - hx;

        // Innovation covariance: S = H*P*H' + R
        // Epsilon floor prevents NaN if P degrades numerically.
        let mut s = self.r;
        for i in 0..3 {
            for j in 0..3 {
                s += h[i] * self.p[i * 3 + j] * h[j];
            }
        }
        s = s.max(f64::EPSILON);

        // Kalman gain: K = P*H' / S
        let s_inv = 1.0 / s;
        let mut k = [0.0; 3];
        for i in 0..3 {
            let mut ph = 0.0;
            for j in 0..3 {
                ph += self.p[i * 3 + j] * h[j];
            }
            k[i] = ph * s_inv;
        }

        // State update: x = x + K*y
        for i in 0..3 {
            self.state[i] += k[i] * y;
        }

        // Covariance update: P = (I - K*H) * P
        let old_p = self.p;
        for i in 0..3 {
            for j in 0..3 {
                let mut sum = 0.0;
                for m in 0..3 {
                    let ikh = if i == m { 1.0 } else { 0.0 } - k[i] * h[m];
                    sum += ikh * old_p[m * 3 + j];
                }
                self.p[i * 3 + j] = sum;
            }
        }

        self.last_innovation = Some(y);
        self.last_innovation_var = Some(s);
        self.count += 1;
        Ok(())
    }

    /// Returns the current state estimate [x0, x1, x2].
    #[inline]
    #[must_use]
    pub fn state(&self) -> [f64; 3] {
        self.state
    }

    /// Returns the current covariance as a 3x3 matrix.
    #[inline]
    #[must_use]
    pub fn covariance(&self) -> [[f64; 3]; 3] {
        [
            [self.p[0], self.p[1], self.p[2]],
            [self.p[3], self.p[4], self.p[5]],
            [self.p[6], self.p[7], self.p[8]],
        ]
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
    /// # Panics
    ///
    /// Panics if any element is NaN or infinite.
    #[inline]
    pub fn set_process_noise(&mut self, q: [[f64; 3]; 3]) {
        assert!(
            q.iter().flat_map(|r| r.iter()).all(|v| v.is_finite()),
            "process noise Q elements must be finite"
        );
        self.q = [
            q[0][0], q[0][1], q[0][2], q[1][0], q[1][1], q[1][2], q[2][0], q[2][1], q[2][2],
        ];
    }

    /// Returns the current measurement noise (R).
    #[inline]
    #[must_use]
    pub fn measurement_noise(&self) -> f64 {
        self.r
    }

    /// Returns the current process noise (Q) as a 3x3 matrix.
    #[inline]
    #[must_use]
    pub fn process_noise(&self) -> [[f64; 3]; 3] {
        [
            [self.q[0], self.q[1], self.q[2]],
            [self.q[3], self.q[4], self.q[5]],
            [self.q[6], self.q[7], self.q[8]],
        ]
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

impl Kalman3dBuilder {
    /// Sets the 3x3 process noise matrix Q (required).
    #[inline]
    #[must_use]
    pub fn process_noise(mut self, q: [[f64; 3]; 3]) -> Self {
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

    /// Sets the initial state estimate. Default: [0, 0, 0].
    #[inline]
    #[must_use]
    pub fn initial_state(mut self, state: [f64; 3]) -> Self {
        self.initial_state = state;
        self
    }

    /// Sets the initial covariance matrix. Default: identity.
    #[inline]
    #[must_use]
    pub fn initial_covariance(mut self, p: [[f64; 3]; 3]) -> Self {
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
    pub fn build(self) -> Result<Kalman3d, nexus_stats_core::ConfigError> {
        let q_mat = self
            .process_noise
            .ok_or(nexus_stats_core::ConfigError::Missing("process_noise"))?;
        let r = self
            .measurement_noise
            .ok_or(nexus_stats_core::ConfigError::Missing("measurement_noise"))?;

        if r <= 0.0 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "measurement_noise must be positive",
            ));
        }

        let mut q = [0.0; 9];
        let mut p = [0.0; 9];
        for i in 0..3 {
            for j in 0..3 {
                q[i * 3 + j] = q_mat[i][j];
                p[i * 3 + j] = self.initial_covariance[i][j];
            }
        }

        Ok(Kalman3d {
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

    fn diagonal_q() -> [[f64; 3]; 3] {
        [[0.01, 0.0, 0.0], [0.0, 0.01, 0.0], [0.0, 0.0, 0.01]]
    }

    #[test]
    fn constant_signal_converges() {
        let mut kf = Kalman3d::builder()
            .process_noise(diagonal_q())
            .measurement_noise(1.0)
            .build()
            .unwrap();

        for _ in 0..100 {
            kf.predict();
            kf.update(50.0, [1.0, 0.0, 0.0]).unwrap();
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
        // Observe all 3 states to ensure all covariances shrink
        let mut kf = Kalman3d::builder()
            .process_noise([[0.001, 0.0, 0.0], [0.0, 0.001, 0.0], [0.0, 0.0, 0.001]])
            .measurement_noise(1.0)
            .initial_covariance([[100.0, 0.0, 0.0], [0.0, 100.0, 0.0], [0.0, 0.0, 100.0]])
            .build()
            .unwrap();

        kf.predict();
        kf.update(50.0, [1.0, 0.0, 0.0]).unwrap();
        kf.update(25.0, [0.0, 1.0, 0.0]).unwrap();
        kf.update(10.0, [0.0, 0.0, 1.0]).unwrap();
        let cov1 = kf.covariance();
        let trace1 = cov1[0][0] + cov1[1][1] + cov1[2][2];

        for _ in 0..50 {
            kf.predict();
            kf.update(50.0, [1.0, 0.0, 0.0]).unwrap();
            kf.update(25.0, [0.0, 1.0, 0.0]).unwrap();
            kf.update(10.0, [0.0, 0.0, 1.0]).unwrap();
        }

        let cov2 = kf.covariance();
        let trace2 = cov2[0][0] + cov2[1][1] + cov2[2][2];

        assert!(
            trace2 < trace1,
            "covariance trace should decrease: {trace1} -> {trace2}"
        );
    }

    #[test]
    fn innovation_stored() {
        let mut kf = Kalman3d::builder()
            .process_noise(diagonal_q())
            .measurement_noise(1.0)
            .build()
            .unwrap();

        assert!(kf.innovation().is_none());
        assert!(kf.innovation_variance().is_none());

        kf.predict();
        kf.update(10.0, [1.0, 0.0, 0.0]).unwrap();

        assert!(kf.innovation().is_some());
        assert!(kf.innovation_variance().is_some());
        assert!(kf.innovation_variance().unwrap() > 0.0);
    }

    #[test]
    fn reset_restores_initial() {
        let mut kf = Kalman3d::builder()
            .process_noise(diagonal_q())
            .measurement_noise(1.0)
            .initial_state([5.0, 3.0, 1.0])
            .build()
            .unwrap();

        for _ in 0..50 {
            kf.predict();
            kf.update(100.0, [1.0, 0.0, 0.0]).unwrap();
        }

        kf.reset();
        assert_eq!(kf.count(), 0);
        assert_eq!(kf.state(), [5.0, 3.0, 1.0]);
        assert!(kf.innovation().is_none());
    }

    #[test]
    fn builder_missing_process_noise() {
        let result = Kalman3d::builder().measurement_noise(1.0).build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Missing("process_noise"))
        ));
    }

    #[test]
    fn builder_missing_measurement_noise() {
        let result = Kalman3d::builder().process_noise(diagonal_q()).build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Missing("measurement_noise"))
        ));
    }

    #[test]
    fn builder_invalid_measurement_noise() {
        let result = Kalman3d::builder()
            .process_noise(diagonal_q())
            .measurement_noise(0.0)
            .build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Invalid(_))
        ));

        let result = Kalman3d::builder()
            .process_noise(diagonal_q())
            .measurement_noise(-1.0)
            .build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Invalid(_))
        ));
    }

    #[test]
    fn three_state_tracking() {
        // Observe position only, H = [1, 0, 0].
        // True signal: position grows linearly.
        let mut kf = Kalman3d::builder()
            .process_noise([[0.1, 0.0, 0.0], [0.0, 0.1, 0.0], [0.0, 0.0, 0.1]])
            .measurement_noise(1.0)
            .build()
            .unwrap();

        for i in 0..200 {
            kf.predict();
            kf.update(i as f64, [1.0, 0.0, 0.0]).unwrap();
        }

        let s = kf.state();
        assert!(
            (s[0] - 199.0).abs() < 5.0,
            "position = {}, expected ~199",
            s[0]
        );
    }

    #[test]
    fn multi_observation_model() {
        // H = [0.5, 0.5, 0.0] — observe average of first two states.
        let mut kf = Kalman3d::builder()
            .process_noise(diagonal_q())
            .measurement_noise(0.1)
            .build()
            .unwrap();

        for _ in 0..200 {
            kf.predict();
            // Observe 10.0 = 0.5*x0 + 0.5*x1
            kf.update(10.0, [0.5, 0.5, 0.0]).unwrap();
        }

        let s = kf.state();
        // x0 + x1 should be ~20.0
        let sum = s[0] + s[1];
        assert!((sum - 20.0).abs() < 2.0, "x0 + x1 = {sum}, expected ~20.0");
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut kf = Kalman3d::builder()
            .process_noise(diagonal_q())
            .measurement_noise(1.0)
            .build()
            .unwrap();
        assert_eq!(
            kf.update(f64::NAN, [1.0, 0.0, 0.0]),
            Err(nexus_stats_core::DataError::NotANumber)
        );
        assert_eq!(
            kf.update(f64::INFINITY, [1.0, 0.0, 0.0]),
            Err(nexus_stats_core::DataError::Infinite)
        );
        assert_eq!(kf.count(), 0);
    }
}
