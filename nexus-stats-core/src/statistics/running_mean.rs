//! One step of a running mean, shared by the accumulators built on it.

/// How far a sample was from a running mean, before and after the mean
/// took it in.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct Deviation {
    /// `sample - mean` before the step.
    pub(crate) before: f64,
    /// `sample - mean` after the step.
    pub(crate) after: f64,
}

/// Moves `mean` the fraction `weight` of the way to `sample`. For a plain
/// running mean `weight` is `1 / count`.
#[inline]
pub(crate) fn step_mean(mean: &mut f64, sample: f64, weight: f64) -> Deviation {
    let before = sample - *mean;
    *mean += before * weight;
    Deviation {
        before,
        after: sample - *mean,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn step_mean_moves_the_mean_and_reports_both_deviations() {
        // Third sample of 2, 4, 9: the mean goes from 3 to 5.
        let mut mean = 3.0;
        let deviation = step_mean(&mut mean, 9.0, 1.0 / 3.0);
        assert_eq!(mean, 5.0);
        assert_eq!(
            deviation,
            Deviation {
                before: 6.0,
                after: 4.0
            }
        );
    }

    #[test]
    fn the_first_sample_becomes_the_mean() {
        let mut mean = 0.0;
        let deviation = step_mean(&mut mean, 7.5, 1.0);
        assert_eq!(mean, 7.5);
        assert_eq!(deviation.after, 0.0);
    }
}
