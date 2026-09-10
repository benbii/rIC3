use crate::ic3::{mic::DropVarParameter, proofoblig::Po};
use nalgebra::{SMatrix, SVector};
use rand::{RngExt, rngs::SmallRng};

const INPUT_DIM: usize = 7;
const HIDDEN_DIM: usize = 16;
const ACTIONS: usize = 4;
const LR: f64 = 0.05;
const EPSILON: f64 = 0.1;
const L2: f64 = 0.001;

/// The single online-CTG configuration retained from the experiment.
pub(crate) struct OnlineCtg {
    weights1: SMatrix<f64, HIDDEN_DIM, INPUT_DIM>,
    bias1: SVector<f64, HIDDEN_DIM>,
    weights2: SMatrix<f64, ACTIONS, HIDDEN_DIM>,
    bias2: SVector<f64, ACTIONS>,
}

impl OnlineCtg {
    pub(crate) fn new(rng: &mut SmallRng) -> Self {
        Self {
            weights1: SMatrix::from_fn(|_, _| rng.random::<f64>() * 0.2 - 0.1),
            bias1: SVector::from_fn(|_, _| rng.random::<f64>() * 0.2 - 0.1),
            weights2: SMatrix::from_fn(|_, _| rng.random::<f64>() * 0.2 - 0.1),
            bias2: SVector::from_fn(|_, _| rng.random::<f64>() * 0.2 - 0.1),
        }
    }

    pub(crate) fn select(
        &self,
        context: &[f64; INPUT_DIM],
        rng: &mut SmallRng,
    ) -> (DropVarParameter, usize) {
        let context = SVector::from_column_slice(context);
        let action = if rng.random::<f64>() < EPSILON {
            (rng.random::<u64>() as usize) % ACTIONS
        } else {
            let score = self.weights2 * (self.weights1 * context + self.bias1).map(|x| x.max(0.0))
                + self.bias2;
            let mut action = 0;
            for i in 1..ACTIONS {
                if score[i] > score[action] {
                    action = i;
                }
            }
            action
        };
        let parameter = match action {
            0 => DropVarParameter::new(0, 0, 0),
            1 => DropVarParameter::new(1, 3, 1),
            2 => DropVarParameter::new(2, 5, 1),
            3 => DropVarParameter::new(8, 4, 1),
            _ => unreachable!(),
        };
        (parameter, action)
    }

    pub(crate) fn feedback(&mut self, context: &[f64; INPUT_DIM], action: usize, reward: f64) {
        let context = SVector::from_column_slice(context);
        let hidden_input = self.weights1 * context + self.bias1;
        let hidden_derivative = hidden_input.map(|x| f64::from(x > 0.0));
        let score = self.weights2 * hidden_input.map(|x| x.max(0.0)) + self.bias2;
        let grad_output = 2.0 * (score[action] - reward);

        // Intentionally use the ReLU derivative for the output update, then
        // use the already-updated output weights for the hidden update.
        for s in 0..ACTIONS {
            for h in 0..HIDDEN_DIM {
                self.weights2[(s, h)] -= LR
                    * ((s == action).then_some(grad_output).unwrap_or(0.0) * hidden_derivative[h]
                        + L2 * self.weights2[(s, h)]);
            }
            if s == action {
                self.bias2[s] -= LR * grad_output;
            }
        }

        for h in 0..HIDDEN_DIM {
            let grad_hidden = grad_output * self.weights2[(action, h)] * hidden_derivative[h];
            for i in 0..INPUT_DIM {
                self.weights1[(h, i)] -=
                    LR * (grad_hidden * context[i] + L2 * self.weights1[(h, i)]);
            }
            self.bias1[h] -= LR * grad_hidden;
        }
    }

    pub(crate) fn reward(
        po: &Po,
        original_cube_size: usize,
        generalized_cube_size: usize,
        pushed_frame: usize,
        level: usize,
    ) -> f64 {
        let pushing_power = pushed_frame as f64 - po.frame as f64;
        debug_assert!(original_cube_size > 0);
        let size_reduction = 1.0 - generalized_cube_size as f64 / original_cube_size as f64;
        let pushing_ratio = pushing_power / (level - po.frame + 1) as f64;
        let push_quality = if pushing_power > 0.0 {
            pushing_ratio
        } else {
            -0.1
        };
        let generalization_quality = if size_reduction > 0.5 && pushing_ratio > 0.3 {
            0.3
        } else if size_reduction > 0.7 && pushing_ratio < 0.1 {
            -0.2
        } else {
            0.0
        };
        let mut reward = size_reduction * 0.35 + push_quality * 0.45 + generalization_quality;
        if pushed_frame >= level {
            reward += 0.4;
        }
        if generalized_cube_size == 1 {
            reward += 0.2;
        }
        if po.frame as f64 > 0.7 * level as f64 && pushing_power > 0.0 {
            reward += 0.1;
        }
        reward.clamp(-0.5, 2.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::SeedableRng;

    #[test]
    fn feedback_preserves_experimental_update() {
        let mut online = OnlineCtg {
            weights1: SMatrix::zeros(),
            bias1: SVector::repeat(1.0),
            weights2: SMatrix::zeros(),
            bias2: SVector::zeros(),
        };
        online.feedback(&[1.0; INPUT_DIM], 0, 1.0);

        assert!((online.weights2[(0, 0)] - 0.1).abs() < 1e-12);
        assert!((online.bias2[0] - 0.1).abs() < 1e-12);
        assert!((online.weights1[(0, 0)] - 0.01).abs() < 1e-12);
        assert!((online.bias1[0] - 1.01).abs() < 1e-12);
        assert!(online.weights2[(1, 0)].abs() < 1e-12);
    }

    #[test]
    fn seeded_rng_reproduces_network_and_actions() {
        let mut left_rng = SmallRng::seed_from_u64(2104);
        let mut right_rng = SmallRng::seed_from_u64(2104);
        let left = OnlineCtg::new(&mut left_rng);
        let right = OnlineCtg::new(&mut right_rng);
        let context = [1.0; INPUT_DIM];

        assert_eq!(left.weights1, right.weights1);
        assert_eq!(left.bias1, right.bias1);
        assert_eq!(left.weights2, right.weights2);
        assert_eq!(left.bias2, right.bias2);
        for _ in 0..100 {
            assert_eq!(
                left.select(&context, &mut left_rng).1,
                right.select(&context, &mut right_rng).1
            );
        }
    }
}
