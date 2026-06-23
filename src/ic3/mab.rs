use crate::ic3::{frame::Frames, mic::DropVarParameter, proofoblig::ProofObligation};
use log::{trace, warn};
use nalgebra::{SMatrix, SVector};

/// 6 features + bias.
const CONTEXT_DIM: usize = 7;
/// Dynamic (activity-aware) arms.
const BALANCED_ARM: usize = 0;
const AGGRESSIVE_ARM: usize = 1;
const CONSERVATIVE_ARM: usize = 2;
const NUM_DYNAMIC_ARMS: usize = 3;
/// Static arms: fixed (limit, max, level) configurations of DropVarParameter.
const FIXED_ARM_CONFIGS: [(usize, usize, usize); 4] = [
    (0, 0, 0), // basic: no CTG
    (1, 3, 1), // conservative CTG
    (2, 5, 1), // balanced CTG
    (8, 4, 1), // aggressive deep CTG
];
const NUM_ARMS: usize = NUM_DYNAMIC_ARMS + FIXED_ARM_CONFIGS.len();

type Ic3MabVector = SVector<f64, CONTEXT_DIM>;
type Ic3MabMatrix = SMatrix<f64, CONTEXT_DIM, CONTEXT_DIM>;

/// Max activity along the successor chain of the po (up to 3 hops), used by
/// the dynamic arms to gauge the difficulty of blocking the current CTI.
fn branch_act(po: &ProofObligation) -> Option<f64> {
    let n = po.next.as_ref()?;
    let mut act = n.act;
    if let Some(nn) = n.next.as_ref() {
        act = act.max(nn.act);
        if let Some(nnn) = nn.next.as_ref() {
            act = act.max(nnn.act);
        }
    }
    Some(act)
}

/// Balanced arm.
pub(crate) fn balanced_params(po: &ProofObligation, x: f64) -> DropVarParameter {
    let Some(act) = branch_act(po) else {
        return DropVarParameter::default();
    };
    match act {
        40.0.. => {
            let limit = ((act - 40.0).powf(x) * 2.0 + 5.0).round() as usize;
            DropVarParameter::new(limit, 5, 1)
        }
        ..10.0 => DropVarParameter::new(0, 0, 0),
        _ => DropVarParameter::new(1, (act - 10.0) as usize / 10 + 2, 1),
    }
}

/// Aggressive dynamic arm: lower thresholds, stronger generalization effort.
fn aggressive_params(po: &ProofObligation) -> DropVarParameter {
    let Some(act) = branch_act(po) else {
        return DropVarParameter::new(1, 1, 1);
    };
    match act {
        25.0.. => {
            let limit = ((act - 25.0).powf(0.3) * 2.5 + 6.0).round() as usize;
            DropVarParameter::new(limit, 6, 1)
        }
        ..5.0 => DropVarParameter::new(1, 1, 1),
        _ => DropVarParameter::new(2, (act - 5.0) as usize / 8 + 3, 1),
    }
}

/// Conservative dynamic arm: higher thresholds, capped generalization effort.
fn conservative_params(po: &ProofObligation) -> DropVarParameter {
    let Some(act) = branch_act(po) else {
        return DropVarParameter::default();
    };
    match act {
        50.0.. => {
            let limit = (((act - 50.0).powf(0.3) * 1.5 + 4.0).round() as usize).min(6);
            DropVarParameter::new(limit, 3, 1)
        }
        ..15.0 => DropVarParameter::new(0, 0, 0),
        _ => DropVarParameter::new(1, ((act - 15.0) as usize / 12 + 1).min(3), 0),
    }
}

pub(crate) struct CtgMab {
    alpha: f64,
    lambda: f64,
    a: [Ic3MabMatrix; NUM_ARMS],
    a_inv: [Ic3MabMatrix; NUM_ARMS],
    b: [Ic3MabVector; NUM_ARMS],
    theta: [Ic3MabVector; NUM_ARMS],
    avg_cube_size: f64,
    cube_size_count: usize,
}

impl CtgMab {
    pub fn new(alpha: f64, lambda: f64) -> Self {
        assert!(alpha.is_finite() && alpha >= 0.0);
        assert!(lambda.is_finite() && lambda > 0.0);
        let a = Ic3MabMatrix::identity() * lambda;
        let a_inv = Ic3MabMatrix::identity() / lambda;
        Self {
            alpha,
            lambda,
            a: [a; NUM_ARMS],
            a_inv: [a_inv; NUM_ARMS],
            b: [Ic3MabVector::zeros(); NUM_ARMS],
            theta: [Ic3MabVector::zeros(); NUM_ARMS],
            avg_cube_size: 0.0,
            cube_size_count: 0,
        }
    }

    /// Proof-aware context vector: [relative level, relative cube size,
    /// push potential, relative depth, frame saturation, activity, bias].
    /// Also maintains the running average cube size used for normalization.
    pub fn encode(&mut self, lvl: usize, frames: &Frames, po: &ProofObligation) -> Ic3MabVector {
        debug_assert!(lvl > 0);
        let relative_level = po.frame as f64 / lvl as f64;
        let total_cube_size = self.cube_size_count as f64 * self.avg_cube_size;
        self.cube_size_count += 1;
        self.avg_cube_size =
            (total_cube_size + po.state.len() as f64) / self.cube_size_count as f64;
        let relative_cube_size = po.state.len() as f64 / self.avg_cube_size.max(1.0);
        let potential_of_push = 1.0 - relative_level;
        debug_assert!(po.frame + po.depth > 0);
        let relative_depth = po.frame as f64 / (po.frame + po.depth) as f64;
        let saturation = if po.frame < frames.len() {
            frames[po.frame].len()
        } else {
            0
        };
        let frame_saturation = (saturation as f64 / 100.0).min(1.0);
        let act_feat = (po.act / 100.0).clamp(0.0, 1.0);
        Ic3MabVector::from_column_slice(&[
            relative_level,
            relative_cube_size,
            potential_of_push,
            relative_depth,
            frame_saturation,
            act_feat,
            1.0,
        ])
    }

    /// Select a generalization strategy with LinUCB
    pub fn infer(&self, inp: &Ic3MabVector, po: &ProofObligation) -> (DropVarParameter, usize) {
        let mut best_arm = 0;
        let mut best_score = f64::NEG_INFINITY;
        // LinUCB arm selection: argmax of theta^T x + alpha * sqrt(x^T A^-1 x).
        for arm in 0..NUM_ARMS {
            let predicted = self.theta[arm].dot(inp);
            let uncertainty = (inp.transpose() * &self.a_inv[arm] * inp)[(0, 0)];
            let score = predicted + self.alpha * uncertainty.max(0.0).sqrt();
            if score > best_score {
                best_score = score;
                best_arm = arm;
            }
        }
        let p = match best_arm {
            BALANCED_ARM => balanced_params(po, 0.3),
            AGGRESSIVE_ARM => aggressive_params(po),
            CONSERVATIVE_ARM => conservative_params(po),
            _ => {
                let (limit, max, level) = FIXED_ARM_CONFIGS[best_arm - NUM_DYNAMIC_ARMS];
                DropVarParameter::new(limit, max, level)
            }
        };
        trace!("MAB chose arm {best_arm}: {p:?}");
        (p, best_arm)
    }

    pub fn reward(
        &mut self,
        po: &ProofObligation,
        original_cube_size: usize,
        generalized_cube_size: usize,
        pushed_frame: usize,
        arm: usize,
        level: usize,
    ) -> f64 {
        let pushing_power = pushed_frame as f64 - po.frame as f64;
        assert!(original_cube_size > 0);
        let size_reduction_ratio = 1.0 - generalized_cube_size as f64 / original_cube_size as f64;
        debug_assert!(level >= po.frame);
        let max_possible_push = level - po.frame + 1;
        let pushing_power_ratio = pushing_power / max_possible_push as f64;
        // push quality: reward effective pushes, penalize unpushable clauses
        let push_quality = if pushing_power > 0.0 {
            pushing_power_ratio
        } else {
            -0.1
        };
        // ideal vs over-generalization
        let gener_quality = if size_reduction_ratio > 0.5 && pushing_power_ratio > 0.3 {
            0.3
        } else if size_reduction_ratio > 0.7 && pushing_power_ratio < 0.1 {
            -0.2
        } else {
            0.0
        };
        // bonus events: frontier push, complete generalization, high-level push
        let mut reward = size_reduction_ratio * 0.35 + push_quality * 0.45 + gener_quality;
        if pushed_frame >= level {
            reward += 0.4;
        }
        if generalized_cube_size == 1 {
            reward += 0.2;
        }
        if po.frame as f64 > 0.7 * level as f64 && pushing_power > 0.0 {
            reward += 0.1;
        }
        reward = reward.clamp(-0.5, 2.0);
        trace!("MAB arm {arm} got reward {reward:.2}");
        reward
    }

    /// LinUCB update, with A initialized to lambda I.
    pub fn train(&mut self, arm: usize, ctx: &Ic3MabVector, reward: f64) {
        self.a[arm] += ctx * ctx.transpose();
        self.b[arm] += ctx * reward;
        if let Some(inv) = self.a[arm].try_inverse() {
            self.theta[arm] = &inv * &self.b[arm];
            self.a_inv[arm] = inv;
        } else {
            warn!("MAB: matrix A for arm {arm} became non-invertible, resetting arm");
            self.a[arm] = Ic3MabMatrix::identity() * self.lambda;
            self.a_inv[arm] = Ic3MabMatrix::identity() / self.lambda;
            self.b[arm] = Ic3MabVector::zeros();
            self.theta[arm] = Ic3MabVector::zeros();
        }
    }
}
