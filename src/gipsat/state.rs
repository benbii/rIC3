use logicrs::{Lbool, Lit, Var, VarMap};

const VALUE_MASK: u8 = 0b0000_0011;
const PHASE_MASK: u8 = 0b0000_1100;
const IN_DOMAIN: u8 = 0b0001_0000;
const IN_BUCKET: u8 = 0b0010_0000;

#[derive(Clone, Copy)]
pub(super) struct State(u8);

impl State {
    #[inline]
    pub(super) fn lit_value(self, lit: Lit) -> Lbool {
        Lbool((self.0 & VALUE_MASK) ^ (!lit.polarity() as u8))
    }

    #[inline]
    pub(super) fn value(self) -> Lbool {
        Lbool(self.0 & VALUE_MASK)
    }

    #[inline]
    pub(super) fn phase(self) -> Lbool {
        Lbool((self.0 & PHASE_MASK) >> 2)
    }

    #[inline]
    pub(super) fn in_domain(self) -> bool {
        self.0 & IN_DOMAIN != 0
    }

    #[inline]
    pub(super) fn domain_value(self, lit: Lit) -> (bool, Lbool) {
        let key = (self.0 & (IN_DOMAIN | VALUE_MASK)) ^ lit.polarity() as u8;
        (key <= IN_DOMAIN, Lbool((key & VALUE_MASK) ^ 1))
    }
}

impl Default for State {
    #[inline]
    fn default() -> Self {
        Self(Lbool::NONE.0 | (Lbool::NONE.0 << 2))
    }
}

#[derive(Clone)]
pub(super) struct VarState {
    state: VarMap<State>,
}

impl VarState {
    pub(super) fn new_with(var: Var) -> Self {
        let mut res = Self {
            state: VarMap::new_with(var),
        };
        res.set(Lit::constant(true));
        res
    }

    #[inline]
    pub(super) fn get(&self, var: Var) -> State {
        self.state[var]
    }

    #[inline]
    pub(super) fn lit_value(&self, lit: Lit) -> Lbool {
        self.get(lit.var()).lit_value(lit)
    }

    #[inline]
    pub(super) fn value(&self, var: Var) -> Lbool {
        self.get(var).value()
    }

    #[inline]
    pub(super) fn set(&mut self, lit: Lit) {
        let state = &mut self.state[lit.var()].0;
        *state = (*state & !VALUE_MASK) | lit.polarity() as u8;
    }

    #[inline]
    pub(super) fn set_none(&mut self, var: Var) {
        let state = &mut self.state[var].0;
        *state = (*state & !VALUE_MASK) | Lbool::NONE.0;
    }

    #[inline]
    pub(super) fn unassign_save_phase(&mut self, var: Var, phase: bool) {
        let state = &mut self.state[var].0;
        *state = (*state & !(VALUE_MASK | PHASE_MASK)) | Lbool::NONE.0 | ((phase as u8) << 2);
    }

    #[inline]
    pub(super) fn insert_domain(&mut self, var: Var) -> bool {
        let state = &mut self.state[var].0;
        let was_in_domain = *state & IN_DOMAIN != 0;
        *state |= IN_DOMAIN;
        !was_in_domain
    }

    #[inline]
    pub(super) fn remove_domain(&mut self, var: Var) {
        self.state[var].0 &= !IN_DOMAIN;
    }

    #[inline]
    pub(super) fn insert_bucket(&mut self, var: Var) -> bool {
        let state = &mut self.state[var].0;
        if *state & IN_BUCKET != 0 {
            false
        } else {
            *state |= IN_BUCKET;
            true
        }
    }

    #[inline]
    pub(super) fn remove_bucket(&mut self, var: Var) {
        self.state[var].0 &= !IN_BUCKET;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fields_do_not_clobber_each_other() {
        assert_eq!(std::mem::size_of::<State>(), 1);

        let var = Var::new(1);
        let mut states = VarState::new_with(var);
        let initial = states.get(var);
        assert!(initial.value().is_none());
        assert!(initial.phase().is_none());
        assert!(!initial.in_domain());
        assert_eq!(initial.0 & IN_BUCKET, 0);

        assert!(states.insert_domain(var));
        assert!(states.insert_bucket(var));
        states.set(Lit::new(var, true));
        let assigned = states.get(var);
        assert_eq!(assigned.value(), Lbool::TRUE);
        assert!(assigned.in_domain());
        assert_ne!(assigned.0 & IN_BUCKET, 0);

        states.unassign_save_phase(var, false);
        let unassigned = states.get(var);
        assert!(unassigned.value().is_none());
        assert_eq!(unassigned.phase(), Lbool::FALSE);
        assert!(unassigned.in_domain());
        assert_ne!(unassigned.0 & IN_BUCKET, 0);

        states.remove_domain(var);
        states.remove_bucket(var);
        assert_eq!(states.get(var).0 & 0b1111_0000, 0);
    }

    #[test]
    fn branchless_domain_value_matches_reference() {
        let var = Var::new(1);
        for raw_state in u8::MIN..=u8::MAX {
            let state = State(raw_state);
            for polarity in [false, true] {
                let lit = Lit::new(var, polarity);
                let (skip, value) = state.domain_value(lit);
                assert_eq!(value, state.lit_value(lit));
                assert_eq!(skip, value == Lbool::TRUE || !state.in_domain());
            }
        }
    }
}
