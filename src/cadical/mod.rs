use logicrs::{Lit, LitVec, Var};
use std::ffi::{c_int, c_void};

unsafe extern "C" {
    fn cadical_solver_new() -> *mut c_void;
    fn cadical_solver_free(s: *mut c_void);
    fn cadical_solver_declare_more_variables(s: *mut c_void, count: c_int) -> c_int;
    fn cadical_solver_add_clause(s: *mut c_void, clause: *mut c_int, len: c_int);
    fn cadical_solver_solve(s: *mut c_void, assumps: *mut c_int, len: c_int) -> c_int;
    fn cadical_solver_simplify(s: *mut c_void) -> c_int;
    fn cadical_solver_freeze(s: *mut c_void, lit: c_int);
    fn cadical_solver_model_value(s: *mut c_void, lit: c_int) -> c_int;
    fn cadical_solver_conflict_has(s: *mut c_void, lit: c_int) -> bool;
    fn cadical_solver_clauses(s: *mut c_void, len: *mut c_int) -> *mut c_void;
    fn cadical_set_seed(s: *mut c_void, seed: c_int);
}

const CADICAL_MAX_SEED: u64 = 2_000_000_000;

fn cadical_seed(seed: u64) -> c_int {
    (seed % (CADICAL_MAX_SEED + 1)) as c_int
}

fn lit_to_cadical_lit(lit: &Lit) -> i32 {
    let mut res = Into::<usize>::into(lit.var()) as i32 + 1;
    if !lit.polarity() {
        res = -res;
    }
    res
}

fn cadical_lit_to_lit(lit: i32) -> Lit {
    let p = lit > 0;
    let v = Var::new(lit.unsigned_abs() as usize - 1);
    Lit::new(v, p)
}

pub struct CaDiCaL {
    solver: *mut c_void,
    num_var: usize,
}

impl CaDiCaL {
    pub fn new() -> Self {
        Self {
            solver: unsafe { cadical_solver_new() },
            num_var: 0,
        }
    }

    pub fn new_var_to(&mut self, var: Var) {
        let target = usize::from(var) + 1;
        if target <= self.num_var {
            return;
        }
        let count = target - self.num_var;
        let count = c_int::try_from(count).expect("too many CaDiCaL variables");
        let declared = unsafe { cadical_solver_declare_more_variables(self.solver, count) };
        self.num_var = target;
        assert_eq!(declared as usize, self.num_var);
    }

    #[inline]
    pub fn add_clause(&mut self, clause: &[Lit]) {
        let clause: Vec<i32> = clause.iter().map(lit_to_cadical_lit).collect();
        unsafe { cadical_solver_add_clause(self.solver, clause.as_ptr() as _, clause.len() as _) }
    }

    pub fn cad_solve(&mut self, assumps: &[Lit]) -> bool {
        let assumps: Vec<i32> = assumps.iter().map(lit_to_cadical_lit).collect();
        match unsafe {
            cadical_solver_solve(self.solver, assumps.as_ptr() as _, assumps.len() as _)
        } {
            10 => true,
            20 => false,
            _ => todo!(),
        }
    }

    pub fn cad_satval(&self, lit: Lit) -> Option<bool> {
        let lit = lit_to_cadical_lit(&lit);
        let res = unsafe { cadical_solver_model_value(self.solver, lit) };
        if res == lit {
            Some(true)
        } else if res == -lit {
            Some(false)
        } else {
            None
        }
    }

    pub fn unsat_has(&self, lit: Lit) -> bool {
        let lit = lit_to_cadical_lit(&lit);
        unsafe { cadical_solver_conflict_has(self.solver, lit) }
    }

    pub fn simplify(&mut self) -> Option<bool> {
        match unsafe { cadical_solver_simplify(self.solver) } {
            10 => Some(true),
            20 => Some(false),
            _ => None,
        }
    }

    pub fn set_frozen(&mut self, var: Var, frozen: bool) {
        assert!(frozen);
        unsafe { cadical_solver_freeze(self.solver, lit_to_cadical_lit(&var.lit())) }
    }

    pub fn clauses(&self) -> Vec<LitVec> {
        let mut cnf = Vec::new();
        unsafe {
            let mut len = 0;
            let clauses: *mut usize = cadical_solver_clauses(self.solver, &mut len as *mut _) as _;
            if len > 0 {
                let clauses = Vec::from_raw_parts(clauses, len as _, len as _);
                for i in (0..clauses.len()).step_by(2) {
                    let data = clauses[i] as *mut i32;
                    let len = clauses[i + 1];
                    let cls: Vec<_> = (0..len).map(|i| *data.add(i)).collect();
                    cnf.push(LitVec::from_iter(cls.into_iter().map(cadical_lit_to_lit)));
                }
            }
        }
        cnf
    }

    pub fn set_seed(&mut self, seed: u64) {
        unsafe { cadical_set_seed(self.solver, cadical_seed(seed)) }
    }
}

impl Drop for CaDiCaL {
    fn drop(&mut self) {
        unsafe { cadical_solver_free(self.solver) };
    }
}

impl Default for CaDiCaL {
    fn default() -> Self {
        Self::new()
    }
}

#[test]
fn seed_conversion_stays_in_range() {
    assert_eq!(cadical_seed(0), 0);
    assert_eq!(cadical_seed(CADICAL_MAX_SEED), 2_000_000_000);
    assert_eq!(cadical_seed(CADICAL_MAX_SEED + 1), 0);
    assert_eq!(cadical_seed(u64::MAX), 486_179_583);
}

#[test]
fn test() {
    use logicrs::LitVec;
    let mut solver = CaDiCaL::new();
    solver.new_var_to(Var(2));
    let lit0 = Var(0).lit();
    let lit1 = Var(1).lit();
    let lit2 = Var(2).lit();
    solver.add_clause(&LitVec::from([lit0, !lit2]));
    solver.add_clause(&LitVec::from([lit1, !lit2]));
    solver.add_clause(&LitVec::from([!lit0, !lit1, lit2]));
    if solver.cad_solve(&[lit2]) {
        assert!(solver.cad_satval(lit0).unwrap());
        assert!(solver.cad_satval(lit1).unwrap());
        assert!(solver.cad_satval(lit2).unwrap());
    } else {
        panic!()
    }
}
