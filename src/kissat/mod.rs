use logicrs::{Lit, Var};
use std::ffi::{CString, c_char, c_int, c_void};

unsafe extern "C" {
    fn kissat_init() -> *mut c_void;
    fn kissat_release(s: *mut c_void);
    fn kissat_add(s: *mut c_void, lit: c_int);
    fn kissat_solve(s: *mut c_void) -> c_int;
    fn kissat_value(s: *mut c_void, lit: c_int) -> c_int;
    fn kissat_set_option(s: *mut c_void, op: *mut c_char, v: c_int) -> c_int;
}

fn kissat_seed(seed: u64) -> c_int {
    (seed & i32::MAX as u64) as c_int
}

fn lit_to_kissat_lit(lit: &Lit) -> i32 {
    let mut res = Into::<usize>::into(lit.var()) as i32 + 1;
    if !lit.polarity() {
        res = -res;
    }
    res
}

pub struct Kissat {
    solver: *mut c_void,
    num_var: usize,
}

impl Kissat {
    pub fn new() -> Self {
        let solver = unsafe { kissat_init() };
        #[allow(dangling_pointers_from_temporaries)]
        unsafe {
            kissat_set_option(solver, CString::new("quiet").unwrap().as_ptr() as *mut _, 1)
        };
        Self { solver, num_var: 0 }
    }

    pub fn new_var_to(&mut self, n: Var) {
        self.num_var = self.num_var.max(usize::from(n) + 1);
    }

    #[inline]
    pub fn add_clause(&mut self, clause: &[Lit]) {
        for lit in clause.iter().map(lit_to_kissat_lit) {
            unsafe { kissat_add(self.solver, lit) };
        }
        unsafe { kissat_add(self.solver, 0) };
    }

    pub fn ksat_solve(&mut self, assumps: &[Lit]) -> bool {
        debug_assert!(assumps.is_empty());
        match unsafe { kissat_solve(self.solver) } {
            10 => true,
            20 => false,
            _ => unreachable!(),
        }
    }

    pub fn ksat_satval(&self, lit: Lit) -> Option<bool> {
        let lit = lit_to_kissat_lit(&lit);
        let res = unsafe { kissat_value(self.solver, lit) };
        if res == lit {
            Some(true)
        } else if res == -lit {
            Some(false)
        } else {
            None
        }
    }

    pub fn set_seed(&mut self, seed: u64) {
        unsafe {
            kissat_set_option(
                self.solver,
                CString::new("seed").unwrap().as_ptr() as *mut _,
                kissat_seed(seed),
            )
        };
    }
}

impl Drop for Kissat {
    fn drop(&mut self) {
        unsafe { kissat_release(self.solver) }
    }
}

impl Default for Kissat {
    fn default() -> Self {
        Self::new()
    }
}

#[test]
fn seed_conversion_stays_in_range() {
    assert_eq!(kissat_seed(0), 0);
    assert_eq!(kissat_seed(i32::MAX as u64), i32::MAX);
    assert_eq!(kissat_seed(i32::MAX as u64 + 1), 0);
    assert_eq!(kissat_seed(u64::MAX), i32::MAX);
}

#[test]
fn test() {
    let mut solver = Kissat::new();
    solver.new_var_to(Var(2));
    let lit0 = Var(0).lit();
    let lit1 = Var(1).lit();
    let lit2 = Var(2).lit();
    solver.add_clause(&[lit0, !lit2]);
    solver.add_clause(&[lit1, !lit2]);
    solver.add_clause(&[!lit0, !lit1, lit2]);
    solver.add_clause(&[lit2]);
    if solver.ksat_solve(&[]) {
        assert!(solver.ksat_satval(lit0).unwrap());
        assert!(solver.ksat_satval(lit1).unwrap());
        assert!(solver.ksat_satval(lit2).unwrap());
    } else {
        panic!()
    }
}
