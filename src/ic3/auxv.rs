use crate::ic3::IC3;
use crate::RseedSet as HashSet;
use logicrs::{DagCnf, Var};

impl IC3 {
    pub fn add_aux(&mut self, rel: &DagCnf, auxs: &HashSet<Var>) {
        self.ts.add_aux(rel, auxs);
        self.activity.reserve(self.ts.max_var());
        self.tsctx = Box::new(self.ts.ctx());
        self.frame.reserve(self.tsctx.max_latch);
    }
}
