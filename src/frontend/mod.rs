use crate::{McProof, McWitness, transys::Transys, wltransys::WlTransys};
use std::path::Path;

pub mod aig;
pub mod btor;

pub trait Frontend {
    fn ts(&mut self) -> Transys;
    fn wts(&mut self) -> WlTransys {
        panic!("frontend unsupported for wltransys")
    }
    fn safe_certificate(&mut self, model: &Path, proof: McProof) -> String;
    fn unsafe_certificate(&mut self, model: &Path, witness: McWitness) -> String;
    fn certify(&mut self, model: &Path, cert: &Path) -> bool;
}
