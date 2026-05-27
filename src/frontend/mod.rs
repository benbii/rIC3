use crate::{
    McProof, McWitness,
    transys::Transys,
    wltransys::{WlTransys, symbol::WlTsSymbol},
};
use std::{fmt::Display, path::Path};

pub mod aig;
pub mod btor;

pub trait Frontend {
    fn ts(&mut self) -> Transys;
    fn wts(&mut self) -> (WlTransys, WlTsSymbol) {
        panic!("frontend unsupported for wltransys")
    }
    fn safe_certificate(&mut self, proof: McProof) -> Box<dyn Display>;
    fn unsafe_certificate(&mut self, witness: McWitness) -> Box<dyn Display>;
    fn certify(&mut self, model: &Path, cert: &Path) -> bool;
}
