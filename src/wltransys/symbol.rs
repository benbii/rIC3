use ahash::HashMap;
use logicrs::fol::Term;
use std::ops::Deref;

#[derive(Debug, Clone)]
pub struct WlTsSymbol {
    pub signal: HashMap<Term, Vec<String>>,
    pub prop: Vec<String>,
}

impl Deref for WlTsSymbol {
    type Target = HashMap<Term, Vec<String>>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.signal
    }
}
