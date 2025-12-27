use btor::Btor;
use giputils::hash::GHashMap;
use logicrs::fol::{self, BvTermValue, TermValue};
use rIC3::{
    frontend::{btor::BtorFrontend, Frontend},
    wltransys::certify::WlWitness,
};
use std::{fs, mem::take, path::Path};

use super::state::LastRunState;

/// Translate all old CTIs to new model coordinates.
/// Returns: Map of property_name -> translated WlWitness (only for properties that still exist)
pub fn translate_old_ctis(
    old_state: &LastRunState,
    dut_old: &Path,
    dut_new: &Path,
) -> anyhow::Result<GHashMap<String, WlWitness>> {
    if !dut_old.exists() || old_state.ctis.is_empty() {
        return Ok(GHashMap::default());
    }

    // Load old model
    let btor_old = Btor::from_file(dut_old.join("dut.btor"));
    let btorfe_old = BtorFrontend::new(btor_old.clone());
    let ywbc_old = fs::read_to_string(dut_old.join("dut.ywb"))?;
    let ywb_old = btor_old.ywb(&ywbc_old);
    let wb_old = btor_old.witness_map(&ywbc_old);
    // Invert: signal_name -> old_term
    let wb_old: GHashMap<_, _> = wb_old.into_iter().map(|(k, v)| (v, k)).collect();

    // Load new model
    let btor_new = Btor::from_file(dut_new.join("dut.btor"));
    let ywbc_new = fs::read_to_string(dut_new.join("dut.ywb"))?;
    let ywb_new = btor_new.ywb(&ywbc_new);
    let wb_new = btor_new.witness_map(&ywbc_new);

    // Build term mapping: old_term -> new_term (via signal name)
    let mut term_map = GHashMap::new();
    for (new_term, signal_name) in wb_new {
        if let Some(old_term) = wb_old.get(&signal_name) {
            term_map.insert(old_term.clone(), new_term);
        }
    }

    // Translate each CTI
    let mut result = GHashMap::default();
    for (prop_name, old_cti_str) in &old_state.ctis {
        // Deserialize old CTI
        let mut cti = btorfe_old.deserialize_wl_unsafe_certificate(old_cti_str.clone());

        // Find new bad_id by matching assertion name
        let old_bad_name = &ywb_old.asserts[cti.bad_id];
        let Some(new_bad_id) = ywb_new.asserts.iter().position(|s| s == old_bad_name) else {
            continue; // Property was removed
        };
        cti.bad_id = new_bad_id;

        // Remap terms
        for k in 0..cti.len() {
            for x in take(&mut cti.input[k]) {
                if let Some(n) = term_map.get(x.t()) {
                    cti.input[k].push(BvTermValue::new(n.clone(), x.v().clone()));
                }
            }
            for x in take(&mut cti.state[k]) {
                if let Some(n) = term_map.get(x.t()) {
                    let x = x.into_bv();
                    cti.state[k].push(TermValue::new(n.clone(), fol::Value::Bv(x.v().clone())));
                }
            }
        }

        result.insert(prop_name.clone(), cti);
    }

    Ok(result)
}

/// When model unchanged, deserialize CTIs directly (no translation needed)
pub fn deserialize_ctis_direct(
    old_state: &LastRunState,
    dut: &Path,
) -> anyhow::Result<GHashMap<String, WlWitness>> {
    let btor = Btor::from_file(dut.join("dut.btor"));
    let btorfe = BtorFrontend::new(btor);

    let mut result = GHashMap::default();
    for (prop_name, cti_str) in &old_state.ctis {
        let cti = btorfe.deserialize_wl_unsafe_certificate(cti_str.clone());
        result.insert(prop_name.clone(), cti);
    }
    Ok(result)
}
