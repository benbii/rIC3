use rIC3::{
    Btor, Engine, Lit, McResult, Var, VarRange,
    aig::{Aig, AigEdge},
    bmc::{BMC, BMCConfig},
    cadical::CaDiCaL,
    config::PreprocConfig,
    frontend::{Frontend, aig::AigFrontend, btor::BtorFrontend},
    ic3::{IC3, IC3Config},
    kind::{Kind, KindConfig},
    transys::{Transys, certify::Restore, unroll::TransysUnroll},
};
use std::sync::Arc;

// Equal initial latches; either preserve their equality or break it at depth 1.
// Both frontends must reserve the same kind of free slot, even without gate init.
fn models(gate_init: bool, unsafe_model: bool) -> [Transys; 2] {
    let mut aig = Aig::new();
    let i = AigEdge::from(aig.new_input());
    let j = AigEdge::from(aig.new_input());
    let a = aig.new_leaf_node();
    let b = aig.new_leaf_node();
    let init = if gate_init {
        aig.new_and_node(i, j)
    } else {
        AigEdge::constant(false)
    };
    aig.add_latch(a, b.into(), Some(init));
    aig.add_latch(b, AigEdge::from(b).not_if(unsafe_model), Some(init));
    let ab = aig.new_and_node(a.into(), !AigEdge::from(b));
    let ba = aig.new_and_node(!AigEdge::from(a), b.into());
    let bad = aig.trivial_new_or_node(ab, ba);
    aig.bads.extend([bad, b.into()]);

    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("init.btor2");
    let init_id = if gate_init { 6 } else { 7 };
    let next_id = if unsafe_model { 11 } else { 5 };
    std::fs::write(
        &path,
        format!(
            "1 sort bitvec 1\n2 input 1 i\n3 input 1 j\n4 state 1 a\n5 state 1 b\n\
             6 and 1 2 3\n7 zero 1\n8 init 1 4 {init_id}\n9 init 1 5 {init_id}\n\
             10 next 1 4 5\n11 not 1 5\n12 next 1 5 {next_id}\n\
             13 xor 1 4 5\n14 bad 13 equality\n15 bad 5 second\n"
        ),
    )
    .unwrap();
    [
        AigFrontend::new(aig).ts(),
        BtorFrontend::new(Btor::from_file(path)).ts(),
    ]
}

#[test]
fn reserved_slot_survives_property_cuts_sweeping_and_cache_roundtrip() {
    for gate_init in [false, true] {
        for ots in models(gate_init, false) {
            let original_iv = Restore::new(&ots).init_var();
            assert_eq!(
                original_iv.0,
                ots.latch.iter().map(|v| v.0).max().unwrap() + 1
            );
            assert!(!ots.is_latch(original_iv));
            assert!(ots.init(original_iv).is_none());
            for prop in 0..2 {
                for (scorr, frts) in [(false, false), (true, false), (false, true), (true, true)] {
                    let cfg = PreprocConfig {
                        prop,
                        local_proof: false,
                        scorr,
                        frts,
                        scorr_tl: 1,
                        frts_tl: 1,
                        preproc_file: None,
                        fake_preproc_wait: false,
                    };
                    let (ts, rst) = Transys::preproc(ots.clone_deep(), &cfg, Restore::new(&ots));
                    let data = bincode::serialize(&(ts, rst)).unwrap();
                    let (mut ts, mut rst): (Transys, Restore) =
                        bincode::deserialize(&data).unwrap();
                    let iv = rst.init_var();
                    assert_eq!(rst.restore_var(iv), original_iv);
                    assert_eq!(rst.forward(original_iv.lit()), iv.lit());
                    assert!(!ts.is_latch(iv));
                    assert!(ts.latch.iter().all(|&l| l < iv));
                    assert!(
                        VarRange::new_inclusive(Var(1), ts.max_var())
                            .filter(|&v| !ts.rel.clauses_of_var(v).is_empty())
                            .all(|v| v > iv)
                    );

                    let mut flat_rst = rst.clone();
                    let mut flat = ts.clone_deep().remove_dep();
                    flat.simplify(&mut flat_rst);
                    let flat_iv = flat_rst.init_var();
                    assert_eq!(flat_rst.restore_var(flat_iv), original_iv);
                    assert!(!flat.latch.contains(&flat_iv));

                    let needs_init = ts.has_gate_init();
                    let num_latch = ts.latch.len();
                    ts.remove_gate_init(&mut rst);
                    assert_eq!(rst.init_var(), iv);
                    assert_eq!(rst.restore_var(iv), original_iv);
                    assert_eq!(ts.latch.len(), num_latch + usize::from(needs_init));
                    assert!(!ts.has_gate_init());
                    if needs_init {
                        assert_eq!(ts.init(iv), Some(Lit::constant(true)));
                        assert_eq!(ts.next(iv.lit()), Lit::constant(false));
                    }
                    let lowered = bincode::serialize(&ts).unwrap();
                    ts.remove_gate_init(&mut rst);
                    assert_eq!(bincode::serialize(&ts).unwrap(), lowered);
                }
            }
        }
    }
}

#[test]
fn inn_skips_a_dormant_reserved_slot() {
    for gate_init in [false, true] {
        for mut ts in models(gate_init, false) {
            let mut rst = Restore::new(&ts);
            let iv = rst.init_var();
            ts.remove_gate_init(&mut rst);
            let mut uts = TransysUnroll::new(Arc::new(ts));
            uts.unroll(true);
            let inn = uts.internal_signals();
            assert_eq!(inn.is_latch(iv), gate_init);
            assert!(
                inn.latch
                    .iter()
                    .all(|&v| { uts.ts.is_latch(v) || !uts.ts.rel.clauses_of_var(v).is_empty() })
            );
        }
    }
}

#[test]
fn reserved_slot_preserves_engines_witnesses_and_ic3_proofs() {
    for gate_init in [false, true] {
        for unsafe_model in [false, true] {
            for ots in models(gate_init, unsafe_model) {
                let cfg = PreprocConfig {
                    prop: 0,
                    local_proof: false,
                    scorr: false,
                    frts: false,
                    scorr_tl: 1,
                    frts_tl: 1,
                    preproc_file: None,
                    fake_preproc_wait: false,
                };
                let (ts, rst) = Transys::preproc(ots.clone_deep(), &cfg, Restore::new(&ots));
                for mode in 0..10 {
                    let mut engine: Box<dyn Engine> = match mode {
                        0..=5 => Box::new(IC3::new(
                            IC3Config {
                                inn: mode >= 2,
                                pred_prop: mode % 2 == 1,
                                abs_cst: mode >= 4,
                                abs_trans: mode >= 4,
                                time_limit: 5,
                                ..Default::default()
                            },
                            ts.clone_deep(),
                            ots.clone_deep(),
                            rst.clone(),
                        )),
                        6..=7 => Box::new(Kind::new(
                            KindConfig {
                                end: 3,
                                simple_path: mode == 7,
                                skip_bmc: false,
                            },
                            ts.clone_deep(),
                            ots.clone_deep(),
                            rst.clone(),
                        )),
                        _ => Box::new(BMC::new(
                            BMCConfig {
                                end: 3,
                                kissat: mode == 9,
                                ..Default::default()
                            },
                            ts.clone_deep(),
                            ots.clone_deep(),
                            rst.clone(),
                        )),
                    };
                    let result = engine.check();
                    if unsafe_model {
                        assert!(
                            matches!(result, McResult::Unsafe(1)),
                            "mode {mode}: {result:?}"
                        );
                        let witness = engine.witness().into_bl().unwrap();
                        assert_eq!(witness.len(), 2);
                        assert_eq!(witness.bad_id, 0);
                        for state in &witness.state {
                            assert_eq!(state.len(), ots.latch.len());
                            assert!(state.iter().all(|l| ots.latch.contains(&l.var())));
                        }
                    } else if mode >= 8 {
                        assert!(matches!(result, McResult::Unknown(3)));
                    } else {
                        assert!(matches!(result, McResult::Safe), "mode {mode}: {result:?}");
                        if mode >= 6 {
                            continue;
                        }
                        let proof = engine.proof().into_bl().unwrap();
                        let mut base = CaDiCaL::new();
                        proof.load_init(&mut base);
                        proof.load_trans(&mut base, true);
                        assert!(!base.cad_solve(&proof.bad));
                        let mut uts = TransysUnroll::new(Arc::new(proof));
                        uts.unroll_to(1);
                        let mut step = CaDiCaL::new();
                        uts.load_trans(&mut step, 0, true);
                        uts.load_trans(&mut step, 1, true);
                        assert!(!step.cad_solve(&[!uts.ts.bad[0], uts.lit_next(uts.ts.bad[0], 1)]));
                    }
                }
            }
        }
    }
}
