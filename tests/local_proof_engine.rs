use rIC3::{
    Engine, Lit, LitVec, McResult, McWitness, Var,
    bmc::{BMC, BMCConfig},
    config::PreprocConfig,
    ic3::{IC3, IC3Config},
    kind::{Kind, KindConfig},
    transys::{Transys, certify::Restore},
};
use std::collections::HashSet;

fn preproc_config(prop: usize, local_proof: bool) -> PreprocConfig {
    PreprocConfig {
        prop,
        local_proof,
        scorr: false,
        scorr_tl: 0,
        frts: false,
        frts_tl: 0,
        preproc_file: None,
        fake_preproc_wait: false,
    }
}

// Exercise the same normalized model and restoration metadata in every bit-level
// engine, including INN and both BMC backends. BMC cannot prove safety.
fn check_engines(ots: &Transys, cfg: &PreprocConfig, expected: McResult, bad_id: usize) {
    let rst = Restore::new(ots);
    let (ts, rst) = Transys::preproc(ots.clone_deep(), cfg, rst);
    for mode in 0..7 {
        let mut engine: Box<dyn Engine> = match mode {
            0..=3 => Box::new(IC3::new(
                IC3Config {
                    inn: mode >= 2,
                    pred_prop: mode % 2 == 1,
                    time_limit: 5,
                    ..Default::default()
                },
                ts.clone_deep(),
                ots.clone_deep(),
                rst.clone(),
            )),
            4 => Box::new(Kind::new(
                KindConfig {
                    end: 4,
                    ..Default::default()
                },
                ts.clone_deep(),
                ots.clone_deep(),
                rst.clone(),
            )),
            _ => Box::new(BMC::new(
                BMCConfig {
                    kissat: mode == 6,
                    end: 4,
                    ..Default::default()
                },
                ts.clone_deep(),
                ots.clone_deep(),
                rst.clone(),
            )),
        };
        let result = engine.check();
        match (expected, result) {
            (McResult::Unsafe(d), McResult::Unsafe(actual)) => {
                assert_eq!(d, actual, "engine mode {mode}");
                let McWitness::Bl(witness) = engine.witness() else {
                    panic!("expected a bit-level witness");
                };
                assert_eq!(witness.bad_id, bad_id, "engine mode {mode}");
                assert_eq!(witness.len(), d + 1, "engine mode {mode}");
            }
            (McResult::Safe, McResult::Safe) if mode < 5 => (),
            (McResult::Safe, McResult::Unknown(4)) if mode >= 5 => (),
            _ => panic!("engine mode {mode}: expected {expected:?}, got {result:?}"),
        }
    }
}

#[test]
fn helper_selection_closes_transitively_and_ignores_constants() {
    let mut ts = Transys::new();
    let a = ts.new_var();
    let b = ts.new_var();
    let c = ts.new_var();
    let unrelated = ts.new_var();
    ts.input.extend([a, b, c, unrelated]);
    let bc = !ts.rel_mut().new_xnor(b.lit(), c.lit());
    let ab = !ts.rel_mut().new_xnor(a.lit(), b.lit());
    // The connection to c is encountered before the bridge to the target.
    ts.bad = LitVec::from([
        c.lit(),
        unrelated.lit(),
        bc,
        a.lit(),
        ab,
        Lit::constant(false),
    ]);
    let rst = Restore::new(&ts);
    let (prepared, rst) = Transys::preproc(ts.clone_deep(), &preproc_config(3, true), rst);
    assert_eq!(prepared.bad.len(), 4);
    assert_eq!(
        prepared
            .bad
            .iter()
            .map(|&bad| rst.restore(bad))
            .collect::<Vec<_>>(),
        [ts.bad[3], ts.bad[0], ts.bad[2], ts.bad[4]],
    );
    assert!(rst.try_forward(unrelated.lit()).is_none());
    assert!(prepared.constraint.is_empty());
}

#[test]
fn helper_selection_follows_next_and_nonconstant_init() {
    let mut ts = Transys::new();
    let a = ts.new_var();
    let b = ts.new_var();
    let init = ts.new_var();
    let unrelated = ts.new_var();
    ts.add_input(init);
    ts.add_latch(a, Some(init.lit()), b.lit());
    ts.add_latch(b, Some(Lit::constant(false)), b.lit());
    ts.add_latch(unrelated, Some(Lit::constant(false)), unrelated.lit());
    ts.bad = LitVec::from([unrelated.lit(), b.lit(), init.lit(), a.lit()]);
    let rst = Restore::new(&ts);
    let (prepared, rst) = Transys::preproc(ts.clone_deep(), &preproc_config(3, true), rst);
    assert_eq!(prepared.bad.len(), 3);
    assert_eq!(
        prepared
            .bad
            .iter()
            .map(|&bad| rst.restore(bad))
            .collect::<Vec<_>>(),
        [ts.bad[3], ts.bad[1], ts.bad[2]],
    );
    assert!(rst.try_forward(unrelated.lit()).is_none());
}

#[test]
fn constraints_bridge_cones_without_seeding_unrelated_components() {
    let mut ts = Transys::new();
    let a = ts.new_var();
    let b = ts.new_var();
    let c = ts.new_var();
    let d = ts.new_var();
    ts.input.extend([a, b, c, d]);
    let ab = ts.rel_mut().new_xnor(a.lit(), b.lit());
    let cd = ts.rel_mut().new_xnor(c.lit(), d.lit());
    ts.constraint = LitVec::from([ab, cd]);
    ts.bad = LitVec::from([a.lit(), b.lit(), c.lit(), d.lit()]);
    let rst = Restore::new(&ts);
    let (prepared, rst) = Transys::preproc(ts.clone_deep(), &preproc_config(0, true), rst);
    assert_eq!(prepared.bad.len(), 2);
    assert_eq!(
        prepared
            .bad
            .iter()
            .map(|&bad| rst.restore(bad))
            .collect::<Vec<_>>(),
        [ts.bad[0], ts.bad[1]],
    );
    // Pruning helpers does not remove real environmental constraints.
    assert_eq!(prepared.constraint.len(), 2);
    assert!(rst.try_forward(c.lit()).is_some());
    assert!(rst.try_forward(d.lit()).is_some());
}

#[test]
fn overlapping_components_match_explicit_fanin_fixed_point() {
    use rand::{RngExt, SeedableRng, rngs::SmallRng};
    let mut rng = SmallRng::seed_from_u64(73);
    for _ in 0..24 {
        let mut ts = Transys::new();
        let vars: Vec<_> = (0..12).map(|_| ts.new_var()).collect();
        ts.input.extend_from_slice(&vars[8..]);
        for &v in &vars[..8] {
            let next = vars[rng.random_range(0..vars.len())].lit();
            let init = if rng.random_bool(0.5) {
                Lit::constant(false)
            } else {
                vars[rng.random_range(8..vars.len())].lit()
            };
            ts.add_latch(v, Some(init), next);
        }
        for _ in 0..8 {
            let a = vars[rng.random_range(0..vars.len())].lit();
            let b = vars[rng.random_range(0..vars.len())].lit();
            let bad = ts.rel_mut().new_and([a, b]);
            ts.bad.push(bad);
        }
        let constraint = ts.rel_mut().new_xnor(vars[0].lit(), vars[11].lit());
        ts.constraint.push(constraint);
        let cones: Vec<HashSet<Var>> = ts
            .bad
            .iter()
            .chain(ts.constraint.iter())
            .map(|root| {
                let mut cone = HashSet::new();
                let mut pending = vec![root.var()];
                while let Some(v) = pending.pop() {
                    if v.is_constant() || !cone.insert(v) {
                        continue;
                    }
                    pending.extend_from_slice(ts.rel.dep(v));
                    if ts.is_latch(v) {
                        pending.push(ts.var_next_lit(v).var());
                    }
                    if let Some(init) = ts.init(v) {
                        pending.push(init.var());
                    }
                }
                cone
            })
            .collect();
        for prop in 0..ts.bad.len() {
            let mut cut = cones[prop].clone();
            loop {
                let previous = cut.len();
                for cone in &cones {
                    if !cut.is_disjoint(cone) {
                        cut.extend(cone);
                    }
                }
                if cut.len() == previous {
                    break;
                }
            }
            let expected: Vec<_> = (0..ts.bad.len())
                .filter(|&i| i != prop && !cut.is_disjoint(&cones[i]))
                .collect();
            let rst = Restore::new(&ts);
            let (prepared, rst) =
                Transys::preproc(ts.clone_deep(), &preproc_config(prop, true), rst);
            let actual: Vec<_> = prepared
                .bad
                .iter()
                .skip(1)
                .map(|&bad| rst.restore(bad))
                .collect();
            assert_eq!(
                actual,
                expected.iter().map(|&i| ts.bad[i]).collect::<Vec<_>>()
            );
        }
    }
}

#[test]
fn single_property_local_proof_is_an_exact_preprocessing_noop() {
    let mut ts = Transys::new();
    let a = ts.new_var();
    ts.add_latch(a, Some(Lit::constant(false)), Lit::constant(true));
    ts.bad = LitVec::from(a.lit());
    for prop in [0, usize::MAX] {
        let mut baseline = None;
        for local_proof in [false, true] {
            let rst = Restore::new(&ts);
            let result = Transys::preproc(ts.clone_deep(), &preproc_config(prop, local_proof), rst);
            assert_eq!(result.0.bad.len(), 1);
            let bytes = bincode::serialize(&result).unwrap();
            if let Some(baseline) = &baseline {
                assert_eq!(baseline, &bytes);
            } else {
                baseline = Some(bytes);
            }
            check_engines(
                &ts,
                &preproc_config(prop, local_proof),
                McResult::Unsafe(1),
                0,
            );
        }
    }
}

#[test]
fn endpoint_failures_do_not_assume_helpers_and_preserve_selected_id() {
    let mut ts = Transys::new();
    let a = ts.new_var();
    ts.add_latch(a, Some(Lit::constant(false)), Lit::constant(true));
    ts.bad = LitVec::from([a.lit(), a.lit()]);
    for local_proof in [false, true] {
        check_engines(&ts, &preproc_config(1, local_proof), McResult::Unsafe(1), 1);
    }
    // Both assertions also fail initially; the initial query must stay unguarded.
    ts.add_init(a, Lit::constant(true));
    check_engines(&ts, &preproc_config(1, true), McResult::Unsafe(0), 1);
}

#[test]
fn compressed_target_reports_the_original_failing_property() {
    let mut ts = Transys::new();
    let a = ts.new_var();
    let b = ts.new_var();
    ts.add_latch(a, Some(Lit::constant(false)), a.lit());
    ts.add_latch(b, Some(Lit::constant(false)), Lit::constant(true));
    // A real OR node is introduced, not just OR(false, b) simplified to b.
    ts.bad = LitVec::from([a.lit(), b.lit()]);
    check_engines(
        &ts,
        &preproc_config(usize::MAX, false),
        McResult::Unsafe(1),
        1,
    );
    check_engines(&ts, &preproc_config(0, false), McResult::Safe, 0);
    ts.bad[0] = Lit::constant(false);
    let rst = Restore::new(&ts);
    let (prepared, rst) = Transys::preproc(ts, &preproc_config(0, true), rst);
    assert_eq!(prepared.bad.len(), 1);
    assert!(prepared.bad[0].is_constant(false));
    assert_eq!(rst.restore(prepared.bad[0]), Lit::constant(false));
}

#[test]
fn local_proof_keeps_endpoint_failures_through_scorr_and_frts() {
    let mut ts = Transys::new();
    let a = ts.new_var();
    let duplicate = ts.new_var();
    ts.add_latch(a, Some(Lit::constant(false)), Lit::constant(true));
    ts.add_latch(duplicate, Some(Lit::constant(false)), Lit::constant(true));
    let target = ts.rel_mut().new_or([a.lit(), duplicate.lit()]);
    ts.bad = LitVec::from([a.lit(), target]);
    for scorr in [false, true] {
        for frts in [false, true] {
            let mut cfg = preproc_config(1, true);
            cfg.scorr = scorr;
            cfg.frts = frts;
            cfg.scorr_tl = 1;
            cfg.frts_tl = 1;
            check_engines(&ts, &cfg, McResult::Unsafe(1), 1);
        }
    }
}

#[test]
fn ic3_local_proof_composes_with_local_abstraction() {
    for unsafe_model in [false, true] {
        let mut ts = Transys::new();
        let a = ts.new_var();
        let b = ts.new_var();
        ts.add_latch(a, Some(Lit::constant(false)), b.lit());
        ts.add_latch(b, Some(Lit::constant(false)), Lit::constant(unsafe_model));
        // Helper b is correct in the safe case. In the unsafe case both
        // assertions fail together at frame 1, which must remain visible.
        let target = ts.rel_mut().new_or([a.lit(), b.lit()]);
        ts.bad = LitVec::from([target, b.lit()]);
        for inn in [false, true] {
            for (abs_cst, abs_trans) in [(true, false), (false, true), (true, true)] {
                let rst = Restore::new(&ts);
                let (prepared, rst) =
                    Transys::preproc(ts.clone_deep(), &preproc_config(0, true), rst);
                let mut ic3 = IC3::new(
                    IC3Config {
                        inn,
                        abs_cst,
                        abs_trans,
                        time_limit: 5,
                        ..Default::default()
                    },
                    prepared,
                    ts.clone_deep(),
                    rst,
                );
                let result = ic3.check();
                assert!(
                    matches!(
                        (unsafe_model, result),
                        (false, McResult::Safe) | (true, McResult::Unsafe(1))
                    ),
                    "inn={inn}, abs_cst={abs_cst}, abs_trans={abs_trans}: {result:?}"
                );
                if unsafe_model {
                    let McWitness::Bl(witness) = ic3.witness() else {
                        panic!()
                    };
                    assert_eq!(witness.bad_id, 0);
                }
            }
        }
    }
}

#[test]
fn helpers_strengthen_kind_but_are_not_additional_targets() {
    let mut ts = Transys::new();
    let a = ts.new_var();
    let b = ts.new_var();
    ts.add_latch(a, Some(Lit::constant(false)), b.lit());
    ts.add_latch(b, Some(Lit::constant(false)), b.lit());
    ts.bad = LitVec::from([a.lit(), b.lit()]);
    for local_proof in [false, true] {
        let rst = Restore::new(&ts);
        let (prepared, rst) =
            Transys::preproc(ts.clone_deep(), &preproc_config(0, local_proof), rst);
        let mut kind = Kind::new(
            KindConfig {
                end: 1,
                ..Default::default()
            },
            prepared,
            ts.clone_deep(),
            rst,
        );
        assert!(matches!(
            (local_proof, kind.check()),
            (true, McResult::Safe) | (false, McResult::Unknown(1))
        ));
    }
    // A wrong helper blocks the prefix for target a, but is itself still unsafe.
    ts.add_init(b, Lit::constant(true));
    check_engines(&ts, &preproc_config(0, true), McResult::Safe, 0);
    check_engines(&ts, &preproc_config(1, true), McResult::Unsafe(0), 1);
}

#[test]
fn bmc_helpers_cover_skipped_bounds_and_kissat_rebuilds() {
    let mut ts = Transys::new();
    let a = ts.new_var();
    let b = ts.new_var();
    let c = ts.new_var();
    ts.add_latch(a, Some(Lit::constant(false)), Lit::constant(true));
    ts.add_latch(b, Some(Lit::constant(false)), a.lit());
    ts.add_latch(c, Some(Lit::constant(false)), b.lit());
    let helper = ts.rel_mut().new_and([a.lit(), !b.lit()]);
    ts.bad = LitVec::from([c.lit(), helper]);
    // Target fails from frame 3 onward; helper fails only in frame 1.
    for local_proof in [false, true] {
        for kissat in [false, true] {
            for (start, step) in [(0, 1), (0, 3), (3, 1)] {
                let rst = Restore::new(&ts);
                let (prepared, rst) =
                    Transys::preproc(ts.clone_deep(), &preproc_config(0, local_proof), rst);
                let mut bmc = BMC::new(
                    BMCConfig {
                        start,
                        step,
                        end: 4,
                        kissat,
                        ..Default::default()
                    },
                    prepared,
                    ts.clone_deep(),
                    rst,
                );
                assert!(
                    matches!(
                        (local_proof, bmc.check()),
                        (true, McResult::Unknown(4)) | (false, McResult::Unsafe(3))
                    ),
                    "local={local_proof}, kissat={kissat}, start={start}, step={step}"
                );
            }
        }
    }
}

#[test]
fn cache_roundtrip_keeps_target_and_helper_identities() {
    let mut ts = Transys::new();
    let a = ts.new_var();
    ts.add_latch(a, Some(Lit::constant(false)), Lit::constant(true));
    ts.bad = LitVec::from([a.lit(), a.lit()]);
    let rst = Restore::new(&ts);
    let (prepared, rst) = Transys::preproc(ts.clone_deep(), &preproc_config(1, true), rst);
    let mut bytes = Vec::new();
    bincode::serialize_into(&mut bytes, &prepared).unwrap();
    bincode::serialize_into(&mut bytes, &rst).unwrap();
    bincode::serialize_into(&mut bytes, &12u64).unwrap();
    let mut reader = std::io::Cursor::new(bytes);
    let prepared: Transys = bincode::deserialize_from(&mut reader).unwrap();
    let rst: Restore = bincode::deserialize_from(&mut reader).unwrap();
    let elapsed: u64 = bincode::deserialize_from(&mut reader).unwrap();
    assert_eq!(elapsed, 12);
    assert_eq!(prepared.bad.len(), 2);
    assert_eq!(rst.restore(prepared.bad[0]), ts.bad[1]);
    assert_eq!(rst.restore(prepared.bad[1]), ts.bad[0]);
    let mut kind = Kind::new(KindConfig::default(), prepared, ts, rst);
    assert!(matches!(kind.check(), McResult::Unsafe(1)));
    let McWitness::Bl(witness) = kind.witness() else {
        panic!()
    };
    assert_eq!(witness.bad_id, 1);
}

#[test]
fn every_out_of_range_property_id_compresses_bads() {
    let mut ts = Transys::new();
    ts.bad = LitVec::from([Lit::constant(false), Lit::constant(true)]);
    let mut baseline = None;
    for prop in [2, 3, usize::MAX] {
        for local_proof in [false, true] {
            let cfg = preproc_config(prop, local_proof);
            let rst = Restore::new(&ts);
            let result = Transys::preproc(ts.clone_deep(), &cfg, rst);
            assert_eq!(result.0.bad.len(), 1);
            assert!(result.0.bad[0].is_constant(true));
            let bytes = bincode::serialize(&result).unwrap();
            if let Some(baseline) = &baseline {
                assert_eq!(baseline, &bytes);
            } else {
                baseline = Some(bytes);
            }
        }
    }

    let ts = Transys::new();
    let rst = Restore::new(&ts);
    let (prepared, _) = Transys::preproc(ts, &preproc_config(0, true), rst);
    assert_eq!(prepared.bad.len(), 1);
    assert!(prepared.bad[0].is_constant(false));
}
