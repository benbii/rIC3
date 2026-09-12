use std::{fs, process::Command};

const MODEL: &str = "1 sort bitvec 1
2 state 1 x
3 zero 1
4 one 1
5 init 1 2 3
6 next 1 2 4
7 bad 2 first
8 bad 2 selected
";

#[test]
fn selected_witness_survives_preprocess_export_and_every_engine() {
    let dir = tempfile::tempdir().unwrap();
    let model = dir.path().join("properties.btor2");
    let cache = dir.path().join("properties.preproc");
    fs::write(&model, MODEL).unwrap();
    let prepared = Command::new(env!("CARGO_BIN_EXE_ric3"))
        .arg("preprocess")
        .arg(&model)
        .args(["--prop", "1", "--local-proof", "--no-scorr", "--no-frts"])
        .arg("--preproc-file")
        .arg(&cache)
        .output()
        .unwrap();
    assert!(
        prepared.status.success(),
        "{}",
        String::from_utf8_lossy(&prepared.stderr)
    );
    for cached in [false, true] {
        for engine in [
            vec!["ic3"],
            vec!["ic3", "--inn"],
            vec!["kind", "--end", "3"],
            vec!["bmc", "--end", "3"],
            vec!["bmc", "--kissat", "--end", "3"],
        ] {
            let witness = dir.path().join("witness.btor");
            let mut command = Command::new(env!("CARGO_BIN_EXE_ric3"));
            command
                .arg("check")
                .arg(&model)
                .args(["--no-scorr", "--no-frts"]);
            if cached {
                // Selection and helper identities must come from the cache,
                // without a second --prop or --local-proof on the command line.
                command.arg("--preproc-file").arg(&cache);
            } else {
                command.args(["--prop", "1", "--local-proof"]);
            }
            let output = command
                .arg("--cert")
                .arg(&witness)
                .arg("--witness")
                .args(&engine)
                .output()
                .unwrap();
            assert_eq!(
                output.status.code(),
                Some(10),
                "cached={cached}, engine={engine:?}: {}",
                String::from_utf8_lossy(&output.stderr)
            );
            let cert = fs::read_to_string(&witness).unwrap();
            assert!(cert.starts_with("sat\nb1\n"), "{cert}");
            assert!(String::from_utf8_lossy(&output.stdout).contains("sat\nb1\n"));
        }
    }
}

#[test]
fn cli_compression_and_explicit_selection_agree_between_check_and_preprocess() {
    let dir = tempfile::tempdir().unwrap();
    let model = dir.path().join("properties.btor2");
    let cache = dir.path().join("properties.preproc");
    fs::write(&model, MODEL.replace("7 bad 2 first", "7 bad 3 first")).unwrap();
    for cached in [false, true] {
        for selected in [false, true] {
            let mut command = Command::new(env!("CARGO_BIN_EXE_ric3"));
            command
                .arg(if cached { "preprocess" } else { "check" })
                .arg(&model);
            command.args(["--no-scorr", "--no-frts"]);
            if selected {
                command.args(["--prop", "0"]);
            }
            if cached {
                let output = command.arg("--preproc-file").arg(&cache).output().unwrap();
                assert!(
                    output.status.success(),
                    "{}",
                    String::from_utf8_lossy(&output.stderr)
                );
                command = Command::new(env!("CARGO_BIN_EXE_ric3"));
                command
                    .arg("check")
                    .arg(&model)
                    .arg("--preproc-file")
                    .arg(&cache);
            }
            let output = command.arg("ic3").output().unwrap();
            assert_eq!(
                output.status.code(),
                Some(if selected { 20 } else { 10 }),
                "cached={cached}, selected={selected}: {}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
    }
}

#[test]
fn local_proof_without_a_selected_property_uses_the_compressed_target() {
    let dir = tempfile::tempdir().unwrap();
    let model = dir.path().join("properties.btor2");
    fs::write(&model, MODEL).unwrap();
    for prop in [None, Some("2"), Some("18446744073709551615")] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_ric3"));
        command.arg("check").arg(&model);
        if let Some(prop) = prop {
            command.args(["--prop", prop]);
        }
        let output = command
            .args(["--local-proof", "--no-scorr", "--no-frts", "ic3"])
            .output()
            .unwrap();
        assert_eq!(
            output.status.code(),
            Some(10),
            "prop={prop:?}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

#[test]
fn witness_only_does_not_request_a_local_safety_certificate() {
    let dir = tempfile::tempdir().unwrap();
    let model = dir.path().join("properties.btor2");
    let certificate = dir.path().join("proof.btor");
    fs::write(&model, MODEL.replace("6 next 1 2 4", "6 next 1 2 2")).unwrap();
    for engine in ["ic3", "kind"] {
        for explicit_cert in [false, true] {
            let mut command = Command::new(env!("CARGO_BIN_EXE_ric3"));
            command.arg("check").arg(&model).args([
                "--prop",
                "1",
                "--local-proof",
                "--no-scorr",
                "--no-frts",
                "--witness",
            ]);
            if explicit_cert {
                command.arg("--cert").arg(&certificate);
            }
            let output = command.arg(engine).output().unwrap();
            if explicit_cert {
                assert_ne!(output.status.code(), Some(20));
                assert!(
                    String::from_utf8_lossy(&output.stderr).contains(
                        "standalone safety certificates for local proofs are not supported"
                    )
                );
                assert!(!certificate.exists());
            } else {
                assert_eq!(
                    output.status.code(),
                    Some(20),
                    "{}",
                    String::from_utf8_lossy(&output.stderr)
                );
                assert!(String::from_utf8_lossy(&output.stdout).contains("UNSAT\n0\n"));
            }
        }
    }
}
