use cmake::Config;
use std::{env, io, path::PathBuf, process::Command};

fn rust_codegen_options() -> Vec<String> {
    let flags: Vec<String> = env::var("CARGO_ENCODED_RUSTFLAGS")
        .ok()
        .filter(|flags| !flags.is_empty())
        .map(|flags| flags.split('\x1f').map(str::to_owned).collect())
        .or_else(|| {
            env::var("RUSTFLAGS")
                .ok()
                .map(|flags| flags.split_ascii_whitespace().map(str::to_owned).collect())
        })
        .unwrap_or_default();

    let mut options = Vec::new();
    let mut flags = flags.into_iter();
    while let Some(flag) = flags.next() {
        if flag == "-C" || flag == "--codegen" {
            if let Some(option) = flags.next() {
                options.push(option);
            }
        } else if let Some(option) = flag.strip_prefix("-C") {
            if !option.is_empty() {
                options.push(option.to_owned());
            }
        } else if let Some(option) = flag.strip_prefix("--codegen=") {
            options.push(option.to_owned());
        }
    }
    options
}

fn sat_compiler_flags() -> String {
    let mut flags = vec!["-flto".to_owned()];
    for option in rust_codegen_options() {
        if let Some(cpu) = option.strip_prefix("target-cpu=") {
            flags.push(format!("-march={cpu}"));
        } else if let Some(features) = option.strip_prefix("target-feature=") {
            flags.extend(features.split(',').filter_map(|feature| {
                let feature = feature.trim();
                feature
                    .strip_prefix('+')
                    .map(|feature| format!("-m{feature}"))
                    .or_else(|| {
                        feature
                            .strip_prefix('-')
                            .map(|feature| format!("-mno-{feature}"))
                    })
            }));
        }
    }
    flags.join(" ")
}

fn main() -> io::Result<()> {
    println!("cargo::rustc-check-cfg=cfg(bitwuzla_stub)");
    println!("cargo:rerun-if-env-changed=CARGO_ENCODED_RUSTFLAGS");
    println!("cargo:rerun-if-env-changed=RUSTFLAGS");
    println!("cargo:rerun-if-changed=src/cadical");
    println!("cargo:rerun-if-changed=src/kissat");
    println!("cargo:rerun-if-changed=deps/cadical");
    println!("cargo:rerun-if-changed=deps/kissat");
    let target_os = env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    let target_env = env::var("CARGO_CFG_TARGET_ENV").unwrap_or_default();
    let sat_compiler_flags = sat_compiler_flags();

    let mut cadical = Config::new("src/cadical");
    if target_os == "windows" && target_env == "gnu" {
        cadical.define("CMAKE_C_COMPILER", "x86_64-w64-mingw32-gcc");
        cadical.define("CMAKE_CXX_COMPILER", "x86_64-w64-mingw32-g++");
        cadical.define("CMAKE_SYSTEM_NAME", "Windows");
    } else {
        cadical.define("CMAKE_C_COMPILER", "clang");
        cadical.define("CMAKE_CXX_COMPILER", "clang++");
        cadical.define("CMAKE_C_FLAGS", &sat_compiler_flags);
        cadical.define("CMAKE_CXX_FLAGS", &sat_compiler_flags);
    }
    cadical.define("CMAKE_BUILD_TYPE", "Release");
    let cadical = cadical.build();
    println!(
        "cargo:rustc-link-search=native={}",
        cadical.join("lib").display()
    );

    let mut kissat = Config::new("src/kissat");
    if target_os == "windows" && target_env == "gnu" {
        kissat.define("CMAKE_C_COMPILER", "x86_64-w64-mingw32-gcc");
        kissat.define("CMAKE_SYSTEM_NAME", "Windows");
    } else {
        kissat.define("CMAKE_C_COMPILER", "clang");
        kissat.define("CMAKE_C_FLAGS", &sat_compiler_flags);
    }
    kissat.define("CMAKE_BUILD_TYPE", "Release");
    let kissat = kissat.build();
    println!(
        "cargo:rustc-link-search=native={}",
        kissat.join("lib").display()
    );

    println!("cargo:rerun-if-changed=src/bitwuzla/CMakeLists.txt");
    println!("cargo:rerun-if-changed=src/bitwuzla/bitwuzla-build.sh");
    println!("cargo:rerun-if-changed=deps/bitwuzla");
    println!("cargo:rerun-if-changed=deps/symfpu");
    let root = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    let status = Command::new("bash")
        .arg("bitwuzla-build.sh")
        .current_dir(root.join("src/bitwuzla"))
        .status()?;
    if !status.success() {
        return Err(io::Error::other(format!(
            "src/bitwuzla/bitwuzla-build.sh failed with status: {status}"
        )));
    }
    println!(
        "cargo:rustc-link-search=native={}",
        root.join("src/bitwuzla/build").display()
    );
    println!(
        "cargo:rustc-link-search=native={}",
        root.join("src/bitwuzla/mpfr-4.2.2/src/.libs").display()
    );
    println!(
        "cargo:rustc-link-search=native={}",
        root.join("src/bitwuzla/gmp-6.3.0/.libs").display()
    );

    println!("cargo:rustc-link-lib=static=satif-kissat");
    println!("cargo:rustc-link-lib=static=smtif-bitwuzla");
    println!("cargo:rustc-link-lib=static=satif-cadical");
    println!("cargo:rustc-link-lib=static=mpfr");
    println!("cargo:rustc-link-lib=static=gmp");
    if target_os == "linux" {
        println!("cargo:rustc-link-lib=dylib=m");
        println!("cargo:rustc-link-lib=dylib=stdc++");
    } else if target_os == "macos" {
        println!("cargo:rustc-link-lib=dylib=c++");
    } else if target_os == "windows" && target_env == "gnu" {
        println!("cargo:rustc-link-search=native=/usr/x86_64-w64-mingw32/lib");
        println!("cargo:rustc-link-lib=static=stdc++");
    }

    Ok(())
}
