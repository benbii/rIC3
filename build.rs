use cmake::Config;
use std::{env, io, path::PathBuf, process::Command};

fn main() -> io::Result<()> {
    println!("cargo::rustc-check-cfg=cfg(bitwuzla_stub)");
    println!("cargo:rerun-if-changed=src/cadical");
    println!("cargo:rerun-if-changed=src/kissat");
    println!("cargo:rerun-if-changed=deps/cadical");
    println!("cargo:rerun-if-changed=deps/kissat");
    let target_os = env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    let target_env = env::var("CARGO_CFG_TARGET_ENV").unwrap_or_default();

    let mut cadical = Config::new("src/cadical");
    if target_os == "windows" && target_env == "gnu" {
        cadical.define("CMAKE_CXX_COMPILER", "x86_64-w64-mingw32-g++");
        cadical.define("CMAKE_SYSTEM_NAME", "Windows");
    } else {
        cadical.define("CMAKE_CXX_COMPILER", "clang++");
        cadical.define("CMAKE_CXX_FLAGS", "-flto");
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
        kissat.define("CMAKE_C_FLAGS", "-flto");
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
