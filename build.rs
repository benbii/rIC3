use cmake::Config;

fn main() {
    println!("cargo:rerun-if-changed=src/cadical");
    println!("cargo:rerun-if-changed=src/kissat");
    println!("cargo:rerun-if-changed=deps/cadical");
    println!("cargo:rerun-if-changed=deps/kissat");
    let target_os = std::env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    let target_env = std::env::var("CARGO_CFG_TARGET_ENV").unwrap_or_default();

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
    println!("cargo:rustc-link-lib=static=satif-cadical");
    if target_os == "linux" {
        println!("cargo:rustc-link-lib=dylib=stdc++");
    } else if target_os == "macos" {
        println!("cargo:rustc-link-lib=dylib=c++");
    } else if target_os == "windows" && target_env == "gnu" {
        println!("cargo:rustc-link-search=native=/usr/x86_64-w64-mingw32/lib");
        println!("cargo:rustc-link-lib=static=stdc++");
    }

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
    println!("cargo:rustc-link-lib=static=satif-kissat");
}
