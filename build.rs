use cmake::Config;
#[cfg(feature = "vendor")]
use giputils::build::copy_build;
use std::io;
#[cfg(feature = "vendor")]
use std::process::Command;

#[cfg(feature = "vendor")]
fn build_bitwuzla_vendor() -> io::Result<()> {
    println!("cargo:rerun-if-changed=deps/bitwuzla");
    let cb_path = copy_build("deps/bitwuzla", |src| {
        let status = Command::new("python3")
            .arg("configure.py")
            .current_dir(src)
            .status()?;
        if !status.success() {
            return Err(io::Error::other(format!(
                "configure.py failed with status: {status}"
            )));
        }
        let status = Command::new("meson")
            .arg("compile")
            .current_dir(src.join("build"))
            .status()?;
        if !status.success() {
            return Err(io::Error::other(format!(
                "meson compile failed with status: {status}"
            )));
        }
        Ok(())
    })?;
    println!(
        "cargo:rustc-link-search=native={}",
        cb_path.join("build").join("src").display()
    );
    println!(
        "cargo:rustc-link-search=native={}",
        cb_path.join("build").join("src").join("lib").display()
    );
    println!("cargo:rustc-link-lib=static=bitwuzla");
    println!("cargo:rustc-link-lib=static=bzlautil");
    println!("cargo:rustc-link-lib=static=bitwuzlabb");
    println!("cargo:rustc-link-lib=static=bitwuzlabv");
    println!("cargo:rustc-link-lib=static=bitwuzlals");
    println!("cargo:rustc-link-lib=static=bzlarng");
    #[cfg(target_os = "linux")]
    println!("cargo:rustc-link-lib=dylib=stdc++");
    #[cfg(target_os = "macos")]
    println!("cargo:rustc-link-lib=dylib=c++");
    println!("cargo:rustc-link-lib=dylib=gmp");
    println!("cargo:rustc-link-lib=dylib=mpfr");
    Ok(())
}

#[cfg(not(feature = "vendor"))]
fn link_bitwuzla_system() -> io::Result<()> {
    if let Ok(lib) = pkg_config::Config::new().probe("bitwuzla") {
        for path in lib.link_paths {
            println!("cargo:rustc-link-search=native={}", path.display());
        }
        for lib in lib.libs {
            println!("cargo:rustc-link-lib=dylib={lib}");
        }
        #[cfg(target_os = "linux")]
        println!("cargo:rustc-link-lib=dylib=stdc++");
        #[cfg(target_os = "macos")]
        println!("cargo:rustc-link-lib=dylib=c++");
    } else {
        println!(
            "cargo:warning=Bitwuzla not found. The library will panic at runtime if used. Please install it from https://github.com/bitwuzla/bitwuzla"
        );
        println!("cargo:rustc-cfg=bitwuzla_stub");
    }
    Ok(())
}

fn main() -> io::Result<()> {
    println!("cargo::rustc-check-cfg=cfg(bitwuzla_stub)");
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

    #[cfg(feature = "vendor")]
    build_bitwuzla_vendor()?;

    #[cfg(not(feature = "vendor"))]
    link_bitwuzla_system()?;

    Ok(())
}
