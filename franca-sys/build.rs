use std::process::Command;

pub fn main() {
    let dir = var("OUT_DIR");
    let (arch, os) = (&var("CARGO_CFG_TARGET_ARCH"), &var("CARGO_CFG_TARGET_OS"));
    assert!(arch == "aarch64" || arch == "x86_64" || arch == "riscv64" || arch == "wasm32");
    assert!(os == "macos" || os == "linux");
    let arch = if arch == "riscv64" { "rv64" } else { arch };
    
    println!("cargo::rerun-if-changed=exports.fr");
    println!("cargo::rustc-link-lib=franca");
    println!("cargo::rustc-link-search={}", dir);
    
    let o_path = &*format!("{}/libfranca.o", dir);
    let a_path = &*format!("{}/libfranca.a", dir);
    let franca = find_compiler();
    let status = Command::new(franca)
        .env("FRANCA_NO_CACHE", "1")  // irritating when i make a new target/ directory
        .args([
                "examples/default_driver.fr", "build", "exports.fr", 
                "-o", o_path, "-c",
                "-keep-names",
                "-arch", arch, "-os", os,
        ])
        .output()
        .expect("run franca");
    assert!(
        status.status.success(),
        "{}",
        String::try_from(status.stderr).unwrap()
    );
    
    // TODO: do this myself
    let status = Command::new("ar")
        .args(["rc", a_path, o_path])
        .output()
        .expect("run franca");
    assert!(
        status.status.success(),
        "{}",
        String::try_from(status.stderr).unwrap()
    );
}

// TODO: fetch and ./boot/strap.sh -no-test
fn find_compiler() -> String {
    let host = var("HOST");
    let host_os = if host.contains("linux") { "linux" } else { assert!(host.contains("darwin")); "macos" };
    let host_arch = if host.contains("aarch64") { "arm64" } else { assert!(host.contains("x86_64")); "amd64" };
    let franca_root = std::env::var("FRANCA_ROOT").unwrap_or_else(|_| {
        let mut path = "franca".into();
        for _ in 0..3 {
            if std::fs::exists(&path).ok().unwrap_or(false) {
                return path;
            }
            path = format!("../{}", path);
        }
        panic!("(franca-sys) set FRANCA_ROOT to a clone of https://git.sr.ht/~lukegrahamlandry/franca");
    });
    format!("{}/target/release/franca-{}-{}", franca_root, host_os, host_arch)
}

fn var(name: &str) -> String {
    std::env::var(name).expect(name)        
}
