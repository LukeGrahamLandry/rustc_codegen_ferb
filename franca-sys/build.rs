use std::process::Command;

pub fn main() {
    println!("cargo::rerun-if-changed=exports.fr");
    println!("cargo::rustc-link-lib=franca");
    // TODO: use OUT_DIR
    println!("cargo::rustc-link-search={}/target", std::env::current_dir().unwrap().to_string_lossy());
    
    // TODO: use CARGO_CFG_TARGET_OS and CARGO_CFG_TARGET_ARCH so cross compiling works
    
    // TODO: fetch and ./boot/strap.sh (but without running tests)
    let status = Command::new("franca")
        .args(["examples/default_driver.fr", "build", "exports.fr", "-o", "target/libfranca.o", "-c", "-keep-names"])
        .output()
        .expect("run franca");
    assert!(
        status.status.success(),
        "{}",
        String::try_from(status.stderr).unwrap()
    );
    
    // TODO: do this myself
    let status = Command::new("ar")
        .args(["rc", "target/libfranca.a", "target/libfranca.o"])
        .output()
        .expect("run franca");
    assert!(
        status.status.success(),
        "{}",
        String::try_from(status.stderr).unwrap()
    );
}
