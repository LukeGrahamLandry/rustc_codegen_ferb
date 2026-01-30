pub use franca_sys::{Arch, Artifact, Os};

pub mod builder;
#[cfg(test)]
mod examples;

pub unsafe fn compile_aot(frc: &[u8], logging: &str, arch: Arch, os: Os, kind: Artifact) -> Vec<u8> {
    use franca_sys::*;
    assert_eq!(frc[0..8], ir::MAGIC.to_le_bytes());
    unsafe {
        let fr = init_globals();
        let mut cmd = CompileCmd {
            frc: Slice::from(frc),
            out: Slice::from("".as_bytes()),
            name: Slice::from("".as_bytes()),
            logging: Slice::from(logging.as_bytes()),
            p: 0,
            m: 0,
            arch,
            os,
            kind,
        };
        compile_one(fr, &mut cmd);
        let out = cmd.out.bytes().to_vec();
        drop_module(fr, &mut cmd);
        out
    }
}

pub fn native_target() -> (Arch, Os) {
    #[cfg(target_arch="aarch64")]  let arch = Arch::Arm64;
    #[cfg(target_arch="x86_64")]   let arch = Arch::Amd64;
    #[cfg(target_arch="riscv64")]  let arch = Arch::Rv64;
    #[cfg(target_arch="wasm32")]   let arch = Arch::Wasm32;
    #[cfg(target_os="linux")]      let os = Os::Linux;
    #[cfg(target_os="macos")]      let os = Os::Macos;
    
    (arch, os)
}
