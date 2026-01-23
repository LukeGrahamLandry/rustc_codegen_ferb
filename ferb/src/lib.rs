pub mod builder;
mod examples;

// TODO: target. choose obj or exe or dylib. 
pub fn compile_aot(frc: &[u8]) -> Vec<u8> {
    use franca_sys::*;
    use franca_sys::ir::*;
    assert_eq!(frc[0..8], MAGIC.to_le_bytes());
    unsafe {
        let fr = init_globals();
        let mut cmd = CompileCmd {
            frc: Slice::from(frc),
            out: Slice::from("".as_bytes()),
            name: Slice::from("".as_bytes()),
            p: 0,
            m: 0,
            jit: 0,
        };
        compile_one(fr, &mut cmd);
        let out = cmd.out.bytes().to_vec();
        drop_module(fr, &mut cmd);
        out
    }
}
