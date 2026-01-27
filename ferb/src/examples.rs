#![cfg(test)]

use franca_sys::*;
use crate::builder::*;

#[test]
fn jit_add() {
    let mut m = Module::new();
    
    // fn add_i64(r0: i64, r1: i64) -> i64 { r0 + r1 }
    let name = "add_i64";
    let mut f = Func::new(m.sym(name), Ret::K(Cls::Kl));
    let (r, b) = (f.tmps::<3>(), f.blk());
    f.emit(b, O::par, Cls::Kl, r[0], (), ());
    f.emit(b, O::par, Cls::Kl, r[1], (), ());
    f.emit(b, O::add, Cls::Kl, r[2], r[0], r[1]);
    f.jump(b, J::retl, r[2], None, None);
    m.func(f);
    
    let bytes = m.finish();
    unsafe {
        let fr = init_globals();
        let mut cmd = CompileCmd {
            frc: Slice::from(&bytes[0..]),
            out: Slice::from("".as_bytes()),
            name: Slice::from(name.as_bytes()),
            logging: Slice::from("".as_bytes()),
            p: 0,
            m: 0,
            jit: 1,
        };
        compile_one(fr, &mut cmd);
        let f: fn(a: i64, b: i64) -> i64 = std::mem::transmute(cmd.p); 
        assert_eq!(f(1, 2), 3);
        assert_eq!(f(20, -5), 15);
        drop_module(fr, &mut cmd);
    };
}
