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
    
    jitted(m, &[name], |f| {
        let f: fn(a: i64, b: i64) -> i64 = unsafe { std::mem::transmute(f[0]) }; 
        assert_eq!(f(1, 2), 3);
        assert_eq!(f(20, -5), 15);
    });
}

fn jitted(m: Module, name: &[&str], then: impl FnOnce(&[u64])) {
    assert!(name.len() == 1);
    let bytes = m.finish();
    unsafe {
        let fr = init_globals();
        let mut cmd = CompileCmd {
            frc: Slice::from(&bytes[0..]),
            out: Slice::from("".as_bytes()),
            name: Slice::from(name[0].as_bytes()),
            logging: Slice::from("".as_bytes()),
            p: 0,
            m: 0,
            jit: 1,
        };
        compile_one(fr, &mut cmd);
        then(&[cmd.p]);
        drop_module(fr, &mut cmd);
    };
}
