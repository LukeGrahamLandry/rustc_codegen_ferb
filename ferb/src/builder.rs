use std::collections::HashMap;

pub use franca_sys::ir::*;

#[derive(Default)]
pub struct Module {
    sym: Vec<Sym>,
    blk: Vec<Blk>,
    ins: Vec<Ins>,
    con: Vec<Con>,
    rel: Vec<Reloc>,
    str: Vec<u8>,
    lib: Vec<Lib>,
    idx: Vec<u32>,
    typ: Vec<Typ>,
    symbols: HashMap<String, Id<Sym>>,
}

pub struct Func {
    id: Id<Sym>,
    blocks: Vec<Block>,
    con: Vec<Con>,
    ret: Ret,
    ntmp: usize,
}

#[derive(Copy, Clone, Debug)]
pub struct BlkId(u32);

pub struct Block {
    ins: Vec<Ins>,
    phi: Vec<Phi>,
    s: [Option<BlkId>; 2],
    jmp: BlkJmp,
}

pub struct Phi {
    pub to: Ref,
    pub cls: Cls,
    pub cases: Vec<(BlkId, Ref)>
}

impl Module {
    pub fn new() -> Module {
        Module::default()
    }
    
    pub fn sym(&mut self, name: &str) -> Id<Sym> {
        self.symbols.get(name).map(|it| *it).unwrap_or_else(|| {
            let id = Id::new(self.sym.len());
            self.symbols.insert(name.into(), id);
            let name = self.bytes(name.as_bytes());
            self.sym.push(Sym {
                segment: Seg::Invalid,
                align_log2: 0,
                name,
                payload: P {
                    asm: [0; 8],
                },
            });
            id
        })
    }
    
    pub fn bytes(&mut self, it: &[u8]) -> Idx<u8> {
        let off = self.str.len();
        self.str.extend(it);
        Idx::new(off, it.len())
    }
    
    pub fn func(&mut self, f: Func) {
        assert!(f.ntmp < (1 << 29), "too many temporaries");
        assert!(f.con.len() < (1 << 29), "too many constants");
        
        let id = f.id.off as usize;
        let (ret_cls, retty) = match f.ret {
            Ret::K(k) => (k as u32, Ref::Null),
            Ret::Void => (4, Ref::Null),
            Ret::T(t) => (5, t),
        };
        let con_off = self.con.len();
        self.con.extend(&f.con[2..]);

        let blk_off = self.blk.len();
        self.blk.reserve(f.blocks.len());
        for b in &f.blocks {
            let phi = self.write_phi(b);
            let ins_off = self.ins.len();
            self.ins.extend(&b.ins);
            self.blk.push(Blk {
                ins: Idx::new(ins_off, b.ins.len()),
                s1: b.s[0].map(|b| b.0).unwrap_or(u32::MAX),
                s2: b.s[1].map(|b| b.0).unwrap_or(u32::MAX),
                jmp: b.jmp,
                phi,
            });
        }
        
        let sym = &mut self.sym[id];
        assert_eq!(sym.segment, Seg::Invalid, "redeclared function {:?}", id);
        sym.segment = Seg::Code;
        sym.payload.fnc = Fnc {
            reg: 0,
            blk: Idx::new(blk_off, f.blocks.len()),
            con: Idx::new(con_off, f.con.len() - 2),
            mem: [0; 2],
            retty,
            flags: pack_fnc_flags(false, ret_cls),
            ntmp: f.ntmp as u32,
        };
    }
    
    fn write_phi(&mut self, b: &Block) -> Id<u32> {
        if b.phi.is_empty() {
            return Id::None;
        }
        let phi = self.idx.len();
        self.idx.push(b.phi.len() as u32);
        for p in &b.phi {
            self.idx.reserve(p.cases.len() * 2 + 2);
            self.idx.push(p.cases.len() as u32 | (p.cls as u32) << 30);
            self.idx.push(p.to.0);
            for (r, b) in &p.cases {
                self.idx.push(b.0);
                self.idx.push(r.0);
            }
        };
        Id::new(phi)
    }
    
    pub fn finish(self) -> Vec<u8> {
        let mut out = vec![];
        let mut i = 0;
        let mut items: [[u32; 2]; 13] = [[0; 2]; 13];
        
        fn cast_to_bytes<T>(it: &[T]) -> &[u8] {
            // SAFETY: only used for repr(C) types with layout matching the frc file format. 
            unsafe {
                let p = it.as_ptr() as *const u8;
                std::slice::from_raw_parts(p, it.len() * size_of::<T>())
            }
        }
        macro_rules! f {
            ($name:ident) => {
                if self.$name.len() > 0 {
                    items[i] = [out.len() as u32, self.$name.len() as u32];
                    out.extend(cast_to_bytes(&self.$name));
                }
                i += 1;
            }
        }
        
        out.extend([0; size_of::<Header>()]);  // patched at the end
        i += 1;
        f!(sym);
        f!(blk);
        f!(ins);
        f!(con);
        i += 1;
        f!(rel);
        f!(str);
        f!(lib);
        f!(idx);
        f!(typ);
        i += 1;
        i += 1;
        assert_eq!(i, items.len());
        
        assert!(self.typ.len() < (1 << 29), "too many types");
        assert!(out.len() < u32::MAX as usize, ".frc must be <4gb");  // also catches if any of the Id(x) would overflow
        let h = Header {
            magic_v: MAGIC,
            filelen: out.len() as u32,
            arch_os: 0xFFFF,  // TODO
            entry_sym: Id::None,
            entry_dep: u32::MAX,
            root_scope: u32::MAX,
            hack_enable_const_fold: 1,
            debug_name: Idx::Empty,
            all_deps: [0; 8],
            entry_source: Idx::Empty,
            hack_name_bytes_for_importc: "tagdata\0".as_bytes().try_into().unwrap(),
            pad: [0; 30],
            items,
        };
        out[0..size_of::<Header>()].copy_from_slice(cast_to_bytes(&[h]));
        
        out
    }
}

pub enum Ret {
    K(Cls),
    Void,
    T(Ref),
}

impl Func {
    pub fn new(id: Id<Sym>, ret: Ret) -> Self {
        Self { 
            id, 
            blocks: vec![], 
            con: vec![
                Con { bits: [0xDEADDEAD, 0], sym: Id::None },
                Con { bits: [0; 2], sym: Id::None },
            ],
            ret,
            ntmp: 64,
        }
    }
    
    pub fn tmp(&mut self) -> Ref {
        self.ntmp += 1;
        pack_ref(RefKind::RTmp, self.ntmp as u32 - 1)
    }
    
    pub fn emit(&mut self, b: BlkId, o: O, k: Cls, to: Ref, a0: Ref, a1: Ref) {
        self.blocks[b.0 as usize].ins.push(Ins {
            op_cls: pack_op_cls(o, k),
            to: to,
            arg: [a0, a1],
        });
    }
    
    pub fn blk(&mut self) -> BlkId {
        self.blocks.push(Block {
            ins: vec![],
            phi: vec![],
            s: [None; 2],
            jmp: BlkJmp {
                kind: J::xxx,
                arg: Ref::Null,
            },
        });
        BlkId(self.blocks.len() as u32 - 1)
    }
    
    pub fn jump(&mut self, b: BlkId, kind: J, arg: Ref, s1: Option<BlkId>, s2: Option<BlkId>) {
        let b = &mut self.blocks[b.0 as usize];
        b.jmp = BlkJmp { kind, arg, };
        b.s = [s1, s2];
    }
}
