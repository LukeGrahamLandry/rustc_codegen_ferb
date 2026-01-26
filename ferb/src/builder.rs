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

#[derive(Debug)]
pub struct Func {
    id: Id<Sym>,
    blocks: Vec<Block>,
    con: Vec<Con>,
    ret: Ret,
    ntmp: usize,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Ret {
    K(Cls),
    Void,
    T(Ref),
}

#[derive(Copy, Clone, Debug)]
pub struct BlkId(u32);

#[derive(Debug)]
pub struct Block {
    ins: Vec<Ins>,
    phi: Vec<Phi>,
    s: [Option<BlkId>; 2],
    jmp: BlkJmp,
}

#[derive(Debug)]
pub struct Phi {
    pub to: Ref,
    pub cls: Cls,
    pub cases: Vec<(BlkId, Ref)>
}

#[derive(Debug)]
pub struct Data<'a> {
    pub id: Id<Sym>,
    pub segment: Seg,
    pub template: Template<'a>,
    pub rel: Vec<Reloc>,
}

#[derive(Clone, Debug)]
pub enum Template<'a> {
    Bytes(&'a [u8]),
    Zeroes(usize),
}

#[derive(Clone, Debug)]
pub struct TypeLayout {
    pub size: usize,
    pub align: usize,
    pub cases: Vec<Vec<Field>>,
    pub is_union: bool,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Field {
    Scalar(FieldType),
    Struct(Ref),  // RType from Module::typ
    Pad(u32),
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
        debug_assert_eq!(sym.segment, Seg::Invalid, "redeclared {:?}", id);
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
    
    pub fn data(&mut self, d: Data) {
        let rel_off = self.rel.len();
        self.rel.extend(&d.rel);
        let bytes = match d.template {
            Template::Bytes(it) => self.bytes(it),
            Template::Zeroes(count) => Idx::new(u32::MAX as usize, count),
        };
        let sym = &mut self.sym[d.id.off as usize];
        debug_assert_eq!(sym.segment, Seg::Invalid, "redeclared {:?}", d.id);
        sym.segment = d.segment;
        sym.payload.dat = Dat {
            bytes,
            rel: Idx::new(rel_off, d.rel.len()),
        };
        for it in &d.rel {
            debug_assert!(it.off % 8 == 0 && it.off < bytes.count);
        }
        debug_assert!(matches!(d.segment, Seg::ConstantData | Seg::MutableData));
    }
    
    pub fn import(&mut self, id: Id<Sym>, lib: Id<Lib>) {
        let sym = &mut self.sym[id.off as usize];
        debug_assert_eq!(sym.segment, Seg::Invalid, "redeclared {:?}", id);
        sym.segment = Seg::Import;
        sym.payload.imp = Imp { 
            lib,
            weak: false,  // TODO
            _0: 0,
        };
    }
    
    pub fn library(&mut self, name: &str) -> Id<Lib> {
        let name = self.bytes(name.as_bytes());
        self.lib.push(Lib {
            name,
        });
        Id::new(self.lib.len() - 1)
    }
    
    // TODO: maybe i should do the layout here instead of making the caller deal with it
    pub fn typ(&mut self, t: TypeLayout) -> Ref {
        let fields_off = self.idx.len();
        debug_assert!(t.is_union || t.cases.len() <= 1);
        for case in &t.cases {
            self.idx.reserve(case.len() + 1);
            for &it in case {
                let (tag, data) = match it {
                    Field::Scalar(it) => (it, field_size(it).expect("primitive field")),
                    Field::Struct(it) => (FieldType::FTyp, it.0 >> 3),
                    Field::Pad(n) => (FieldType::FPad, n),
                };
                self.idx.push(pack_field(tag, data));
            }
            self.idx.push(pack_field(FieldType::FEnd, 0));
        }
        debug_assert!(t.size < (1 << 29), "type too large");
        self.typ.push(Typ {
            size: t.size as u32,
            nunion: t.cases.len() as u16,
            align_log2: t.align.trailing_zeros() as u8,
            flags: pack_typ_flags(t.cases.len() == 0, t.is_union),
            fields: Idx::new(fields_off, self.idx.len() - fields_off),
        });
        pack_ref(RefKind::RType, self.typ.len() as u32 - 1)
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
    
    // this is what it's called in the franca codebase so it's what i automatically type
    pub fn intern(&mut self, name: &str) -> Id<Sym> {
        self.sym(name)
    }

    pub fn anon(&mut self) -> Id<Sym> {
        self.sym(&*format!("__R{}", self.sym.len()))
    }
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
    
    pub fn con(&mut self, sym: Id<Sym>, i: i64) -> Ref {
        let trunc = |i| (i & (u32::MAX as i64)) as u32;
        let con = Con { sym, bits: [trunc(i), trunc(i >> 32)], };
        for (i, it) in self.con.iter().enumerate().skip(1) {
            if it == &con {
                return pack_ref(RefKind::RCon, i as u32);
            }
        }
        self.con.push(con);
        pack_ref(RefKind::RCon, self.con.len() as u32 - 1)
    }
    
    pub fn tmp(&mut self) -> Ref {
        self.ntmp += 1;
        pack_ref(RefKind::RTmp, self.ntmp as u32 - 1)
    }
    
    pub fn emit(&mut self, b: BlkId, o: O, k: Cls, to: impl Reflike, a0: impl Reflike, a1: impl Reflike) {
        let (to, a0, a1) = (to.r(self), a0.r(self), a1.r(self));
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
    
    pub fn jump(&mut self, b: BlkId, kind: J, arg: impl Reflike, s1: Option<BlkId>, s2: Option<BlkId>) {
        let arg = arg.r(self);
        let b = &mut self.blocks[b.0 as usize];
        b.jmp = BlkJmp { kind, arg, };
        b.s = [s1, s2];
    }
    
    pub fn blit(&mut self, b: BlkId, dest: Ref, src: Ref, n: usize) {
        debug_assert!(n < (1 << 29), "blit too large");
        let n = pack_ref(RefKind::RInt, n as u32);
        self.emit(b, O::blit0, Cls::Kw, Ref::Null, src, dest);
        self.emit(b, O::blit1, Cls::Kw, Ref::Null, n, Ref::Null);
    }
    
    pub fn tmps<const N: usize>(&mut self) -> [Ref; N] {
        // this is what i want: (0..N).map(|_| self.tmp()).collect::<[Ref; N]>();
        let mut it = [Ref::Null; N];
        for it in &mut it {
            *it = self.tmp();
        }
        it
    }
}

fn field_size(it: FieldType) -> Option<u32> {
    Some(match it {
        FieldType::Fb => 1,
        FieldType::Fh => 2,
        FieldType::Fw => 4,
        FieldType::Fl => 8,
        FieldType::Fs => 4,
        FieldType::Fd => 8,
        _ => return None,
    })
}

// this exists because you can't call f.emit(_, _, _, f.con(Id::None, 0), _) 
// because it counts as two mutable references. this lets it work without always adding extra name bindings.

pub trait Reflike {
    fn r(self, f: &mut Func) -> Ref;
}
impl Reflike for Ref {
    fn r(self, _: &mut Func) -> Ref {
        self
    }
}
impl Reflike for Id<Sym> {
    fn r(self, f: &mut Func) -> Ref {
        f.con(self, 0)
    }
}
impl Reflike for i64 {
    fn r(self, f: &mut Func) -> Ref {
        f.con(Id::None, self)
    }
}
impl Reflike for () {
    fn r(self, _: &mut Func) -> Ref {
        Ref::Null
    }
}
