//
// the binary format for franca ir (.frc)
// https://git.sr.ht/~lukegrahamlandry/franca/tree/main/item/backend/incremental.fr
// not needed yet: Dep, FTy, Fld, Addr, Asm
//  
#![allow(nonstandard_style)]
use std::marker::PhantomData;
use std::fmt::Debug;

pub const MAGIC: u64 = 0x0012_41434E415246;

#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct Header {
    pub magic_v: u64,
    pub filelen: u32,
    pub arch_os: u32,
    pub entry_sym: Id<Sym>,
    pub entry_dep: u32,
    pub root_scope: u32,
    pub hack_enable_const_fold: u32,
    pub debug_name: Idx<u8>,
    pub all_deps: [u32; 8],
    pub entry_source: Idx<u8>,
    pub hack_name_bytes_for_importc: [u8; 8],
    pub pad: [u32; 30],
    pub items: [[u32; 2]; 13],
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct Sym {
    pub segment: Seg,
    pub align_log2: u8,
    pub name: Idx<u8>,
    pub payload: P,
}

#[repr(C)]
#[derive(Copy, Clone)]
pub union P {
    pub fnc: Fnc,
    pub dat: Dat,
    pub imp: Imp,
    pub asm: [u32; 8],
    pub alias: Id<Sym>,
}

#[repr(u8)]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Seg {
    Invalid,
    Code,
    ConstantData,
    MutableData,
    ZeroInitData,
    Import,
    MachineCode,
    Alias,
}

#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct Fnc {
    pub reg: u64,
    pub blk: Idx<Blk>,
    pub con: Idx<Con>,
    pub mem: [u32; 2],
    pub retty: Ref,
    pub flags: u32,  // pack_fnc_flags
    pub ntmp: u32,
}

#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct Blk {
    pub ins: Idx<Ins>,
    pub s1: u32,
    pub s2: u32,
    pub jmp: BlkJmp,
    pub phi: Id<u32>,
}

#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct Dat {
    pub bytes: Idx<u8>,
    pub rel: Idx<Reloc>,
}

#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct Reloc {
    pub off: u32,
    pub id: Id<Sym>,
    pub addend: i64,
}

#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct Imp {
    pub lib: Id<Lib>,
    pub _0: u32,
    pub weak: bool,
}

#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct Lib {
    pub name: Idx<u8>,
}

#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct Typ {
    pub size: u32,
    pub nunion: u16,
    pub align_log2: u8,
    pub flags: u8, // pack_typ_flags
    pub fields: Idx<u32>,  // pack_field
}

#[repr(u32)]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum RefKind {
    RTmp,
    RCon,
    RInt,
    RType,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Ref(pub u32);

#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct Ins {
    pub op_cls: u32,
    pub to: Ref,
    pub arg: [Ref; 2],
}

#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct BlkJmp {
    pub kind: J,
    pub arg: Ref,
}

#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct Con {
    pub bits: [u32; 2],
    pub sym: Id<Sym>,
}

#[derive(Copy, Clone, Debug)]
pub struct TypFlags(pub u8);

#[repr(u32)]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Cls {
    Kw,
    Kl,
    Ks,
    Kd,
}

#[repr(u32)]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum O {
    add = 1,
    sub,
    neg,
    div,
    rem,
    udiv,
    urem,
    mul,
    and,
    or,
    xor,
    sar,
    shr,
    shl,

    ceqw,
    cnew,
    csgew,
    csgtw,
    cslew,
    csltw,
    cugew,
    cugtw,
    culew,
    cultw,

    ceql,
    cnel,
    csgel,
    csgtl,
    cslel,
    csltl,
    cugel,
    cugtl,
    culel,
    cultl,

    ceqs,
    cges,
    cgts,
    cles,
    clts,
    cnes,
    cos,
    cuos,

    ceqd,
    cged,
    cgtd,
    cled,
    cltd,
    cned,
    cod,
    cuod,

    storeb,
    storeh,
    storew,
    storel,
    stores,
    stored,

    loadsb,
    loadub,
    loadsh,
    loaduh,
    loadsw,
    loaduw,
    load,

    extsb,
    extub,
    extsh,
    extuh,
    extsw,
    extuw,

    exts,
    truncd,
    stosi,
    stoui,
    dtosi,
    dtoui,
    swtof,
    uwtof,
    sltof,
    ultof,
    cast,

    byteswap = 82,
    rotr,
    rotl,
    ctz,
    clz,
    ones,

    sqrt,
    min,
    max,

    alloc4 = 92,
    alloc8,
    alloc16,

    vaarg,
    vastart,

    copy,

    dbgloc,

    nop,
    addr,
    blit0,
    blit1,

    par = 115,
    parsb,
    parub,
    parsh,
    paruh,
    parc,
    pare,
    arg,
    argsb,
    argub,
    argsh,
    arguh,
    argc,
    arge,
    argv,
    call,

    sel0 = 156,
    sel1,

    cas0 = 176,
    cas1,
}

#[repr(u32)]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum J {
    xxx,
    retw,
    retl,
    rets,
    retd,
    retsb,
    retub,
    retsh,
    retuh,
    retc,
    ret0,
    jmp,
    jnz,
    hlt = 31,
    switch,
}

#[repr(u8)]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum FieldType {
    FEnd,
    Fb,
    Fh,
    Fw,
    Fl,
    Fs,
    Fd,
    FPad,
    FTyp,
}

pub const fn pack_op_cls(op: O, cls: Cls) -> u32 {
    (op as u32) | (cls as u32) << 30
}

pub const fn pack_ref(kind: RefKind, i: u32) -> Ref {
    Ref((kind as u32) | i << 3)
}

// ret_cls: Cls / 4 / 5
pub const fn pack_fnc_flags(var_arg: bool, ret_cls: u32) -> u32 {
    (ret_cls << 7) | ((var_arg as u32) << 1)
}

pub const fn pack_typ_flags(dark: bool, union: bool) -> u32 {
    (dark as u32) | (union as u32) << 1
}

pub const fn pack_field(kind: FieldType, len: u32) -> u32 {
    (kind as u32) | len << 8
}

#[derive(Copy, Clone)]
pub struct Idx<T> {
    pub off: u32,
    pub count: u32,
    pub _0: PhantomData<T>,
}

#[derive(Copy, Clone)]
pub struct Id<T> {
    pub off: u32,
    pub _0: PhantomData<T>,
}

impl<T> Id<T> {
    pub const None: Self = Self::new(0xFFFFFFFF);
    pub const fn new(off: usize) -> Self {
        Self {
            off: off as u32,
            _0: PhantomData,
        }
    }
}

impl<T> Idx<T> {
    pub const Empty: Self = Self::new(0, 0);
    pub const fn new(off: usize, count: usize) -> Self {
        Self {
            off: off as u32,
            count: count as u32,
            _0: PhantomData,
        }
    }
}

impl<T> Debug for Id<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}]", self.off)
    }
}

impl<T> Debug for Idx<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}..+{}]", self.off, self.count)
    }
}

impl Ref {
    pub const Null: Ref = Ref(0);
}
