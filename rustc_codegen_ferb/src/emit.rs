use rustc_const_eval::interpret::{AllocId, ConstAllocation, GlobalAlloc, Scalar, alloc_range};
use rustc_hir::def_id::DefId;
use rustc_index::{Idx, IndexVec, bit_set::MixedBitSet};
use rustc_middle::{mir::{BasicBlock, BasicBlockData, BinOp, Body, CastKind, ConstOperand, ConstValue, Local, Operand, Place, ProjectionElem, RETURN_PLACE, Rvalue, StatementKind, TerminatorKind, UnOp, mono::{CodegenUnit, MonoItem}}, ty::{EarlyBinder, GenericArgsRef, Instance, Ty, TyCtxt, TyKind, TypingEnv, layout::{self, HasTyCtxt, HasTypingEnv, LayoutOf, LayoutOfHelpers}}};
use ferb::builder as Ferb;
use Ferb::Cls::*;
use Ferb::{J, O, Reflike};
use rustc_abi::{FieldIdx, FieldsShape, HasDataLayout, Size, TagEncoding, Variants};
use rustc_span::Span;

struct Emit<'f, 'tcx> {
    tcx: TyCtxt<'tcx>,
    m: &'f mut Ferb::Module,
    f: &'f mut Ferb::Func,
    b: Ferb::BlkId,
    blocks: IndexVec<BasicBlock, Ferb::BlkId>,
    locals: IndexVec<Local, Val>,
    instance: Instance<'tcx>,
    start_block: Ferb::BlkId,
    mir: &'tcx Body<'tcx>,
}

#[derive(Debug, PartialEq, Copy, Clone)]
struct Val {
    r: Ferb::Ref,
    kind: ValKind,
    k: Ferb::Cls,
}

#[derive(Debug, PartialEq, Copy, Clone)]
enum ValKind {
    Scalar,
    Pair,  // same repr as Memory but fields immutable and only accessed by casts 
    Memory,
    Undef,
}

pub(crate) fn emit<'tcx>(tcx: TyCtxt<'tcx>, cgu: &CodegenUnit<'tcx>) -> Ferb::Module {
    let mut m = Ferb::Module::new();
    // TODO: i inline better if they're sorted in callgraph order (def before use)
    let items = cgu.items_in_deterministic_order(tcx);
    for (it, _data) in items {
        match it {
            MonoItem::Fn(it) => {
                let id = m.intern(tcx.symbol_name(it).name);
                let mut f = Ferb::Func::new(id, Ferb::Ret::K(Kl));
                let mir = tcx.instance_mir(it.def);
                let start_block = f.blk();
                let undef = Val { r: Ferb::Ref::Undef, kind: ValKind::Undef, k: Kw };
                let mut emit = Emit {
                    tcx,
                    blocks: mir.basic_blocks.iter().map(|_| f.blk()).collect(),
                    locals: mir.local_decls.iter().map(|_| undef).collect(),
                    b: start_block,
                    m: &mut m,
                    f: &mut f,
                    instance: it,
                    start_block,
                    mir,
                };
                for i in 0..mir.arg_count {
                    let local = Local::new(i + 1);
                    let ty = mir.local_decls[local].ty;
                    let (k, kind) = emit.cls(ty);
                    let mut r = emit.tmp(k);
                    r.kind = kind;
                    emit.emit(O::par, k, r, Val::R, Val::R);
                    emit.locals[local] = r;
                }

                emit.allocate_locals();
                emit.f.jump(emit.b, J::jmp, (), Some(emit.blocks[BasicBlock::new(0)]), None);
                for (bid, blk) in mir.basic_blocks.iter_enumerated() {
                    emit.b = emit.blocks[bid]; 
                    emit.emit_block(blk);
                }
                m.func(f);
            },
            MonoItem::Static(def) => {
                let id = def_symbol(&mut m, tcx, def, None);
                let p = tcx.eval_static_initializer(def).unwrap();
                let (bytes, segment) = get_all_bytes(p);
                m.data(Ferb::Data {
                    id,
                    segment,
                    template: Ferb::Template::Bytes(bytes),
                    rel: vec![],
                });
            },
            MonoItem::GlobalAsm(_) => todo!(),
        } 
    }
    
    m
}

impl<'f, 'tcx> Emit<'f, 'tcx> {
    fn allocate_locals(&mut self) {
        let mut needs_alloca = MixedBitSet::<Local>::new_empty(self.mir.local_decls.len());
        for b in self.mir.basic_blocks.iter() {
            for it in &b.statements {
                // TODO: any other uses of places that take address?
                if let StatementKind::Assign(box (_, value)) = &it.kind {
                    if let Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) = value {
                        needs_alloca.insert(place.local);
                    }
                }
            }
        }
        for (local, it) in self.mir.local_decls.iter_enumerated() {
            let (k, kind) = self.cls(it.ty);
            let size = self.layout_of(it.ty).size.bytes() as i64;
            let is_arg = self.locals[local].kind != ValKind::Undef;
            let take_ref = needs_alloca.contains(local);
            if is_arg {
                assert!(kind != ValKind::Scalar || !take_ref, "TODO: &arg");
                continue;
            }
            self.locals[local] = match kind {
                ValKind::Scalar => if needs_alloca.contains(local) {
                    self.alloca(size, ValKind::Memory)
                } else {
                    self.tmp(k)
                }
                ValKind::Pair | ValKind::Memory => self.alloca(size, kind),
                ValKind::Undef => todo!(),
            }
        }
    }
    
    fn emit_block(&mut self, blk: &BasicBlockData<'tcx>) {
        for stmt in &blk.statements {
            match &stmt.kind {
                StatementKind::Assign(box (place, value)) => {
                    let r = self.emit_value(value);
                    self.store_place(place, r);
                },
                StatementKind::Nop => (),
                StatementKind::StorageLive(_) => (),
                StatementKind::StorageDead(_) => (),
                _ => todo!("{:?}", stmt),
            }
        }
        let terminator = blk.terminator();
        match &terminator.kind {
            &TerminatorKind::Goto { target } => {
                self.f.jump(self.b, J::jmp, (), Some(self.blocks[target]), None);
            }
            TerminatorKind::Return => {
                let r = self.locals[RETURN_PLACE];
                assert!(r.kind == ValKind::Scalar);
                self.f.jump(self.b, J::retl, r.r, None, None);
            }
            TerminatorKind::Call { func, args, destination, target, .. } => {
                let callee = self.emit_operand(func);
                let sig = func.ty(self.mir, self.tcx).fn_sig(self.tcx);
                let arg_count = sig.inputs().skip_binder().len();
                let args = args.iter().map(|arg| self.emit_operand(&arg.node)).collect::<Vec<_>>();
                for (i, arg) in args.iter().enumerate() {
                    if i == arg_count {
                        assert!(sig.c_variadic());
                        self.f.emit(self.b, O::argv, Kw, (), (), ());
                    }
                    // TODO: struct abi
                    self.f.emit(self.b, O::arg, arg.k, (), arg.r, ());
                }
                if sig.c_variadic() && args.len() == arg_count {
                    // wasm cares if variadic even if none passed
                    self.f.emit(self.b, O::argv, Kw, (), (), ());
                }
                
                let (k, _) = self.cls(sig.output().skip_binder());
                let r = self.tmp(k);
                self.emit(O::call, k, r, callee, Val::R);
                self.store_place(destination, r);
                let j = target.map(|_| J::jmp).unwrap_or(J::hlt);
                let target = target.map(|it| self.blocks[it]);
                self.f.jump(self.b, j, (), target, None);
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                let discr = self.emit_operand(discr);
                assert!(discr.kind == ValKind::Scalar);
                let discr = discr.r;
                if let Some((val, a, b)) = targets.as_static_if() {
                    if val == 0 {
                        // TODO: don't assume Kw
                        self.f.jump(self.b, J::jnz, discr, Some(self.blocks[b]), Some(self.blocks[a]));
                        return;
                    }
                }
                // TODO: don't assume Kl
                // :SLOW
                let mut next = self.f.blk();
                for (&val, &dest) in targets.all_values().iter().zip(targets.all_targets()) {
                    let cond = self.f.tmp();
                    self.f.emit(self.b, O::ceql, Kl, cond, discr, val.0 as u64);
                    self.f.jump(self.b, J::jnz, cond, Some(self.blocks[dest]), Some(next));
                    self.b = next;
                    next = self.f.blk();
                }
                self.f.jump(self.b, J::jmp, (), Some(self.blocks[targets.otherwise()]), None);
            }
            TerminatorKind::Unreachable => self.f.jump(self.b, J::hlt, (), None, None),
            TerminatorKind::Assert { cond, expected, target, .. } => {
                let cond = self.emit_operand(cond);
                let dest = [self.f.blk(), self.blocks[*target]];
                // TODO: also print the msg.
                self.f.jump(dest[0], J::hlt, (), None, None);
                self.f.jump(self.b, J::jnz, cond.r, Some(dest[*expected as usize]), Some(dest[!*expected as usize]));
            }
            _ => todo!("{:?}", terminator),
        }
    }
    
    fn emit_value(&mut self, value: &Rvalue<'tcx>) -> Val {
        match value {
            Rvalue::Use(operand) => self.emit_operand(operand),
            Rvalue::RawPtr(_, place) => {
                assert!(place.projection.len() == 1 && place.projection[0].kind() == ProjectionElem::Deref);
                let local = place.local;
                assert!(self.locals[local].kind != ValKind::Scalar, "{:?}", value);
                self.locals[local]
            }
            Rvalue::Ref(_, _, place) => {
                let local = place.local;
                assert!(self.locals[local].kind != ValKind::Scalar, "{:?}", value);
                self.addr_place(place)
            }
            Rvalue::Cast(kind, value, dest_ty) => {
                let src = self.emit_operand(value);
                let src_ty = value.ty(&self.mir.local_decls, self.tcx);
                match kind {
                    CastKind::Transmute => src,
                    CastKind::PtrToPtr => {
                        assert!(src_ty.is_any_ptr() && dest_ty.is_any_ptr());
                        if is_wide(src_ty) && !is_wide(*dest_ty) {
                            return self.get_pair_slot(src, true);
                        }
                        assert!(is_wide(src_ty) == is_wide(*dest_ty));
                        src
                    }
                    CastKind::IntToInt => {
                        assert!(dest_ty.primitive_size(self.tcx) == src_ty.primitive_size(self.tcx));
                        src
                    },
                    _ => todo!("{:?}", value),
                }
            }
            Rvalue::UnaryOp(op, value) => {
                match op {
                    UnOp::PtrMetadata => {
                        let p = self.emit_operand(value);
                        self.get_pair_slot(p, false)
                    }
                    UnOp::Not => {
                        let r = self.emit_operand(value);
                        let r2 = self.tmp(r.k);
                        let ones = self.r(-1i64, r.k);
                        self.emit(O::xor, r.k, r2, r, ones);
                        r2
                    }
                    _ => todo!("{:?} {:?}", op, value)
                }
            }
            Rvalue::BinaryOp(op, box(lhs, rhs)) => {
                let is_cmp = matches!(*op, BinOp::Eq | BinOp::Lt | BinOp::Le | BinOp::Ne | BinOp::Ge | BinOp::Gt);
                if is_cmp && self.cls(lhs.ty(self.mir, self.tcx)).0 != Kl {
                    todo!()
                }
                let out_ty = value.ty(self.mir, self.tcx);
                let (lhs, rhs) = (self.emit_operand(lhs), self.emit_operand(rhs));
                let op = choose_op(*op, out_ty.is_signed());
                let k = self.cls(out_ty).0;
                let r = self.tmp(k);
                assert!(lhs.kind == ValKind::Scalar && rhs.kind == ValKind::Scalar);
                self.emit(op, k, r, lhs, rhs);
                // TODO: mask if explicitly wrapping
                r
            }
            Rvalue::Aggregate(kind, fields) => {
                use rustc_middle::mir::AggregateKind::*;
                match **kind {
                    Adt(def, varient, args, _, active) => {
                        assert!(active.is_none(), "TODO: union");
                        let ty = self.finish_type(def, args);
                        let mut layout = self.layout_of(ty);
                        // TODO: pass in the place instead
                        let size = layout.size.bytes_usize();
                        let base = self.alloca(size as i64, ValKind::Memory);
                        if let Variants::Multiple { tag_encoding, tag_field, .. } = &layout.variants {
                            assert!(layout.fields.count() == 1 && tag_encoding == &TagEncoding::Direct);
                            let offset = layout.fields.offset(tag_field.as_usize());
                            let r = self.offset(base, offset);
                            let value = varient.as_u32() as u64;
                            let value = self.r(value, Kl);
                            self.emit(O::storel, Kw, Val::R, value, r);
                            layout = layout.for_variant(self, varient);
                        }
                        
                        for field in layout.fields.index_by_increasing_offset() {
                            let value = &fields[FieldIdx::new(field)];
                            let v = self.emit_operand(value);
                            let offset = layout.fields.offset(field);
                            let r = self.offset(base, offset);
                            match v.kind {
                                ValKind::Scalar => self.emit(Ferb::store(v.k), Kw, Val::R, v, r),
                                ValKind::Pair => todo!(),
                                ValKind::Memory => {
                                    let ty = value.ty(self.mir, self.tcx);
                                    let layout = self.layout_of(ty);
                                    let size = layout.size.bytes_usize();
                                    self.f.blit(self.b, r.r, v.r, size);
                                }
                                ValKind::Undef => todo!(),
                            }
                        }
                        base
                    }
                    _ => todo!("{:?}", value),
                }
            }
            Rvalue::Discriminant(place) => {
                let base = self.addr_place(place);
                let ty = place.ty(self.mir, self.tcx);
                let layout = self.layout_of(ty.ty);
                if let Variants::Multiple { tag_encoding, tag_field, .. } = &layout.variants {
                    assert!(layout.fields.count() == 1 && tag_encoding == &TagEncoding::Direct);
                    assert!(matches!(base.kind, ValKind::Memory));
                    let offset = layout.fields.offset(tag_field.as_usize());
                    let base = self.offset(base, offset);
                    let r = self.tmp(Kl);
                    self.emit(O::load, Kl, r, base, Val::R);
                    return r;
                }
                todo!("discriminant {:?}", place)
            }
            _ => todo!("{:?}", value),
        }
    }
    
    fn tmp(&mut self, k: Ferb::Cls) -> Val {
        Val { r: self.f.tmp(), kind: ValKind::Scalar, k }
    }
    
    fn offset(&mut self, r: Val, off: Size) -> Val {
        if off.bytes() == 0 { return r; }
        let r2 = self.tmp(Kl);
        let off = self.r(off.bytes(), Kl);
        self.emit(O::add, Kl, r2, r, off);
        Val { r: r2.r, kind: r.kind, k: Kl, }
    }
    
    fn addr_place(&mut self, place: &Place<'tcx>) -> Val {
        let ty = place.ty(self.mir, self.tcx);
        if let Some(it) = place.as_local() {
            return self.locals[it];
        }
        let mut base = self.locals[place.local];
        let mut parent_ty = self.mir.local_decls[place.local].ty;
        for it in place.projection.iter() {
            use ProjectionElem::*;
            match it.kind() {
                Deref => {
                    assert!(base.kind == ValKind::Scalar);
                    base.kind = ValKind::Memory;
                    return base;  
                }
                Field(field_idx, ()) => {
                    assert!(matches!(base.kind, ValKind::Memory));
                    use FieldsShape::*;
                    let layout = self.layout_of(parent_ty);
                    let offsets = match &layout.fields {
                        Arbitrary { offsets, .. } => offsets,
                        Primitive => return base,
                        _ => todo!("{:?}", place),
                    };
                    base = self.offset(base, offsets[field_idx]);
                }
                Downcast(_, varient) => {
                    assert!(matches!(base.kind, ValKind::Memory));
                    let layout = self.layout_of(parent_ty);
                    let layout = layout.for_variant(self, varient);
                    let first = layout.layout.fields.index_by_increasing_offset().next().unwrap();
                    base = self.offset(base, layout.fields.offset(first));
                },
                _ => todo!("{:?}", place),
            }
            parent_ty = ty.projection_ty(self.tcx, it).ty;
        }
        base
    }
    
    fn store_place(&mut self, place: &Place<'tcx>, r: Val) {
        let base = self.addr_place(place);
        match base.kind {
            ValKind::Scalar | ValKind::Pair => self.emit(O::copy, r.k, base, r, Val::R),
            ValKind::Memory => {
                match r.kind {
                    ValKind::Scalar => self.emit(Ferb::store(r.k), Kw, Val::R, r, base),
                    ValKind::Pair => todo!(),
                    ValKind::Memory => {
                        let ty = place.ty(self.mir, self.tcx).ty;
                        let size = self.layout_of(ty).size.bytes_usize();
                        self.f.blit(self.b, base.r, r.r, size);
                    }
                    _ => todo!(),
                }
            }
            ValKind::Undef => todo!(),
        };
    }
    
    fn load_place(&mut self, place: &Place<'tcx>) -> Val {
        let ty = place.ty(self.mir, self.tcx).ty;
        let (k, _) = self.cls(ty);
        let base = self.addr_place(place);
        let mut r = self.tmp(k);
        match base.kind {
            ValKind::Scalar => self.emit(O::copy, k, r, base, Val::R),
            ValKind::Pair => {
                assert!(k == Kl);
                self.emit(O::copy, Kl, r, base, Val::R);
                r.kind = ValKind::Pair;
            }
            ValKind::Memory => {
                if ty.is_adt() { return base; }
                self.emit(O::load, k, r, base, Val::R);
            }
            ValKind::Undef => todo!("{:?}", place),
        }
        r
    }
    
    fn r(&mut self, r: impl Reflike, k: Ferb::Cls) -> Val {
        Val { r: r.r(self.f), kind: ValKind::Scalar, k }
    }
    
    fn emit_operand(&mut self, operand: &Operand<'tcx>) -> Val {
        match operand {
            Operand::Copy(place) => self.load_place(place),
            Operand::Move(place) => self.load_place(place),
            Operand::Constant(it) => {
                let (val, ty) = self.finish_const(it);
                match val {
                    ConstValue::Scalar(it) => {
                        match it {
                            Scalar::Int(it) => {
                                let (k, _) = self.cls(operand.ty(self.mir, self.tcx));
                                let raw = it.to_bits(it.size()) as u64;
                                return self.r(raw, k);
                            }
                            Scalar::Ptr(p, _) => {
                                let (p, off) = p.prov_and_relative_offset();
                                self.global_alloc(p.alloc_id(), off, ty)
                            }
                        }
                    }
                    ConstValue::ZeroSized => {
                        // const known function gets here. the value is stored in the type field. 
                        match ty.kind() {
                            &TyKind::FnDef(def, args) => {
                                let id = def_symbol(self.m, self.tcx, def, Some(args));
                                return self.r(id, Kl);
                            },
                            _ => todo!("zst {:?}", ty)
                        }
                    }
                    ConstValue::Slice { alloc_id, meta } => {
                        let p = self.global_alloc(alloc_id, Size::ZERO, ty);
                        self.create_pair(p, meta)
                    }
                    _ => todo!("{:?}", operand),
                }
            }
            _ => todo!("{:?}", operand),
        }
    }
    
    // TODO: dumb because i know im slow at promoting if you keep recalculating the address for the second slot.
    fn create_pair(&mut self, a: Val, b: impl Reflike) -> Val {
        let b = self.r(b, Kl);
        let r = self.alloca(16, ValKind::Pair);
        let r2 = self.offset(r, Size::from_bytes(8));
        self.emit(O::storel, Kw, Val::R, a, r);
        self.emit(O::storel, Kw, Val::R, b, r2);
        r
    }
    
    fn get_pair_slot(&mut self, addr: Val, first: bool) -> Val {
        assert!(addr.kind == ValKind::Pair);
        let addr = self.offset(addr, Size::from_bytes(if first { 0 } else { 8 }));
        let r = self.tmp(Kl);
        self.emit(O::load, Kl, r, addr, Val::R);
        r
    }
    
    fn global_alloc(&mut self, p: AllocId, off: Size, ty: Ty) -> Val {
        let p = self.tcx.global_alloc(p);
        assert_eq!(off.bytes(), 0, "TODO: offset ptr");
        match p {
            GlobalAlloc::Memory(it) => {
                let (bytes, segment) = get_all_bytes(it);
                assert!(segment == Ferb::Seg::ConstantData, "TODO: need to deduplicate them so you get the same pointer");
                let id = self.m.anon();
                self.m.data(Ferb::Data {
                    id,
                    segment,
                    template: Ferb::Template::Bytes(bytes),
                    rel: vec![],
                });
                return self.r(id, Kl);
            }
            GlobalAlloc::Static(def) => {
                let id = def_symbol(self.m, self.tcx, def, None);
                return self.r(id, Kl);
            }
            _ => todo!("{:?} {:?}", p, ty),
        }
    }
    
    fn alloca(&mut self, size: i64, kind: ValKind) -> Val {
        let r = self.f.tmp();
        self.f.emit(self.start_block, O::alloc8, Kl, r, size, ());
        Val { r, kind, k: Kl, }
    }
    
    fn cls(&self, ty: Ty<'tcx>) -> (Ferb::Cls, ValKind) {
        if ty.is_adt() {
            return (Kl, ValKind::Memory);
        }
        if ty.is_any_ptr() {
            return (Kl, if is_wide(ty) { ValKind::Pair } else { ValKind::Scalar });
        }
        use rustc_ast::UintTy::*;
        let k = |it| match it {
            U8 | U16 | U32 => Kw,
            U64 | Usize /*TODO*/ => Kl,
            U128 => todo!(),
        };
        (match ty.kind() {
            TyKind::Bool | TyKind::Char => Kw,
            TyKind::Int(it) => k(it.to_unsigned()),
            TyKind::Uint(it) => k(*it),
            TyKind::Float(it) => match it.bit_width() {
                32 => Ks,
                64 => Kd,
                n => todo!("f{}", n),
            },
            TyKind::FnDef(_, _) | TyKind::FnPtr(_, _) => Kl,
            TyKind::Never => Kl,  // eh...
            _ => todo!("{:?}", ty),
        }, ValKind::Scalar)
    }
    
    // gets rid of ::Unevaluated
    fn finish_const(&mut self, it: &ConstOperand<'tcx>) -> (ConstValue, rustc_middle::ty::Ty<'tcx>) {
        let mono = TypingEnv::fully_monomorphized();
        let b = EarlyBinder::bind(it.const_);
        let v = self.instance.instantiate_mir_and_normalize_erasing_regions(self.tcx, mono, b);
        let val = v.eval(self.tcx, mono, it.span).unwrap();
        (val, v.ty())
    }
    
    fn finish_type(&mut self, def: DefId, args: GenericArgsRef<'tcx>) -> Ty<'tcx> {
        let ty = self.tcx.type_of(def);
        let mono = TypingEnv::fully_monomorphized();
        self.tcx.instantiate_and_normalize_erasing_regions(args, mono, ty)
    }

    pub fn emit(&mut self, o: O, k: Ferb::Cls, to: Val, a0: Val, a1: Val) {
        self.f.emit(self.b, o, k, to.r, a0.r, a1.r);
    }
}

fn def_symbol<'tcx>(m: &mut Ferb::Module, tcx: TyCtxt<'tcx>, def: DefId, args: Option<GenericArgsRef<'tcx>>) -> Ferb::Id<Ferb::Sym> {
    let span = tcx.def_span(def);
    let mono = TypingEnv::fully_monomorphized();
    let instance = match args {
        Some(args) => Instance::expect_resolve(tcx, mono, def, args, span),
        None => Instance::mono(tcx, def),
    };
    let id = m.intern(tcx.symbol_name(instance).name);
    id
}

fn get_all_bytes<'tcx>(it: ConstAllocation<'tcx>) -> (&'tcx [u8], Ferb::Seg) {
    let it = it.inner();
    assert!(it.provenance().provenances().next().is_none(), "TODO: rel");
    let range = alloc_range(Size::from_bytes(0), it.size());
    use rustc_ast::Mutability::*;
    let seg = match it.mutability {
        Not => Ferb::Seg::ConstantData,
        Mut => Ferb::Seg::MutableData,
    };
    (it.get_bytes_unchecked(range), seg)
}

fn is_wide(ty: Ty) -> bool {
    if !ty.is_any_ptr() { return false };
    let inner = ty.builtin_deref(true).unwrap();
    inner.is_str() || inner.is_array_slice()
}

impl Val {
    const R: Self = Self { r: Ferb::Ref::Null, kind: ValKind::Scalar, k: Kw, };
}

fn choose_op(op: BinOp, signed: bool) -> Ferb::O {
    use Ferb::O::*;
    use BinOp::*;    
    match op {
        Add | AddUnchecked => add,
        Sub | SubUnchecked => sub,
        Mul | MulUnchecked => mul,
        Div => if signed { div } else { udiv },
        Rem => if signed { rem } else { urem },
        BitXor => xor,
        BitAnd => and,
        BitOr => or,
        Shl | ShlUnchecked => shl,
        Shr | ShrUnchecked => if signed { sar } else { shr },
        Eq => ceql,
        Lt => if signed { csltl } else { cultl },
        Le => if signed { cslel } else { culel },
        Ne => cnel,
        Ge => if signed { csgel } else { cugel },
        Gt => if signed { csgtl } else { cugtl },
        _ => todo!("{:?}", op),
    }
}

impl<'tcx> HasDataLayout for Emit<'_, 'tcx> {
    fn data_layout(&self) -> &rustc_abi::TargetDataLayout {
        &self.tcx.data_layout
    }
}

impl<'tcx> HasTypingEnv<'tcx> for Emit<'_, 'tcx> {
    fn typing_env(&self) -> TypingEnv<'tcx> {
        TypingEnv::fully_monomorphized()
    }
}
impl<'tcx> HasTyCtxt<'tcx> for Emit<'_, 'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
}
impl<'tcx> LayoutOfHelpers<'tcx> for Emit<'_, 'tcx> {
    type LayoutOfResult = layout::TyAndLayout<'tcx>;

    fn handle_layout_err(&self, _: layout::LayoutError<'tcx>, _: Span, _: Ty<'tcx>) -> <Self::LayoutOfResult as layout::MaybeResult<layout::TyAndLayout<'tcx>>>::Error {
        todo!()
    }
}
