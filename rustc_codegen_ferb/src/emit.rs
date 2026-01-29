use rustc_const_eval::interpret::{AllocId, ConstAllocation, GlobalAlloc, Scalar, alloc_range};
use rustc_hir::def_id::DefId;
use rustc_index::{Idx, IndexVec, bit_set::MixedBitSet};
use rustc_middle::{mir::{BasicBlock, BasicBlockData, BinOp, Body, CastKind, ConstOperand, ConstValue, Local, Operand, Place, ProjectionElem, RETURN_PLACE, Rvalue, StatementKind, TerminatorKind, UnOp, mono::{CodegenUnit, MonoItem}, pretty::MirWriter}, ty::{EarlyBinder, GenericArgsRef, Instance, PseudoCanonicalInput, Ty, TyCtxt, TyKind, TypingEnv, layout::{self, HasTyCtxt, HasTypingEnv, LayoutOf, LayoutOfHelpers, TyAndLayout}}};
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
    return_block: Ferb::BlkId,
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
                let mir = tcx.instance_mir(it.def);
                let mono = TypingEnv::fully_monomorphized();
                let ret_ty = EarlyBinder::bind(mir.return_ty());
                let ret_ty = it.instantiate_mir_and_normalize_erasing_regions(tcx, mono, ret_ty);
                
                // TODO: sometimes it decides this is an error
                // let mut buf = Vec::new();
                // let writer = MirWriter::new(tcx);
                // writer.write_mir_fn(mir, &mut buf).unwrap();
                // println!("{}", String::from_utf8_lossy(&buf).into_owned());
                
                let ret = abi_type(&mut m, tcx, ret_ty);
                let mut f = Ferb::Func::new(id, ret);
                let start_block = f.blk();
                let undef = Val { r: Ferb::Ref::Undef, kind: ValKind::Undef, k: Kw };
                let mut emit = Emit {
                    tcx,
                    blocks: mir.basic_blocks.iter().map(|_| f.blk()).collect(),
                    locals: mir.local_decls.iter().map(|_| undef).collect(),
                    return_block: f.blk(),
                    b: start_block,
                    m: &mut m,
                    f: &mut f,
                    instance: it,
                    start_block,
                    mir,
                };
                for i in 0..mir.arg_count {
                    let local = Local::new(i + 1);
                    let ty = emit.mono_ty(mir.local_decls[local].ty);
                    let repr = abi_type(emit.m, tcx, ty);
                    let (k, kind) = emit.cls(ty);
                    let mut r = emit.tmp(k);
                    r.kind = kind;
                    match repr {
                        Ferb::Ret::Void => todo!(),
                        Ferb::Ret::K(kk) => {
                            assert!(k == kk);
                            emit.emit(O::par, k, r, Val::R, Val::R)
                        }
                        Ferb::Ret::T(t) => {
                            emit.f.emit(emit.b, O::parc, k, r.r, t, ());
                            if r.kind == ValKind::Scalar {
                                r.kind = ValKind::Memory;
                            }
                        }
                    }
                    emit.locals[local] = r;
                }
                if cfg!(debug_assertions) { // && tcx.sess.opts.debug_assertions {  // TODO
                    let loc = tcx.def_span(it.def.def_id());
                    let loc = tcx.sess.source_map().span_to_diagnostic_string(loc.shrink_to_lo());
                    emit.f.comment(emit.m, emit.start_block, &*format!("{}", loc));
                }
                emit.allocate_locals();
                emit.f.jump(emit.b, J::jmp, (), Some(emit.blocks[BasicBlock::new(0)]), None);
                emit.emit_return_block(ret);
                
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
            let (k, mut kind) = self.cls(it.ty);
            let size = self.layout(it.ty).size.bytes() as i64;
            let is_arg = self.locals[local].kind != ValKind::Undef;
            if is_arg {
                kind = self.locals[local].kind;
            }
            self.locals[local] = match kind {
                ValKind::Scalar => if needs_alloca.contains(local) {
                    let r = self.alloca(size, ValKind::Memory);
                    if is_arg {
                        self.emit(Ferb::store(k), Kw, Val::R, self.locals[local], r);
                    }
                    r
                } else {
                    if is_arg { continue }
                    self.tmp(k)
                }
                ValKind::Pair | ValKind::Memory => {
                    if is_arg { continue }
                    self.alloca(size, kind)
                }
                ValKind::Undef => todo!(),
            }
        }
    }
    
    fn emit_return_block(&mut self, ret: Ferb::Ret) {
        self.b = self.return_block;
        let ty = self.mir.return_ty();
        if matches!(ty.kind(), TyKind::Never) {
            self.f.jump(self.b, J::hlt, (), None, None);
            return;
        }
        let r = self.locals[RETURN_PLACE];
        let j = match ret {
            Ferb::Ret::K(k) => match k {
                Kw => J::retw,
                Kl => J::retl,
                Ks => J::rets,
                Kd => J::retd,
            },
            Ferb::Ret::Void => J::ret0,
            Ferb::Ret::T(_) => J::retc,
        };
        let r = if ret != Ferb::Ret::Void { r.r } else { Ferb::Ref::Null };
        self.f.jump(self.b, j, r, None, None);
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
            TerminatorKind::Return => self.f.jump(self.b, J::jmp, (), Some(self.return_block), None),
            TerminatorKind::Call { func, args, destination, target, .. } => {
                let callee = self.emit_operand(func);
                let sig = func.ty(self.mir, self.tcx).fn_sig(self.tcx);
                let arg_count = sig.inputs().skip_binder().len();
                let arg_vals = args.iter().map(|arg| self.emit_operand(&arg.node)).collect::<Vec<_>>();
                for (i, &arg) in arg_vals.iter().enumerate() {
                    let mut arg = arg;
                    if i == arg_count {
                        assert!(sig.c_variadic());
                        self.f.emit(self.b, O::argv, Kw, (), (), ());
                    }
                    
                    let ty = self.mono_ty(args[i].node.ty(self.mir, self.tcx));
                    let repr = abi_type(self.m, self.tcx, ty);
                    match repr {
                        Ferb::Ret::Void => todo!(),
                        Ferb::Ret::K(k) => {
                            assert!(arg.kind == ValKind::Scalar && arg.k == k);
                            self.f.emit(self.b, O::arg, arg.k, (), arg.r, ());
                        }
                        Ferb::Ret::T(t) => {
                            if arg.kind == ValKind::Scalar {
                                let r = self.alloca(8, ValKind::Memory);
                                self.emit(Ferb::store(arg.k), Kw, Val::R, arg, r);
                                arg = r;
                                // todo!()
                            }
                            self.f.emit(self.b, O::argc, Kl, (), t, arg.r);
                        }
                    }
                }
                if sig.c_variadic() && args.len() == arg_count {
                    // wasm cares if variadic even if none passed
                    self.f.emit(self.b, O::argv, Kw, (), (), ());
                }
                
                let ret = sig.output();
                let ret = ret.no_bound_vars().unwrap();
                let ret = self.mono_ty(ret);
                let ret = abi_type(self.m, self.tcx, ret);
                match ret {
                    Ferb::Ret::K(k) => {
                        let r = self.tmp(k);
                        self.f.emit(self.b, O::call, k, r.r, callee.r, ());
                        self.store_place(destination, r);
                    },
                    Ferb::Ret::Void => self.f.emit(self.b, O::call, Kw, (), callee.r, ()),
                    Ferb::Ret::T(t) => {
                        let (_, kind) = self.cls(sig.output().skip_binder());
                        let mut r = self.tmp(Kl);
                        r.kind = kind;
                        self.f.emit(self.b, O::call, Kl, r.r, callee.r, t);
                        self.store_place(destination, r);
                    }
                }
                let j = target.map(|_| J::jmp).unwrap_or(J::hlt);
                let target = target.map(|it| self.blocks[it]);
                self.f.jump(self.b, j, (), target, None);
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                let discr = self.emit_operand(discr);
                assert!(discr.kind == ValKind::Scalar);
                if let Some((val, a, b)) = targets.as_static_if() {
                    if val == 0 && discr.k == Kw {
                        self.f.jump(self.b, J::jnz, discr.r, Some(self.blocks[b]), Some(self.blocks[a]));
                        return;
                    }
                }
                // TODO: don't assume Kl
                // :SLOW
                let mut next = self.f.blk();
                for (&val, &dest) in targets.all_values().iter().zip(targets.all_targets()) {
                    let cond = self.f.tmp();
                    self.f.emit(self.b, O::ceql, Kl, cond, discr.r, val.0 as u64);
                    self.f.jump(self.b, J::jnz, cond, Some(self.blocks[dest]), Some(next));
                    self.b = next;
                    next = self.f.blk();
                }
                self.f.jump(self.b, J::jmp, (), Some(self.blocks[targets.otherwise()]), None);
            }
            TerminatorKind::Unreachable => self.f.jump(self.b, J::hlt, (), None, None),
            TerminatorKind::Assert { cond, expected, target, msg, .. } => {
                // TODO: emit the operands properly and call the panic handler. 
                // TODO: am i supposed to check cfg here or does that happen in the frontend? 
                //       (yes, at least for overflow says comment on the enum)
                let failed = self.f.blk();
                let msg = format!("{:?}\n\0", msg);  
                let id = self.m.anon();
                self.m.data(Ferb::Data {
                    id,
                    segment: Ferb::Seg::ConstantData,
                    template: Ferb::Template::Bytes(msg.as_bytes()),
                    rel: vec![],
                });
                let puts = self.m.intern("puts");
                self.f.emit(failed, O::arg, Kl, (), id, ());
                self.f.emit(failed, O::call, Kw, (), puts, ());
                self.f.jump(failed, J::hlt, (), None, None);
                
                let cond = self.emit_operand(cond);
                let dest = [failed, self.blocks[*target]];
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
                        let d = dest_ty.primitive_size(self.tcx).bytes();
                        let s = src_ty.primitive_size(self.tcx).bytes();
                        assert!(d == s);
                        src
                    },
                    CastKind::PointerWithExposedProvenance => src,
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
                let in_ty = lhs.ty(self.mir, self.tcx);
                let (lhs, rhs) = (self.emit_operand(lhs), self.emit_operand(rhs));
                let k = self.cls(out_ty).0;
                assert!(lhs.kind == ValKind::Scalar && rhs.kind == ValKind::Scalar);
                let mut r = self.tmp(k);
                if let Some(op) = (*op).overflowing_to_wrapping() {
                    let op = choose_op(op, in_ty.is_signed());
                    let k = self.cls(in_ty).0;
                    r.kind = ValKind::Memory;
                    let rr = self.tmp(k);
                    self.f.emit(self.start_block, O::alloc8, Kl, r.r, 16, ());
                    self.emit(op, k, rr, lhs, rhs);
                    self.emit(Ferb::store(k), Kw, Val::R, rr, r);
                    // TODO: 8/16/128
                    let ok = self.offset(r, Size::from_bytes(if k == Kl || k == Kd { 8 } else { 4 }));  
                    // TODO: do this properly! for now just lying and saying it didn't overflow
                    let zero = self.r(0u64, Kw);  
                    self.emit(O::storew, Kw, Val::R, zero, ok);
                } else {
                    let op = choose_op(*op, out_ty.is_signed());
                    self.emit(op, k, r, lhs, rhs);
                    // TODO: mask if explicitly wrapping
                }
                r
            }
            Rvalue::Aggregate(kind, fields) => {
                use rustc_middle::mir::AggregateKind::*;
                let ty = value.ty(self.mir, self.tcx);
                let mut layout = self.layout(ty);
                let size = layout.size.bytes_usize();
                // TODO: pass in the place instead
                let base = self.alloca(size as i64, ValKind::Memory);
                match **kind {
                    Adt(_, varient, _, _, active) => {
                        assert!(active.is_none(), "TODO: union");
                        if let Variants::Multiple { tag_encoding, tag_field, .. } = &layout.variants {
                            assert!(layout.fields.count() == 1 && tag_encoding == &TagEncoding::Direct);
                            let offset = layout.fields.offset(tag_field.as_usize());
                            let r = self.offset(base, offset);
                            let value = varient.as_u32() as u64;
                            let value = self.r(value, Kl);
                            self.emit(O::storel, Kw, Val::R, value, r);
                            layout = layout.for_variant(self, varient);
                        }
                    }
                    Tuple => (),
                    _ => todo!("{:?}", value),
                }
                self.emit_aggregate(base, layout, fields);
                base
            }
            Rvalue::Discriminant(place) => {
                let base = self.addr_place(place);
                let ty = place.ty(self.mir, self.tcx);
                let layout = self.layout(ty.ty);
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
    
    fn layout(&self, ty: Ty<'tcx>) -> TyAndLayout<'tcx> {
        let ty = self.mono_ty(ty);
        self.layout_of(ty)
    }
    
    fn emit_aggregate(&mut self, base: Val, layout: TyAndLayout<'tcx>, fields: &IndexVec<FieldIdx, Operand<'tcx>>) {
        for field in layout.fields.index_by_increasing_offset() {
            let value = &fields[FieldIdx::new(field)];
            let v = self.emit_operand(value);
            let offset = layout.fields.offset(field);
            let r = self.offset(base, offset);
            match v.kind {
                ValKind::Scalar => self.emit(Ferb::store(v.k), Kw, Val::R, v, r),
                ValKind::Pair | ValKind::Memory => {
                    let ty = value.ty(self.mir, self.tcx);
                    let layout = self.layout(ty);
                    let size = layout.size.bytes_usize();
                    self.f.blit(self.b, r.r, v.r, size);
                }
                ValKind::Undef => todo!(),
            }
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
        let mut projection = place.projection.iter();
        if place.projection[0].kind() == ProjectionElem::Deref {
            projection.next();
        };
        base.kind = ValKind::Memory;
        for it in projection {
            use ProjectionElem::*;
            match it.kind() {
                Deref => {
                    todo!()
                }
                Field(field_idx, ()) => {
                    assert!(matches!(base.kind, ValKind::Memory));
                    use FieldsShape::*;
                    let layout = self.layout(parent_ty);
                    let offsets = match &layout.fields {
                        Arbitrary { offsets, .. } => offsets,
                        Primitive => return base,
                        _ => todo!("{:?}", place),
                    };
                    base = self.offset(base, offsets[field_idx]);
                }
                Downcast(_, varient) => {
                    assert!(matches!(base.kind, ValKind::Memory));
                    let layout = self.layout(parent_ty);
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
                        let size = self.layout(ty).size.bytes_usize();
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
            Operand::RuntimeChecks(it) => {
                let it = it.value(self.tcx.sess);
                self.r(it as u64, Kw)
            },
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
        let ty = self.mono_ty(ty);
        val_cls(ty)
    }
    
    fn mono_ty(&self, it: Ty<'tcx>) -> Ty<'tcx> {
        let mono = TypingEnv::fully_monomorphized();
        let it = EarlyBinder::bind(it);
        self.instance.instantiate_mir_and_normalize_erasing_regions(self.tcx, mono, it)
    }
    
    // gets rid of ::Unevaluated
    fn finish_const(&mut self, it: &ConstOperand<'tcx>) -> (ConstValue, rustc_middle::ty::Ty<'tcx>) {
        let mono = TypingEnv::fully_monomorphized();
        let b = EarlyBinder::bind(it.const_);
        let v = self.instance.instantiate_mir_and_normalize_erasing_regions(self.tcx, mono, b);
        let val = v.eval(self.tcx, mono, it.span).unwrap();
        (val, v.ty())
    }
    
    pub fn emit(&mut self, o: O, k: Ferb::Cls, to: Val, a0: Val, a1: Val) {
        self.f.emit(self.b, o, k, to.r, a0.r, a1.r);
    }
}

fn val_cls(ty: Ty) -> (Ferb::Cls, ValKind) {
    if ty.is_adt() || matches!(ty.kind(), TyKind::Tuple(_)) {
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
        TyKind::Never => Kl,
        TyKind::Param(_) => unreachable!("monomorphise"),
        _ => todo!("{:?}", ty),
    }, ValKind::Scalar)
}

fn layout_of<'tcx>(tcx: TyCtxt<'tcx>, value: Ty<'tcx>) -> TyAndLayout<'tcx> {
    tcx.layout_of(PseudoCanonicalInput { value,  typing_env: TypingEnv::fully_monomorphized() }).unwrap()
}

fn abi_type<'tcx>(m: &mut Ferb::Module, tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Ferb::Ret {
    let (k, kind) = val_cls(ty);
    if kind == ValKind::Scalar {
        return Ferb::Ret::K(k);
    }
    let layout = layout_of(tcx, ty);
    if layout.size.bytes() == 0 {
        return Ferb::Ret::Void;
    }
    // TODO: proper abi
    let t = m.typ(Ferb::TypeLayout {
        align: layout.align.bytes_usize(),
        size: layout.size.bytes_usize(),
        cases: vec![],
        is_union: false,
    });
    Ferb::Ret::T(t)
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
