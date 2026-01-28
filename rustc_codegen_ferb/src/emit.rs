use rustc_const_eval::interpret::{AllocId, GlobalAlloc, Scalar, alloc_range};
use rustc_hir::def_id::DefId;
use rustc_index::{Idx, IndexVec};
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
                let undef = Val { r: Ferb::Ref::Undef, kind: ValKind::Undef };
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
                    let mut r = emit.tmp();
                    emit.emit(O::par, Kl, r, Val::R, Val::R);
                    let local = Local::new(i + 1);
                    let ty = mir.local_decls[local].ty;
                    if ty.is_adt() {
                        r.kind = ValKind::Memory;
                    }
                    if ty.is_any_ptr() && (ty.builtin_deref(true).unwrap().is_str() || ty.builtin_deref(true).unwrap().is_array_slice()) {
                        r.kind = ValKind::Pair;
                    }
                    emit.locals[local] = r;
                }
                
                emit.f.jump(emit.b, J::jmp, (), Some(emit.blocks[BasicBlock::new(0)]), None);
                for (bid, blk) in mir.basic_blocks.iter_enumerated() {
                    emit.b = emit.blocks[bid]; 
                    emit.emit_block(blk);
                }
                m.func(f);
            },
            MonoItem::Static(_) => todo!(),
            MonoItem::GlobalAsm(_) => todo!(),
        } 
    }
    
    m
}

impl<'f, 'tcx> Emit<'f, 'tcx> {
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
                
                let args = args.iter().map(|arg| self.emit_operand(&arg.node)).collect::<Vec<_>>();
                for arg in args {
                    self.f.emit(self.b, O::arg, Kl, (), arg.r, ());
                }
                let r = self.tmp();
                self.emit(O::call, Kl, r, callee, Val::R);
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
            _ => todo!("{:?}", terminator),
        }
    }
    
    fn emit_value(&mut self, value: &Rvalue<'tcx>) -> Val {
        match value {
            Rvalue::Use(operand) => self.emit_operand(operand),
            Rvalue::RawPtr(_, place) => {
                assert!(place.projection.len() == 1 && place.projection[0].kind() == ProjectionElem::Deref);
                let local = place.local;
                self.locals[local]
            }
            Rvalue::Cast(kind, value, dest_ty) => {
                let src = self.emit_operand(value);
                let src_ty = value.ty(&self.mir.local_decls, self.tcx);
                match kind {
                    CastKind::Transmute => src,
                    CastKind::PtrToPtr => {
                        // TODO: must be a less painful way to check if its just getting the first slot out of a wide pointer. 
                        let str_to_ptr = src_ty.is_any_ptr() && src_ty.builtin_deref(true).unwrap().is_str() && dest_ty.is_any_ptr();
                        if str_to_ptr {
                            return self.get_pair_slot(src, true);
                        }
                        todo!("PtrToPtr {:?} {:?}", src_ty, dest_ty);
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
                    _ => todo!("{:?} {:?}", op, value)
                }
            }
            Rvalue::BinaryOp(op, box(lhs, rhs)) => {
                let (lhs, rhs) = (self.emit_operand(lhs), self.emit_operand(rhs));
                // TODO: don't assume u64
                let op = choose_op(*op, false);
                let r = self.tmp();
                self.emit(op, Kl, r, lhs, rhs);
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
                            let value = self.r(value);
                            self.emit(O::storel, Kw, Val::R, value, r);
                            layout = layout.for_variant(self, varient);
                        }
                        
                        for field in layout.fields.index_by_increasing_offset() {
                            let value = &fields[FieldIdx::new(field)];
                            let v = self.emit_operand(value);
                            let offset = layout.fields.offset(field);
                            let r = self.offset(base, offset);
                            
                            match v.kind {
                                ValKind::Scalar => self.emit(O::storel, Kw, Val::R, v, r),
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
                    let r = self.tmp();
                    self.emit(O::load, Kl, r, base, Val::R);
                    return r;
                }
                todo!("discriminant {:?}", place)
            }
            Rvalue::Ref(_, _, place) => self.addr_place(place),
            _ => todo!("{:?}", value),
        }
    }
    
    fn tmp(&mut self) -> Val {
        Val { r: self.f.tmp(), kind: ValKind::Scalar }
    }
    
    fn offset(&mut self, r: Val, off: Size) -> Val {
        if off.bytes() == 0 { return r; }
        let r2 = self.tmp();
        let off = self.r(off.bytes());
        self.emit(O::add, Kl, r2, r, off);
        Val { r: r2.r, kind: r.kind }
    }
    
    fn addr_place(&mut self, place: &Place<'tcx>) -> Val {
        let ty = place.ty(self.mir, self.tcx);
        if let Some(it) = place.as_local() {
            return self.locals[it];
        }
        let mut base = self.locals[place.local];
        let mut parent_ty = self.mir.local_decls[place.local].ty;
        assert!(matches!(base.kind, ValKind::Memory));
        for it in place.projection.iter() {
            use ProjectionElem::*;
            match it.kind() {
                Deref => (),  // TODO: this can't be right
                Field(field_idx, ()) => {
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
    
    fn store_place(&mut self, place: &Place<'tcx>, mut r: Val) {
        if let Some(local) = place.as_local() {
            if self.locals[local].kind == ValKind::Undef {
                if r.kind == ValKind::Scalar {
                    let v = self.tmp();
                    self.emit(O::copy, Kl, v, r, Val::R);
                    r = v;
                }
                self.locals[local] = r;
                return;
            }
        }
        let base = self.addr_place(place);
        match base.kind {
            ValKind::Scalar | ValKind::Pair => self.emit(O::copy, Kl, base, r, Val::R),
            ValKind::Memory => {
                assert!(r.kind == ValKind::Scalar);
                self.emit(O::storel, Kw, Val::R, r, base);
            }
            ValKind::Undef => todo!(),
        };
    }
    
    fn load_place(&mut self, place: &Place<'tcx>) -> Val {
        let ty = place.ty(self.mir, self.tcx).ty;
        let base = self.addr_place(place);
        let mut r = self.tmp();
        match base.kind {
            ValKind::Scalar => self.emit(O::copy, Kl, r, base, Val::R),
            ValKind::Pair => {
                self.emit(O::copy, Kl, r, base, Val::R);
                r.kind = ValKind::Pair;
            }
            ValKind::Memory => {
                if ty.is_adt() { return base; }
                self.emit(O::load, Kl, r, base, Val::R);
            }
            ValKind::Undef => todo!(),
        }
        r
    }
    
    fn r(&mut self, r: impl Reflike) -> Val {
        Val { r: r.r(self.f), kind: ValKind::Scalar }
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
                                let it = it.to_u64() as i64;
                                return self.r(it);
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
                                let span = self.tcx.def_span(def);
                                let mono = TypingEnv::fully_monomorphized();
                                let instance = Instance::expect_resolve(self.tcx, mono, def, args, span);
                                let id = self.m.intern(self.tcx.symbol_name(instance).name);
                                return self.r(id);
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
        let b = self.r(b);
        let r = self.alloca(16, ValKind::Pair);
        let r2 = self.offset(r, Size::from_bytes(8));
        self.emit(O::storel, Kw, Val::R, a, r);
        self.emit(O::storel, Kw, Val::R, b, r2);
        r
    }
    
    fn get_pair_slot(&mut self, addr: Val, first: bool) -> Val {
        assert!(addr.kind == ValKind::Pair);
        let addr = self.offset(addr, Size::from_bytes(if first { 0 } else { 8 }));
        let r = self.tmp();
        self.emit(O::load, Kl, r, addr, Val::R);
        r
    }
    
    fn global_alloc(&mut self, p: AllocId, off: Size, ty: Ty) -> Val {
        let p = self.tcx.global_alloc(p);
        assert_eq!(off.bytes(), 0, "TODO: offset ptr");
        match p {
            GlobalAlloc::Memory(it) => {
                let it = it.inner();
                let bytes = it.get_bytes_unchecked(alloc_range(Size::from_bytes(0), it.size()));
                assert!(it.mutability.is_not(), "TODO: need to deduplicate them so you get the same pointer");
                let id = self.m.anon();
                self.m.data(Ferb::Data {
                    id,
                    segment: Ferb::Seg::ConstantData,
                    template: Ferb::Template::Bytes(bytes),
                    rel: vec![],
                });
                return self.r(id);
            }
            _ => todo!("{:?} {:?}", p, ty),
        }
    }
    
    fn alloca(&mut self, size: i64, kind: ValKind) -> Val {
        let r = self.f.tmp();
        self.f.emit(self.start_block, O::alloc8, Kl, r, size, ());
        Val { r, kind }
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

impl Val {
    const R: Self = Self { r: Ferb::Ref::Null, kind: ValKind::Scalar, };
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
