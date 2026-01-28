use rustc_const_eval::interpret::{AllocId, GlobalAlloc, Scalar, alloc_range};
use rustc_hir::def_id::DefId;
use rustc_index::{Idx, IndexVec};
use rustc_middle::{mir::{BasicBlock, BasicBlockData, BinOp, Body, CastKind, ConstOperand, ConstValue, Local, Operand, Place, ProjectionElem, RETURN_PLACE, Rvalue, StatementKind, TerminatorKind, UnOp, mono::{CodegenUnit, MonoItem}}, ty::{EarlyBinder, GenericArgsRef, Instance, Ty, TyCtxt, TyKind, TypingEnv, layout::{self, HasTyCtxt, HasTypingEnv, LayoutOf, LayoutOfHelpers}}};
use ferb::builder as Ferb;
use Ferb::Cls::*;
use Ferb::{J, O};
use rustc_abi::{FieldIdx, FieldsShape, HasDataLayout, Primitive, Size, TagEncoding, Variants};
use rustc_span::Span;

struct Emit<'f, 'tcx> {
    tcx: TyCtxt<'tcx>,
    m: &'f mut Ferb::Module,
    f: &'f mut Ferb::Func,
    b: Ferb::BlkId,
    blocks: IndexVec<BasicBlock, Ferb::BlkId>,
    locals: IndexVec<Local, Ferb::Ref>,
    instance: Instance<'tcx>,
    start_block: Ferb::BlkId,
    mir: &'tcx Body<'tcx>,
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
                let mut emit = Emit {
                    tcx,
                    blocks: mir.basic_blocks.iter().map(|_| f.blk()).collect(),
                    locals: mir.local_decls.iter().map(|_| f.tmp()).collect(),
                    b: start_block,
                    m: &mut m,
                    f: &mut f,
                    instance: it,
                    start_block,
                    mir,
                };
                for i in 0..mir.arg_count {
                    emit.f.emit(emit.b, O::par, Kl, emit.locals[Local::new(i + 1)], (), ());
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
                self.f.jump(self.b, J::retl, self.locals[RETURN_PLACE], None, None);
            }
            TerminatorKind::Call { func, args, destination, target, .. } => {
                let dest = self.locals[destination.local];
                let callee = self.emit_operand(func);
                for arg in args {
                    let arg = self.emit_operand(&arg.node);
                    self.f.emit(self.b, O::arg, Kl, (), arg, ());
                }
                self.f.emit(self.b, O::call, Kl, dest, callee, ());
                let j = target.map(|_| J::jmp).unwrap_or(J::hlt);
                let target = target.map(|it| self.blocks[it]);
                self.f.jump(self.b, j, (), target, None);
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                let discr = self.emit_operand(discr);
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
    
    fn emit_value(&mut self, value: &Rvalue<'tcx>) -> Ferb::Ref {
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
                let r = self.f.tmp();
                self.f.emit(self.b, op, Kl, r, lhs, rhs);
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
                        let base = self.alloca(layout.size.bytes_usize() as i64);
                        if let Variants::Multiple { tag_encoding, tag_field, .. } = &layout.variants {
                            assert!(layout.fields.count() == 1 && tag_encoding == &TagEncoding::Direct);
                            let offset = layout.fields.offset(tag_field.as_usize());
                            let r = self.offset(base, offset);
                            let value = varient.as_u32() as u64;
                            self.f.emit(self.b, O::storel, Kw, (), value, r);
                            layout = layout.for_variant(self, varient);
                        }
                        
                        for field in layout.fields.index_by_increasing_offset() {
                            let value = &fields[FieldIdx::new(field)];
                            let value = self.emit_operand(value);
                            let offset = layout.fields.offset(field);
                            let r = self.offset(base, offset);
                            self.f.emit(self.b, O::storel, Kw, (), value, r);
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
                    let offset = layout.fields.offset(tag_field.as_usize());
                    let base = self.offset(base, offset);
                    let r = self.f.tmp();
                    self.f.emit(self.b, O::load, Kl, r, base, ());
                    return r;
                }
                todo!("discriminant {:?}", place)
            }
            _ => todo!("{:?}", value),
        }
    }
    
    fn offset(&mut self, r: Ferb::Ref, off: Size) -> Ferb::Ref {
        if off.bytes() == 0 { return r; }
        let r2 = self.f.tmp();
        self.f.emit(self.b, O::add, Kl, r2, r, off.bytes());
        r2
    }
    
    fn addr_place(&mut self, place: &Place<'tcx>) -> Ferb::Ref {
        let ty = place.ty(self.mir, self.tcx);
        if let Some(it) = place.as_local() {
            return self.locals[it];
        }
        let mut base = self.locals[place.local];
        let mut parent_ty = self.mir.local_decls[place.local].ty;
        for it in place.projection.iter() {
            use ProjectionElem::*;
            match it.kind() {
                Deref => todo!(),
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
    
    // when place.as_local, addr_place could still be a stack address 
    // (for wide pointers) which is convoluted. should make it more consistant. 
    // have something like compiler/emit_ir.fr/Placement that i can pass around. 
    fn store_place(&mut self, place: &Place<'tcx>, r: Ferb::Ref) {
        let base = self.addr_place(place);
        if place.as_local().is_some() {
            self.f.emit(self.b, O::copy, Kl, base, r, ());
            return;
        }
        self.f.emit(self.b, O::storel, Kw, (), r, base);
    }
    
    fn load_place(&mut self, place: &Place<'tcx>) -> Ferb::Ref {
        let base = self.addr_place(place);
        if place.as_local().is_some() {
            return base;
        }
        let r = self.f.tmp();
        self.f.emit(self.b, O::load, Kl, r, base, ());
        r
    }
    
    fn emit_operand(&mut self, operand: &Operand<'tcx>) -> Ferb::Ref {
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
                                return self.f.con(Ferb::Id::None, it);
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
                                return self.f.con(id, 0);
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
    fn create_pair(&mut self, a: impl Ferb::Reflike, b: impl Ferb::Reflike) -> Ferb::Ref {
        let r = self.alloca(16);
        let r2 = self.offset(r, Size::from_bytes(8));
        self.f.emit(self.b, O::storel, Kw, (), a, r);
        self.f.emit(self.b, O::storel, Kw, (), b, r2);
        r
    }
    
    fn get_pair_slot(&mut self, addr: impl Ferb::Reflike, first: bool) -> Ferb::Ref {
        let addr = addr.r(self.f);
        let addr = self.offset(addr, Size::from_bytes(if first { 0 } else { 8 }));
        let r = self.f.tmp();
        self.f.emit(self.b, O::load, Kl, r, addr, ());
        r
    }
    
    fn global_alloc(&mut self, p: AllocId, off: Size, ty: Ty) -> Ferb::Ref {
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
                return self.f.con(id, 0);
            }
            _ => todo!("{:?} {:?}", p, ty),
        }
    }
    
    fn alloca(&mut self, size: i64) -> Ferb::Ref {
        let r = self.f.tmp();
        self.f.emit(self.start_block, O::alloc8, Kl, r, size, ());
        r
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

