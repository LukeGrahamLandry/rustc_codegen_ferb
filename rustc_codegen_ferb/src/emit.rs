// this doesn't use rustc_codegen_ssa::BuilderMethods 
// because i find it awkward to write the program inside out. 
// it remains to be seen whether that was the right choice. 

use rustc_const_eval::interpret::{AllocId, ConstAllocation, GlobalAlloc, Scalar, alloc_range};
use rustc_hir::def_id::DefId;
use rustc_index::{Idx, IndexVec, bit_set::MixedBitSet};
use rustc_middle::{mir::{BasicBlock, BasicBlockData, BinOp, Body, CastKind, ConstOperand, ConstValue, Local, NonDivergingIntrinsic, Operand, Place, ProjectionElem, RETURN_PLACE, Rvalue, StatementKind, TerminatorKind, UnOp, mono::{CodegenUnit, MonoItem}, pretty::MirWriter}, ty::{EarlyBinder, GenericArgsRef, Instance, PseudoCanonicalInput, Ty, TyCtxt, TyKind, TypingEnv, adjustment::PointerCoercion, layout::{self, HasTyCtxt, HasTypingEnv, LayoutOf, LayoutOfHelpers, TyAndLayout}, print::with_no_trimmed_paths}};
use ferb::builder as Ferb;
use Ferb::Cls::*;
use Ferb::{J, O, Reflike};
use rustc_abi::{ExternAbi, FieldIdx, FieldsShape, HasDataLayout, Size, TagEncoding, Variants};
use rustc_span::Span;

const DEBUG: bool = false;

struct Emit<'f, 'tcx> {
    tcx: TyCtxt<'tcx>,
    m: &'f mut Ferb::Module,
    f: &'f mut Ferb::Func,
    b: Ferb::BlkId,
    blocks: IndexVec<BasicBlock, Ferb::BlkId>,
    locals: IndexVec<Local, Placement>,
    instance: Instance<'tcx>,
    start_block: Ferb::BlkId,
    return_block: Ferb::BlkId,
    mir: &'tcx Body<'tcx>,
}

#[derive(Debug, PartialEq, Copy, Clone)]
enum Placement {
    NewScalar(Ferb::Cls),
    Scalar(Ferb::Ref, Ferb::Cls),
    Blit(Ferb::Ref, usize),
    NewMemory(usize),
}

pub(crate) fn emit<'tcx>(tcx: TyCtxt<'tcx>, cgu: &CodegenUnit<'tcx>) -> Ferb::Module {
    let mut m = Ferb::Module::new();
    // TODO: i inline better if they're sorted in callgraph order (def before use)
    let items = cgu.items_in_deterministic_order(tcx);
    for (it, _data) in items {
        match it {
            MonoItem::Fn(it) => {
                let name = tcx.symbol_name(it).name;
                let id = m.intern(name);
                let mir = tcx.instance_mir(it.def);
                let mono = TypingEnv::fully_monomorphized();
                let ret_ty = EarlyBinder::bind(mir.return_ty());
                let ret_ty = it.instantiate_mir_and_normalize_erasing_regions(tcx, mono, ret_ty);
                
                if DEBUG {
                    with_no_trimmed_paths! {{  // fixes "diagnostics were expected but none were emitted"
                        let mut buf = Vec::new();
                        let writer = MirWriter::new(tcx);
                        writer.write_mir_fn(mir, &mut buf).unwrap();
                        eprintln!("${}();", name);
                        eprintln!("{}", String::from_utf8_lossy(&buf).into_owned());
                    }};
                }
                
                let ret = abi_type(&mut m, tcx, ret_ty);
                let mut f = Ferb::Func::new(id, ret);
                let start_block = f.blk();
                let mut emit = Emit {
                    tcx,
                    blocks: mir.basic_blocks.iter().map(|_| f.blk()).collect(),
                    locals: mir.local_decls.iter().map(|_| Placement::NewScalar(Kw)).collect(),
                    return_block: f.blk(),
                    b: start_block,
                    m: &mut m,
                    f: &mut f,
                    instance: it,
                    start_block,
                    mir,
                };
                for local in mir.args_iter() {
                    let ty = emit.mono_ty(mir.local_decls[local].ty);
                    let repr = abi_type(emit.m, tcx, ty);
                    let r = emit.f.tmp();
                    emit.locals[local] = match repr {
                        Ferb::Ret::Void => todo!(),
                        Ferb::Ret::K(k) => {
                            emit.emit(O::par, k, r, (), ());
                            Placement::Scalar(r, k)
                        }
                        Ferb::Ret::T(t) => {
                            emit.f.emit(emit.b, O::parc, Kl, r, t, ());
                            let size = emit.layout(ty).size.bytes_usize();
                            Placement::Blit(r, size)
                        }
                    };
                }
                if DEBUG {
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
                        if !place.is_indirect() {
                            needs_alloca.insert(place.local);
                        }
                    }
                }
            }
        }
        for (local, it) in self.mir.local_decls.iter_enumerated() {
            let ty = self.mono_ty(it.ty);
            let (k, _) = self.cls(ty);
            let size = self.layout(ty).size.bytes_usize();
            let is_arg = local.index() != 0 && local.index() < self.mir.arg_count + 1;
            if is_arg { 
                if needs_alloca.contains(local) {
                    if let Placement::Scalar(r, k) = self.locals[local] {
                        let dest = self.alloca(size);
                        self.emit(Ferb::store(k), Kw, (), r, dest);
                        self.locals[local] = Placement::Blit(dest, size);
                    }
                }
                continue;
            }
            
            if is_wide(ty) || is_big(ty) || needs_alloca.contains(local) {
                let dest = self.alloca(size);
                self.locals[local] = Placement::Blit(dest, size);
            } else {
                self.locals[local] = Placement::Scalar(self.f.tmp(), k);
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
        let r = match self.locals[RETURN_PLACE] {
            Placement::Blit(r, _) | Placement::Scalar(r, _) => r,
            Placement::NewScalar(_) | Placement::NewMemory(_) => unreachable!(),
        };
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
        let r = if ret != Ferb::Ret::Void { r } else { Ferb::Ref::Null };
        self.f.jump(self.b, j, r, None, None);
    }
    
    fn emit_block(&mut self, blk: &BasicBlockData<'tcx>) {
        for stmt in &blk.statements {
            match &stmt.kind {
                StatementKind::Assign(box (place, value)) => {
                    let dest = self.addr_place(place);
                    let _ = self.emit_value(value, dest);
                },
                StatementKind::Nop => (),
                StatementKind::StorageLive(_) => (),
                StatementKind::StorageDead(_) => (),
                StatementKind::Intrinsic(box it) => match it {
                    NonDivergingIntrinsic::Assume(_) => (),  // not my department
                    NonDivergingIntrinsic::CopyNonOverlapping { .. } => todo!(),
                }
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
                let callee = self.emit_operand(func, Placement::NewScalar(Kl));
                let sig = func.ty(self.mir, self.tcx).fn_sig(self.tcx);
                
                let mut arg_count = sig.inputs().skip_binder().len();
                let mut arg_types = args.iter().map(|arg| abi_type(self.m, self.tcx, self.mono_ty(arg.node.ty(self.mir, self.tcx)))).collect::<Vec<_>>();
                let mut arg_vals = args.iter().zip(&arg_types)
                    .map(|(arg, &repr)| self.emit_operand(&arg.node, match repr {
                        Ferb::Ret::K(k) => Placement::NewScalar(k),
                        Ferb::Ret::Void => Placement::NewScalar(Kw),  // ehh...
                        Ferb::Ret::T(t) => Placement::NewMemory(self.m.size_of(t)),
                    }))
                    .collect::<Vec<_>>();
                if sig.abi() == ExternAbi::RustCall {
                    // when calling a closure directly, the args are packed into a tuple but the callee wants them spread. 
                    assert!(arg_count == 2 && !sig.c_variadic());
                    let ty = sig.inputs().skip_binder()[1];
                    self.unpack_direct_closure_args(&mut arg_vals, &mut arg_types, ty);
                    arg_count = arg_vals.len();
                }
                for (i, &r) in arg_vals.iter().enumerate() {
                    if i == arg_count {
                        assert!(sig.c_variadic());
                        self.f.emit(self.b, O::argv, Kw, (), (), ());
                    }
                    
                    let repr = arg_types[i];
                    match repr {
                        Ferb::Ret::Void => todo!(),
                        Ferb::Ret::K(k) => {
                            self.f.emit(self.b, O::arg, k, (), r, ());
                        }
                        Ferb::Ret::T(t) => {
                            self.f.emit(self.b, O::argc, Kl, (), t, r);
                        }
                    }
                }
                if sig.c_variadic() && args.len() == arg_count {
                    // wasm cares if variadic even if none passed
                    self.f.emit(self.b, O::argv, Kw, (), (), ());
                }
                
                let ret = sig.output();
                let ret = ret.skip_binder();  // discards lifetimes but not generics i hope
                let ret = self.mono_ty(ret);
                let ret = abi_type(self.m, self.tcx, ret);
                let dest = self.addr_place(destination);
                match ret {
                    Ferb::Ret::K(k) => {
                        let r = self.scalar_dest(dest);
                        self.emit(O::call, k, r, callee, ());
                        self.scalar_result(dest, r, k);
                    },
                    Ferb::Ret::Void => self.emit(O::call, Kw, (), callee, ()),
                    Ferb::Ret::T(t) => {
                        let Placement::Blit(r, size) = dest else { todo!() };
                        let rr = self.f.tmp();
                        self.emit(O::call, Kl, rr, callee, t);
                        self.f.blit(self.b, r, rr, size);  // :SLOW
                    }
                }
                let j = target.map(|_| J::jmp).unwrap_or(J::hlt);
                let target = target.map(|it| self.blocks[it]);
                self.f.jump(self.b, j, (), target, None);
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                let (k, _) = self.cls(discr.ty(self.mir, self.tcx));
                let discr = self.emit_operand(discr, Placement::NewScalar(k));
                if let Some((val, a, b)) = targets.as_static_if() {
                    if val == 0 && k == Kw {
                        self.f.jump(self.b, J::jnz, discr, Some(self.blocks[b]), Some(self.blocks[a]));
                        return;
                    }
                }
                // :SLOW
                let mut next = self.f.blk();
                for (&val, &dest) in targets.all_values().iter().zip(targets.all_targets()) {
                    let cond = self.f.tmp();
                    let op = Ferb::fix_cmp_cls(O::ceql, k).unwrap();
                    self.f.emit(self.b, op, Kl, cond, discr, val.0 as u64);
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
                
                let cond = self.emit_operand(cond, Placement::NewScalar(Kw));
                let dest = [failed, self.blocks[*target]];
                self.f.jump(self.b, J::jnz, cond, Some(dest[*expected as usize]), Some(dest[!*expected as usize]));
            }
            TerminatorKind::Drop { place, target, drop, async_fut, .. } => {
                assert!(drop.is_none() && async_fut.is_none());
                // you get one of these even if it does nothing when generic over something without +Copy
                let _ = place;  // TODO
                self.f.jump(self.b, J::jmp, (), Some(self.blocks[*target]), None);
            }
            _ => todo!("{:?}", terminator),
        }
    }
    
    fn unpack_direct_closure_args(&mut self, arg_vals: &mut Vec<Ferb::Ref>, arg_types: &mut Vec<Ferb::Ret>, ty: Ty<'tcx>) {
        let base = arg_vals.pop().unwrap();
        let _ = arg_types.pop().unwrap();
        let inner = match ty.kind() {
            TyKind::Tuple(it) => it,
            _ => todo!(),
        };
        
        let layout = self.layout(ty);
        for (i, ty) in inner.iter().enumerate() {
            let ty = abi_type(self.m, self.tcx, ty);
            arg_types.push(ty);
            let field = self.offset(base, layout.fields.offset(i));
            let field = match ty {
                Ferb::Ret::K(k) => {
                    let r = self.f.tmp();
                    self.emit(O::load, k, r, field,());
                    r
                }
                Ferb::Ret::Void => todo!(),
                Ferb::Ret::T(_) => field,
            };
            arg_vals.push(field);
        }
    }
    
    fn scalar_dest(&mut self, dest: Placement) -> Ferb::Ref {
        match dest {
            Placement::NewScalar(_) => self.f.tmp(),
            Placement::Scalar(dest, _) => dest,
            Placement::Blit(_, size) | Placement::NewMemory(size) => {
                assert!(size <= 8);
                self.f.tmp()
            },
        }
    }
    
    fn scalar_result(&mut self, dest: Placement, r: impl Reflike, k: Ferb::Cls) -> Ferb::Ref {
        let r = r.r(self.f);
        match dest {
            Placement::NewScalar(_) => r,
            Placement::Scalar(dest, k) => {
                if dest != r {
                    self.f.emit(self.b, O::copy, k, dest, r, ());
                }
                dest
            }
            Placement::Blit(dest, size) => {
                assert!(size <= 8);
                self.f.emit(self.b, Ferb::store(k), Kw, (), r, dest);
                dest
            }
            Placement::NewMemory(size) => {
                assert!(size <= 8);
                let dest = self.alloca(size);
                self.scalar_result(Placement::Blit(dest, size), r, k)
            }
        }
    }
    
    fn get_memory(&mut self, dest: Placement) -> Ferb::Ref {
        match dest {
            Placement::NewScalar(_) | Placement::Scalar(_, _) => todo!(),
            Placement::Blit(dest, _) => dest,
            Placement::NewMemory(size) => self.alloca(size),
        }
    }
    
    fn new_placement(&mut self, ty: Ty<'tcx>) -> Placement {
        if is_big(ty) || is_wide(ty) {
            return Placement::NewMemory(self.layout(ty).size.bytes_usize())
        }
        let (k, _) = self.cls(ty);
        Placement::NewScalar(k)
    }
    
    fn emit_value(&mut self, value: &Rvalue<'tcx>, dest: Placement) -> Ferb::Ref {
        match value {
            Rvalue::Use(operand) => self.emit_operand(operand, dest),
            Rvalue::RawPtr(_, place) | Rvalue::Ref(_, _, place) => {
                let place = self.addr_place(place);
                let Placement::Blit(r, _) = place else { todo!() }; 
                if is_wide(value.ty(self.mir, self.tcx)) {
                    self.copy_placement(dest, place)
                } else {
                    self.scalar_result(dest, r, Kl)
                }
            }
            Rvalue::Cast(kind, value, dest_ty) => {
                let src = self.new_placement(value.ty(self.mir, self.tcx));
                let src = self.emit_operand(value, src);
                let src_ty = value.ty(&self.mir.local_decls, self.tcx);
                match kind {
                    CastKind::Transmute => {
                        if is_wide(src_ty) {
                            match dest {
                                Placement::Blit(dest, size) => {
                                    self.f.blit(self.b, dest, src, size);
                                    dest
                                }
                                Placement::NewMemory(_) => src,
                                _ => todo!(),
                            }
                        } else {
                            self.scalar_result(dest, src, Kl)
                        }
                    },
                    CastKind::PtrToPtr => {
                        assert!(src_ty.is_any_ptr() && dest_ty.is_any_ptr());
                        if is_wide(src_ty) && !is_wide(*dest_ty) {
                            let r = self.get_pair_slot(src, true);
                            return self.scalar_result(dest, r, Kl)
                        }
                        assert!(is_wide(src_ty) == is_wide(*dest_ty));
                        assert!(!is_wide(src_ty)); // TODO: blit
                        self.scalar_result(dest, src, Kl)
                    }
                    CastKind::IntToInt => {
                        let d = dest_ty.primitive_size(self.tcx).bytes();
                        let s = src_ty.primitive_size(self.tcx).bytes();
                        let k = if d == 8 { Kl } else { Kw };
                        if s == d { return self.scalar_result(dest, src, k) };
                        // TODO: sign
                        // TODO: decide which direction has to guarentee high bits. rn i do it both ways. 
                        let o = match d.min(s) {
                            1 => O::extub,
                            2 => O::extuh,
                            4 if d > 4 => O::extuw,
                            4 => O::copy,
                            _ => todo!("{:?} {:?}", src_ty, dest_ty),
                        };
                        let r = self.scalar_dest(dest);
                        self.emit(o, k, r, src, ());
                        self.scalar_result(dest, r, k)
                    },
                    CastKind::PointerWithExposedProvenance => {
                        assert!(!is_wide(*dest_ty));  // TODO
                        self.scalar_result(dest, src, Kl)
                    },
                    CastKind::PointerCoercion(kind, _)  => {
                        assert!(!matches!(kind, PointerCoercion::ClosureFnPointer(_) | PointerCoercion::Unsize));
                        assert!(!is_wide(*dest_ty));  // TODO
                        self.scalar_result(dest, src, Kl)
                    },
                    _ => todo!("{:?}", value),
                }
            }
            Rvalue::UnaryOp(op, value) => {
                match op {
                    UnOp::PtrMetadata => {
                        let p = self.new_placement(value.ty(self.mir, self.tcx));
                        let p = self.emit_operand(value, p);
                        let r = self.get_pair_slot(p, false);
                        self.scalar_result(dest, r, Kl)
                    }
                    UnOp::Not => {
                        // TODO: what's bool bit pattern? match(bool) => b == 0 instead?
                        let (k, _) = self.cls(value.ty(self.mir, self.tcx));
                        let src = self.emit_operand(value, Placement::NewScalar(k));
                        let r = self.scalar_dest(dest);
                        self.emit(O::xor, k, r, src, -1i64);
                        self.scalar_result(dest, r, k)
                    }
                    _ => todo!("{:?} {:?}", op, value)
                }
            }
            Rvalue::BinaryOp(op, box(lhs, rhs)) => {
                let in_ty = lhs.ty(self.mir, self.tcx);
                let in_k = self.cls(in_ty).0;
                let out_ty = value.ty(self.mir, self.tcx);
                let (lhs, rhs) = (self.emit_operand(lhs, Placement::NewScalar(in_k)), self.emit_operand(rhs, Placement::NewScalar(in_k)));
                let k = self.cls(out_ty).0;
                if let Some(op) = (*op).overflowing_to_wrapping() {
                    let r = self.get_memory(dest);
                    let op = choose_op(op, in_ty.is_signed());
                    let k = in_k;
                    let rr = self.f.tmp();
                    self.emit(op, k, rr, lhs, rhs);
                    self.emit(Ferb::store(k), Kw, (), rr, r);
                    // TODO: 8/16/128
                    let ok = self.offset(r, Size::from_bytes(if k == Kl || k == Kd { 8 } else { 4 }));  
                    // TODO: do this properly! for now just lying and saying it didn't overflow
                    self.emit(O::storew, Kw, (), 0u64, ok);
                    assert!(matches!(dest, Placement::Blit(_, _) | Placement::NewMemory(_)));
                    r
                } else {
                    let r = self.scalar_dest(dest);
                    let op = choose_op(*op, out_ty.is_signed());
                    let op = Ferb::fix_cmp_cls(op, in_k).unwrap_or(op);
                    self.emit(op, k, r, lhs, rhs);
                    // TODO: mask if explicitly wrapping
                    self.scalar_result(dest, r, k)
                }
            }
            Rvalue::Aggregate(kind, fields) => {
                use rustc_middle::mir::AggregateKind::*;
                let ty = value.ty(self.mir, self.tcx);
                assert!(is_big(ty));
                let mut layout = self.layout(ty);
                let base = self.get_memory(dest);
                match **kind {
                    Adt(_, varient, _, _, active) => {
                        assert!(active.is_none(), "TODO: union");
                        if let Variants::Multiple { tag_encoding, tag_field, tag, .. } = &layout.variants {
                            assert!(layout.fields.count() == 1 && tag_encoding == &TagEncoding::Direct);
                            let value = varient.as_u32() as u64;
                            let (_, o, ty) = tag_load_store(self.tcx, tag);
                            let dest = self.offset_placement(base, layout, *tag_field, ty);
                            let r = self.get_memory(dest);
                            self.emit(o, Kw, (), value, r);
                            layout = layout.for_variant(self, varient);
                        }
                    }
                    Tuple | Array(_) | Closure(_, _) => (),
                    _ => todo!("{:?}", value),
                }
                self.emit_aggregate(base, layout, fields);
                assert!(matches!(dest, Placement::Blit(_, _) | Placement::NewMemory(_)));
                base
            }
            Rvalue::Discriminant(place) => {
                assert!(value.ty(self.mir, self.tcx).primitive_size(self.tcx).bytes() == /*TODO*/ 8);  // regardless of size in memory
                let base = self.addr_place(place);
                let ty = place.ty(self.mir, self.tcx);
                let layout = self.layout(ty.ty);
                if let Variants::Multiple { tag_encoding, tag_field, tag, .. } = &layout.variants {
                    assert!(layout.fields.count() == 1 && tag_encoding == &TagEncoding::Direct);
                    let base = self.get_memory(base);
                    let (o, _, ty) = tag_load_store(self.tcx, tag);
                    let base = self.offset_placement(base, layout, *tag_field, ty);
                    let Placement::Blit(base, _) = base else { todo!() };
                    let r = self.scalar_dest(dest);
                    self.emit(o, Kl, r, base, ());
                    return self.scalar_result(dest, r, Kl);
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
    
    fn emit_aggregate(&mut self, base: Ferb::Ref, layout: TyAndLayout<'tcx>, fields: &IndexVec<FieldIdx, Operand<'tcx>>) {
        for field in layout.fields.index_by_increasing_offset() {
            let field = FieldIdx::new(field);
            let value = &fields[field];
            let ty = value.ty(self.mir, self.tcx);
            let dest = self.offset_placement(base, layout, field, ty);
            let _ = self.emit_operand(value, dest);
        }
    }
    
    fn offset_placement(&mut self, base: Ferb::Ref, layout: TyAndLayout<'tcx>, field: FieldIdx, field_ty: Ty<'tcx>) -> Placement {
        let offset = layout.fields.offset(field.as_usize());
        let r = self.offset(base, offset);
        let field_layout = self.layout(field_ty);
        let size = field_layout.size.bytes_usize();
        Placement::Blit(r, size)
    }
    
    fn offset(&mut self, r: Ferb::Ref, off: Size) -> Ferb::Ref {
        if off.bytes() == 0 { return r; }
        let r2 = self.f.tmp();
        self.emit(O::add, Kl, r2, r, off.bytes());
        r2
    }
    
    fn addr_place(&mut self, place: &Place<'tcx>) -> Placement {
        let ty = place.ty(self.mir, self.tcx);
        if let Some(it) = place.as_local() {
            return self.locals[it];
        }
        let final_size = self.layout(ty.ty).size.bytes_usize();
        let mut base = match self.locals[place.local] {
            Placement::NewScalar(_) | Placement::NewMemory(_) => todo!(),
            Placement::Scalar(r, _) | Placement::Blit(r, _) => r,
        };
        let mut parent_ty = self.mir.local_decls[place.local].ty;
        let mut projection = place.projection.iter();
        if place.is_indirect() {
            parent_ty = match parent_ty.kind() {
                TyKind::RawPtr(inner, _) | TyKind::Ref(_, inner, _) => *inner,
                _ => todo!(),
            };
            projection.next();
        };
        for it in projection {
            use ProjectionElem::*;
            match it {
                Deref => unreachable!(),  // only allowed as first projection
                Field(field_idx, inner) => {
                    use FieldsShape::*;
                    let layout = self.layout(parent_ty);
                    let offsets = match &layout.fields {
                        Arbitrary { offsets, .. } => offsets,
                        Primitive => return Placement::Blit(base, final_size),
                        _ => todo!("{:?}", place),
                    };
                    base = self.offset(base, offsets[field_idx]);
                    parent_ty = inner;
                }
                Downcast(_, varient) => {
                    let layout = self.layout(parent_ty);
                    if let Variants::Multiple { tag_encoding, .. } = &layout.variants {
                        assert!(tag_encoding == &TagEncoding::Direct);
                    };
                    let layout = layout.for_variant(self, varient);
                    let first = layout.layout.fields.index_by_increasing_offset().next().unwrap();
                    base = self.offset(base, layout.fields.offset(first));
                    parent_ty = ty.projection_ty(self.tcx, it).ty;
                },
                Index(index) => {
                    let Placement::Scalar(index, _) = self.locals[index] else { todo!() };
                    let inner = match parent_ty.kind() {
                        TyKind::Array(it, _) => *it,
                        _ => todo!(),
                    };
                    let layout = self.layout(inner);
                    let step = layout.size.bytes();
                    let r = self.f.tmps::<2>();
                    self.f.emit(self.b, O::mul, Kl, r[0], index, step);
                    self.f.emit(self.b, O::add, Kl, r[1], base, r[0]);
                    base = r[1];
                    parent_ty = inner;
                }
                _ => todo!("{:?}", place),
            }
        }
        Placement::Blit(base, final_size)
    }
    
    fn load_place(&mut self, dest: Placement, place: &Place<'tcx>) -> Ferb::Ref {
        let src = self.addr_place(place);
        let rr = self.copy_placement(dest, src);
        // eprintln!("load_place {:?} = {:?} = {:?} = {:?}", dest, place, src, rr);
        rr
    }
    
    fn copy_placement(&mut self, dest: Placement, src: Placement,) -> Ferb::Ref {
        match src {
            Placement::NewScalar(_) | Placement::NewMemory(_) => unreachable!(),
            Placement::Scalar(r, k) => self.scalar_result(dest, r, k),
            Placement::Blit(src, _) => match dest {
                Placement::NewScalar(k) => {
                    let dest = self.f.tmp();
                    self.emit(O::load, k, dest, src, ());
                    dest
                },
                Placement::Scalar(dest, k) => {
                    self.emit(O::load, k, dest, src, ());
                    dest
                }
                Placement::Blit(dest, size) => {
                    self.f.blit(self.b, dest, src, size);
                    dest
                },
                Placement::NewMemory(_) => src,
            },
        }
    }
    
    fn emit_operand(&mut self, operand: &Operand<'tcx>, dest: Placement) -> Ferb::Ref {
        match operand {
            Operand::Copy(place) => self.load_place(dest, place),
            Operand::Move(place) => self.load_place(dest, place),
            Operand::Constant(it) => {
                let (val, ty) = self.finish_const(it);
                match val {
                    ConstValue::Scalar(it) => {
                        let ty = operand.ty(self.mir, self.tcx);
                        match it {
                            Scalar::Int(it) => {
                                let (k, _) = self.cls(ty);
                                let raw = it.to_bits(it.size()) as u64;
                                self.scalar_result(dest, raw, k)
                            }
                            Scalar::Ptr(p, _) => {
                                assert!(!is_big(ty));
                                let (p, off) = p.prov_and_relative_offset();
                                let p = self.global_alloc(p.alloc_id(), off, ty);
                                self.scalar_result(dest, p, Kl)
                            }
                        }
                    }
                    ConstValue::ZeroSized => {
                        // const known function gets here. the value is stored in the type field. 
                        match ty.kind() {
                            &TyKind::FnDef(def, args) => {
                                let id = def_symbol(self.m, self.tcx, def, Some(args));
                                self.scalar_result(dest, id, Kl)
                            },
                            &TyKind::Tuple(it) => {
                                assert!(it.len() == 0, "{:?}", ty);
                                self.scalar_result(dest, Ferb::Ref::Undef, Kl)
                            }
                            _ => todo!("zst {:?}", ty)
                        }
                    }
                    ConstValue::Slice { alloc_id, meta } => {
                        let p = self.global_alloc(alloc_id, Size::ZERO, ty);
                        self.create_pair(dest, p, meta)
                    }
                    ConstValue::Indirect { alloc_id, offset } => {
                        let size = self.layout(ty).size.bytes_usize();
                        let src = self.global_alloc(alloc_id, offset, ty);
                        let src = src.r(self.f);
                        self.copy_placement(dest, Placement::Blit(src, size))
                    }
                }
            }
            Operand::RuntimeChecks(it) => {
                let it = it.value(self.tcx.sess);
                self.scalar_result(dest, it as u64, Kw)
            },
        }
    }
    
    // TODO: dumb because i know im slow at promoting if you keep recalculating the address for the second slot.
    fn create_pair(&mut self, dest: Placement, a: impl Reflike, b: impl Reflike) -> Ferb::Ref {
        let r = self.get_memory(dest);
        let r2 = self.offset(r, Size::from_bytes(8));
        self.emit(O::storel, Kw, (), a, r);
        self.emit(O::storel, Kw, (), b, r2);
        r
    }
    
    fn get_pair_slot(&mut self, addr: Ferb::Ref, first: bool) -> Ferb::Ref {
        let addr = self.offset(addr, Size::from_bytes(if first { 0 } else { 8 }));
        let r = self.f.tmp();
        self.emit(O::load, Kl, r, addr, ());
        r
    }
    
    fn global_alloc(&mut self, p: AllocId, off: Size, ty: Ty) -> Ferb::Id<Ferb::Sym> {
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
                id
            }
            GlobalAlloc::Static(def) => {
                let id = def_symbol(self.m, self.tcx, def, None);
                id
            }
            _ => todo!("{:?} {:?}", p, ty),
        }
    }
    
    fn alloca(&mut self, size: usize) -> Ferb::Ref {
        let r = self.f.tmp();
        self.f.emit(self.start_block, O::alloc8, Kl, r, size, ());
        r
    }
    
    fn cls(&self, ty: Ty<'tcx>) -> (Ferb::Cls, ()) {
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
    
    pub fn emit(&mut self, o: O, k: Ferb::Cls, to: impl Reflike, a0: impl Reflike, a1: impl Reflike) {
        self.f.emit(self.b, o, k, to, a0, a1);
    }
}

fn tag_load_store<'tcx>(tcx: TyCtxt<'tcx>, tag: &rustc_abi::Scalar) -> (O, O, Ty<'tcx>) {
    let tag = tag.primitive();
    use rustc_abi::{Primitive::*, Integer::*};
    match tag {
        Int(integer, signed) => match integer {
            I8 => (if signed { O::loadsb } else { O::loadub }, O::storeb, tcx.types.i8),
            I16 => (if signed { O::loadsh } else { O::loaduh }, O::storeh, tcx.types.i16),
            I32 => (if signed { O::loadsw } else { O::loaduw }, O::storew, tcx.types.i32),
            I64 => (O::load, O::storel, tcx.types.i64),
            I128 => todo!(),
        },
        _ => todo!("{:?}", tag),
    }
}

fn is_big(ty: Ty) -> bool {
    assert!(!matches!(ty.kind(), TyKind::Param(_)));
    matches!(ty.kind(), TyKind::Adt(_, _) | TyKind::Tuple(_) | TyKind::Array(_, _) | TyKind::Closure(_, _))
}

fn val_cls(ty: Ty) -> (Ferb::Cls, ()) {
    if is_big(ty) {
        return (Kl, ());
    }
    if is_wide(ty) { return (Kl, ()) }
    if ty.is_any_ptr() { return (Kl, ()) }

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
    }, ())
}

fn layout_of<'tcx>(tcx: TyCtxt<'tcx>, value: Ty<'tcx>) -> TyAndLayout<'tcx> {
    tcx.layout_of(PseudoCanonicalInput { value,  typing_env: TypingEnv::fully_monomorphized() }).unwrap()
}

fn abi_type<'tcx>(m: &mut Ferb::Module, tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Ferb::Ret {
    let (k, _) = val_cls(ty);
    if !is_big(ty) && !is_wide(ty) {
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
    if !ty.is_any_ptr() || matches!(ty.kind(), TyKind::FnPtr(_, _)){ return false };
    let inner = ty.builtin_deref(true).unwrap_or_else(|| todo!("{:?}", ty));
    inner.is_str() || inner.is_array_slice()
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
