// this doesn't use rustc_codegen_ssa::BuilderMethods 
// because i find it awkward to write the program inside out. 
// it remains to be seen whether that was the right choice. 

use rustc_codegen_ssa::base::is_call_from_compiler_builtins_to_upstream_monomorphization;
use rustc_const_eval::interpret::{AllocId, GlobalAlloc, Scalar, alloc_range};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_index::{Idx, IndexVec, bit_set::MixedBitSet};
use rustc_middle::{mir::{BasicBlock, BasicBlockData, BinOp, Body, CastKind, ConstOperand, ConstValue, Local, NonDivergingIntrinsic, Operand, Place, ProjectionElem, RETURN_PLACE, Rvalue, StatementKind, TerminatorKind, UnOp, mono::{CodegenUnit, MonoItem}}, ty::{EarlyBinder, GenericArgsRef, Instance, InstanceKind, PseudoCanonicalInput, Ty, TyCtxt, TyKind, TypingEnv, adjustment::PointerCoercion, layout::{self, HasTyCtxt, HasTypingEnv, LayoutOf, LayoutOfHelpers, TyAndLayout}, print::with_no_trimmed_paths}};
use ferb::builder as Ferb;
use Ferb::{J, O, Reflike, Cls::*};
use rustc_abi::{ExternAbi, FieldIdx, FieldsShape, HasDataLayout, Size, TagEncoding, VariantIdx, Variants};
use rustc_span::Span;

const DEBUG: bool = false;

pub(crate) struct Emit<'f, 'tcx> {
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) m: &'f mut Ferb::Module,
    pub(crate) f: &'f mut Ferb::Func,
    pub(crate) b: Ferb::BlkId,
    blocks: IndexVec<BasicBlock, Ferb::BlkId>,
    locals: IndexVec<Local, Placement>,
    instance: Instance<'tcx>,
    start_block: Ferb::BlkId,
    return_block: Ferb::BlkId,
    pub(crate) mir: &'tcx Body<'tcx>,
    pub(crate) caller_location: Option<Ferb::Ref>,
    c: &'f mut Ctx<'tcx>,
}

struct Ctx<'tcx> {
    allocations: FxHashMap<AllocId, Ferb::Id<Ferb::Sym>>,
    finished: FxHashSet<Ferb::Id<Ferb::Sym>>,
    types: FxHashMap<Ty<'tcx>, Ferb::Ref>,
}

#[derive(Debug, PartialEq, Copy, Clone)]
pub(crate) enum Placement {
    NewScalar(Ferb::Cls),
    Scalar(Ferb::Ref, Ferb::Cls),
    Blit(Ferb::Ref, usize),
    NewMemory(usize),
    Zst,
}

pub(crate) fn emit<'tcx>(tcx: TyCtxt<'tcx>, cgu: &CodegenUnit<'tcx>) -> Ferb::Module {
    let mut m = Ferb::Module::new();
    // TODO: i inline better if they're sorted in callgraph order (def before use)
    let items = cgu.items_in_deterministic_order(tcx);
    let mut c = Ctx {
        allocations: FxHashMap::default(),
        finished: FxHashSet::default(),
        types: FxHashMap::default(),
    };
    for (it, _data) in items {
        match it {
            MonoItem::Fn(it) => {
                emit_func(&mut m, tcx, it, &mut c);
                let id = m.intern(tcx.symbol_name(it).name);
                c.finished.insert(id);
            },
            MonoItem::Static(def) => {
                let alloc = tcx.reserve_alloc_id();  // :SLOW?
                let mem = tcx.eval_static_initializer(def).unwrap();
                tcx.set_alloc_id_memory(alloc, mem);
                let id = get_symbol(&mut m, tcx, def, None);
                c.allocations.insert(alloc, id);
            },
            MonoItem::GlobalAsm(_) => todo!(),
        } 
    }
    crate::extra::maybe_create_entry_wrapper(&mut m, tcx, cgu);

    // TODO: make sure fxhashmap doesn't do the random order thing because i care about repro
    loop {
        // :SLOW
        let pending = c.allocations.iter().filter(|(_, id)| !c.finished.contains(&id)).map(|(&k, &v)| (k, v)).collect::<Vec<_>>();
        if pending.len() == 0 { break };
        
        for (p, id) in pending {
            if c.finished.contains(&id) { continue };
            let alloc = tcx.global_alloc(p);
            let it = match alloc {
                GlobalAlloc::Memory(it) => it,
                GlobalAlloc::Static(def) => {
                    assert!(tcx.should_codegen_locally(get_instance(tcx, def, None)));
                    tcx.eval_static_initializer(def).unwrap()
                },
                GlobalAlloc::Function { instance } => {
                    // TODO: i feel i should never have to emit here. 
                    // if !should_codegen_locally, you can still get its body but all the callees won't have been in the list either and you'd have to infinitly pull in everything. 
                    if tcx.should_codegen_locally(instance) {
                        assert!(!tcx.instantiate_and_check_impossible_predicates((instance.def_id(), &instance.args)));
                        let instance = get_instance(tcx, instance.def_id(), Some(instance.args));
                        emit_func(&mut m, tcx, instance, &mut c);
                    }
                    c.finished.insert(id);
                    continue;
                },
                _ => todo!("{:?}", p),
            };
            
            c.finished.insert(id);
            let it = it.inner();
            let rel = it.provenance().ptrs().iter().map(|(off, id)| {
                let id = global_alloc(&mut m, tcx, &mut c, id.alloc_id()); 
                Ferb::Reloc { addend: 0, off: off.bytes() as u32, id }
            }).collect::<Vec<_>>();
            let range = alloc_range(Size::from_bytes(0), it.size());
            use rustc_ast::Mutability::*;
            let segment = match it.mutability {
                Not => Ferb::Seg::ConstantData,
                Mut => Ferb::Seg::MutableData,
            };
            let bytes = it.get_bytes_unchecked(range);
            
            m.data(Ferb::Data {
                id,
                segment,
                template: if bytes.iter().all(|&it| it == 0) {
                    Ferb::Template::Zeroes(bytes.len())
                } else {
                    Ferb::Template::Bytes(bytes)
                },
                rel,
            });
        }
    }
    
    m
}

fn emit_func<'tcx>(m: &mut Ferb::Module, tcx: TyCtxt<'tcx>, it: Instance<'tcx>, c: &mut Ctx<'tcx>) {
    if DEBUG {
        // fixes "diagnostics were expected but none were emitted"
        with_no_trimmed_paths! {{ emit_func2(m, tcx, it, c); }};
    } else {
        emit_func2(m, tcx, it, c);
    }
}

fn emit_func2<'tcx>(m: &mut Ferb::Module, tcx: TyCtxt<'tcx>, it: Instance<'tcx>, c: &mut Ctx<'tcx>) {
    let name = tcx.symbol_name(it).name;
    let id = m.intern(name);
    let mir = tcx.instance_mir(it.def);
    let mono = TypingEnv::fully_monomorphized();
    let ret_ty = EarlyBinder::bind(mir.return_ty());
    let ret_ty = it.instantiate_mir_and_normalize_erasing_regions(tcx, mono, ret_ty);
    
    let ret = abi_type(m, tcx, c, ret_ty);
    let mut f = Ferb::Func::new(id, ret);
    let start_block = f.blk();
    let mut emit = Emit {
        tcx,
        blocks: mir.basic_blocks.iter().map(|_| f.blk()).collect(),
        locals: mir.local_decls.iter().map(|_| Placement::Zst).collect(),
        return_block: f.blk(),
        b: start_block,
        m,
        f: &mut f,
        instance: it,
        start_block,
        mir,
        caller_location: None,
        c
    };
    
    let count = if mir.spread_arg.is_some() { 1 } else { mir.arg_count };
    let mut wide_pairs = vec![];  // :SplatWidePointer
    for local in 1..count+1 {
        let local = Local::new(local);
        let ty = emit.mono_ty(mir.local_decls[local].ty);
        let repr = emit.abi_type(ty);
        let r = emit.f.tmp();
        emit.locals[local] = match repr {
            Ferb::Ret::Void => Placement::Zst,
            Ferb::Ret::K(k) => {
                emit.emit(O::par, k, r, (), ());
                Placement::Scalar(r, k)
            }
            Ferb::Ret::T(t) => {
                let size = emit.layout(ty).size.bytes_usize();
                if emit.is_wide(ty) {
                    let a = emit.f.tmps::<2>();
                    emit.emit(O::par, Kl, a[0], (), ());
                    emit.emit(O::par, Kl, a[1], (), ());
                    wide_pairs.push((r, a));
                } else {
                    emit.emit(O::parc, Kl, r, t, ());
                }
                Placement::Blit(r, size)
            }
        };
    }
    
    // inverse of unpack_direct_closure_args
    if let Some(args_tuple) = mir.spread_arg {
        assert!(mir.arg_count == 2 && args_tuple.as_u32() == 2);

        let ty = mir.local_decls[args_tuple].ty;
        let ty = emit.mono_ty(ty);
        let TyKind::Tuple(inner) = ty.kind() else { todo!("{:?}", ty) };
        
        let mut arg_vals = vec![];
        for ty in inner.iter() {
            let wide = emit.is_wide(ty);
            let ty = emit.abi_type(ty);
            let r = emit.f.tmp();
            match ty {
                Ferb::Ret::K(k) => emit.emit(O::par, k, r, (), ()),
                Ferb::Ret::Void => (),
                Ferb::Ret::T(t) => {
                    if wide {
                        let a = emit.f.tmps::<2>();
                        emit.emit(O::par, Kl, a[0], (), ());
                        emit.emit(O::par, Kl, a[1], (), ());
                        wide_pairs.push((r, a));
                    } else {
                        emit.emit(O::parc, Kl, r, t, ());
                    }
                    emit.emit(O::parc, Kl, r, t, ());
                }
            };
            arg_vals.push(r);
        }
        
        emit.caller_location_par();
        let layout = emit.layout(ty);
        let size = layout.size.bytes_usize();
        let base = emit.alloca(size);
        emit.locals[args_tuple] = Placement::Blit(base, size);
        for (i, ty) in inner.iter().enumerate() {
            let ty = emit.abi_type(ty);
            let field = emit.offset(base, layout.fields.offset(i));
            let r = arg_vals[i];
            match ty {
                Ferb::Ret::K(k) => emit.emit(Ferb::store(k), Kw, (), r, field),
                Ferb::Ret::Void => (),
                Ferb::Ret::T(t) => emit.f.blit(emit.b, r, field, emit.m.size_of(t)),
            };
        }
        if size == 0 {
            emit.locals[args_tuple] = Placement::Zst;
        }
    } else {
        emit.caller_location_par();
    }
    
    for (r, a) in wide_pairs {
        emit.emit(O::alloc8, Kl, r, 16, ());
        let r2 = emit.offset(r, Size::from_bytes(8));
        emit.emit(O::storel, Kw, (), a[0], r);
        emit.emit(O::storel, Kw, (), a[1], r2);
    }
    if DEBUG {
        let loc = tcx.def_span(it.def.def_id());
        let loc = tcx.sess.source_map().span_to_diagnostic_string(loc.shrink_to_lo());
        emit.f.comment(emit.m, emit.start_block, &*format!("{} {}", loc, it));
    }
    emit.allocate_locals();
    emit.f.jump(emit.b, J::jmp, (), Some(emit.blocks[BasicBlock::new(0)]), None);
    emit.emit_return_block(ret);
    
    for (bid, blk) in mir.basic_blocks.iter_enumerated() {
        emit.b = emit.blocks[bid]; 
        emit.emit_block(blk);
    }
    m.func(f);
}

impl<'f, 'tcx> Emit<'f, 'tcx> {
    fn caller_location_par(&mut self) {
        if !self.instance.def.requires_caller_location(self.tcx) { return }
        let r = self.f.tmp();
        self.emit(O::par, Kl, r, (), ());
        self.caller_location = Some(r);
    }
    
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
            if size == 0 { continue };
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
            
            assert!(matches!(self.locals[local], Placement::Zst));
            if self.is_wide(ty) || is_big(ty) || needs_alloca.contains(local) {
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
            Placement::Zst => Ferb::Ref::Null,
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
        self.f.jump(self.b, j, r, None, None);
    }
    
    fn emit_block(&mut self, blk: &BasicBlockData<'tcx>) {
        for stmt in &blk.statements {
            match &stmt.kind {
                StatementKind::Assign(box (place, value)) => {
                    if DEBUG { self.f.comment(self.m, self.b, &*format!("{:?}", stmt)); }
                    let dest = self.addr_place(place);
                    let _ = self.emit_value(value, dest);
                },
                StatementKind::Nop | StatementKind::StorageLive(_) | StatementKind::StorageDead(_) => (),
                StatementKind::Intrinsic(box it) => match it {
                    NonDivergingIntrinsic::Assume(_) => (),  // not my department
                    NonDivergingIntrinsic::CopyNonOverlapping(it) => self.call_memcpy(it),
                }
                _ => todo!("{:?}", stmt),
            }
        }
        let terminator = blk.terminator();
        if DEBUG { self.f.comment(self.m, self.b, &*format!("{:?}", terminator.kind)); }
        match &terminator.kind {
            &TerminatorKind::Goto { target } => {
                self.f.jump(self.b, J::jmp, (), Some(self.blocks[target]), None);
            }
            TerminatorKind::Return => self.f.jump(self.b, J::jmp, (), Some(self.return_block), None),
            TerminatorKind::Call { func, args, destination, target, .. } => {
                let dest = self.addr_place(destination);
                let j = target.map(|_| J::jmp).unwrap_or(J::hlt);
                let target = target.map(|it| self.blocks[it]);
                
                let f_ty = func.ty(self.mir, self.tcx);
                let f_ty = self.mono_ty(f_ty);
                // TODO: is this different from fn_abi_of_instance?
                let sig = f_ty.fn_sig(self.tcx);  
                
                let mut arg_count = sig.inputs().skip_binder().len();
                let mut arg_types = args.iter().map(|arg| self.abi_type(arg.node.ty(self.mir, self.tcx))).collect::<Vec<_>>();
                let mut arg_vals = args.iter().zip(&arg_types)
                    .map(|(arg, &repr)| self.emit_operand(&arg.node, match repr {
                        Ferb::Ret::K(k) => Placement::NewScalar(k),
                        Ferb::Ret::Void => Placement::Zst,
                        Ferb::Ret::T(t) => Placement::NewMemory(self.m.size_of(t)),
                    }))
                    .collect::<Vec<_>>();
                let mut caller_location = false;
                let mut callee: Option<Ferb::Ref> = None;
                if let &TyKind::FnDef(id, generics) = f_ty.kind() {
                    let instance = get_instance(self.tcx, id, Some(generics));
                    caller_location = instance.def.requires_caller_location(self.tcx);
                    
                    assert!(!is_call_from_compiler_builtins_to_upstream_monomorphization(self.tcx, instance));
                    match instance.def {
                        InstanceKind::Intrinsic(def) => {
                            assert!(!sig.c_variadic());
                            if self.call_intrinsic(dest, &arg_vals, def, sig.inputs().skip_binder(), terminator.source_info) {
                                self.f.jump(self.b, j, (), target, None);
                                return;
                            }
                        }
                        InstanceKind::Virtual(_, vtable_index) => {
                            assert!(!sig.c_variadic());
                            callee = Some(self.load_trait_object(&mut arg_vals[0], &mut arg_types[0], vtable_index));
                        }
                        InstanceKind::DropGlue(_, None) => {
                            // avoid linker error for nop drop
                            // TODO: i don't understand how it decides if call this or TerminatorKind::Drop
                            self.f.jump(self.b, j, (), target, None);
                            return;
                        }
                        _ => ()
                    }
                };
                if sig.abi() == ExternAbi::RustCall {
                    // when calling a closure directly, the args are packed into a tuple but the callee wants them spread. 
                    assert!(arg_count == 2 && !sig.c_variadic());
                    let ty = sig.inputs().skip_binder()[1];
                    let ty = self.mono_ty(ty);
                    self.unpack_direct_closure_args(&mut arg_vals, &mut arg_types, ty);
                    arg_count = arg_vals.len();
                }
                for (i, &r) in arg_vals.iter().enumerate() {
                    if i == arg_count {
                        assert!(sig.c_variadic());
                        self.f.emit(self.b, O::argv, Kw, (), (), ());
                    }
                    
                    match arg_types[i] {
                        Ferb::Ret::Void => continue,
                        Ferb::Ret::K(k) => {
                            self.f.emit(self.b, O::arg, k, (), r, ());
                        }
                        Ferb::Ret::T(t) => {
                            if self.is_wide(args[i].node.ty(self.mir, self.tcx)) {
                                // :SplatWidePointer
                                // wide pointers are passed as two scalars, this is very similar to what the c abi would do anyway for a struct but not the same when it runs out of registers part way through. 
                                let (a, b) = (self.get_pair_slot(r, true), self.get_pair_slot(r, false));
                                self.f.emit(self.b, O::arg, Kl, (), a, ());
                                self.f.emit(self.b, O::arg, Kl, (), b, ());
                            } else {
                                self.f.emit(self.b, O::argc, Kl, (), t, r);
                            }
                        }
                    }
                }
                if sig.c_variadic() && args.len() == arg_count {
                    // wasm cares if variadic even if none passed
                    self.f.emit(self.b, O::argv, Kw, (), (), ());
                }
                if caller_location {
                    let r = self.caller_location(terminator.source_info);
                    self.emit(O::arg, Kl, (), r, ());
                }
                
                // delay until after it can't be an intrinsic so don't bloat the Module with junk symbols. 
                let callee = callee.unwrap_or_else(|| self.emit_operand(func, Placement::NewScalar(Kl)));
                
                let ret = sig.output();
                let ret = ret.skip_binder();  // discards lifetimes but not generics i hope
                let ret = self.abi_type(ret);
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
            TerminatorKind::Assert { cond, expected, target, msg, .. } => {
                // TODO: am i supposed to check cfg here or does that happen in the frontend? 
                //       (yes, at least for overflow says comment on the enum)
                let failed = self.f.blk();
                self.call_panic(failed, msg);
                let cond = self.emit_operand(cond, Placement::NewScalar(Kw));
                let dest = [failed, self.blocks[*target]];
                self.f.jump(self.b, J::jnz, cond, Some(dest[*expected as usize]), Some(dest[!*expected as usize]));
            }
            TerminatorKind::Drop { place, target, drop, async_fut, .. } => {
                assert!(drop.is_none() && async_fut.is_none());
                self.call_drop(place);
                self.f.jump(self.b, J::jmp, (), Some(self.blocks[*target]), None);
            }
            TerminatorKind::Unreachable |
            TerminatorKind::UnwindTerminate { .. } | TerminatorKind::UnwindResume { .. } => 
                self.f.jump(self.b, J::hlt, (), None, None),  // TODO
            _ => todo!("{:?}", terminator),
        }
    }
    
    fn unpack_direct_closure_args(&mut self, arg_vals: &mut Vec<Ferb::Ref>, arg_types: &mut Vec<Ferb::Ret>, ty: Ty<'tcx>) {
        let base = arg_vals.pop().unwrap();
        let _ = arg_types.pop().unwrap();
        let TyKind::Tuple(inner) = ty.kind() else { todo!("{:?}", ty) };
        
        let layout = self.layout(ty);
        for (i, ty) in inner.iter().enumerate() {
            let ty = self.abi_type(ty);
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
    
    fn load_trait_object(&mut self, self_arg: &mut Ferb::Ref, self_type: &mut Ferb::Ret, vtable_index: usize) -> Ferb::Ref {
        let d_ptr = self.get_pair_slot(*self_arg, true);
        let v_ptr = self.get_pair_slot(*self_arg, false);
        // rustc_codegen_ssa::meth::VirtualIndex::get_fn
        let vtable_index = vtable_index * self.tcx.data_layout().pointer_size().bytes_usize();
        let r = self.f.tmps::<2>();
        self.emit(O::add, Kl, r[0], v_ptr, vtable_index);
        self.emit(O::load, Kl, r[1], r[0], ());
        *self_arg = d_ptr;
        *self_type = Ferb::Ret::K(Kl);  // TODO?
        r[1]
    }
    
    pub(crate) fn scalar_dest(&mut self, dest: Placement) -> Ferb::Ref {
        match dest {
            Placement::Zst => Ferb::Ref::Undef,
            Placement::NewScalar(_) => self.f.tmp(),
            Placement::Scalar(dest, _) => dest,
            Placement::Blit(_, size) | Placement::NewMemory(size) => {
                assert!(size <= 8);
                self.f.tmp()
            },
        }
    }
    
    pub(crate) fn scalar_result(&mut self, dest: Placement, r: impl Reflike, k: Ferb::Cls) -> Ferb::Ref {
        let r = r.r(self.f);
        match dest {
            Placement::Zst => Ferb::Ref::Undef,
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
            Placement::Zst => Ferb::Ref::Undef,
        }
    }
    
    pub(crate) fn new_placement(&mut self, ty: Ty<'tcx>) -> Placement {
        let size = self.layout(ty).size.bytes_usize();
        if size == 0 && !matches!(ty.kind(), TyKind::FnDef(_, _)) {
            return Placement::Zst;
        }
        if is_big(ty) || self.is_wide(ty) {
            return Placement::NewMemory(size)
        }
        let (k, _) = self.cls(ty);
        Placement::NewScalar(k)
    }
    
    fn emit_value(&mut self, value: &Rvalue<'tcx>, dest: Placement) -> Ferb::Ref {
        match value {
            Rvalue::Use(operand) => self.emit_operand(operand, dest),
            Rvalue::RawPtr(_, place) | Rvalue::Ref(_, _, place) => {
                let place = self.addr_place(place);
                let r = match place {
                    Placement::Blit(r, _) => r,
                    Placement::Zst => Ferb::Ref::Undef,
                    _ => todo!("{:?}", place),
                };
                self.ptr_result(dest, r, self.mono_ty(value.ty(self.mir, self.tcx)))
            }
            Rvalue::Cast(kind, value, dest_ty) => {
                let dest_ty = self.mono_ty(*dest_ty);
                let src_ty = value.ty(&self.mir.local_decls, self.tcx);
                let src_ty = self.mono_ty(src_ty);
                let src_place = self.new_placement(src_ty);
                let src = self.emit_operand(value, src_place);
                match kind {
                    CastKind::Transmute => {
                        // HACK: i repr all structs in memory
                        let to_big = is_big(dest_ty) || self.is_wide(dest_ty);
                        let from_big = is_big(src_ty) || self.is_wide(src_ty);
                        if from_big {
                            if !to_big {
                                let r = self.f.tmp();
                                self.emit(O::load, Kl, r, src, ());
                                return self.scalar_result(dest, r, Kl)
                            }
                            match dest {
                                Placement::Blit(dest, size) => {
                                    self.f.blit(self.b, dest, src, size);
                                    dest
                                }
                                Placement::NewMemory(_) => src,
                                _ => todo!(),
                            }
                        } else {
                            if to_big {
                                let r = self.get_memory(dest);
                                self.emit(Ferb::store(Kl), Kw, (), src, r);
                                return r;
                            }
                            return self.scalar_result(dest, src, Kl);
                        }
                    },
                    CastKind::PtrToPtr => {
                        assert!(src_ty.is_any_ptr() && dest_ty.is_any_ptr());
                        if self.is_wide(src_ty) && !self.is_wide(dest_ty) {
                            let r = self.get_pair_slot(src, true);
                            return self.scalar_result(dest, r, Kl)
                        }
                        assert!(self.is_wide(src_ty) == self.is_wide(dest_ty));
                        self.ptr_result(dest, src, src_ty)
                    }
                    CastKind::IntToInt => {
                        let d = dest_ty.primitive_size(self.tcx).bytes();
                        let s = src_ty.primitive_size(self.tcx).bytes();
                        assert!(d <= 8 && s <= 8);
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
                    CastKind::PointerExposeProvenance |
                    CastKind::PointerWithExposedProvenance => {
                        assert!(!self.is_wide(dest_ty) && !self.is_wide(src_ty));  // TODO
                        assert!(is_big(dest_ty) == is_big(src_ty));
                        self.scalar_result(dest, src, Kl)
                    },
                    CastKind::PointerCoercion(kind, _)  => {
                        match kind {
                            PointerCoercion::ClosureFnPointer(_) => todo!(),
                            PointerCoercion::Unsize => self.unsize(dest, src_ty, dest_ty, src),
                            _ => {
                                assert!(!self.is_wide(dest_ty) && !self.is_wide(src_ty));  // TODO
                                self.scalar_result(dest, src, Kl)
                            },
                        }
                    },
                    _ => todo!("{:?} {:?}", value, kind),
                }
            }
            Rvalue::UnaryOp(op, value) => {
                let ty = self.mono_ty(value.ty(self.mir, self.tcx));
                match op {
                    UnOp::PtrMetadata => {
                        let p = self.new_placement(ty);
                        let p = self.emit_operand(value, p);
                        let r = self.get_pair_slot(p, false);
                        self.scalar_result(dest, r, Kl)
                    }
                    UnOp::Not => {
                        let (k, _) = self.cls(ty);
                        let (o, a) = if ty.is_bool() { (O::ceqw, 0) } else { (O::xor, -1i64) };
                        let src = self.emit_operand(value, Placement::NewScalar(k));
                        let r = self.scalar_dest(dest);
                        self.emit(o, k, r, src, a);
                        self.scalar_result(dest, r, k)
                    }
                    _ => todo!("{:?} {:?}", op, value)
                }
            }
            Rvalue::BinaryOp(op, box(lhs, rhs)) => {
                let in_ty = lhs.ty(self.mir, self.tcx);
                let in_ty = self.mono_ty(in_ty);
                let in_k = self.cls(in_ty).0;
                let out_ty = value.ty(self.mir, self.tcx);
                let (lhs, rhs) = (self.emit_operand(lhs, Placement::NewScalar(in_k)), self.emit_operand(rhs, Placement::NewScalar(in_k)));
                let k = self.cls(out_ty).0;
                if op == &BinOp::Offset {
                    assert!(!self.is_wide(in_ty));
                    let inner = in_ty.builtin_deref(true).unwrap();
                    let r = self.step_pointer(lhs, rhs, inner);
                    return self.scalar_result(dest, r, k);
                }
                                
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
                let ty = self.mono_ty(ty);
                let mut layout = self.layout(ty);
                let base = self.get_memory(dest);
                match **kind {
                    Adt(_, variant, _, _, active) => {
                        assert!(active.is_none(), "TODO: union");
                        if let Variants::Multiple { tag_encoding, tag_field, tag, .. } = &layout.variants {
                            if let Some(value) = encoded_tag(variant, tag_encoding) {
                                let (_, o, ty) = tag_load_store(self.tcx, tag);
                                let dest = self.offset_placement(base, layout, *tag_field, ty);
                                let r = self.get_memory(dest);
                                self.emit(o, Kw, (), value, r);
                            }
                            layout = layout.for_variant(&WasteOfTime(self.tcx), variant);
                        }
                    }
                    Tuple | Array(_) | Closure(_, _) => (),
                    _ => assert!(self.is_wide(ty), "{:?}", value),
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
                    let base = self.get_memory(base);
                    let (o, _, ty) = tag_load_store(self.tcx, tag);
                    let base = self.offset_placement(base, layout, *tag_field, ty);
                    let Placement::Blit(base, _) = base else { todo!() };
                    let r = self.scalar_dest(dest);
                    self.emit(o, Kl, r, base, ());
                    match tag_encoding {
                        TagEncoding::Direct => return self.scalar_result(dest, r, Kl),
                        TagEncoding::Niche { .. } => return self.get_niche(dest, r, layout),
                    }
                }
                todo!("discriminant {:?}", place)
            }
            _ => todo!("{:?}", value),
        }
    }
    
    fn unsize(&mut self, dest: Placement, src_ty: Ty<'tcx>, dest_ty: Ty<'tcx>, src: Ferb::Ref) -> Ferb::Ref {
        assert!(self.is_wide(dest_ty) && !self.is_wide(src_ty), "{:?} -> {:?}", src_ty, dest_ty);
        let real_src_ty = src_ty;
        let src_ty = src_ty.builtin_deref(true).unwrap();
        let dest_ty = dest_ty.builtin_deref(true).unwrap();
        let (src_ty, dest_ty) = self.tcx.struct_lockstep_tails_for_codegen(src_ty, dest_ty, TypingEnv::fully_monomorphized());
        match dest_ty.kind() {
            // *[T; N] -> (*[T], N);
            TyKind::Slice(_) | TyKind::Str => {
                let TyKind::Array(_, size) = src_ty.kind() else { todo!() };
                let size = size.try_to_scalar().unwrap_or_else(|| todo!("{:?}", size));
                let size = self.emit_scalar(Placement::NewScalar(Kl), size, self.tcx.types.isize);
                let data = if is_big(real_src_ty) {
                    // HACK: i repr all structs in memory. 
                    //       when unsizing Box<T>, data is the pointer, not stack slot of Box. 
                    let r = self.f.tmp();
                    self.emit(O::load, Kl, r, src, ());
                    r
                } else {
                    src
                };
                self.create_pair(dest, data, size)
            },
            // *(|| {}) -> (*captures, *vtable);   or any other trait object
            TyKind::Dynamic(bound, _) => {
                assert!(!matches!(src_ty.kind(), TyKind::Dynamic(_, _)));   // TODO: is this special?
                // TODO: surely i shouldn't need a special case for this?
                let closure = matches!(src_ty.kind(), TyKind::Closure(_, _));
                let self_type = if closure { real_src_ty } else { src_ty };
                let bound = bound.principal().map(|it| self.tcx.instantiate_bound_regions_with_erased(it));
                let id = self.tcx.vtable_allocation((self_type, bound));
                let id = self.global_alloc(id, Size::from_bytes(0));
                let data = if closure { 
                    let data = self.alloca(8);     // &&Closure
                    self.emit(O::storel, Kw, (), src, data);
                    data
                } else {
                    src
                };
                self.create_pair(dest, data, id)
            }
            _ => todo!(),
        }
    }
    
    pub(crate) fn layout(&self, ty: Ty<'tcx>) -> TyAndLayout<'tcx> {
        let ty = self.mono_ty(ty);
        WasteOfTime(self.tcx).layout_of(ty)
    }
    
    fn emit_aggregate(&mut self, base: Ferb::Ref, layout: TyAndLayout<'tcx>, fields: &IndexVec<FieldIdx, Operand<'tcx>>) {
        for field in layout.fields.index_by_increasing_offset() {
            let field = FieldIdx::new(field);
            let value = &fields[field];
            let ty = value.ty(self.mir, self.tcx);
            if self.layout(ty).size.bytes() == 0 { continue };
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
    
    pub fn addr_place(&mut self, place: &Place<'tcx>) -> Placement {
        let ty = place.ty(self.mir, self.tcx);
        if let Some(it) = place.as_local() {
            return self.locals[it];
        }
        let final_size = self.layout(ty.ty).size.bytes_usize();
        let mut base = match self.locals[place.local] {
            Placement::Zst => return Placement::Zst,
            Placement::NewScalar(_) | Placement::NewMemory(_) => todo!(),
            Placement::Scalar(r, _) | Placement::Blit(r, _) => r,
        };
        let mut parent_ty = self.mono_ty(self.mir.local_decls[place.local].ty);
        let mut projection = place.projection.iter();
        if place.is_indirect() {
            parent_ty = match parent_ty.kind() {
                TyKind::RawPtr(inner, _) | TyKind::Ref(_, inner, _) => *inner,
                _ => todo!(),
            };
            projection.next();
        };
        
        // when projecting from *(unsized struct) to *(its unsized field) 
        // need to offset the pointer but keep the parent's metadata.  
        let mut metadata: Option<Ferb::Ref> = None;
        if parent_ty.is_adt() && self.tcx.type_has_metadata(self.mono_ty(parent_ty), TypingEnv::fully_monomorphized()) {
            metadata = Some(self.get_pair_slot(base, false));
            base = self.get_pair_slot(base, true);
        }
        
        // note: is_wide: &[T] vs Slice: [T]. can be unsized because place is already a pointer. 
        for it in projection {
            use ProjectionElem::*;
            (parent_ty, base) = match it {
                Deref => unreachable!(),  // only allowed as first projection
                Field(field_idx, inner) => {
                    use FieldsShape::*;
                    let layout = self.layout(parent_ty);
                    let offsets = match &layout.fields {
                        Arbitrary { offsets, .. } => offsets,
                        Primitive => return Placement::Blit(base, final_size),
                        _ => todo!("{:?}", place),
                    };
                    if layout.size.bytes() == 0 { return Placement::Zst };
                    (inner, self.offset(base, offsets[field_idx]))
                }
                Downcast(_, varient) => {
                    let layout = self.layout(parent_ty);
                    let layout = layout.for_variant(&WasteOfTime(self.tcx), varient);
                    let first = layout.layout.fields.index_by_increasing_offset().next().unwrap();
                    let inner = ty.projection_ty(self.tcx, it).ty;
                    (inner, self.offset(base, layout.fields.offset(first)))
                },
                Index(index) => {
                    let Placement::Scalar(index, _) = self.locals[index] else { todo!() };
                    let (inner, p) = match parent_ty.kind() {
                        &TyKind::Array(inner, _) => (inner, base),
                        &TyKind::Slice(inner) => (inner, self.get_pair_slot(base, true)),
                        _ => todo!("{:?}", parent_ty),
                    };
                    (inner, self.step_pointer(p, index, inner))
                }
                ConstantIndex { offset, from_end, .. } => {
                    assert!(!from_end, "{:?}", place);  // TODO
                    let (inner, p) = match parent_ty.kind() {
                        &TyKind::Slice(inner) => (inner, self.get_pair_slot(base, true)),
                        &TyKind::Array(inner, _) => (inner, base),
                        _ => todo!(), 
                    };
                    (inner, self.step_pointer(p, offset, inner))
                }
                _ => todo!("{:?}", place),
            };
        }
        if let Some(metadata) = metadata {
            if self.tcx.type_has_metadata(self.mono_ty(ty.ty), TypingEnv::fully_monomorphized()) {
                base = self.create_pair(Placement::NewMemory(16), base, metadata);
            }
        }
        Placement::Blit(base, final_size)
    }
    
    fn step_pointer(&mut self, base: Ferb::Ref, index: impl Reflike, inner: Ty<'tcx>) -> Ferb::Ref {
        let layout = self.layout(inner);
        let step = layout.size.bytes();
        let r = self.f.tmps::<2>();
        self.f.emit(self.b, O::mul, Kl, r[0], index, step);
        self.f.emit(self.b, O::add, Kl, r[1], base, r[0]);
        r[1]
    }
    
    fn load_place(&mut self, dest: Placement, place: &Place<'tcx>) -> Ferb::Ref {
        let src = self.addr_place(place);
        self.copy_placement(dest, src)
    }
    
    pub(crate) fn copy_placement(&mut self, dest: Placement, src: Placement,) -> Ferb::Ref {
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
                Placement::Zst => Ferb::Ref::Undef,
            },
            Placement::Zst => Ferb::Ref::Undef,
        }
    }
    
   pub(crate) fn emit_operand(&mut self, operand: &Operand<'tcx>, dest: Placement) -> Ferb::Ref {
        match operand {
            Operand::Copy(place) => self.load_place(dest, place),
            Operand::Move(place) => self.load_place(dest, place),
            Operand::Constant(it) => {
                let (val, ty) = self.finish_const(it);
                self.emit_const(dest, val, ty)
            }
            Operand::RuntimeChecks(it) => {
                let it = it.value(self.tcx.sess);
                self.scalar_result(dest, it as u64, Kw)
            },
        }
    }
    
    pub(crate) fn emit_const(&mut self, dest: Placement, val: ConstValue, ty: Ty<'tcx>) -> Ferb::Ref {
        match val {
            ConstValue::Scalar(it) => self.emit_scalar(dest, it, ty),
            ConstValue::ZeroSized => {
                // const known function gets here. the value is stored in the type field. 
                match ty.kind() {
                    &TyKind::FnDef(def, args) => {
                        let id = get_symbol(self.m, self.tcx, def, Some(args));
                        if dest == Placement::Zst {
                            // TODO: this is a problem. i'd rather never get here. format! does but print! doesn't
                            return Ferb::Ref::Undef;
                        }
                        assert!(dest != Placement::Zst);
                        self.scalar_result(dest, id, Kl)
                    },
                    TyKind::Tuple(_) | TyKind::Adt(_, _) | TyKind::Closure(_, _) 
                        => Ferb::Ref::Undef,
                    _ => todo!("zst {:?}", ty)
                }
            }
            ConstValue::Slice { alloc_id, meta } => {
                let p = self.global_alloc(alloc_id, Size::ZERO);
                self.create_pair(dest, p, meta)
            }
            ConstValue::Indirect { alloc_id, offset } => {
                let size = self.layout(ty).size.bytes_usize();
                let src = self.global_alloc(alloc_id, offset);
                let src = src.r(self.f);
                self.copy_placement(dest, Placement::Blit(src, size))
            }
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
    
    fn global_alloc(&mut self, p: AllocId, off: Size) -> Ferb::Id<Ferb::Sym> {
        assert_eq!(off.bytes(), 0, "TODO: offset ptr");
        global_alloc(self.m, self.tcx, self.c, p)
    }
    
    fn alloca(&mut self, size: usize) -> Ferb::Ref {
        let r = self.f.tmp();
        self.f.emit(self.start_block, O::alloc8, Kl, r, size, ());
        r
    }
    
    pub(crate) fn cls(&self, ty: Ty<'tcx>) -> (Ferb::Cls, ()) {
        let ty = self.mono_ty(ty);
        val_cls(self.tcx, ty)
    }
    
    pub(crate) fn mono_ty(&self, it: Ty<'tcx>) -> Ty<'tcx> {
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

    fn emit_scalar(&mut self, dest: Placement, it: Scalar, ty: Ty<'tcx>) -> Ferb::Ref {
        match it {
            Scalar::Int(it) => {
                let (k, _) = self.cls(ty);
                let raw = it.to_bits(it.size()) as u64;
                self.scalar_result(dest, raw, k)
            }
            Scalar::Ptr(p, _) => {
                assert!(!is_big(ty));
                let (p, off) = p.prov_and_relative_offset();
                let p = self.global_alloc(p.alloc_id(), off);
                self.scalar_result(dest, p, Kl)
            }
        }
    }
    
    pub(crate) fn abi_type(&mut self, ty: Ty<'tcx>) -> Ferb::Ret {
        let ty = self.mono_ty(ty);
        abi_type(self.m, self.tcx, self.c, ty)
    }

    fn ptr_result(&mut self, dest: Placement, src: Ferb::Ref, src_ty: Ty<'tcx>) -> Ferb::Ref {
        assert!(src_ty.is_any_ptr());
        if self.is_wide(src_ty) {
            self.copy_placement(dest, Placement::Blit(src, 16))
        } else {
            self.scalar_result(dest, src, Kl)
        }
    }

    fn is_wide(&self, ty: Ty<'tcx>) -> bool {
        is_wide(self.tcx, self.mono_ty(ty))
    }
}

fn global_alloc(m: &mut Ferb::Module, tcx: TyCtxt, c: &mut Ctx, p: AllocId) -> Ferb::Id<Ferb::Sym> {
    if let Some(&id) = c.allocations.get(&p) { return id; }
    
    let id = match tcx.global_alloc(p) {
        GlobalAlloc::Memory(_) => m.anon(),
        GlobalAlloc::Static(def) => 
            get_symbol(m, tcx, def, None),
        GlobalAlloc::Function { instance } => 
            get_symbol(m, tcx, instance.def_id(), Some(instance.args)),
        _ => todo!(),
    };
    c.allocations.insert(p, id);
    id
}

fn encoded_tag(variant: VariantIdx, tag_encoding: &TagEncoding<VariantIdx>) -> Option<u64> {
    Some(match tag_encoding {
        TagEncoding::Direct => variant.as_u32() as u64,
        TagEncoding::Niche { untagged_variant, niche_variants, niche_start } => {
            if variant == *untagged_variant {
                return None
            };
            let niche_value = variant.as_u32() - niche_variants.start().as_u32();
            let niche_value = (niche_value as u128).wrapping_add(*niche_start);
            niche_value as u64
        },
    })
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
        Pointer(_) => (O::load, O::storel, tcx.types.i64),
        _ => todo!("{:?}", tag),
    }
}

fn is_big(ty: Ty) -> bool {
    assert!(!matches!(ty.kind(), TyKind::Param(_)));
    matches!(ty.kind(), TyKind::Adt(_, _) | TyKind::Tuple(_) | TyKind::Array(_, _) | TyKind::Closure(_, _))
}

fn val_cls<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> (Ferb::Cls, ()) {
    if is_big(ty) {
        return (Kl, ());
    }
    if is_wide(tcx, ty) { return (Kl, ()) }
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
    tcx.layout_of(PseudoCanonicalInput { value, typing_env: TypingEnv::fully_monomorphized() }).unwrap()
}

// TODO: it's probably a loosing game to try to use my abi stuff like this instead of rustc's. 
//       because it's important to match calling convention even for non-extern-c so you can:
//       - use precompiled standard library
//       - compile dependencies with llvm optimisations
//       so my backend should give you the option of being explicit about how you want to pass things
//       instead of needing to reverse engineer a matching extern "C" signeture. 
fn abi_type<'tcx>(m: &mut Ferb::Module, tcx: TyCtxt<'tcx>, c: &mut Ctx<'tcx>, ty: Ty<'tcx>) -> Ferb::Ret {
    let (k, _) = val_cls(tcx, ty);
    let layout = layout_of(tcx, ty);
    let size = layout.size.bytes_usize();
    if size == 0 {
        return Ferb::Ret::Void;
    }
    if !is_big(ty) && !is_wide(tcx, ty) {
        return Ferb::Ret::K(k);
    }
    if let Some(&t) = c.types.get(&ty) { return Ferb::Ret::T(t) };
    
    use Ferb::Field::*;
    let cases = match &layout.fields {
        FieldsShape::Primitive => vec![vec![abi_field(m, tcx, c, ty)]],
        FieldsShape::Union(count) => {
            let mut cases = vec![];
            for i in 0..count.get() {
                let ty = layout.field(&WasteOfTime(tcx), i);
                if ty.layout.size.bytes() != 0 {
                    cases.push(vec![abi_field(m, tcx, c, ty.ty)]);
                }
            }
            cases
        },
        &FieldsShape::Array { stride, count } => {
            let mut fields = vec![];
            let inner = layout.field(&WasteOfTime(tcx), 0);
            let size = inner.layout.size.bytes();
            let inner = abi_field(m, tcx, c, inner.ty);
            for _ in 0..count {
                fields.push(inner);
                pad(&mut fields, stride.bytes() as u32 - size as u32);
            }
            vec![fields]
        }
        FieldsShape::Arbitrary { offsets, in_memory_order } => {
            let mut fields = vec![];
            let mut off = 0;
            for it in in_memory_order {
                pad(&mut fields, offsets[*it].bytes() as u32 - off);
                let ty = layout.field(&WasteOfTime(tcx), it.as_usize());
                if is_wide(tcx, ty.ty) {
                    // TODO: clearly my is_wide doesn't work
                    for _ in 0..ty.layout.size.bytes()/8 {
                        fields.push(Scalar(Ferb::FieldType::Fl));
                    }
                } else {
                    if ty.layout.size.bytes() != 0 {
                        fields.push(abi_field(m, tcx, c, ty.ty));
                    }
                }
                off = offsets[*it].bytes() as u32 + ty.layout.size.bytes() as u32;
            }
            pad(&mut fields, size as u32 - off);
            vec![fields]
        },
    };
    
    let t = m.typ(Ferb::TypeLayout {
        align: layout.align.bytes_usize(),
        size,
        cases,
        is_union: matches!(layout.fields, FieldsShape::Union(_)),
    });
    c.types.insert(ty, t);
    Ferb::Ret::T(t)
}

fn abi_field<'tcx>(m: &mut Ferb::Module, tcx: TyCtxt<'tcx>, c: &mut Ctx<'tcx>, ty: Ty<'tcx>) -> Ferb::Field {
    let layout = layout_of(tcx, ty);
    use Ferb::Field::*; use Ferb::FieldType::*;
    match &layout.fields {
        FieldsShape::Primitive => Scalar(if ty.is_floating_point() {
            match layout.size.bytes() { 4 => Fs, 8 => Fd, _ => todo!(), }
        } else {
            match layout.size.bytes() { 1 => Fb, 2 => Fh, 4 => Fw, 8 => Fl, _ => todo!(), }
        }),
        _ => match abi_type(m, tcx, c, ty) {
            Ferb::Ret::K(k) => Scalar(match k {
                Kw => Fw, Kl => Fl, Ks => Fs, Kd => Fd,
            }),
            Ferb::Ret::Void => Pad(0),
            Ferb::Ret::T(t) => Struct(t),
        }
    }
}

// TODO: this is dumb, i'm inconsistant about what FPad means. 
//       franca/backend/amd64/sysv.fr/retr doesn't like things like { w, pad 4 } for Option<i32>. 
fn pad(fields: &mut Vec<Ferb::Field>, size: u32) {
    if size == 0 { return };
    match size {
        1 => fields.push(Ferb::Field::Scalar(Ferb::FieldType::Fb)),
        2 => fields.push(Ferb::Field::Scalar(Ferb::FieldType::Fh)),
        4 => fields.push(Ferb::Field::Scalar(Ferb::FieldType::Fw)),
        8 => fields.push(Ferb::Field::Scalar(Ferb::FieldType::Fl)),
        _ => fields.push(Ferb::Field::Pad(size)),
    }
}

pub(crate) fn get_instance<'tcx>(tcx: TyCtxt<'tcx>, def: DefId, args: Option<GenericArgsRef<'tcx>>) -> Instance<'tcx> {
    let span = tcx.def_span(def);
    let mono = TypingEnv::fully_monomorphized();
    match args {
        Some(args) => Instance::expect_resolve(tcx, mono, def, args, span),
        None => Instance::mono(tcx, def),
    }
}

pub(crate) fn get_symbol<'tcx>(m: &mut Ferb::Module, tcx: TyCtxt<'tcx>, def: DefId, args: Option<GenericArgsRef<'tcx>>) -> Ferb::Id<Ferb::Sym> {
    m.intern(tcx.symbol_name(get_instance(tcx, def, args)).name)
}

fn is_wide<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    assert!(!matches!(ty.kind(), TyKind::Param(_)));
    let inner = if let Some(it) = ty.boxed_ty() {
        it
    } else {
        if !ty.is_any_ptr() || matches!(ty.kind(), TyKind::FnPtr(_, _)) { return false };
        ty.builtin_deref(true).unwrap_or_else(|| todo!("{:?}", ty))
    };
    tcx.type_has_metadata(inner, TypingEnv::fully_monomorphized())
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

struct WasteOfTime<'tcx>(TyCtxt<'tcx>);

impl<'tcx> HasDataLayout for WasteOfTime<'tcx> {
    fn data_layout(&self) -> &rustc_abi::TargetDataLayout {
        &self.0.data_layout
    }
}

impl<'tcx> HasTypingEnv<'tcx> for WasteOfTime<'tcx> {
    fn typing_env(&self) -> TypingEnv<'tcx> {
        TypingEnv::fully_monomorphized()
    }
}
impl<'tcx> HasTyCtxt<'tcx> for WasteOfTime<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.0
    }
}
impl<'tcx> LayoutOfHelpers<'tcx> for WasteOfTime<'tcx> {
    type LayoutOfResult = layout::TyAndLayout<'tcx>;

    fn handle_layout_err(&self, _: layout::LayoutError<'tcx>, _: Span, _: Ty<'tcx>) -> <Self::LayoutOfResult as layout::MaybeResult<layout::TyAndLayout<'tcx>>>::Error {
        todo!()
    }
}
