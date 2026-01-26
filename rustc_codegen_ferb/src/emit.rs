use rustc_const_eval::interpret::{GlobalAlloc, Scalar, alloc_range};
use rustc_index::{Idx, IndexVec};
use rustc_middle::{mir::{BasicBlock, BasicBlockData, ConstOperand, ConstValue, Local, Operand, RETURN_PLACE, Rvalue, StatementKind, TerminatorKind, mono::{CodegenUnit, MonoItem}}, ty::{EarlyBinder, Instance, TyCtxt, TyKind, TypingEnv}};
use ferb::builder as Ferb;
use Ferb::Cls::*;
use Ferb::{J, O};
use rustc_abi::Size;

struct Emit<'f, 'tcx> {
    tcx: TyCtxt<'tcx>,
    m: &'f mut Ferb::Module,
    f: &'f mut Ferb::Func,
    b: Ferb::BlkId,
    blocks: IndexVec<BasicBlock, Ferb::BlkId>,
    locals: IndexVec<Local, Ferb::Ref>,
    instance: Instance<'tcx>,
}

pub(crate) fn emit<'tcx>(tcx: TyCtxt<'tcx>, cgu: &CodegenUnit<'tcx>) -> Ferb::Module {
    let mut m = Ferb::Module::new();
    let items = cgu.items_in_deterministic_order(tcx);
    for (it, _data) in items {
        match it {
            MonoItem::Fn(it) => {
                let id = m.intern(tcx.symbol_name(it).name);
                let mut f = Ferb::Func::new(id, Ferb::Ret::K(Kw));
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
                };
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
                    let dest = self.locals[place.local];
                    let r = self.emit_value(value);
                    self.f.emit(self.b, O::copy, Kw, dest, r, ());
                },
                StatementKind::Nop => (),
                _ => todo!("{:?}", stmt),
            }
        }
        let terminator = blk.terminator();
        match &terminator.kind {
            &TerminatorKind::Goto { target } => {
                self.f.jump(self.b, J::jmp, (), Some(self.blocks[target]), None);
            }
            TerminatorKind::Return => {
                self.f.jump(self.b, J::retw, self.locals[RETURN_PLACE], None, None);
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
            _ => todo!("{:?}", terminator),
        }
    }
    
    fn emit_value(&mut self, value: &Rvalue<'tcx>) -> Ferb::Ref {
        match value {
            Rvalue::Use(operand) => self.emit_operand(operand),
            _ => todo!("{:?}", value),
        }
    }
    
    fn emit_operand(&mut self, operand: &Operand<'tcx>) -> Ferb::Ref {
        match operand {
            Operand::Constant(it) => {
                let (val, ty) = self.finish_const(it);
                match val {
                    ConstValue::Scalar(it) => {
                        match it {
                            Scalar::Int(it) => {
                                let it = it.to_u32() as i64;
                                return self.f.con(Ferb::Id::None, it);
                            }
                            Scalar::Ptr(p, _) => {
                                let (p, off) = p.prov_and_relative_offset();
                                let p = self.tcx.global_alloc(p.alloc_id());
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
                    _ => todo!("{:?}", operand),
                }
            }
            _ => todo!("{:?}", operand),
        }
    }
    
    // gets rid of ::Unevaluated
    fn finish_const(&mut self, it: &ConstOperand<'tcx>) -> (ConstValue, rustc_middle::ty::Ty<'tcx>) {
        let mono = TypingEnv::fully_monomorphized();
        let b = EarlyBinder::bind(it.const_);
        let v = self.instance.instantiate_mir_and_normalize_erasing_regions(self.tcx, mono, b);
        let val = v.eval(self.tcx, mono, it.span).unwrap();
        (val, v.ty())
    }
}
