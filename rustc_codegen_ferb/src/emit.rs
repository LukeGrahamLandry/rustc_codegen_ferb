use rustc_const_eval::interpret::Scalar;
use rustc_index::{Idx, IndexVec};
use rustc_middle::{mir::{BasicBlock, BasicBlockData, Body, Const, ConstValue, Local, Operand, Rvalue, StatementKind, TerminatorKind, mono::{CodegenUnit, MonoItem}}, ty::{InstanceKind, TyCtxt}};
use ferb::builder as Ferb;
use Ferb::Cls::*;
use Ferb::{J, O};

struct Emit<'f, 'tcx> {
    tcx: TyCtxt<'tcx>,
    m: &'f mut Ferb::Module,
    f: &'f mut Ferb::Func,
    mir: &'tcx Body<'tcx>,
    b: Ferb::BlkId,
    blocks: IndexVec<BasicBlock, Ferb::BlkId>,
    locals: IndexVec<Local, Ferb::Ref>,
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
                    mir,
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
    fn emit_block(&mut self, blk: &BasicBlockData) {
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
                self.f.jump(self.b, J::retw, self.locals[Local::new(0)], None, None);
            }
            _ => todo!(),
        }
    }
    
    fn emit_value(&mut self, value: &Rvalue) -> Ferb::Ref {
        match value {
            Rvalue::Use(operand) => match operand {
                Operand::Constant(it) => {
                    match it.const_ {
                        Const::Val(it, _ty) => {
                            match it {
                                ConstValue::Scalar(it) => {
                                    match it {
                                        Scalar::Int(it) => {
                                            let it = it.to_u32() as i64;
                                            return self.f.con(Ferb::Id::None, it);
                                        }
                                        _ => todo!("{:?}", value),
                                        
                                    }
                                }
                                _ => todo!("{:?}", value),
                                
                            }
                        }
                        _ => todo!("{:?}", value),
                    }
                },
                _ => todo!("{:?}", value),
            },
            _ => todo!("{:?}", value),
        }
    }
}
