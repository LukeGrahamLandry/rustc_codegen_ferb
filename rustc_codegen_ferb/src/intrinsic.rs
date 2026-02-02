use ferb::builder as Ferb;
use Ferb::{O, J, Cls::*};
use rustc_hir::def_id::DefId;
use rustc_middle::{mir::{AssertKind, CopyNonOverlapping, Operand}, ty::Ty};
use rustc_span::sym;

use crate::emit::{Emit, Placement};

impl<'f, 'tcx> Emit<'f, 'tcx> {
    pub(crate) fn call_memcpy(&mut self, it: &CopyNonOverlapping<'tcx>) {
        let (dest, src, size) = (
            self.emit_operand(&it.dst, Placement::NewScalar(Kl)),
            self.emit_operand(&it.src, Placement::NewScalar(Kl)),
            self.emit_operand(&it.count, Placement::NewScalar(Kl)),
        );
        // TODO: if const size: self.f.blit(self.b, dest, src, size);
        let id = self.m.intern("memcpy");
        self.emit(O::arg, Kl, (), dest, ());
        self.emit(O::arg, Kl, (), src, ());
        self.emit(O::arg, Kl, (), size, ());
        self.emit(O::call, Kw, (), id, ());
    }

    // TODO: emit the operands properly and call the panic handler. 
    pub(crate) fn call_panic(&mut self, failed: Ferb::BlkId, msg: &AssertKind<Operand<'tcx>>)  {
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
    }
        
    pub(crate) fn call_intrinsic(&mut self, dest: Placement, arg_vals: &[Ferb::Ref], def: DefId, inputs: &'tcx [Ty<'tcx>]) -> bool {
        let intrinsic = self.tcx.item_name(def);
        match intrinsic {
            sym::black_box => {
                // TODO: do a #no_inline that escapes the address so it's actually a black_box to opt
                assert!(arg_vals.len() == 1);
                let result = match self.abi_type(inputs[0]) {
                    Ferb::Ret::K(k) => Placement::Scalar(arg_vals[0], k),
                    Ferb::Ret::Void => Placement::Zst,
                    Ferb::Ret::T(t) => Placement::Blit(arg_vals[0], self.m.size_of(t)),
                };
                self.copy_placement(dest, result);
            }
            sym::ctpop => {  // CounT POPulation
                assert!(arg_vals.len() == 1);
                let r = self.scalar_dest(dest);
                let (k, _) = self.cls(inputs[0]);
                self.emit(O::ones, k, r, arg_vals[0], ());
                self.scalar_result(dest, r, k);
            }
            sym::write_bytes => {
                let id = self.m.intern("memset");
                let (dest, value, size) = (arg_vals[0], arg_vals[1], arg_vals[2]);
                self.emit(O::arg, Kl, (), dest, ());
                self.emit(O::arg, Kl, (), value, ());
                self.emit(O::arg, Kl, (), size, ());
                self.emit(O::call, Kw, (), id, ());
            }
            sym::size_of_val => {
                let size = self.layout(inputs[0]).size.bytes();
                self.scalar_result(dest, size, Kl);
            }
            sym::align_of_val => {
                let size = self.layout(inputs[0]).align.bytes();
                self.scalar_result(dest, size, Kl);
            }
            _ => return false,
        }
        true
    }
}
