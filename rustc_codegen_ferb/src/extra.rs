use rustc_abi::{ExternAbi, TagEncoding, Variants};
use rustc_ast::expand::allocator::{
    AllocatorMethod, AllocatorTy, NO_ALLOC_SHIM_IS_UNSTABLE,
    default_fn_name, global_fn_name,
};
use rustc_codegen_ssa::{ModuleKind, base::{allocator_kind_for_codegen, allocator_shim_contents}};
use rustc_hir::{LangItem, def_id::LOCAL_CRATE};
use rustc_middle::{mir::{Place, mono::{CodegenUnit, CodegenUnitNameBuilder, MonoItem}}, ty::{Instance, InstanceKind, Ty, TyCtxt, TyKind, TypingEnv}};
use rustc_session::config::{EntryFnType, OutputType};
use rustc_span::DUMMY_SP;
use rustc_symbol_mangling::mangle_internal_symbol;
use ferb::builder::*;

use crate::{compiled_module, emit::{Emit, Placement, get_instance, get_symbol}, translate_target};

pub(crate) fn allocator_module(tcx: TyCtxt) -> Option<rustc_codegen_ssa::CompiledModule> {
    allocator_kind_for_codegen(tcx).map(|kind| {
        let mut m = Module::new();
        allocator(tcx, &mut m, &allocator_shim_contents(tcx, kind));
        let names = &mut CodegenUnitNameBuilder::new(tcx);
        let name = names.build_cgu_name(LOCAL_CRATE, &["crate"], Some("allocator")).to_string();
        let (arch, os) = translate_target(tcx.sess);
        let obj = unsafe { ferb::compile_aot(&*m.finish(), "main", "", arch, os, ferb::Artifact::Relocatable, false, false) };
        let outputs = &tcx.output_filenames(());
        let output_file = outputs.temp_path_for_cgu(OutputType::Object, &name, tcx.sess.invocation_temp.as_deref());
        std::fs::write(&output_file, obj.unwrap()).unwrap();
        compiled_module(name, ModuleKind::Allocator, Some(output_file))
    })
}

// https://github.com/rust-lang/rust/blob/a1db344c0829cb682df4174e9370b60915751605/compiler/rustc_codegen_llvm/src/allocator.rs
fn allocator(tcx: TyCtxt<'_>, m: &mut Module, methods: &[AllocatorMethod]) {
    for method in methods {
        let ret = match method.output {
            AllocatorTy::ResultPtr => Ret::K(Cls::Kl),
            AllocatorTy::Unit | AllocatorTy::Never => Ret::Void,
            _ => unreachable!(),
        };
        let from_name = mangle_internal_symbol(tcx, &global_fn_name(method.name));
        let to_name = mangle_internal_symbol(tcx, &default_fn_name(method.name));
        let mut f = Func::new(m.intern(&*from_name), ret);
        let b = f.blk();
        let mut args = Vec::with_capacity(method.inputs.len());
        for input in method.inputs.iter() {
            let n = 1 + matches!(input.ty, AllocatorTy::Layout) as u32;
            for _ in 0..n {
                let r = f.tmp();
                f.emit(b, O::par, Cls::Kl, r, (), ());
                args.push(r);
            }
        }
        for r in args { 
            f.emit(b, O::arg, Cls::Kl, (), r, ());
        }
        let (r, j, k) = if ret == Ret::Void { (Ref::Null, J::ret0, Cls::Kw) } else { (f.tmp(), J::retl, Cls::Kl) };
        let callee = m.intern(&*to_name);
        f.emit(b, O::call, k, r, callee, ());
        f.jump(b, j, r, None, None);
        m.func(f);
    }

    // __rust_no_alloc_shim_is_unstable_v2
    let from_name = mangle_internal_symbol(tcx, NO_ALLOC_SHIM_IS_UNSTABLE);
    let mut f = Func::new(m.intern(&*from_name), Ret::Void);
    let b = f.blk();
    f.jump(b, J::ret0, Ref::Null, None, None);
    m.func(f);
}

// https://github.com/rust-lang/rust/blob/a1db344c0829cb682df4174e9370b60915751605/compiler/rustc_codegen_ssa/src/base.rs#L469
pub(crate) fn maybe_create_entry_wrapper<'tcx>(m: &mut Module, tcx: TyCtxt<'tcx>, cgu: &CodegenUnit<'tcx>) {
    let Some((main_def, entry_type)) = tcx.entry_fn(()) else { return };
    let main_is_local = main_def.is_local();
    let instance = get_instance(tcx, main_def, None);
    if (main_is_local && !cgu.contains_item(&MonoItem::Fn(instance))) || !cgu.is_primary() {
        return;
    }
    let rust_main = get_symbol(m, tcx, main_def, None);

    let mut f = Func::new(m.intern("main"), Ret::K(Cls::Kw));
    let b = f.blk();
    let (argc, argv) = if tcx.sess.target.main_needs_argc_argv {
        let r = f.tmps::<2>();
        f.emit(b, O::par, Cls::Kl, r[0], (), ());
        f.emit(b, O::par, Cls::Kl, r[1], (), ());
        (r[0], r[1])
    } else {
        (Ref::Zero, Ref::Zero)
    };
    let r = f.tmp();

    let main_ret_ty = tcx.fn_sig(main_def).no_bound_vars().unwrap().output();
    let main_ret_ty = tcx.normalize_erasing_regions(TypingEnv::fully_monomorphized(), main_ret_ty.no_bound_vars().unwrap());

    let EntryFnType::Main { sigpipe } = entry_type;
    let start_def = tcx.require_lang_item(LangItem::Start, DUMMY_SP);
    let start_fn = get_symbol(m, tcx, start_def, Some(tcx.mk_args(&[main_ret_ty.into()])));
    f.emit(b, O::arg, Cls::Kl, (), rust_main, ());
    f.emit(b, O::arg, Cls::Kl, (), argc, ());
    f.emit(b, O::arg, Cls::Kl, (), argv, ());
    f.emit(b, O::arg, Cls::Kl, (), sigpipe as usize, ());
    f.emit(b, O::call, Cls::Kw, r, start_fn, ());
    f.jump(b, J::retw, r, None, None);
    m.func(f);
}


impl<'f, 'tcx> Emit<'f, 'tcx> {
    // https://github.com/rust-lang/rust/blob/a1db344c0829cb682df4174e9370b60915751605/compiler/rustc_codegen_ssa/src/mir/block.rs#L596
    pub(crate) fn call_drop(&mut self, place: &Place<'tcx>) {
        let ty = self.mono_ty(place.ty(self.mir, self.tcx).ty);
        let drop_fn = Instance::resolve_drop_in_place(self.tcx, ty);

        if let InstanceKind::DropGlue(_, None) = drop_fn.def {
            // you get TerminatorKind::Drop that does nothing 
            // when generic without +Copy bound but the concrete type is copy. 
            return;
        }
        // TODO: factor out the terminatorkind::call stuff so this can just call it with the instance?
        
        if let TyKind::Dynamic(_, _) = ty.kind() {
            todo!("{:?} {:?}", place, drop_fn);
        }
        
        // not one that has special handling in TerminatorKind::Call
        let sig = drop_fn.ty(self.tcx, TypingEnv::fully_monomorphized()).fn_sig(self.tcx);
        assert!(sig.abi() != ExternAbi::RustCall);
        assert!(!matches!(drop_fn.def, InstanceKind::Intrinsic(_) | InstanceKind::Virtual(_, _)));
        // drop_in_place isn't #[track_caller], specific impl Drop doesn't matter.
        assert!(!drop_fn.def.requires_caller_location(self.tcx));
        
        let place = self.addr_place(place);
        let Placement::Blit(r, _) = place else { todo!() }; 
        // TODO: can you drop an unsized type other than a trait object? wide *mut T
        let id = self.m.intern(self.tcx.symbol_name(drop_fn).name);
        self.emit(O::arg, Cls::Kl, (), r, ());
        self.emit(O::call, Cls::Kw, (), id, ());
    }
    
    // https://github.com/rust-lang/rust/blob/a1db344c0829cb682df4174e9370b60915751605/compiler/rustc_codegen_ssa/src/mir/operand.rs#L483
    pub(crate) fn get_niche(&mut self, dest: Placement, tag_r: Ref, layout: rustc_abi::TyAndLayout<'_, Ty<'_>>) -> Ref {
        let Variants::Multiple { tag_encoding, .. } = &layout.variants else { unreachable!() };
        let TagEncoding::Niche { untagged_variant, niche_variants, niche_start } = tag_encoding else { unreachable!() };
        let relative_max = niche_variants.end().as_u32() - niche_variants.start().as_u32();
        assert!(relative_max == 0);  // TODO
        let is_niche = self.f.tmp();
        self.emit(O::ceql, Cls::Kw, is_niche, tag_r, *niche_start as u64);
        let tagged_discr = niche_variants.start().as_u32() as u64;
        self.f.sel(self.b, tag_r, Cls::Kl, is_niche, tagged_discr, untagged_variant.as_u32() as u64);
        self.scalar_result(dest, tag_r, Cls::Kl)
    }
}
