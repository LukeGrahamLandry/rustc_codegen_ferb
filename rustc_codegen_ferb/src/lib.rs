#![feature(rustc_private)]

use std::any::Any;

use rustc_codegen_ssa::{
    CodegenResults, CompiledModule, CrateInfo, ModuleKind, traits::CodegenBackend,
};
use rustc_data_structures::fx::FxIndexMap;
use rustc_middle::{
    dep_graph::{WorkProduct, WorkProductId},
    ty::TyCtxt,
};
use rustc_session::{
    Session,
    config::{OutFileName, OutputFilenames, OutputType},
};

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_codegen_ssa;
extern crate rustc_const_eval;
extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_fs_util;
extern crate rustc_hir;
extern crate rustc_incremental;
extern crate rustc_index;
extern crate rustc_log;
extern crate rustc_metadata;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_symbol_mangling;
extern crate rustc_target;

#[allow(unused_extern_crates)]
extern crate rustc_driver;

pub struct FerbCodegenBackend {}

pub struct OngoingCodegen {
    crate_info: CrateInfo,
    cgu_name: String,
}

impl CodegenBackend for FerbCodegenBackend {
    fn locale_resource(&self) -> &'static str {
        "" // ?
    }

    fn name(&self) -> &'static str {
        "franca"
    }

    fn codegen_crate<'tcx>(&self, tcx: TyCtxt<'tcx>) -> Box<dyn Any> {
        let cgus = tcx.collect_and_partition_mono_items(()).codegen_units;
        assert!(cgus.len() == 1, "TODO: multiple cgus");

        Box::new(OngoingCodegen {
            crate_info: CrateInfo::new(tcx, tcx.sess.target.cpu.as_ref().into()),
            cgu_name: cgus[0].name().as_str().into(),
        })
    }

    fn join_codegen(
        &self,
        ongoing_codegen: Box<dyn Any>,
        _sess: &Session,
        outputs: &OutputFilenames,
    ) -> (CodegenResults, FxIndexMap<WorkProductId, WorkProduct>) {
        let worker: Box<OngoingCodegen> = ongoing_codegen.downcast().unwrap();

        let OutFileName::Real(fake_output) = outputs.path(OutputType::Object) else {
            panic!("TODO: OutFileName")
        };
        std::fs::write(&fake_output, fake_object_file()).unwrap();

        let result = CompiledModule {
            name: worker.cgu_name,
            kind: ModuleKind::Regular,
            object: Some(fake_output),
            dwarf_object: None,
            bytecode: None,
            assembly: None,
            llvm_ir: None,
            links_from_incr_cache: vec![],
        };

        let work_products = FxIndexMap::default();
        (
            CodegenResults {
                allocator_module: None,
                crate_info: worker.crate_info,
                modules: vec![result],
            },
            work_products,
        )
    }
}

#[unsafe(no_mangle)]
pub fn __rustc_codegen_backend() -> Box<dyn CodegenBackend> {
    Box::new(FerbCodegenBackend {})
}

fn fake_object_file() -> Vec<u8> {
    use ferb::builder::*;
    let mut m = Module::new();
    
    let (msg, puts) = (m.sym("msg"), m.sym("puts"));
    let libc = m.library("libc");
    m.import(puts, libc);
    m.data(Data {
        id: msg,
        segment: Seg::ConstantData,
        template: Template::Bytes("Hello\0".as_bytes()),
        rel: vec![],
    });
    
    let mut f = Func::new(m.sym("main"), Ret::K(Cls::Kl));
    let (msg, puts, b) = (f.con(msg, 0), f.con(puts, 0), f.blk());
    f.emit(b, O::arg, Cls::Kl, Ref::Null, msg, Ref::Null);
    f.emit(b, O::call, Cls::Kl, Ref::Null, puts, Ref::Null);
    let c = f.con(Id::None, 24);
    f.jump(b, J::retl, c, None, None);
    m.func(f);
    
    ferb::compile_aot(&m.finish())
}
