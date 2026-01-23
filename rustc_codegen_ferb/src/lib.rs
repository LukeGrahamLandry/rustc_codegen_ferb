#![feature(rustc_private)]

use std::{any::Any, process::Command};

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
        std::fs::write(
            "tempfile.ssa",
            r#"
            data $msg = { b "Hello\0" }
            export function w $main() {
            @start
                call $puts(l $msg)
                ret 24
            }
        "#
            .as_bytes(),
        )
        .unwrap();
        let path = fake_output.as_os_str().to_str().unwrap();
        let status = Command::new("franca")
            .args([
                "backend/meta/qbe_frontend.fr",
                "-c",
                "tempfile.ssa",
                "-o",
                path,
            ])
            .output()
            .expect("run franca");
        assert!(
            status.status.success(),
            "{}",
            String::try_from(status.stderr).unwrap()
        );
        println!("{:?}", fake_output);

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
