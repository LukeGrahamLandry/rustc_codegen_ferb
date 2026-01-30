#![feature(rustc_private)]
#![feature(box_patterns)]

use std::any::Any;

use rustc_codegen_ssa::{
    CodegenResults, CompiledModule, CrateInfo, ModuleKind, TargetConfig, back::{archive::ArArchiveBuilderBuilder, link::link_binary}, traits::CodegenBackend
};
use rustc_data_structures::fx::FxIndexMap;
use rustc_metadata::EncodedMetadata;
use rustc_middle::{
    dep_graph::{WorkProduct, WorkProductId}, middle::exported_symbols::SymbolExportKind, ty::TyCtxt
};
use rustc_session::{
    Session,
    config::{OutFileName, OutputFilenames, OutputType},
};
use rustc_span::{sym, Symbol};
use rustc_target::spec::{Arch, Os};
use ferb::builder as Ferb;

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

mod emit;

pub struct FerbCodegenBackend {}

pub struct OngoingCodegen {
    crate_info: CrateInfo,
    cgu_name: String,
    m: Ferb::Module,
    need_linker: bool,
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
        let crate_info = CrateInfo::new(tcx, tcx.sess.target.cpu.as_ref().into());
        let need_linker = {
            // TODO: probably too hacky to be worth it since will only help when #![no_std]
            let magic = |it: &(String, SymbolExportKind)| 
                it.0.contains("rust_begin_unwind") || it.0.contains("rust_probestack") || it.0 == "rust_eh_personality" || it.0 == "main";
            let have_imports = crate_info.linked_symbols.iter().any(|it| it.1.iter().any(|it| !magic(it)));
            let outputs = &tcx.output_filenames(()).outputs;
            have_imports || !(outputs.len() == 1 && outputs.contains_key(&OutputType::Exe))
        };
        
        let m = crate::emit::emit(tcx, &cgus[0]);
        Box::new(OngoingCodegen {
            crate_info,
            cgu_name: cgus[0].name().as_str().into(),
            m,
            need_linker,
        })
    }

    fn join_codegen(
        &self,
        ongoing_codegen: Box<dyn Any>,
        sess: &Session,
        outputs: &OutputFilenames,
    ) -> (CodegenResults, FxIndexMap<WorkProductId, WorkProduct>) {
        let worker: Box<OngoingCodegen> = ongoing_codegen.downcast().unwrap();
        let (ty, artifact) = if worker.need_linker { 
            (OutputType::Object, ferb::Artifact::Relocatable)
        } else { 
            (OutputType::Exe, ferb::Artifact::Exe)
        };
        let OutFileName::Real(output_file) = outputs.path(ty) else {
            panic!("TODO: OutFileName")
        };
        
        let (arch, os) = translate_target(sess);
        let logging = &*std::env::var("FRANCA_DASH_d").unwrap_or_else(|_| String::new());
        // TODO: use threaded *CodegenShared from franca/backend/lib.fr instead of building up the whole module first
        let obj = unsafe { ferb::compile_aot(&worker.m.finish(), logging, arch, os, artifact) };
        std::fs::write(&output_file, obj).unwrap();

        let result = CompiledModule {
            name: worker.cgu_name,
            kind: ModuleKind::Regular,
            object: if worker.need_linker { Some(output_file) } else { None },
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
    
    // im clealy not at the point of caring about this 
    // but it fixes warning spam every time rustc runs.
    // "warning: target feature $whatever must be enabled to ensure that the ABI of the current target can be implemented correctly"
    fn target_config(&self, sess: &Session) -> TargetConfig {
        let f = match sess.target.arch {
            Arch::AArch64 => vec![sym::neon],
            Arch::X86_64 => vec![Symbol::intern("x87"), sym::sse2],
            _ => vec![],
        };

        TargetConfig {
            target_features: f.clone(),
            unstable_target_features: f,
            has_reliable_f16: false,
            has_reliable_f16_math: false,
            has_reliable_f128: false,
            has_reliable_f128_math: false,
        }
    }
    
    // for my (tiny) mandel.rs, -Zself-profile says link_binary() is 41ms out of 58 ms.
    // so if just creating an exe and have all the code, can skip the linker. 
    fn link(&self, sess: &Session, codegen_results: CodegenResults, metadata: EncodedMetadata, outputs: &OutputFilenames) {
        let need_linker = codegen_results.modules.iter().any(|it| it.object.is_some());
        if need_linker {
            link_binary(sess, &ArArchiveBuilderBuilder, codegen_results, metadata, outputs, self.name());
        }
    }
}

#[unsafe(no_mangle)]
pub fn __rustc_codegen_backend() -> Box<dyn CodegenBackend> {
    Box::new(FerbCodegenBackend {})
}

fn translate_target(sess: &Session) -> (ferb::Arch, ferb::Os) {
    let arch = match sess.target.arch {
        Arch::AArch64 => ferb::Arch::Arm64,
        Arch::RiscV64 => ferb::Arch::Rv64,
        Arch::Wasm32 => ferb::Arch::Wasm32,
        Arch::Wasm64 => todo!(),
        Arch::X86_64 => ferb::Arch::Amd64,
        _ => todo!(),
    };
    let os = match sess.target.os {
        Os::Linux => ferb::Os::Linux,
        Os::MacOs => ferb::Os::Macos,
        _ => todo!(),
    };
    (arch, os)
}
