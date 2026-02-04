THIS IS UNFINISHED  
this is a codegen backend for rustc using [@/franca/backend](https://git.sr.ht/~lukegrahamlandry/franca/tree/main/item/backend) instead of llvm.  
see the `tests` folder for programs it can compile so far (you will not be impressed).  

Supported Targets: linux/macos aarch64/x86_64/riscv64.  
As a very rough complexity estimate `llvm : cranelift :: cranelift : ferb`.  

[![](https://builds.sr.ht/~lukegrahamlandry/rustc_codegen_ferb/commits/main/.build.yml.svg)](https://builds.sr.ht/~lukegrahamlandry/rustc_codegen_ferb/commits/main/.build.yml)

## NOT YET IMPLEMENTED

- i128/u128, f16/f128
- thread locals
- unwinding, debug info
- inline/global assembly
- intrinsics: `std::{simd, arch}::*;`
- tail calls
- checked arithmetic

there's lots of other stuff that is unfinished but doesn't require backend improvements to fix. 

## thank you for information

- https://github.com/rust-lang/rust (rustc_codegen_cranelift, rustc_codegen_ssa, rustc_codegen_llvm)
- https://rustc-dev-guide.rust-lang.org/part-5-intro.html
