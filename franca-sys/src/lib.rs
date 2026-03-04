use std::marker::PhantomData;

pub mod ir;

#[repr(C)]
#[derive(Copy, Clone)]
pub struct Globals(*mut ());

#[repr(C)]
pub struct Slice<'a> {
    pub ptr: *const u8,
    pub len: u64,
    pub _0: PhantomData<&'a ()>,
}

#[repr(C)]
pub struct CompileCmd<'a> {
    // .frc ir bytes or a string of qbe .ssa text ir. 
    pub frc: Slice<'a>,
    // if kind != Jit this will return the compiled artifact bytes.
    pub out: Slice<'a>,  // lie!
    // name of the entry point function. if kind == Jit, its address will be returned in `p`
    pub name: Slice<'a>,
    // string of characters representing which opt passes to log to stderr (similar to qbe's -d argument)
    pub logging: Slice<'a>,    
    pub p: u64,
    pub m: u64,
    pub arch: Arch,
    pub os: Os,
    pub kind: Artifact,
    pub no_libc: bool,
    pub no_interp: bool,
    // returns status. if false, `out` contains the error message.
    pub ok: bool,
}

unsafe extern "C" {
    pub fn init_globals() -> Globals;
    pub fn compile_one(fr: Globals, arg: *mut CompileCmd);
    pub fn drop_module(fr: Globals, arg: *mut CompileCmd);
}

#[repr(i64)]
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Arch {
    Arm64,
    Amd64,
    Rv64,
    Wasm32,
}

#[repr(i64)]
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Os {
    Macos,
    Linux,
}

#[repr(i64)]
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Artifact {
    CachedLate,
    Jit,
    Exe,
    Relocatable,
    Dynamic,
    CachedEarly,
}

impl<'a> From<&'a [u8]> for Slice<'a> {
    fn from(it: &'a [u8]) -> Slice<'a>  {
        Slice { ptr: it.as_ptr(), len: it.len() as u64, _0: PhantomData }
    }
}

impl<'a> Slice<'a> {
    pub fn bytes(&self) -> &'a [u8] {
        if self.len == 0 {
            return &[]; // i don't require nonnull pointer but rust does
        }
        unsafe { std::slice::from_raw_parts(self.ptr, self.len as usize) }
    }
    
    pub unsafe fn bytes_mut(&self) -> &'a mut [u8] {
        if self.len == 0 {
            return &mut [];  // i don't require nonnull pointer but rust does
        }
        unsafe { std::slice::from_raw_parts_mut(self.ptr as *mut u8, self.len as usize) }
    }
}
