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
    pub frc: Slice<'a>,
    pub out: Slice<'a>,  // lie!
    pub name: Slice<'a>,
    pub p: u64,
    pub m: u64,
    pub jit: u8,
}

unsafe extern "C" {
    pub fn init_globals() -> Globals;
    pub fn compile_one(fr: Globals, arg: *mut CompileCmd);
    pub fn drop_module(fr: Globals, arg: *mut CompileCmd);
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
