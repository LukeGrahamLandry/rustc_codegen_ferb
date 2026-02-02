#![no_std] #![no_main]
#![allow(internal_features)] #![feature(lang_items)]
use core::num::NonZeroU64;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let vv = [1, 0, 2];
    let v = &vv[..];
    let vv = &vv[0..2];
    if (v[1] != 0 || vv[1] != 0) as i32 != 0 { return 1 };
    
    let x: Option<NonZeroU64> = NonZeroU64::new(123);
    match x {  // niche
        Some(x) if x.get() == 123 => (),
        _ => return 2,
    };
    let x: Option<NonZeroU64> = None;
    if !x.is_none() { return 3 };
    
    enum Foo { _A, _B } struct Bar { _a: usize, _b: Foo }  // same shape as core::alloc::Layout
    let x: Option<(usize, Bar)> = None;
    if !x.is_none() { return 4 };
    
    0
}

#[panic_handler] fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }
#[lang = "eh_personality"] pub fn rust_eh_personality() -> ! { loop {} }
