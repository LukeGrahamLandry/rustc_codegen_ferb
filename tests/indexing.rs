#![no_std] #![no_main]
#![allow(internal_features)] #![feature(lang_items)]

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let vv = [1, 0, 2];
    let v = &vv[..];
    let vv = &vv[0..2];
    return (v[1] != 0 || vv[1] != 0) as i32;
}

#[panic_handler] fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }
#[lang = "eh_personality"] pub fn rust_eh_personality() -> ! { loop {} }
