#![no_std] #![no_main]
#![allow(internal_features)] #![feature(lang_items)]

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let x = 3;
    let f = |a, b| x - a - b;
    let one = (|a| a)(1);
    let two = (|| 2)();
    f(one, two)
}

#[panic_handler] fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }
#[lang = "eh_personality"] pub fn rust_eh_personality() -> ! { loop {} }
