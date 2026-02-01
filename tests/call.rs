#![no_std] #![no_main]
#![allow(internal_features)] #![feature(lang_items)]

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let x = 3;
    let f = |a, b| x - a - b;
    let one = (|a| a)(1);
    let two = (|| 2)();
    if f(one, two) != 0 { return 1 };
    
    let foo = |a: i32| a + x;
    if call_dyn(&foo, -3) != 0 { return 2 };
    
    0
}

fn call_dyn(f: &dyn Fn(i32) -> i32, a: i32) -> i32 { f(a) }

#[panic_handler] fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }
#[lang = "eh_personality"] pub fn rust_eh_personality() -> ! { loop {} }
