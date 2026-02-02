#![no_std] #![no_main]
#![allow(internal_features)] #![feature(lang_items)]

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let x = core::hint::black_box(3);  // intrinsic!
    
    let f = |a, b| x - a - b;
    let one = (|a| a)(1);
    let two = (|| 2)();
    if f(one, two) != 0 { return 1 };
    
    let foo = |a: i32| a + x;
    if call_dyn(&foo, -3) != 0 { return 2 };
    
    // same shape as std::rt::lang_start
    let bar: fn() -> i32 = bar;
    if call_dyn_unit2(bar) != 123 { return 3 };
    
    0
}

fn call_dyn(f: &dyn Fn(i32) -> i32, a: i32) -> i32 { f(a) }

fn bar() -> i32 { 123 }
fn call_once<F, T>(f: F) -> T where F: FnOnce() -> T { f() }
fn call_dyn_unit(f: &dyn Fn() -> i32) -> i32 { f() }
fn call_dyn_unit2(f: fn() -> i32) -> i32 { 
    call_dyn_unit(&move || call_once(f)) 
}

#[panic_handler] fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }
#[lang = "eh_personality"] pub fn rust_eh_personality() -> ! { loop {} }
