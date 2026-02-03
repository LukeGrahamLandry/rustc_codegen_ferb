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
    
    track_caller();
    
    let mut x = 1;
    { let _ = Defer(Some(|| x = 0)); };
    { core::mem::forget(Defer(Some(|| x = 2))); };
    x
}

fn call_dyn(f: &dyn Fn(i32) -> i32, a: i32) -> i32 { f(a) }

fn bar() -> i32 { 123 }
fn call_once<F, T>(f: F) -> T where F: FnOnce() -> T { f() }
fn call_dyn_unit(f: &dyn Fn() -> i32) -> i32 { f() }
fn call_dyn_unit2(f: fn() -> i32) -> i32 { 
    call_dyn_unit(&move || call_once(f)) 
}

struct Defer<F: FnOnce()>(Option<F>);
impl<F: FnOnce()> Drop for Defer<F> {
    fn drop(&mut self) {
        self.0.take().unwrap()();
    }
}

fn track_caller() {
    use core::panic::Location;
    #[track_caller] fn track_yes() -> &'static Location<'static> { Location::caller() }
    fn track_no() -> &'static Location<'static> { Location::caller() }
    unsafe extern "C" { fn printf(fmt: *const u8, ...) -> i32; }
    
    let loc = &[track_no(), track_yes(), Location::caller()];
    for loc in loc {
        // TODO: should be loc.file_as_c_str() but if i do that llvm and i disagree unless i reorder so %s is last
        //       but llvm is the one that changes. so i guess i'm "wrong" to pass single field struct as a scalar to vararg but that happens to behave sanely.
        //       file.as_ptr happens to work because it stores it with the extra zero rather than reallocating. 
        //       correct thing is file_as_c_str.as_ptr... but i miscompile that. TODO!
        unsafe { printf("%s:%d:%d\n\0".as_ptr(), loc.file().as_ptr(), loc.line(), loc.column()) };
    }
}

#[panic_handler] fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }
#[lang = "eh_personality"] pub fn rust_eh_personality() -> ! { loop {} }
