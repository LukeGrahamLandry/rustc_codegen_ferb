#![no_std]
#![no_main]
#![allow(internal_features)]
#![feature(lang_items)]
use core::panic::PanicInfo;

#[no_mangle]
pub extern "C" fn main() -> usize {
    const S: *const u8 = "Hello\0".as_ptr();
    #[allow(unused_assignments)]
    let mut s = "nope";
    s = " World\0";
    let five = another(0, Thing { a: 2u64 as usize, b: 3, c: 0f64 });
    let mut n = important_value(30, five).wrapping_add(s.len());
    let s = s.as_ptr();
    let a = match n.wrapping_sub(41) {
        0 => 41,
        1 => 42,
        2 => 40,
        _ => 39,
    };
    let value = 1f64;
    let mut t = Thing { a, b: 42, c: value + 1f64};
    n = unsafe {
        static mut BAR: Thing = Thing { a: 123, b: 0, c: 0.0 };
        BAR.a = n;
        BAR.a
    };
    if n <= t.a {
        unsafe { puts(S); };
    }
    let mut x = 5;
    let xx = &mut x;
    *xx = 4;
    while n >= t.b {
        unsafe { printf("%s %d%.0f\n\0".as_ptr(), s, x, t.c) };
        n = n.wrapping_sub(1);
        t.a = t.a.wrapping_sub(1);
    }
    
    let foo = Some(n);
    let n = match foo {
        Some(n) => n,
        None => 456,
    };
    let foo: Option<usize> = None;
    let n = match foo {
        Some(_) => 123,
        None => n,
    };
    let foo = (0, twice(t.a).1, "");
    let value = n - foo.1;
    voidcall();
    return value;
}

fn voidcall() {}
fn twice<T: Copy>(a: T) -> (T, T) { (a, a) }

fn another(a: usize, b: Thing) -> usize {
    let a = &a;
    let t = Thing { a: *a, b: b.b, c: 0f64 };
    let t = Things { t };
    t.t.a.wrapping_add(t.t.b).wrapping_add(b.a)
}

struct Thing {
    a: usize,
    b: usize,
    c: f64,
}

struct Things {
    t: Thing,
}

fn important_value(a: usize, b: usize) -> usize {
    a.wrapping_add(b)
}

unsafe extern "C" {
    fn puts(s: *const u8) -> i32;
    fn printf(fmt: *const u8, ...) -> i32;
}

#[panic_handler]
fn panic(_: &PanicInfo) -> ! {
    loop {}
}

// the humble `for` loop references this if opt-level=0
#[lang = "eh_personality"]
pub fn rust_eh_personality() -> ! {
    unsafe { puts("rust_eh_personality\0".as_ptr()) }; 
    loop {}
}
