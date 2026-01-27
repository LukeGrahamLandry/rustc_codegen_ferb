#![no_std]
#![no_main]
use core::panic::PanicInfo;

#[no_mangle]
pub extern "C" fn main() -> usize {
    const S: *const u8 = "Hello\0".as_ptr();
    #[allow(unused_assignments)]
    let mut s = "nope";
    s = " World\0";
    let mut n = important_value(30, 5).wrapping_add(s.len());
    let s = s.as_ptr();
    let a = match n.wrapping_sub(41) {
        0 => 41,
        1 => 42,
        2 => 40,
        _ => 39,
    };
    if n <= a {
        unsafe { puts(S); };
    }
    while n >= 42 {
        unsafe { puts(s); };
        n = n.wrapping_sub(1);
    }
    return n.wrapping_sub(41);
}

fn important_value(a: usize, b: usize) -> usize {
    a.wrapping_add(b)
}

unsafe extern "C" {
    fn puts(s: *const u8) -> i32;
}

#[panic_handler]
fn panic(_: &PanicInfo) -> ! {
    loop {}
}
