#![no_std]
#![no_main]
use core::panic::PanicInfo;

#[no_mangle]
pub extern "C" fn main() -> usize {
    const S: *const u8 = "Hello\0".as_ptr();
    #[allow(unused_assignments)]
    let mut s = "nope";
    s = " World\0";
    let n = 35_usize.wrapping_add(s.len());
    let s = s.as_ptr();
    unsafe { puts(S); };
    unsafe { puts(s); };
    return n;
}

unsafe extern "C" {
    fn puts(s: *const u8) -> i32;
}

#[panic_handler]
fn panic(_: &PanicInfo) -> ! {
    loop {}
}
