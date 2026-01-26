#![no_std]
#![no_main]
use core::panic::PanicInfo;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    const S: *const u8 = "Hello\0".as_ptr();
    unsafe { puts(S); };
    return 42;
}

unsafe extern "C" {
    fn puts(s: *const u8) -> i32;
}

#[panic_handler]
fn panic(_: &PanicInfo) -> ! {
    loop {}
}
