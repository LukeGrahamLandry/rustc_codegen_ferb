#![no_std]
#![no_main]
use core::panic::PanicInfo;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    return 42;
}

#[panic_handler]
fn panic(_: &PanicInfo) -> ! {
    loop {}
}
