#![no_std]
#![no_main]

#[no_mangle]
pub extern "C" fn main() -> usize {
    let mut a = Foo { a: 0, };
    let i = foo(&mut a);
    return i;
}

struct Foo {
    a: usize,
}

fn foo(a: &mut Foo) -> usize {
    bar(a)
}

// TODO: this doesn't work without mut
//       because the reborrow to make an im makes it think it needs stack slot.
fn bar(a: &mut Foo) -> usize {
    a.a
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

