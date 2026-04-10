use std::alloc::{Layout, GlobalAlloc};

#[global_allocator]
static ALLOCATOR: BssAllocator = BssAllocator();
struct BssAllocator();
unsafe impl Sync for BssAllocator {}
unsafe impl GlobalAlloc for BssAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 { 
        unsafe {
            const N: usize = 1 << 16;
            static mut ARRAY: [u8; N] = [0; N];
            static mut I: usize = 0;
            let a = layout.align();
            let base = &ARRAY[I] as *const u8 as usize;
            let p = ((base + I + a - 1) / a) * a;
            I = p + layout.size() - base;
            assert!(I <= N);
            p as *mut u8
        }
    }
    
    unsafe fn dealloc(&self, _: *mut u8, _: Layout) {}
}

unsafe extern "C" { fn printf(fmt: *const u8, ...) -> i32; }
fn main() {
    unsafe { printf("main() via std::rt::lang_start\n\0".as_ptr()) };
    
    let mut n = 0;
    let mut check = |cond: bool| {
        if !cond { unsafe { printf("[%d] failed\n\0".as_ptr(), n) }; };
        n += 1;
    };
    
    let x = Box::new(123);
    check(*x == 123);
    
    const E: usize = 0x0065656565656565;
    let mut x = vec![E];
    let v = &x[0];
    unsafe { printf("x(*v) = %lx; s(v) = %s;\n\0".as_ptr(), *v, v) };
    x.push(0);
    check(x[0] == E && x.len() == 2 && x.capacity() > 1);
    
    println!("Hello World! {}", n);
    
    // on x86_64 :SplatWidePointer makes an abi difference (and would break without when using precompiled standard library)
    #[derive(Debug)] struct Foo { _a: i64 }
    println!("{:?}", Foo { _a: 123 });
}
