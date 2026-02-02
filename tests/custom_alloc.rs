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
    
    let x = Box::new(123);
    if *x != 123 { panic!() };
}

// i'm cheating. see "TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO" in emit.rs
