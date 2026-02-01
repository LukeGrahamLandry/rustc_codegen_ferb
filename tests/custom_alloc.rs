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
            I = ((I + a - 1) / a) * a;
            let p = &ARRAY[I];
            I += layout.size();
            assert!(I <= N);
            p as *const u8 as *mut u8
        }
    }
    
    unsafe fn dealloc(&self, _: *mut u8, _: Layout) {}
}

unsafe extern "C" { fn printf(fmt: *const u8, ...) -> i32; }
fn main() {
    // can't compile Box::new() yet so can't test directly 
    // but the runtime allocates before calling main()
    // (can check by putting todo!() in alloc() above)
    unsafe { printf("main() via std::rt::lang_start\n\0".as_ptr()) };
}

// i'm cheating. see "TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO" in emit.rs
