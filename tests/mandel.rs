#![no_std] #![no_main]
#![allow(internal_features)] #![feature(lang_items)]

fn mandelbrot(c: Pos, mut z: Pos, steps: i64) -> i64 {
    let mut i = 0;
    let mut z_sq = z.mul(z);
    while i < steps && z_sq.x + z_sq.y < 4.0 {
        z.y = z.x * 2.0 * z.y;
        z.x = z_sq.x - z_sq.y;
        z = z.add(c);
        z_sq = z.mul(z);
        i = i + 1;
    };
    i
}

#[no_mangle]
pub extern "C" fn main() -> usize {
    let (max_steps, x) = (45, 0.0 - 1.5);
    let mut pos: Pos = Pos { x, y: 0.0 - 1.0 };
    for _ in 0..35 {
        for _ in 0..70 {
            let steps = mandelbrot(pos, Pos { x: 0.0, y: 0.0 }, max_steps);
            if steps == max_steps {
                unsafe { printf("@\0".as_ptr()) };
            } else {
                unsafe { printf(" \0".as_ptr()) };
            }
            pos.x = pos.x + 0.03;
        }
        unsafe { printf("|\n\0".as_ptr()) };
        pos.x = x;
        pos.y = pos.y + 0.06;
    }
    0
}

#[derive(Clone, Copy)]
struct Pos { x: f64, y: f64, }

impl Pos {
    fn add(self, b: Pos) -> Pos {
        Pos { x: self.x + b.x, y: self.y + b.y, }
    }
    fn mul(self, b: Pos) -> Pos {
        Pos { x: self.x * b.x, y: self.y * b.y, }
    }
}

unsafe extern "C" { fn printf(fmt: *const u8, ...) -> i32; }
#[panic_handler] fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }
#[lang = "eh_personality"] pub fn rust_eh_personality() -> ! { loop {} }
