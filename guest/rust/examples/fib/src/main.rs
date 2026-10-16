//! Fibonacci guest in Rust. Input: 8 bytes little endian `n`.
//! Output: 8 bytes little endian `fib(n) mod 2^64`. Exit code 0, or 1 on
//! short input. This is the Rust counterpart of `guest/examples/fib.c`.

#![no_std]
#![no_main]

use core::panic::PanicInfo;

#[no_mangle]
pub extern "C" fn om_main() -> u64 {
    if om_guest::input_len() < 8 {
        return 1;
    }
    let n = om_guest::read_u64(0);
    let (mut a, mut b) = (0u64, 1u64);
    for _ in 0..n {
        let t = a.wrapping_add(b);
        a = b;
        b = t;
    }
    om_guest::write_u64(a);
    0
}

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    om_guest::halt_panic()
}
