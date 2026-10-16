//! Runtime support for Rust guests on open-magnetar (spec 14).
//!
//! `no_std` plus `alloc`. The entry point `_start` is provided here in
//! assembly: it sets `sp` from the linker symbol `__stack_top`, calls the
//! guest's `om_main`, then halts with `om_main`'s return value as the exit
//! code (`li a7, 0; ecall`, spec 14.4). A guest binary therefore only has
//! to provide:
//!
//! ```ignore
//! #[no_mangle]
//! pub extern "C" fn om_main() -> u64 { /* ... */ 0 }
//!
//! #[panic_handler]
//! fn panic(_: &core::panic::PanicInfo) -> ! { om_guest::halt_panic() }
//! ```
//!
//! The I/O helpers mirror `guest/rt/om.h`: the input region starts with a
//! little endian `u64` byte length followed by the input bytes, and the
//! output region uses the same encoding. Output is append only, which
//! keeps the encoding canonical (spec 14.1).

#![no_std]

extern crate alloc;

use core::alloc::{GlobalAlloc, Layout};
use core::arch::global_asm;
use core::ptr;

global_asm!(
    r#"
    .section .text.init, "ax"
    .globl _start
_start:
    la   sp, __stack_top
    call om_main
    li   a7, 0
    ecall
3:  j    3b
"#
);

extern "C" {
    static __input_base: u8;
    static __output_base: u8;
    static mut __heap_start: u8;
    static __heap_end: u8;
}

fn input_base() -> *const u8 {
    ptr::addr_of!(__input_base)
}

fn output_base() -> *mut u8 {
    ptr::addr_of!(__output_base) as *mut u8
}

/// Byte length of the public input.
pub fn input_len() -> u64 {
    unsafe { ptr::read_volatile(input_base() as *const u64) }
}

/// The public input bytes.
pub fn input() -> &'static [u8] {
    let len = input_len() as usize;
    unsafe { core::slice::from_raw_parts(input_base().add(8), len) }
}

/// Read a little endian `u64` at byte offset `off` in the input.
pub fn read_u64(off: usize) -> u64 {
    let b = &input()[off..off + 8];
    u64::from_le_bytes(b.try_into().unwrap())
}

/// Append bytes to the public output.
pub fn write(bytes: &[u8]) {
    unsafe {
        let out = output_base();
        let len = ptr::read_volatile(out as *const u64) as usize;
        ptr::copy_nonoverlapping(bytes.as_ptr(), out.add(8 + len), bytes.len());
        ptr::write_volatile(out as *mut u64, (len + bytes.len()) as u64);
    }
}

/// Append one little endian `u64` to the public output.
pub fn write_u64(v: u64) {
    write(&v.to_le_bytes());
}

/// Panic handler body for guests: halt with exit code 1.
pub fn halt_panic() -> ! {
    unsafe {
        core::arch::asm!("li a0, 1", "li a7, 0", "ecall", options(noreturn));
    }
}

// Bump allocator over the linker heap region. It never frees, as spec 14
// requires. The target is single threaded with no atomics, so a plain
// static cursor is sound here.
struct BumpAlloc;

static mut HEAP_CURSOR: usize = 0;

unsafe impl GlobalAlloc for BumpAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let start = ptr::addr_of!(__heap_start) as usize;
        let end = ptr::addr_of!(__heap_end) as usize;
        if HEAP_CURSOR == 0 {
            HEAP_CURSOR = start;
        }
        let align_offset = HEAP_CURSOR % layout.align();
        if align_offset != 0 {
            HEAP_CURSOR += layout.align() - align_offset;
        }
        if HEAP_CURSOR + layout.size() > end {
            return ptr::null_mut();
        }
        let p = HEAP_CURSOR as *mut u8;
        HEAP_CURSOR += layout.size();
        p
    }

    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {}
}

#[global_allocator]
static ALLOCATOR: BumpAlloc = BumpAlloc;
