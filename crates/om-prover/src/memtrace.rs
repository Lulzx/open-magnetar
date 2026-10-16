//! Opt-in prover phase trace: with `OM_TRACE=1` in the environment,
//! [`mark`] prints the elapsed time and the process peak resident set
//! size after each prover phase to stderr. A binary that installs
//! [`CountingAlloc`] as its global allocator also gets the live heap
//! and the heap peak within each phase. Diagnostics only; it never
//! touches proof bytes.

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::OnceLock;
use std::sync::atomic::{AtomicBool, AtomicIsize, Ordering};
use std::time::Instant;

// Signed: frees of blocks allocated before counting began may take
// the count slightly below zero.
static LIVE: AtomicIsize = AtomicIsize::new(0);
static PEAK: AtomicIsize = AtomicIsize::new(0);
static COUNTING: AtomicBool = AtomicBool::new(false);

/// The system allocator with live-byte and peak accounting, for
/// [`mark`]. Install with `#[global_allocator]` in a binary.
pub struct CountingAlloc;

impl CountingAlloc {
    /// Start counting if `OM_TRACE` is set (call first thing in
    /// `main`); otherwise the allocator only forwards.
    pub fn enable_from_env() {
        if enabled().is_some() {
            COUNTING.store(true, Ordering::Relaxed);
        }
    }

    fn add(n: usize) {
        if COUNTING.load(Ordering::Relaxed) {
            let n = n as isize;
            let live = LIVE.fetch_add(n, Ordering::Relaxed) + n;
            PEAK.fetch_max(live, Ordering::Relaxed);
        }
    }

    fn sub(n: usize) {
        if COUNTING.load(Ordering::Relaxed) {
            LIVE.fetch_sub(n as isize, Ordering::Relaxed);
        }
    }
}

// SAFETY: every call forwards to `System` unchanged; only counters
// are updated on the side.
unsafe impl GlobalAlloc for CountingAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // SAFETY: forwarded with the caller's layout.
        let p = unsafe { System.alloc(layout) };
        if !p.is_null() {
            Self::add(layout.size());
        }
        p
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        // SAFETY: forwarded with the caller's layout.
        let p = unsafe { System.alloc_zeroed(layout) };
        if !p.is_null() {
            Self::add(layout.size());
        }
        p
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // SAFETY: `ptr` was allocated by `System` with `layout`.
        unsafe { System.dealloc(ptr, layout) };
        Self::sub(layout.size());
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        // SAFETY: forwarded unchanged.
        let p = unsafe { System.realloc(ptr, layout, new_size) };
        if !p.is_null() {
            Self::sub(layout.size());
            Self::add(new_size);
        }
        p
    }
}

#[repr(C)]
struct Rusage {
    utime: [i64; 2],
    stime: [i64; 2],
    maxrss: i64,
    rest: [i64; 13],
}

unsafe extern "C" {
    fn getrusage(who: i32, usage: *mut Rusage) -> i32;
}

fn enabled() -> Option<Instant> {
    static START: OnceLock<Option<Instant>> = OnceLock::new();
    *START.get_or_init(|| std::env::var_os("OM_TRACE").map(|_| Instant::now()))
}

/// Peak resident set size of this process so far, in MiB.
fn peak_mib() -> f64 {
    let mut u = Rusage {
        utime: [0; 2],
        stime: [0; 2],
        maxrss: 0,
        rest: [0; 13],
    };
    // SAFETY: `getrusage(RUSAGE_SELF, &mut u)` writes one `struct rusage`.
    let ok = unsafe { getrusage(0, &mut u) } == 0;
    if !ok {
        return 0.0;
    }
    // macOS reports bytes, Linux kilobytes.
    let bytes = if cfg!(target_os = "macos") {
        u.maxrss
    } else {
        u.maxrss * 1024
    };
    bytes as f64 / (1024.0 * 1024.0)
}

/// Print one phase line if tracing is enabled.
pub fn mark(phase: &str) {
    if let Some(start) = enabled() {
        const MIB: f64 = 1024.0 * 1024.0;
        let heap = if COUNTING.load(Ordering::Relaxed) {
            let live = LIVE.load(Ordering::Relaxed).max(0);
            let peak = PEAK.swap(live, Ordering::Relaxed).max(0);
            format!(
                "  heap live {:>9.1} MiB, phase peak {:>9.1} MiB",
                live as f64 / MIB,
                peak as f64 / MIB
            )
        } else {
            String::new()
        };
        eprintln!(
            "[om] {:>8.2}s  rss peak {:>9.1} MiB{heap}  {phase}",
            start.elapsed().as_secs_f64(),
            peak_mib()
        );
    }
}
