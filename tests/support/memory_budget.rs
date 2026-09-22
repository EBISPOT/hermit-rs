//! Bound the live allocations of an isolated test worker. Exceeding the budget
//! aborts the worker, which the parent reports as a failed test. It cannot leave
//! a detached reasoning task consuming memory after a timeout.
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};

struct BudgetAllocator;
static LIVE: AtomicUsize = AtomicUsize::new(0);
const LIMIT: usize = 512 * 1024 * 1024;

fn reserve(bytes: usize) {
    if LIVE
        .fetch_add(bytes, Ordering::Relaxed)
        .saturating_add(bytes)
        > LIMIT
    {
        // Avoid allocating while reporting an allocation failure.
        eprintln!("test worker exceeded its 512 MiB allocation budget");
        std::process::abort();
    }
}

unsafe impl GlobalAlloc for BudgetAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        reserve(layout.size());
        let ptr = unsafe { System.alloc(layout) };
        if ptr.is_null() {
            LIVE.fetch_sub(layout.size(), Ordering::Relaxed);
        }
        ptr
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        reserve(layout.size());
        let ptr = unsafe { System.alloc_zeroed(layout) };
        if ptr.is_null() {
            LIVE.fetch_sub(layout.size(), Ordering::Relaxed);
        }
        ptr
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe {
            System.dealloc(ptr, layout);
        }
        LIVE.fetch_sub(layout.size(), Ordering::Relaxed);
    }
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        let extra = size.saturating_sub(layout.size());
        reserve(extra);
        let new = unsafe { System.realloc(ptr, layout, size) };
        if new.is_null() {
            LIVE.fetch_sub(extra, Ordering::Relaxed);
        } else if size < layout.size() {
            LIVE.fetch_sub(layout.size() - size, Ordering::Relaxed);
        }
        new
    }
}

#[global_allocator]
static ALLOCATOR: BudgetAllocator = BudgetAllocator;
