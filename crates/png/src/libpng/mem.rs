//! Memory handed to the caller: `png_malloc` and friends, through the
//! caller's allocator when `png_create_read_struct_2` or `png_set_mem_fn`
//! gave one. Our own buffers are Rust allocations.
use super::err::*;
use super::*;

unsafe extern "C" {
    fn malloc(n: usize) -> *mut c_void;
    fn free(p: *mut c_void);
}

/// Allocates through the caller's function, or `malloc`. Null on failure.
pub unsafe fn alloc(p: *mut Png, n: usize) -> *mut c_void {
    if n == 0 {
        return core::ptr::null_mut();
    }
    if !p.is_null() {
        if let Some(f) = (*p).malloc_fn {
            return f(p, n);
        }
    }
    malloc(n)
}

pub unsafe fn dealloc(p: *mut Png, ptr: *mut c_void) {
    if ptr.is_null() {
        return;
    }
    if !p.is_null() {
        if let Some(f) = (*p).free_fn {
            return f(p, ptr);
        }
    }
    free(ptr)
}

api! {
    pub unsafe extern "C" fn png_malloc(p: png_structp, size: usize) -> png_voidp {
        if p.is_null() {
            return core::ptr::null_mut();
        }
        let r = alloc(p, size);
        if r.is_null() {
            fail(p, "Out of memory");
            raise(p)
        }
        r
    }

    pub unsafe extern "C" fn png_calloc(p: png_structp, size: usize) -> png_voidp {
        let r = png_malloc(p, size);
        if !r.is_null() {
            core::ptr::write_bytes(r as *mut u8, 0, size);
        }
        r
    }

    pub unsafe extern "C" fn png_malloc_warn(p: png_structp, size: usize) -> png_voidp {
        if p.is_null() {
            return core::ptr::null_mut();
        }
        let r = alloc(p, size);
        if r.is_null() {
            warn(p, "Out of memory");
        }
        r
    }

    pub unsafe extern "C" fn png_malloc_default(p: png_structp, size: usize) -> png_voidp {
        if p.is_null() || size == 0 {
            return core::ptr::null_mut();
        }
        let r = malloc(size);
        if r.is_null() {
            fail(p, "Out of Memory");
            raise(p)
        }
        r
    }

    pub unsafe extern "C" fn png_free(p: png_structp, ptr: png_voidp) {
        if p.is_null() {
            return;
        }
        dealloc(p, ptr)
    }

    pub unsafe extern "C" fn png_free_default(p: png_structp, ptr: png_voidp) {
        if p.is_null() || ptr.is_null() {
            return;
        }
        free(ptr)
    }

    pub unsafe extern "C" fn png_set_mem_fn(p: png_structp, mem_ptr: png_voidp, malloc_fn: MallocFn, free_fn: FreeFn) {
        if p.is_null() {
            return;
        }
        (*p).mem_ptr = mem_ptr;
        (*p).malloc_fn = malloc_fn;
        (*p).free_fn = free_fn;
    }

    pub unsafe extern "C" fn png_get_mem_ptr(p: png_structp) -> png_voidp {
        if p.is_null() { core::ptr::null_mut() } else { (*p).mem_ptr }
    }
}
