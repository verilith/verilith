//! The write functions that `png.h` declares even in a read-only build.
//! Writing is not here: `png_create_write_struct` returns NULL, as libpng's
//! does when it cannot make the structure, and the others do nothing.
use super::*;

api! {
    pub unsafe extern "C" fn png_create_write_struct(ver: *const c_char, error_ptr: png_voidp, error_fn: ErrorFn, warn_fn: ErrorFn) -> png_structp {
        let _ = (ver, error_ptr, error_fn, warn_fn);
        core::ptr::null_mut()
    }

    pub unsafe extern "C" fn png_create_write_struct_2(ver: *const c_char, error_ptr: png_voidp, error_fn: ErrorFn, warn_fn: ErrorFn,
        mem_ptr: png_voidp, malloc_fn: MallocFn, free_fn: FreeFn) -> png_structp {
        let _ = (ver, error_ptr, error_fn, warn_fn, mem_ptr, malloc_fn, free_fn);
        core::ptr::null_mut()
    }

    pub unsafe extern "C" fn png_destroy_write_struct(pp: *mut png_structp, info_pp: *mut png_infop) {
        let _ = (pp, info_pp);
    }

    pub unsafe extern "C" fn png_set_write_fn(p: png_structp, io_ptr: png_voidp, write_fn: RwFn, flush_fn: FlushFn) {
        let _ = (p, io_ptr, write_fn, flush_fn);
    }

    pub unsafe extern "C" fn png_set_write_status_fn(p: png_structp, f: WriteStatusFn) {
        let _ = (p, f);
    }

    pub unsafe extern "C" fn png_write_sig(p: png_structp) {
        let _ = p;
    }

    pub unsafe extern "C" fn png_write_chunk(p: png_structp, name: *const u8, data: *const u8, len: usize) {
        let _ = (p, name, data, len);
    }

    pub unsafe extern "C" fn png_write_chunk_start(p: png_structp, name: *const u8, len: png_uint_32) {
        let _ = (p, name, len);
    }

    pub unsafe extern "C" fn png_write_chunk_data(p: png_structp, data: *const u8, len: usize) {
        let _ = (p, data, len);
    }

    pub unsafe extern "C" fn png_write_chunk_end(p: png_structp) {
        let _ = p;
    }

    pub unsafe extern "C" fn png_write_info_before_PLTE(p: png_structp, info: png_infop) {
        let _ = (p, info);
    }

    pub unsafe extern "C" fn png_write_info(p: png_structp, info: png_infop) {
        let _ = (p, info);
    }

    pub unsafe extern "C" fn png_write_row(p: png_structp, row: *const u8) {
        let _ = (p, row);
    }

    pub unsafe extern "C" fn png_write_rows(p: png_structp, rows: *mut png_bytep, n: png_uint_32) {
        let _ = (p, rows, n);
    }

    pub unsafe extern "C" fn png_write_image(p: png_structp, image: *mut png_bytep) {
        let _ = (p, image);
    }

    pub unsafe extern "C" fn png_write_end(p: png_structp, info: png_infop) {
        let _ = (p, info);
    }
}
