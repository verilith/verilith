//! Errors and warnings: libpng's `png_error` family, the caller's error
//! functions and `longjmp`.
use super::*;
use std::io::Write;

/// The length of the message buffer in `Png` (libpng's
/// `PNG_MAX_ERROR_TEXT` is 196, plus room for a chunk name).
pub const MSG_LEN: usize = 256;

/// An error whose message is in `Png::msg`. It is `Copy`, so a `Result`
/// holding it owns nothing and a `longjmp` over it is sound.
#[derive(Clone, Copy, Debug)]
pub struct E;

pub type R<T> = Result<T, E>;

// `Png::flags` bits.
pub const F_BENIGN_WARN: u32 = 1 << 0;
pub const F_APP_WARNINGS_WARN: u32 = 1 << 1;
pub const F_APP_ERRORS_WARN: u32 = 1 << 2;
pub const F_FILLER_AFTER: u32 = 1 << 3;
pub const F_ROW_INIT: u32 = 1 << 4;
pub const F_DETECT_UNINIT: u32 = 1 << 5;

/// Copies `parts` into `buf` as one NUL-terminated string.
fn compose(buf: &mut [u8; MSG_LEN], parts: &[&[u8]]) {
    let mut n = 0;
    for p in parts {
        for &b in p.iter() {
            if b == 0 || n + 1 >= MSG_LEN {
                break;
            }
            buf[n] = b;
            n += 1;
        }
    }
    buf[n] = 0;
}

/// The chunk name as libpng prints it (`png_format_buffer`): letters as
/// they are, other bytes as `[hh]`.
fn chunk_label(name: u32, out: &mut [u8; 16]) -> usize {
    const HEX: &[u8; 16] = b"0123456789ABCDEF";
    let mut n = 0;
    for c in name.to_be_bytes() {
        if c.is_ascii_alphabetic() {
            out[n] = c;
            n += 1;
        } else {
            out[n] = b'[';
            out[n + 1] = HEX[(c >> 4) as usize];
            out[n + 2] = HEX[(c & 15) as usize];
            out[n + 3] = b']';
            n += 4;
        }
    }
    n
}

unsafe fn c_bytes<'a>(s: *const c_char) -> &'a [u8] {
    if s.is_null() {
        b""
    } else {
        core::slice::from_raw_parts(s as *const u8, cstr_len(s))
    }
}

/// Sets the message and returns the error.
pub unsafe fn fail(p: *mut Png, msg: &str) -> E {
    if !p.is_null() {
        compose(&mut (*p).msg, &[msg.as_bytes()]);
    }
    E
}

/// Sets the message, prefixed with the current chunk's name.
pub unsafe fn chunk_fail(p: *mut Png, msg: &str) -> E {
    if !p.is_null() {
        let mut l = [0u8; 16];
        let n = chunk_label((*p).chunk_name, &mut l);
        compose(&mut (*p).msg, &[&l[..n], b": ", msg.as_bytes()]);
    }
    E
}

/// `png_error` with the message in `Png::msg`.
pub unsafe fn raise(p: *mut Png) -> ! {
    let m = (*p).msg.as_ptr() as *const c_char;
    error_impl(p, m)
}

/// `png_error`: the caller's error function, then the default one, which
/// prints the message and `longjmp`s.
pub unsafe fn error_impl(p: *mut Png, msg: *const c_char) -> ! {
    if !p.is_null() {
        if let Some(f) = (*p).error_fn {
            f(p, msg);
        }
    }
    {
        let mut e = std::io::stderr().lock();
        let _ = e.write_all(b"libpng error: ");
        let _ = e.write_all(c_bytes(msg));
        let _ = e.write_all(b"\n");
    }
    longjmp(p, 1)
}

/// `png_longjmp`.
pub unsafe fn longjmp(p: *mut Png, val: c_int) -> ! {
    if !p.is_null() {
        if let Some(f) = (*p).longjmp_fn {
            if let Some(b) = (*p).jmp_buf.as_mut() {
                f(b.as_mut_ptr() as *mut c_void, val);
            }
        }
    }
    std::process::abort()
}

/// `png_warning`.
pub unsafe fn warning_impl(p: *mut Png, msg: *const c_char) {
    if !p.is_null() {
        if let Some(f) = (*p).warning_fn {
            f(p, msg);
            return;
        }
    }
    let mut e = std::io::stderr().lock();
    let _ = e.write_all(b"libpng warning: ");
    let _ = e.write_all(c_bytes(msg));
    let _ = e.write_all(b"\n");
}

pub unsafe fn warn(p: *mut Png, msg: &str) {
    let mut b = [0u8; MSG_LEN];
    compose(&mut b, &[msg.as_bytes()]);
    warning_impl(p, b.as_ptr() as *const c_char);
}

pub unsafe fn chunk_warn(p: *mut Png, msg: &str) {
    let mut l = [0u8; 16];
    let n = chunk_label((*p).chunk_name, &mut l);
    let mut b = [0u8; MSG_LEN];
    compose(&mut b, &[&l[..n], b": ", msg.as_bytes()]);
    warning_impl(p, b.as_ptr() as *const c_char);
}

/// `png_benign_error`: a warning (the default when reading), or an error.
pub unsafe fn benign(p: *mut Png, msg: &str) -> R<()> {
    let chunk = (*p).chunk_name != 0;
    if (*p).flags & F_BENIGN_WARN != 0 {
        if chunk { chunk_warn(p, msg) } else { warn(p, msg) }
        Ok(())
    } else if chunk {
        Err(chunk_fail(p, msg))
    } else {
        Err(fail(p, msg))
    }
}

/// `png_chunk_benign_error`.
pub unsafe fn chunk_benign(p: *mut Png, msg: &str) -> R<()> {
    if (*p).flags & F_BENIGN_WARN != 0 {
        chunk_warn(p, msg);
        Ok(())
    } else {
        Err(chunk_fail(p, msg))
    }
}

/// `png_app_error`.
pub unsafe fn app_error(p: *mut Png, msg: &str) -> R<()> {
    if (*p).flags & F_APP_ERRORS_WARN != 0 {
        warn(p, msg);
        Ok(())
    } else {
        Err(fail(p, msg))
    }
}

/// `png_app_warning`.
pub unsafe fn app_warning(p: *mut Png, msg: &str) -> R<()> {
    if (*p).flags & F_APP_WARNINGS_WARN != 0 {
        warn(p, msg);
        Ok(())
    } else {
        Err(fail(p, msg))
    }
}

/// Runs an exported function's work and raises its error, if any. The
/// work's frame is gone by the time `png_error` runs.
#[inline]
pub unsafe fn run<T>(p: *mut Png, r: R<T>, dflt: T) -> T {
    match r {
        Ok(v) => v,
        Err(E) => {
            if p.is_null() {
                dflt
            } else {
                raise(p)
            }
        }
    }
}

api! {
    pub unsafe extern "C" fn png_error(p: png_structp, msg: *const c_char) -> ! {
        error_impl(p, msg)
    }

    pub unsafe extern "C" fn png_chunk_error(p: png_structp, msg: *const c_char) -> ! {
        if p.is_null() {
            error_impl(p, msg)
        }
        let s = core::str::from_utf8(c_bytes(msg)).unwrap_or("error");
        chunk_fail(p, s);
        raise(p)
    }

    pub unsafe extern "C" fn png_warning(p: png_structp, msg: *const c_char) {
        warning_impl(p, msg)
    }

    pub unsafe extern "C" fn png_chunk_warning(p: png_structp, msg: *const c_char) {
        if p.is_null() {
            return warning_impl(p, msg);
        }
        let s = core::str::from_utf8(c_bytes(msg)).unwrap_or("warning");
        chunk_warn(p, s)
    }

    pub unsafe extern "C" fn png_benign_error(p: png_structp, msg: *const c_char) {
        if p.is_null() {
            return;
        }
        let s = core::str::from_utf8(c_bytes(msg)).unwrap_or("error");
        let r = benign(p, s);
        run(p, r, ())
    }

    pub unsafe extern "C" fn png_chunk_benign_error(p: png_structp, msg: *const c_char) {
        if p.is_null() {
            return;
        }
        let s = core::str::from_utf8(c_bytes(msg)).unwrap_or("error");
        let r = chunk_benign(p, s);
        run(p, r, ())
    }

    pub unsafe extern "C" fn png_set_error_fn(p: png_structp, error_ptr: png_voidp, error_fn: ErrorFn, warning_fn: ErrorFn) {
        if p.is_null() {
            return;
        }
        (*p).error_ptr = error_ptr;
        (*p).error_fn = error_fn;
        (*p).warning_fn = warning_fn;
    }

    pub unsafe extern "C" fn png_get_error_ptr(p: png_structp) -> png_voidp {
        if p.is_null() { core::ptr::null_mut() } else { (*p).error_ptr }
    }

    /// Returns the `jmp_buf` that `png_jmpbuf` hands to `setjmp`. It is
    /// allocated here, `jmp_buf_size` bytes, on the first call.
    pub unsafe extern "C" fn png_set_longjmp_fn(p: png_structp, longjmp_fn: LongjmpFn, jmp_buf_size: usize) -> *mut c_void {
        if p.is_null() {
            return core::ptr::null_mut();
        }
        match (*p).jmp_buf.as_mut() {
            Some(b) => {
                if (*p).jmp_buf_size != jmp_buf_size {
                    warn(p, "Application jmp_buf size changed");
                    return core::ptr::null_mut();
                }
                (*p).longjmp_fn = longjmp_fn;
                b.as_mut_ptr() as *mut c_void
            }
            None => {
                let n = jmp_buf_size.div_ceil(16).max(1);
                let mut b = vec![0u128; n].into_boxed_slice();
                let ptr = b.as_mut_ptr() as *mut c_void;
                (*p).jmp_buf = Some(b);
                (*p).jmp_buf_size = jmp_buf_size;
                (*p).longjmp_fn = longjmp_fn;
                ptr
            }
        }
    }

    pub unsafe extern "C" fn png_longjmp(p: png_structp, val: c_int) -> ! {
        longjmp(p, val)
    }

    pub unsafe extern "C" fn png_set_benign_errors(p: png_structp, allowed: c_int) {
        if p.is_null() {
            return;
        }
        let f = F_BENIGN_WARN | F_APP_WARNINGS_WARN | F_APP_ERRORS_WARN;
        if allowed != 0 {
            (*p).flags |= f;
        } else {
            (*p).flags &= !f;
        }
    }
}
