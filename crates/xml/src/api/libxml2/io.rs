//! The rest of what callers link: input callbacks (`xmlIO.h`), URIs
//! (`uri.h`) and encoding handlers (`encoding.h`). Inputs are read whole;
//! URIs are not parsed (`xmlParseURIReference` fails), and no encoding
//! handlers are offered, since the parser decodes its input itself.

use super::*;

pub type MatchCb = Option<unsafe extern "C" fn(*const c_char) -> c_int>;
pub type OpenCb = Option<unsafe extern "C" fn(*const c_char) -> *mut c_void>;
pub type ReadCb = Option<unsafe extern "C" fn(*mut c_void, *mut c_char, c_int) -> c_int>;
pub type CloseCb = Option<unsafe extern "C" fn(*mut c_void) -> c_int>;

#[derive(Clone, Copy)]
struct Callbacks {
    m: MatchCb,
    o: OpenCb,
    r: ReadCb,
    c: CloseCb,
}

static CALLBACKS: std::sync::Mutex<Vec<Callbacks>> = std::sync::Mutex::new(Vec::new());

#[unsafe(no_mangle)]
pub extern "C" fn xmlRegisterInputCallbacks(m: MatchCb, o: OpenCb, r: ReadCb, c: CloseCb) -> c_int {
    let mut v = CALLBACKS.lock().unwrap_or_else(|e| e.into_inner());
    if v.len() >= 15 {
        return -1;
    }
    v.push(Callbacks { m, o, r, c });
    v.len() as c_int - 1
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlPopInputCallbacks() -> c_int {
    let mut v = CALLBACKS.lock().unwrap_or_else(|e| e.into_inner());
    if v.pop().is_none() {
        return -1;
    }
    v.len() as c_int
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlCleanupInputCallbacks() {
    CALLBACKS.lock().unwrap_or_else(|e| e.into_inner()).clear();
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlRegisterDefaultInputCallbacks() {}

/// The bytes the newest callbacks that take `name` read, if any do.
/// `Some(None)`: they took it, and opening or reading failed.
pub unsafe fn read_by_callbacks(name: &[u8]) -> Option<Option<Vec<u8>>> {
    unsafe {
        let v: Vec<Callbacks> = CALLBACKS.lock().unwrap_or_else(|e| e.into_inner()).clone();
        let cname = nul(name);
        for cb in v.iter().rev() {
            let (Some(m), Some(o), Some(r)) = (cb.m, cb.o, cb.r) else { continue };
            if m(cname.as_ptr() as *const c_char) == 0 {
                continue;
            }
            let ctx = o(cname.as_ptr() as *const c_char);
            if ctx.is_null() {
                return Some(None);
            }
            let mut out = Vec::new();
            let mut buf = [0u8; 4096];
            let mut ok = true;
            loop {
                let n = r(ctx, buf.as_mut_ptr() as *mut c_char, buf.len() as c_int);
                if n < 0 {
                    ok = false;
                    break;
                }
                if n == 0 {
                    break;
                }
                out.extend_from_slice(&buf[..n as usize]);
            }
            if let Some(c) = cb.c {
                c(ctx);
            }
            return Some(if ok { Some(out) } else { None });
        }
        None
    }
}

// --- URIs ------------------------------------------------------------------------------------

/// `xmlURI`.
#[repr(C)]
pub struct Uri {
    pub scheme: *mut c_char,
    pub opaque: *mut c_char,
    pub authority: *mut c_char,
    pub server: *mut c_char,
    pub user: *mut c_char,
    pub port: c_int,
    pub path: *mut c_char,
    pub query: *mut c_char,
    pub fragment: *mut c_char,
    pub cleanup: c_int,
    pub query_raw: *mut c_char,
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlCreateURI() -> *mut Uri {
    xnew()
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlFreeURI(u: *mut Uri) {
    unsafe {
        if u.is_null() {
            return;
        }
        for p in [(*u).scheme, (*u).opaque, (*u).authority, (*u).server, (*u).user, (*u).path, (*u).query, (*u).fragment, (*u).query_raw] {
            xfree(p as *mut c_void);
        }
        xfree(u as *mut c_void);
    }
}

/// Not parsed here: always an error.
#[unsafe(no_mangle)]
pub extern "C" fn xmlParseURIReference(_u: *mut Uri, _s: *const c_char) -> c_int {
    1
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlParseURI(_s: *const c_char) -> *mut Uri {
    null_mut()
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlPrintURI(_f: *mut c_void, _u: *mut Uri) {}

#[unsafe(no_mangle)]
pub extern "C" fn xmlNormalizeURIPath(_p: *mut c_char) -> c_int {
    0
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlBuildURI(uri: *const XChar, base: *const XChar) -> *mut XChar {
    unsafe {
        if uri.is_null() {
            return null_mut();
        }
        xstrdup(&super::parser::build_uri(cbytes(uri), copt(base)))
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlBuildURISafe(uri: *const XChar, base: *const XChar, out: *mut *mut XChar) -> c_int {
    unsafe {
        if out.is_null() {
            return 1;
        }
        *out = xmlBuildURI(uri, base);
        if (*out).is_null() { 1 } else { 0 }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlPathToURI(path: *const XChar) -> *mut XChar {
    unsafe { if path.is_null() { null_mut() } else { xstrdup(cbytes(path)) } }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCanonicPath(path: *const XChar) -> *mut XChar {
    unsafe { xmlPathToURI(path) }
}

// --- encodings ---------------------------------------------------------------------------------

/// No handlers: the parser reads UTF-8, UTF-16, ISO-8859-1 and US-ASCII
/// itself, and the serializer writes UTF-8, ISO-8859-1 and US-ASCII.
#[unsafe(no_mangle)]
pub extern "C" fn xmlGetCharEncodingHandler(_enc: c_int) -> *mut c_void {
    null_mut()
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlFindCharEncodingHandler(_name: *const c_char) -> *mut c_void {
    null_mut()
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlCharEncInFunc(_h: *mut c_void, _out: *mut Buffer, _in: *mut Buffer) -> c_int {
    -1
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlCharEncOutFunc(_h: *mut c_void, _out: *mut Buffer, _in: *mut Buffer) -> c_int {
    -1
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlCharEncCloseFunc(h: *mut c_void) -> c_int {
    if h.is_null() { 0 } else { -1 }
}
