//! cJSON-compatible C ABI.
//!
//! This layer is NOT verified. It turns the verified parser's tape into the
//! linked `cJSON` node structure that C callers expect and implements the
//! read-side cJSON API on top of it. It is kept small and mechanical:
//! all syntax decisions are made by the verified parser.
#![allow(non_snake_case, non_camel_case_types, non_upper_case_globals)]
#![allow(clippy::missing_safety_doc)]

use crate::number::parse_f64;
use crate::parser::{ex_decode, parse_with, Kind, NumVal, Sink, Tok};
use crate::spec::STok;
use vstd::prelude::*;
use core::ffi::{c_char, c_double, c_int, c_void};
use core::ptr;
use std::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};

pub const cJSON_Invalid: c_int = 0;
pub const cJSON_False: c_int = 1 << 0;
pub const cJSON_True: c_int = 1 << 1;
pub const cJSON_NULL: c_int = 1 << 2;
pub const cJSON_Number: c_int = 1 << 3;
pub const cJSON_String: c_int = 1 << 4;
pub const cJSON_Array: c_int = 1 << 5;
pub const cJSON_Object: c_int = 1 << 6;
pub const cJSON_Raw: c_int = 1 << 7;
pub const cJSON_IsReference: c_int = 256;
pub const cJSON_StringIsConst: c_int = 512;

#[repr(C)]
pub struct cJSON {
    pub next: *mut cJSON,
    pub prev: *mut cJSON,
    pub child: *mut cJSON,
    pub type_: c_int,
    pub valuestring: *mut c_char,
    pub valueint: c_int,
    pub valuedouble: c_double,
    pub string: *mut c_char,
}

#[repr(C)]
pub struct cJSON_Hooks {
    pub malloc_fn: Option<unsafe extern "C" fn(usize) -> *mut c_void>,
    pub free_fn: Option<unsafe extern "C" fn(*mut c_void)>,
}

extern "C" {
    fn malloc(size: usize) -> *mut c_void;
    fn free(p: *mut c_void);
    fn strlen(s: *const c_char) -> usize;
    fn memchr(s: *const c_void, c: c_int, n: usize) -> *mut c_void;
}

// ---------------------------------------------------------------------------
// Allocation hooks
// ---------------------------------------------------------------------------

static MALLOC_FN: AtomicPtr<c_void> = AtomicPtr::new(ptr::null_mut());
static FREE_FN: AtomicPtr<c_void> = AtomicPtr::new(ptr::null_mut());

unsafe fn hook_malloc(size: usize) -> *mut c_void {
    let f = MALLOC_FN.load(Ordering::Relaxed);
    if f.is_null() {
        malloc(size)
    } else {
        let f: unsafe extern "C" fn(usize) -> *mut c_void = core::mem::transmute(f);
        f(size)
    }
}

unsafe fn hook_free(p: *mut c_void) {
    let f = FREE_FN.load(Ordering::Relaxed);
    if f.is_null() {
        free(p)
    } else {
        let f: unsafe extern "C" fn(*mut c_void) = core::mem::transmute(f);
        f(p)
    }
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_InitHooks(hooks: *mut cJSON_Hooks) {
    if hooks.is_null() {
        MALLOC_FN.store(ptr::null_mut(), Ordering::Relaxed);
        FREE_FN.store(ptr::null_mut(), Ordering::Relaxed);
        return;
    }
    let h = &*hooks;
    MALLOC_FN.store(
        h.malloc_fn.map_or(ptr::null_mut(), |f| f as *mut c_void),
        Ordering::Relaxed,
    );
    FREE_FN.store(
        h.free_fn.map_or(ptr::null_mut(), |f| f as *mut c_void),
        Ordering::Relaxed,
    );
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_malloc(size: usize) -> *mut c_void {
    hook_malloc(size)
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_free(object: *mut c_void) {
    if !object.is_null() {
        hook_free(object)
    }
}

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

static ERROR_JSON: AtomicPtr<c_char> = AtomicPtr::new(ptr::null_mut());
static ERROR_POS: AtomicUsize = AtomicUsize::new(0);

#[no_mangle]
pub unsafe extern "C" fn cJSON_GetErrorPtr() -> *const c_char {
    let j = ERROR_JSON.load(Ordering::Relaxed);
    if j.is_null() {
        ptr::null()
    } else {
        j.add(ERROR_POS.load(Ordering::Relaxed))
    }
}

// ---------------------------------------------------------------------------
// Building the tree
// ---------------------------------------------------------------------------

unsafe fn new_item() -> *mut cJSON {
    let p = hook_malloc(core::mem::size_of::<cJSON>()) as *mut cJSON;
    if !p.is_null() {
        ptr::write_bytes(p, 0, 1);
    }
    p
}

unsafe fn copy_cstr(bytes: &[u8]) -> *mut c_char {
    let p = hook_malloc(bytes.len() + 1) as *mut u8;
    if !p.is_null() {
        ptr::copy_nonoverlapping(bytes.as_ptr(), p, bytes.len());
        *p.add(bytes.len()) = 0;
    }
    p as *mut c_char
}

fn saturating_int(d: f64) -> c_int {
    if d >= c_int::MAX as f64 {
        c_int::MAX
    } else if d <= c_int::MIN as f64 {
        c_int::MIN
    } else {
        d as c_int
    }
}

/// Appends `item` as the last child of `parent`, keeping cJSON's invariant
/// that `child->prev` points at the last child.
unsafe fn append_child(parent: *mut cJSON, item: *mut cJSON) {
    let first = (*parent).child;
    if first.is_null() {
        (*parent).child = item;
        (*item).prev = item;
    } else {
        let last = (*first).prev;
        (*last).next = item;
        (*item).prev = last;
        (*first).prev = item;
    }
}

verus! {

/// Builds a cJSON tree from the parser's tokens as they are produced, so the
/// input is parsed in one pass with no intermediate tape. Allocation
/// failures and (impossible) malformed token sequences set `failed`; the
/// parse still runs to completion and the partial tree is freed afterwards.
#[verifier::external_body]
pub struct Builder {
    input: *const u8,
    input_len: usize,
    root: *mut cJSON,
    /// Open containers, innermost last (at most `MAX_DEPTH`).
    stack: Vec<*mut cJSON>,
    pending_key: *mut c_char,
    scratch: Vec<u8>,
    count: usize,
    err_pos: usize,
    failed: bool,
}

} // verus!

thread_local! {
    /// Buffers reused across parses on the same thread.
    static BUFFERS: core::cell::Cell<(Vec<*mut cJSON>, Vec<u8>)> = const { core::cell::Cell::new((Vec::new(), Vec::new())) };
}

impl Builder {
    fn input(&self) -> &[u8] {
        unsafe { core::slice::from_raw_parts(self.input, self.input_len) }
    }

    /// Copies a string token's decoded bytes into a new NUL-terminated buffer.
    unsafe fn string_copy(&mut self, t: &Tok) -> *mut c_char {
        let (a, b) = (t.a as usize, t.b as usize);
        let input = core::slice::from_raw_parts(self.input, self.input_len);
        if b < a || b > input.len() {
            return ptr::null_mut();
        }
        if t.escaped {
            self.scratch.clear();
            ex_decode(input, a, b, &mut self.scratch);
            copy_cstr(&self.scratch)
        } else {
            copy_cstr(&input[a..b])
        }
    }

    unsafe fn push_tok(&mut self, t: Tok) {
        self.count += 1;
        if self.failed {
            return;
        }
        match t.kind {
            Kind::ArrEnd | Kind::ObjEnd => {
                if self.stack.pop().is_none() {
                    self.failed = true;
                }
                return;
            }
            Kind::Key => {
                if !self.pending_key.is_null() {
                    self.failed = true;
                    return;
                }
                self.pending_key = self.string_copy(&t);
                if self.pending_key.is_null() {
                    self.failed = true;
                }
                return;
            }
            _ => {}
        }
        let item = new_item();
        if item.is_null() {
            self.failed = true;
            return;
        }
        // Link first so that a later failure frees the item with the tree.
        match self.stack.last() {
            Some(&parent) => append_child(parent, item),
            None => {
                if !self.root.is_null() {
                    hook_free(item as *mut c_void);
                    self.failed = true;
                    return;
                }
                self.root = item;
            }
        }
        if !self.pending_key.is_null() {
            (*item).string = self.pending_key;
            self.pending_key = ptr::null_mut();
        }
        match t.kind {
            Kind::Null => (*item).type_ = cJSON_NULL,
            Kind::True => (*item).type_ = cJSON_True,
            Kind::False => (*item).type_ = cJSON_False,
            Kind::Num => {
                let d = match self.input().get(t.a as usize..t.b as usize) {
                    Some(lex) => parse_f64(lex),
                    None => {
                        self.failed = true;
                        return;
                    }
                };
                (*item).type_ = cJSON_Number;
                (*item).valuedouble = d;
                (*item).valueint = saturating_int(d);
            }
            Kind::Str => {
                (*item).type_ = cJSON_String;
                (*item).valuestring = self.string_copy(&t);
                if (*item).valuestring.is_null() {
                    self.failed = true;
                }
            }
            Kind::ArrStart => {
                (*item).type_ = cJSON_Array;
                self.stack.push(item);
            }
            Kind::ObjStart => {
                (*item).type_ = cJSON_Object;
                self.stack.push(item);
            }
            Kind::Key | Kind::ArrEnd | Kind::ObjEnd => {}
        }
    }

    /// The finished tree, or null (after freeing everything) on failure.
    unsafe fn finish(mut self, ok: bool) -> *mut cJSON {
        let mut stack = core::mem::take(&mut self.stack);
        let unbalanced = !stack.is_empty();
        stack.clear();
        let mut scratch = core::mem::take(&mut self.scratch);
        if scratch.capacity() > 1 << 16 {
            scratch = Vec::new();
        }
        BUFFERS.with(|b| b.set((stack, scratch)));
        if !self.pending_key.is_null() {
            hook_free(self.pending_key as *mut c_void);
            self.pending_key = ptr::null_mut();
            self.failed = true;
        }
        if !ok || self.failed || unbalanced {
            if !self.root.is_null() {
                cJSON_Delete(self.root);
            }
            return ptr::null_mut();
        }
        self.root
    }
}

verus! {

/// The C ABI's token sink. Its methods are trusted (not verified): they
/// forward each token to `Builder`, and `hist` is the ghost record of the
/// tokens received, which the verified parser's postconditions describe.
pub struct TreeSink {
    pub hist: Ghost<Seq<STok>>,
    /// Unbounded: the tree grows as needed.
    pub room: Ghost<int>,
    pub b: Builder,
}

impl Sink for TreeSink {
    open spec fn hist(&self) -> Seq<STok> {
        self.hist@
    }

    open spec fn inv(&self, s: Seq<u8>) -> bool {
        true
    }

    open spec fn ready(&self, s: Seq<u8>, a: int, b: int) -> bool {
        true
    }

    #[verifier::external_body]
    #[inline(always)]
    fn push(&mut self, t: Tok) {
        unsafe { self.b.push_tok(t) }
    }

    open spec fn room(&self) -> int {
        self.room@
    }

    #[verifier::external_body]
    #[inline(always)]
    fn push_fast(&mut self, t: Tok) {
        unsafe { self.b.push_tok(t) }
    }

    #[verifier::external_body]
    #[inline(always)]
    fn eager(&self) -> bool {
        false
    }

    #[verifier::external_body]
    #[inline(always)]
    fn push_num_fast(&mut self, t: Tok, _s: &[u8], _n: NumVal, _ok: bool) {
        unsafe { self.b.push_tok(t) }
    }

    #[verifier::external_body]
    #[inline(always)]
    fn push_str_fast(&mut self, t: Tok, _s: &[u8]) {
        unsafe { self.b.push_tok(t) }
    }

    #[inline(always)]
    fn scan_str(&mut self, s: &[u8], idx: &[u32], k: usize, Ghost(st): Ghost<int>) -> (r: Option<
        (usize, usize, bool),
    >) {
        crate::stage2::ex2_string(s, idx, k, Ghost(st))
    }

    #[verifier::external_body]
    #[inline(always)]
    fn reserve(&mut self, _n: usize) {
    }

    #[verifier::external_body]
    #[inline(always)]
    fn count(&self) -> (n: usize) {
        self.b.count
    }

    #[verifier::external_body]
    #[inline(always)]
    fn close(&mut self, _idx: usize) {
    }

    #[verifier::external_body]
    #[inline(always)]
    fn fail(&mut self, pos: usize) {
        if pos > self.b.err_pos {
            self.b.err_pos = pos;
        }
    }
}

} // verus!

// ---------------------------------------------------------------------------
// Parsing
// ---------------------------------------------------------------------------

unsafe fn parse_impl(
    value: *const c_char,
    len: usize,
    return_parse_end: *mut *const c_char,
    require_null_terminated: bool,
) -> *mut cJSON {
    ERROR_JSON.store(ptr::null_mut(), Ordering::Relaxed);
    ERROR_POS.store(0, Ordering::Relaxed);
    if value.is_null() {
        return ptr::null_mut();
    }
    let input = core::slice::from_raw_parts(value as *const u8, len);
    let (stack, scratch) = BUFFERS.with(|b| b.take());
    let mut sink = TreeSink {
        hist: Ghost::assume_new(),
        room: Ghost::assume_new(),
        b: Builder {
            input: input.as_ptr(),
            input_len: input.len(),
            root: ptr::null_mut(),
            stack,
            pending_key: ptr::null_mut(),
            scratch,
            count: 0,
            err_pos: 0,
            failed: false,
        },
    };
    let result = parse_with(input, require_null_terminated, &mut sink);
    let err_pos = sink.b.err_pos;
    let root = sink.b.finish(result.is_ok());
    let end = match result {
        Ok(r) => r,
        Err(pos) => {
            let pos = pos.max(err_pos).min(len);
            ERROR_JSON.store(value as *mut c_char, Ordering::Relaxed);
            ERROR_POS.store(pos, Ordering::Relaxed);
            if !return_parse_end.is_null() {
                *return_parse_end = value.add(pos);
            }
            return ptr::null_mut();
        }
    };
    if root.is_null() {
        return ptr::null_mut();
    }
    if !return_parse_end.is_null() {
        let end = if require_null_terminated {
            crate::parser::ex_skip_ws(input, end)
        } else {
            end
        };
        *return_parse_end = value.add(end);
    }
    root
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_Parse(value: *const c_char) -> *mut cJSON {
    cJSON_ParseWithOpts(value, ptr::null_mut(), 0)
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_ParseWithLength(
    value: *const c_char,
    buffer_length: usize,
) -> *mut cJSON {
    cJSON_ParseWithLengthOpts(value, buffer_length, ptr::null_mut(), 0)
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_ParseWithOpts(
    value: *const c_char,
    return_parse_end: *mut *const c_char,
    require_null_terminated: c_int,
) -> *mut cJSON {
    if value.is_null() {
        return ptr::null_mut();
    }
    parse_impl(
        value,
        strlen(value),
        return_parse_end,
        require_null_terminated != 0,
    )
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_ParseWithLengthOpts(
    value: *const c_char,
    buffer_length: usize,
    return_parse_end: *mut *const c_char,
    require_null_terminated: c_int,
) -> *mut cJSON {
    if value.is_null() || buffer_length == 0 {
        return ptr::null_mut();
    }
    // cJSON treats a NUL inside the buffer as the end of the text.
    let bytes = core::slice::from_raw_parts(value as *const u8, buffer_length);
    let nul = memchr(value as *const c_void, 0, buffer_length);
    let len = if nul.is_null() {
        bytes.len()
    } else {
        nul as usize - value as usize
    };
    parse_impl(value, len, return_parse_end, require_null_terminated != 0)
}

// ---------------------------------------------------------------------------
// Deleting
// ---------------------------------------------------------------------------

#[no_mangle]
pub unsafe extern "C" fn cJSON_Delete(item: *mut cJSON) {
    // Iterative over siblings, recursive over children; depth is bounded by
    // the parser's nesting limit for trees this library built.
    let mut item = item;
    while !item.is_null() {
        let next = (*item).next;
        if (*item).type_ & cJSON_IsReference == 0 && !(*item).child.is_null() {
            cJSON_Delete((*item).child);
        }
        if (*item).type_ & cJSON_IsReference == 0 && !(*item).valuestring.is_null() {
            hook_free((*item).valuestring as *mut c_void);
        }
        if (*item).type_ & cJSON_StringIsConst == 0 && !(*item).string.is_null() {
            hook_free((*item).string as *mut c_void);
        }
        hook_free(item as *mut c_void);
        item = next;
    }
}

// ---------------------------------------------------------------------------
// Reading
// ---------------------------------------------------------------------------

#[no_mangle]
pub unsafe extern "C" fn cJSON_GetArraySize(array: *const cJSON) -> c_int {
    if array.is_null() {
        return 0;
    }
    let mut n: usize = 0;
    let mut c = (*array).child;
    while !c.is_null() {
        n += 1;
        c = (*c).next;
    }
    n as c_int
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_GetArrayItem(array: *const cJSON, index: c_int) -> *mut cJSON {
    if array.is_null() || index < 0 {
        return ptr::null_mut();
    }
    let mut c = (*array).child;
    let mut i = index;
    while !c.is_null() && i > 0 {
        i -= 1;
        c = (*c).next;
    }
    c
}

fn ascii_lower(b: u8) -> u8 {
    b.to_ascii_lowercase()
}

unsafe fn cstr_eq(a: *const c_char, b: *const c_char, case_sensitive: bool) -> bool {
    if a.is_null() || b.is_null() {
        return false;
    }
    let mut i = 0;
    loop {
        let x = *a.add(i) as u8;
        let y = *b.add(i) as u8;
        let eq = if case_sensitive {
            x == y
        } else {
            ascii_lower(x) == ascii_lower(y)
        };
        if !eq {
            return false;
        }
        if x == 0 {
            return true;
        }
        i += 1;
    }
}

unsafe fn get_object_item(
    object: *const cJSON,
    name: *const c_char,
    case_sensitive: bool,
) -> *mut cJSON {
    if object.is_null() || name.is_null() {
        return ptr::null_mut();
    }
    let mut c = (*object).child;
    while !c.is_null() {
        // As in cJSON, the case-sensitive search stops at the first member
        // without a name.
        if case_sensitive && (*c).string.is_null() {
            return ptr::null_mut();
        }
        if cstr_eq(name, (*c).string, case_sensitive) {
            return c;
        }
        c = (*c).next;
    }
    ptr::null_mut()
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_GetObjectItem(
    object: *const cJSON,
    string: *const c_char,
) -> *mut cJSON {
    get_object_item(object, string, false)
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_GetObjectItemCaseSensitive(
    object: *const cJSON,
    string: *const c_char,
) -> *mut cJSON {
    get_object_item(object, string, true)
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_HasObjectItem(object: *const cJSON, string: *const c_char) -> c_int {
    (!cJSON_GetObjectItem(object, string).is_null()) as c_int
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_GetStringValue(item: *const cJSON) -> *mut c_char {
    if cJSON_IsString(item) == 0 {
        return ptr::null_mut();
    }
    (*item).valuestring
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_GetNumberValue(item: *const cJSON) -> c_double {
    if cJSON_IsNumber(item) == 0 {
        return f64::NAN;
    }
    (*item).valuedouble
}

macro_rules! type_predicate {
    ($name:ident, $mask:expr) => {
        #[no_mangle]
        pub unsafe extern "C" fn $name(item: *const cJSON) -> c_int {
            if item.is_null() {
                return 0;
            }
            (((*item).type_ & 0xFF) == $mask) as c_int
        }
    };
}

type_predicate!(cJSON_IsInvalid, cJSON_Invalid);
type_predicate!(cJSON_IsFalse, cJSON_False);
type_predicate!(cJSON_IsTrue, cJSON_True);
type_predicate!(cJSON_IsNull, cJSON_NULL);
type_predicate!(cJSON_IsNumber, cJSON_Number);
type_predicate!(cJSON_IsString, cJSON_String);
type_predicate!(cJSON_IsArray, cJSON_Array);
type_predicate!(cJSON_IsObject, cJSON_Object);
type_predicate!(cJSON_IsRaw, cJSON_Raw);

#[no_mangle]
pub unsafe extern "C" fn cJSON_IsBool(item: *const cJSON) -> c_int {
    if item.is_null() {
        return 0;
    }
    (((*item).type_ & (cJSON_True | cJSON_False)) != 0) as c_int
}

static VERSION: &[u8] = b"1.7.19\0";

#[no_mangle]
pub extern "C" fn cJSON_Version() -> *const c_char {
    VERSION.as_ptr() as *const c_char
}

// ---------------------------------------------------------------------------
// Comparing
// ---------------------------------------------------------------------------

fn compare_double(a: f64, b: f64) -> bool {
    let max = if a.abs() > b.abs() { a.abs() } else { b.abs() };
    (a - b).abs() <= max * f64::EPSILON
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_Compare(
    a: *const cJSON,
    b: *const cJSON,
    case_sensitive: c_int,
) -> c_int {
    compare(a, b, case_sensitive != 0) as c_int
}

unsafe fn compare(a: *const cJSON, b: *const cJSON, case_sensitive: bool) -> bool {
    if a.is_null() || b.is_null() || ((*a).type_ & 0xFF) != ((*b).type_ & 0xFF) {
        return false;
    }
    let t = (*a).type_ & 0xFF;
    match t {
        cJSON_False | cJSON_True | cJSON_NULL | cJSON_Number | cJSON_String | cJSON_Raw
        | cJSON_Array | cJSON_Object => {}
        _ => return false,
    }
    if a == b {
        return true;
    }
    match t {
        cJSON_False | cJSON_True | cJSON_NULL => true,
        cJSON_Number => compare_double((*a).valuedouble, (*b).valuedouble),
        cJSON_String | cJSON_Raw => {
            !(*a).valuestring.is_null()
                && !(*b).valuestring.is_null()
                && cstr_eq((*a).valuestring, (*b).valuestring, true)
        }
        cJSON_Array => {
            let mut x = (*a).child;
            let mut y = (*b).child;
            while !x.is_null() && !y.is_null() {
                if !compare(x, y, case_sensitive) {
                    return false;
                }
                x = (*x).next;
                y = (*y).next;
            }
            x.is_null() && y.is_null()
        }
        cJSON_Object => {
            let mut x = (*a).child;
            while !x.is_null() {
                let y = get_object_item(b, (*x).string, case_sensitive);
                if y.is_null() || !compare(x, y, case_sensitive) {
                    return false;
                }
                x = (*x).next;
            }
            let mut y = (*b).child;
            while !y.is_null() {
                let x = get_object_item(a, (*y).string, case_sensitive);
                if x.is_null() || !compare(y, x, case_sensitive) {
                    return false;
                }
                y = (*y).next;
            }
            true
        }
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Printing
// ---------------------------------------------------------------------------

extern "C" {
    fn snprintf(buf: *mut c_char, n: usize, fmt: *const c_char, ...) -> c_int;
    fn strtod(s: *const c_char, end: *mut *mut c_char) -> c_double;
}

/// Formats a double with a printf format, replacing a locale decimal comma.
unsafe fn format_double(out: &mut Vec<u8>, fmt: &[u8], d: f64) -> Option<()> {
    let mut buf = [0u8; 26];
    let n = snprintf(
        buf.as_mut_ptr() as *mut c_char,
        buf.len(),
        fmt.as_ptr() as *const c_char,
        d,
    );
    if n < 0 || n as usize > buf.len() - 1 {
        return None;
    }
    out.extend(
        buf[..n as usize]
            .iter()
            .map(|&b| if b == b',' { b'.' } else { b }),
    );
    Some(())
}

unsafe fn print_number(item: *const cJSON, out: &mut Vec<u8>) -> Option<()> {
    let d = (*item).valuedouble;
    if d.is_nan() || d.is_infinite() {
        out.extend_from_slice(b"null");
    } else if d == (*item).valueint as f64 {
        out.extend_from_slice((*item).valueint.to_string().as_bytes());
    } else {
        let mut tmp = Vec::new();
        format_double(&mut tmp, b"%1.15g\0", d)?;
        tmp.push(0);
        let test = strtod(tmp.as_ptr() as *const c_char, ptr::null_mut());
        if compare_double(test, d) {
            out.extend_from_slice(&tmp[..tmp.len() - 1]);
        } else {
            format_double(out, b"%1.17g\0", d)?;
        }
    }
    Some(())
}

/// Writes a C string as a JSON string, with the verified escaper (the same
/// escapes cJSON uses).
unsafe fn print_string_ptr(s: *const c_char, out: &mut Vec<u8>) {
    let bytes: &[u8] = if s.is_null() { &[] } else { core::slice::from_raw_parts(s as *const u8, strlen(s)) };
    crate::write::write_string(out, bytes);
}

/// Mirrors cJSON's print_value / print_array / print_object output format.
unsafe fn print_value(
    item: *const cJSON,
    format: bool,
    depth: usize,
    out: &mut Vec<u8>,
) -> Option<()> {
    if item.is_null() {
        return None;
    }
    match (*item).type_ & 0xFF {
        cJSON_NULL => out.extend_from_slice(b"null"),
        cJSON_False => out.extend_from_slice(b"false"),
        cJSON_True => out.extend_from_slice(b"true"),
        cJSON_Number => print_number(item, out)?,
        cJSON_Raw => {
            let v = (*item).valuestring;
            if v.is_null() {
                return None;
            }
            out.extend_from_slice(core::slice::from_raw_parts(v as *const u8, strlen(v)));
        }
        cJSON_String => print_string_ptr((*item).valuestring, out),
        cJSON_Array => {
            if depth >= crate::spec::MAX_DEPTH {
                return None;
            }
            out.push(b'[');
            let mut c = (*item).child;
            while !c.is_null() {
                print_value(c, format, depth + 1, out)?;
                if !(*c).next.is_null() {
                    out.push(b',');
                    if format {
                        out.push(b' ');
                    }
                }
                c = (*c).next;
            }
            out.push(b']');
        }
        cJSON_Object => {
            if depth >= crate::spec::MAX_DEPTH {
                return None;
            }
            let depth = depth + 1;
            out.push(b'{');
            if format {
                out.push(b'\n');
            }
            let mut c = (*item).child;
            while !c.is_null() {
                if format {
                    out.extend(core::iter::repeat(b'\t').take(depth));
                }
                print_string_ptr((*c).string, out);
                out.push(b':');
                if format {
                    out.push(b'\t');
                }
                print_value(c, format, depth, out)?;
                if !(*c).next.is_null() {
                    out.push(b',');
                }
                if format {
                    out.push(b'\n');
                }
                c = (*c).next;
            }
            if format {
                out.extend(core::iter::repeat(b'\t').take(depth - 1));
            }
            out.push(b'}');
        }
        _ => return None,
    }
    Some(())
}

unsafe fn print_to_malloc(item: *const cJSON, format: bool) -> *mut c_char {
    let mut out = Vec::new();
    if print_value(item, format, 0, &mut out).is_none() {
        return ptr::null_mut();
    }
    copy_cstr(&out)
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_Print(item: *const cJSON) -> *mut c_char {
    print_to_malloc(item, true)
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_PrintUnformatted(item: *const cJSON) -> *mut c_char {
    print_to_malloc(item, false)
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_PrintBuffered(
    item: *const cJSON,
    prebuffer: c_int,
    fmt: c_int,
) -> *mut c_char {
    if prebuffer < 0 {
        return ptr::null_mut();
    }
    print_to_malloc(item, fmt != 0)
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_PrintPreallocated(
    item: *mut cJSON,
    buffer: *mut c_char,
    length: c_int,
    format: c_int,
) -> c_int {
    if length < 0 || buffer.is_null() {
        return 0;
    }
    let mut out = Vec::new();
    if print_value(item, format != 0, 0, &mut out).is_none() || out.len() + 1 > length as usize {
        return 0;
    }
    ptr::copy_nonoverlapping(out.as_ptr(), buffer as *mut u8, out.len());
    *buffer.add(out.len()) = 0;
    1
}

// ---------------------------------------------------------------------------
// Building and editing (ported from cJSON 1.7.19, same semantics)
// ---------------------------------------------------------------------------

/// cJSON's `CJSON_CIRCULAR_LIMIT`: how deep `cJSON_Duplicate` recurses.
const CIRCULAR_LIMIT: usize = 10000;

unsafe fn strdup_hook(s: *const c_char) -> *mut c_char {
    if s.is_null() {
        return ptr::null_mut();
    }
    copy_cstr(core::slice::from_raw_parts(s as *const u8, strlen(s)))
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_SetNumberHelper(object: *mut cJSON, number: c_double) -> c_double {
    if object.is_null() {
        return f64::NAN;
    }
    (*object).valueint = saturating_int(number);
    (*object).valuedouble = number;
    number
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_SetValuestring(object: *mut cJSON, valuestring: *const c_char) -> *mut c_char {
    if object.is_null() || (*object).type_ & cJSON_String == 0 || (*object).type_ & cJSON_IsReference != 0 {
        return ptr::null_mut();
    }
    if (*object).valuestring.is_null() || valuestring.is_null() {
        return ptr::null_mut();
    }
    let v1 = strlen(valuestring);
    let v2 = strlen((*object).valuestring);
    if v1 <= v2 {
        // The two strings must not overlap.
        let (a, b) = (valuestring as usize, (*object).valuestring as usize);
        if !(a + v1 < b || b + v2 < a) {
            return ptr::null_mut();
        }
        ptr::copy_nonoverlapping(valuestring, (*object).valuestring, v1 + 1);
        return (*object).valuestring;
    }
    let copy = strdup_hook(valuestring);
    if copy.is_null() {
        return ptr::null_mut();
    }
    hook_free((*object).valuestring as *mut c_void);
    (*object).valuestring = copy;
    copy
}

unsafe fn create_reference(item: *const cJSON) -> *mut cJSON {
    if item.is_null() {
        return ptr::null_mut();
    }
    let r = new_item();
    if r.is_null() {
        return r;
    }
    ptr::copy_nonoverlapping(item, r, 1);
    (*r).string = ptr::null_mut();
    (*r).type_ |= cJSON_IsReference;
    (*r).next = ptr::null_mut();
    (*r).prev = ptr::null_mut();
    r
}

unsafe fn add_item_to_array(array: *mut cJSON, item: *mut cJSON) -> bool {
    if item.is_null() || array.is_null() || array == item {
        return false;
    }
    let child = (*array).child;
    if child.is_null() {
        (*array).child = item;
        (*item).prev = item;
        (*item).next = ptr::null_mut();
    } else if !(*child).prev.is_null() {
        let last = (*child).prev;
        (*last).next = item;
        (*item).prev = last;
        (*child).prev = item;
    }
    true
}

unsafe fn add_item_to_object(object: *mut cJSON, string: *const c_char, item: *mut cJSON, constant_key: bool) -> bool {
    if object.is_null() || string.is_null() || item.is_null() || object == item {
        return false;
    }
    let (new_key, new_type) = if constant_key {
        (string as *mut c_char, (*item).type_ | cJSON_StringIsConst)
    } else {
        let k = strdup_hook(string);
        if k.is_null() {
            return false;
        }
        (k, (*item).type_ & !cJSON_StringIsConst)
    };
    if (*item).type_ & cJSON_StringIsConst == 0 && !(*item).string.is_null() {
        hook_free((*item).string as *mut c_void);
    }
    (*item).string = new_key;
    (*item).type_ = new_type;
    add_item_to_array(object, item)
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_AddItemToArray(array: *mut cJSON, item: *mut cJSON) -> c_int {
    add_item_to_array(array, item) as c_int
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_AddItemToObject(object: *mut cJSON, string: *const c_char, item: *mut cJSON) -> c_int {
    add_item_to_object(object, string, item, false) as c_int
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_AddItemToObjectCS(object: *mut cJSON, string: *const c_char, item: *mut cJSON) -> c_int {
    add_item_to_object(object, string, item, true) as c_int
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_AddItemReferenceToArray(array: *mut cJSON, item: *mut cJSON) -> c_int {
    if array.is_null() {
        return 0;
    }
    add_item_to_array(array, create_reference(item)) as c_int
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_AddItemReferenceToObject(object: *mut cJSON, string: *const c_char, item: *mut cJSON) -> c_int {
    if object.is_null() || string.is_null() {
        return 0;
    }
    add_item_to_object(object, string, create_reference(item), false) as c_int
}

/// Adds a new item to an object, or deletes it if that fails.
unsafe fn add_new(object: *mut cJSON, name: *const c_char, item: *mut cJSON) -> *mut cJSON {
    if add_item_to_object(object, name, item, false) {
        return item;
    }
    cJSON_Delete(item);
    ptr::null_mut()
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_AddNullToObject(object: *mut cJSON, name: *const c_char) -> *mut cJSON {
    add_new(object, name, cJSON_CreateNull())
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_AddTrueToObject(object: *mut cJSON, name: *const c_char) -> *mut cJSON {
    add_new(object, name, cJSON_CreateTrue())
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_AddFalseToObject(object: *mut cJSON, name: *const c_char) -> *mut cJSON {
    add_new(object, name, cJSON_CreateFalse())
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_AddBoolToObject(object: *mut cJSON, name: *const c_char, boolean: c_int) -> *mut cJSON {
    add_new(object, name, cJSON_CreateBool(boolean))
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_AddNumberToObject(object: *mut cJSON, name: *const c_char, number: c_double) -> *mut cJSON {
    add_new(object, name, cJSON_CreateNumber(number))
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_AddStringToObject(object: *mut cJSON, name: *const c_char, string: *const c_char) -> *mut cJSON {
    add_new(object, name, cJSON_CreateString(string))
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_AddRawToObject(object: *mut cJSON, name: *const c_char, raw: *const c_char) -> *mut cJSON {
    add_new(object, name, cJSON_CreateRaw(raw))
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_AddObjectToObject(object: *mut cJSON, name: *const c_char) -> *mut cJSON {
    add_new(object, name, cJSON_CreateObject())
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_AddArrayToObject(object: *mut cJSON, name: *const c_char) -> *mut cJSON {
    add_new(object, name, cJSON_CreateArray())
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_DetachItemViaPointer(parent: *mut cJSON, item: *mut cJSON) -> *mut cJSON {
    if parent.is_null() || item.is_null() || (item != (*parent).child && (*item).prev.is_null()) {
        return ptr::null_mut();
    }
    if item != (*parent).child {
        (*(*item).prev).next = (*item).next;
    }
    if !(*item).next.is_null() {
        (*(*item).next).prev = (*item).prev;
    }
    if item == (*parent).child {
        (*parent).child = (*item).next;
    } else if (*item).next.is_null() {
        (*(*parent).child).prev = (*item).prev;
    }
    (*item).prev = ptr::null_mut();
    (*item).next = ptr::null_mut();
    item
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_DetachItemFromArray(array: *mut cJSON, which: c_int) -> *mut cJSON {
    if which < 0 {
        return ptr::null_mut();
    }
    cJSON_DetachItemViaPointer(array, cJSON_GetArrayItem(array, which))
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_DeleteItemFromArray(array: *mut cJSON, which: c_int) {
    cJSON_Delete(cJSON_DetachItemFromArray(array, which))
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_DetachItemFromObject(object: *mut cJSON, string: *const c_char) -> *mut cJSON {
    cJSON_DetachItemViaPointer(object, cJSON_GetObjectItem(object, string))
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_DetachItemFromObjectCaseSensitive(object: *mut cJSON, string: *const c_char) -> *mut cJSON {
    cJSON_DetachItemViaPointer(object, cJSON_GetObjectItemCaseSensitive(object, string))
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_DeleteItemFromObject(object: *mut cJSON, string: *const c_char) {
    cJSON_Delete(cJSON_DetachItemFromObject(object, string))
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_DeleteItemFromObjectCaseSensitive(object: *mut cJSON, string: *const c_char) {
    cJSON_Delete(cJSON_DetachItemFromObjectCaseSensitive(object, string))
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_InsertItemInArray(array: *mut cJSON, which: c_int, newitem: *mut cJSON) -> c_int {
    if which < 0 || newitem.is_null() {
        return 0;
    }
    let after = cJSON_GetArrayItem(array, which);
    if after.is_null() {
        return add_item_to_array(array, newitem) as c_int;
    }
    if after != (*array).child && (*after).prev.is_null() {
        return 0;
    }
    (*newitem).next = after;
    (*newitem).prev = (*after).prev;
    (*after).prev = newitem;
    if after == (*array).child {
        (*array).child = newitem;
    } else {
        (*(*newitem).prev).next = newitem;
    }
    1
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_ReplaceItemViaPointer(parent: *mut cJSON, item: *mut cJSON, replacement: *mut cJSON) -> c_int {
    if parent.is_null() || (*parent).child.is_null() || replacement.is_null() || item.is_null() {
        return 0;
    }
    if replacement == item {
        return 1;
    }
    (*replacement).next = (*item).next;
    (*replacement).prev = (*item).prev;
    if !(*replacement).next.is_null() {
        (*(*replacement).next).prev = replacement;
    }
    if (*parent).child == item {
        if (*(*parent).child).prev == (*parent).child {
            (*replacement).prev = replacement;
        }
        (*parent).child = replacement;
    } else {
        if !(*replacement).prev.is_null() {
            (*(*replacement).prev).next = replacement;
        }
        if (*replacement).next.is_null() {
            (*(*parent).child).prev = replacement;
        }
    }
    (*item).next = ptr::null_mut();
    (*item).prev = ptr::null_mut();
    cJSON_Delete(item);
    1
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_ReplaceItemInArray(array: *mut cJSON, which: c_int, newitem: *mut cJSON) -> c_int {
    if which < 0 {
        return 0;
    }
    cJSON_ReplaceItemViaPointer(array, cJSON_GetArrayItem(array, which), newitem)
}

unsafe fn replace_item_in_object(object: *mut cJSON, string: *const c_char, replacement: *mut cJSON, case_sensitive: bool) -> c_int {
    if replacement.is_null() || string.is_null() {
        return 0;
    }
    if (*replacement).type_ & cJSON_StringIsConst == 0 && !(*replacement).string.is_null() {
        hook_free((*replacement).string as *mut c_void);
    }
    (*replacement).string = strdup_hook(string);
    if (*replacement).string.is_null() {
        return 0;
    }
    (*replacement).type_ &= !cJSON_StringIsConst;
    cJSON_ReplaceItemViaPointer(object, get_object_item(object, string, case_sensitive), replacement)
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_ReplaceItemInObject(object: *mut cJSON, string: *const c_char, newitem: *mut cJSON) -> c_int {
    replace_item_in_object(object, string, newitem, false)
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_ReplaceItemInObjectCaseSensitive(object: *mut cJSON, string: *const c_char, newitem: *mut cJSON) -> c_int {
    replace_item_in_object(object, string, newitem, true)
}

unsafe fn create_typed(type_: c_int) -> *mut cJSON {
    let item = new_item();
    if !item.is_null() {
        (*item).type_ = type_;
    }
    item
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_CreateNull() -> *mut cJSON {
    create_typed(cJSON_NULL)
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_CreateTrue() -> *mut cJSON {
    create_typed(cJSON_True)
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_CreateFalse() -> *mut cJSON {
    create_typed(cJSON_False)
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_CreateBool(boolean: c_int) -> *mut cJSON {
    create_typed(if boolean != 0 { cJSON_True } else { cJSON_False })
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_CreateNumber(num: c_double) -> *mut cJSON {
    let item = create_typed(cJSON_Number);
    if !item.is_null() {
        (*item).valuedouble = num;
        (*item).valueint = saturating_int(num);
    }
    item
}

/// An item of `type_` holding a copy of `s` as its value string.
unsafe fn create_with_string(type_: c_int, s: *const c_char) -> *mut cJSON {
    let item = create_typed(type_);
    if !item.is_null() {
        (*item).valuestring = strdup_hook(s);
        if (*item).valuestring.is_null() {
            cJSON_Delete(item);
            return ptr::null_mut();
        }
    }
    item
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_CreateString(string: *const c_char) -> *mut cJSON {
    create_with_string(cJSON_String, string)
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_CreateRaw(raw: *const c_char) -> *mut cJSON {
    create_with_string(cJSON_Raw, raw)
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_CreateStringReference(string: *const c_char) -> *mut cJSON {
    let item = create_typed(cJSON_String | cJSON_IsReference);
    if !item.is_null() {
        (*item).valuestring = string as *mut c_char;
    }
    item
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_CreateObjectReference(child: *const cJSON) -> *mut cJSON {
    let item = create_typed(cJSON_Object | cJSON_IsReference);
    if !item.is_null() {
        (*item).child = child as *mut cJSON;
    }
    item
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_CreateArrayReference(child: *const cJSON) -> *mut cJSON {
    let item = create_typed(cJSON_Array | cJSON_IsReference);
    if !item.is_null() {
        (*item).child = child as *mut cJSON;
    }
    item
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_CreateArray() -> *mut cJSON {
    create_typed(cJSON_Array)
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_CreateObject() -> *mut cJSON {
    create_typed(cJSON_Object)
}

/// An array of `count` items made by `make(i)`, or null.
unsafe fn create_array_of(count: c_int, make: impl Fn(usize) -> *mut cJSON) -> *mut cJSON {
    let a = cJSON_CreateArray();
    if a.is_null() {
        return a;
    }
    for i in 0..count as usize {
        let n = make(i);
        if n.is_null() {
            cJSON_Delete(a);
            return ptr::null_mut();
        }
        append_child(a, n);
    }
    a
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_CreateIntArray(numbers: *const c_int, count: c_int) -> *mut cJSON {
    if count < 0 || numbers.is_null() {
        return ptr::null_mut();
    }
    create_array_of(count, |i| cJSON_CreateNumber(*numbers.add(i) as c_double))
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_CreateFloatArray(numbers: *const f32, count: c_int) -> *mut cJSON {
    if count < 0 || numbers.is_null() {
        return ptr::null_mut();
    }
    create_array_of(count, |i| cJSON_CreateNumber(*numbers.add(i) as c_double))
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_CreateDoubleArray(numbers: *const c_double, count: c_int) -> *mut cJSON {
    if count < 0 || numbers.is_null() {
        return ptr::null_mut();
    }
    create_array_of(count, |i| cJSON_CreateNumber(*numbers.add(i)))
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_CreateStringArray(strings: *const *const c_char, count: c_int) -> *mut cJSON {
    if count < 0 || strings.is_null() {
        return ptr::null_mut();
    }
    create_array_of(count, |i| cJSON_CreateString(*strings.add(i)))
}

#[no_mangle]
pub unsafe extern "C" fn cJSON_Duplicate(item: *const cJSON, recurse: c_int) -> *mut cJSON {
    duplicate(item, 0, recurse != 0)
}

unsafe fn duplicate(item: *const cJSON, depth: usize, recurse: bool) -> *mut cJSON {
    if item.is_null() {
        return ptr::null_mut();
    }
    let n = new_item();
    if n.is_null() {
        return n;
    }
    (*n).type_ = (*item).type_ & !cJSON_IsReference;
    (*n).valueint = (*item).valueint;
    (*n).valuedouble = (*item).valuedouble;
    if !(*item).valuestring.is_null() {
        (*n).valuestring = strdup_hook((*item).valuestring);
        if (*n).valuestring.is_null() {
            cJSON_Delete(n);
            return ptr::null_mut();
        }
    }
    if !(*item).string.is_null() {
        (*n).string = if (*item).type_ & cJSON_StringIsConst != 0 { (*item).string } else { strdup_hook((*item).string) };
        if (*n).string.is_null() {
            cJSON_Delete(n);
            return ptr::null_mut();
        }
    }
    if !recurse {
        return n;
    }
    let mut child = (*item).child;
    while !child.is_null() {
        if depth >= CIRCULAR_LIMIT {
            cJSON_Delete(n);
            return ptr::null_mut();
        }
        let c = duplicate(child, depth + 1, true);
        if c.is_null() {
            cJSON_Delete(n);
            return ptr::null_mut();
        }
        append_child(n, c);
        child = (*child).next;
    }
    n
}

/// Removes whitespace and `//` and `/* */` comments in place, as cJSON
/// does. Strings are copied as they are. The work is the verified
/// `minify::minify_in_place`.
#[no_mangle]
pub unsafe extern "C" fn cJSON_Minify(json: *mut c_char) {
    if json.is_null() {
        return;
    }
    // The string and its NUL.
    let buf = core::slice::from_raw_parts_mut(json as *mut u8, strlen(json) + 1);
    crate::minify::minify_in_place(buf);
}
