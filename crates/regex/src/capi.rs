//! The C API.
//!
//! `vregex_*` is the native API. The `cre2_*` functions follow cre2, the
//! C wrapper of RE2 (`cre2.h`); with the `cre2-abi` feature they are
//! exported under cre2's names so that vregex links in place of cre2 and
//! RE2, and without it as `vregex_cre2_*`.
//!
//! This is plain Rust glue outside the proof. It checks its arguments,
//! calls the verified `Regex::new` and `Regex::search_with`, and copies
//! the results out.
#![allow(clippy::missing_safety_doc)]
#![allow(unsafe_op_in_unsafe_fn)]

use crate::pike::{Scratch, NONE};
use crate::{Error, Regex};
use core::ffi::{c_char, c_int};
use std::sync::atomic::{AtomicPtr, Ordering};
use std::sync::Mutex;

/// A compiled pattern, with working memory kept between searches.
pub struct Handle {
    re: Option<Regex>,
    /// The pattern with `\z` after it, for searches anchored at both
    /// ends; compiled when first needed.
    both: Mutex<Option<Option<Box<Regex>>>>,
    pattern: Vec<u8>,
    /// The pattern as compiled: with the options' flags in front.
    source: Vec<u8>,
    err: c_int,
    err_at: usize,
    pool: Pool,
    both_pool: Pool,
}

type Work = (Scratch, Vec<usize>);

/// Working memory kept between searches. One set sits in `first`, taken
/// and put back with a single atomic swap each, so a search on one thread
/// takes no lock and allocates nothing; sets that other threads were
/// using at the same time wait in `rest`.
struct Pool {
    first: AtomicPtr<Work>,
    rest: Mutex<Vec<Box<Work>>>,
}

impl Pool {
    fn new() -> Pool {
        Pool { first: AtomicPtr::new(core::ptr::null_mut()), rest: Mutex::new(Vec::new()) }
    }

    fn take(&self, re: &Regex) -> Box<Work> {
        let p = self.first.swap(core::ptr::null_mut(), Ordering::AcqRel);
        if !p.is_null() {
            // Only `put` stores a pointer here, from `Box::into_raw`, and
            // the swap took it out, so this is its one owner.
            return unsafe { Box::from_raw(p) };
        }
        if let Some(w) = self.rest.lock().ok().and_then(|mut r| r.pop()) {
            return w;
        }
        Box::new((re.scratch(), re.slots()))
    }

    fn put(&self, w: Box<Work>) {
        let old = self.first.swap(Box::into_raw(w), Ordering::AcqRel);
        if !old.is_null() {
            let old = unsafe { Box::from_raw(old) };
            if let Ok(mut r) = self.rest.lock() {
                r.push(old);
            }
        }
    }
}

impl Drop for Pool {
    fn drop(&mut self) {
        let p = *self.first.get_mut();
        if !p.is_null() {
            drop(unsafe { Box::from_raw(p) });
        }
    }
}

pub const VREGEX_OK: c_int = 0;
pub const VREGEX_SYNTAX: c_int = 1;
pub const VREGEX_BAD_UTF8: c_int = 2;
pub const VREGEX_TOO_BIG: c_int = 3;
pub const VREGEX_UNSUPPORTED: c_int = 4;

fn compile(pattern: &[u8], source: Vec<u8>) -> Box<Handle> {
    let (re, err, err_at) = match Regex::new(&source) {
        Ok(re) => (Some(re), VREGEX_OK, 0),
        Err(Error::Syntax(at)) => (None, VREGEX_SYNTAX, at.saturating_sub(source.len() - pattern.len())),
        Err(Error::BadUtf8) => (None, VREGEX_BAD_UTF8, 0),
        Err(Error::TooBig) => (None, VREGEX_TOO_BIG, 0),
    };
    Box::new(Handle {
        re,
        both: Mutex::new(None),
        pattern: pattern.to_vec(),
        source,
        err,
        err_at,
        pool: Pool::new(),
        both_pool: Pool::new(),
    })
}

unsafe fn bytes<'a>(p: *const c_char, n: usize) -> &'a [u8] {
    if p.is_null() || n == 0 {
        &[]
    } else {
        core::slice::from_raw_parts(p as *const u8, n)
    }
}

/// Searches `text` from `from` with `re`, using working memory from
/// `pool`. On a match, calls `found` with the slots and returns true.
fn search(re: &Regex, pool: &Pool, text: &[u8], from: usize, found: impl FnOnce(&[usize])) -> bool {
    if from > text.len() || text.len() == usize::MAX {
        return false;
    }
    let mut w = pool.take(re);
    let (sc, out) = &mut *w;
    let hit = re.search_with(text, from, sc, out).0;
    if hit {
        found(out);
    }
    pool.put(w);
    hit
}

// ---------------------------------------------------------------------------
// Native API
// ---------------------------------------------------------------------------

/// Compiles `pattern[..len]`. Never null; check `vregex_error`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vregex_new(pattern: *const c_char, len: usize) -> *mut Handle {
    let pat = bytes(pattern, len);
    Box::into_raw(compile(pat, pat.to_vec()))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vregex_free(re: *mut Handle) {
    if !re.is_null() {
        drop(Box::from_raw(re));
    }
}

/// `VREGEX_OK`, or why the pattern did not compile.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vregex_error(re: *const Handle) -> c_int {
    (*re).err
}

/// For `VREGEX_SYNTAX`: the byte offset in the pattern where it went wrong.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vregex_error_offset(re: *const Handle) -> usize {
    (*re).err_at
}

/// Number of groups, counting group 0 (the whole match). 0 if the pattern
/// did not compile.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vregex_groups(re: *const Handle) -> usize {
    match &(*re).re {
        Some(r) => r.groups(),
        None => 0,
    }
}

/// The number of the group called `name[..len]`, or -1.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vregex_group_index(re: *const Handle, name: *const c_char, len: usize) -> c_int {
    let name = bytes(name, len);
    if let Some(r) = &(*re).re {
        for (n, k) in r.names.iter() {
            if n.as_slice() == name {
                return *k as c_int;
            }
        }
    }
    -1
}

/// Searches `text[..len]` from byte `from` for the leftmost match. Returns
/// 1 and fills `slots[..nslots]` (start and end of group 0, then of group
/// 1, ...; `SIZE_MAX` for a group that took no part), or returns 0.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vregex_search(
    re: *const Handle,
    text: *const c_char,
    len: usize,
    from: usize,
    slots: *mut usize,
    nslots: usize,
) -> c_int {
    let h = &*re;
    let r = match &h.re {
        Some(r) => r,
        None => return 0,
    };
    let hit = search(r, &h.pool, bytes(text, len), from, |out| {
        for i in 0..nslots {
            *slots.add(i) = if i < out.len() { out[i] } else { NONE };
        }
    });
    hit as c_int
}

// ---------------------------------------------------------------------------
// cre2's API
// ---------------------------------------------------------------------------

#[repr(C)]
pub struct Cre2String {
    pub data: *const c_char,
    pub length: c_int,
}

pub const CRE2_UNANCHORED: c_int = 1;
pub const CRE2_ANCHOR_START: c_int = 2;
pub const CRE2_ANCHOR_BOTH: c_int = 3;

pub const CRE2_UTF8: c_int = 1;
pub const CRE2_LATIN1: c_int = 2;

/// RE2's options. The ones marked "refused" make `cre2_new` fail when set
/// to something other than RE2's default.
pub struct Options {
    case_sensitive: bool,
    dot_nl: bool,
    literal: bool,
    /// Refused.
    longest_match: bool,
    /// Refused.
    posix_syntax: bool,
    /// Refused.
    never_nl: bool,
    /// Refused.
    never_capture: bool,
    /// Refused if Latin-1.
    encoding: c_int,
    // These have no effect on RE2 either unless posix_syntax is set.
    perl_classes: bool,
    word_boundary: bool,
    one_line: bool,
    log_errors: bool,
    max_mem: i64,
}

impl Options {
    fn new() -> Options {
        Options {
            case_sensitive: true,
            dot_nl: false,
            literal: false,
            longest_match: false,
            posix_syntax: false,
            never_nl: false,
            never_capture: false,
            encoding: CRE2_UTF8,
            perl_classes: false,
            word_boundary: false,
            one_line: false,
            log_errors: true,
            max_mem: 8 << 20,
        }
    }
}

macro_rules! cre2 {
    ($(#[$m:meta])* fn $name:ident = $cname:literal ($($a:ident : $t:ty),*) $(-> $r:ty)? $body:block) => {
        $(#[$m])*
        #[cfg_attr(feature = "cre2-abi", unsafe(export_name = $cname))]
        #[cfg_attr(not(feature = "cre2-abi"), unsafe(export_name = concat!("vregex_", $cname)))]
        pub unsafe extern "C" fn $name($($a: $t),*) $(-> $r)? $body
    };
}

cre2! { fn cre2_opt_new = "cre2_opt_new"() -> *mut Options { Box::into_raw(Box::new(Options::new())) } }
cre2! { fn cre2_opt_delete = "cre2_opt_delete"(o: *mut Options) { if !o.is_null() { drop(Box::from_raw(o)); } } }

macro_rules! opt_flag {
    ($set:ident = $sname:literal, $get:ident = $gname:literal, $f:ident) => {
        cre2! { fn $set = $sname(o: *mut Options, v: c_int) { (*o).$f = v != 0; } }
        cre2! { fn $get = $gname(o: *const Options) -> c_int { (*o).$f as c_int } }
    };
}

opt_flag!(cre2_opt_set_case_sensitive = "cre2_opt_set_case_sensitive", cre2_opt_case_sensitive = "cre2_opt_case_sensitive", case_sensitive);
opt_flag!(cre2_opt_set_dot_nl = "cre2_opt_set_dot_nl", cre2_opt_dot_nl = "cre2_opt_dot_nl", dot_nl);
opt_flag!(cre2_opt_set_literal = "cre2_opt_set_literal", cre2_opt_literal = "cre2_opt_literal", literal);
opt_flag!(cre2_opt_set_longest_match = "cre2_opt_set_longest_match", cre2_opt_longest_match = "cre2_opt_longest_match", longest_match);
opt_flag!(cre2_opt_set_posix_syntax = "cre2_opt_set_posix_syntax", cre2_opt_posix_syntax = "cre2_opt_posix_syntax", posix_syntax);
opt_flag!(cre2_opt_set_never_nl = "cre2_opt_set_never_nl", cre2_opt_never_nl = "cre2_opt_never_nl", never_nl);
opt_flag!(cre2_opt_set_never_capture = "cre2_opt_set_never_capture", cre2_opt_never_capture = "cre2_opt_never_capture", never_capture);
opt_flag!(cre2_opt_set_perl_classes = "cre2_opt_set_perl_classes", cre2_opt_perl_classes = "cre2_opt_perl_classes", perl_classes);
opt_flag!(cre2_opt_set_word_boundary = "cre2_opt_set_word_boundary", cre2_opt_word_boundary = "cre2_opt_word_boundary", word_boundary);
opt_flag!(cre2_opt_set_one_line = "cre2_opt_set_one_line", cre2_opt_one_line = "cre2_opt_one_line", one_line);
opt_flag!(cre2_opt_set_log_errors = "cre2_opt_set_log_errors", cre2_opt_log_errors = "cre2_opt_log_errors", log_errors);

cre2! { fn cre2_opt_set_encoding = "cre2_opt_set_encoding"(o: *mut Options, v: c_int) { (*o).encoding = v; } }
cre2! { fn cre2_opt_encoding = "cre2_opt_encoding"(o: *const Options) -> c_int { (*o).encoding } }
cre2! { fn cre2_opt_set_max_mem = "cre2_opt_set_max_mem"(o: *mut Options, v: i64) { (*o).max_mem = v; } }
cre2! { fn cre2_opt_max_mem = "cre2_opt_max_mem"(o: *const Options) -> i64 { (*o).max_mem } }

/// The pattern text that stands for the bytes `lit` taken literally.
fn quote_literal(lit: &[u8], out: &mut Vec<u8>) {
    for &b in lit {
        // Bytes of multi-byte characters, letters, digits and `_` stand
        // for themselves; anything else in ASCII is escaped.
        if b >= 0x80 || b.is_ascii_alphanumeric() || b == b'_' {
            out.push(b);
        } else if b == 0 {
            out.extend_from_slice(b"\\x00");
        } else {
            out.push(b'\\');
            out.push(b);
        }
    }
}

cre2! {
    /// Compiles `pattern[..len]` under `opt` (null for the defaults). Never
    /// null; check `cre2_error_code`.
    fn cre2_new = "cre2_new"(pattern: *const c_char, len: c_int, opt: *const Options) -> *mut Handle {
        let pat = bytes(pattern, len.max(0) as usize);
        let defaults = Options::new();
        let o = if opt.is_null() { &defaults } else { &*opt };
        if o.longest_match || o.posix_syntax || o.never_nl || o.never_capture || o.encoding != CRE2_UTF8 {
            let mut h = compile(pat, Vec::new());
            h.re = None;
            h.err = VREGEX_UNSUPPORTED;
            return Box::into_raw(h);
        }
        let mut src = Vec::with_capacity(pat.len() + 8);
        if !o.case_sensitive {
            src.extend_from_slice(b"(?i)");
        }
        if o.dot_nl {
            src.extend_from_slice(b"(?s)");
        }
        if o.literal {
            quote_literal(pat, &mut src);
        } else {
            src.extend_from_slice(pat);
        }
        Box::into_raw(compile(pat, src))
    }
}

cre2! { fn cre2_delete = "cre2_delete"(re: *mut Handle) { vregex_free(re) } }

cre2! {
    /// 0 if the pattern compiled. Otherwise nonzero: RE2's
    /// `ErrorPatternTooLarge` (14) or `ErrorBadUTF8` (12) where those are
    /// the reason, else `ErrorInternal` (1); RE2's finer syntax error
    /// codes are not reproduced.
    fn cre2_error_code = "cre2_error_code"(re: *const Handle) -> c_int {
        match (*re).err {
            VREGEX_OK => 0,
            VREGEX_BAD_UTF8 => 12,
            VREGEX_TOO_BIG => 14,
            _ => 1,
        }
    }
}

cre2! {
    fn cre2_error_string = "cre2_error_string"(re: *const Handle) -> *const c_char {
        let s: &'static [u8] = match (*re).err {
            VREGEX_OK => b"\0",
            VREGEX_SYNTAX => b"syntax error\0",
            VREGEX_BAD_UTF8 => b"invalid UTF-8\0",
            VREGEX_TOO_BIG => b"pattern too large\0",
            _ => b"option not supported\0",
        };
        s.as_ptr() as *const c_char
    }
}

cre2! {
    /// Number of capturing groups, not counting the whole match; -1 if the
    /// pattern did not compile.
    fn cre2_num_capturing_groups = "cre2_num_capturing_groups"(re: *const Handle) -> c_int {
        match &(*re).re {
            Some(r) => r.groups() as c_int - 1,
            None => -1,
        }
    }
}

cre2! {
    /// The number of the group called `name` (a C string), or -1.
    fn cre2_find_named_capturing_groups = "cre2_find_named_capturing_groups"(re: *const Handle, name: *const c_char) -> c_int {
        let n = core::ffi::CStr::from_ptr(name).to_bytes();
        vregex_group_index(re, n.as_ptr() as *const c_char, n.len())
    }
}

cre2! {
    /// Number of instructions in the compiled program; -1 if the pattern
    /// did not compile. (Not the same number as RE2's.)
    fn cre2_program_size = "cre2_program_size"(re: *const Handle) -> c_int {
        match &(*re).re {
            Some(r) => r.prog.insts.len() as c_int,
            None => -1,
        }
    }
}

cre2! {
    /// Searches `text[startpos..endpos]`, with `text[..endpos]` as the
    /// whole text. Returns 1 on a match and fills `m[..nmatch]` with the
    /// groups (null data for a group that took no part), or returns 0.
    fn cre2_match = "cre2_match"(re: *const Handle, text: *const c_char, textlen: c_int, startpos: c_int, endpos: c_int, anchor: c_int, m: *mut Cre2String, nmatch: c_int) -> c_int {
        let h = &*re;
        let r = match &h.re {
            Some(r) => r,
            None => return 0,
        };
        if startpos < 0 || endpos > textlen || startpos > endpos {
            return 0;
        }
        let t = bytes(text, endpos as usize);
        let from = startpos as usize;
        let mut ok = false;
        let fill = |out: &[usize]| {
            // An anchored match is the leftmost match if that starts at
            // `from`: the search prefers earlier starts, and at one start
            // reports the match the pattern prefers.
            if anchor != CRE2_UNANCHORED && out[0] != from {
                return;
            }
            for i in 0..nmatch.max(0) as usize {
                let s = &mut *m.add(i);
                if 2 * i + 1 < out.len() && out[2 * i] != NONE {
                    s.data = text.add(out[2 * i]);
                    s.length = (out[2 * i + 1] - out[2 * i]) as c_int;
                } else {
                    s.data = core::ptr::null();
                    s.length = 0;
                }
            }
            ok = true;
        };
        if anchor == CRE2_ANCHOR_BOTH {
            // The match of `(?:pattern)\\z` that starts at `from`.
            let mut both = match h.both.lock() {
                Ok(b) => b,
                Err(_) => return 0,
            };
            if both.is_none() {
                let mut src = Vec::with_capacity(h.source.len() + 8);
                src.extend_from_slice(b"(?:");
                src.extend_from_slice(&h.source);
                src.extend_from_slice(b")\\z");
                *both = Some(Regex::new(&src).ok().map(Box::new));
            }
            match both.as_ref().and_then(|b| b.as_ref()) {
                Some(b) => search(b, &h.both_pool, t, from, fill),
                None => return 0,
            };
        } else {
            search(r, &h.pool, t, from, fill);
        }
        ok as c_int
    }
}

cre2! {
    /// The pattern as given to `cre2_new` (not NUL-terminated here: use
    /// with the length given to `cre2_new`).
    fn cre2_pattern = "cre2_pattern"(re: *const Handle) -> *const c_char {
        (*re).pattern.as_ptr() as *const c_char
    }
}
