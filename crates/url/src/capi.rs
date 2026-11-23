//! A C API with the same types and behavior as ada's `ada_c.h`.
//!
//! Each function is exported as `vurl_<name>`, or as `ada_<name>` with the
//! `ada-abi` feature so that vurl links in place of ada. This is plain Rust
//! glue outside the proof: it calls the verified parser and the setters and
//! hands out pointers into the URL's href.
#![allow(clippy::missing_safety_doc)]
#![allow(unsafe_op_in_unsafe_fn)]

use crate::searchparams::UrlSearchParams;
use crate::url::Url;
use core::ffi::c_char;
use core::sync::atomic::{AtomicU32, Ordering};

pub const OMITTED: u32 = 0xffff_ffff;

#[repr(C)]
#[derive(Clone, Copy)]
pub struct AdaString {
    pub data: *const c_char,
    pub length: usize,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct AdaOwnedString {
    pub data: *const c_char,
    pub length: usize,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct AdaStringPair {
    pub key: AdaString,
    pub value: AdaString,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct AdaUrlComponents {
    pub protocol_end: u32,
    pub username_end: u32,
    pub host_start: u32,
    pub host_end: u32,
    pub port: u32,
    pub pathname_start: u32,
    pub search_start: u32,
    pub hash_start: u32,
}

#[repr(C)]
pub struct AdaVersionComponents {
    pub major: i32,
    pub minor: i32,
    pub revision: i32,
}

/// What an `ada_url` points to.
pub struct Handle {
    url: Option<Url>,
    comps: AdaUrlComponents,
}

static MAX_INPUT_LENGTH: AtomicU32 = AtomicU32::new(u32::MAX);

fn max_len() -> usize {
    MAX_INPUT_LENGTH.load(Ordering::Relaxed) as usize
}

const NULL: AdaString = AdaString { data: core::ptr::null(), length: 0 };

fn view(s: &[u8]) -> AdaString {
    AdaString { data: s.as_ptr() as *const c_char, length: s.len() }
}

fn owned(v: Vec<u8>) -> AdaOwnedString {
    let b = v.into_boxed_slice();
    let length = b.len();
    AdaOwnedString { data: Box::into_raw(b) as *const u8 as *const c_char, length }
}

unsafe fn bytes<'a>(p: *const c_char, n: usize) -> &'a [u8] {
    if p.is_null() || n == 0 {
        &[]
    } else {
        core::slice::from_raw_parts(p as *const u8, n)
    }
}

/// ada's component offsets for `u`.
pub fn components(u: &Url) -> AdaUrlComponents {
    let protocol_end = u.scheme_end as u32 + 1;
    let (username_end, host_start, host_end) = if u.has_authority() {
        let creds = u.username_end + 1 < u.host_start || u.username_end > u.scheme_end + 3;
        let hs = if creds { u.host_start - 1 } else { u.host_start };
        (u.username_end as u32, hs as u32, u.host_end as u32)
    } else {
        (protocol_end, protocol_end, protocol_end)
    };
    AdaUrlComponents {
        protocol_end,
        username_end,
        host_start,
        host_end,
        port: u.port.map_or(OMITTED, |p| p as u32),
        pathname_start: u.path_start as u32,
        search_start: u.query_start.map_or(OMITTED, |q| q as u32),
        hash_start: u.fragment_start.map_or(OMITTED, |f| f as u32),
    }
}

fn new_handle(url: Option<Url>) -> *mut Handle {
    // Reuse the box the last `free` on this thread kept, if any.
    let mut bx = with_bufs(|b| b.spare.take()).unwrap_or_else(|| Box::new(Handle { url: None, comps: Default::default() }));
    fill(&mut bx, url);
    Box::into_raw(bx)
}

/// Puts `url` (or `None` if its href is over the length limit) in `h`.
#[inline(always)]
fn fill(h: &mut Handle, url: Option<Url>) {
    h.url = url;
    if h.url.as_ref().map_or(false, |u| u.href.len() > max_len()) {
        h.url = None;
    }
    h.comps = h.url.as_ref().map(components).unwrap_or_default();
}

/// Frees a handle, keeping its box and a small href buffer on this thread
/// for the next parse, which then allocates nothing.
unsafe fn free_handle(p: *mut Handle) {
    let mut bx = Box::from_raw(p);
    let url = bx.url.take();
    // During thread teardown the buffers may be gone; then just drop.
    let _ = BUFS.try_with(|c| {
        // SAFETY: as in `with_bufs`; nothing below re-enters it.
        let b = &mut *c.get();
        if let Some(u) = url {
            if b.sc.href.capacity() == 0 && u.href.capacity() <= 4096 {
                let mut v = u.href;
                v.clear();
                b.sc.href = v;
            }
        }
        if b.spare.is_none() {
            b.spare = Some(bx);
        }
    });
}

unsafe fn get<'a>(p: *mut Handle) -> Option<&'a Url> {
    p.as_ref().and_then(|h| h.url.as_ref())
}

/// Runs a setter on the handle's URL, keeping the old URL if the setter's
/// result is longer than the maximum input length.
///
/// `grow` bounds how much longer the setter can make the href; when even
/// that stays within the limit, no copy of the old URL is kept. (No setter
/// writes more than 64 bytes per input byte: percent-encoding triples a
/// byte, and the longest UTS #46 mapping is 18 code points.)
unsafe fn set(p: *mut Handle, input_len: usize, f: impl FnOnce(&mut Url) -> bool) -> bool {
    let Some(h) = p.as_mut() else { return false };
    let Some(u) = h.url.as_mut() else { return false };
    let bound = u.href.len().saturating_add(input_len.saturating_mul(64)).saturating_add(64);
    let saved = if bound > max_len() { Some(u.clone()) } else { None };
    let mut r = f(u);
    if u.href.len() > max_len() {
        if let Some(old) = saved {
            *u = old;
        }
        r = false;
    }
    h.comps = components(u);
    r
}

/// Whether `input` parses (against `base`) within the length limit. The
/// href is written into a per-thread buffer that is kept for the next call,
/// so this allocates nothing once warm.
fn can_parse_limited(input: &[u8], base: Option<&Url>) -> bool {
    if input.len() > max_len() {
        return false;
    }
    with_bufs(|b| match crate::api::parse_sc(input, base, &mut b.sc) {
        Some(u) => {
            let ok = u.href.len() <= max_len();
            // Keep a small href buffer for the next parse.
            if u.href.capacity() <= 4096 {
                b.sc.href = u.href;
            }
            ok
        },
        None => false,
    })
}

/// Per-thread buffers kept across calls: the host parser's scratch storage
/// (with a spare href buffer) and the buffer `hostname_after_set` hands
/// out, so that a call allocates nothing it does not return.
struct Bufs {
    sc: crate::host::Scratch,
    host: Vec<u8>,
    /// A freed handle's box, kept for the next `new_handle`.
    spare: Option<Box<Handle>>,
}

thread_local! {
    /// Only `with_bufs` touches it, and parsing never calls back into it.
    static BUFS: core::cell::UnsafeCell<Bufs> = const {
        core::cell::UnsafeCell::new(Bufs {
            sc: crate::host::Scratch { dec: Vec::new(), map: Vec::new(), href: Vec::new() },
            host: Vec::new(),
            spare: None,
        })
    };
}

/// Runs `f` with this thread's buffers. (The host parser drops large
/// scratch buffers itself; `can_parse_limited` keeps only a small href.) `f`
/// must not call `with_bufs` itself.
#[inline(always)]
fn with_bufs<R>(f: impl FnOnce(&mut Bufs) -> R) -> R {
    // SAFETY: this is the only reference to the cell's contents while it
    // lives, since `f` does not re-enter `with_bufs`.
    let b = unsafe { &mut *BUFS.with(|c| c.get()) };
    f(b)
}

fn parse_limited(input: &[u8], base: Option<&Url>) -> Option<Url> {
    if input.len() > max_len() {
        return None;
    }
    match with_bufs(|b| crate::api::parse_sc(input, base, &mut b.sc)) {
        Some(u) if u.href.len() > max_len() => None,
        r => r,
    }
}

fn utf8(b: &[u8]) -> std::borrow::Cow<'_, str> {
    // `from_utf8` has an ASCII fast path that `from_utf8_lossy` lacks.
    match core::str::from_utf8(b) {
        Ok(s) => std::borrow::Cow::Borrowed(s),
        Err(_) => String::from_utf8_lossy(b),
    }
}

macro_rules! export {
    ($(fn $name:ident($($a:ident: $t:ty),*) $(-> $r:ty)? $body:block)*) => {$(
        #[cfg_attr(feature = "ada-abi", unsafe(export_name = concat!("ada_", stringify!($name))))]
        #[cfg_attr(not(feature = "ada-abi"), unsafe(export_name = concat!("vurl_", stringify!($name))))]
        pub unsafe extern "C" fn $name($($a: $t),*) $(-> $r)? $body
    )*};
}

macro_rules! getter {
    ($($name:ident => $f:expr;)*) => {$(
        export! {
            fn $name(p: *mut Handle) -> AdaString {
                match get(p) {
                    Some(u) => {
                        let f: fn(&Url) -> &str = $f;
                        view(f(u).as_bytes())
                    }
                    None => NULL,
                }
            }
        }
    )*};
}

macro_rules! predicate {
    ($($name:ident => $f:expr;)*) => {$(
        export! {
            fn $name(p: *mut Handle) -> bool {
                let f: fn(&Url) -> bool = $f;
                get(p).map_or(false, f)
            }
        }
    )*};
}

macro_rules! setter {
    ($($name:ident => $f:ident;)*) => {$(
        export! {
            fn $name(p: *mut Handle, input: *const c_char, length: usize) -> bool {
                let v = utf8(bytes(input, length));
                set(p, length, |u| u.$f(&v))
            }
        }
    )*};
}

export! {
    fn parse(input: *const c_char, length: usize) -> *mut Handle {
        new_handle(parse_limited(bytes(input, length), None))
    }

    fn parse_with_base(input: *const c_char, input_length: usize, base: *const c_char, base_length: usize) -> *mut Handle {
        let url = parse_limited(bytes(base, base_length), None).and_then(|b| parse_limited(bytes(input, input_length), Some(&b)));
        new_handle(url)
    }

    fn can_parse(input: *const c_char, length: usize) -> bool {
        can_parse_limited(bytes(input, length), None)
    }

    fn can_parse_with_base(input: *const c_char, input_length: usize, base: *const c_char, base_length: usize) -> bool {
        parse_limited(bytes(base, base_length), None).map_or(false, |b| can_parse_limited(bytes(input, input_length), Some(&b)))
    }

    fn free(p: *mut Handle) {
        if !p.is_null() {
            free_handle(p);
        }
    }

    fn free_owned_string(s: AdaOwnedString) {
        if !s.data.is_null() {
            drop(Box::from_raw(core::ptr::slice_from_raw_parts_mut(s.data as *mut u8, s.length)));
        }
    }

    // `set_hostname` on a copy of `p`, which is left as it is: the
    // setter's result goes to `ok`, and the edited URL is returned as a
    // new handle, or null when it is the same as `p`'s.
    fn with_hostname(p: *mut Handle, input: *const c_char, length: usize, ok: *mut bool) -> *mut Handle {
        let mut r = false;
        let mut out = core::ptr::null_mut();
        if let Some(u) = get(p) {
            let v = utf8(bytes(input, length));
            let (res, nu) = u.with_hostname(&v);
            r = res;
            if let Some(nu) = nu {
                if nu.href.len() <= max_len() {
                    out = new_handle(Some(nu));
                } else {
                    r = false;
                }
            }
        }
        if !ok.is_null() {
            *ok = r;
        }
        out
    }

    // The host that `set_hostname` would give `p`, without making the new
    // URL: 1 when the setter succeeds, with the host in `*host` (a view that
    // stays valid until the next call of this function on this thread) and
    // its type (as `get_host_type`) in `*host_type`; 0 when the setter
    // fails; -1 when this shortcut does not apply, and `with_hostname` is
    // needed instead.
    fn hostname_after_set(p: *mut Handle, input: *const c_char, length: usize, host: *mut AdaString, host_type: *mut u8) -> i32 {
        use crate::host::HostKind;
        let Some(u) = get(p) else { return 0 };
        let v = utf8(bytes(input, length));
        // The host stays in this thread's buffer until the next call.
        with_bufs(|b| {
            let out = &mut b.host;
            match u.hostname_host_in(&v, out, &mut b.sc) {
                None => -1,
                Some(None) => 0,
                // The new href is at most this long; past the length limit,
                // `with_hostname` decides.
                Some(Some(_)) if u.href.len().saturating_add(out.len()).saturating_add(2) > max_len() => -1,
                Some(Some(k)) => {
                    if !host.is_null() {
                        *host = view(out);
                    }
                    if !host_type.is_null() {
                        *host_type = match k {
                            HostKind::Ipv4 => 1,
                            HostKind::Ipv6 => 2,
                            _ => 0,
                        };
                    }
                    1
                }
            }
        })
    }

    fn copy(p: *mut Handle) -> *mut Handle {
        match p.as_ref() {
            // The components are already computed; only a URL over a since
            // lowered length limit needs `new_handle`'s check.
            Some(h) if h.url.as_ref().map_or(true, |u| u.href.len() <= max_len()) => {
                Box::into_raw(Box::new(Handle { url: h.url.clone(), comps: h.comps }))
            }
            Some(h) => new_handle(h.url.clone()),
            None => new_handle(None),
        }
    }

    fn is_valid(p: *mut Handle) -> bool {
        get(p).is_some()
    }

    fn get_origin(p: *mut Handle) -> AdaOwnedString {
        match get(p) {
            Some(u) => owned(u.origin().into_bytes()),
            None => AdaOwnedString { data: core::ptr::null(), length: 0 },
        }
    }

    fn get_port(p: *mut Handle) -> AdaString {
        match get(p) {
            Some(u) if u.port.is_some() => view(&u.href[u.host_end + 1..u.path_start]),
            Some(u) => view(&u.href[u.href.len()..]),
            None => NULL,
        }
    }

    fn get_host_type(p: *mut Handle) -> u8 {
        use crate::host::HostKind;
        match get(p).and_then(|u| u.host_kind) {
            Some(HostKind::Ipv4) => 1,
            Some(HostKind::Ipv6) => 2,
            _ => 0,
        }
    }

    fn get_scheme_type(p: *mut Handle) -> u8 {
        match get(p).map(|u| u.scheme()) {
            None | Some("http") => 0,
            Some("https") => 2,
            Some("ws") => 3,
            Some("ftp") => 4,
            Some("wss") => 5,
            Some("file") => 6,
            Some(_) => 1,
        }
    }

    fn set_search(p: *mut Handle, input: *const c_char, length: usize) {
        let v = utf8(bytes(input, length));
        set(p, length, |u| {
            u.set_search(&v);
            true
        });
    }

    fn set_hash(p: *mut Handle, input: *const c_char, length: usize) {
        let v = utf8(bytes(input, length));
        set(p, length, |u| {
            u.set_hash(&v);
            true
        });
    }

    fn clear_port(p: *mut Handle) {
        set(p, 0, |u| u.set_port(""));
    }

    fn clear_hash(p: *mut Handle) {
        set(p, 0, |u| {
            u.set_hash("");
            true
        });
    }

    fn clear_search(p: *mut Handle) {
        set(p, 0, |u| {
            u.set_search("");
            true
        });
    }

    fn get_components(p: *mut Handle) -> *const AdaUrlComponents {
        match p.as_ref() {
            Some(h) if h.url.is_some() => &h.comps,
            _ => core::ptr::null(),
        }
    }

    fn idna_to_unicode(input: *const c_char, length: usize) -> AdaOwnedString {
        // As ada does: each ASCII "xn--" label that decodes to a valid
        // non-ASCII label is decoded, and every other label is kept as it is.
        let s = utf8(bytes(input, length));
        if !s.contains("xn--") {
            return owned(s.into_owned().into_bytes());
        }
        let mut out = String::with_capacity(s.len());
        for (i, label) in s.split('.').enumerate() {
            if i > 0 {
                out.push('.');
            }
            if !(label.starts_with("xn--") && label.is_ascii()) {
                out.push_str(label);
                continue;
            }
            match verilith_text::idna::domain_to_unicode(label) {
                (u, Ok(())) if !u.is_ascii() => out.push_str(&u),
                _ => out.push_str(label),
            }
        }
        owned(out.into_bytes())
    }

    fn idna_to_ascii(input: *const c_char, length: usize) -> AdaOwnedString {
        let s = utf8(bytes(input, length));
        // Not vtext's domain_to_ascii: its shortcut returns lowercase ASCII
        // as it is, without checking xn-- labels, and ada rejects invalid ones.
        owned(
            verilith_text::idna::to_ascii(&s, verilith_text::idna::Options::URL)
                .map(String::into_bytes)
                .unwrap_or_default(),
        )
    }

    fn set_max_input_length(length: u32) {
        MAX_INPUT_LENGTH.store(length, Ordering::Relaxed);
    }

    fn get_max_input_length() -> u32 {
        MAX_INPUT_LENGTH.load(Ordering::Relaxed)
    }

    fn get_version() -> *const c_char {
        concat!(env!("CARGO_PKG_VERSION"), "\0").as_ptr() as *const c_char
    }

    fn get_version_components() -> AdaVersionComponents {
        let n = |s: &str| s.parse().unwrap_or(0);
        AdaVersionComponents {
            major: n(env!("CARGO_PKG_VERSION_MAJOR")),
            minor: n(env!("CARGO_PKG_VERSION_MINOR")),
            revision: n(env!("CARGO_PKG_VERSION_PATCH")),
        }
    }
}

getter! {
    get_href => |u| u.href();
    get_username => |u| u.username();
    get_password => |u| u.password();
    get_hash => |u| u.hash();
    get_host => |u| u.host();
    get_hostname => |u| u.hostname();
    get_pathname => |u| u.pathname();
    get_search => |u| u.search();
    get_protocol => |u| u.protocol();
}

setter! {
    set_href => set_href;
    set_host => set_host;
    set_hostname => set_hostname;
    set_protocol => set_protocol;
    set_username => set_username;
    set_password => set_password;
    set_port => set_port;
    set_pathname => set_pathname;
}

predicate! {
    has_credentials => |u| !u.username().is_empty() || !u.password().is_empty();
    has_empty_hostname => |u| u.has_authority() && u.hostname().is_empty();
    has_hostname => |u| u.has_authority();
    has_non_empty_username => |u| !u.username().is_empty();
    has_non_empty_password => |u| !u.password().is_empty();
    has_port => |u| u.port.is_some();
    has_password => |u| !u.password().is_empty();
    has_hash => |u| u.fragment_start.is_some();
    has_search => |u| u.query_start.is_some();
}

// URLSearchParams.

/// Iterator over a search params list. Like ada's, it borrows the list,
/// which must outlive it.
pub struct ParamsIter {
    params: *const UrlSearchParams,
    pos: usize,
}

impl ParamsIter {
    unsafe fn next(&mut self) -> Option<&(Vec<u8>, Vec<u8>)> {
        let l = &self.params.as_ref()?.list;
        let r = l.get(self.pos);
        if r.is_some() {
            self.pos += 1;
        }
        r
    }

    unsafe fn has_next(&self) -> bool {
        self.params.as_ref().map_or(false, |p| self.pos < p.list.len())
    }
}

unsafe fn params<'a>(p: *mut UrlSearchParams) -> Option<&'a mut UrlSearchParams> {
    p.as_mut()
}

fn new_iter(p: *mut UrlSearchParams) -> *mut ParamsIter {
    Box::into_raw(Box::new(ParamsIter { params: p, pos: 0 }))
}

export! {
    fn parse_search_params(input: *const c_char, length: usize) -> *mut UrlSearchParams {
        let b = bytes(input, length);
        let p = if b.len() > max_len() { UrlSearchParams::default() } else { UrlSearchParams::parse(b) };
        Box::into_raw(Box::new(p))
    }

    fn free_search_params(p: *mut UrlSearchParams) {
        if !p.is_null() {
            drop(Box::from_raw(p));
        }
    }

    fn search_params_size(p: *mut UrlSearchParams) -> usize {
        params(p).map_or(0, |p| p.len())
    }

    fn search_params_sort(p: *mut UrlSearchParams) {
        if let Some(p) = params(p) {
            p.sort();
        }
    }

    fn search_params_to_string(p: *mut UrlSearchParams) -> AdaOwnedString {
        match params(p) {
            Some(p) => owned(p.to_bytes()),
            None => AdaOwnedString { data: core::ptr::null(), length: 0 },
        }
    }

    fn search_params_append(p: *mut UrlSearchParams, key: *const c_char, key_length: usize, value: *const c_char, value_length: usize) {
        if let Some(p) = params(p) {
            p.append(bytes(key, key_length), bytes(value, value_length));
        }
    }

    fn search_params_set(p: *mut UrlSearchParams, key: *const c_char, key_length: usize, value: *const c_char, value_length: usize) {
        if let Some(p) = params(p) {
            p.set(bytes(key, key_length), bytes(value, value_length));
        }
    }

    fn search_params_remove(p: *mut UrlSearchParams, key: *const c_char, key_length: usize) {
        if let Some(p) = params(p) {
            p.remove(bytes(key, key_length));
        }
    }

    fn search_params_remove_value(p: *mut UrlSearchParams, key: *const c_char, key_length: usize, value: *const c_char, value_length: usize) {
        if let Some(p) = params(p) {
            p.remove_value(bytes(key, key_length), bytes(value, value_length));
        }
    }

    fn search_params_has(p: *mut UrlSearchParams, key: *const c_char, key_length: usize) -> bool {
        params(p).map_or(false, |p| p.has(bytes(key, key_length)))
    }

    fn search_params_has_value(p: *mut UrlSearchParams, key: *const c_char, key_length: usize, value: *const c_char, value_length: usize) -> bool {
        params(p).map_or(false, |p| p.has_value(bytes(key, key_length), bytes(value, value_length)))
    }

    fn search_params_get(p: *mut UrlSearchParams, key: *const c_char, key_length: usize) -> AdaString {
        match params(p).and_then(|p| p.get(bytes(key, key_length))) {
            Some(v) => view(v),
            None => NULL,
        }
    }

    fn search_params_get_all(p: *mut UrlSearchParams, key: *const c_char, key_length: usize) -> *mut Vec<Vec<u8>> {
        let all = params(p).map(|p| p.get_all(bytes(key, key_length))).unwrap_or_default();
        Box::into_raw(Box::new(all))
    }

    fn search_params_reset(p: *mut UrlSearchParams, input: *const c_char, length: usize) {
        if let Some(p) = params(p) {
            let b = bytes(input, length);
            if b.len() > max_len() {
                p.list.clear();
            } else {
                p.reset(b);
            }
        }
    }

    fn search_params_get_keys(p: *mut UrlSearchParams) -> *mut ParamsIter {
        new_iter(p)
    }

    fn search_params_get_values(p: *mut UrlSearchParams) -> *mut ParamsIter {
        new_iter(p)
    }

    fn search_params_get_entries(p: *mut UrlSearchParams) -> *mut ParamsIter {
        new_iter(p)
    }

    fn free_strings(p: *mut Vec<Vec<u8>>) {
        if !p.is_null() {
            drop(Box::from_raw(p));
        }
    }

    fn strings_size(p: *mut Vec<Vec<u8>>) -> usize {
        p.as_ref().map_or(0, |v| v.len())
    }

    fn strings_get(p: *mut Vec<Vec<u8>>, index: usize) -> AdaString {
        match p.as_ref().and_then(|v| v.get(index)) {
            Some(s) => view(s),
            None => NULL,
        }
    }

    fn free_search_params_keys_iter(p: *mut ParamsIter) {
        if !p.is_null() {
            drop(Box::from_raw(p));
        }
    }

    fn search_params_keys_iter_next(p: *mut ParamsIter) -> AdaString {
        match p.as_mut().and_then(|i| i.next()) {
            Some((k, _)) => view(k),
            None => NULL,
        }
    }

    fn search_params_keys_iter_has_next(p: *mut ParamsIter) -> bool {
        p.as_ref().map_or(false, |i| i.has_next())
    }

    fn free_search_params_values_iter(p: *mut ParamsIter) {
        if !p.is_null() {
            drop(Box::from_raw(p));
        }
    }

    fn search_params_values_iter_next(p: *mut ParamsIter) -> AdaString {
        match p.as_mut().and_then(|i| i.next()) {
            Some((_, v)) => view(v),
            None => NULL,
        }
    }

    fn search_params_values_iter_has_next(p: *mut ParamsIter) -> bool {
        p.as_ref().map_or(false, |i| i.has_next())
    }

    fn free_search_params_entries_iter(p: *mut ParamsIter) {
        if !p.is_null() {
            drop(Box::from_raw(p));
        }
    }

    fn search_params_entries_iter_next(p: *mut ParamsIter) -> AdaStringPair {
        match p.as_mut().and_then(|i| i.next()) {
            Some((k, v)) => AdaStringPair { key: view(k), value: view(v) },
            None => AdaStringPair { key: NULL, value: NULL },
        }
    }

    fn search_params_entries_iter_has_next(p: *mut ParamsIter) -> bool {
        p.as_ref().map_or(false, |i| i.has_next())
    }
}
