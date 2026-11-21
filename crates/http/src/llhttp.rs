//! llhttp's parser, on vhttp's verified streaming head machine
//! (`stream.rs`) and chunked decoder (`chunked.rs`).
//!
//! llhttp is a generated state machine (`llhttp.c`) behind a small C API
//! (`api.c`, `http.c`). This module replaces only the generated part: it
//! exports `llhttp__internal_init` and `llhttp__internal_execute`, and
//! calls back into llhttp's own `api.c` and `http.c` for the callbacks and
//! for the upgrade and keep-alive rules. Built with `--features
//! llhttp-abi` and linked with those two files, it is a drop-in for llhttp
//! (Node.js's HTTP parser).
//!
//! This file is not verified. It moves bytes, calls callbacks, keeps
//! spans and pauses, and adds llhttp's own rejections (method names, URL
//! rules, `Connection` and `Upgrade`). What it decides about a head it
//! decides by calling the verified `llcore.rs`: each step on a wire byte
//! (`lstep_exec`, `l09_exec`, `lbulk_exec`), the one-shot path
//! (`fast_head_exec`), what follows a complete head (`after_head_exec`)
//! and how the machine state is packed between calls. `llproof.rs` proves
//! what those decisions amount to; three llhttp behaviours go beyond the
//! machines' HTTP/1.x grammar, and they are spelled out there: HTTP/0.9
//! and HTTP/2.0 heads (and a request line with no version, which llhttp
//! takes as HTTP/0.9) are checked as HTTP/1.0 heads and report their real
//! version; a request whose Transfer-Encoding does not end in `chunked`
//! reaches `on_headers_complete` before it is rejected (`deferred_te`);
//! and with the `llhttp-lenient` feature, a parser with lenient flags set (Node's
//! `--insecure-http-parser`) runs on llhttp's own generated parser, since
//! lenient modes accept what the verified grammar rejects by design.
//!
//! The parser keeps all of its state in the caller's `llhttp_t`, which
//! has no destructor, so nothing is ever allocated.
use crate::chunked::{step_exec, CState};
use crate::framing::FieldsExec;
use crate::llcore::*;
use crate::parse::{Header, Span};
use crate::spec::{Body, TeState};
use crate::stream::*;
use core::ffi::{c_char, c_int, c_void};

/// `llhttp_t`, laid out as in `llhttp.h`.
#[repr(C)]
pub struct LlhttpT {
    _index: i32,
    _span_pos0: usize,
    _span_cb0: usize,
    error: i32,
    reason: *const c_char,
    error_pos: *const c_char,
    data: *mut c_void,
    _current: usize,
    content_length: u64,
    type_: u8,
    method: u8,
    http_major: u8,
    http_minor: u8,
    header_state: u8,
    lenient_flags: u16,
    upgrade: u8,
    finish: u8,
    flags: u16,
    status_code: u16,
    initial_message_completed: u8,
    settings: *mut c_void,
}

/// The adapter's state between calls is three 64-bit words. On 64-bit
/// targets they live in `_span_cb0`, `_current` and `_span_pos0`, which
/// llhttp's generated parser owns and nothing else reads. On 32-bit targets
/// (wasm32, for undici) those fields are too small, so the words live in a
/// table keyed by the parser's address; all-zero words are not stored.
/// `llhttp__internal_init` (so `llhttp_init` and `llhttp_reset`) clears the
/// entry, and `forget` drops it when the parser's memory is freed.
impl LlhttpT {
    #[cfg(target_pointer_width = "64")]
    #[inline(always)]
    fn words(&self) -> [u64; 3] {
        [self._span_cb0 as u64, self._current as u64, self._span_pos0 as u64]
    }

    #[cfg(target_pointer_width = "64")]
    #[inline(always)]
    fn set_words(&mut self, w: [u64; 3]) {
        self._span_cb0 = w[0] as usize;
        self._current = w[1] as usize;
        self._span_pos0 = w[2] as usize;
    }

    #[cfg(not(target_pointer_width = "64"))]
    fn words(&self) -> [u64; 3] {
        let key = self as *const LlhttpT as usize;
        side::table().get(&key).copied().unwrap_or([0, 0, 0])
    }

    #[cfg(not(target_pointer_width = "64"))]
    fn set_words(&mut self, w: [u64; 3]) {
        let key = self as *const LlhttpT as usize;
        let mut t = side::table();
        if w == [0, 0, 0] {
            t.remove(&key);
        } else {
            t.insert(key, w);
        }
    }
}

#[cfg(not(target_pointer_width = "64"))]
mod side {
    use std::collections::HashMap;
    use std::sync::{Mutex, MutexGuard, OnceLock};

    static T: OnceLock<Mutex<HashMap<usize, [u64; 3]>>> = OnceLock::new();

    pub fn table() -> MutexGuard<'static, HashMap<usize, [u64; 3]>> {
        T.get_or_init(|| Mutex::new(HashMap::new())).lock().unwrap_or_else(|e| e.into_inner())
    }
}

/// Drops the state kept for the parser at `p` on a 32-bit target, for an
/// allocator to call when `p` is freed (`llhttp_free`). A no-op on 64-bit
/// targets and for addresses that hold no parser.
pub fn forget(p: *const c_void) {
    #[cfg(not(target_pointer_width = "64"))]
    {
        side::table().remove(&(p as usize));
    }
    let _ = p;
}

type Hook = unsafe extern "C" fn(*mut LlhttpT, *const u8, *const u8) -> c_int;

extern "C" {
    fn llhttp__on_message_begin(s: *mut LlhttpT, p: *const u8, e: *const u8) -> c_int;
    fn llhttp__on_reset(s: *mut LlhttpT, p: *const u8, e: *const u8) -> c_int;
    fn llhttp__on_method(s: *mut LlhttpT, p: *const u8, e: *const u8) -> c_int;
    fn llhttp__on_method_complete(s: *mut LlhttpT, p: *const u8, e: *const u8) -> c_int;
    fn llhttp__on_url(s: *mut LlhttpT, p: *const u8, e: *const u8) -> c_int;
    fn llhttp__on_url_complete(s: *mut LlhttpT, p: *const u8, e: *const u8) -> c_int;
    fn llhttp__on_protocol(s: *mut LlhttpT, p: *const u8, e: *const u8) -> c_int;
    fn llhttp__on_protocol_complete(s: *mut LlhttpT, p: *const u8, e: *const u8) -> c_int;
    fn llhttp__on_version(s: *mut LlhttpT, p: *const u8, e: *const u8) -> c_int;
    fn llhttp__on_version_complete(s: *mut LlhttpT, p: *const u8, e: *const u8) -> c_int;
    fn llhttp__on_status(s: *mut LlhttpT, p: *const u8, e: *const u8) -> c_int;
    fn llhttp__on_status_complete(s: *mut LlhttpT, p: *const u8, e: *const u8) -> c_int;
    fn llhttp__on_header_field(s: *mut LlhttpT, p: *const u8, e: *const u8) -> c_int;
    fn llhttp__on_header_field_complete(s: *mut LlhttpT, p: *const u8, e: *const u8) -> c_int;
    fn llhttp__on_header_value(s: *mut LlhttpT, p: *const u8, e: *const u8) -> c_int;
    fn llhttp__on_header_value_complete(s: *mut LlhttpT, p: *const u8, e: *const u8) -> c_int;
    fn llhttp__on_headers_complete(s: *mut LlhttpT, p: *const u8, e: *const u8) -> c_int;
    fn llhttp__on_body(s: *mut LlhttpT, p: *const u8, e: *const u8) -> c_int;
    fn llhttp__on_message_complete(s: *mut LlhttpT, p: *const u8, e: *const u8) -> c_int;
    fn llhttp__on_chunk_header(s: *mut LlhttpT, p: *const u8, e: *const u8) -> c_int;
    fn llhttp__on_chunk_extension_name(s: *mut LlhttpT, p: *const u8, e: *const u8) -> c_int;
    fn llhttp__on_chunk_complete(s: *mut LlhttpT, p: *const u8, e: *const u8) -> c_int;
    fn llhttp__before_headers_complete(s: *mut LlhttpT, p: *const u8, e: *const u8) -> c_int;
    fn llhttp__after_headers_complete(s: *mut LlhttpT, p: *const u8, e: *const u8) -> c_int;
    fn llhttp__after_message_complete(s: *mut LlhttpT, p: *const u8, e: *const u8) -> c_int;
}

// llhttp_errno
const HPE_OK: i32 = 0;
const HPE_LF_EXPECTED: i32 = 3;
const HPE_UNEXPECTED_CONTENT_LENGTH: i32 = 4;
const HPE_CLOSED_CONNECTION: i32 = 5;
const HPE_INVALID_METHOD: i32 = 6;
const HPE_INVALID_URL: i32 = 7;
const HPE_INVALID_CONSTANT: i32 = 8;
const HPE_INVALID_VERSION: i32 = 9;
const HPE_INVALID_HEADER_TOKEN: i32 = 10;
const HPE_INVALID_CONTENT_LENGTH: i32 = 11;
const HPE_INVALID_CHUNK_SIZE: i32 = 12;
const HPE_STRICT: i32 = 2;
const HPE_INVALID_STATUS: i32 = 13;
const HPE_INVALID_TRANSFER_ENCODING: i32 = 15;
const HPE_CB_MESSAGE_BEGIN: i32 = 16;
const HPE_CB_HEADERS_COMPLETE: i32 = 17;
const HPE_CB_MESSAGE_COMPLETE: i32 = 18;
const HPE_CB_CHUNK_HEADER: i32 = 19;
const HPE_CB_CHUNK_COMPLETE: i32 = 20;
const HPE_PAUSED: i32 = 21;
const HPE_PAUSED_UPGRADE: i32 = 22;
const HPE_PAUSED_H2_UPGRADE: i32 = 23;
const HPE_USER: i32 = 24;
const HPE_CB_RESET: i32 = 31;

// llhttp_flags
const F_CONNECTION_KEEP_ALIVE: u16 = 0x1;
const F_CONNECTION_CLOSE: u16 = 0x2;
const F_CONNECTION_UPGRADE: u16 = 0x4;
const F_CHUNKED: u16 = 0x8;
const F_UPGRADE: u16 = 0x10;
const F_CONTENT_LENGTH: u16 = 0x20;
const F_SKIPBODY: u16 = 0x40;
const F_TRAILING: u16 = 0x80;
const F_TRANSFER_ENCODING: u16 = 0x200;

const HTTP_REQUEST: u8 = 1;

/// The method names llhttp accepts in HTTP mode, with their numbers.
const METHODS: [(&[u8], u8); 47] = [
    (b"DELETE", 0), (b"GET", 1), (b"HEAD", 2), (b"POST", 3), (b"PUT", 4), (b"CONNECT", 5),
    (b"OPTIONS", 6), (b"TRACE", 7), (b"COPY", 8), (b"LOCK", 9), (b"MKCOL", 10), (b"MOVE", 11),
    (b"PROPFIND", 12), (b"PROPPATCH", 13), (b"SEARCH", 14), (b"UNLOCK", 15), (b"BIND", 16),
    (b"REBIND", 17), (b"UNBIND", 18), (b"ACL", 19), (b"REPORT", 20), (b"MKACTIVITY", 21),
    (b"CHECKOUT", 22), (b"MERGE", 23), (b"M-SEARCH", 24), (b"NOTIFY", 25), (b"SUBSCRIBE", 26),
    (b"UNSUBSCRIBE", 27), (b"PATCH", 28), (b"PURGE", 29), (b"MKCALENDAR", 30), (b"LINK", 31),
    (b"UNLINK", 32), (b"SOURCE", 33), (b"QUERY", 46),
    // llhttp also knows these (RTSP, ICE and the HTTP/2 preface); they
    // matter only for where an unknown method is reported.
    (b"PRI", NOT_HTTP), (b"DESCRIBE", NOT_HTTP), (b"ANNOUNCE", NOT_HTTP), (b"SETUP", NOT_HTTP),
    (b"PLAY", NOT_HTTP), (b"PAUSE", NOT_HTTP), (b"TEARDOWN", NOT_HTTP),
    (b"GET_PARAMETER", NOT_HTTP), (b"SET_PARAMETER", NOT_HTTP), (b"REDIRECT", NOT_HTTP),
    (b"RECORD", NOT_HTTP), (b"FLUSH", NOT_HTTP),
];
const NOT_HTTP: u8 = 255;
const ALL_METHODS: u64 = (1u64 << 47) - 1;

/// What the parser is doing.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Head = 0,
    Identity = 1,
    Chunked = 2,
    Eof = 3,
    Closed = 4,
    Upgraded = 5,
}

/// Names the adapter tracks for llhttp's own flags (not for framing).
const H_CONNECTION: u8 = 1;
const H_UPGRADE: u8 = 2;

/// Adapter state, unpacked from the private fields of `llhttp_t` at the
/// start of `execute` and packed back at the end.
#[derive(Clone, Copy)]
struct St {
    mode: Mode,
    hs: HS,
    cs: CState,
    /// `on_message_begin` was called for the current message.
    begun: bool,
    /// A value span was emitted for the current field line.
    val_emitted: bool,
    /// The current value has started (past leading OWS).
    val_started: bool,
    /// Method candidates (bit i: `METHODS[i]`) and bytes matched.
    meth: u64,
    mlen: u8,
    /// Which tracked header the current line is (`H_*`), and the matcher
    /// for its name: bytes so far and candidates.
    hkind: u8,
    nlen: u8,
    ncand: u8,
    /// Connection-token matcher: bytes so far, candidates (1 close,
    /// 2 keep-alive, 4 upgrade), and whether the current token is dead.
    tlen: u8,
    tcand: u8,
    /// Flags gathered from Connection and Upgrade lines.
    cflags: u16,
    /// Where in the request target the URL check is (`url_step`).
    ustage: u8,
    /// A Content-Length line came before any Transfer-Encoding line.
    cl_first: bool,
    /// The version, when it is not 1.x (`llcore::VER_*`).
    ver: u8,
    /// How much of the request target matches an HTTP/1.x version
    /// (`llcore::LS::tv`).
    tv: u8,
}

fn start_hs(req: bool) -> HS {
    HS {
        ph: if req { Ph::RStart } else { Ph::SVer { k: 0 } },
        f: FieldsExec { cl: None, te: TeState { present: false, chunked_last: false }, hosts: 0 },
        minor: 0,
        status: 0,
        req,
        host: false,
    }
}

impl St {
    fn fresh(req: bool) -> St {
        St {
            mode: Mode::Head,
            hs: start_hs(req),
            cs: CState::SizeStart,
            begun: false,
            val_emitted: false,
            val_started: false,
            meth: ALL_METHODS,
            mlen: 0,
            hkind: 0,
            nlen: 0,
            ncand: 0,
            tlen: 0,
            tcand: 0,
            cflags: 0,
            ustage: 0,
            cl_first: false,
            ver: 0,
            tv: 0,
        }
    }

    /// Reads the state. An all-zero `llhttp_t` (after `llhttp_init`) is
    /// the start of a message.
    fn load(p: &LlhttpT) -> St {
        let req = p.type_ == HTTP_REQUEST;
        let w = p.words();
        let b = w[0].to_le_bytes();
        let c = w[1].to_le_bytes();
        if b[0] & 0x80 == 0 {
            return St::fresh(req);
        }
        let mode = match b[0] & 7 {
            0 => Mode::Head,
            1 => Mode::Identity,
            2 => Mode::Chunked,
            3 => Mode::Eof,
            4 => Mode::Closed,
            _ => Mode::Upgraded,
        };
        let misc = b[4];
        let cl_present = misc & 8 != 0;
        let in_chunked = mode == Mode::Chunked;
        let in_method = b[1] == 2 && mode == Mode::Head;
        let wide = if in_chunked || in_method { 0 } else { w[2] };
        let ph = ph_unpack(b[1], b[2], b[3], wide);
        St {
            mode,
            hs: HS {
                ph,
                f: FieldsExec {
                    cl: if cl_present { Some(p.content_length) } else { None },
                    te: TeState { present: misc & 16 != 0, chunked_last: misc & 32 != 0 },
                    hosts: b[5] & 3,
                },
                minor: b[6],
                status: p.status_code,
                req,
                host: false,
            },
            cs: if in_chunked { cs_unpack(b[7], w[2]) } else { CState::SizeStart },
            begun: misc & 1 != 0,
            val_emitted: misc & 2 != 0,
            val_started: misc & 4 != 0,
            meth: if in_method { w[2] } else { ALL_METHODS },
            mlen: c[5],
            hkind: (b[5] >> 2) & 3,
            nlen: c[0],
            ncand: c[1],
            tlen: c[2],
            tcand: c[3],
            cflags: u16::from_le_bytes([c[6], c[7]]),
            ustage: c[4],
            cl_first: misc & 64 != 0,
            ver: (b[5] >> 4) & 3,
            tv: (b[0] >> 3) & 15,
        }
    }

    fn store(&self, p: &mut LlhttpT) {
        let (tag, small, bits, wide) = ph_pack(self.hs.ph);
        let (ct, cn) = cs_pack(self.cs);
        let misc = self.begun as u8
            | (self.val_emitted as u8) << 1
            | (self.val_started as u8) << 2
            | (self.hs.f.cl.is_some() as u8) << 3
            | (self.hs.f.te.present as u8) << 4
            | (self.hs.f.te.chunked_last as u8) << 5
            | (self.cl_first as u8) << 6;
        let b = [
            0x80 | self.mode as u8 | (self.tv & 15) << 3,
            tag,
            small,
            bits,
            misc,
            (self.hs.f.hosts & 3) | (self.hkind & 3) << 2 | (self.ver & 3) << 4,
            self.hs.minor,
            ct,
        ];
        let w0 = u64::from_le_bytes(b);
        let cf = self.cflags.to_le_bytes();
        let w1 =
            u64::from_le_bytes([self.nlen, self.ncand, self.tlen, self.tcand, self.ustage, self.mlen, cf[0], cf[1]]);
        let w2 = match self.mode {
            Mode::Chunked => cn,
            _ if matches!(self.hs.ph, Ph::Method) => self.meth,
            _ => wide,
        };
        p.set_words([w0, w1, w2]);
        if let Some(n) = self.hs.f.cl {
            if self.mode == Mode::Head {
                p.content_length = n;
            }
        }
        if self.mode == Mode::Head {
            p.status_code = self.hs.status;
        }
    }
}

fn lower(c: u8) -> u8 {
    c.to_ascii_lowercase()
}

/// Steps the tracked-name matcher (`connection`, `upgrade`).
fn name_track(st: &mut St, c: u8) {
    const NAMES: [&[u8]; 3] = [b"connection", b"upgrade", b"proxy-connection"];
    if st.nlen == 0 {
        st.ncand = 7;
    }
    let i = st.nlen as usize;
    for (k, n) in NAMES.iter().enumerate() {
        if st.ncand & (1 << k) != 0 && (i >= n.len() || n[i] != lower(c)) {
            st.ncand &= !(1 << k);
        }
    }
    st.nlen = st.nlen.saturating_add(1);
}

fn name_kind(st: &St) -> u8 {
    if (st.ncand & 1 != 0 && st.nlen == 10) || (st.ncand & 4 != 0 && st.nlen == 16) {
        H_CONNECTION
    } else if st.ncand & 2 != 0 && st.nlen == 7 {
        H_UPGRADE
    } else {
        0
    }
}

/// Steps the Connection token matcher; `c` is a value byte or `None` at
/// the end of the value.
fn token_track(st: &mut St, c: Option<u8>) {
    const TOKENS: [&[u8]; 3] = [b"close", b"keep-alive", b"upgrade"];
    const FLAGS: [u16; 3] = [F_CONNECTION_CLOSE, F_CONNECTION_KEEP_ALIVE, F_CONNECTION_UPGRADE];
    let end = match c {
        None | Some(b',') => true,
        _ => false,
    };
    if end {
        for k in 0..3 {
            if st.tcand & (1 << k) != 0 && st.tlen as usize == TOKENS[k].len() {
                st.cflags |= FLAGS[k];
            }
        }
        st.tlen = 0;
        st.tcand = 0;
        return;
    }
    let c = c.unwrap();
    if c == b' ' || c == b'\t' {
        if st.tlen != 0 {
            // Whitespace after a token: it ends unless a comma follows.
            st.tcand |= 0x80;
        }
        return;
    }
    if st.tlen == 0 && st.tcand & 0x80 == 0 {
        st.tcand = 7;
    }
    if st.tcand & 0x80 != 0 {
        // A second word in one element: not a token we know.
        st.tcand = 0x80;
    }
    let i = st.tlen as usize;
    for k in 0..3 {
        if st.tcand & (1 << k) != 0 && (i >= TOKENS[k].len() || TOKENS[k][i] != lower(c)) {
            st.tcand &= !(1 << k);
        }
    }
    st.tlen = st.tlen.saturating_add(1);
}

/// The flags a whole Connection value sets: what `token_track` computes
/// byte by byte. An element counts when, without its OWS, it is one of
/// the tokens.
fn conn_flags(v: &[u8]) -> u16 {
    let mut f = 0;
    for e in v.split(|&c| c == b',') {
        let mut a = 0;
        let mut z = e.len();
        while a < z && (e[a] == b' ' || e[a] == b'\t') {
            a += 1;
        }
        while z > a && (e[z - 1] == b' ' || e[z - 1] == b'\t') {
            z -= 1;
        }
        let t = &e[a..z];
        // Field values have no CTLs, so OR-ing 0x20 compares with these
        // lowercase-and-`-` literals case-insensitively (as in
        // `fast_parse`).
        match t.len() {
            5 if lc4(t, 0) == lit4(b"clos") && t[4] | 0x20 == b'e' => f |= F_CONNECTION_CLOSE,
            10 if lc8(t, 0) == lit8(b"keep-ali") && lc2(t, 8) == lit2(b"ve") => f |= F_CONNECTION_KEEP_ALIVE,
            7 if lc4(t, 0) == lit4(b"upgr") && lc4(t, 3) == lit4(b"rade") => f |= F_CONNECTION_UPGRADE,
            _ => {}
        }
    }
    f
}

/// llhttp's request-target rules, which are stricter than RFC 9112's (and
/// so than the verified grammar): no bytes above 0x7E, an origin-form or
/// `*` target, an absolute URL with a letters-only scheme, or for CONNECT
/// a plain authority. This accepts a subset of what llhttp accepts.
/// Stages: 0 start, 1 path, 2 scheme, 3 after `:`, 4 after `:/`,
/// 5 authority of an absolute URL, 6 CONNECT authority.
fn url_step(ustage: &mut u8, connect: bool, c: u8) -> bool {
    const SERVER: &[u8] = b"-._~!$&'()*+,;=:@[]%";
    if !(0x21..=0x7E).contains(&c) {
        return false;
    }
    let alnum = c.is_ascii_alphanumeric();
    *ustage = match *ustage {
        0 if c == b'/' || c == b'*' => 1,
        0 if connect && (alnum || b"-._:[]".contains(&c)) => 6,
        0 if !connect && c.is_ascii_alphabetic() => 2,
        1 => 1,
        2 if c.is_ascii_alphabetic() => 2,
        2 if c == b':' => 3,
        3 if c == b'/' => 4,
        4 if c == b'/' => 5,
        5 if c == b'/' || c == b'?' => 1,
        5 if alnum || SERVER.contains(&c) => 5,
        6 if alnum || b"-._:[]".contains(&c) => 6,
        _ => return false,
    };
    true
}

fn method_step(st: &mut St, c: u8) {
    let i = st.mlen as usize;
    let mut m = st.meth;
    let mut bits = m;
    while bits != 0 {
        let k = bits.trailing_zeros() as usize;
        bits &= bits - 1;
        let name = METHODS[k].0;
        if i >= name.len() || name[i] != c {
            m &= !(1 << k);
        }
    }
    st.meth = m;
    st.mlen = st.mlen.saturating_add(1);
}

/// The number of an HTTP method name, for the one-shot path (the
/// `METHODS` entries other than `NOT_HTTP`).
#[inline]
fn method_code(name: &[u8]) -> Option<u8> {
    Some(match name {
        b"GET" => 1,
        b"POST" => 3,
        b"PUT" => 4,
        b"HEAD" => 2,
        b"DELETE" => 0,
        b"OPTIONS" => 6,
        b"PATCH" => 28,
        b"CONNECT" => 5,
        b"TRACE" => 7,
        b"COPY" => 8,
        b"LOCK" => 9,
        b"MKCOL" => 10,
        b"MOVE" => 11,
        b"PROPFIND" => 12,
        b"PROPPATCH" => 13,
        b"SEARCH" => 14,
        b"UNLOCK" => 15,
        b"BIND" => 16,
        b"REBIND" => 17,
        b"UNBIND" => 18,
        b"ACL" => 19,
        b"REPORT" => 20,
        b"MKACTIVITY" => 21,
        b"CHECKOUT" => 22,
        b"MERGE" => 23,
        b"M-SEARCH" => 24,
        b"NOTIFY" => 25,
        b"SUBSCRIBE" => 26,
        b"UNSUBSCRIBE" => 27,
        b"PURGE" => 29,
        b"MKCALENDAR" => 30,
        b"LINK" => 31,
        b"UNLINK" => 32,
        b"SOURCE" => 33,
        b"QUERY" => 46,
        _ => return None,
    })
}

fn method_end(st: &St) -> Option<u8> {
    let mut bits = st.meth;
    while bits != 0 {
        let k = bits.trailing_zeros() as usize;
        bits &= bits - 1;
        if METHODS[k].0.len() == st.mlen as usize && METHODS[k].1 != NOT_HTTP {
            return Some(METHODS[k].1);
        }
    }
    None
}

/// Span kinds.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Sp {
    None = 0,
    Url,
    Status,
    Field,
    Value,
    Body,
    Ext,
}

fn span_hook(k: Sp) -> Option<Hook> {
    match k {
        Sp::None => None,
        Sp::Url => Some(llhttp__on_url),
        Sp::Status => Some(llhttp__on_status),
        Sp::Field => Some(llhttp__on_header_field),
        Sp::Value => Some(llhttp__on_header_value),
        Sp::Body => Some(llhttp__on_body),
        Sp::Ext => Some(llhttp__on_chunk_extension_name),
    }
}

/// How `execute` stopped early.
enum Stop {
    /// An error code (already stored, with its reason and position).
    Err(c_int),
}

struct Run<'a> {
    p: &'a mut LlhttpT,
    base: *const u8,
    st: St,
    span: Sp,
    span_start: usize,
    /// Replaying bytes already reported: no callbacks.
    quiet: bool,
    /// The head just ended is a request whose Transfer-Encoding does not
    /// end in `chunked` (`deferred_te`).
    bad_te: bool,
}

/// Which callback a fast-path report was.
#[derive(Clone, Copy, PartialEq)]
enum Cb {
    Reset,
    Begin,
    Span,
}

std::thread_local! {
    static HEADERS: core::cell::RefCell<Vec<Header>> = const { core::cell::RefCell::new(Vec::new()) };
}

/// Most field lines the one-shot path takes; longer heads stream.
const FAST_MAX: usize = 64;

static R_METHOD: &[u8] = b"Invalid method encountered\0";
static R_URL: &[u8] = b"Invalid characters in url\0";
static R_CONSTANT: &[u8] = b"Expected HTTP/, RTSP/ or ICE/\0";
static R_VERSION: &[u8] = b"Invalid HTTP version\0";
static R_LF: &[u8] = b"Expected LF after CR\0";
static R_STATUS: &[u8] = b"Invalid status code\0";
static R_HEADER: &[u8] = b"Invalid header token\0";
static R_VALUE: &[u8] = b"Invalid header value char\0";
static R_CL: &[u8] = b"Invalid character in Content-Length\0";
static R_CL_DUP: &[u8] = b"Duplicate Content-Length\0";
static R_CL_TE: &[u8] = b"Content-Length can't be present with Transfer-Encoding\0";
static R_TE_CL: &[u8] = b"Transfer-Encoding can't be present with Content-Length\0";
static R_H2: &[u8] = b"Pause on PRI/Upgrade\0";
static R_TE: &[u8] = b"Invalid `Transfer-Encoding` header value\0";
static R_TE_REQ: &[u8] = b"Request has invalid `Transfer-Encoding`\0";
static R_HOST: &[u8] = b"Missing or duplicate Host header\0";
static R_CHUNK: &[u8] = b"Invalid chunked body\0";
static R_CHUNK_WS: &[u8] = b"Whitespace in chunk size line\0";
static R_CLOSED: &[u8] = b"Data after `Connection: close`\0";
static R_PAUSED: &[u8] = b"Paused in callback\0";
static R_UPGRADE: &[u8] = b"Pause on CONNECT/Upgrade\0";
static R_CB: &[u8] = b"User callback error\0";

/// Sets the `llhttp_t` fields a complete head reports.
fn head_fields(p: &mut LlhttpT, hs: &HS, cflags: u16, ver: u8) {
    (p.http_major, p.http_minor) = match ver {
        VER_09 => (0, 9),
        VER_20 => (2, 0),
        _ => (1, hs.minor),
    };
    p.status_code = hs.status;
    let mut flags = cflags;
    if let Some(n) = hs.f.cl {
        flags |= F_CONTENT_LENGTH;
        p.content_length = n;
    } else {
        p.content_length = 0;
    }
    if hs.f.te.present {
        flags |= F_TRANSFER_ENCODING;
        if hs.f.te.chunked_last {
            flags |= F_CHUNKED;
        }
    }
    p.flags = flags;
}

/// A head `fast_parse` took, with its field lines in `HEADERS`.
struct FastHead {
    /// Where the request line starts (after any empty lines) and where
    /// the head ends, relative to the head's buffer.
    start: usize,
    end: usize,
    method: u8,
    /// The request target, or the reason phrase.
    span: Span,
    /// The machine state at the end of the head.
    done: HS,
    cflags: u16,
    ustage: u8,
}

impl FastHead {
    fn new(req: bool) -> FastHead {
        FastHead { start: 0, end: 0, method: 0, span: Span { start: 0, end: 0 }, done: start_hs(req), cflags: 0, ustage: 0 }
    }
}

/// The whole head at the start of `b`, parsed by the verified one-shot
/// parser into `h` (`llcore::fast_head_exec`, which also checks the
/// framing rules the machine checks at the end of a head), and checked
/// here against llhttp's own method and URL rules. False if the head is
/// incomplete, invalid, or anything llhttp's own rules reject: the
/// streaming path then handles it, errors included.
fn fast_parse(b: &[u8], req: bool, hs: &mut Vec<Header>, h: &mut FastHead) -> bool {
    let f = match fast_head_exec(b, req, FAST_MAX, hs) {
        Some(f) => f,
        None => return false,
    };
    h.end = f.end;
    h.done = f.done;
    h.span = f.span;
    if req {
        h.start = f.method.start;
        let code = match method_code(&b[f.method.start..f.method.end]) {
            Some(c) => c,
            None => return false,
        };
        h.method = code;
        let url = &b[f.span.start..f.span.end];
        // Origin form: the path from the first byte.
        let mut ustage = if url.first() == Some(&b'/') { 1 } else { 0 };
        let mut k = ustage as usize;
        while k < url.len() && ustage != 1 {
            if !url_step(&mut ustage, code == 5, url[k]) {
                return false;
            }
            k += 1;
        }
        // In the path, any VCHAR. The verified parser already took
        // only bytes above 0x20 other than 0x7F.
        if !url[k..].is_ascii() || matches!(ustage, 2 | 3 | 4) {
            return false;
        }
        h.ustage = ustage;
    }
    if h.done.f.te.present && empty_te(b, hs, h.end) {
        // The streaming path reports it.
        return false;
    }
    // Connection and Upgrade. Names are tchars, and among tchars `c | 0x20`
    // equals a lowercase letter or `-` only for that letter in either case
    // or `-` itself, so OR-ing 0x20 into each byte compares names with
    // these literals case-insensitively, a word at a time.
    let n = hs.len();
    for k in 0..n {
        let f = hs[k];
        let nl = f.name.end - f.name.start;
        let s = f.name.start;
        let conn = match nl {
            10 => lc8(b, s) == lit8(b"connecti") && lc2(b, s + 8) == lit2(b"on"),
            16 => lc8(b, s) == lit8(b"proxy-co") && lc8(b, s + 8) == lit8(b"nnection"),
            7 => {
                if lc4(b, s) == lit4(b"upgr") && lc4(b, s + 3) == lit4(b"rade") {
                    let cr = if k + 1 < n { hs[k + 1].name.start } else { h.end - 2 } - 2;
                    if f.value.start < cr {
                        h.cflags |= F_UPGRADE;
                    }
                }
                false
            }
            _ => false,
        };
        if conn {
            let cr = if k + 1 < n { hs[k + 1].name.start } else { h.end - 2 } - 2;
            h.cflags |= conn_flags(&b[f.name.end + 1..cr]);
        }
    }
    true
}

/// An empty Transfer-Encoding among `hs` (a head ending at `end` in `b`),
/// which llhttp rejects and the machine takes as an empty list.
#[cold]
#[inline(never)]
fn empty_te(b: &[u8], hs: &[Header], end: usize) -> bool {
    let n = hs.len();
    for k in 0..n {
        let f = hs[k];
        let s = f.name.start;
        if f.name.end - s == 17 && lc8(b, s) == lit8(b"transfer") {
            let cr = if k + 1 < n { hs[k + 1].name.start } else { end - 2 } - 2;
            if f.value.start >= cr {
                return true;
            }
        }
    }
    false
}



#[inline(always)]
fn lc8(b: &[u8], i: usize) -> u64 {
    u64::from_le_bytes(b[i..i + 8].try_into().unwrap()) | 0x2020_2020_2020_2020
}

#[inline(always)]
fn lc4(b: &[u8], i: usize) -> u32 {
    u32::from_le_bytes(b[i..i + 4].try_into().unwrap()) | 0x2020_2020
}

#[inline(always)]
fn lc2(b: &[u8], i: usize) -> u16 {
    u16::from_le_bytes(b[i..i + 2].try_into().unwrap()) | 0x2020
}

const fn lit8(s: &[u8; 8]) -> u64 {
    u64::from_le_bytes(*s)
}

const fn lit4(s: &[u8; 4]) -> u32 {
    u32::from_le_bytes(*s)
}

const fn lit2(s: &[u8; 2]) -> u16 {
    u16::from_le_bytes(*s)
}

/// Reports a `fast_parse` head at `i` in `d` (`base` is `d`'s start), in
/// the streaming path's order and positions. A callback that returns
/// anything but 0 is handed to `stop` with the position the streaming path
/// would resume at.
#[inline(always)]
fn report(
    p: *mut LlhttpT,
    base: *const u8,
    d: &[u8],
    i: usize,
    h: &FastHead,
    hs: &[Header],
    mut stop: impl FnMut(c_int, usize, Cb) -> Result<(), Stop>,
) -> Result<(), Stop> {
    let _ = d;
    let mut cb = move |f: Hook, a: usize, b: usize, resume: usize, k: Cb| -> Result<(), Stop> {
        let r = unsafe { f(p, base.wrapping_add(a), base.wrapping_add(b)) };
        if r == 0 {
            Ok(())
        } else {
            stop(r, resume, k)
        }
    };
    let s = i + h.start;
    if unsafe { (*p).initial_message_completed } != 0 {
        cb(llhttp__on_reset, s, s, s, Cb::Reset)?;
    }
    unsafe { (*p).finish = 2 };
    cb(llhttp__on_message_begin, s, s, s, Cb::Begin)?;
    let t = h.span;
    if h.done.req {
        cb(llhttp__on_url, i + t.start, i + t.end, i + t.end, Cb::Span)?;
    } else if t.end > t.start {
        cb(llhttp__on_status, i + t.start, i + t.end, i + t.end, Cb::Span)?;
    }
    let n = hs.len();
    for k in 0..n {
        let f = hs[k];
        let cr = i + if k + 1 < n { hs[k + 1].name.start } else { h.end - 2 } - 2;
        cb(llhttp__on_header_field, i + f.name.start, i + f.name.end, i + f.name.end, Cb::Span)?;
        let vs = i + f.value.start;
        if vs < cr {
            cb(llhttp__on_header_value, vs, cr, cr, Cb::Span)?;
        } else {
            cb(llhttp__on_header_value, cr, cr, cr + 1, Cb::Span)?;
        }
    }
    Ok(())
}

impl<'a> Run<'a> {
    fn ptr(&self, i: usize) -> *const u8 {
        self.base.wrapping_add(i)
    }

    fn fail(&mut self, code: c_int, reason: &'static [u8], at: usize) -> Stop {
        self.p.error = code;
        self.p.reason = reason.as_ptr() as *const c_char;
        self.p.error_pos = self.ptr(at) as *const c_char;
        Stop::Err(code)
    }

    /// The result of a callback: 0 continues; `HPE_PAUSED` pauses with
    /// parsing to resume at `at`; anything else is an error.
    fn check(&mut self, r: c_int, at: usize, cb_err: c_int) -> Result<(), Stop> {
        if r == 0 {
            Ok(())
        } else if r == HPE_PAUSED {
            Err(self.fail(HPE_PAUSED, R_PAUSED, at))
        } else {
            let code = if r == -1 { cb_err } else { r };
            if self.p.reason.is_null() || code != HPE_USER {
                self.p.reason = R_CB.as_ptr() as *const c_char;
            }
            self.p.error = code;
            self.p.error_pos = self.ptr(at) as *const c_char;
            Err(Stop::Err(code))
        }
    }

    fn call(&mut self, f: Hook, at: usize, cb_err: c_int) -> Result<(), Stop> {
        if self.quiet {
            return Ok(());
        }
        let r = unsafe { f(self.p, self.ptr(at), self.ptr(at)) };
        self.check(r, at, cb_err)
    }

    fn data(&mut self, f: Hook, a: usize, b: usize, resume: usize) -> Result<(), Stop> {
        if self.quiet {
            return Ok(());
        }
        let r = unsafe { f(self.p, self.ptr(a), self.ptr(b)) };
        self.check(r, resume, HPE_USER)
    }

    /// Closes the open span at `i` (exclusive), emitting it.
    fn close_span(&mut self, i: usize, resume: usize) -> Result<(), Stop> {
        let k = self.span;
        self.span = Sp::None;
        if let Some(f) = span_hook(k) {
            if i > self.span_start {
                if k == Sp::Value {
                    self.st.val_emitted = true;
                }
                self.data(f, self.span_start, i, resume)?;
            }
        }
        Ok(())
    }

    fn head_error(&mut self, ph: Ph, c: u8, i: usize) -> Stop {
        let (code, r) = match ph {
            Ph::RStart | Ph::Method => (HPE_INVALID_METHOD, R_METHOD),
            Ph::Target0 | Ph::Target => (HPE_INVALID_URL, R_URL),
            Ph::RVer { .. } => (HPE_INVALID_VERSION, R_VERSION),
            Ph::SVer { k } => {
                if k < 7 {
                    (HPE_INVALID_CONSTANT, R_CONSTANT)
                } else {
                    (HPE_INVALID_VERSION, R_VERSION)
                }
            }
            Ph::RStartLf | Ph::RLf | Ph::SLf | Ph::RCr => (HPE_LF_EXPECTED, R_LF),
            Ph::SSp | Ph::Code { .. } | Ph::Reason => (HPE_INVALID_STATUS, R_STATUS),
            Ph::Line | Ph::Name { .. } => (HPE_INVALID_HEADER_TOKEN, R_HEADER),
            Ph::EndLf => {
                if c != b'\n' {
                    (HPE_LF_EXPECTED, R_LF)
                } else {
                    let f = self.st.hs.f;
                    if f.te.present && f.cl.is_some() {
                        // llhttp reports whichever came second.
                        if self.st.cl_first {
                            (HPE_INVALID_TRANSFER_ENCODING, R_TE_CL)
                        } else {
                            (HPE_INVALID_CONTENT_LENGTH, R_CL_TE)
                        }
                    } else if f.te.present {
                        (HPE_INVALID_TRANSFER_ENCODING, R_TE_REQ)
                    } else {
                        (HPE_INVALID_HEADER_TOKEN, R_HOST)
                    }
                }
            }
            Ph::Val { v } | Ph::ValLf { v } => {
                let lf = matches!(ph, Ph::ValLf { .. });
                if lf && c != b'\n' {
                    (HPE_LF_EXPECTED, R_LF)
                } else {
                    match v {
                        VK::ClLead | VK::ClDig { .. } | VK::ClTrail { .. } => {
                            if lf {
                                (HPE_UNEXPECTED_CONTENT_LENGTH, R_CL_DUP)
                            } else {
                                (HPE_INVALID_CONTENT_LENGTH, R_CL)
                            }
                        }
                        VK::TeSep { .. } | VK::TeTok { .. } | VK::TeAfter { .. } => {
                            (HPE_INVALID_TRANSFER_ENCODING, R_TE)
                        }
                        _ => (HPE_INVALID_HEADER_TOKEN, R_VALUE),
                    }
                }
            }
            Ph::Done => (HPE_INVALID_HEADER_TOKEN, R_HEADER),
        };
        let code = if matches!(ph, Ph::Name { .. }) && c == b':' {
            // A duplicate Transfer-Encoding or a `_` look-alike name.
            HPE_INVALID_HEADER_TOKEN
        } else {
            code
        };
        self.fail(code, r, i)
    }

    /// The state as `llcore` sees it.
    #[inline(always)]
    fn ls(&self) -> LS {
        LS { hs: self.st.hs, ver: self.st.ver, tv: self.st.tv }
    }

    #[inline(always)]
    fn set_ls(&mut self, s: LS) {
        self.st.hs = s.hs;
        self.st.ver = s.ver;
        self.st.tv = s.tv;
    }

    /// The request line ends at `i` (a CR) right after the target: the
    /// machine reads ` HTTP/1.0` there, and the head is HTTP/0.9's
    /// (`llcore::l09`).
    #[cold]
    fn http09(&mut self, i: usize) -> Result<(), Stop> {
        if matches!(self.st.ustage, 2 | 3 | 4) {
            return Err(self.fail(HPE_INVALID_URL, R_URL, i));
        }
        self.enter(Sp::None, i)?;
        match l09_exec(self.ls()) {
            Some(s) => self.set_ls(s),
            None => return Err(self.fail(HPE_INVALID_URL, R_URL, i)),
        }
        Ok(())
    }

    /// The span byte `i` of the head belongs to, stepping from `ph` to
    /// `next`.
    fn head_kind(&self, ph: Ph, next: Ph, c: u8) -> Sp {
        match (ph, next) {
            (Ph::Target0, Ph::Target) | (Ph::Target, Ph::Target) => Sp::Url,
            (Ph::Reason, Ph::Reason) => Sp::Status,
            (_, Ph::Name { .. }) => Sp::Field,
            (Ph::Val { .. }, Ph::Val { .. }) => {
                if self.st.val_started || !(c == b' ' || c == b'\t') {
                    Sp::Value
                } else {
                    Sp::None
                }
            }
            _ => Sp::None,
        }
    }

    /// Byte `i` belongs to span `kind`: closes the open span if it is
    /// another one. Nothing is committed yet, so a pause resumes at `i`.
    fn enter(&mut self, kind: Sp, i: usize) -> Result<(), Stop> {
        if self.span != kind && self.span != Sp::None {
            self.close_span(i, i)?;
        }
        Ok(())
    }

    /// After byte `i` is committed: opens its span.
    fn open(&mut self, kind: Sp, i: usize) {
        if kind != Sp::None && self.span != kind {
            self.span = kind;
            self.span_start = i;
        }
    }

    /// Head bytes from `i`; returns where the head ended, or `len` if
    /// it has not.
    fn head(&mut self, d: &[u8], mut i: usize) -> Result<usize, Stop> {
        while i < d.len() {
            // Bulk: a run of bytes whose steps are trivial and that only
            // extend the open span (the verified `lbulk_exec`).
            let bulk = match self.st.hs.ph {
                Ph::Target => self.span == Sp::Url && self.st.ustage == 1,
                Ph::Reason => self.span == Sp::Status,
                Ph::Val { .. } => self.span == Sp::Value && self.st.hkind != H_CONNECTION,
                Ph::Name { .. } => self.span == Sp::Field && self.st.ncand == 0,
                _ => false,
            };
            if bulk {
                let from = self.ls();
                let (mut next, mut r) = lbulk_exec(&from, d, i);
                if self.st.hs.ph == Ph::Target {
                    // llhttp takes only VCHAR in a URL. The state does not
                    // change over target bytes, so stopping early leaves
                    // it as it was.
                    if let Some(k) = d[i..r].iter().position(|&c| c >= 0x80) {
                        r = i + k;
                    }
                    next = from;
                }
                if matches!(next.hs.ph, Ph::Name { .. }) {
                    self.st.nlen = self.st.nlen.saturating_add((r - i).min(255) as u8);
                }
                self.set_ls(next);
                i = r;
                if i == d.len() {
                    break;
                }
            }
            let c = d[i];
            let ph = self.st.hs.ph;
            let begins = if self.st.hs.req { ph == Ph::RStart && c != b'\r' } else { true };
            if !self.st.begun && begins {
                self.st.begun = true;
                if self.p.initial_message_completed != 0 {
                    self.call(llhttp__on_reset, i, HPE_CB_RESET)?;
                }
                self.p.finish = 2;
                self.call(llhttp__on_message_begin, i, HPE_CB_MESSAGE_BEGIN)?;
            }
            if ph == Ph::Target && c == b'\r' {
                // A request line with no version: llhttp takes it as
                // HTTP/0.9. The machine reads the version it implies.
                self.http09(i)?;
                continue;
            }
            let (stepped, c) = match lstep_exec(self.ls(), c) {
                Stepped::Next(n, m) => (n, m),
                Stepped::BadVersion => return Err(self.fail(HPE_INVALID_VERSION, R_VERSION, i + 1)),
                Stepped::Invalid => {
                    if ph == Ph::EndLf && c == b'\n' && deferred_te_exec(&self.st.hs) {
                        // llhttp reports this head before rejecting the
                        // request (`after_hc`), so Node.js answers 400.
                        self.st.hs.ph = Ph::Done;
                        self.bad_te = true;
                        return Ok(i + 1);
                    }
                    return Err(self.head_error(ph, c, i));
                }
            };
            let next = stepped.hs;
            let kind = self.head_kind(ph, next.ph, c);
            self.enter(kind, i)?;
            // Commit byte `i`.
            self.set_ls(stepped);
            let mut empty_value = false;
            match (ph, next.ph) {
                (_, Ph::Method) => {
                    method_step(&mut self.st, c);
                    if self.st.meth == 0 {
                        // No method starts this way: llhttp stops here.
                        return Err(self.fail(HPE_INVALID_METHOD, R_METHOD, i));
                    }
                }
                (_, Ph::Target) => {
                    if !url_step(&mut self.st.ustage, self.p.method == 5, c) {
                        return Err(self.fail(HPE_INVALID_URL, R_URL, i));
                    }
                }
                (Ph::Target, Ph::RVer { .. }) => {
                    if matches!(self.st.ustage, 2 | 3 | 4) {
                        return Err(self.fail(HPE_INVALID_URL, R_URL, i));
                    }
                }
                (Ph::Line, Ph::Name { .. }) => {
                    self.st.nlen = 0;
                    name_track(&mut self.st, c);
                }
                (Ph::Name { .. }, Ph::Name { .. }) => name_track(&mut self.st, c),
                (Ph::Name { .. }, Ph::Val { .. }) => {
                    self.st.hkind = name_kind(&self.st);
                    self.st.val_emitted = false;
                    self.st.val_started = false;
                    self.st.tlen = 0;
                    self.st.tcand = 0;
                }
                (Ph::Val { .. }, Ph::Val { .. }) => {
                    if kind == Sp::Value {
                        self.st.val_started = true;
                    }
                    if self.st.hkind == H_CONNECTION {
                        token_track(&mut self.st, Some(c));
                    }
                }
                (Ph::Val { v }, Ph::ValLf { .. }) => {
                    if matches!(v, VK::TeSep { .. }) && !self.st.val_started {
                        // An empty Transfer-Encoding: llhttp rejects it.
                        return Err(self.fail(HPE_INVALID_TRANSFER_ENCODING, R_TE, i));
                    }
                    if matches!(v, VK::ClDig { .. } | VK::ClTrail { .. }) && !self.st.hs.f.te.present {
                        self.st.cl_first = true;
                    }
                    empty_value = !self.st.val_emitted;
                    self.st.val_emitted = true;
                    if self.st.hkind == H_CONNECTION {
                        token_track(&mut self.st, None);
                    } else if self.st.hkind == H_UPGRADE && self.st.val_started {
                        self.st.cflags |= F_UPGRADE;
                    }
                }
                _ => {}
            }
            self.open(kind, i);
            i += 1;
            if ph == Ph::Method && next.ph == Ph::Target0 {
                match method_end(&self.st) {
                    Some(m) => self.p.method = m,
                    None => return Err(self.fail(HPE_INVALID_METHOD, R_METHOD, i - 1)),
                }
            }
            if empty_value {
                // An empty value: llhttp still reports it.
                self.data(llhttp__on_header_value, i - 1, i - 1, i)?;
            }
            if next.ph == Ph::Done {
                return Ok(i);
            }
        }
        Ok(i)
    }

    /// A report from the one-shot path. If the callback pauses or fails,
    /// the streaming state is rebuilt by replaying the bytes before
    /// `resume` without callbacks, so parsing resumes where it would have.
    #[cold]
    #[inline(never)]
    fn fast_stop(&mut self, r: c_int, resume: usize, cb: Cb, from: &(&[u8], usize)) -> Result<(), Stop> {
        let (d, start) = *from;
        self.quiet = true;
        let replay = self.head(&d[..resume], start);
        self.quiet = false;
        self.span = Sp::None;
        if replay.is_err() {
            // Unreachable: the bytes form the start of a valid head.
            return Err(self.fail(HPE_INVALID_CONSTANT, R_CB, resume));
        }
        if cb != Cb::Span {
            self.st.begun = true;
            if cb == Cb::Begin {
                self.p.finish = 2;
            }
        }
        let err = match cb {
            Cb::Reset => HPE_CB_RESET,
            Cb::Begin => HPE_CB_MESSAGE_BEGIN,
            Cb::Span => HPE_USER,
        };
        self.check(r, resume, err)
    }

    /// The common case: the whole head is in `d` from `i`, at the start of
    /// a message. Parses it with the verified one-shot parser
    /// (`fast_parse`) and reports it as the streaming path would. `None`
    /// (nothing reported) if the streaming path must handle it.
    fn fast_head(&mut self, d: &[u8], i: usize) -> Result<Option<usize>, Stop> {
        let req = self.st.hs.req;
        HEADERS.with(|cell| {
            let mut hs = match cell.try_borrow_mut() {
                Ok(v) => v,
                Err(_) => return Ok(None),
            };
            let mut h = FastHead::new(req);
            if !fast_parse(&d[i..], req, &mut hs, &mut h) {
                return Ok(None);
            }
            if req {
                self.p.method = h.method;
            }
            // `self.st` is left as it was until every callback has
            // returned, so a pause can replay from it.
            let base = self.base;
            let p: *mut LlhttpT = &mut *self.p;
            report(p, base, d, i, &h, &hs, |r, resume, cb| self.fast_stop(r, resume, cb, &(d, i)))?;
            self.st.begun = true;
            self.st.hs = h.done;
            self.st.cflags = h.cflags;
            self.st.ustage = h.ustage;
            Ok(Some(i + h.end))
        })
    }

    /// The head is complete at `i`: callbacks and the body framing.
    fn headers_done(&mut self, i: usize) -> Result<(), Stop> {
        head_fields(self.p, &self.st.hs, self.st.cflags, self.st.ver);
        unsafe { llhttp__before_headers_complete(self.p, self.ptr(i), self.ptr(i)) };
        let r = unsafe { llhttp__on_headers_complete(self.p, self.ptr(i), self.ptr(i)) };
        self.after_hc(i, r)
    }

    /// `headers_done` once `on_headers_complete` returned `r`.
    fn after_hc(&mut self, i: usize, r: c_int) -> Result<(), Stop> {
        let hs = self.st.hs;
        let mut paused = false;
        match r {
            0 => {}
            1 => self.p.flags |= F_SKIPBODY,
            2 => {
                self.p.upgrade = 1;
                self.p.flags |= F_SKIPBODY;
            }
            HPE_PAUSED => paused = true,
            _ => {
                let code = if r == -1 { HPE_CB_HEADERS_COMPLETE } else { r };
                return Err(self.fail(code, R_CB, i));
            }
        }
        let skip = self.p.flags & F_SKIPBODY != 0;
        let how = unsafe { llhttp__after_headers_complete(self.p, self.ptr(i), self.ptr(i)) };
        let bad_te = self.bad_te;
        self.bad_te = false;
        self.dispatch(i, after_head_exec(&hs, bad_te, how, skip))?;
        if paused && self.p.error == 0 {
            return Err(self.fail(HPE_PAUSED, R_PAUSED, i));
        }
        Ok(())
    }

    /// What follows the head at `i` (`llcore::after_head`): its body, the
    /// hand-over to another protocol, or the rejection of a request whose
    /// Transfer-Encoding does not end in `chunked`.
    fn dispatch(&mut self, i: usize, after: After) -> Result<(), Stop> {
        let body = match after {
            After::Reject => return Err(self.fail(HPE_INVALID_TRANSFER_ENCODING, R_TE_REQ, i)),
            After::Upgrade => {
                self.st.mode = Mode::Upgraded;
                return self.message_complete(i, true);
            }
            After::Body(b) => b,
        };
        match body {
            Body::Empty => self.message_complete(i, false)?,
            Body::Length(n) => {
                self.p.content_length = n;
                if n == 0 {
                    self.message_complete(i, false)?;
                } else {
                    self.st.mode = Mode::Identity;
                }
            }
            Body::Chunked => {
                self.st.mode = Mode::Chunked;
                self.st.cs = CState::SizeStart;
            }
            Body::Close => {
                self.st.mode = Mode::Eof;
                self.p.finish = 1;
            }
        }
        Ok(())
    }

    /// The message ends at `i`.
    fn message_complete(&mut self, i: usize, upgrade_exit: bool) -> Result<(), Stop> {
        let r = unsafe { llhttp__on_message_complete(self.p, self.ptr(i), self.ptr(i)) };
        self.after_mc(i, upgrade_exit, r)
    }

    /// `message_complete` once `on_message_complete` returned `r`.
    fn after_mc(&mut self, i: usize, upgrade_exit: bool, r: c_int) -> Result<(), Stop> {
        let req = self.st.hs.req;
        let paused = r == HPE_PAUSED;
        if r != 0 && !paused {
            let code = if r == -1 { HPE_CB_MESSAGE_COMPLETE } else { r };
            return Err(self.fail(code, R_CB, i));
        }
        if upgrade_exit || self.p.upgrade == 1 {
            self.st = St::fresh(req);
            self.st.mode = Mode::Upgraded;
            self.p.finish = 0;
            return Err(self.fail(HPE_PAUSED_UPGRADE, R_UPGRADE, i));
        }
        let keep = unsafe { llhttp__after_message_complete(self.p, self.ptr(i), self.ptr(i)) };
        self.st = St::fresh(req);
        self.p.content_length = 0;
        self.p.status_code = 0;
        self.p.flags = 0;
        if keep != 0 {
            self.p.initial_message_completed = 1;
        } else {
            self.st.mode = Mode::Closed;
        }
        if paused {
            return Err(self.fail(HPE_PAUSED, R_PAUSED, i));
        }
        Ok(())
    }

    /// Chunked body bytes from `i`.
    fn chunked(&mut self, d: &[u8], mut i: usize) -> Result<usize, Stop> {
        while i < d.len() {
            let cs = self.st.cs;
            if let CState::Data { left } = cs {
                let avail = (d.len() - i) as u64;
                let n = if left < avail { left } else { avail };
                self.st.cs = if n == left { CState::DataCr } else { CState::Data { left: left - n } };
                let n = n as usize;
                self.data(llhttp__on_body, i, i + n, i + n)?;
                i += n;
                continue;
            }
            let c = d[i];
            // llhttp rejects the BWS that RFC 9112 allows around `;` and
            // `=` in a size line (outside quoted strings); so does Node.
            if (c == b' ' || c == b'\t')
                && matches!(
                    cs,
                    CState::Size { .. }
                        | CState::SizeWs { .. }
                        | CState::ExtPreName { .. }
                        | CState::ExtName { .. }
                        | CState::ExtNameWs { .. }
                        | CState::ExtPreVal { .. }
                        | CState::ExtTok { .. }
                        | CState::ExtValEnd { .. }
                        | CState::ExtValWs { .. }
                )
            {
                return Err(self.fail(HPE_STRICT, R_CHUNK_WS, i));
            }
            let (next, _) = match step_exec(cs, c) {
                Some(x) => x,
                None => return Err(self.fail(HPE_INVALID_CHUNK_SIZE, R_CHUNK, i)),
            };
            let kind = match next {
                CState::ExtPreName { .. }
                | CState::ExtName { .. }
                | CState::ExtNameWs { .. }
                | CState::ExtPreVal { .. }
                | CState::ExtTok { .. }
                | CState::ExtQ { .. }
                | CState::ExtQEsc { .. }
                | CState::ExtValEnd { .. }
                | CState::ExtValWs { .. } => {
                    if matches!(cs, CState::Size { .. } | CState::SizeWs { .. }) { Sp::None } else { Sp::Ext }
                }
                CState::TrName => Sp::Field,
                CState::TrValue
                    if matches!(cs, CState::TrValue) && (self.st.val_started || !(c == b' ' || c == b'\t')) =>
                {
                    Sp::Value
                }
                _ => Sp::None,
            };
            self.enter(kind, i)?;
            self.st.cs = next;
            let mut empty_value = false;
            match (cs, next) {
                (CState::TrStart, CState::TrName) => {
                    self.p.flags |= F_TRAILING;
                }
                (CState::TrName, CState::TrValue) => {
                    self.st.val_emitted = false;
                    self.st.val_started = false;
                }
                (CState::TrValue, CState::TrValue) if kind == Sp::Value => self.st.val_started = true,
                (CState::TrValue, CState::TrLf) => {
                    empty_value = !self.st.val_emitted;
                    self.st.val_emitted = true;
                }
                _ => {}
            }
            self.open(kind, i);
            i += 1;
            if empty_value {
                self.data(llhttp__on_header_value, i - 1, i - 1, i)?;
            }
            match (cs, next) {
                (CState::SizeLf { n }, _) => {
                    self.p.content_length = n;
                    self.call(llhttp__on_chunk_header, i, HPE_CB_CHUNK_HEADER)?;
                }
                (CState::DataLf, CState::SizeStart) => {
                    self.call(llhttp__on_chunk_complete, i, HPE_CB_CHUNK_COMPLETE)?;
                }
                (_, CState::Done) => {
                    self.call(llhttp__on_chunk_complete, i, HPE_CB_CHUNK_COMPLETE)?;
                    self.message_complete(i, false)?;
                    return Ok(i);
                }
                _ => {}
            }
        }
        Ok(i)
    }

    fn go(&mut self, d: &[u8]) -> Result<(), Stop> {
        // A message whose last callback paused completes on resuming.
        match self.st.mode {
            Mode::Identity if self.p.content_length == 0 => self.message_complete(0, false)?,
            Mode::Chunked if self.st.cs == CState::Done => self.message_complete(0, false)?,
            _ => {}
        }
        self.go_from(d, 0)
    }

    fn go_from(&mut self, d: &[u8], mut i: usize) -> Result<(), Stop> {
        while i < d.len() {
            match self.st.mode {
                Mode::Head => {
                    if !self.st.begun && self.span == Sp::None && matches!(self.st.hs.ph, Ph::RStart | Ph::SVer { k: 0 }) {
                        const PREFACE: &[u8] = b"PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n";
                        if self.st.hs.req && d[i..].starts_with(PREFACE) {
                            // The HTTP/2 connection preface: llhttp hands
                            // the connection over.
                            return Err(self.fail(HPE_PAUSED_H2_UPGRADE, R_H2, i + PREFACE.len()));
                        }
                        if !self.st.hs.req && (d[i] == b'\r' || d[i] == b'\n') {
                            // llhttp skips blank lines before a status line
                            // too, as RFC 9112 asks of request lines.
                            i += 1;
                            continue;
                        }
                        if let Some(e) = self.fast_head(d, i)? {
                            i = e;
                            self.headers_done(i)?;
                            continue;
                        }
                    }
                    i = self.head(d, i)?;
                    if self.st.hs.ph == Ph::Done {
                        self.headers_done(i)?;
                    }
                }
                Mode::Identity => {
                    let left = self.p.content_length;
                    let n = if left < (d.len() - i) as u64 { left as usize } else { d.len() - i };
                    self.p.content_length = left - n as u64;
                    let done = self.p.content_length == 0;
                    self.data(llhttp__on_body, i, i + n, i + n)?;
                    i += n;
                    if done {
                        self.message_complete(i, false)?;
                    }
                }
                Mode::Chunked => i = self.chunked(d, i)?,
                Mode::Eof => {
                    self.data(llhttp__on_body, i, d.len(), d.len())?;
                    i = d.len();
                }
                Mode::Closed => {
                    if d[i] == b'\r' || d[i] == b'\n' {
                        i += 1;
                    } else if self.p.lenient_flags & 0x20 != 0 {
                        i = d.len();
                    } else {
                        return Err(self.fail(HPE_CLOSED_CONNECTION, R_CLOSED, i));
                    }
                }
                Mode::Upgraded => {
                    // After `llhttp_resume_after_upgrade`, llhttp parses the
                    // rest as a new message.
                    let req = self.st.hs.req;
                    self.st = St::fresh(req);
                }
            }
        }
        // Flush the open span; it stays open, continuing in the next call.
        if let Some(f) = span_hook(self.span) {
            if self.span == Sp::Value {
                self.st.val_emitted = true;
            }
            if self.span_start < d.len() {
                self.data(f, self.span_start, d.len(), d.len())?;
            }
        }
        Ok(())
    }
}

/// Ends `execute` with `run`'s state stored.
fn finish(run: Run, r: Result<(), Stop>) -> c_int {
    run.st.store(run.p);
    run.p._index = run.span as i32;
    match r {
        Ok(()) => 0,
        Err(Stop::Err(code)) => code,
    }
}

/// `execute` on a parser between messages (its adapter state all zero)
/// for the common case, without unpacking that state: whole heads parsed
/// by `fast_parse`, and bodiless messages completed in place, as `Run::go`
/// would. Anything else is handed to a `Run` at the point it comes up, in
/// the state `go` would have reached; `None` if it comes up before
/// anything was reported.
unsafe fn lean(p: &mut LlhttpT, d: &[u8]) -> Option<c_int> {
    let req = p.type_ == HTTP_REQUEST;
    let base = d.as_ptr();
    let pp: *mut LlhttpT = p;
    let mut i = 0;
    loop {
        let general = |i: usize| -> c_int {
            let mut run = Run { st: St::fresh(req), p: &mut *pp, base, span: Sp::None, span_start: 0, quiet: false, bad_te: false };
            let r = run.go_from(d, i);
            finish(run, r)
        };
        // `fast_parse` takes neither the HTTP/2 preface nor blank lines
        // before a status line, so those stream too.
        let decline = |i: usize| if i == 0 { None } else { Some(general(i)) };
        let mut h = FastHead::new(req);
        let mut stopped = 0;
        let taken = HEADERS.with(|cell| {
            let mut hs = match cell.try_borrow_mut() {
                Ok(v) => v,
                Err(_) => return false,
            };
            if !fast_parse(&d[i..], req, &mut hs, &mut h) {
                return false;
            }
            if req {
                (*pp).method = h.method;
            }
            let _ = report(pp, base, d, i, &h, &hs, |r, resume, cb| {
                let mut run = Run { st: St::fresh(req), p: &mut *pp, base, span: Sp::None, span_start: 0, quiet: false, bad_te: false };
                let res = run.fast_stop(r, resume, cb, &(d, i));
                stopped = 1 + finish(run, res);
                Err(Stop::Err(0))
            });
            true
        });
        if !taken {
            return decline(i);
        }
        if stopped != 0 {
            return Some(stopped - 1);
        }
        // The state `go` would be in now.
        let st_head = || {
            let mut st = St::fresh(req);
            st.begun = true;
            st.hs = h.done;
            st.cflags = h.cflags;
            st.ustage = h.ustage;
            st
        };
        let e = i + h.end;
        let at = base.wrapping_add(e);
        head_fields(&mut *pp, &h.done, h.cflags, 0);
        llhttp__before_headers_complete(pp, at, at);
        let r = llhttp__on_headers_complete(pp, at, at);
        if r != 0 {
            let mut run = Run { st: st_head(), p: &mut *pp, base, span: Sp::None, span_start: 0, quiet: false, bad_te: false };
            let res = run.after_hc(e, r).and_then(|_| run.go_from(d, e));
            return Some(finish(run, res));
        }
        let how = llhttp__after_headers_complete(pp, at, at);
        let body = after_head_exec(&h.done, false, how, false);
        if !matches!(body, After::Body(Body::Empty) | After::Body(Body::Length(0))) {
            let mut run = Run { st: st_head(), p: &mut *pp, base, span: Sp::None, span_start: 0, quiet: false, bad_te: false };
            let res = run.dispatch(e, body).and_then(|_| run.go_from(d, e));
            return Some(finish(run, res));
        }
        if matches!(body, After::Body(Body::Length(0))) {
            (*pp).content_length = 0;
        }
        let r = llhttp__on_message_complete(pp, at, at);
        if r != 0 || (*pp).upgrade == 1 {
            let mut run = Run { st: st_head(), p: &mut *pp, base, span: Sp::None, span_start: 0, quiet: false, bad_te: false };
            let res = run.after_mc(e, false, r).and_then(|_| run.go_from(d, e));
            return Some(finish(run, res));
        }
        let keep = llhttp__after_message_complete(pp, at, at);
        (*pp).content_length = 0;
        (*pp).status_code = 0;
        (*pp).flags = 0;
        if keep == 0 {
            let mut st = St::fresh(req);
            st.mode = Mode::Closed;
            let mut run = Run { st, p: &mut *pp, base, span: Sp::None, span_start: 0, quiet: false, bad_te: false };
            let res = run.go_from(d, e);
            return Some(finish(run, res));
        }
        (*pp).initial_message_completed = 1;
        i = e;
        if i == d.len() {
            // Between messages again: the all-zero state.
            (*pp).set_words([0, 0, 0]);
            (*pp)._index = 0;
            return Some(0);
        }
    }
}

#[cfg(feature = "llhttp-lenient")]
extern "C" {
    fn vhttp_lenient_start(s: *mut LlhttpT);
    fn vhttp_lenient_execute(s: *mut LlhttpT, p: *const c_char, endp: *const c_char) -> c_int;
}

/// `llhttp__internal_init`: the start of the first message.
#[cfg_attr(feature = "llhttp-abi", export_name = "llhttp__internal_init")]
#[cfg_attr(not(feature = "llhttp-abi"), no_mangle)]
pub unsafe extern "C" fn vhttp_llhttp_internal_init(s: *mut LlhttpT) -> c_int {
    (*s).set_words([0, 0, 0]);
    core::ptr::write_bytes(s, 0, 1);
    0
}

/// `llhttp__internal_execute`: parses `p..endp`.
#[cfg_attr(feature = "llhttp-abi", export_name = "llhttp__internal_execute")]
#[cfg_attr(not(feature = "llhttp-abi"), no_mangle)]
pub unsafe extern "C" fn vhttp_llhttp_internal_execute(
    s: *mut LlhttpT,
    p: *const c_char,
    endp: *const c_char,
) -> c_int {
    let parser = &mut *s;
    if parser.error != HPE_OK {
        return parser.error;
    }
    #[cfg(feature = "llhttp-lenient")]
    if parser.lenient_flags != 0 {
        // Lenient modes accept what the verified machines reject: llhttp's
        // own parser takes the message. Lenient flags are set right after
        // `llhttp_init` or `llhttp_reset`, so a parser this adapter has
        // started never switches over: its `_current` is 0 only at the
        // start of a message.
        if parser._current == 0 {
            vhttp_lenient_start(s);
        }
        return vhttp_lenient_execute(s, p, endp);
    }
    let len = (endp as usize).wrapping_sub(p as usize);
    let d: &[u8] = if len == 0 || p.is_null() { &[] } else { core::slice::from_raw_parts(p as *const u8, len) };
    let span = match parser._index & 7 {
        1 => Sp::Url,
        2 => Sp::Status,
        3 => Sp::Field,
        4 => Sp::Value,
        5 => Sp::Body,
        6 => Sp::Ext,
        _ => Sp::None,
    };
    if span == Sp::None && parser.words()[0] == 0 && !d.is_empty() {
        if let Some(code) = lean(parser, d) {
            return code;
        }
    }
    let mut run = Run { st: St::load(parser), p: parser, base: p as *const u8, span, span_start: 0, quiet: false, bad_te: false };
    let r = run.go(d);
    finish(run, r)
}
