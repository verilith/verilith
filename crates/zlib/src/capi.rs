//! C ABIs compatible with zlib (compression and decompression) and
//! libdeflate's decompressor.
//!
//! A thin adapter, not verified: pointer checks, `z_stream` bookkeeping and
//! result codes. All decoding happens in the verified `Inflater`, driven by
//! `wrap::Decompressor` (one-shot calls) or `stream::Stream` (`inflate()`,
//! `inflateBack()`); all encoding in the verified `dstream::Deflater`
//! (`deflate()`) or `deflate::zlib_compress` (`compress2`). The logic that
//! is not pointer handling is verified in `glue`: the buffer of deflate
//! output waiting for `next_out`, `inflateSync`'s marker search and
//! `adler32_combine`. Copying the gzip header out for `inflateGetHeader`
//! and the CRC-32 combine helpers are here, unverified.
//!
//! Functions are exported as `vz_*` (zlib) and `vzlib_*` (libdeflate). With
//! the `zlib-abi` or `libdeflate-abi` feature they are exported under the
//! original names instead, so a program linked against `libvzlib.a` uses
//! them in place of zlib's or libdeflate's.
//!
//! Differences from zlib's inflate:
//! - The window is always 32 KiB whatever `windowBits` says.
//! - `zalloc`/`zfree` are accepted but not called: memory comes from the
//!   Rust allocator (about 110 KiB per stream).
//! - `inflate()` may decode up to 64 KiB ahead of the output buffer
//!   internally (it still never reports more input used than the stream
//!   needs).
//! - A raw stream's dictionary must be set before the first `inflate()`.
//! - `inflatePrime` is not supported (`Z_STREAM_ERROR`), `inflateValidate`
//!   cannot turn checksum checks off, `inflateSyncPoint` always answers 0,
//!   and `inflateMark` always answers -65536 (position unknown).
//! - After `inflateSync` finds a flush point, the rest is decoded as raw
//!   DEFLATE: the stream ends at its last block and the trailer is not
//!   checked.
#![allow(non_snake_case)]
#![allow(unsafe_op_in_unsafe_fn)]
use crate::stream::{Progress, Stream, Wrapper};
use crate::wrap::{Decompressor, Error, Format};
use crate::glue::{Pending, SyncSearch};
use std::os::raw::{c_char, c_int, c_long, c_uint, c_ulong, c_void};

pub const Z_OK: c_int = 0;
pub const Z_STREAM_END: c_int = 1;
pub const Z_NEED_DICT: c_int = 2;
pub const Z_ERRNO: c_int = -1;
pub const Z_STREAM_ERROR: c_int = -2;
pub const Z_DATA_ERROR: c_int = -3;
pub const Z_MEM_ERROR: c_int = -4;
pub const Z_BUF_ERROR: c_int = -5;
pub const Z_VERSION_ERROR: c_int = -6;
pub const Z_FINISH: c_int = 4;

/// zlib's `z_stream`, field for field.
#[repr(C)]
pub struct ZStream {
    pub next_in: *const u8,
    pub avail_in: c_uint,
    pub total_in: c_ulong,
    pub next_out: *mut u8,
    pub avail_out: c_uint,
    pub total_out: c_ulong,
    pub msg: *const c_char,
    pub state: *mut c_void,
    pub zalloc: *const c_void,
    pub zfree: *const c_void,
    pub opaque: *mut c_void,
    pub data_type: c_int,
    pub adler: c_ulong,
    pub reserved: c_ulong,
}

/// zlib's `gz_header`, field for field.
#[repr(C)]
pub struct GzHeader {
    pub text: c_int,
    pub time: c_ulong,
    pub xflags: c_int,
    pub os: c_int,
    pub extra: *mut u8,
    pub extra_len: c_uint,
    pub extra_max: c_uint,
    pub name: *mut u8,
    pub name_max: c_uint,
    pub comment: *mut u8,
    pub comm_max: c_uint,
    pub hcrc: c_int,
    pub done: c_int,
}

static VERSION: &[u8] = b"1.3.1.vzlib\0";
static MSG_DATA: &[u8] = b"invalid compressed data\0";

// Stages of copying a gzip header into a `GzHeader`.
const H_FIXED: u8 = 0;
const H_XLEN: u8 = 1;
const H_EXTRA: u8 = 2;
const H_NAME: u8 = 3;
const H_COMMENT: u8 = 4;
const H_HCRC: u8 = 5;
const H_DONE: u8 = 6;

thread_local! {
    /// The fixed Huffman codes, built by an earlier deflate stream on this
    /// thread. Building them costs as much as compressing a small input.
    static FX_SPARE: std::cell::RefCell<Option<FixedCodes>> = const { std::cell::RefCell::new(None) };
}

/// Spare inflate states from streams that have ended, for the next
/// inflateInit on any thread. Shared rather than per thread because
/// Node's async inflate starts a stream on a worker thread and ends it on
/// the main one.
const SPARES: usize = 4;
static SPARE: [std::sync::atomic::AtomicPtr<State>; SPARES] =
    [const { std::sync::atomic::AtomicPtr::new(std::ptr::null_mut()) }; SPARES];

/// A spare state, if one is kept.
fn take_spare() -> *mut State {
    use std::sync::atomic::Ordering;
    for slot in &SPARE {
        if !slot.load(Ordering::Relaxed).is_null() {
            let p = slot.swap(std::ptr::null_mut(), Ordering::Acquire);
            if !p.is_null() {
                return p;
            }
        }
    }
    std::ptr::null_mut()
}

/// Keeps `p` (from `Box::into_raw`) as a spare if a slot is free, and
/// frees it otherwise.
unsafe fn keep_spare(p: *mut State) {
    use std::sync::atomic::Ordering;
    for slot in &SPARE {
        if slot.load(Ordering::Relaxed).is_null()
            && slot.compare_exchange(std::ptr::null_mut(), p, Ordering::Release, Ordering::Relaxed).is_ok()
        {
            return;
        }
    }
    drop(Box::from_raw(p));
}

/// Keeps fixed codes for the next deflate stream on this thread.
fn keep_fx(fx: Option<FixedCodes>) {
    if fx.is_some() {
        let _ = FX_SPARE.try_with(move |w| *w.borrow_mut() = fx);
    }
}

/// What `z_stream.state` points to.
#[derive(Clone)]
struct State {
    st: Stream,
    /// The wrapper asked for at initialization (`inflateSync` switches
    /// `st` to raw; `inflateReset` switches it back).
    wrapper: Wrapper,
    /// Where `inflateGetHeader` wants the gzip header, and how far the copy
    /// has got: the stage, the byte within it, the flags, the extra
    /// field's length.
    head: *mut GzHeader,
    hstage: u8,
    hpos: usize,
    hflg: u8,
    hxlen: usize,
    /// How much of the `00 00 FF FF` flush marker `inflateSync` has found.
    sync: SyncSearch,
}

impl State {
    fn new(wrapper: Wrapper) -> State {
        State { st: Stream::open(wrapper), wrapper, head: std::ptr::null_mut(), hstage: H_FIXED, hpos: 0, hflg: 0, hxlen: 0, sync: SyncSearch::new() }
    }

    /// A boxed state for a new stream: a spare one restarted, as
    /// inflateReset would, which saves allocating and zeroing its 96 KiB
    /// window and tables (most of the cost of a small one-shot stream;
    /// Node makes one per call), or a new one.
    fn boxed(wrapper: Wrapper) -> *mut State {
        let p = take_spare();
        if p.is_null() {
            return Box::into_raw(Box::new(State::new(wrapper)));
        }
        // SAFETY: spares come from `Box::into_raw` and are owned once taken.
        let st = unsafe { &mut *p };
        st.restart(wrapper);
        st.hpos = 0;
        st.hflg = 0;
        st.hxlen = 0;
        p
    }

    fn restart(&mut self, wrapper: Wrapper) {
        self.st.restart(wrapper);
        self.wrapper = wrapper;
        self.head = std::ptr::null_mut();
        self.hstage = H_FIXED;
        self.sync = SyncSearch::new();
    }

    /// Moves to the next field the header flags say is present, clearing
    /// the pointers of the absent ones as zlib does.
    unsafe fn next_field(&mut self, h: &mut GzHeader, mut stage: u8) {
        loop {
            let (bit, present) = match stage {
                H_XLEN => (4, self.hflg & 4 != 0),
                H_NAME => (8, self.hflg & 8 != 0),
                H_COMMENT => (16, self.hflg & 16 != 0),
                H_HCRC => (2, self.hflg & 2 != 0),
                _ => (0, true),
            };
            if present {
                break;
            }
            match bit {
                4 => h.extra = std::ptr::null_mut(),
                8 => h.name = std::ptr::null_mut(),
                16 => h.comment = std::ptr::null_mut(),
                _ => {}
            }
            stage += if stage == H_XLEN { 2 } else { 1 };
        }
        self.hstage = stage;
        self.hpos = 0;
    }

    /// Copies the next header byte into `*self.head`.
    unsafe fn header_byte(&mut self, x: u8) {
        let h = &mut *self.head;
        let p = self.hpos;
        self.hpos += 1;
        match self.hstage {
            H_FIXED => {
                match p {
                    3 => self.hflg = x,
                    4..=7 => h.time |= (x as c_ulong) << (8 * (p - 4)),
                    8 => h.xflags = x as c_int,
                    9 => h.os = x as c_int,
                    _ => {}
                }
                if p == 9 {
                    h.text = (self.hflg & 1) as c_int;
                    h.hcrc = ((self.hflg >> 1) & 1) as c_int;
                    self.next_field(h, H_XLEN);
                }
            }
            H_XLEN => {
                self.hxlen |= (x as usize) << (8 * p);
                if p == 1 {
                    h.extra_len = self.hxlen as c_uint;
                    if self.hxlen == 0 {
                        self.next_field(h, H_NAME);
                    } else {
                        self.hstage = H_EXTRA;
                        self.hpos = 0;
                    }
                }
            }
            H_EXTRA => {
                if !h.extra.is_null() && p < h.extra_max as usize {
                    *h.extra.add(p) = x;
                }
                if p + 1 == self.hxlen {
                    self.next_field(h, H_NAME);
                }
            }
            H_NAME | H_COMMENT => {
                let (buf, max) = if self.hstage == H_NAME { (h.name, h.name_max) } else { (h.comment, h.comm_max) };
                if !buf.is_null() && p < max as usize {
                    *buf.add(p) = x;
                }
                if x == 0 {
                    let next = self.hstage + 1;
                    self.next_field(h, next);
                }
            }
            H_HCRC => {
                if p == 1 {
                    self.hstage = H_DONE;
                }
            }
            _ => {}
        }
    }
}

#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "zlibVersion"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub extern "C" fn vz_zlibVersion() -> *const c_char {
    VERSION.as_ptr() as *const c_char
}

fn wrapper_for(window_bits: c_int) -> Option<Wrapper> {
    match window_bits {
        0 | 8..=15 => Some(Wrapper::Zlib),
        -15..=-8 => Some(Wrapper::Raw),
        // 16 and 32 take the window size from the header, as in zlib.
        16 | 24..=31 => Some(Wrapper::Gzip),
        32 | 40..=47 => Some(Wrapper::Auto),
        _ => None,
    }
}

unsafe fn version_ok(version: *const c_char, stream_size: c_int) -> bool {
    !version.is_null() && *version == b'1' as c_char && stream_size as usize == std::mem::size_of::<ZStream>()
}

/// Sets up `*strm` for a new stream with `state`.
unsafe fn init(strm: *mut ZStream, state: *mut State) {
    let s = &mut *strm;
    s.msg = std::ptr::null();
    s.total_in = 0;
    s.total_out = 0;
    s.data_type = 0;
    s.adler = if (*state).wrapper == Wrapper::Gzip { 0 } else { 1 };
    s.state = state as *mut c_void;
}

/// # Safety
/// As zlib's `inflateInit2_`: `strm` must point to a `z_stream`.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "inflateInit2_"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_inflateInit2_(strm: *mut ZStream, window_bits: c_int, version: *const c_char, stream_size: c_int) -> c_int {
    if !version_ok(version, stream_size) {
        return Z_VERSION_ERROR;
    }
    if strm.is_null() {
        return Z_STREAM_ERROR;
    }
    let w = match wrapper_for(window_bits) {
        Some(w) => w,
        None => return Z_STREAM_ERROR,
    };
    init(strm, State::boxed(w));
    Z_OK
}

/// # Safety
/// As zlib's `inflateInit_`.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "inflateInit_"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_inflateInit_(strm: *mut ZStream, version: *const c_char, stream_size: c_int) -> c_int {
    vz_inflateInit2_(strm, 15, version, stream_size)
}

unsafe fn state<'a>(strm: *mut ZStream) -> Option<&'a mut State> {
    if strm.is_null() || (*strm).state.is_null() {
        None
    } else {
        Some(&mut *((*strm).state as *mut State))
    }
}

/// # Safety
/// As zlib's `inflate`: `next_in` and `next_out` must be valid for
/// `avail_in` and `avail_out` bytes.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "inflate"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_inflate(strm: *mut ZStream, flush: c_int) -> c_int {
    let state = match state(strm) {
        Some(st) => st,
        None => return Z_STREAM_ERROR,
    };
    let s = &mut *strm;
    if (s.next_out.is_null() && s.avail_out != 0) || (s.next_in.is_null() && s.avail_in != 0) {
        return Z_STREAM_ERROR;
    }
    let input: &[u8] = if s.avail_in == 0 { &[] } else { std::slice::from_raw_parts(s.next_in, s.avail_in as usize) };
    let output: &mut [u8] = if s.avail_out == 0 { &mut [] } else { std::slice::from_raw_parts_mut(s.next_out, s.avail_out as usize) };
    let in_header = state.st.in_header();
    match state.st.inflate(input, output) {
        Ok((used, made, p)) => {
            if in_header && !state.head.is_null() {
                // The first byte tells gzip from zlib, so `is_gzip` is
                // settled once any input is used.
                let copy = if state.st.is_gzip() { used } else { 0 };
                for &x in &input[..copy] {
                    if state.hstage == H_DONE {
                        break;
                    }
                    state.header_byte(x);
                }
                if !state.st.in_header() {
                    (*state.head).done = if state.st.is_gzip() { 1 } else { -1 };
                }
            }
            s.next_in = s.next_in.wrapping_add(used);
            s.avail_in -= used as c_uint;
            s.total_in = s.total_in.wrapping_add(used as c_ulong);
            s.next_out = s.next_out.wrapping_add(made);
            s.avail_out -= made as c_uint;
            s.total_out = s.total_out.wrapping_add(made as c_ulong);
            match p {
                Progress::NeedDict => {
                    s.adler = state.st.dict_id() as c_ulong;
                    Z_NEED_DICT
                }
                Progress::End => {
                    s.adler = state.st.check() as c_ulong;
                    Z_STREAM_END
                }
                Progress::Ok if flush != Z_FINISH => {
                    s.adler = state.st.check() as c_ulong;
                    Z_OK
                }
                _ => {
                    s.adler = state.st.check() as c_ulong;
                    Z_BUF_ERROR
                }
            }
        }
        Err(_) => {
            s.msg = MSG_DATA.as_ptr() as *const c_char;
            Z_DATA_ERROR
        }
    }
}

/// # Safety
/// As zlib's `inflateEnd`.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "inflateEnd"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_inflateEnd(strm: *mut ZStream) -> c_int {
    if strm.is_null() || (*strm).state.is_null() {
        return Z_STREAM_ERROR;
    }
    let st = (*strm).state as *mut State;
    (*strm).state = std::ptr::null_mut();
    // Keep a few states for the next inflateInit; free the rest.
    keep_spare(st);
    Z_OK
}

unsafe fn reset(strm: *mut ZStream, w: Wrapper) -> c_int {
    let state = match state(strm) {
        Some(st) => st,
        None => return Z_STREAM_ERROR,
    };
    state.restart(w);
    let s = &mut *strm;
    s.total_in = 0;
    s.total_out = 0;
    s.msg = std::ptr::null();
    s.adler = if w == Wrapper::Gzip { 0 } else { 1 };
    Z_OK
}

/// # Safety
/// As zlib's `inflateReset2`.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "inflateReset2"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_inflateReset2(strm: *mut ZStream, window_bits: c_int) -> c_int {
    match wrapper_for(window_bits) {
        Some(w) => reset(strm, w),
        None => Z_STREAM_ERROR,
    }
}

/// # Safety
/// As zlib's `inflateReset`: keeps the wrapper chosen at initialization.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "inflateReset"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_inflateReset(strm: *mut ZStream) -> c_int {
    match state(strm) {
        Some(st) => reset(strm, st.wrapper),
        None => Z_STREAM_ERROR,
    }
}

/// # Safety
/// As zlib's `inflateResetKeep` (the same as `inflateReset` here).
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "inflateResetKeep"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_inflateResetKeep(strm: *mut ZStream) -> c_int {
    vz_inflateReset(strm)
}

/// # Safety
/// As zlib's `inflateSetDictionary`: `dictionary` must be valid for
/// `dict_length` bytes. For a zlib stream, call it after `inflate`
/// returns `Z_NEED_DICT`; for a raw stream, before the first `inflate`.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "inflateSetDictionary"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_inflateSetDictionary(strm: *mut ZStream, dictionary: *const u8, dict_length: c_uint) -> c_int {
    let state = match state(strm) {
        Some(st) => st,
        None => return Z_STREAM_ERROR,
    };
    if dictionary.is_null() && dict_length != 0 {
        return Z_STREAM_ERROR;
    }
    let d: &[u8] = if dict_length == 0 { &[] } else { std::slice::from_raw_parts(dictionary, dict_length as usize) };
    match state.st.set_dictionary(d) {
        Ok(()) => Z_OK,
        Err(Error::BadData) => Z_DATA_ERROR,
        Err(_) => Z_STREAM_ERROR,
    }
}

/// # Safety
/// As zlib's `inflateGetDictionary`: `dictionary`, if not null, must have
/// room for 32768 bytes.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "inflateGetDictionary"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_inflateGetDictionary(strm: *mut ZStream, dictionary: *mut u8, dict_length: *mut c_uint) -> c_int {
    let state = match state(strm) {
        Some(st) => st,
        None => return Z_STREAM_ERROR,
    };
    let h = state.st.history();
    if !dictionary.is_null() && !h.is_empty() {
        std::ptr::copy_nonoverlapping(h.as_ptr(), dictionary, h.len());
    }
    if !dict_length.is_null() {
        *dict_length = h.len() as c_uint;
    }
    Z_OK
}

/// # Safety
/// As zlib's `inflateGetHeader`: `head` and the buffers it points to must
/// stay valid until the header has been read.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "inflateGetHeader"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_inflateGetHeader(strm: *mut ZStream, head: *mut GzHeader) -> c_int {
    let state = match state(strm) {
        Some(st) => st,
        None => return Z_STREAM_ERROR,
    };
    if !matches!(state.st.wrapper(), Wrapper::Gzip | Wrapper::Auto) || head.is_null() {
        return Z_STREAM_ERROR;
    }
    (*head).done = 0;
    (*head).time = 0;
    state.head = head;
    state.hstage = H_FIXED;
    state.hpos = 0;
    state.hxlen = 0;
    Z_OK
}

/// # Safety
/// As zlib's `inflateSync`: skips input to the next `00 00 FF FF` flush
/// marker, then decodes what follows as raw DEFLATE.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "inflateSync"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_inflateSync(strm: *mut ZStream) -> c_int {
    let state = match state(strm) {
        Some(st) => st,
        None => return Z_STREAM_ERROR,
    };
    let s = &mut *strm;
    if s.avail_in == 0 {
        return Z_BUF_ERROR;
    }
    if s.next_in.is_null() {
        return Z_STREAM_ERROR;
    }
    let input = std::slice::from_raw_parts(s.next_in, s.avail_in as usize);
    let n = state.sync.scan(input);
    s.next_in = s.next_in.add(n);
    s.avail_in -= n as c_uint;
    s.total_in = s.total_in.wrapping_add(n as c_ulong);
    if !state.sync.found() {
        return Z_DATA_ERROR;
    }
    let w = state.wrapper;
    state.restart(Wrapper::Raw);
    state.wrapper = w;
    s.msg = std::ptr::null();
    Z_OK
}

/// # Safety
/// As zlib's `inflateSyncPoint`. Always 0 here: no point is reported.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "inflateSyncPoint"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_inflateSyncPoint(strm: *mut ZStream) -> c_int {
    match state(strm) {
        Some(_) => 0,
        None => Z_STREAM_ERROR,
    }
}

/// # Safety
/// As zlib's `inflateCopy`: `source` must be initialized, `dest` must
/// point to a `z_stream`.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "inflateCopy"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_inflateCopy(dest: *mut ZStream, source: *mut ZStream) -> c_int {
    let state = match state(source) {
        Some(st) => st,
        None => return Z_STREAM_ERROR,
    };
    if dest.is_null() {
        return Z_STREAM_ERROR;
    }
    let copy = Box::new(state.clone());
    std::ptr::copy_nonoverlapping(source, dest, 1);
    (*dest).state = Box::into_raw(copy) as *mut c_void;
    Z_OK
}

/// # Safety
/// As zlib's `inflatePrime`. Not supported: always `Z_STREAM_ERROR`.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "inflatePrime"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_inflatePrime(_strm: *mut ZStream, _bits: c_int, _value: c_int) -> c_int {
    Z_STREAM_ERROR
}

/// # Safety
/// As zlib's `inflateMark`. Always -65536: the position is not reported.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "inflateMark"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_inflateMark(_strm: *mut ZStream) -> c_long {
    -65536
}

/// # Safety
/// As zlib's `inflateValidate`. Checksums are always checked here.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "inflateValidate"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_inflateValidate(strm: *mut ZStream, _check: c_int) -> c_int {
    match state(strm) {
        Some(_) => Z_OK,
        None => Z_STREAM_ERROR,
    }
}

/// # Safety
/// As zlib's `inflateUndermine`, which zlib builds without by default:
/// distances beyond the output are always errors.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "inflateUndermine"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_inflateUndermine(strm: *mut ZStream, _subvert: c_int) -> c_int {
    match state(strm) {
        Some(_) => Z_DATA_ERROR,
        None => Z_STREAM_ERROR,
    }
}

/// zlib's `in_func` and `out_func` for `inflateBack`.
pub type InFunc = unsafe extern "C" fn(*mut c_void, *mut *const u8) -> c_uint;
pub type OutFunc = unsafe extern "C" fn(*mut c_void, *mut u8, c_uint) -> c_int;

/// # Safety
/// As zlib's `inflateBackInit_`. The `window` is not used: the stream has
/// its own.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "inflateBackInit_"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_inflateBackInit_(
    strm: *mut ZStream,
    window_bits: c_int,
    window: *mut u8,
    version: *const c_char,
    stream_size: c_int,
) -> c_int {
    if !version_ok(version, stream_size) {
        return Z_VERSION_ERROR;
    }
    if strm.is_null() || window.is_null() || !(8..=15).contains(&window_bits) {
        return Z_STREAM_ERROR;
    }
    init(strm, Box::into_raw(Box::new(State::new(Wrapper::Raw))));
    Z_OK
}

/// # Safety
/// As zlib's `inflateBack`: decodes a raw DEFLATE stream, taking input
/// from `in_fn` (after any already at `next_in`) and giving output to
/// `out_fn`.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "inflateBack"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_inflateBack(
    strm: *mut ZStream,
    in_fn: Option<InFunc>,
    in_desc: *mut c_void,
    out_fn: Option<OutFunc>,
    out_desc: *mut c_void,
) -> c_int {
    let state = match state(strm) {
        Some(st) => st,
        None => return Z_STREAM_ERROR,
    };
    let (in_fn, out_fn) = match (in_fn, out_fn) {
        (Some(i), Some(o)) => (i, o),
        _ => return Z_STREAM_ERROR,
    };
    let s = &mut *strm;
    state.restart(Wrapper::Raw);
    s.msg = std::ptr::null();
    let mut next = s.next_in;
    let mut have = if next.is_null() { 0 } else { s.avail_in as usize };
    let mut buf = vec![0u8; 1 << 16];
    loop {
        let input: &[u8] = if have == 0 { &[] } else { std::slice::from_raw_parts(next, have) };
        match state.st.inflate(input, &mut buf) {
            Ok((used, made, p)) => {
                next = next.wrapping_add(used);
                have -= used;
                if made > 0 && out_fn(out_desc, buf.as_mut_ptr(), made as c_uint) != 0 {
                    s.next_in = next;
                    s.avail_in = have as c_uint;
                    return Z_BUF_ERROR;
                }
                if p == Progress::End {
                    s.next_in = next;
                    s.avail_in = have as c_uint;
                    return Z_STREAM_END;
                }
                if used == 0 && made == 0 {
                    // Stalled with room for output: more input is needed.
                    if have != 0 {
                        s.msg = MSG_DATA.as_ptr() as *const c_char;
                        return Z_DATA_ERROR;
                    }
                    let mut p: *const u8 = std::ptr::null();
                    have = in_fn(in_desc, &mut p) as usize;
                    next = p;
                    if have == 0 || next.is_null() {
                        s.next_in = std::ptr::null();
                        s.avail_in = 0;
                        return Z_BUF_ERROR;
                    }
                }
            }
            Err(_) => {
                s.next_in = next;
                s.avail_in = have as c_uint;
                s.msg = MSG_DATA.as_ptr() as *const c_char;
                return Z_DATA_ERROR;
            }
        }
    }
}

/// # Safety
/// As zlib's `inflateBackEnd`.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "inflateBackEnd"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_inflateBackEnd(strm: *mut ZStream) -> c_int {
    vz_inflateEnd(strm)
}

/// # Safety
/// As zlib's `uncompress2`.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "uncompress2"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_uncompress2(dest: *mut u8, dest_len: *mut c_ulong, source: *const u8, source_len: *mut c_ulong) -> c_int {
    if dest_len.is_null() || source_len.is_null() || (source.is_null() && *source_len != 0) || (dest.is_null() && *dest_len != 0) {
        return Z_STREAM_ERROR;
    }
    let input: &[u8] = if *source_len == 0 { &[] } else { std::slice::from_raw_parts(source, *source_len as usize) };
    let output: &mut [u8] = if *dest_len == 0 { &mut [] } else { std::slice::from_raw_parts_mut(dest, *dest_len as usize) };
    let mut d = Decompressor::new();
    let r = d.decompress_into(Format::Zlib, input, output);
    match r {
        Ok((used, n)) => {
            *source_len = used as c_ulong;
            *dest_len = n as c_ulong;
            Z_OK
        }
        Err(e) => {
            *source_len = d.inf.consumed().min(input.len()) as c_ulong;
            *dest_len = d.inf.out_pos as c_ulong;
            if e == Error::InsufficientSpace {
                Z_BUF_ERROR
            } else {
                Z_DATA_ERROR
            }
        }
    }
}

/// # Safety
/// As zlib's `uncompress`.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "uncompress"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_uncompress(dest: *mut u8, dest_len: *mut c_ulong, source: *const u8, source_len: c_ulong) -> c_int {
    let mut n = source_len;
    vz_uncompress2(dest, dest_len, source, &mut n)
}

// ---------------------------------------------------------------------------
// Checksums
// ---------------------------------------------------------------------------

/// # Safety
/// As zlib's `adler32_z`: `buf` must be valid for `len` bytes, or null.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "adler32_z"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_adler32_z(adler: c_ulong, buf: *const u8, len: usize) -> c_ulong {
    if buf.is_null() {
        return 1;
    }
    let d = std::slice::from_raw_parts(buf, len);
    let (a, b) = verilith_checksum::cpu::adler32_update((adler & 0xffff) as u32 % 65521, ((adler >> 16) & 0xffff) as u32 % 65521, d);
    ((b << 16) | a) as c_ulong
}

/// # Safety
/// As zlib's `adler32`: `buf` must be valid for `len` bytes, or null.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "adler32"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_adler32(adler: c_ulong, buf: *const u8, len: c_uint) -> c_ulong {
    vz_adler32_z(adler, buf, len as usize)
}

/// # Safety
/// As zlib's `crc32_z`: `buf` must be valid for `len` bytes, or null.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "crc32_z"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_crc32_z(crc: c_ulong, buf: *const u8, len: usize) -> c_ulong {
    if buf.is_null() {
        return 0;
    }
    let d = std::slice::from_raw_parts(buf, len);
    (!verilith_checksum::cpu::crc32_update(!(crc as u32), d)) as c_ulong
}

/// # Safety
/// As zlib's `crc32`: `buf` must be valid for `len` bytes, or null.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "crc32"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_crc32(crc: c_ulong, buf: *const u8, len: c_uint) -> c_ulong {
    vz_crc32_z(crc, buf, len as usize)
}

/// The Adler-32 of A followed by B, from those of A and B and B's length
/// (proven in `glue::adler32_combine`).
fn adler32_combine(adler1: c_ulong, adler2: c_ulong, len2: i64) -> c_ulong {
    if len2 < 0 {
        return 0xffff_ffff;
    }
    crate::glue::adler32_combine(adler1 as u32, adler2 as u32, len2 as u64) as c_ulong
}

#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "adler32_combine"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub extern "C" fn vz_adler32_combine(adler1: c_ulong, adler2: c_ulong, len2: c_long) -> c_ulong {
    adler32_combine(adler1, adler2, len2 as i64)
}

#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "adler32_combine64"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub extern "C" fn vz_adler32_combine64(adler1: c_ulong, adler2: c_ulong, len2: i64) -> c_ulong {
    adler32_combine(adler1, adler2, len2)
}

/// CRC-32's polynomial, reflected.
const POLY: u32 = 0xedb8_8320;

/// `a * b` modulo the CRC polynomial, with bit 31 the coefficient of x^0.
fn multmodp(a: u32, mut b: u32) -> u32 {
    let mut p = 0;
    let mut m = 1u32 << 31;
    while m != 0 {
        if a & m != 0 {
            p ^= b;
        }
        m >>= 1;
        b = if b & 1 != 0 { (b >> 1) ^ POLY } else { b >> 1 };
    }
    p
}

/// x^(n * 2^k) modulo the CRC polynomial.
fn x2nmodp(mut n: u64, mut k: u32) -> u32 {
    let mut p = 1u32 << 31;
    while n != 0 {
        if n & 1 != 0 {
            // x^(2^k), by squaring x k times.
            let mut q = 1u32 << 30;
            for _ in 0..(k & 31) {
                q = multmodp(q, q);
            }
            p = multmodp(q, p);
        }
        n >>= 1;
        k += 1;
    }
    p
}

/// The operator `crc32_combine_op` takes for a second part of `len2` bytes.
fn crc32_combine_gen(len2: i64) -> u32 {
    x2nmodp(len2.max(0) as u64, 3)
}

#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "crc32_combine_gen64"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub extern "C" fn vz_crc32_combine_gen64(len2: i64) -> c_ulong {
    crc32_combine_gen(len2) as c_ulong
}

#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "crc32_combine_gen"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub extern "C" fn vz_crc32_combine_gen(len2: c_long) -> c_ulong {
    crc32_combine_gen(len2 as i64) as c_ulong
}

#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "crc32_combine_op"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub extern "C" fn vz_crc32_combine_op(crc1: c_ulong, crc2: c_ulong, op: c_ulong) -> c_ulong {
    (multmodp(op as u32, crc1 as u32) ^ (crc2 as u32)) as c_ulong
}

#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "crc32_combine64"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub extern "C" fn vz_crc32_combine64(crc1: c_ulong, crc2: c_ulong, len2: i64) -> c_ulong {
    vz_crc32_combine_op(crc1, crc2, crc32_combine_gen(len2) as c_ulong)
}

#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "crc32_combine"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub extern "C" fn vz_crc32_combine(crc1: c_ulong, crc2: c_ulong, len2: c_long) -> c_ulong {
    vz_crc32_combine64(crc1, crc2, len2 as i64)
}

static CRC_TABLE: [u32; 256] = {
    let mut t = [0u32; 256];
    let mut i = 0;
    while i < 256 {
        let mut c = i as u32;
        let mut k = 0;
        while k < 8 {
            c = if c & 1 != 0 { (c >> 1) ^ POLY } else { c >> 1 };
            k += 1;
        }
        t[i] = c;
        i += 1;
    }
    t
};

#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "get_crc_table"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub extern "C" fn vz_get_crc_table() -> *const u32 {
    CRC_TABLE.as_ptr()
}

// ---------------------------------------------------------------------------
// Miscellany
// ---------------------------------------------------------------------------

#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "zError"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub extern "C" fn vz_zError(err: c_int) -> *const c_char {
    let m: &[u8] = match err {
        Z_STREAM_END => b"stream end\0",
        Z_NEED_DICT => b"need dictionary\0",
        Z_ERRNO => b"file error\0",
        Z_STREAM_ERROR => b"stream error\0",
        Z_DATA_ERROR => b"data error\0",
        Z_MEM_ERROR => b"insufficient memory\0",
        Z_BUF_ERROR => b"buffer error\0",
        Z_VERSION_ERROR => b"incompatible version\0",
        _ => b"\0",
    };
    m.as_ptr() as *const c_char
}

/// As zlib's `zlibCompileFlags`: the type sizes (bits 0 to 7).
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "zlibCompileFlags"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub extern "C" fn vz_zlibCompileFlags() -> c_ulong {
    fn code(n: usize) -> c_ulong {
        match n {
            2 => 0,
            4 => 1,
            8 => 2,
            _ => 3,
        }
    }
    code(std::mem::size_of::<c_uint>())
        | code(std::mem::size_of::<c_ulong>()) << 2
        | code(std::mem::size_of::<*const c_void>()) << 4
        | code(std::mem::size_of::<c_long>()) << 6
}

// ---------------------------------------------------------------------------
// libdeflate
// ---------------------------------------------------------------------------

pub const LIBDEFLATE_SUCCESS: c_int = 0;
pub const LIBDEFLATE_BAD_DATA: c_int = 1;
pub const LIBDEFLATE_SHORT_OUTPUT: c_int = 2;
pub const LIBDEFLATE_INSUFFICIENT_SPACE: c_int = 3;

#[cfg_attr(feature = "libdeflate-abi", unsafe(export_name = "libdeflate_alloc_decompressor"))]
#[cfg_attr(not(feature = "libdeflate-abi"), unsafe(no_mangle))]
pub extern "C" fn vzlib_alloc_decompressor() -> *mut Decompressor {
    Box::into_raw(Box::new(Decompressor::new()))
}

/// # Safety
/// `options` is ignored (custom allocators are not supported).
#[cfg_attr(feature = "libdeflate-abi", unsafe(export_name = "libdeflate_alloc_decompressor_ex"))]
#[cfg_attr(not(feature = "libdeflate-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vzlib_alloc_decompressor_ex(_options: *const c_void) -> *mut Decompressor {
    vzlib_alloc_decompressor()
}

/// # Safety
/// `d` must come from `vzlib_alloc_decompressor`, or be null.
#[cfg_attr(feature = "libdeflate-abi", unsafe(export_name = "libdeflate_free_decompressor"))]
#[cfg_attr(not(feature = "libdeflate-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vzlib_free_decompressor(d: *mut Decompressor) {
    if !d.is_null() {
        drop(Box::from_raw(d));
    }
}

unsafe fn ld_decompress(
    fmt: Format,
    d: *mut Decompressor,
    input: *const u8,
    in_nbytes: usize,
    out: *mut u8,
    out_nbytes_avail: usize,
    actual_in: *mut usize,
    actual_out: *mut usize,
) -> c_int {
    if d.is_null() || (input.is_null() && in_nbytes != 0) || (out.is_null() && out_nbytes_avail != 0) {
        return LIBDEFLATE_BAD_DATA;
    }
    let i: &[u8] = if in_nbytes == 0 { &[] } else { std::slice::from_raw_parts(input, in_nbytes) };
    let o: &mut [u8] = if out_nbytes_avail == 0 { &mut [] } else { std::slice::from_raw_parts_mut(out, out_nbytes_avail) };
    match (*d).decompress_into(fmt, i, o) {
        Ok((used, n)) => {
            if !actual_in.is_null() {
                *actual_in = used;
            }
            if actual_out.is_null() {
                if n != out_nbytes_avail {
                    return LIBDEFLATE_SHORT_OUTPUT;
                }
            } else {
                *actual_out = n;
            }
            LIBDEFLATE_SUCCESS
        }
        Err(Error::InsufficientSpace) => LIBDEFLATE_INSUFFICIENT_SPACE,
        Err(_) => LIBDEFLATE_BAD_DATA,
    }
}

macro_rules! ld_fns {
    ($fmt:expr, $name:ident, $abi:literal, $name_ex:ident, $abi_ex:literal) => {
        /// # Safety
        /// As the libdeflate function of the same name.
        #[cfg_attr(feature = "libdeflate-abi", unsafe(export_name = $abi))]
        #[cfg_attr(not(feature = "libdeflate-abi"), unsafe(no_mangle))]
        pub unsafe extern "C" fn $name(d: *mut Decompressor, i: *const u8, n: usize, o: *mut u8, avail: usize, actual_out: *mut usize) -> c_int {
            ld_decompress($fmt, d, i, n, o, avail, std::ptr::null_mut(), actual_out)
        }

        /// # Safety
        /// As the libdeflate function of the same name.
        #[cfg_attr(feature = "libdeflate-abi", unsafe(export_name = $abi_ex))]
        #[cfg_attr(not(feature = "libdeflate-abi"), unsafe(no_mangle))]
        pub unsafe extern "C" fn $name_ex(
            d: *mut Decompressor,
            i: *const u8,
            n: usize,
            o: *mut u8,
            avail: usize,
            actual_in: *mut usize,
            actual_out: *mut usize,
        ) -> c_int {
            ld_decompress($fmt, d, i, n, o, avail, actual_in, actual_out)
        }
    };
}

ld_fns!(Format::Raw, vzlib_deflate_decompress, "libdeflate_deflate_decompress", vzlib_deflate_decompress_ex, "libdeflate_deflate_decompress_ex");
ld_fns!(Format::Zlib, vzlib_zlib_decompress, "libdeflate_zlib_decompress", vzlib_zlib_decompress_ex, "libdeflate_zlib_decompress_ex");
ld_fns!(Format::Gzip, vzlib_gzip_decompress, "libdeflate_gzip_decompress", vzlib_gzip_decompress_ex, "libdeflate_gzip_decompress_ex");

// ---------------------------------------------------------------------------
// Compression
// ---------------------------------------------------------------------------

pub const Z_NO_FLUSH: c_int = 0;
pub const Z_PARTIAL_FLUSH: c_int = 1;
pub const Z_SYNC_FLUSH: c_int = 2;
pub const Z_FULL_FLUSH: c_int = 3;
pub const Z_BLOCK: c_int = 5;
pub const Z_DEFLATED: c_int = 8;
pub const Z_DEFAULT_COMPRESSION: c_int = -1;

use crate::dstream::{Deflater, Flush};
use crate::deflate::FixedCodes;

/// Input `deflate()` takes in before handing out output, when the caller's
/// output buffer is small.
const D_STEP: usize = 1 << 18;

/// What `z_stream.state` points to for a deflate stream.
#[derive(Clone)]
struct DState {
    /// None once the stream is finished, and before the first `deflate()`
    /// (`fresh`), which makes it.
    d: Option<Deflater>,
    /// No `deflate()` yet since init or reset.
    fresh: bool,
    /// Output produced and not yet copied out.
    out: Pending,
    fmt: Format,
    level: u32,
    wbits: u32,
    /// The strongest flush done since input last arrived (-1: none).
    last_flush: c_int,
    /// A preset dictionary from `deflateSetDictionary`, for the deflater
    /// the first `deflate()` makes.
    dict: Option<Vec<u8>>,
}

impl DState {
    fn new(fmt: Format, level: u32, wbits: u32) -> DState {
        DState { d: None, fresh: true, out: Pending::new(), fmt, level, wbits, last_flush: -1, dict: None }
    }

    /// Makes the deflater on the first `deflate()`. When that call also
    /// ends the stream, its input is all there is, and the match tables are
    /// sized to it: zeroing full-size ones costs more than compressing a
    /// few KiB.
    fn start(&mut self, finish_with: Option<usize>) {
        if self.fresh {
            self.fresh = false;
            let mut d = match (self.dict.take(), finish_with) {
                (Some(dict), _) => Deflater::new_with_dict(self.fmt, self.level, self.wbits, &dict),
                (None, Some(n)) => Deflater::new_sized(self.fmt, self.level, self.wbits, n),
                (None, None) => Deflater::new(self.fmt, self.level, self.wbits),
            };
            d.give_fx(FX_SPARE.try_with(|w| w.borrow_mut().take()).ok().flatten());
            self.d = Some(d);
        }
    }

    /// Moves the deflater's new output into `out`.
    fn collect(&mut self) {
        if let Some(d) = self.d.as_mut() {
            let v = d.take();
            self.push(v);
        }
    }

    fn push(&mut self, v: Vec<u8>) {
        self.out = std::mem::replace(&mut self.out, Pending::new()).pushed(v);
    }

    fn pending(&self) -> usize {
        self.out.len()
    }
}

unsafe fn dstate<'a>(strm: *mut ZStream) -> Option<&'a mut DState> {
    if strm.is_null() || (*strm).state.is_null() {
        None
    } else {
        Some(&mut *((*strm).state as *mut DState))
    }
}

fn level_of(level: c_int) -> Option<u32> {
    match level {
        -1 => Some(6),
        0..=9 => Some(level as u32),
        _ => None,
    }
}

/// # Safety
/// As zlib's `deflateInit2_`.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "deflateInit2_"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_deflateInit2_(
    strm: *mut ZStream,
    level: c_int,
    method: c_int,
    window_bits: c_int,
    mem_level: c_int,
    strategy: c_int,
    version: *const c_char,
    stream_size: c_int,
) -> c_int {
    if version.is_null() || *version != b'1' as c_char || stream_size != std::mem::size_of::<ZStream>() as c_int {
        return Z_VERSION_ERROR;
    }
    if strm.is_null() {
        return Z_STREAM_ERROR;
    }
    let (fmt, bits) = match window_bits {
        8..=15 => (Format::Zlib, window_bits.max(9)),
        -15..=-8 => (Format::Raw, (-window_bits).max(9)),
        24..=31 => (Format::Gzip, (window_bits - 16).max(9)),
        _ => return Z_STREAM_ERROR,
    };
    let level = match level_of(level) {
        Some(l) => l,
        None => return Z_STREAM_ERROR,
    };
    if method != Z_DEFLATED || !(1..=9).contains(&mem_level) || !(0..=4).contains(&strategy) {
        return Z_STREAM_ERROR;
    }
    let s = &mut *strm;
    s.state = Box::into_raw(Box::new(DState::new(fmt, level, bits as u32))) as *mut c_void;
    s.total_in = 0;
    s.total_out = 0;
    s.msg = std::ptr::null();
    s.data_type = 2;
    s.adler = if fmt == Format::Gzip { 0 } else { 1 };
    Z_OK
}

/// # Safety
/// As zlib's `deflateInit_`.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "deflateInit_"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_deflateInit_(strm: *mut ZStream, level: c_int, version: *const c_char, stream_size: c_int) -> c_int {
    vz_deflateInit2_(strm, level, Z_DEFLATED, 15, 8, 0, version, stream_size)
}

/// Copies pending output to `next_out`.
unsafe fn d_drain(s: &mut ZStream, st: &mut DState) {
    if st.pending() == 0 || s.avail_out == 0 || s.next_out.is_null() {
        return;
    }
    let n = st.out.drain_into(std::slice::from_raw_parts_mut(s.next_out, s.avail_out as usize));
    s.next_out = s.next_out.add(n);
    s.avail_out -= n as c_uint;
    s.total_out = s.total_out.wrapping_add(n as c_ulong);
}

/// # Safety
/// As zlib's `deflate`.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "deflate"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_deflate(strm: *mut ZStream, flush: c_int) -> c_int {
    let st = match dstate(strm) {
        Some(st) => st,
        None => return Z_STREAM_ERROR,
    };
    let s = &mut *strm;
    if !(0..=5).contains(&flush) || s.next_out.is_null() || (s.next_in.is_null() && s.avail_in != 0) {
        return Z_STREAM_ERROR;
    }
    if st.fresh && flush == Z_FINISH && s.avail_out != 0 && st.dict.is_none() && crate::par::wanted(s.avail_in as usize, st.level) {
        // The whole stream in one call, and threads are allowed
        // (`vzlib_set_threads`): compress it in parallel. The stream is
        // then finished, as after the serial path below.
        let n = s.avail_in as usize;
        let c = crate::par::compress(st.fmt, std::slice::from_raw_parts(s.next_in, n), st.level, st.wbits, crate::par::CHUNK, crate::par::threads());
        st.fresh = false;
        // The check value is in the trailer; a raw stream has none, and
        // zlib leaves `adler` at 1 there.
        s.adler = match st.fmt {
            Format::Zlib => u32::from_be_bytes(c[c.len() - 4..].try_into().unwrap()) as c_ulong,
            Format::Gzip => u32::from_le_bytes(c[c.len() - 8..c.len() - 4].try_into().unwrap()) as c_ulong,
            Format::Raw => 1,
        };
        s.next_in = s.next_in.add(n);
        s.avail_in = 0;
        s.total_in = s.total_in.wrapping_add(n as c_ulong);
        st.push(c);
    }
    st.start(if flush == Z_FINISH { Some(s.avail_in as usize) } else { None });
    if st.d.is_none() && flush != Z_FINISH {
        return Z_STREAM_ERROR;
    }
    if st.d.is_none() && s.avail_in != 0 {
        return Z_BUF_ERROR;
    }
    if s.avail_out == 0 {
        return Z_BUF_ERROR;
    }
    let in0 = s.avail_in;
    let out0 = s.avail_out;
    d_drain(s, st);
    // Take input in steps while the output keeps up.
    while s.avail_in > 0 && st.pending() == 0 {
        let d = st.d.as_mut().unwrap();
        let n = (s.avail_in as usize).min(D_STEP);
        let input = std::slice::from_raw_parts(s.next_in, n);
        d.write(input, Flush::None);
        s.next_in = s.next_in.add(n);
        s.avail_in -= n as c_uint;
        s.total_in = s.total_in.wrapping_add(n as c_ulong);
        s.adler = d.check() as c_ulong;
        st.last_flush = -1;
        st.collect();
        d_drain(s, st);
    }
    if s.avail_in == 0 && st.pending() == 0 && st.d.is_some() && flush != Z_NO_FLUSH {
        if flush == Z_FINISH {
            let d = st.d.take().unwrap();
            let (rest, fx) = d.finish_keep();
            keep_fx(fx);
            st.push(rest);
            d_drain(s, st);
        } else if st.last_flush < flush.min(Z_FULL_FLUSH) || flush == Z_BLOCK {
            let mode = match flush {
                Z_BLOCK => Flush::Block,
                Z_FULL_FLUSH => Flush::Full,
                _ => Flush::Sync,
            };
            let d = st.d.as_mut().unwrap();
            d.write(&[], mode);
            st.last_flush = if flush == Z_BLOCK { st.last_flush } else { flush.min(Z_FULL_FLUSH) };
            st.collect();
            d_drain(s, st);
        }
    }
    if st.d.is_none() && st.pending() == 0 {
        return Z_STREAM_END;
    }
    if s.avail_in == in0 && s.avail_out == out0 {
        return Z_BUF_ERROR;
    }
    Z_OK
}

/// # Safety
/// As zlib's `deflateEnd`.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "deflateEnd"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_deflateEnd(strm: *mut ZStream) -> c_int {
    if strm.is_null() || (*strm).state.is_null() {
        return Z_STREAM_ERROR;
    }
    let mut st = Box::from_raw((*strm).state as *mut DState);
    (*strm).state = std::ptr::null_mut();
    if let Some(d) = st.d.as_mut() {
        keep_fx(d.take_fx());
    }
    // zlib reports a stream ended before it finished.
    if st.d.is_some() {
        Z_DATA_ERROR
    } else {
        Z_OK
    }
}

/// # Safety
/// As zlib's `deflateReset`.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "deflateReset"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_deflateReset(strm: *mut ZStream) -> c_int {
    let st = match dstate(strm) {
        Some(st) => st,
        None => return Z_STREAM_ERROR,
    };
    *st = DState::new(st.fmt, st.level, st.wbits);
    let s = &mut *strm;
    s.total_in = 0;
    s.total_out = 0;
    s.msg = std::ptr::null();
    s.adler = if st.fmt == Format::Gzip { 0 } else { 1 };
    Z_OK
}

/// # Safety
/// As zlib's `deflateResetKeep`.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "deflateResetKeep"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_deflateResetKeep(strm: *mut ZStream) -> c_int {
    vz_deflateReset(strm)
}

/// # Safety
/// As zlib's `deflateParams`. The strategy is accepted and not used.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "deflateParams"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_deflateParams(strm: *mut ZStream, level: c_int, strategy: c_int) -> c_int {
    let st = match dstate(strm) {
        Some(st) => st,
        None => return Z_STREAM_ERROR,
    };
    let level = match level_of(level) {
        Some(l) => l,
        None => return Z_STREAM_ERROR,
    };
    if !(0..=4).contains(&strategy) {
        return Z_STREAM_ERROR;
    }
    if let Some(d) = st.d.as_mut() {
        if level != st.level {
            d.set_level(level);
            st.collect();
            d_drain(&mut *strm, st);
        }
    }
    // Output from ending the block waits in the state for the next
    // `deflate()`, so there is no Z_BUF_ERROR case.
    st.level = level;
    Z_OK
}

/// # Safety
/// As zlib's `deflateTune`; the parameters are accepted and not used.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "deflateTune"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_deflateTune(strm: *mut ZStream, _good: c_int, _lazy: c_int, _nice: c_int, _chain: c_int) -> c_int {
    match dstate(strm) {
        Some(_) => Z_OK,
        None => Z_STREAM_ERROR,
    }
}

/// The most output compressing `n` bytes can take, with any wrapper.
fn bound(n: u64) -> u64 {
    n + (n >> 11) + 64
}

/// # Safety
/// As zlib's `deflateBound`.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "deflateBound"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_deflateBound(_strm: *mut ZStream, source_len: c_ulong) -> c_ulong {
    bound(source_len as u64) as c_ulong
}

/// As zlib's `compressBound`.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "compressBound"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub extern "C" fn vz_compressBound(source_len: c_ulong) -> c_ulong {
    bound(source_len as u64) as c_ulong
}

/// # Safety
/// As zlib's `deflatePending`.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "deflatePending"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_deflatePending(strm: *mut ZStream, pending: *mut c_uint, bits: *mut c_int) -> c_int {
    let st = match dstate(strm) {
        Some(st) => st,
        None => return Z_STREAM_ERROR,
    };
    let (bytes, nbits) = st.d.as_ref().map_or((0, 0), |d| d.pending());
    if !pending.is_null() {
        *pending = (st.pending() + bytes) as c_uint;
    }
    if !bits.is_null() {
        *bits = nbits as c_int;
    }
    Z_OK
}

/// # Safety
/// As zlib's `deflateCopy`.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "deflateCopy"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_deflateCopy(dest: *mut ZStream, source: *mut ZStream) -> c_int {
    let st = match dstate(source) {
        Some(st) => st,
        None => return Z_STREAM_ERROR,
    };
    if dest.is_null() {
        return Z_STREAM_ERROR;
    }
    std::ptr::copy_nonoverlapping(source, dest, 1);
    (*dest).state = Box::into_raw(Box::new(st.clone())) as *mut c_void;
    Z_OK
}

/// # Safety
/// As zlib's `deflateSetDictionary`, for zlib and raw streams, before the
/// first `deflate()` (or after a reset). The compressor then starts after
/// the dictionary (`Deflater::new_with_dict`, verified): matches may refer
/// into its last 32 KiB, and a zlib header names its Adler-32 with FDICT.
/// Gzip streams, and raw streams that have already taken input, get
/// `Z_STREAM_ERROR` (zlib allows the latter). Calling it twice keeps the
/// second dictionary; an empty one means none, as in zlib.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "deflateSetDictionary"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_deflateSetDictionary(strm: *mut ZStream, dictionary: *const u8, dict_length: c_uint) -> c_int {
    let st = match dstate(strm) {
        Some(st) => st,
        None => return Z_STREAM_ERROR,
    };
    if (dictionary.is_null() && dict_length != 0) || st.fmt == Format::Gzip || !st.fresh {
        return Z_STREAM_ERROR;
    }
    let dict: &[u8] = if dict_length == 0 { &[] } else { std::slice::from_raw_parts(dictionary, dict_length as usize) };
    if dict.is_empty() {
        st.dict = None;
        (*strm).adler = 1;
        return Z_OK;
    }
    // zlib leaves the dictionary's Adler-32 in strm->adler.
    (*strm).adler = crate::checksum::adler32(dict) as c_ulong;
    st.dict = Some(dict.to_vec());
    Z_OK
}

/// # Safety
/// As zlib's `deflateSetHeader`; custom gzip headers are not supported
/// (`Z_STREAM_ERROR`). The header written has no name, time or extra field.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "deflateSetHeader"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_deflateSetHeader(_strm: *mut ZStream, _head: *mut GzHeader) -> c_int {
    Z_STREAM_ERROR
}

/// # Safety
/// As zlib's `deflatePrime`; not supported (`Z_STREAM_ERROR`).
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "deflatePrime"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_deflatePrime(_strm: *mut ZStream, _bits: c_int, _value: c_int) -> c_int {
    Z_STREAM_ERROR
}

/// # Safety
/// As zlib's `compress2`.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "compress2"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_compress2(dest: *mut u8, dest_len: *mut c_ulong, source: *const u8, source_len: c_ulong, level: c_int) -> c_int {
    if dest_len.is_null() || (source.is_null() && source_len != 0) || (dest.is_null() && *dest_len != 0) {
        return Z_STREAM_ERROR;
    }
    let level = match level_of(level) {
        Some(l) => l,
        None => return Z_STREAM_ERROR,
    };
    let input: &[u8] = if source_len == 0 { &[] } else { std::slice::from_raw_parts(source, source_len as usize) };
    let c = if crate::par::wanted(input.len(), level) {
        crate::par::compress(Format::Zlib, input, level, 15, crate::par::CHUNK, crate::par::threads())
    } else {
        crate::deflate::zlib_compress(input, level)
    };
    let n = c.len().min(*dest_len as usize);
    if n > 0 {
        std::ptr::copy_nonoverlapping(c.as_ptr(), dest, n);
    }
    *dest_len = n as c_ulong;
    if n < c.len() {
        Z_BUF_ERROR
    } else {
        Z_OK
    }
}

/// Sets how many threads `compress`, `compress2` and a `deflate` call that
/// is given a whole stream at once (`Z_FINISH` on the first call) may use,
/// process-wide: 1 for none, 0 for one per CPU. Not part of zlib. The
/// default is 1, or the environment variable `VZLIB_THREADS` if it is set
/// when compression first runs. Inputs under 512 KiB, level 0 and streams
/// with a preset dictionary are compressed on the calling thread whatever
/// this says. Returns the number of threads now allowed.
#[unsafe(no_mangle)]
pub extern "C" fn vzlib_set_threads(n: c_int) -> c_int {
    crate::par::set_threads(n.max(0) as usize);
    crate::par::threads().min(c_int::MAX as usize) as c_int
}

/// # Safety
/// As zlib's `compress`.
#[cfg_attr(feature = "zlib-abi", unsafe(export_name = "compress"))]
#[cfg_attr(not(feature = "zlib-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vz_compress(dest: *mut u8, dest_len: *mut c_ulong, source: *const u8, source_len: c_ulong) -> c_int {
    vz_compress2(dest, dest_len, source, source_len, Z_DEFAULT_COMPRESSION)
}
