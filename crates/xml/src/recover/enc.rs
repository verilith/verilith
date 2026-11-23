//! Input decoding as libxml2 does it without iconv (encoding.c, xmlIO.c,
//! parserInternals.c): the built-in decoders, the names they are found by,
//! the chunks the buffer is converted in, and the encoding detection and
//! switching of `xmlDetectEncoding` and `xmlSetDeclaredEncoding`.
use super::codes::*;
use super::tables::*;
use super::*;
use crate::lenient::{chunk_ascii, chunk_latin1, chunk_utf16, put, CHUNK_INPUT, CHUNK_OK, CHUNK_SPACE};
use vstd::slice::slice_subrange;
use crate::lenient::vec_of;
use vstd::prelude::*;

verus! {


/// A built-in input decoder (`defaultHandlers` with an input function).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Enc {
    Utf16Le,
    Utf16Be,
    Latin1,
    Ascii,
    /// One of the 8-bit tables, by index into `EIGHT_BIT`.
    Table(u8),
}

/// `a == b`.
pub fn enc_eq(a: Option<Enc>, b: Option<Enc>) -> (r: bool) {
    match (a, b) {
        (None, None) => true,
        (Some(Enc::Utf16Le), Some(Enc::Utf16Le)) => true,
        (Some(Enc::Utf16Be), Some(Enc::Utf16Be)) => true,
        (Some(Enc::Latin1), Some(Enc::Latin1)) => true,
        (Some(Enc::Ascii), Some(Enc::Ascii)) => true,
        (Some(Enc::Table(x)), Some(Enc::Table(y))) => x == y,
        _ => false,
    }
}

/// `xmlParseCharEncodingInternal`: the `xmlCharEncoding` of a name, or -1.
fn encoding_id(name: &[u8]) -> i32 {
    let mut lo = 0usize;
    let mut hi = ENC_NAMES_LEN;
    while lo < hi
        invariant
            hi <= ENC_NAMES_LEN,
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        let (n, id) = enc_name(mid);
        let d = cmp_ci(name, n);
        if d == 0 {
            return id as i32;
        } else if d < 0 {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }
    -1
}

use crate::lenient::cmp_ci;

/// The decoder of a default handler, by `xmlCharEncoding`: `Ok(None)` for
/// UTF-8 (no decoder), `Err` for a handler with no input function.
fn handler_of(id: i32) -> (r: Result<Option<Enc>, i32>)
    ensures
        r matches Ok(Some(Enc::Table(t))) ==> t < 15,
{
    match id {
        1 => Ok(None),
        2 => Ok(Some(Enc::Utf16Le)),
        3 => Ok(Some(Enc::Utf16Be)),
        10 => Ok(Some(Enc::Latin1)),
        22 => Ok(Some(Enc::Ascii)),
        // "UTF-16" decodes as little-endian.
        23 => Ok(Some(Enc::Utf16Le)),
        _ => {
            let mut k: usize = 0;
            while k < 15
                decreases 15 - k,
            {
                if EIGHT_BIT_IDS[k] as i32 == id {
                    return Ok(Some(Enc::Table(k as u8)));
                }
                k = k + 1;
            }
            Err(ERR_UNSUPPORTED_ENCODING)
        }
    }
}

/// `xmlCreateCharEncodingHandler(name, XML_ENC_INPUT)`.
pub fn lookup_encoding(name: &[u8], html: bool) -> (r: Result<Option<Enc>, i32>)
    ensures
        r matches Ok(Some(Enc::Table(t))) ==> t < 15,
{
    let mut id = encoding_id(name);
    if id == 1 {
        return Ok(None);
    }
    if id > 0 && id < 32 {
        if html {
            if id == 22 || id == 10 {
                id = 31;
            } else if id == 9 || id == 23 {
                id = 2;
            }
        }
        return handler_of(id);
    }
    Err(ERR_UNSUPPORTED_ENCODING)
}

/// `xmlLookupCharEncodingHandler`.
pub fn lookup_id(id: i32) -> (r: Result<Option<Enc>, i32>)
    ensures
        r matches Ok(Some(Enc::Table(t))) ==> t < 15,
{
    if id <= 0 || id >= 32 {
        return Err(ERR_UNSUPPORTED_ENCODING);
    }
    if id == 1 {
        return Ok(None);
    }
    handler_of(id)
}


/// One decoder call (`xmlEncInputChunk`): converts `inp` into at most
/// `room` bytes of `out`; returns the bytes read and the result.
fn chunk(e: Enc, inp: &[u8], out: &mut Vec<u8>, room: usize, flush: bool) -> (r: (usize, u8))
    ensures
        r.0 <= inp@.len(),
        r.1 <= CHUNK_INPUT,
{
    let n = inp.len();
    let (i, mut res) = match e {
        // Verified (`crate::lenient`): each writes the spec's decoding of
        // what it reads.
        Enc::Utf16Le => chunk_utf16(true, inp, out, room),
        Enc::Utf16Be => chunk_utf16(false, inp, out, room),
        Enc::Latin1 => chunk_latin1(inp, out, room),
        Enc::Ascii => chunk_ascii(inp, out, room),
        Enc::Table(t) => chunk_table(t, inp, out, room),
    };
    if flush && res == CHUNK_OK && i != n {
        res = CHUNK_INPUT;
    }
    (i, res)
}

/// An 8-bit character set (`ISO-8859-x` and the like) to UTF-8: the
/// table gives the code point of each byte from 0x80, 0 for none.
fn chunk_table(t: u8, inp: &[u8], out: &mut Vec<u8>, room: usize) -> (r: (usize, u8))
    ensures
        r.0 <= inp@.len(),
        r.1 <= CHUNK_INPUT,
{
    let tk = (t as usize) % 15;
    let n = inp.len();
    let mut i: usize = 0;
    let mut left = room;
    while i < n
        invariant
            i <= n == inp@.len(),
            tk < 15,
        decreases n - i,
    {
        let b = inp[i];
        let c: u32 = if b < 0x80 { b as u32 } else { EIGHT_BIT[tk][(b - 0x80) as usize] as u32 };
        if c == 0 && b >= 0x80 {
            return (i, CHUNK_INPUT);
        }
        if !put(out, c, &mut left) {
            return (i, CHUNK_SPACE);
        }
        i = i + 1;
    }
    (i, CHUNK_OK)
}

/// `xmlCharEncInput`: converts what was read, up to `max_out` bytes of
/// output. Returns the bytes produced, or the error code.
pub fn char_enc_input(buf: &mut Vec<u8>, src: &mut Source, max_out: usize, flush: bool) -> (r: Result<usize, i32>)
    ensures
        final(src).raw == old(src).raw,
        final(src).mode == old(src).mode,
        final(src).enc == old(src).enc,
        final(src).delivered == old(src).delivered,
        final(src).pos <= final(src).raw@.len(),
        old(src).pos <= old(src).raw@.len() ==> final(src).pos >= old(src).pos || final(src).pos == old(src).delivered,
{
    let e = match src.enc {
        Some(e) => e,
        None => {
            if src.pos > src.raw.len() {
                src.pos = src.raw.len();
            }
            return Ok(0);
        }
    };
    let rl = src.raw.len();
    let end = if src.delivered <= rl { src.delivered } else { rl };
    let start = if src.pos < end { src.pos } else { end };
    if end - start == 0 && !flush {
        src.pos = start;
        return Ok(0);
    }
    let before = buf.len();
    let (used, res) = chunk(e, slice_subrange(src.raw.as_slice(), start, end), buf, max_out, flush);
    src.pos = start + used;
    if res == CHUNK_INPUT {
        src.error = ERR_INVALID_ENCODING;
        return Err(ERR_INVALID_ENCODING);
    }
    Ok(buf.len().saturating_sub(before))
}

/// `xmlParserInputBufferGrow(buf, len)`.
pub fn buffer_grow(buf: &mut Vec<u8>, src: &mut Source, len: usize) -> (r: i32)
    ensures
        final(src).raw == old(src).raw,
        final(src).mode == old(src).mode,
        final(src).enc == old(src).enc,
{
    if src.error != 0 {
        return -1;
    }
    let len = if len < MINLEN { MINLEN } else { len };
    let mut res: i32 = 0;
    if src.mode == Mode::Stream {
        let left = src.raw.len().saturating_sub(src.delivered);
        let n = if src.eof { 0 } else if left < len { left } else { len };
        if n == 0 {
            src.eof = true;
        }
        src.delivered = src.delivered + n;
        res = if n > i32::MAX as usize { i32::MAX } else { n as i32 };
        if src.enc.is_none() {
            let from = src.pos;
            let to = src.delivered;
            if from < to && to <= src.raw.len() {
                buf.extend_from_slice(slice_subrange(src.raw.as_slice(), from, to));
            }
            src.pos = to;
        }
    }
    if src.enc.is_some() {
        let size = if src.mode == Mode::Memory { len } else { usize::MAX };
        match char_enc_input(buf, src, size, false) {
            Ok(n) => res = if n > i32::MAX as usize { i32::MAX } else { n as i32 },
            Err(_) => return -1,
        }
    }
    res
}

/// Sets up a fresh input over its source: a memory buffer without a
/// decoder is all there from the start.
pub fn init_buffer(i: &mut Input) {
    let take = match &i.src {
        Some(src) => src.mode == Mode::Memory && src.enc.is_none(),
        None => false,
    };
    if take {
        let mut raw: Vec<u8> = Vec::new();
        match &mut i.src {
            Some(src) => {
                std::mem::swap(&mut raw, &mut src.raw);
                src.pos = 0;
                src.delivered = 0;
            },
            None => {},
        }
        i.buf = raw;
    }
}

impl<S: Sink> Parser<S> {
    /// `xmlInputSetEncodingHandler` on the current input; the error code.
    pub fn set_encoding_handler(&mut self, h: Option<Enc>) -> i32
        requires
            old(self).wf(),
        ensures
            final(self).moves(old(self)),
    {
        let input = self.inp_mut();
        input.flags = input.flags | INPUT_HAS_ENCODING;
        let processed = input.cur;
        let code = match &mut input.src {
            None => ERR_ARGUMENT,
            Some(src) => {
                if enc_eq(src.enc, h) {
                    ERR_OK
                } else if src.enc.is_some() {
                    src.enc = h;
                    ERR_OK
                } else {
                    match h {
                        None => ERR_OK,
                        Some(h) => {
                            // The buffer becomes the raw input, less what
                            // was read: the rest of the buffer, the bytes
                            // read but not yet moved to it, then the unread.
                            let mut raw: Vec<u8> = Vec::new();
                            if processed < input.buf.len() {
                                raw.extend_from_slice(slice_subrange(input.buf.as_slice(), processed, input.buf.len()));
                            }
                            let rl = src.raw.len();
                            let rest_from = if src.pos < rl { src.pos } else { rl };
                            let undelivered_from = if src.delivered > rest_from { src.delivered } else { rest_from };
                            if rest_from < undelivered_from && undelivered_from <= rl {
                                raw.extend_from_slice(slice_subrange(src.raw.as_slice(), rest_from, undelivered_from));
                            }
                            let delivered = raw.len();
                            if undelivered_from < rl {
                                raw.extend_from_slice(slice_subrange(src.raw.as_slice(), undelivered_from, rl));
                            }
                            src.raw = raw;
                            src.pos = 0;
                            src.delivered = if src.mode == Mode::Memory { src.raw.len() } else { delivered };
                            src.enc = Some(h);
                            input.consumed = input.consumed.saturating_add(processed as u64);
                            input.buf = Vec::new();
                            input.base = 0;
                            input.cur = 0;
                            match char_enc_input(&mut input.buf, src, MINLEN, false) {
                                Err(c) => c,
                                Ok(_) => ERR_OK,
                            }
                        },
                    }
                }
            },
        };
        code
    }

    /// `xmlSwitchEncoding` with a detected encoding.
    pub fn switch_encoding(&mut self, id: i32)
        requires
            old(self).wf(),
        ensures
            final(self).moves(old(self)),
    {
        match lookup_id(id) {
            Err(code) => self.fatal(code, None),
            Ok(h) => {
                let code = self.set_encoding_handler(h);
                if code != ERR_OK {
                    self.err_io(code);
                }
            },
        }
    }

    /// `xmlSwitchInputEncodingName`, for an encoding given before parsing
    /// (`xmlCtxtReadMemory`'s `encoding`).
    pub fn switch_encoding_name(&mut self, name: &[u8]) -> i32
        requires
            old(self).wf(),
        ensures
            final(self).moves(old(self)),
    {
        match lookup_encoding(name, false) {
            Err(code) => {
                if code == ERR_UNSUPPORTED_ENCODING {
                    let m = cat(&[b"Unsupported encoding: ", name, b"\n"]);
                    self.warning(ERR_UNSUPPORTED_ENCODING, m.as_slice(), Some(name), None);
                } else {
                    self.fatal(code, Some(name));
                }
                -1
            },
            Ok(h) => {
                let code = self.set_encoding_handler(h);
                if code != ERR_OK {
                    self.err_io(code);
                    return -1;
                }
                0
            },
        }
    }

    /// `xmlDetectEncoding`.
    pub fn detect_encoding(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).moves(old(self)),
    {
        if self.grow_now() < 0 {
            return;
        }
        if self.avail() < 4 {
            return;
        }
        let b0 = self.nxt(0);
        let b1 = self.nxt(1);
        let b2 = self.nxt(2);
        let b3 = self.nxt(3);
        if self.inp().flags & INPUT_HAS_ENCODING != 0 {
            if b0 == 0xEF && b1 == 0xBB && b2 == 0xBF {
                let i = self.inp_mut();
                i.cur = i.cur.saturating_add(3);
            }
            return;
        }
        let html = self.html;
        let (enc, auto, bom): (i32, u32, usize) = if b0 == 0x00 && !html && b1 == 0 && b2 == 0 && b3 == 0x3C {
            (5, INPUT_AUTO_OTHER, 0)
        } else if b0 == 0x00 && b1 == 0x3C && b2 == 0 && b3 == 0x3F {
            (3, INPUT_AUTO_UTF16BE, 0)
        } else if b0 == 0x3C && b1 == 0 && !html && b2 == 0 && b3 == 0 {
            (4, INPUT_AUTO_OTHER, 0)
        } else if b0 == 0x3C && b1 == 0 && b2 == 0x3F && b3 == 0 {
            (2, INPUT_AUTO_UTF16LE, 0)
        } else if b0 == 0x4C && !html && b1 == 0x6F && b2 == 0xA7 && b3 == 0x94 {
            (6, INPUT_AUTO_OTHER, 0)
        } else if b0 == 0xEF && b1 == 0xBB && b2 == 0xBF {
            (1, INPUT_AUTO_UTF8, 3)
        } else if b0 == 0xFE && b1 == 0xFF {
            (3, INPUT_AUTO_UTF16BE, 2)
        } else if b0 == 0xFF && b1 == 0xFE {
            (2, INPUT_AUTO_UTF16LE, 2)
        } else {
            (0, 0, 0)
        };
        if bom > 0 {
            let i = self.inp_mut();
            i.cur = i.cur.saturating_add(bom);
        }
        if enc != 0 {
            let i = self.inp_mut();
            i.flags = i.flags | auto;
            if enc == 6 {
                // xmlDetectEBCDIC: no EBCDIC decoder without iconv.
                self.fatal(ERR_UNSUPPORTED_ENCODING, Some(b"detecting EBCDIC\n"));
            } else {
                self.switch_encoding(enc);
            }
        }
    }

    /// `xmlSetDeclaredEncoding`.
    pub fn set_declared_encoding(&mut self, encoding: Vec<u8>)
        requires
            old(self).wf(),
        ensures
            final(self).evolves(old(self)),
            final(self).inputs@.len() == old(self).inputs@.len(),
    {
        let mut encoding = encoding;
        let flags = self.inp().flags;
        if flags & INPUT_HAS_ENCODING == 0 && self.options & PARSE_IGNORE_ENC == 0 {
            match lookup_encoding(encoding.as_slice(), self.html) {
                Err(code) => {
                    self.fatal(code, Some(encoding.as_slice()));
                    return;
                },
                Ok(h) => {
                    let code = self.set_encoding_handler(h);
                    if code != ERR_OK {
                        self.err_io(code);
                        return;
                    }
                    let i = self.inp_mut();
                    i.flags = i.flags | INPUT_USES_ENC_DECL;
                },
            }
        } else if flags & INPUT_AUTO_ENCODING != 0 {
            let a = flags & INPUT_AUTO_ENCODING;
            let auto: &[u8] = if a == INPUT_AUTO_UTF8 {
                b"UTF-8"
            } else if a == INPUT_AUTO_UTF16LE {
                b"UTF-16LE"
            } else if a == INPUT_AUTO_UTF16BE {
                b"UTF-16BE"
            } else {
                b""
            };
            if auto.len() > 0 {
                let name = encoding.as_slice();
                let matched = if a == INPUT_AUTO_UTF8 {
                    eq_ci(name, b"UTF-8") || eq_ci(name, b"UTF8")
                } else {
                    eq_ci(name, b"UTF-16") || eq_ci(name, auto) || eq_ci(name, b"UTF16")
                };
                if !matched {
                    let m = cat(&[b"Encoding '", name, b"' doesn't match auto-detected '", auto, b"'\n"]);
                    self.warning(WAR_ENCODING_MISMATCH, m.as_slice(), Some(name), Some(auto));
                    encoding = vec_of(auto);
                }
            }
        }
        self.encoding = Some(encoding.clone());
        self.sink.set_encoding(Some(encoding.as_slice()));
    }

    /// `xmlParserCheckEOF`.
    pub fn check_eof(&mut self, code: i32)
        requires
            old(self).wf(),
        ensures
            final(self).moves(old(self)),
    {
        if self.sink.err_no() != ERR_OK {
            return;
        }
        if !self.at_end() {
            self.fatal(code, None);
            return;
        }
        let r = {
            let input = self.inp_mut();
            match &mut input.src {
                Some(src) => {
                    if src.enc.is_some() {
                        Some(char_enc_input(&mut input.buf, src, 64, true))
                    } else {
                        None
                    }
                },
                None => None,
            }
        };
        match r {
            Some(Err(c)) => self.err_io(c),
            Some(Ok(_)) => {
                if !self.at_end() {
                    self.fatal(ERR_INTERNAL_ERROR, Some(b"expected EOF"));
                }
            },
            None => {},
        }
    }
}

} // verus!
