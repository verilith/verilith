//! Input decoding as libxml2 does it without iconv (encoding.c, xmlIO.c,
//! parserInternals.c): the built-in decoders, the names they are found by,
//! the chunks the buffer is converted in, and the encoding detection and
//! switching of `xmlDetectEncoding` and `xmlSetDeclaredEncoding`.
use super::codes::*;
use super::tables::*;
use super::*;

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

/// `xmlParseCharEncodingInternal`: the `xmlCharEncoding` of a name, or -1.
fn encoding_id(name: &[u8]) -> i32 {
    let mut lo = 0usize;
    let mut hi = ENC_NAMES.len();
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        let (n, id) = ENC_NAMES[mid];
        match cmp_ci(name, n) {
            core::cmp::Ordering::Equal => return id as i32,
            core::cmp::Ordering::Less => hi = mid,
            core::cmp::Ordering::Greater => lo = mid + 1,
        }
    }
    -1
}

/// `xmlStrcasecmp`.
fn cmp_ci(a: &[u8], b: &[u8]) -> core::cmp::Ordering {
    let mut i = 0;
    loop {
        let x = at(a, i).to_ascii_lowercase();
        let y = at(b, i).to_ascii_lowercase();
        if x != y || x == 0 {
            return x.cmp(&y);
        }
        i += 1;
    }
}

/// The decoder of a default handler, by `xmlCharEncoding`: `Ok(None)` for
/// UTF-8 (no decoder), `Err` for a handler with no input function.
fn handler_of(id: i32) -> Result<Option<Enc>, i32> {
    match id {
        1 => Ok(None),
        2 => Ok(Some(Enc::Utf16Le)),
        3 => Ok(Some(Enc::Utf16Be)),
        10 => Ok(Some(Enc::Latin1)),
        22 => Ok(Some(Enc::Ascii)),
        // "UTF-16" decodes as little-endian.
        23 => Ok(Some(Enc::Utf16Le)),
        _ => {
            let mut k = 0;
            while k < EIGHT_BIT_IDS.len() {
                if EIGHT_BIT_IDS[k] as i32 == id {
                    return Ok(Some(Enc::Table(k as u8)));
                }
                k += 1;
            }
            Err(ERR_UNSUPPORTED_ENCODING)
        }
    }
}

/// `xmlCreateCharEncodingHandler(name, XML_ENC_INPUT)`.
pub fn lookup_encoding(name: &[u8], html: bool) -> Result<Option<Enc>, i32> {
    let mut id = encoding_id(name);
    if id == 1 {
        return Ok(None);
    }
    if id > 0 && id < 32 {
        if html {
            id = match id {
                22 | 10 => 31,
                9 | 23 => 2,
                x => x,
            };
        }
        return handler_of(id);
    }
    Err(ERR_UNSUPPORTED_ENCODING)
}

/// `xmlLookupCharEncodingHandler`.
pub fn lookup_id(id: i32) -> Result<Option<Enc>, i32> {
    if id <= 0 || id >= 32 {
        return Err(ERR_UNSUPPORTED_ENCODING);
    }
    if id == 1 {
        return Ok(None);
    }
    handler_of(id)
}

/// `xmlCharEncError`.
#[derive(PartialEq, Eq)]
enum Res {
    Success,
    Space,
    Input,
}

/// UTF-8 bytes of `c` appended, if `room` allows.
fn put(out: &mut Vec<u8>, c: u32, room: &mut usize) -> bool {
    let n = if c < 0x80 { 1 } else if c < 0x800 { 2 } else if c < 0x10000 { 3 } else { 4 };
    if *room < n {
        return false;
    }
    *room -= n;
    push_char(out, c);
    true
}

/// One decoder call (`xmlEncInputChunk`): converts `inp` into at most
/// `room` bytes of `out`; returns the bytes read and the result.
fn chunk(e: Enc, inp: &[u8], out: &mut Vec<u8>, mut room: usize, flush: bool) -> (usize, Res) {
    let mut i = 0usize;
    let n = inp.len();
    let mut res = Res::Success;
    match e {
        Enc::Utf16Le | Enc::Utf16Be => {
            let end = n & !1usize;
            let w = |k: usize| -> u32 {
                if e == Enc::Utf16Le {
                    at(inp, k) as u32 | ((at(inp, k + 1) as u32) << 8)
                } else {
                    ((at(inp, k) as u32) << 8) | at(inp, k + 1) as u32
                }
            };
            while i < end {
                let c = w(i);
                if (c & 0xF800) != 0xD800 {
                    if !put(out, c, &mut room) {
                        res = Res::Space;
                        break;
                    }
                    i += 2;
                } else {
                    if (c & 0xFC00) != 0xD800 {
                        res = Res::Input;
                        break;
                    }
                    if end - i < 4 {
                        break;
                    }
                    let d = w(i + 2);
                    if (d & 0xFC00) != 0xDC00 {
                        res = Res::Input;
                        break;
                    }
                    let cp = ((c - 0xD800) << 10) + (d - 0xDC00) + 0x10000;
                    if !put(out, cp, &mut room) {
                        res = Res::Space;
                        break;
                    }
                    i += 4;
                }
            }
        }
        Enc::Latin1 => {
            while i < n {
                if !put(out, inp[i] as u32, &mut room) {
                    res = Res::Space;
                    break;
                }
                i += 1;
            }
        }
        Enc::Ascii => {
            // asciiToAscii checks the space first, then the bytes.
            let take = if room < n { room } else { n };
            if room < n {
                res = Res::Space;
            }
            while i < take {
                if inp[i] >= 0x80 {
                    res = Res::Input;
                    break;
                }
                out.push(inp[i]);
                i += 1;
            }
        }
        Enc::Table(t) => {
            let table = &EIGHT_BIT[(t as usize) % EIGHT_BIT.len()];
            while i < n {
                let b = inp[i];
                let c = if b < 0x80 { b as u32 } else { table[(b - 0x80) as usize] as u32 };
                if c == 0 && b >= 0x80 {
                    res = Res::Input;
                    break;
                }
                if !put(out, c, &mut room) {
                    res = Res::Space;
                    break;
                }
                i += 1;
            }
        }
    }
    if flush && res == Res::Success && i != n {
        res = Res::Input;
    }
    (i, res)
}

/// `xmlCharEncInput`: converts what was read, up to `max_out` bytes of
/// output. Returns the bytes produced, or the error code.
pub fn char_enc_input(buf: &mut Vec<u8>, src: &mut Source, max_out: usize, flush: bool) -> Result<usize, i32> {
    let e = match src.enc {
        Some(e) => e,
        None => return Ok(0),
    };
    let start = if src.pos < src.delivered { src.pos } else { src.delivered };
    let avail = src.delivered - start;
    if avail == 0 && !flush {
        return Ok(0);
    }
    let before = buf.len();
    let end = if src.delivered <= src.raw.len() { src.delivered } else { src.raw.len() };
    let (used, res) = chunk(e, &src.raw[start..end], buf, max_out, flush);
    src.pos = start + used;
    if res == Res::Input {
        src.error = ERR_INVALID_ENCODING;
        return Err(ERR_INVALID_ENCODING);
    }
    Ok(buf.len() - before)
}

/// `xmlParserInputBufferGrow(buf, len)`.
pub fn buffer_grow(buf: &mut Vec<u8>, src: &mut Source, len: usize) -> i32 {
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
        src.delivered += n;
        res = n as i32;
        if src.enc.is_none() {
            let from = src.pos;
            let to = src.delivered;
            if from < to && to <= src.raw.len() {
                buf.extend_from_slice(&src.raw[from..to]);
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
    if let Some(src) = i.src.as_mut() {
        if src.mode == Mode::Memory && src.enc.is_none() {
            src.delivered = src.raw.len();
            i.buf = core::mem::take(&mut src.raw);
            src.pos = 0;
            src.delivered = 0;
        }
    }
}

impl<S: Sink> Parser<S> {
    /// `xmlInputSetEncodingHandler` on the current input; the error code.
    pub fn set_encoding_handler(&mut self, h: Option<Enc>) -> i32 {
        let input = self.inp_mut();
        input.flags |= INPUT_HAS_ENCODING;
        let src = match input.src.as_mut() {
            None => return ERR_ARGUMENT,
            Some(s) => s,
        };
        if src.enc == h {
            return ERR_OK;
        }
        if src.enc.is_some() {
            src.enc = h;
            return ERR_OK;
        }
        let h = match h {
            None => return ERR_OK,
            Some(h) => h,
        };
        // The buffer becomes the raw input, less what was read.
        let processed = input.cur;
        let mut raw: Vec<u8> = Vec::new();
        if processed < input.buf.len() {
            raw.extend_from_slice(&input.buf[processed..]);
        }
        let delivered_extra = raw.len();
        let rest_from = if src.pos < src.raw.len() { src.pos } else { src.raw.len() };
        let undelivered_from = if src.delivered > rest_from { src.delivered } else { rest_from };
        // Bytes read but not yet moved to the buffer, then the unread.
        if rest_from < undelivered_from && undelivered_from <= src.raw.len() {
            raw.extend_from_slice(&src.raw[rest_from..undelivered_from]);
        }
        let delivered = raw.len();
        let _ = delivered_extra;
        if undelivered_from < src.raw.len() {
            raw.extend_from_slice(&src.raw[undelivered_from..]);
        }
        src.raw = raw;
        src.pos = 0;
        src.delivered = if src.mode == Mode::Memory { src.raw.len() } else { delivered };
        src.enc = Some(h);
        input.consumed = input.consumed.saturating_add(processed as u64);
        input.buf = Vec::new();
        input.base = 0;
        input.cur = 0;
        let mut code = ERR_OK;
        let has = src.delivered > 0 || processed > 0 || true;
        if has {
            let r = char_enc_input(&mut input.buf, src, MINLEN, false);
            if let Err(c) = r {
                code = c;
            }
        }
        code
    }

    /// `xmlSwitchEncoding` with a detected encoding.
    pub fn switch_encoding(&mut self, id: i32) {
        match lookup_id(id) {
            Err(code) => self.fatal(code, None),
            Ok(h) => {
                let code = self.set_encoding_handler(h);
                if code != ERR_OK {
                    self.err_io(code);
                }
            }
        }
    }

    /// `xmlSwitchInputEncodingName`, for an encoding given before parsing
    /// (`xmlCtxtReadMemory`'s `encoding`).
    pub fn switch_encoding_name(&mut self, name: &[u8]) -> i32 {
        match lookup_encoding(name, false) {
            Err(code) => {
                if code == ERR_UNSUPPORTED_ENCODING {
                    let m = cat(&[b"Unsupported encoding: ", name, b"\n"]);
                    self.warning(ERR_UNSUPPORTED_ENCODING, &m, Some(name), None);
                } else {
                    self.fatal(code, Some(name));
                }
                -1
            }
            Ok(h) => {
                let code = self.set_encoding_handler(h);
                if code != ERR_OK {
                    self.err_io(code);
                    return -1;
                }
                0
            }
        }
    }

    /// `xmlDetectEncoding`.
    pub fn detect_encoding(&mut self) {
        if self.grow_now() < 0 {
            return;
        }
        if self.avail() < 4 {
            return;
        }
        let b = [self.nxt(0), self.nxt(1), self.nxt(2), self.nxt(3)];
        if self.inp().flags & INPUT_HAS_ENCODING != 0 {
            if b[0] == 0xEF && b[1] == 0xBB && b[2] == 0xBF {
                self.inp_mut().cur += 3;
            }
            return;
        }
        let html = self.html;
        let (enc, auto, bom): (i32, u32, usize) = match b[0] {
            0x00 if !html && b[1] == 0 && b[2] == 0 && b[3] == 0x3C => (5, INPUT_AUTO_OTHER, 0),
            0x00 if b[1] == 0x3C && b[2] == 0 && b[3] == 0x3F => (3, INPUT_AUTO_UTF16BE, 0),
            0x3C if b[1] == 0 && !html && b[2] == 0 && b[3] == 0 => (4, INPUT_AUTO_OTHER, 0),
            0x3C if b[1] == 0 && b[2] == 0x3F && b[3] == 0 => (2, INPUT_AUTO_UTF16LE, 0),
            0x4C if !html && b[1] == 0x6F && b[2] == 0xA7 && b[3] == 0x94 => (6, INPUT_AUTO_OTHER, 0),
            0xEF if b[1] == 0xBB && b[2] == 0xBF => (1, INPUT_AUTO_UTF8, 3),
            0xFE if b[1] == 0xFF => (3, INPUT_AUTO_UTF16BE, 2),
            0xFF if b[1] == 0xFE => (2, INPUT_AUTO_UTF16LE, 2),
            _ => (0, 0, 0),
        };
        if bom > 0 {
            self.inp_mut().cur += bom;
        }
        if enc != 0 {
            self.inp_mut().flags |= auto;
            if enc == 6 {
                // xmlDetectEBCDIC: no EBCDIC decoder without iconv.
                self.fatal(ERR_UNSUPPORTED_ENCODING, Some(b"detecting EBCDIC\n"));
            } else {
                self.switch_encoding(enc);
            }
        }
    }

    /// `xmlSetDeclaredEncoding`.
    pub fn set_declared_encoding(&mut self, encoding: Vec<u8>) {
        let mut encoding = Some(encoding);
        let flags = self.inp().flags;
        if flags & INPUT_HAS_ENCODING == 0 && self.options & PARSE_IGNORE_ENC == 0 {
            let name = encoding.clone().unwrap_or_default();
            match lookup_encoding(&name, self.html) {
                Err(code) => {
                    self.fatal(code, Some(&name));
                    return;
                }
                Ok(h) => {
                    let code = self.set_encoding_handler(h);
                    if code != ERR_OK {
                        self.err_io(code);
                        return;
                    }
                    self.inp_mut().flags |= INPUT_USES_ENC_DECL;
                }
            }
        } else if flags & INPUT_AUTO_ENCODING != 0 {
            let (allowed, auto): (&[&[u8]], &[u8]) = match flags & INPUT_AUTO_ENCODING {
                INPUT_AUTO_UTF8 => (&[b"UTF-8", b"UTF8"], b"UTF-8"),
                INPUT_AUTO_UTF16LE => (&[b"UTF-16", b"UTF-16LE", b"UTF16"], b"UTF-16LE"),
                INPUT_AUTO_UTF16BE => (&[b"UTF-16", b"UTF-16BE", b"UTF16"], b"UTF-16BE"),
                _ => (&[], b""),
            };
            if !allowed.is_empty() {
                let name = encoding.clone().unwrap_or_default();
                let mut matched = false;
                for a in allowed {
                    if eq_ci(&name, a) {
                        matched = true;
                    }
                }
                if !matched {
                    let m = cat(&[b"Encoding '", &name, b"' doesn't match auto-detected '", auto, b"'\n"]);
                    self.warning(WAR_ENCODING_MISMATCH, &m, Some(&name), Some(auto));
                    encoding = Some(auto.to_vec());
                }
            }
        }
        self.encoding = encoding.clone();
        self.sink.set_encoding(encoding.as_deref());
    }

    /// `xmlParserCheckEOF`.
    pub fn check_eof(&mut self, code: i32) {
        if self.sink.err_no() != ERR_OK {
            return;
        }
        if !self.at_end() {
            self.fatal(code, None);
            return;
        }
        let r = {
            let n = self.inputs.len();
            let input = &mut self.inputs[n - 1];
            match input.src.as_mut() {
                Some(src) if src.enc.is_some() => Some(char_enc_input(&mut input.buf, src, 64, true)),
                _ => None,
            }
        };
        match r {
            Some(Err(c)) => self.err_io(c),
            Some(Ok(_)) => {
                if !self.at_end() {
                    self.fatal(ERR_INTERNAL_ERROR, Some(b"expected EOF"));
                }
            }
            None => {}
        }
    }
}
