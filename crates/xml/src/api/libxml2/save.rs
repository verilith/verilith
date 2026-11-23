//! Writing trees out (`xmlsave.h`), and the `xmlBuffer` the old API writes
//! into: a port of libxml2's serializer, without the HTML and XHTML
//! modes, writing UTF-8, ISO-8859-1 or US-ASCII.

use super::tree::xmlStringTextNoenc;
use super::*;

// --- xmlBuffer ---------------------------------------------------------------------------

const BUFFER_ALLOC_IO: c_int = 4;

unsafe fn buf_bytes<'a>(b: *const Buffer) -> &'a [u8] {
    unsafe {
        if b.is_null() || (*b).content.is_null() {
            &[]
        } else {
            std::slice::from_raw_parts((*b).content, (*b).use_ as usize)
        }
    }
}

/// Room for `extra` more bytes and a NUL.
unsafe fn buf_grow(b: *mut Buffer, extra: usize) -> bool {
    unsafe {
        let need = (*b).use_ as usize + extra + 1;
        if need <= (*b).size as usize && !(*b).content.is_null() {
            return true;
        }
        if need > c_int::MAX as usize {
            return false;
        }
        let size = need.max((*b).size as usize * 2).max(64).min(c_int::MAX as usize);
        let p = xrealloc((*b).content as *mut c_void, size) as *mut XChar;
        if p.is_null() {
            return false;
        }
        (*b).content = p;
        (*b).size = size as c_uint;
        true
    }
}

unsafe fn buf_add(b: *mut Buffer, s: &[u8]) -> c_int {
    unsafe {
        if b.is_null() {
            return -1;
        }
        if s.is_empty() {
            return 0;
        }
        if !buf_grow(b, s.len()) {
            return ERR_NO_MEMORY;
        }
        std::ptr::copy_nonoverlapping(s.as_ptr(), (*b).content.add((*b).use_ as usize), s.len());
        (*b).use_ += s.len() as c_uint;
        *(*b).content.add((*b).use_ as usize) = 0;
        0
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlBufferCreateSize(size: usize) -> *mut Buffer {
    let b: *mut Buffer = xnew();
    if b.is_null() {
        return b;
    }
    unsafe {
        let size = size.clamp(1, c_int::MAX as usize - 1);
        (*b).content = xmalloc(size + 1) as *mut XChar;
        if (*b).content.is_null() {
            xfree(b as *mut c_void);
            return null_mut();
        }
        *(*b).content = 0;
        (*b).size = (size + 1) as c_uint;
        (*b).alloc = BUFFER_ALLOC_IO;
        (*b).contentIO = (*b).content;
    }
    b
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlBufferCreate() -> *mut Buffer {
    xmlBufferCreateSize(4096)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlBufferCreateStatic(mem: *mut c_void, size: usize) -> *mut Buffer {
    unsafe {
        if mem.is_null() {
            return null_mut();
        }
        let b = xmlBufferCreateSize(size);
        buf_add(b, std::slice::from_raw_parts(mem as *const u8, size));
        b
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlBufferFree(b: *mut Buffer) {
    unsafe {
        if b.is_null() {
            return;
        }
        xfree((*b).content as *mut c_void);
        xfree(b as *mut c_void);
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlBufferEmpty(b: *mut Buffer) {
    unsafe {
        if b.is_null() {
            return;
        }
        (*b).use_ = 0;
        if !(*b).content.is_null() {
            *(*b).content = 0;
        }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlBufferContent(b: *const Buffer) -> *const XChar {
    unsafe { if b.is_null() { null() } else { (*b).content } }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlBufferLength(b: *const Buffer) -> c_int {
    unsafe { if b.is_null() { 0 } else { (*b).use_ as c_int } }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlBufferUse(b: *const Buffer) -> c_int {
    unsafe { xmlBufferLength(b) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlBufferDetach(b: *mut Buffer) -> *mut XChar {
    unsafe {
        if b.is_null() {
            return null_mut();
        }
        let p = (*b).content;
        (*b).content = null_mut();
        (*b).contentIO = null_mut();
        (*b).size = 0;
        (*b).use_ = 0;
        p
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlBufferAdd(b: *mut Buffer, s: *const XChar, len: c_int) -> c_int {
    unsafe {
        if b.is_null() || s.is_null() || len < -1 {
            return -1;
        }
        let v = if len < 0 { cbytes(s) } else { std::slice::from_raw_parts(s, len as usize) };
        buf_add(b, v)
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlBufferAddHead(b: *mut Buffer, s: *const XChar, len: c_int) -> c_int {
    unsafe {
        if b.is_null() || s.is_null() || len < -1 {
            return -1;
        }
        let v = if len < 0 { cbytes(s).to_vec() } else { std::slice::from_raw_parts(s, len as usize).to_vec() };
        let mut all = v;
        all.extend_from_slice(buf_bytes(b));
        xmlBufferEmpty(b);
        buf_add(b, &all)
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlBufferCat(b: *mut Buffer, s: *const XChar) -> c_int {
    unsafe { xmlBufferAdd(b, s, -1) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlBufferCCat(b: *mut Buffer, s: *const c_char) -> c_int {
    unsafe { xmlBufferAdd(b, s as *const XChar, -1) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlBufferWriteCHAR(b: *mut Buffer, s: *const XChar) {
    unsafe {
        xmlBufferAdd(b, s, -1);
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlBufferWriteChar(b: *mut Buffer, s: *const c_char) {
    unsafe {
        xmlBufferAdd(b, s as *const XChar, -1);
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlBufferWriteQuotedString(b: *mut Buffer, s: *const XChar) {
    unsafe {
        if b.is_null() || s.is_null() {
            return;
        }
        let mut o = Out::new(Sink::Mem, Enc::Utf8);
        o.quoted(cbytes(s));
        buf_add(b, &o.out);
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlBufferGrow(b: *mut Buffer, len: c_uint) -> c_int {
    unsafe {
        if b.is_null() {
            return -1;
        }
        if !buf_grow(b, len as usize) {
            return -1;
        }
        ((*b).size - (*b).use_ - 1) as c_int
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlBufferShrink(b: *mut Buffer, len: c_uint) -> c_int {
    unsafe {
        if b.is_null() || len > (*b).use_ {
            return -1;
        }
        let n = (*b).use_ - len;
        std::ptr::copy((*b).content.add(len as usize), (*b).content, n as usize);
        (*b).use_ = n;
        *(*b).content.add(n as usize) = 0;
        len as c_int
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlBufferResize(b: *mut Buffer, size: c_uint) -> c_int {
    unsafe {
        if b.is_null() {
            return 0;
        }
        if size as usize + 1 <= (*b).size as usize {
            return 1;
        }
        if buf_grow(b, (size as usize).saturating_sub((*b).use_ as usize)) { 1 } else { 0 }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlBufferSetAllocationScheme(_b: *mut Buffer, _scheme: c_int) {}

// --- encodings out -------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq)]
pub enum Enc {
    Utf8,
    Latin1,
    Ascii,
    Utf16Le,
    Utf16Be,
}

/// The output encodings this serializer has, by name.
pub fn enc_by_name(name: &[u8]) -> Option<Enc> {
    let n = name.to_ascii_uppercase();
    match &n[..] {
        b"UTF-8" | b"UTF8" => Some(Enc::Utf8),
        b"ISO-8859-1" | b"ISO_8859-1" | b"ISO-LATIN-1" | b"ISO LATIN 1" | b"LATIN1" | b"LATIN-1" | b"L1" | b"ISO8859-1" => Some(Enc::Latin1),
        b"US-ASCII" | b"ASCII" | b"US_ASCII" | b"ANSI_X3.4-1968" => Some(Enc::Ascii),
        b"UTF-16" | b"UTF16" | b"UTF-16LE" | b"UTF16LE" => Some(Enc::Utf16Le),
        b"UTF-16BE" | b"UTF16BE" => Some(Enc::Utf16Be),
        _ => None,
    }
}

fn dec_ref(out: &mut Vec<u8>, cp: u32) {
    out.extend_from_slice(format!("&#{cp};").as_bytes());
}

/// The byte order mark an encoding's output starts with: UTF-16 (with no
/// byte order named) is written little-endian after one.
pub fn bom(name: &[u8]) -> &'static [u8] {
    match &name.to_ascii_uppercase()[..] {
        b"UTF-16" | b"UTF16" => &[0xFF, 0xFE],
        _ => &[],
    }
}

fn encode(out: &mut Vec<u8>, enc: Enc, s: &[u8]) {
    if enc == Enc::Utf16Le || enc == Enc::Utf16Be {
        let t = String::from_utf8_lossy(s);
        for u in t.encode_utf16() {
            let b = if enc == Enc::Utf16Le { u.to_le_bytes() } else { u.to_be_bytes() };
            out.extend_from_slice(&b);
        }
        return;
    }
    if enc == Enc::Utf8 || s.is_ascii() {
        out.extend_from_slice(s);
        return;
    }
    let limit = if enc == Enc::Latin1 { 0xFF } else { 0x7F };
    let mut i = 0;
    while i < s.len() {
        let b = s[i];
        if b < 0x80 {
            out.push(b);
            i += 1;
            continue;
        }
        let (cp, n) = utf8_at(&s[i..]);
        if cp <= limit {
            out.push(cp as u8);
        } else {
            dec_ref(out, cp);
        }
        i += n;
    }
}

/// The code point at the start of `s` and its length; U+FFFD for a bad
/// sequence, one byte long.
fn utf8_at(s: &[u8]) -> (u32, usize) {
    let b = s[0];
    let n = if b >= 0xF0 { 4 } else if b >= 0xE0 { 3 } else if b >= 0xC0 { 2 } else { 1 };
    if n == 1 || s.len() < n {
        return (0xFFFD, 1);
    }
    match std::str::from_utf8(&s[..n]) {
        Ok(t) => (t.chars().next().map_or(0xFFFD, |c| c as u32), n),
        Err(_) => (0xFFFD, 1),
    }
}

// --- the output ------------------------------------------------------------------------------

pub type WriteCb = Option<unsafe extern "C" fn(*mut c_void, *const c_char, c_int) -> c_int>;
pub type CloseCb = Option<unsafe extern "C" fn(*mut c_void) -> c_int>;

pub enum Sink {
    Mem,
    Buffer(*mut Buffer),
    Io(WriteCb, CloseCb, *mut c_void),
    File(std::fs::File),
    Stdout,
}

/// An output: bytes in the current encoding, kept until flushed.
pub struct Out {
    pub out: Vec<u8>,
    pub enc: Enc,
    pub sink: Sink,
    pub error: bool,
    pub written: usize,
}

const ESC_ATTR: u32 = 1;
const ESC_NON_ASCII: u32 = 2;

impl Out {
    pub fn new(sink: Sink, enc: Enc) -> Out {
        Out { out: Vec::new(), enc, sink, error: false, written: 0 }
    }

    pub fn w(&mut self, s: &[u8]) {
        encode(&mut self.out, self.enc, s);
    }

    /// `xmlOutputBufferWriteQuotedString`.
    pub fn quoted(&mut self, s: &[u8]) {
        if s.contains(&b'"') {
            if s.contains(&b'\'') {
                self.w(b"\"");
                let mut base = 0;
                for (i, &c) in s.iter().enumerate() {
                    if c == b'"' {
                        self.w(&s[base..i]);
                        self.w(b"&quot;");
                        base = i + 1;
                    }
                }
                self.w(&s[base..]);
                self.w(b"\"");
            } else {
                self.w(b"'");
                self.w(s);
                self.w(b"'");
            }
        } else {
            self.w(b"\"");
            self.w(s);
            self.w(b"\"");
        }
    }

    /// `xmlSerializeText`.
    pub fn text(&mut self, s: &[u8], flags: u32) {
        let mut base = 0;
        let mut i = 0;
        while i < s.len() {
            let c = s[i];
            let rep: Option<&[u8]> = if c < 0x80 {
                match c {
                    b'&' => Some(b"&amp;"),
                    b'<' => Some(b"&lt;"),
                    b'>' => Some(b"&gt;"),
                    b'\r' => Some(b"&#13;"),
                    b'"' if flags & ESC_ATTR != 0 => Some(b"&quot;"),
                    b'\t' if flags & ESC_ATTR != 0 => Some(b"&#9;"),
                    b'\n' if flags & ESC_ATTR != 0 => Some(b"&#10;"),
                    b'\t' | b'\n' => None,
                    0..0x20 => Some(b"&#xFFFD;"),
                    _ => None,
                }
            } else if flags & ESC_NON_ASCII != 0 {
                self.w(&s[base..i]);
                let (mut cp, n) = utf8_at(&s[i..]);
                if cp == 0xFFFE || cp == 0xFFFF {
                    cp = 0xFFFD;
                }
                self.w(format!("&#x{cp:X};").as_bytes());
                i += n;
                base = i;
                continue;
            } else {
                None
            };
            if let Some(r) = rep {
                self.w(&s[base..i]);
                self.w(r);
                base = i + 1;
            }
            i += 1;
        }
        self.w(&s[base..]);
    }

    /// Sends what is kept to the sink.
    pub fn flush(&mut self) -> c_int {
        if self.error {
            return -1;
        }
        let data = std::mem::take(&mut self.out);
        let n = data.len();
        let ok = unsafe {
            match &mut self.sink {
                Sink::Mem => {
                    self.out = data;
                    return 0;
                }
                Sink::Buffer(b) => buf_add(*b, &data) == 0,
                Sink::Io(Some(f), _, ctx) => {
                    let mut off = 0;
                    let mut ok = true;
                    while off < n {
                        let chunk = (n - off).min(c_int::MAX as usize);
                        let r = f(*ctx, data[off..].as_ptr() as *const c_char, chunk as c_int);
                        if r < 0 {
                            ok = false;
                            break;
                        }
                        off += chunk;
                    }
                    ok
                }
                Sink::Io(None, _, _) => true,
                Sink::File(file) => std::io::Write::write_all(file, &data).is_ok(),
                Sink::Stdout => std::io::Write::write_all(&mut std::io::stdout(), &data).is_ok(),
            }
        };
        if !ok {
            self.error = true;
            return -1;
        }
        self.written += n;
        n as c_int
    }

    /// Flushes and closes; the bytes written, or -1.
    pub fn close(&mut self) -> c_int {
        let r = self.flush();
        let mut ret = if self.error || r < 0 { -1 } else { self.written as c_int };
        if let Sink::Io(_, Some(c), ctx) = self.sink {
            if unsafe { c(ctx) } < 0 {
                ret = -1;
            }
        }
        self.sink = Sink::Mem;
        ret
    }
}

// --- the serializer ----------------------------------------------------------------------------

pub const SAVE_FORMAT: c_int = 1 << 0;
pub const SAVE_NO_DECL: c_int = 1 << 1;
pub const SAVE_NO_EMPTY: c_int = 1 << 2;
pub const SAVE_NO_XHTML: c_int = 1 << 3;
pub const SAVE_XHTML: c_int = 1 << 4;
pub const SAVE_AS_XML: c_int = 1 << 5;
pub const SAVE_AS_HTML: c_int = 1 << 6;
pub const SAVE_WSNONSIG: c_int = 1 << 7;
pub const SAVE_EMPTY: c_int = 1 << 8;
pub const SAVE_NO_INDENT: c_int = 1 << 9;
pub const SAVE_INDENT: c_int = 1 << 10;

/// `xmlSaveCtxt`.
pub struct SaveCtxt {
    pub o: Out,
    /// The encoding asked for, or switched to for a document.
    pub encoding: Option<Vec<u8>>,
    pub options: c_int,
    pub format: c_int,
    pub level: c_int,
    pub indent: Vec<u8>,
    pub indent_nr: c_int,
    pub indent_size: c_int,
}

impl SaveCtxt {
    pub fn new(sink: Sink, encoding: Option<Vec<u8>>, options: c_int) -> SaveCtxt {
        let enc = encoding.as_deref().and_then(enc_by_name).unwrap_or(Enc::Utf8);
        let mut c = SaveCtxt { o: Out::new(sink, enc), encoding, options: 0, format: 0, level: 0, indent: Vec::new(), indent_nr: 0, indent_size: 0 };
        c.init(options);
        c
    }

    fn init(&mut self, mut options: c_int) {
        let g = globals();
        let s = unsafe { (*g).tree_indent_string };
        let ind = if s.is_null() { b"  ".to_vec() } else { unsafe { cbytes(s as *const XChar).to_vec() } };
        self.indent_size = ind.len() as c_int;
        if self.indent_size > 0 {
            self.indent_nr = 60 / self.indent_size;
            let mut v = Vec::new();
            for _ in 0..self.indent_nr {
                v.extend_from_slice(&ind);
            }
            self.indent = v;
        }
        if options & SAVE_FORMAT != 0 {
            self.format = 1;
        } else if options & SAVE_WSNONSIG != 0 {
            self.format = 2;
        }
        if options & SAVE_EMPTY == 0 && unsafe { (*g).save_no_empty_tags } != 0 {
            options |= SAVE_NO_EMPTY;
        }
        self.options = options;
    }

    fn text_flags(&self, flags: u32) -> u32 {
        if self.encoding.is_none() { flags | ESC_NON_ASCII } else { flags }
    }

    fn write_text(&mut self, s: &[u8], flags: u32) {
        let f = self.text_flags(flags);
        self.o.text(s, f);
    }

    fn write_indent(&mut self, extra: c_int) {
        let g = globals();
        if self.options & SAVE_NO_INDENT != 0 || (self.options & SAVE_INDENT == 0 && unsafe { (*g).indent_tree_output } == 0) {
            return;
        }
        let level = (self.level + extra).min(self.indent_nr).max(0);
        let n = (self.indent_size * level) as usize;
        let ind = self.indent[..n.min(self.indent.len())].to_vec();
        self.o.w(&ind);
    }

    fn ws_nonsig(&mut self, extra: c_int) {
        self.o.w(b"\n");
        let mut i = 0;
        let total = self.level + extra;
        while i < total {
            let k = (total - i).min(self.indent_nr);
            let n = (self.indent_size * k) as usize;
            let ind = self.indent[..n.min(self.indent.len())].to_vec();
            self.o.w(&ind);
            if self.indent_nr <= 0 {
                break;
            }
            i += self.indent_nr;
        }
    }

    unsafe fn ns(&mut self, ns: *mut Ns) {
        unsafe {
            if ns.is_null() {
                return;
            }
            if (*ns).type_ == NAMESPACE_DECL && !(*ns).href.is_null() {
                if copt((*ns).prefix) == Some(b"xml") {
                    return;
                }
                if self.format == 2 {
                    self.ws_nonsig(2);
                } else {
                    self.o.w(b" ");
                }
                match copt((*ns).prefix) {
                    Some(p) => {
                        self.o.w(b"xmlns:");
                        self.o.w(p);
                    }
                    None => self.o.w(b"xmlns"),
                }
                self.o.w(b"=\"");
                self.write_text(cbytes((*ns).href), ESC_ATTR);
                self.o.w(b"\"");
            }
        }
    }

    unsafe fn attr(&mut self, a: *mut Attr) {
        unsafe {
            if a.is_null() {
                return;
            }
            if self.format == 2 {
                self.ws_nonsig(2);
            } else {
                self.o.w(b" ");
            }
            if !(*a).ns.is_null() {
                if let Some(p) = copt((*(*a).ns).prefix) {
                    self.o.w(p);
                    self.o.w(b":");
                }
            }
            self.o.w(cbytes((*a).name));
            self.o.w(b"=\"");
            let mut c = (*a).children;
            while !c.is_null() {
                match (*c).type_ {
                    TEXT_NODE => self.write_text(cbytes((*c).content), ESC_ATTR),
                    ENTITY_REF_NODE => {
                        self.o.w(b"&");
                        self.o.w(cbytes((*c).name));
                        self.o.w(b";");
                    }
                    _ => {}
                }
                c = (*c).next;
            }
            self.o.w(b"\"");
        }
    }

    fn occur(&mut self, c: *mut ElementContent) {
        match unsafe { (*c).ocur } {
            CONTENT_OPT => self.o.w(b"?"),
            CONTENT_MULT => self.o.w(b"*"),
            CONTENT_PLUS => self.o.w(b"+"),
            _ => {}
        }
    }

    unsafe fn element_content(&mut self, content: *mut ElementContent) {
        unsafe {
            if content.is_null() {
                return;
            }
            self.o.w(b"(");
            let mut cur = content;
            loop {
                if cur.is_null() {
                    return;
                }
                match (*cur).type_ {
                    CONTENT_PCDATA => self.o.w(b"#PCDATA"),
                    CONTENT_ELEMENT => {
                        if let Some(p) = copt((*cur).prefix) {
                            self.o.w(p);
                            self.o.w(b":");
                        }
                        self.o.w(cbytes((*cur).name));
                    }
                    CONTENT_SEQ | CONTENT_OR => {
                        if cur != content && !(*cur).parent.is_null() && ((*cur).type_ != (*(*cur).parent).type_ || (*cur).ocur != CONTENT_ONCE) {
                            self.o.w(b"(");
                        }
                        cur = (*cur).c1;
                        continue;
                    }
                    _ => {}
                }
                while cur != content {
                    let parent = (*cur).parent;
                    if parent.is_null() {
                        return;
                    }
                    if ((*cur).type_ == CONTENT_OR || (*cur).type_ == CONTENT_SEQ) && ((*cur).type_ != (*parent).type_ || (*cur).ocur != CONTENT_ONCE) {
                        self.o.w(b")");
                    }
                    self.occur(cur);
                    if cur == (*parent).c1 {
                        if (*parent).type_ == CONTENT_SEQ {
                            self.o.w(b" , ");
                        } else if (*parent).type_ == CONTENT_OR {
                            self.o.w(b" | ");
                        }
                        cur = (*parent).c2;
                        break;
                    }
                    cur = parent;
                }
                if cur == content {
                    break;
                }
            }
            self.o.w(b")");
            self.occur(content);
        }
    }

    unsafe fn element_decl(&mut self, e: *mut ElementDecl) {
        unsafe {
            self.o.w(b"<!ELEMENT ");
            if let Some(p) = copt((*e).prefix) {
                self.o.w(p);
                self.o.w(b":");
            }
            self.o.w(cbytes((*e).name));
            self.o.w(b" ");
            match (*e).etype {
                ELEMENT_TYPE_EMPTY => self.o.w(b"EMPTY"),
                ELEMENT_TYPE_ANY => self.o.w(b"ANY"),
                ELEMENT_TYPE_MIXED | ELEMENT_TYPE_ELEMENT => self.element_content((*e).content),
                _ => {}
            }
            self.o.w(b">\n");
        }
    }

    unsafe fn enumeration(&mut self, mut e: *mut Enumeration) {
        unsafe {
            while !e.is_null() {
                self.o.w(cbytes((*e).name));
                if !(*e).next.is_null() {
                    self.o.w(b" | ");
                }
                e = (*e).next;
            }
            self.o.w(b")");
        }
    }

    unsafe fn attribute_decl(&mut self, a: *mut AttributeDecl) {
        unsafe {
            self.o.w(b"<!ATTLIST ");
            self.o.w(cbytes((*a).elem));
            self.o.w(b" ");
            if let Some(p) = copt((*a).prefix) {
                self.o.w(p);
                self.o.w(b":");
            }
            self.o.w(cbytes((*a).name));
            let t: &[u8] = match (*a).atype {
                1 => b" CDATA",
                2 => b" ID",
                3 => b" IDREF",
                4 => b" IDREFS",
                5 => b" ENTITY",
                6 => b" ENTITIES",
                7 => b" NMTOKEN",
                8 => b" NMTOKENS",
                ATTRIBUTE_ENUMERATION => b" (",
                ATTRIBUTE_NOTATION => b" NOTATION (",
                _ => b"",
            };
            self.o.w(t);
            if (*a).atype == ATTRIBUTE_ENUMERATION || (*a).atype == ATTRIBUTE_NOTATION {
                self.enumeration((*a).tree);
            }
            match (*a).def {
                ATTRIBUTE_REQUIRED => self.o.w(b" #REQUIRED"),
                ATTRIBUTE_IMPLIED => self.o.w(b" #IMPLIED"),
                ATTRIBUTE_FIXED => self.o.w(b" #FIXED"),
                _ => {}
            }
            if let Some(v) = copt((*a).defaultValue) {
                self.o.w(b" \"");
                self.write_text(v, ESC_ATTR);
                self.o.w(b"\"");
            }
            self.o.w(b">\n");
        }
    }

    fn entity_content(&mut self, s: &[u8]) {
        self.o.w(b"\"");
        let mut base = 0;
        for (i, &c) in s.iter().enumerate() {
            let r: &[u8] = match c {
                b'"' => b"&quot;",
                b'%' => b"&#x25;",
                _ => continue,
            };
            self.o.w(&s[base..i]);
            self.o.w(r);
            base = i + 1;
        }
        self.o.w(&s[base..]);
        self.o.w(b"\"");
    }

    unsafe fn entity_decl(&mut self, e: *mut Entity) {
        unsafe {
            let t = (*e).etype;
            if t == INTERNAL_PARAMETER_ENTITY || t == EXTERNAL_PARAMETER_ENTITY {
                self.o.w(b"<!ENTITY % ");
            } else {
                self.o.w(b"<!ENTITY ");
            }
            self.o.w(cbytes((*e).name));
            self.o.w(b" ");
            if t == EXTERNAL_GENERAL_PARSED_ENTITY || t == EXTERNAL_GENERAL_UNPARSED_ENTITY || t == EXTERNAL_PARAMETER_ENTITY {
                match copt((*e).ExternalID) {
                    Some(p) => {
                        self.o.w(b"PUBLIC ");
                        self.o.quoted(p);
                        self.o.w(b" ");
                    }
                    None => self.o.w(b"SYSTEM "),
                }
                self.o.quoted(cbytes((*e).SystemID));
            }
            if t == EXTERNAL_GENERAL_UNPARSED_ENTITY && !(*e).content.is_null() {
                self.o.w(b" NDATA ");
                match copt((*e).orig) {
                    Some(o) => self.o.w(o),
                    None => self.o.w(cbytes((*e).content)),
                }
            }
            if t == INTERNAL_GENERAL_ENTITY || t == INTERNAL_PARAMETER_ENTITY {
                match copt((*e).orig) {
                    Some(o) => self.o.quoted(o),
                    None => {
                        if let Some(c) = copt((*e).content) {
                            self.entity_content(c);
                        }
                    }
                }
            }
            self.o.w(b">\n");
        }
    }

    unsafe fn notation(&mut self, n: *mut Notation) {
        unsafe {
            self.o.w(b"<!NOTATION ");
            self.o.w(cbytes((*n).name));
            match copt((*n).PublicID) {
                Some(p) => {
                    self.o.w(b" PUBLIC ");
                    self.o.quoted(p);
                    if let Some(s) = copt((*n).SystemID) {
                        self.o.w(b" ");
                        self.o.quoted(s);
                    }
                }
                None => {
                    self.o.w(b" SYSTEM ");
                    self.o.quoted(cbytes((*n).SystemID));
                }
            }
            self.o.w(b" >\n");
        }
    }

    unsafe fn dtd(&mut self, d: *mut Dtd) {
        unsafe {
            if d.is_null() {
                return;
            }
            self.o.w(b"<!DOCTYPE ");
            self.o.w(cbytes((*d).name));
            if let Some(p) = copt((*d).ExternalID) {
                self.o.w(b" PUBLIC ");
                self.o.quoted(p);
                self.o.w(b" ");
                self.o.quoted(cbytes((*d).SystemID));
            } else if let Some(s) = copt((*d).SystemID) {
                self.o.w(b" SYSTEM ");
                self.o.quoted(s);
            }
            if (*d).entities.is_null() && (*d).elements.is_null() && (*d).attributes.is_null() && (*d).notations.is_null() && (*d).pentities.is_null() {
                self.o.w(b">");
                return;
            }
            self.o.w(b" [\n");
            if !(*d).notations.is_null() && ((*d).doc.is_null() || (*(*d).doc).intSubset == d) {
                for n in (*((*d).notations as *mut Hash)).values() {
                    self.notation(n as *mut Notation);
                }
            }
            let (format, level) = (self.format, self.level);
            self.format = 0;
            self.level = -1;
            let mut c = (*d).children;
            while !c.is_null() {
                self.node(c);
                c = (*c).next;
            }
            self.format = format;
            self.level = level;
            self.o.w(b"]>");
        }
    }

    unsafe fn qname(&mut self, n: *mut Node) {
        unsafe {
            if !(*n).ns.is_null() {
                if let Some(p) = copt((*(*n).ns).prefix) {
                    self.o.w(p);
                    self.o.w(b":");
                }
            }
            self.o.w(cbytes((*n).name));
        }
    }

    /// `xmlNodeDumpOutputInternal`.
    pub unsafe fn node(&mut self, root: *mut Node) {
        unsafe {
            if root.is_null() {
                return;
            }
            let format = self.format;
            let mut unformatted: *mut Node = null_mut();
            let mut cur = root;
            let mut parent = (*cur).parent;
            loop {
                let mut descend = false;
                match (*cur).type_ {
                    DOCUMENT_NODE | HTML_DOCUMENT_NODE => {
                        let enc = self.encoding.clone();
                        self.doc(cur as *mut Doc, enc);
                    }
                    DTD_NODE => self.dtd(cur as *mut Dtd),
                    DOCUMENT_FRAG_NODE => {
                        if (*cur).parent == parent && !(*cur).children.is_null() {
                            parent = cur;
                            cur = (*cur).children;
                            continue;
                        }
                    }
                    ELEMENT_DECL => self.element_decl(cur as *mut ElementDecl),
                    ATTRIBUTE_DECL => self.attribute_decl(cur as *mut AttributeDecl),
                    ENTITY_DECL => self.entity_decl(cur as *mut Entity),
                    ELEMENT_NODE => {
                        if cur != root && self.format == 1 {
                            self.write_indent(0);
                        }
                        if (*cur).parent != parent && !(*cur).children.is_null() {
                            self.node(cur);
                        } else {
                            self.o.w(b"<");
                            self.qname(cur);
                            let mut ns = (*cur).nsDef;
                            while !ns.is_null() {
                                self.ns(ns);
                                ns = (*ns).next;
                            }
                            let mut a = (*cur).properties;
                            while !a.is_null() {
                                self.attr(a);
                                a = (*a).next;
                            }
                            if (*cur).children.is_null() {
                                if self.options & SAVE_NO_EMPTY == 0 {
                                    if self.format == 2 {
                                        self.ws_nonsig(0);
                                    }
                                    self.o.w(b"/>");
                                } else {
                                    if self.format == 2 {
                                        self.ws_nonsig(1);
                                    }
                                    self.o.w(b"></");
                                    self.qname(cur);
                                    if self.format == 2 {
                                        self.ws_nonsig(0);
                                    }
                                    self.o.w(b">");
                                }
                            } else {
                                if self.format == 1 {
                                    let mut t = (*cur).children;
                                    while !t.is_null() {
                                        if matches!((*t).type_, TEXT_NODE | CDATA_SECTION_NODE | ENTITY_REF_NODE) {
                                            self.format = 0;
                                            unformatted = cur;
                                            break;
                                        }
                                        t = (*t).next;
                                    }
                                }
                                if self.format == 2 {
                                    self.ws_nonsig(1);
                                }
                                self.o.w(b">");
                                if self.format == 1 {
                                    self.o.w(b"\n");
                                }
                                if self.level >= 0 {
                                    self.level += 1;
                                }
                                descend = true;
                            }
                        }
                    }
                    TEXT_NODE => {
                        if let Some(c) = copt((*cur).content) {
                            if (*cur).name != xmlStringTextNoenc.as_ptr() {
                                self.write_text(c, 0);
                            } else {
                                self.o.w(c);
                            }
                        }
                    }
                    PI_NODE => {
                        if cur != root && self.format == 1 {
                            self.write_indent(0);
                        }
                        self.o.w(b"<?");
                        self.o.w(cbytes((*cur).name));
                        if let Some(c) = copt((*cur).content) {
                            if self.format == 2 {
                                self.ws_nonsig(0);
                            } else {
                                self.o.w(b" ");
                            }
                            self.o.w(c);
                        } else if self.format == 2 {
                            self.ws_nonsig(0);
                        }
                        self.o.w(b"?>");
                    }
                    COMMENT_NODE => {
                        if cur != root && self.format == 1 {
                            self.write_indent(0);
                        }
                        if let Some(c) = copt((*cur).content) {
                            self.o.w(b"<!--");
                            self.o.w(c);
                            self.o.w(b"-->");
                        }
                    }
                    ENTITY_REF_NODE => {
                        self.o.w(b"&");
                        self.o.w(cbytes((*cur).name));
                        self.o.w(b";");
                    }
                    CDATA_SECTION_NODE => {
                        let c = copt((*cur).content).unwrap_or(b"");
                        if c.is_empty() {
                            self.o.w(b"<![CDATA[]]>");
                        } else {
                            let mut start = 0;
                            let mut end = 0;
                            while end < c.len() {
                                if c[end..].starts_with(b"]]>") {
                                    end += 2;
                                    self.o.w(b"<![CDATA[");
                                    self.o.w(&c[start..end]);
                                    self.o.w(b"]]>");
                                    start = end;
                                }
                                end += 1;
                            }
                            if start != end {
                                self.o.w(b"<![CDATA[");
                                self.o.w(&c[start.min(c.len())..]);
                                self.o.w(b"]]>");
                            }
                        }
                    }
                    ATTRIBUTE_NODE => self.attr(cur as *mut Attr),
                    NAMESPACE_DECL => self.ns(cur as *mut Ns),
                    _ => {}
                }
                if descend {
                    parent = cur;
                    cur = (*cur).children;
                    continue;
                }
                loop {
                    if cur == root {
                        return;
                    }
                    if self.format == 1 && (*cur).type_ != XINCLUDE_START && (*cur).type_ != XINCLUDE_END {
                        self.o.w(b"\n");
                    }
                    if !(*cur).next.is_null() {
                        cur = (*cur).next;
                        break;
                    }
                    cur = parent;
                    parent = (*cur).parent;
                    if (*cur).type_ == ELEMENT_NODE {
                        if self.level > 0 {
                            self.level -= 1;
                        }
                        if self.format == 1 {
                            self.write_indent(0);
                        }
                        self.o.w(b"</");
                        self.qname(cur);
                        if self.format == 2 {
                            self.ws_nonsig(0);
                        }
                        self.o.w(b">");
                        if cur == unformatted {
                            self.format = format;
                            unformatted = null_mut();
                        }
                    }
                }
            }
        }
    }

    /// `xmlSaveDocInternal`.
    pub unsafe fn doc(&mut self, d: *mut Doc, encoding: Option<Vec<u8>>) -> c_int {
        unsafe {
            if (*d).type_ != DOCUMENT_NODE && (*d).type_ != HTML_DOCUMENT_NODE {
                return -1;
            }
            if (*d).type_ == HTML_DOCUMENT_NODE && self.options & (SAVE_AS_XML | SAVE_XHTML) == 0 || self.options & SAVE_AS_HTML != 0 {
                return -1;
            }
            let encoding = encoding.or_else(|| copt((*d).encoding).map(|e| e.to_vec()));
            let mut switched = false;
            if let Some(e) = &encoding {
                if self.encoding.is_none() {
                    let Some(enc) = enc_by_name(e) else {
                        return -1;
                    };
                    self.o.flush();
                    self.o.enc = enc;
                    self.o.out.extend_from_slice(bom(e));
                    self.encoding = Some(e.clone());
                    switched = true;
                }
            }
            if self.options & SAVE_NO_DECL == 0 {
                self.o.w(b"<?xml version=\"");
                match copt((*d).version) {
                    Some(v) => self.o.w(v),
                    None => self.o.w(b"1.0"),
                }
                self.o.w(b"\"");
                if let Some(e) = &encoding {
                    self.o.w(b" encoding=\"");
                    self.o.w(e);
                    self.o.w(b"\"");
                }
                match (*d).standalone {
                    0 => self.o.w(b" standalone=\"no\""),
                    1 => self.o.w(b" standalone=\"yes\""),
                    _ => {}
                }
                self.o.w(b"?>\n");
            }
            let mut c = (*d).children;
            while !c.is_null() {
                self.level = 0;
                self.node(c);
                if (*c).type_ != XINCLUDE_START && (*c).type_ != XINCLUDE_END {
                    self.o.w(b"\n");
                }
                c = (*c).next;
            }
            if switched {
                self.o.flush();
                self.o.enc = Enc::Utf8;
                self.encoding = None;
            }
            0
        }
    }
}

// --- the save API ----------------------------------------------------------------------------------

unsafe fn new_save(sink: Sink, encoding: *const c_char, options: c_int) -> *mut SaveCtxt {
    unsafe {
        let enc = copt(encoding as *const XChar).map(|e| e.to_vec());
        if let Some(e) = &enc {
            if enc_by_name(e).is_none() {
                return null_mut();
            }
        }
        let b = enc.as_deref().map_or(&[][..], bom);
        let mut c = SaveCtxt::new(sink, enc.clone(), options);
        c.o.out.extend_from_slice(b);
        Box::into_raw(Box::new(c))
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSaveToBuffer(b: *mut Buffer, encoding: *const c_char, options: c_int) -> *mut SaveCtxt {
    unsafe {
        if b.is_null() {
            return null_mut();
        }
        new_save(Sink::Buffer(b), encoding, options)
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSaveToIO(w: WriteCb, c: CloseCb, ctx: *mut c_void, encoding: *const c_char, options: c_int) -> *mut SaveCtxt {
    unsafe { new_save(Sink::Io(w, c, ctx), encoding, options) }
}

unsafe fn open_out(filename: *const c_char) -> Option<Sink> {
    unsafe {
        let name = copt(filename as *const XChar)?;
        if name == b"-" {
            return Some(Sink::Stdout);
        }
        let name = name.strip_prefix(b"file://localhost").or_else(|| name.strip_prefix(b"file://")).unwrap_or(name);
        let p = std::str::from_utf8(name).ok()?;
        std::fs::File::create(p).ok().map(Sink::File)
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSaveToFilename(filename: *const c_char, encoding: *const c_char, options: c_int) -> *mut SaveCtxt {
    unsafe {
        match open_out(filename) {
            Some(s) => new_save(s, encoding, options),
            None => null_mut(),
        }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSaveToFd(fd: c_int, encoding: *const c_char, options: c_int) -> *mut SaveCtxt {
    unsafe {
        unsafe extern "C" fn fd_write(ctx: *mut c_void, b: *const c_char, n: c_int) -> c_int {
            unsafe { write(ctx as isize as c_int, b as *const c_void, n as usize) as c_int }
        }
        unsafe extern "C" {
            fn write(fd: c_int, b: *const c_void, n: usize) -> isize;
        }
        if fd < 0 {
            return null_mut();
        }
        new_save(Sink::Io(Some(fd_write), None, fd as isize as *mut c_void), encoding, options)
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSaveDoc(c: *mut SaveCtxt, d: *mut Doc) -> c_long {
    unsafe {
        if c.is_null() || d.is_null() {
            return -1;
        }
        let enc = (*c).encoding.clone();
        if (*c).doc(d, enc) < 0 {
            return -1;
        }
        0
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSaveTree(c: *mut SaveCtxt, n: *mut Node) -> c_long {
    unsafe {
        if c.is_null() || n.is_null() {
            return -1;
        }
        (*c).node(n);
        0
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSaveFlush(c: *mut SaveCtxt) -> c_int {
    unsafe { if c.is_null() { -1 } else { (*c).o.flush() } }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSaveClose(c: *mut SaveCtxt) -> c_int {
    unsafe {
        if c.is_null() {
            return -1;
        }
        let mut b = Box::from_raw(c);
        let r = b.o.flush();
        b.o.close();
        r
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSaveFinish(c: *mut SaveCtxt) -> c_int {
    unsafe {
        if c.is_null() {
            return ERR_INTERNAL_ERROR;
        }
        let mut b = Box::from_raw(c);
        let r = b.o.close();
        if r < 0 { ERR_INTERNAL_ERROR } else { ERR_OK }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSaveSetIndentString(c: *mut SaveCtxt, indent: *const c_char) -> c_int {
    unsafe {
        if c.is_null() {
            return -1;
        }
        let ind = copt(indent as *const XChar).unwrap_or(b"");
        let c = &mut *c;
        c.indent_size = ind.len() as c_int;
        c.indent_nr = if ind.is_empty() { 0 } else { 60 / ind.len() as c_int };
        c.indent = ind.repeat(c.indent_nr as usize);
        0
    }
}

/// `xmlDocDumpInternal` into a fresh output.
unsafe fn dump_doc(sink: Sink, d: *mut Doc, encoding: *const c_char, format: c_int) -> Out {
    unsafe {
        let mut options = SAVE_AS_XML;
        if format != 0 {
            options |= SAVE_FORMAT;
        }
        let mut c = SaveCtxt::new(sink, None, options);
        c.doc(d, copt(encoding as *const XChar).map(|e| e.to_vec()));
        c.o
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlDocDumpFormatMemoryEnc(d: *mut Doc, mem: *mut *mut XChar, size: *mut c_int, encoding: *const c_char, format: c_int) {
    unsafe {
        if !size.is_null() {
            *size = 0;
        }
        if mem.is_null() {
            return;
        }
        *mem = null_mut();
        if d.is_null() {
            return;
        }
        let o = dump_doc(Sink::Mem, d, encoding, format);
        let p = xmalloc(o.out.len() + 1) as *mut XChar;
        if p.is_null() {
            return;
        }
        std::ptr::copy_nonoverlapping(o.out.as_ptr(), p, o.out.len());
        *p.add(o.out.len()) = 0;
        *mem = p;
        if !size.is_null() {
            *size = o.out.len() as c_int;
        }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlDocDumpMemory(d: *mut Doc, mem: *mut *mut XChar, size: *mut c_int) {
    unsafe { xmlDocDumpFormatMemoryEnc(d, mem, size, null(), 0) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlDocDumpFormatMemory(d: *mut Doc, mem: *mut *mut XChar, size: *mut c_int, format: c_int) {
    unsafe { xmlDocDumpFormatMemoryEnc(d, mem, size, null(), format) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlDocDumpMemoryEnc(d: *mut Doc, mem: *mut *mut XChar, size: *mut c_int, encoding: *const c_char) {
    unsafe { xmlDocDumpFormatMemoryEnc(d, mem, size, encoding, 0) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSaveFormatFileEnc(filename: *const c_char, d: *mut Doc, encoding: *const c_char, format: c_int) -> c_int {
    unsafe {
        if d.is_null() {
            return -1;
        }
        let Some(sink) = open_out(filename) else { return -1 };
        let mut o = dump_doc(sink, d, encoding, format);
        o.close()
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSaveFileEnc(filename: *const c_char, d: *mut Doc, encoding: *const c_char) -> c_int {
    unsafe { xmlSaveFormatFileEnc(filename, d, encoding, 0) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSaveFormatFile(filename: *const c_char, d: *mut Doc, format: c_int) -> c_int {
    unsafe { xmlSaveFormatFileEnc(filename, d, null(), format) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSaveFile(filename: *const c_char, d: *mut Doc) -> c_int {
    unsafe { xmlSaveFormatFileEnc(filename, d, null(), 0) }
}

// A C `FILE *`, written through `fwrite`.
unsafe extern "C" {
    fn fwrite(p: *const c_void, size: usize, n: usize, f: *mut c_void) -> usize;
}

unsafe extern "C" fn file_write(ctx: *mut c_void, b: *const c_char, n: c_int) -> c_int {
    unsafe { fwrite(b as *const c_void, 1, n as usize, ctx) as c_int }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlDocFormatDump(f: *mut c_void, d: *mut Doc, format: c_int) -> c_int {
    unsafe {
        if f.is_null() || d.is_null() {
            return -1;
        }
        let mut o = dump_doc(Sink::Io(Some(file_write), None, f), d, null(), format);
        o.close()
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlDocDump(f: *mut c_void, d: *mut Doc) -> c_int {
    unsafe { xmlDocFormatDump(f, d, 0) }
}

/// `xmlNodeDumpOutput` over `sink`, in UTF-8.
unsafe fn dump_node(sink: Sink, n: *mut Node, level: c_int, format: c_int) -> Out {
    unsafe {
        let mut options = SAVE_AS_XML;
        if format != 0 {
            options |= SAVE_FORMAT;
        }
        let mut c = SaveCtxt::new(sink, Some(b"UTF-8".to_vec()), options);
        c.level = level.clamp(0, 100);
        c.node(n);
        c.o
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNodeDump(b: *mut Buffer, _d: *mut Doc, n: *mut Node, level: c_int, format: c_int) -> c_int {
    unsafe {
        if b.is_null() || n.is_null() {
            return -1;
        }
        let o = dump_node(Sink::Mem, n, level, format);
        if buf_add(b, &o.out) != 0 {
            return -1;
        }
        o.out.len().min(c_int::MAX as usize) as c_int
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlElemDump(f: *mut c_void, _d: *mut Doc, n: *mut Node) {
    unsafe {
        if f.is_null() || n.is_null() {
            return;
        }
        let mut o = dump_node(Sink::Io(Some(file_write), None, f), n, 0, 1);
        o.close();
    }
}
