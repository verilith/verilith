//! Character classes, names and character references (parser.c 2566-3500).
use super::codes::*;
use super::tables::*;
use super::*;

fn in_ranges(c: u32, r: &[(u32, u32)]) -> bool {
    let mut lo = 0usize;
    let mut hi = r.len();
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if c < r[mid].0 {
            hi = mid;
        } else if c > r[mid].1 {
            lo = mid + 1;
        } else {
            return true;
        }
    }
    false
}

/// `IS_LETTER` (XML 1.0 4th edition, chvalid.h).
pub fn is_letter(c: u32) -> bool {
    let base = if c < 0x100 {
        (0x41..=0x5A).contains(&c) || (0x61..=0x7A).contains(&c) || (0xC0..=0xD6).contains(&c) || (0xD8..=0xF6).contains(&c) || c >= 0xF8
    } else {
        in_ranges(c, &BASE_CHAR)
    };
    let ideo = c >= 0x100 && ((0x4E00..=0x9FA5).contains(&c) || c == 0x3007 || (0x3021..=0x3029).contains(&c));
    base || ideo
}

pub fn is_digit(c: u32) -> bool {
    if c < 0x100 { (0x30..=0x39).contains(&c) } else { in_ranges(c, &DIGIT) }
}

pub fn is_combining(c: u32) -> bool {
    c >= 0x100 && in_ranges(c, &COMBINING)
}

pub fn is_extender(c: u32) -> bool {
    if c < 0x100 { c == 0xB7 } else { in_ranges(c, &EXTENDER) }
}

pub use crate::lenient::is_pubid_char;
use crate::lenient::{name_char_new, name_start_new};

/// `xmlIsNameStartChar`.
pub fn is_name_start(c: u32, old10: bool) -> bool {
    if !old10 {
        name_start_new(c)
    } else {
        c != 0x20 && c != b'>' as u32 && c != b'/' as u32 && (is_letter(c) || c == b'_' as u32 || c == b':' as u32)
    }
}

/// `xmlIsNameChar`.
pub fn is_name_char(c: u32, old10: bool) -> bool {
    if !old10 {
        name_char_new(c)
    } else {
        c != 0x20
            && c != b'>' as u32
            && c != b'/' as u32
            && (is_letter(c) || is_digit(c) || c == b'.' as u32 || c == b'-' as u32 || c == b'_' as u32 || c == b':' as u32 || is_combining(c) || is_extender(c))
    }
}

const SCAN_NC: u32 = 1;
const SCAN_NMTOKEN: u32 = 2;
const SCAN_OLD10: u32 = 4;

/// `xmlScanName`: the end of the name at `i` in `s`, `None` when it is
/// longer than `max`.
pub fn scan_name(s: &[u8], i: usize, max: usize, mut flags: u32) -> Option<usize> {
    let stop: u32 = if flags & SCAN_NC != 0 { b':' as u32 } else { 0 };
    let old10 = flags & SCAN_OLD10 != 0;
    let mut p = i;
    let mut max = max;
    loop {
        let mut c = at(s, p) as u32;
        let len;
        if c < 0x80 {
            if c == stop {
                break;
            }
            len = 1;
        } else {
            match utf8_char(s, p, 4) {
                None => break,
                Some((v, l)) => {
                    c = v;
                    len = l;
                }
            }
        }
        let ok = if flags & SCAN_NMTOKEN != 0 { is_name_char(c, old10) } else { is_name_start(c, old10) };
        if !ok {
            break;
        }
        if len > max {
            return None;
        }
        p += len;
        max -= len;
        flags |= SCAN_NMTOKEN;
    }
    Some(p)
}

fn ascii_name_start(c: u8) -> bool {
    c.is_ascii_lowercase() || c.is_ascii_uppercase() || c == b'_' || c == b':'
}

fn ascii_name_char(c: u8) -> bool {
    c.is_ascii_lowercase() || c.is_ascii_uppercase() || c.is_ascii_digit() || c == b'_' || c == b'-' || c == b':' || c == b'.'
}

impl<S: Sink> Parser<S> {
    fn old10(&self) -> bool {
        self.options & PARSE_OLD10 != 0
    }

    /// `xmlParseCharRef`: the character, 0 on error.
    pub fn parse_char_ref(&mut self) -> u32 {
        let mut val: u32 = 0;
        let mut count: u32 = 0;
        if self.cur() == b'&' && self.nxt(1) == b'#' && self.nxt(2) == b'x' {
            self.skip(3);
            self.grow();
            while self.cur() != b';' && !self.stopped() {
                let prev = count;
                count += 1;
                if prev > 20 {
                    count = 0;
                    self.grow();
                }
                let c = self.cur();
                if c.is_ascii_digit() {
                    val = val * 16 + (c - b'0') as u32;
                } else if (b'a'..=b'f').contains(&c) && count < 20 {
                    val = val * 16 + (c - b'a') as u32 + 10;
                } else if (b'A'..=b'F').contains(&c) && count < 20 {
                    val = val * 16 + (c - b'A') as u32 + 10;
                } else {
                    self.fatal(ERR_INVALID_HEX_CHARREF, None);
                    val = 0;
                    break;
                }
                if val > 0x110000 {
                    val = 0x110000;
                }
                self.next();
                count += 1;
            }
            if self.cur() == b';' {
                let i = self.inp_mut();
                i.col = i.col.saturating_add(1);
                i.cur += 1;
            }
        } else if self.cur() == b'&' && self.nxt(1) == b'#' {
            self.skip(2);
            self.grow();
            while self.cur() != b';' {
                let prev = count;
                count += 1;
                if prev > 20 {
                    count = 0;
                    self.grow();
                }
                let c = self.cur();
                if c.is_ascii_digit() {
                    val = val * 10 + (c - b'0') as u32;
                } else {
                    self.fatal(ERR_INVALID_DEC_CHARREF, None);
                    val = 0;
                    break;
                }
                if val > 0x110000 {
                    val = 0x110000;
                }
                self.next();
                count += 1;
            }
            if self.cur() == b';' {
                let i = self.inp_mut();
                i.col = i.col.saturating_add(1);
                i.cur += 1;
            }
        } else {
            if self.cur() == b'&' {
                self.skip(1);
            }
            self.fatal(ERR_INVALID_CHARREF, None);
        }
        if val >= 0x110000 {
            let m = b"xmlParseCharRef: character reference out of bounds\n";
            self.fatal_int(ERR_INVALID_CHAR, m, val as i32);
            val = 0xFFFD;
        } else if !is_char(val) {
            let m = cat(&[b"xmlParseCharRef: invalid xmlChar value ", &itoa(val as i64), b"\n"]);
            self.fatal_int(ERR_INVALID_CHAR, &m, val as i32);
        }
        val
    }

    /// `xmlParseStringCharRef` over `s` at `*i`.
    pub fn parse_string_char_ref(&mut self, s: &[u8], i: &mut usize) -> u32 {
        let mut p = *i;
        let mut val: u32 = 0;
        if at(s, p) == b'&' && at(s, p + 1) == b'#' && at(s, p + 2) == b'x' {
            p += 3;
            let mut c = at(s, p);
            while c != b';' {
                if c.is_ascii_digit() {
                    val = val * 16 + (c - b'0') as u32;
                } else if (b'a'..=b'f').contains(&c) {
                    val = val * 16 + (c - b'a') as u32 + 10;
                } else if (b'A'..=b'F').contains(&c) {
                    val = val * 16 + (c - b'A') as u32 + 10;
                } else {
                    self.fatal(ERR_INVALID_HEX_CHARREF, None);
                    val = 0;
                    break;
                }
                if val > 0x110000 {
                    val = 0x110000;
                }
                p += 1;
                c = at(s, p);
            }
            if c == b';' {
                p += 1;
            }
        } else if at(s, p) == b'&' && at(s, p + 1) == b'#' {
            p += 2;
            let mut c = at(s, p);
            while c != b';' {
                if c.is_ascii_digit() {
                    val = val * 10 + (c - b'0') as u32;
                } else {
                    self.fatal(ERR_INVALID_DEC_CHARREF, None);
                    val = 0;
                    break;
                }
                if val > 0x110000 {
                    val = 0x110000;
                }
                p += 1;
                c = at(s, p);
            }
            if c == b';' {
                p += 1;
            }
        } else {
            self.fatal(ERR_INVALID_CHARREF, None);
            return 0;
        }
        *i = p;
        if val >= 0x110000 {
            self.fatal_int(ERR_INVALID_CHAR, b"xmlParseStringCharRef: character reference out of bounds\n", val as i32);
        } else if is_char(val) {
            return val;
        } else {
            let m = cat(&[b"xmlParseStringCharRef: invalid xmlChar value ", &itoa(val as i64), b"\n"]);
            self.fatal_int(ERR_INVALID_CHAR, &m, val as i32);
        }
        0
    }

    /// The bytes `from..to` of the current input.
    pub fn slice(&self, from: usize, to: usize) -> Vec<u8> {
        let b = &self.inp().buf;
        let to = if to < b.len() { to } else { b.len() };
        if from < to { b[from..to].to_vec() } else { Vec::new() }
    }

    fn parse_name_complex(&mut self) -> Option<Vec<u8>> {
        let max = if self.options & PARSE_HUGE != 0 { MAX_TEXT_LENGTH } else { MAX_NAME_LENGTH };
        let old10 = self.old10();
        let (mut c, mut l) = self.current_char();
        if !is_name_start(c, old10) {
            return None;
        }
        let mut len: usize = l;
        self.nextl(l);
        (c, l) = self.current_char();
        while is_name_char(c, old10) {
            len = len.saturating_add(l);
            self.nextl(l);
            (c, l) = self.current_char();
        }
        if len > max {
            self.fatal(ERR_NAME_TOO_LONG, Some(b"Name"));
            return None;
        }
        let (cur, base) = (self.inp().cur, self.inp().base);
        if cur.saturating_sub(base) < len {
            self.fatal(ERR_INTERNAL_ERROR, Some(b"unexpected change of input buffer"));
            return None;
        }
        let crlf = self.cur() == b'\n' && cur > 0 && at(&self.inp().buf, cur - 1) == b'\r';
        if crlf {
            Some(self.slice(cur - (len + 1), cur - 1))
        } else {
            Some(self.slice(cur - len, cur))
        }
    }

    /// `xmlParseName`.
    pub fn parse_name(&mut self) -> Option<Vec<u8>> {
        let max = if self.options & PARSE_HUGE != 0 { MAX_TEXT_LENGTH } else { MAX_NAME_LENGTH };
        self.grow();
        let start = self.inp().cur;
        let mut p = start;
        if ascii_name_start(at(&self.inp().buf, p)) {
            p += 1;
            while ascii_name_char(at(&self.inp().buf, p)) {
                p += 1;
            }
            let c = at(&self.inp().buf, p);
            if c > 0 && c < 0x80 {
                let count = p - start;
                if count > max {
                    self.fatal(ERR_NAME_TOO_LONG, Some(b"Name"));
                    return None;
                }
                let r = self.slice(start, p);
                let i = self.inp_mut();
                i.cur = p;
                i.col = i.col.saturating_add(count as i32);
                return Some(r);
            }
        }
        self.parse_name_complex()
    }

    fn parse_ncname_complex(&mut self) -> Option<Vec<u8>> {
        let max = if self.options & PARSE_HUGE != 0 { MAX_TEXT_LENGTH } else { MAX_NAME_LENGTH };
        let old10 = self.old10();
        let start = self.inp().cur;
        let (mut c, mut l) = self.current_char();
        if c == 0x20 || c == b'>' as u32 || c == b'/' as u32 || !is_name_start(c, old10) || c == b':' as u32 {
            return None;
        }
        let mut len: usize = 0;
        while c != 0x20 && c != b'>' as u32 && c != b'/' as u32 && is_name_char(c, old10) && c != b':' as u32 {
            len = len.saturating_add(l);
            self.nextl(l);
            (c, l) = self.current_char();
        }
        if len > max {
            self.fatal(ERR_NAME_TOO_LONG, Some(b"NCName"));
            return None;
        }
        Some(self.slice(start, start + len))
    }

    /// `xmlParseNCName`.
    pub fn parse_ncname(&mut self) -> Option<Vec<u8>> {
        let max = if self.options & PARSE_HUGE != 0 { MAX_TEXT_LENGTH } else { MAX_NAME_LENGTH };
        let start = self.inp().cur;
        let e = self.inp().buf.len();
        let mut p = start;
        let b = |k: usize, s: &Self| at(&s.inp().buf, k);
        let c0 = b(p, self);
        if (c0.is_ascii_lowercase() || c0.is_ascii_uppercase() || c0 == b'_') && p < e {
            p += 1;
            loop {
                let c = b(p, self);
                if (c.is_ascii_lowercase() || c.is_ascii_uppercase() || c.is_ascii_digit() || c == b'_' || c == b'-' || c == b'.') && p < e {
                    p += 1;
                } else {
                    break;
                }
            }
            if p < e {
                let c = b(p, self);
                if c > 0 && c < 0x80 {
                    let count = p - start;
                    if count > max {
                        self.fatal(ERR_NAME_TOO_LONG, Some(b"NCName"));
                        return None;
                    }
                    let r = self.slice(start, p);
                    let i = self.inp_mut();
                    i.cur = p;
                    i.col = i.col.saturating_add(count as i32);
                    return Some(r);
                }
            }
        }
        self.parse_ncname_complex()
    }

    /// `xmlParseNameAndCompare`: `Ok(())` when the name is `other`, else
    /// the name read (or `None`).
    pub fn parse_name_and_compare(&mut self, other: &[u8]) -> Result<(), Option<Vec<u8>>> {
        self.grow();
        let start = self.inp().cur;
        let mut p = start;
        let mut k = 0;
        while at(&self.inp().buf, p) != 0 && k < other.len() && at(&self.inp().buf, p) == other[k] {
            p += 1;
            k += 1;
        }
        let c = at(&self.inp().buf, p);
        if k == other.len() && (c == b'>' || blank(c)) {
            let i = self.inp_mut();
            i.col = i.col.saturating_add((p - start) as i32);
            i.cur = p;
            return Ok(());
        }
        let r = self.parse_name();
        if r.as_deref() == Some(other) {
            return Ok(());
        }
        Err(r)
    }

    /// `xmlParseStringName` over `s` at `*i`.
    pub fn parse_string_name(&mut self, s: &[u8], i: &mut usize) -> Option<Vec<u8>> {
        let max = if self.options & PARSE_HUGE != 0 { MAX_TEXT_LENGTH } else { MAX_NAME_LENGTH };
        let flags = if self.old10() { SCAN_OLD10 } else { 0 };
        match scan_name(s, *i, max, flags) {
            None => {
                self.fatal(ERR_NAME_TOO_LONG, Some(b"NCName"));
                None
            }
            Some(e) => {
                if e == *i {
                    return None;
                }
                let r = s[*i..e].to_vec();
                *i = e;
                Some(r)
            }
        }
    }

    /// `xmlParseNmtoken`.
    pub fn parse_nmtoken(&mut self) -> Option<Vec<u8>> {
        let max = if self.options & PARSE_HUGE != 0 { MAX_TEXT_LENGTH } else { MAX_NAME_LENGTH };
        let old10 = self.old10();
        let mut buf: Vec<u8> = Vec::new();
        let (mut c, mut l) = self.current_char();
        while is_name_char(c, old10) {
            push_char(&mut buf, c);
            self.nextl(l);
            (c, l) = self.current_char();
            if buf.len() >= MAX_NAMELEN {
                // The growing buffer: capacity starts at twice the length
                // and grows by half, up to the limit.
                let mut cap: usize = buf.len() * 2;
                while is_name_char(c, old10) {
                    if buf.len() + 10 > cap {
                        if cap >= max {
                            self.fatal(ERR_NAME_TOO_LONG, Some(b"NmToken"));
                            return None;
                        }
                        let extra = cap.div_ceil(2);
                        cap = if cap > max - extra { max } else { cap + extra };
                    }
                    push_char(&mut buf, c);
                    self.nextl(l);
                    (c, l) = self.current_char();
                }
                return Some(buf);
            }
        }
        if buf.is_empty() {
            return None;
        }
        if buf.len() > max {
            self.fatal(ERR_NAME_TOO_LONG, Some(b"NmToken"));
            return None;
        }
        Some(buf)
    }
}
