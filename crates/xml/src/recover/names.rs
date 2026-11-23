//! Character classes, names and character references (parser.c 2566-3500).
use super::codes::*;
use super::tables::*;
use super::*;
use crate::lenient::{opt_eq, vec_of};
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {


fn in_ranges(c: u32, r: &[(u32, u32)]) -> bool {
    let mut lo = 0usize;
    let mut hi = r.len();
    while lo < hi
        invariant
            hi <= r@.len(),
        decreases hi - lo,
    {
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
pub fn is_letter(c: u32) -> (r: bool)
    ensures
        r ==> c != 0,
{
    let base = if c < 0x100 {
        (0x41 <= c && c <= 0x5A) || (0x61 <= c && c <= 0x7A) || (0xC0 <= c && c <= 0xD6) || (0xD8 <= c && c <= 0xF6) || c >= 0xF8
    } else {
        in_ranges(c, &BASE_CHAR)
    };
    let ideo = c >= 0x100 && ((0x4E00 <= c && c <= 0x9FA5) || c == 0x3007 || (0x3021 <= c && c <= 0x3029));
    base || ideo
}

pub fn is_digit(c: u32) -> (r: bool)
    ensures
        r ==> c != 0,
{
    if c < 0x100 { 0x30 <= c && c <= 0x39 } else { in_ranges(c, &DIGIT) }
}

pub fn is_combining(c: u32) -> (r: bool)
    ensures
        r ==> c != 0,
{
    c >= 0x100 && in_ranges(c, &COMBINING)
}

pub fn is_extender(c: u32) -> (r: bool)
    ensures
        r ==> c != 0,
{
    if c < 0x100 { c == 0xB7 } else { in_ranges(c, &EXTENDER) }
}

pub use crate::lenient::is_pubid_char;
use crate::lenient::{name_char_new, name_start_new};

/// `xmlIsNameStartChar`.
pub fn is_name_start(c: u32, old10: bool) -> (r: bool)
    ensures
        r ==> c != 0,
        !old10 ==> r == crate::chars::name_start_cp(c as int),
{
    if !old10 {
        name_start_new(c)
    } else {
        c != 0x20 && c != 0x3E && c != 0x2F && (is_letter(c) || c == 0x5F || c == 0x3A)
    }
}

/// `xmlIsNameChar`.
pub fn is_name_char(c: u32, old10: bool) -> (r: bool)
    ensures
        r ==> c != 0,
        !old10 ==> r == crate::chars::name_cp(c as int),
{
    if !old10 {
        name_char_new(c)
    } else {
        c != 0x20 && c != 0x3E && c != 0x2F && (is_letter(c) || is_digit(c) || c == 0x2E || c == 0x2D || c == 0x5F
            || c == 0x3A || is_combining(c) || is_extender(c))
    }
}

/// An ASCII digit.
pub fn is_digit_ch(c: u8) -> (r: bool)
    ensures
        r == (0x30 <= c <= 0x39),
{
    0x30 <= c && c <= 0x39
}

const SCAN_NC: u32 = 1;
const SCAN_NMTOKEN: u32 = 2;
const SCAN_OLD10: u32 = 4;

/// `xmlScanName`: the end of the name at `i` in `s`, `None` when it is
/// longer than `max`.
pub fn scan_name(s: &[u8], i: usize, max: usize, flags: u32) -> (r: Option<usize>)
    ensures
        r matches Some(p) ==> i <= p && (p == i || p <= s@.len()),
{
    let mut flags = flags;
    let stop: u32 = if flags & SCAN_NC != 0 { 0x3A } else { 0 };
    let old10 = flags & SCAN_OLD10 != 0;
    let mut p = i;
    let mut max = max;
    let _n = s.len();
    loop
        invariant
            _n == s@.len(),
            i <= p,
            p == i || p <= s@.len(),
        decreases s@.len() + 1 - p,
    {
        let mut c = at(s, p) as u32;
        let len: usize;
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
                },
            }
        }
        let ok = if flags & SCAN_NMTOKEN != 0 { is_name_char(c, old10) } else { is_name_start(c, old10) };
        if !ok {
            break;
        }
        if len > max {
            return None;
        }
        p = p + len;
        max = max - len;
        flags = flags | SCAN_NMTOKEN;
    }
    Some(p)
}

fn ascii_name_start(c: u8) -> (r: bool)
    ensures
        r ==> c != 0,
{
    (0x61 <= c && c <= 0x7A) || (0x41 <= c && c <= 0x5A) || c == 0x5F || c == 0x3A
}

fn ascii_name_char(c: u8) -> (r: bool)
    ensures
        r ==> c != 0,
{
    (0x61 <= c && c <= 0x7A) || (0x41 <= c && c <= 0x5A) || (0x30 <= c && c <= 0x39) || c == 0x5F || c == 0x2D || c == 0x3A || c == 0x2E
}

impl<S: Sink> Parser<S> {
    fn old10(&self) -> bool {
        self.options & PARSE_OLD10 != 0
    }

    /// `xmlParseCharRef`: the character, 0 on error.
    pub fn parse_char_ref(&mut self) -> u32
        requires
            old(self).wf(),
        ensures
            final(self).advances(old(self)),
    {
        let mut val: u32 = 0;
        let mut count: u32 = 0;
        if self.cur() == 0x26 && self.nxt(1) == 0x23 && self.nxt(2) == 0x78 {
            self.skip(3);
            self.grow();
            while self.cur() != 0x3B && !self.stopped()
                invariant
                    self.advances(old(self)),
                    val <= 0x110000,
                    count <= 22,
                decreases self.fuel,
            {
                if !self.step() {
                    break;
                }
                let prev = count;
                count = count + 1;
                if prev > 20 {
                    count = 0;
                    self.grow();
                }
                let c = self.cur();
                if is_digit_ch(c) {
                    val = val * 16 + (c - 0x30) as u32;
                } else if 0x61 <= c && c <= 0x66 && count < 20 {
                    val = val * 16 + (c - 0x61) as u32 + 10;
                } else if 0x41 <= c && c <= 0x46 && count < 20 {
                    val = val * 16 + (c - 0x41) as u32 + 10;
                } else {
                    self.fatal(ERR_INVALID_HEX_CHARREF, None);
                    val = 0;
                    break;
                }
                if val > 0x110000 {
                    val = 0x110000;
                }
                self.next();
                count = count + 1;
            }
            if self.cur() == 0x3B {
                let i = self.inp_mut();
                i.col = sat_add_i32(i.col, 1);
                i.cur = i.cur.saturating_add(1);
            }
        } else if self.cur() == 0x26 && self.nxt(1) == 0x23 {
            self.skip(2);
            self.grow();
            while self.cur() != 0x3B
                invariant
                    self.advances(old(self)),
                    val <= 0x110000,
                    count <= 22,
                decreases self.fuel,
            {
                if !self.step() {
                    break;
                }
                let prev = count;
                count = count + 1;
                if prev > 20 {
                    count = 0;
                    self.grow();
                }
                let c = self.cur();
                if is_digit_ch(c) {
                    val = val * 10 + (c - 0x30) as u32;
                } else {
                    self.fatal(ERR_INVALID_DEC_CHARREF, None);
                    val = 0;
                    break;
                }
                if val > 0x110000 {
                    val = 0x110000;
                }
                self.next();
                count = count + 1;
            }
            if self.cur() == 0x3B {
                let i = self.inp_mut();
                i.col = sat_add_i32(i.col, 1);
                i.cur = i.cur.saturating_add(1);
            }
        } else {
            if self.cur() == 0x26 {
                self.skip(1);
            }
            self.fatal(ERR_INVALID_CHARREF, None);
        }
        if val >= 0x110000 {
            let m = b"xmlParseCharRef: character reference out of bounds\n";
            self.fatal_int(ERR_INVALID_CHAR, m, val as i32);
            val = 0xFFFD;
        } else if !is_char(val) {
            let m = cat(&[b"xmlParseCharRef: invalid xmlChar value ", itoa(val as i64).as_slice(), b"\n"]);
            self.fatal_int(ERR_INVALID_CHAR, m.as_slice(), val as i32);
        }
        val
    }

    /// `xmlParseStringCharRef` over `s` at `*i`.
    pub fn parse_string_char_ref(&mut self, s: &[u8], i: &mut usize) -> u32
        requires
            old(self).wf(),
        ensures
            final(self).only_sink(old(self)),
            *final(i) >= *old(i),
            *final(i) == *old(i) || *final(i) <= s@.len(),
    {
        let _n = s.len();
        let mut p = *i;
        let mut val: u32 = 0;
        if at(s, p) == 0x26 && crate::lenient::at_off(s, p, 1) == 0x23 && crate::lenient::at_off(s, p, 2) == 0x78 {
            p = p + 3;
            let mut c = at(s, p);
            while c != 0x3B
                invariant
                    _n == s@.len(),
                    *old(i) < p <= s@.len(),
                    c == crate::lenient::at_spec(s@, p as int),
                    val <= 0x110000,
                    self.wf(),
                    self.only_sink(old(self)),
                decreases s@.len() - p,
            {
                if is_digit_ch(c) {
                    val = val * 16 + (c - 0x30) as u32;
                } else if 0x61 <= c && c <= 0x66 {
                    val = val * 16 + (c - 0x61) as u32 + 10;
                } else if 0x41 <= c && c <= 0x46 {
                    val = val * 16 + (c - 0x41) as u32 + 10;
                } else {
                    self.fatal(ERR_INVALID_HEX_CHARREF, None);
                    val = 0;
                    break;
                }
                if val > 0x110000 {
                    val = 0x110000;
                }
                p = p + 1;
                c = at(s, p);
            }
            if c == 0x3B {
                p = p + 1;
            }
        } else if at(s, p) == 0x26 && crate::lenient::at_off(s, p, 1) == 0x23 {
            p = p + 2;
            let mut c = at(s, p);
            while c != 0x3B
                invariant
                    _n == s@.len(),
                    *old(i) < p <= s@.len(),
                    c == crate::lenient::at_spec(s@, p as int),
                    val <= 0x110000,
                    self.wf(),
                    self.only_sink(old(self)),
                decreases s@.len() - p,
            {
                if is_digit_ch(c) {
                    val = val * 10 + (c - 0x30) as u32;
                } else {
                    self.fatal(ERR_INVALID_DEC_CHARREF, None);
                    val = 0;
                    break;
                }
                if val > 0x110000 {
                    val = 0x110000;
                }
                p = p + 1;
                c = at(s, p);
            }
            if c == 0x3B {
                p = p + 1;
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
            let m = cat(&[b"xmlParseStringCharRef: invalid xmlChar value ", itoa(val as i64).as_slice(), b"\n"]);
            self.fatal_int(ERR_INVALID_CHAR, m.as_slice(), val as i32);
        }
        0
    }

    /// The bytes `from..to` of the current input.
    pub fn slice(&self, from: usize, to: usize) -> Vec<u8>
        requires
            self.wf(),
    {
        let b = &self.inp().buf;
        let to = if to < b.len() { to } else { b.len() };
        if from < to { vec_of(slice_subrange(b.as_slice(), from, to)) } else { Vec::new() }
    }

    fn parse_name_complex(&mut self) -> Option<Vec<u8>>
        requires
            old(self).wf(),
        ensures
            final(self).advances(old(self)),
    {
        let max = if self.options & PARSE_HUGE != 0 { MAX_TEXT_LENGTH } else { MAX_NAME_LENGTH };
        let old10 = self.old10();
        let r = self.current_char();
        let (mut c, mut l) = (r.0, r.1);
        if !is_name_start(c, old10) {
            return None;
        }
        let mut len: usize = l;
        self.nextl(l);
        let r = self.current_char();
        c = r.0;
        l = r.1;
        while is_name_char(c, old10)
            invariant
                self.advances(old(self)),
            decreases self.fuel,
        {
            if !self.step() {
                break;
            }
            len = len.saturating_add(l);
            self.nextl(l);
            let r = self.current_char();
            c = r.0;
            l = r.1;
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
        let crlf = self.cur() == 0x0A && cur > 0 && at(&self.inp().buf, cur - 1) == 0x0D;
        if crlf {
            Some(self.slice(cur.saturating_sub(len + 1), cur - 1))
        } else {
            Some(self.slice(cur.saturating_sub(len), cur))
        }
    }

    /// `xmlParseName`.
    pub fn parse_name(&mut self) -> Option<Vec<u8>>
        requires
            old(self).wf(),
        ensures
            final(self).advances(old(self)),
    {
        let max = if self.options & PARSE_HUGE != 0 { MAX_TEXT_LENGTH } else { MAX_NAME_LENGTH };
        self.grow();
        let start = self.inp().cur;
        let _n = self.inp().buf.len();
        let mut p = start;
        if ascii_name_start(at(&self.inp().buf, p)) {
            p = p + 1;
            while ascii_name_char(at(&self.inp().buf, p))
                invariant
                    self.wf(),
                    _n == self.top().buf@.len(),
                    start < p <= _n,
                decreases _n - p,
            {
                p = p + 1;
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
                i.col = sat_add_i32(i.col, count as i32);
                return Some(r);
            }
        }
        self.parse_name_complex()
    }

    fn parse_ncname_complex(&mut self) -> Option<Vec<u8>>
        requires
            old(self).wf(),
        ensures
            final(self).advances(old(self)),
    {
        let max = if self.options & PARSE_HUGE != 0 { MAX_TEXT_LENGTH } else { MAX_NAME_LENGTH };
        let old10 = self.old10();
        let start = self.inp().cur;
        let r = self.current_char();
        let (mut c, mut l) = (r.0, r.1);
        if c == 0x20 || c == 0x3E || c == 0x2F || !is_name_start(c, old10) || c == 0x3A {
            return None;
        }
        let mut len: usize = 0;
        while c != 0x20 && c != 0x3E && c != 0x2F && is_name_char(c, old10) && c != 0x3A
            invariant
                self.advances(old(self)),
            decreases self.fuel,
        {
            if !self.step() {
                break;
            }
            len = len.saturating_add(l);
            self.nextl(l);
            let r = self.current_char();
            c = r.0;
            l = r.1;
        }
        if len > max {
            self.fatal(ERR_NAME_TOO_LONG, Some(b"NCName"));
            return None;
        }
        Some(self.slice(start, start.saturating_add(len)))
    }

    /// `xmlParseNCName`.
    pub fn parse_ncname(&mut self) -> Option<Vec<u8>>
        requires
            old(self).wf(),
        ensures
            final(self).advances(old(self)),
    {
        let max = if self.options & PARSE_HUGE != 0 { MAX_TEXT_LENGTH } else { MAX_NAME_LENGTH };
        let start = self.inp().cur;
        let e = self.inp().buf.len();
        let mut p = start;
        let c0 = at(&self.inp().buf, p);
        if ((0x61 <= c0 && c0 <= 0x7A) || (0x41 <= c0 && c0 <= 0x5A) || c0 == 0x5F) && p < e {
            p = p + 1;
            loop
                invariant
                    self.wf(),
                    e == self.top().buf@.len(),
                    start <= p <= e,
                decreases e - p,
            {
                let c = at(&self.inp().buf, p);
                if ((0x61 <= c && c <= 0x7A) || (0x41 <= c && c <= 0x5A) || (0x30 <= c && c <= 0x39) || c == 0x5F || c
                    == 0x2D || c == 0x2E) && p < e {
                    p = p + 1;
                } else {
                    break;
                }
            }
            if p < e {
                let c = at(&self.inp().buf, p);
                if c > 0 && c < 0x80 {
                    let count = p - start;
                    if count > max {
                        self.fatal(ERR_NAME_TOO_LONG, Some(b"NCName"));
                        return None;
                    }
                    let r = self.slice(start, p);
                    let i = self.inp_mut();
                    i.cur = p;
                    i.col = sat_add_i32(i.col, count as i32);
                    return Some(r);
                }
            }
        }
        self.parse_ncname_complex()
    }

    /// `xmlParseNameAndCompare`: `Ok(())` when the name is `other`, else
    /// the name read (or `None`).
    pub fn parse_name_and_compare(&mut self, other: &[u8]) -> Result<(), Option<Vec<u8>>>
        requires
            old(self).wf(),
        ensures
            final(self).advances(old(self)),
    {
        self.grow();
        let start = self.inp().cur;
        let _n = self.inp().buf.len();
        let mut p = start;
        let mut k: usize = 0;
        while at(&self.inp().buf, p) != 0 && k < other.len() && at(&self.inp().buf, p) == other[k]
            invariant
                self.wf(),
                _n == self.top().buf@.len(),
                start <= p,
                p == start || p <= _n,
                k <= other@.len(),
            decreases other@.len() - k,
        {
            p = p + 1;
            k = k + 1;
        }
        let c = at(&self.inp().buf, p);
        if k == other.len() && (c == 0x3E || blank(c)) {
            let i = self.inp_mut();
            i.col = sat_add_i32(i.col, (p - start) as i32);
            i.cur = p;
            return Ok(());
        }
        let r = self.parse_name();
        if opt_eq(opt_slice(&r), Some(other)) {
            return Ok(());
        }
        Err(r)
    }

    /// `xmlParseStringName` over `s` at `*i`.
    pub fn parse_string_name(&mut self, s: &[u8], i: &mut usize) -> Option<Vec<u8>>
        requires
            old(self).wf(),
        ensures
            final(self).only_sink(old(self)),
            *final(i) >= *old(i),
            *final(i) == *old(i) || *final(i) <= s@.len(),
    {
        let max = if self.options & PARSE_HUGE != 0 { MAX_TEXT_LENGTH } else { MAX_NAME_LENGTH };
        let flags = if self.old10() { SCAN_OLD10 } else { 0 };
        match scan_name(s, *i, max, flags) {
            None => {
                self.fatal(ERR_NAME_TOO_LONG, Some(b"NCName"));
                None
            },
            Some(e) => {
                if e == *i {
                    return None;
                }
                let r = vec_of(slice_subrange(s, *i, e));
                *i = e;
                Some(r)
            },
        }
    }

    /// `xmlParseNmtoken`.
    pub fn parse_nmtoken(&mut self) -> Option<Vec<u8>>
        requires
            old(self).wf(),
        ensures
            final(self).advances(old(self)),
    {
        let max = if self.options & PARSE_HUGE != 0 { MAX_TEXT_LENGTH } else { MAX_NAME_LENGTH };
        let old10 = self.old10();
        let mut buf: Vec<u8> = Vec::new();
        let r = self.current_char();
        let (mut c, mut l) = (r.0, r.1);
        while is_name_char(c, old10)
            invariant
                self.advances(old(self)),
            decreases self.fuel,
        {
            if !self.step() {
                break;
            }
            push_char(&mut buf, c);
            self.nextl(l);
            let r = self.current_char();
            c = r.0;
            l = r.1;
            if buf.len() >= MAX_NAMELEN {
                // The growing buffer: capacity starts at twice the length
                // and grows by half, up to the limit.
                let mut cap: usize = buf.len().saturating_mul(2);
                while is_name_char(c, old10)
                    invariant
                        self.advances(old(self)),
                    decreases self.fuel,
                {
                    if !self.step() {
                        break;
                    }
                    if buf.len().saturating_add(10) > cap {
                        if cap >= max {
                            self.fatal(ERR_NAME_TOO_LONG, Some(b"NmToken"));
                            return None;
                        }
                        let extra = cap / 2 + cap % 2;
                        cap = if cap > max - extra { max } else { cap + extra };
                    }
                    push_char(&mut buf, c);
                    self.nextl(l);
                    let r = self.current_char();
                    c = r.0;
                    l = r.1;
                }
                return Some(buf);
            }
        }
        if buf.len() == 0 {
            return None;
        }
        if buf.len() > max {
            self.fatal(ERR_NAME_TOO_LONG, Some(b"NmToken"));
            return None;
        }
        Some(buf)
    }
}

} // verus!
