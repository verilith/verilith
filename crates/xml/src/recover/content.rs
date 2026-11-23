//! Character data, start and end tags, CDATA sections and content
//! (parser.c 2067-2227, 2851-2918, 4487-4767, 8127-9890, 1303-1436).
use super::codes::*;
use super::refs::*;
use super::*;
use vstd::prelude::*;

verus! {


/// The `xml` prefix's namespace name.
pub fn xml_ns() -> &'static [u8] {
    b"http://www.w3.org/XML/1998/namespace"
}
/// The `xmlns` prefix's namespace name.
pub fn xmlns_ns() -> &'static [u8] {
    b"http://www.w3.org/2000/xmlns/"
}
pub const MAX_ATTRS: usize = 100_000_000;
pub const MAX_ITEMS: usize = 1_000_000_000;

// Verified (`crate::lenient`).
pub use crate::lenient::{check_language_id, grow_capacity_min, hex2, is_byte_char, test_char_data};

/// Where an attribute's namespace comes from.
#[derive(Clone, Copy, PartialEq, Eq)]
enum NsIdx {
    Empty,
    Xml,
    At(usize),
}

struct Att {
    name: Vec<u8>,
    prefix: Option<Vec<u8>>,
    ns: NsIdx,
    value: Vec<u8>,
}

/// Whether an optional name is `lit`.
pub fn opt_is(o: &Option<Vec<u8>>, lit: &[u8]) -> bool {
    match o {
        Some(v) => crate::lenient::bytes_eq(v, lit),
        None => false,
    }
}

/// `==` on optional names.
pub fn opt_vec_eq(a: &Option<Vec<u8>>, b: &Option<Vec<u8>>) -> bool {
    crate::lenient::opt_eq(opt_slice(a), opt_slice(b))
}

/// A copy of a name stack entry.
fn clone_name(e: &NameEntry) -> NameEntry {
    NameEntry { name: e.name.clone(), prefix: e.prefix.clone(), uri: e.uri.clone(), line: e.line, ns_nr: e.ns_nr }
}

/// A copy of an element's default attributes.
fn clone_defaults(v: &Vec<DefAttr>) -> Vec<DefAttr> {
    let mut r: Vec<DefAttr> = Vec::new();
    let mut k: usize = 0;
    while k < v.len()
        decreases v@.len() - k,
    {
        let d = &v[k];
        r.push(DefAttr { prefix: d.prefix.clone(), name: d.name.clone(), value: d.value.clone(), external: d.external, expanded_size: d.expanded_size });
        k = k + 1;
    }
    r
}

impl<S: Sink> Parser<S> {
    // --- the name and space stacks ---

    /// `nameNsPush`.
    pub fn name_ns_push(&mut self, name: Vec<u8>, prefix: Option<Vec<u8>>, uri: Option<Vec<u8>>, line: i32, ns_nr: usize)
        ensures
            final(self).names@ == old(self).names@.push(NameEntry { name, prefix, uri, line, ns_nr }),
            final(self).inputs == old(self).inputs,
            final(self).fuel == old(self).fuel,
            final(self).sink == old(self).sink,
    {
        self.names.push(NameEntry { name, prefix, uri, line, ns_nr });
    }

    /// `namePop`.
    pub fn name_pop(&mut self)
        ensures
            final(self).names@ == if old(self).names@.len() > 0 { old(self).names@.drop_last() } else { old(self).names@ },
            final(self).inputs == old(self).inputs,
            final(self).fuel == old(self).fuel,
            final(self).sink == old(self).sink,
    {
        self.names.pop();
    }

    /// `ctxt->name`.
    pub fn cur_name(&self) -> Vec<u8> {
        let n = self.names.len();
        if n > 0 { self.names[n - 1].name.clone() } else { Vec::new() }
    }

    /// `spacePush`.
    pub fn space_push(&mut self, v: i32)
        ensures
            final(self).inputs == old(self).inputs,
            final(self).fuel == old(self).fuel,
            final(self).sink == old(self).sink,
            final(self).names == old(self).names,
            final(self).nsdb == old(self).nsdb,
    {
        if self.space_nr < self.spaces.len() {
            self.spaces.set(self.space_nr, v);
        } else {
            self.spaces.push(v);
        }
        self.space_nr = self.space_nr.saturating_add(1);
    }

    /// `spacePop`.
    pub fn space_pop(&mut self)
        ensures
            final(self).space_nr == if old(self).space_nr > 0 { old(self).space_nr - 1 } else { 0 },
            final(self).inputs == old(self).inputs,
            final(self).fuel == old(self).fuel,
            final(self).sink == old(self).sink,
            final(self).names == old(self).names,
            final(self).nsdb == old(self).nsdb,
    {
        if self.space_nr == 0 {
            return;
        }
        self.space_nr = self.space_nr - 1;
        let n = self.space_nr;
        if n < self.spaces.len() {
            self.spaces.set(n, -1);
        }
    }

    fn space_slot(&self) -> usize {
        if self.space_nr > 0 { self.space_nr - 1 } else { 0 }
    }

    /// `*ctxt->space`.
    pub fn space(&self) -> i32 {
        let k = self.space_slot();
        if k < self.spaces.len() { self.spaces[k] } else { -1 }
    }

    pub fn set_space(&mut self, v: i32)
        ensures
            final(self).inputs == old(self).inputs,
            final(self).fuel == old(self).fuel,
            final(self).sink == old(self).sink,
            final(self).names == old(self).names,
            final(self).nsdb == old(self).nsdb,
    {
        let k = self.space_slot();
        if k < self.spaces.len() {
            self.spaces.set(k, v);
        } else {
            self.spaces.push(v);
        }
    }

    // --- character data ---

    /// `areBlanks`.
    fn are_blanks(&mut self, s: &[u8], blank_chars: bool) -> bool
        requires
            old(self).wf(),
        ensures
            final(self).only_sink(old(self)),
    {
        let sp = self.space();
        if sp == 1 || sp == -2 {
            return false;
        }
        if !blank_chars {
            let mut i: usize = 0;
            while i < s.len()
                decreases s@.len() - i,
            {
                if !blank(s[i]) {
                    return false;
                }
                i = i + 1;
            }
        }
        let next = [self.cur(), self.nxt(1)];
        self.sink.blanks_ignorable_in_tree(next)
    }

    /// `xmlCharacters`.
    pub fn characters(&mut self, s: &[u8], is_blank: bool)
        requires
            old(self).wf(),
        ensures
            final(self).inputs == old(self).inputs,
            final(self).fuel == old(self).fuel,
            final(self).names == old(self).names,
            final(self).nsdb == old(self).nsdb,
    {
        if !self.sax_on() {
            return;
        }
        let check = !self.keep_blanks || !self.sink.blanks_same_as_chars();
        self.sync();
        if check && self.are_blanks(s, is_blank) {
            if self.keep_blanks {
                self.sink.ignorable_whitespace(s);
            }
        } else {
            if self.sink.has_characters() {
                self.sink.characters(s);
            }
            if check && self.space() == -1 {
                self.set_space(-2);
            }
        }
    }

    fn chars_from_input(&mut self, in_: usize, is_blank: bool)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).fuel == old(self).fuel,
            final(self).inputs@.len() == old(self).inputs@.len(),
            final(self).top().buf == old(self).top().buf,
            final(self).top().cur == if old(self).top().cur < in_ { in_ } else { old(self).top().cur },
    {
        while in_ > self.inp().cur
            invariant
                self.wf(),
                self.fuel == old(self).fuel,
                self.inputs@.len() == old(self).inputs@.len(),
                self.top().buf == old(self).top().buf,
                self.top().cur == old(self).top().cur || (old(self).top().cur < self.top().cur <= in_),
            decreases in_ - self.top().cur,
        {
            let start = self.inp().cur;
            let mut n = in_ - start;
            if n > MAX_ITEMS {
                n = MAX_ITEMS;
            }
            self.set_cur(start + n);
            let s = self.slice(start, start + n);
            self.characters(&s, is_blank);
        }
    }

    /// The byte at `k` of the current input.
    pub fn bat(&self, k: usize) -> (r: u8)
        requires
            self.wf(),
        ensures
            r == crate::lenient::at_spec(self.top().buf@, k as int),
    {
        at(&self.inp().buf, k)
    }

    /// Moves the current input to `c`.
    pub fn set_cur(&mut self, c: usize)
        requires
            old(self).wf(),
        ensures
            final(self).moves(old(self)),
            final(self).sink == old(self).sink,
            final(self).top().buf == old(self).top().buf,
            final(self).top().cur == c,
    {
        let i = self.inp_mut();
        i.cur = c;
    }

    /// The current input's column and line.
    pub fn set_pos(&mut self, line: i32, col: i32)
        requires
            old(self).wf(),
        ensures
            final(self).moves(old(self)),
            final(self).sink == old(self).sink,
            final(self).top().buf == old(self).top().buf,
            final(self).top().cur == old(self).top().cur,
            final(self).top().line == line,
            final(self).top().col == col,
    {
        let i = self.inp_mut();
        i.line = line;
        i.col = col;
    }

    /// A column further.
    pub fn col_inc(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).moves(old(self)),
            final(self).sink == old(self).sink,
            final(self).top().buf == old(self).top().buf,
            final(self).top().cur == old(self).top().cur,
    {
        let i = self.inp_mut();
        i.col = sat_add_i32(i.col, 1);
    }

    /// A line further.
    pub fn line_inc(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).moves(old(self)),
            final(self).sink == old(self).sink,
            final(self).top().buf == old(self).top().buf,
            final(self).top().cur == old(self).top().cur,
    {
        let i = self.inp_mut();
        i.line = sat_add_i32(i.line, 1);
        i.col = 1;
    }

    /// `xmlParseCharDataInternal`.
    pub fn parse_char_data_internal(&mut self, partial: bool)
        requires
            old(self).wf(),
        ensures
            final(self).evolves(old(self)),
    {
        let mut line = self.inp().line;
        let mut col = self.inp().col;
        let mut terminate = false;
        self.grow();
        let mut in_ = self.inp().cur;
        loop
            invariant
                self.evolves(old(self)),
            decreases self.fuel,
        {
            if !self.step() {
                return;
            }
            // get_more_space:
            let ghost b0 = self.top().buf@;
            let ghost f0 = self.fuel;
            let ghost n0 = self.inputs@.len();
            let _bl = self.inp().buf.len();
            loop
                invariant
                    self.wf(),
                    self.fuel == f0,
                    f0 <= old(self).fuel,
                    self.inputs@.len() == n0,
                    self.top().buf@ == b0,
                    _bl == b0.len(),
                decreases b0.len() - in_,
            {
                let ghost i0 = in_;
                while self.bat(in_) == 0x20
                    invariant
                        self.wf(),
                        self.fuel == f0,
                        self.inputs@.len() == n0,
                        self.top().buf@ == b0,
                        _bl == b0.len(),
                        in_ >= i0,
                    decreases b0.len() - in_,
                {
                    in_ = in_ + 1;
                    self.col_inc();
                }
                if self.bat(in_) == 0x0A {
                    self.line_inc();
                    in_ = in_ + 1;
                    while self.bat(in_) == 0x0A
                        invariant
                            self.wf(),
                            self.fuel == f0,
                            self.inputs@.len() == n0,
                            self.top().buf@ == b0,
                            _bl == b0.len(),
                            in_ > i0,
                            in_ <= b0.len(),
                        decreases b0.len() - in_,
                    {
                        self.line_inc();
                        in_ = in_ + 1;
                    }
                    continue;
                }
                break;
            }
            if self.bat(in_) == b'<' {
                self.chars_from_input(in_, true);
                return;
            }
            // get_more:
            loop
                invariant
                    self.wf(),
                    self.fuel == f0,
                    f0 <= old(self).fuel,
                    self.inputs@.len() == n0,
                    self.top().buf@ == b0,
                    _bl == b0.len(),
                decreases b0.len() - in_,
            {
                let ghost i0 = in_;
                let mut ccol = self.inp().col;
                while test_char_data(self.bat(in_))
                    invariant
                        self.wf(),
                        self.top().buf@ == b0,
                        _bl == b0.len(),
                        in_ >= i0,
                    decreases b0.len() - in_,
                {
                    in_ = in_ + 1;
                    ccol = sat_add_i32(ccol, 1);
                }
                let l = self.inp().line;
                self.set_pos(l, ccol);
                if self.bat(in_) == 0x0A {
                    self.line_inc();
                    in_ = in_ + 1;
                    while self.bat(in_) == 0x0A
                        invariant
                            self.wf(),
                            self.fuel == f0,
                            self.inputs@.len() == n0,
                            self.top().buf@ == b0,
                            _bl == b0.len(),
                            in_ > i0,
                            in_ <= b0.len(),
                        decreases b0.len() - in_,
                    {
                        self.line_inc();
                        in_ = in_ + 1;
                    }
                    continue;
                }
                if self.bat(in_) == b']' {
                    let avail = self.inp().buf.len().saturating_sub(in_);
                    if partial && avail < 2 {
                        terminate = true;
                        break;
                    }
                    if self.bat(in_ + 1) == b']' {
                        if partial && avail < 3 {
                            terminate = true;
                            break;
                        }
                        if self.bat(in_ + 2) == b'>' {
                            self.fatal(ERR_MISPLACED_CDATA_END, None);
                        }
                    }
                    in_ = in_ + 1;
                    self.col_inc();
                    continue;
                }
                break;
            }
            // invoke_callback:
            if in_ > self.inp().cur {
                self.chars_from_input(in_, false);
                line = self.inp().line;
                col = self.inp().col;
            }
            self.set_cur(in_);
            if self.bat(in_) == 0x0D && crate::lenient::at_off(&self.inp().buf, in_, 1) == 0x0A {
                in_ = in_ + 1;
                self.set_cur(in_);
                in_ = in_ + 1;
                self.line_inc();
                let c = self.bat(in_);
                if (0x20 <= c && c <= 0x7F) || c == 0x09 || c == 0x0A {
                    continue;
                }
                break;
            }
            let c = self.bat(in_);
            if c == b'<' || c == b'&' || terminate {
                return;
            }
            self.shrink();
            self.grow();
            in_ = self.inp().cur;
            let c = self.bat(in_);
            if !((0x20 <= c && c <= 0x7F) || c == 0x09 || c == 0x0A) {
                break;
            }
        }
        self.set_pos(line, col);
        self.parse_char_data_complex(partial);
    }

    /// `xmlParseCharDataComplex`.
    fn parse_char_data_complex(&mut self, partial: bool)
        requires
            old(self).wf(),
        ensures
            final(self).evolves(old(self)),
    {
        let mut buf: Vec<u8> = Vec::new();
        let r = self.current_char_recover();
        let mut cur = r.0;
        let mut l = r.1;
        while cur != 0x3C && cur != 0x26 && is_char(cur)
            invariant
                self.evolves(old(self)),
            decreases self.fuel,
        {
            if !self.step() {
                return;
            }
            if cur == 0x5D {
                let avail = self.avail();
                if partial && avail < 2 {
                    break;
                }
                if self.nxt(1) == b']' {
                    if partial && avail < 3 {
                        break;
                    }
                    if self.nxt(2) == b'>' {
                        self.fatal(ERR_MISPLACED_CDATA_END, None);
                    }
                }
            }
            push_char(&mut buf, cur);
            self.nextl(l);
            if buf.len() >= PARSER_BIG_BUFFER_SIZE {
                let mut s: Vec<u8> = Vec::new();
                std::mem::swap(&mut s, &mut buf);
                self.characters(&s, false);
                self.shrink();
            }
            let r = self.current_char_recover();
            cur = r.0;
            l = r.1;
        }
        if buf.len() > 0 {
            self.characters(&buf, false);
        }
        if !self.at_end() {
            let c = self.cur();
            if cur == 0 && c != 0 {
                if !partial {
                    let m = cat(&[b"Incomplete UTF-8 sequence starting with ", hex2(c).as_slice(), b"\n"]);
                    self.fatal_int(ERR_INVALID_CHAR, &m, c as i32);
                    self.nextl(1);
                }
            } else if cur != 0x3C && cur != 0x26 && cur != 0x5D {
                let m = cat(&[b"PCDATA invalid Char value ", itoa(cur as i64).as_slice(), b"\n"]);
                self.fatal_int(ERR_INVALID_CHAR, &m, cur as i32);
                self.nextl(l);
            }
        }
    }

    // --- SAX1 tags ---

    fn xml_space_value(&mut self, val: &[u8])
        requires
            old(self).wf(),
        ensures
            final(self).inputs == old(self).inputs,
            final(self).fuel == old(self).fuel,
            final(self).names == old(self).names,
            final(self).nsdb == old(self).nsdb,
    {
        if crate::lenient::bytes_eq(val, b"default") {
            self.set_space(0);
        } else if crate::lenient::bytes_eq(val, b"preserve") {
            self.set_space(1);
        } else {
            let m = cat(&[b"Invalid value \"", val, b"\" for xml:space : \"default\" or \"preserve\" expected\n"]);
            self.warning(WAR_SPACE_VALUE, &m, Some(val), None);
        }
    }

    fn lang_value(&mut self, val: &[u8])
        requires
            old(self).wf(),
        ensures
            final(self).only_sink(old(self)),
    {
        if !check_language_id(val) {
            let m = cat(&[b"Malformed value for xml:lang : ", val, b"\n"]);
            self.warning(WAR_LANG_VALUE, &m, Some(val), None);
        }
    }

    /// `xmlParseAttribute` (SAX1): the name, and the value when it parsed.
    fn parse_attribute(&mut self) -> Option<(Vec<u8>, Option<Vec<u8>>)>
        requires
            old(self).wf(),
        ensures
            final(self).evolves(old(self)),
    {
        self.grow();
        let name = match self.parse_name() {
            None => {
                self.fatal_msg(ERR_NAME_REQUIRED, b"error parsing attribute name\n");
                return None;
            }
            Some(n) => n,
        };
        self.skip_blanks();
        if self.cur() != b'=' {
            let m = cat(&[b"Specification mandates value for attribute ", name.as_slice(), b"\n"]);
            self.fatal_str(ERR_ATTRIBUTE_WITHOUT_VALUE, &m, Some(name.as_slice()));
            return Some((name, None));
        }
        self.next();
        self.skip_blanks();
        let val = self.parse_att_value();
        if self.options & PARSE_PEDANTIC != 0 && crate::lenient::bytes_eq(&name, b"xml:lang") {
            match &val {
                Some(v) => self.lang_value(v),
                None => self.lang_value(b""),
            }
        }
        if crate::lenient::bytes_eq(&name, b"xml:space") {
            match &val {
                Some(v) => self.xml_space_value(v),
                None => self.xml_space_value(b""),
            }
        }
        Some((name, val))
    }

    /// `xmlParseStartTag` (SAX1).
    fn parse_start_tag(&mut self) -> Option<Vec<u8>>
        requires
            old(self).wf(),
        ensures
            final(self).evolves(old(self)),
    {
        if self.cur() != b'<' {
            return None;
        }
        self.next1();
        let name = match self.parse_name() {
            None => {
                self.fatal_msg(ERR_NAME_REQUIRED, b"xmlParseStartTag: invalid element name\n");
                return None;
            }
            Some(n) => n,
        };
        self.skip_blanks();
        self.grow();
        let mut atts: Vec<(Vec<u8>, Vec<u8>)> = Vec::new();
        while self.cur() != b'>' && (self.cur() != b'/' || self.nxt(1) != b'>') && is_byte_char(self.cur()) && !self.stopped()
            invariant
                self.evolves(old(self)),
            decreases self.fuel,
        {
            if !self.step() {
                break;
            }
            let (attname, attvalue) = match self.parse_attribute() {
                None => break,
                Some(a) => a,
            };
            match attvalue {
                None => {}
                Some(v) => {
                    let mut dup = false;
                    let mut i: usize = 0;
                    let ghost f1 = self.fuel;
                    while i < atts.len()
                        invariant
                            self.wf(),
                            self.fuel == f1,
                        decreases atts@.len() - i,
                    {
                        if crate::lenient::bytes_eq(atts[i].0.as_slice(), attname.as_slice()) {
                            self.err_attribute_dup(None, &attname);
                            dup = true;
                            break;
                        }
                        i = i + 1;
                    }
                    if !dup {
                        let nbatts = atts.len().saturating_mul(2);
                        let mut ok = true;
                        if nbatts.saturating_add(4) > self.maxatts {
                            match grow_capacity_min(self.maxatts, 11, MAX_ATTRS) {
                                None => {
                                    self.sink.mem_error();
                                    ok = false;
                                }
                                Some(n) => self.maxatts = n.saturating_mul(2),
                            }
                        }
                        if ok {
                            atts.push((attname, v));
                        }
                    }
                }
            }
            self.grow();
            if self.cur() == b'>' || (self.cur() == b'/' && self.nxt(1) == b'>') {
                break;
            }
            if self.skip_blanks() == 0 {
                self.fatal_msg(ERR_SPACE_REQUIRED, b"attributes construct error\n");
            }
            self.shrink();
            self.grow();
        }
        if self.sax_on() {
            self.sync();
            let mut v: Vec<(&[u8], Option<&[u8]>)> = Vec::new();
            let mut i: usize = 0;
            while i < atts.len()
                decreases atts@.len() - i,
            {
                v.push((atts[i].0.as_slice(), Some(atts[i].1.as_slice())));
                i = i + 1;
            }
            self.sink.start_element(&name, &v);
        }
        Some(name)
    }

    fn tag_mismatch(&mut self, line: i32, got: Option<Vec<u8>>)
        requires
            old(self).wf(),
        ensures
            final(self).only_sink(old(self)),
    {
        let name = match got {
            Some(n) => n,
            None => crate::lenient::vec_of(b"unparsable"),
        };
        let open = self.cur_name();
        let m = cat(&[b"Opening and ending tag mismatch: ", open.as_slice(), b" line ", itoa(line as i64).as_slice(), b" and ", name.as_slice(), b"\n"]);
        self.fatal_sis(ERR_TAG_NAME_MISMATCH, &m, Some(open.as_slice()), line, Some(name.as_slice()));
    }

    /// `xmlParseEndTag1`.
    fn parse_end_tag1(&mut self, line: i32)
        requires
            old(self).wf(),
        ensures
            final(self).evolves(old(self)),
    {
        self.grow();
        if self.cur() != b'<' || self.nxt(1) != b'/' {
            self.fatal_msg(ERR_LTSLASH_REQUIRED, b"xmlParseEndTag: '</' not found\n");
            return;
        }
        self.skip(2);
        let open = self.cur_name();
        let r = self.parse_name_and_compare(&open);
        self.grow();
        self.skip_blanks();
        if !is_byte_char(self.cur()) || self.cur() != b'>' {
            self.fatal(ERR_GT_REQUIRED, None);
        } else {
            self.next1();
        }
        match r {
            Err(got) => self.tag_mismatch(line, got),
            Ok(()) => {}
        }
        if self.sax_on() {
            self.sync();
            self.sink.end_element(&open);
        }
        self.name_pop();
        self.space_pop();
    }

    // --- SAX2 tags ---

    /// `xmlParseQNameHashed`: (local name, prefix).
    fn parse_qname(&mut self) -> (Option<Vec<u8>>, Option<Vec<u8>>)
        requires
            old(self).wf(),
        ensures
            final(self).advances(old(self)),
    {
        self.grow();
        let start = self.inp().cur;
        let mut p: Option<Vec<u8>> = None;
        let mut is_ncname = false;
        let mut l = self.parse_ncname();
        if l.is_some() {
            is_ncname = true;
            if self.cur() == b':' {
                self.next();
                p = l;
                l = self.parse_ncname();
            }
        }
        if l.is_none() || self.cur() == b':' {
            if !is_ncname && self.cur() != b':' {
                return (None, None);
            }
            let _ = self.parse_nmtoken();
            let end = self.inp().cur;
            let name = self.slice(start, end);
            let m = cat(&[b"Failed to parse QName '", name.as_slice(), b"'\n"]);
            self.ns_err(NS_ERR_QNAME, &m, Some(name.as_slice()), None, None);
            return (Some(name), None);
        }
        (l, p)
    }

    /// `xmlParseQNameAndCompare`.
    fn parse_qname_and_compare(&mut self, name: &[u8], prefix: &[u8]) -> Result<(), Option<Vec<u8>>>
        requires
            old(self).wf(),
        ensures
            final(self).advances(old(self)),
    {
        self.grow();
        let _bl = self.inp().buf.len();
        let mut in_ = self.inp().cur;
        let mut k: usize = 0;
        while self.bat(in_) != 0 && k < prefix.len() && self.bat(in_) == prefix[k]
            invariant
                self.wf(),
                _bl == self.top().buf@.len(),
            decreases prefix@.len() - k,
        {
            in_ = in_ + 1;
            k = k + 1;
        }
        if k == prefix.len() && self.bat(in_) == b':' {
            in_ = in_ + 1;
            let mut k: usize = 0;
            while self.bat(in_) != 0 && k < name.len() && self.bat(in_) == name[k]
                invariant
                    self.wf(),
                    _bl == self.top().buf@.len(),
                decreases name@.len() - k,
            {
                in_ = in_ + 1;
                k = k + 1;
            }
            if k == name.len() && (self.bat(in_) == b'>' || blank(self.bat(in_))) {
                let i = self.inp_mut();
                let d = in_.saturating_sub(i.cur);
                let d32: i32 = if d > i32::MAX as usize { i32::MAX } else { d as i32 };
                i.col = sat_add_i32(i.col, d32);
                i.cur = in_;
                return Ok(());
            }
        }
        let (ret, prefix2) = self.parse_qname();
        match ret {
            None => Err(None),
            Some(r) => {
                let same_prefix = match &prefix2 {
                    Some(p) => crate::lenient::bytes_eq(p, prefix),
                    None => false,
                };
                if crate::lenient::bytes_eq(&r, name) && same_prefix {
                    Ok(())
                } else {
                    Err(Some(r))
                }
            }
        }
    }

    /// `xmlParseAttribute2`: None when no name parsed, else the name,
    /// prefix and (when it parsed) the value.
    fn parse_attribute2(&mut self, pref: Option<&[u8]>, elem: &[u8]) -> Option<(Vec<u8>, Option<Vec<u8>>, Option<Vec<u8>>)>
        requires
            old(self).wf(),
        ensures
            final(self).evolves(old(self)),
            final(self).inputs@.len() == old(self).inputs@.len(),
            final(self).names == old(self).names,
            final(self).nsdb == old(self).nsdb,
    {
        self.grow();
        let (name, prefix) = self.parse_qname();
        let name = match name {
            None => {
                self.fatal_msg(ERR_NAME_REQUIRED, b"error parsing attribute name\n");
                return None;
            }
            Some(n) => n,
        };
        let mut special = 0;
        if self.atts_special.len() > 0 {
            let fe = match pref {
                Some(p) => cat(&[p, b":", elem]),
                None => crate::lenient::vec_of(elem),
            };
            let fa = match &prefix {
                Some(p) => cat(&[p.as_slice(), b":", name.as_slice()]),
                None => name.clone(),
            };
            special = match self.special_lookup(&fe, &fa) {
                Some(t) => t,
                None => 0,
            };
        }
        self.skip_blanks();
        if self.cur() != b'=' {
            let m = cat(&[b"Specification mandates value for attribute ", name.as_slice(), b"\n"]);
            self.fatal_str(ERR_ATTRIBUTE_WITHOUT_VALUE, &m, Some(name.as_slice()));
            return Some((name, prefix, None));
        }
        self.next();
        self.skip_blanks();
        let is_xmlns_prefix = match &prefix {
            Some(p) => crate::lenient::bytes_eq(p, b"xmlns"),
            None => false,
        };
        let is_ns = (prefix.is_none() && crate::lenient::bytes_eq(&name, b"xmlns")) || is_xmlns_prefix;
        let (val, flags) = match self.parse_att_value_internal(special, is_ns) {
            None => return Some((name, prefix, None)),
            Some(v) => v,
        };
        if self.sink.validate() && self.sink.standalone() == 1 && special & SPECIAL_EXTERNAL != 0 && flags & ATTVAL_NORM_CHANGE != 0 {
            let m = cat(&[b"standalone: normalization of attribute ", name.as_slice(), b" on ", elem, b" by external subset declaration\n"]);
            self.validity_error(DTD_NOT_STANDALONE, &m, Some(name.as_slice()), Some(elem));
        }
        let is_xml_prefix = match &prefix {
            Some(p) => crate::lenient::bytes_eq(p, b"xml"),
            None => false,
        };
        if is_xml_prefix {
            if self.options & PARSE_PEDANTIC != 0 && crate::lenient::bytes_eq(&name, b"lang") {
                self.lang_value(&val);
            }
            if crate::lenient::bytes_eq(&name, b"space") {
                self.xml_space_value(&val);
            }
        }
        Some((name, prefix, Some(val)))
    }

    /// `xmlCtxtGrowAttrs`, on the count only.
    fn grow_attrs(&mut self) -> bool
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).inputs == old(self).inputs,
            final(self).fuel == old(self).fuel,
            final(self).names == old(self).names,
            final(self).nsdb == old(self).nsdb,
    {
        match grow_capacity_min(self.maxatts / 5, 10, MAX_ATTRS) {
            None => {
                self.fatal(ERR_RESOURCE_LIMIT, Some(b"Maximum number of attributes exceeded"));
                false
            }
            Some(n) => {
                self.maxatts = n.saturating_mul(5);
                true
            }
        }
    }

    fn ns_uri_of(&self, ns: NsIdx) -> Option<Vec<u8>> {
        match ns {
            NsIdx::Empty => None,
            NsIdx::Xml => Some(crate::lenient::vec_of(xml_ns())),
            NsIdx::At(i) => if i < self.nsdb.tab.len() { Some(self.nsdb.tab[i].uri.clone()) } else { None },
        }
    }

    fn check_ns_uri(&mut self, uri: &[u8], attname: Option<&[u8]>, pedantic_only: bool)
        requires
            old(self).wf(),
        ensures
            final(self).only_sink(old(self)),
    {
        let (valid, has_scheme) = self.sink.uri_check(uri);
        match attname {
            None => {
                if !valid {
                    let m = cat(&[b"xmlns: '", uri, b"' is not a valid URI\n"]);
                    self.ns_err(WAR_NS_URI, &m, Some(uri), None, None);
                } else if !has_scheme {
                    let m = cat(&[b"xmlns: URI ", uri, b" is not absolute\n"]);
                    self.ns_warn(WAR_NS_URI_RELATIVE, &m, Some(uri), None, None);
                }
            }
            Some(a) => {
                if !valid {
                    let m = cat(&[b"xmlns:", a, b": '", uri, b"' is not a valid URI\n"]);
                    self.ns_err(WAR_NS_URI, &m, Some(a), Some(uri), None);
                } else if pedantic_only && self.options & PARSE_PEDANTIC != 0 && !has_scheme {
                    let m = cat(&[b"xmlns:", a, b": URI ", uri, b" is not absolute\n"]);
                    self.ns_warn(WAR_NS_URI_RELATIVE, &m, Some(a), Some(uri), None);
                }
            }
        }
    }

    /// `xmlParseStartTag2`: the local name, prefix, URI and the number of
    /// namespaces pushed.
    fn parse_start_tag2(&mut self) -> Option<(Vec<u8>, Option<Vec<u8>>, Option<Vec<u8>>, usize)>
        requires
            old(self).wf(),
        ensures
            final(self).evolves(old(self)),
            final(self).names == old(self).names,
    {
        if self.cur() != b'<' {
            return None;
        }
        self.next1();
        let mut nb_ns: usize = 0;
        let mut nb_total_def: usize = 0;
        let mut nbdef: usize = 0;
        if !self.nsdb.start_element() {
            self.sink.mem_error();
            return None;
        }
        let (local, prefix) = self.parse_qname();
        let local = match local {
            None => {
                self.fatal_msg(ERR_NAME_REQUIRED, b"StartTag: invalid element name\n");
                return None;
            }
            Some(l) => l,
        };
        self.skip_blanks();
        self.grow();
        let mut atts: Vec<Att> = Vec::new();
        while self.cur() != b'>' && (self.cur() != b'/' || self.nxt(1) != b'>') && is_byte_char(self.cur()) && !self.stopped()
            invariant
                self.evolves(old(self)),
                self.names == old(self).names,
            decreases self.fuel,
        {
            if !self.step() {
                break;
            }
            let (attname, aprefix, attvalue) = match self.parse_attribute2(opt_slice(&prefix), &local) {
                None => break,
                Some(a) => a,
            };
            match attvalue {
                None => {}
                Some(v) => {
                    if crate::lenient::bytes_eq(&attname, b"xmlns") && aprefix.is_none() {
                        let uri = v;
                        let mut push = true;
                        if uri.len() > 0 {
                            self.check_ns_uri(&uri, None, false);
                            if crate::lenient::bytes_eq(&uri, xml_ns()) {
                                // attname is "xmlns" here, never "xml".
                                self.ns_err(NS_ERR_XML_NAMESPACE, b"xml namespace URI cannot be the default namespace\n", None, None, None);
                                push = false;
                            } else if crate::lenient::bytes_eq(&uri, xmlns_ns()) {
                                self.ns_err(NS_ERR_XML_NAMESPACE, b"reuse of the xmlns namespace name is forbidden\n", None, None, None);
                                push = false;
                            }
                        }
                        if push && self.ns_push(None, &uri, false) > 0 {
                            nb_ns = nb_ns.saturating_add(1);
                        }
                    } else if opt_is(&aprefix, b"xmlns") {
                        let uri = v;
                        let push = if crate::lenient::bytes_eq(&attname, b"xml") {
                            if !crate::lenient::bytes_eq(&uri, xml_ns()) {
                                self.ns_err(NS_ERR_XML_NAMESPACE, b"xml namespace prefix mapped to wrong URI\n", None, None, None);
                            }
                            false
                        } else if crate::lenient::bytes_eq(&uri, xml_ns()) {
                            self.ns_err(NS_ERR_XML_NAMESPACE, b"xml namespace URI mapped to wrong prefix\n", None, None, None);
                            false
                        } else if crate::lenient::bytes_eq(&attname, b"xmlns") {
                            self.ns_err(NS_ERR_XML_NAMESPACE, b"redefinition of the xmlns prefix is forbidden\n", None, None, None);
                            false
                        } else if crate::lenient::bytes_eq(&uri, xmlns_ns()) {
                            self.ns_err(NS_ERR_XML_NAMESPACE, b"reuse of the xmlns namespace name is forbidden\n", None, None, None);
                            false
                        } else if uri.len() == 0 {
                            let m = cat(&[b"xmlns:", attname.as_slice(), b": Empty XML namespace is not allowed\n"]);
                            self.ns_err(NS_ERR_XML_NAMESPACE, &m, Some(attname.as_slice()), None, None);
                            false
                        } else {
                            self.check_ns_uri(&uri, Some(attname.as_slice()), true);
                            true
                        };
                        if push && self.ns_push(Some(attname.as_slice()), &uri, false) > 0 {
                            nb_ns = nb_ns.saturating_add(1);
                        }
                    } else {
                        let ok = if atts.len().saturating_mul(5).saturating_add(5) > self.maxatts { self.grow_attrs() } else { true };
                        if ok {
                            atts.push(Att { name: attname, prefix: aprefix, ns: NsIdx::Empty, value: v });
                        }
                    }
                }
            }
            self.grow();
            if self.cur() == b'>' || (self.cur() == b'/' && self.nxt(1) == b'>') {
                break;
            }
            if self.skip_blanks() == 0 {
                self.fatal_msg(ERR_SPACE_REQUIRED, b"attributes construct error\n");
                break;
            }
            self.grow();
        }
        let nratts = atts.len();

        // Namespaces from the default attributes.
        let mut defaults: Vec<DefAttr> = Vec::new();
        {
            let mut k: usize = 0;
            while k < self.atts_default.len()
                decreases self.atts_default@.len() - k,
            {
                let e = &self.atts_default[k];
                if crate::lenient::bytes_eq(e.0.0.as_slice(), local.as_slice()) && crate::lenient::opt_eq(opt_slice(&e.0.1), opt_slice(&prefix)) {
                    defaults = clone_defaults(&e.1);
                    break;
                }
                k = k + 1;
            }
        }
        let ghost f1 = self.fuel;
        let mut di: usize = 0;
        while di < defaults.len()
            invariant
                self.wf(),
                self.fuel == f1,
                f1 <= old(self).fuel,
                self.names == old(self).names,
            decreases defaults@.len() - di,
        {
            let d = &defaults[di];
            if crate::lenient::bytes_eq(&d.name, b"xmlns") && d.prefix.is_none() {
                self.entity_check(d.expanded_size);
                if self.ns_push(None, &d.value, true) > 0 {
                    nb_ns = nb_ns.saturating_add(1);
                }
            } else if opt_is(&d.prefix, b"xmlns") {
                self.entity_check(d.expanded_size);
                if self.ns_push(Some(d.name.as_slice()), &d.value, true) > 0 {
                    nb_ns = nb_ns.saturating_add(1);
                }
            } else {
                if nratts.saturating_add(nb_total_def) >= MAX_ATTRS {
                    self.fatal(ERR_RESOURCE_LIMIT, Some(b"Maximum number of attributes exceeded"));
                    break;
                }
                nb_total_def = nb_total_def + 1;
            }
            di = di + 1;
        }

        // Resolve the attributes' prefixes.
        let mut i: usize = 0;
        while i < atts.len()
            invariant
                self.wf(),
                self.fuel == f1,
                f1 <= old(self).fuel,
                self.names == old(self).names,
                atts@.len() == nratts,
            decreases atts@.len() - i,
        {
            let ns = match &atts[i].prefix {
                None => NsIdx::Empty,
                Some(p) => if crate::lenient::bytes_eq(p, b"xml") {
                    NsIdx::Xml
                } else {
                    let k = self.nsdb.lookup(Some(p.as_slice()));
                    if k == nsdb::NONE || k < self.nsdb.min {
                        let p = p.clone();
                        let a = atts[i].name.clone();
                        let m = cat(&[b"Namespace prefix ", p.as_slice(), b" for ", a.as_slice(), b" on ", local.as_slice(), b" is not defined\n"]);
                        self.ns_err(NS_ERR_UNDEFINED_NAMESPACE, &m, Some(p.as_slice()), Some(a.as_slice()), Some(local.as_slice()));
                        NsIdx::Empty
                    } else {
                        NsIdx::At(k)
                    }
                },
            };
            atts[i].ns = ns;
            i = i + 1;
        }

        // Duplicates: the entries of the attribute hash, by index.
        let max_atts = nratts.saturating_add(nb_total_def);
        let mut table: Vec<usize> = Vec::new();
        let mut num_dup: usize = 0;
        let mut num_ns: usize = 0;
        if max_atts > 1 {
            let mut j: usize = 0;
            while j < nratts
                invariant
                    self.wf(),
                    self.fuel == f1,
                    f1 <= old(self).fuel,
                    self.names == old(self).names,
                    atts@.len() == nratts,
                    forall|t: int| 0 <= t < table@.len() ==> table@[t] < atts@.len(),
                decreases nratts - j,
            {
                if atts[j].ns == NsIdx::Empty && atts[j].prefix.is_some() {
                    j = j + 1;
                    continue;
                }
                let uri = self.ns_uri_of(atts[j].ns);
                let mut res: Option<usize> = None;
                let mut t: usize = 0;
                while t < table.len()
                    invariant
                        forall|t: int| 0 <= t < table@.len() ==> table@[t] < atts@.len(),
                        res matches Some(e) ==> e < atts@.len(),
                        j < atts@.len(),
                    decreases table@.len() - t,
                {
                    let e = table[t];
                    if crate::lenient::bytes_eq(&atts[e].name, &atts[j].name) && opt_vec_eq(&self.ns_uri_of(atts[e].ns), &uri) {
                        res = Some(e);
                        break;
                    }
                    t = t + 1;
                }
                match res {
                    None => table.push(j),
                    Some(e) => {
                        if opt_vec_eq(&atts[e].prefix, &atts[j].prefix) {
                            let p = atts[j].prefix.clone();
                            let n = atts[j].name.clone();
                            self.err_attribute_dup(opt_slice(&p), &n);
                            num_dup = num_dup.saturating_add(1);
                        } else {
                            let n = atts[j].name.clone();
                            let u = match &uri {
                                Some(u) => u.clone(),
                                None => Vec::new(),
                            };
                            let m = cat(&[b"Namespaced Attribute ", n.as_slice(), b" in '", u.as_slice(), b"' redefined\n"]);
                            self.ns_err(NS_ERR_ATTRIBUTE_REDEFINED, &m, Some(n.as_slice()), opt_slice(&uri), None);
                            num_ns = num_ns.saturating_add(1);
                        }
                    }
                }
                j = j + 1;
            }
        }

        // The default attributes themselves.
        let mut di: usize = 0;
        while di < defaults.len()
            invariant
                self.wf(),
                self.fuel == f1,
                f1 <= old(self).fuel,
                self.names == old(self).names,
                nratts <= atts@.len(),
                forall|t: int| 0 <= t < table@.len() ==> table@[t] < atts@.len(),
            decreases defaults@.len() - di,
        {
            let d = &defaults[di];
            di = di + 1;
            if crate::lenient::bytes_eq(&d.name, b"xmlns") && d.prefix.is_none() {
                continue;
            }
            if opt_is(&d.prefix, b"xmlns") {
                continue;
            }
            let ns = match &d.prefix {
                None => NsIdx::Empty,
                Some(p) => if crate::lenient::bytes_eq(p, b"xml") {
                    NsIdx::Xml
                } else {
                    let k = self.nsdb.lookup(Some(p.as_slice()));
                    if k == nsdb::NONE || k < self.nsdb.min {
                        let m = cat(&[b"Namespace prefix ", p.as_slice(), b" for ", d.name.as_slice(), b" on ", local.as_slice(), b" is not defined\n"]);
                        self.ns_err(NS_ERR_UNDEFINED_NAMESPACE, &m, Some(p.as_slice()), Some(d.name.as_slice()), Some(local.as_slice()));
                        NsIdx::Empty
                    } else {
                        NsIdx::At(k)
                    }
                },
            };
            let mut fresh = false;
            if max_atts > 1 {
                let uri = self.ns_uri_of(ns);
                let mut res: Option<usize> = None;
                let mut t: usize = 0;
                while t < table.len()
                    invariant
                        forall|t: int| 0 <= t < table@.len() ==> table@[t] < atts@.len(),
                        res matches Some(e) ==> e < atts@.len(),
                    decreases table@.len() - t,
                {
                    let e = table[t];
                    if crate::lenient::bytes_eq(&atts[e].name, &d.name) && opt_vec_eq(&self.ns_uri_of(atts[e].ns), &uri) {
                        res = Some(e);
                        break;
                    }
                    t = t + 1;
                }
                match res {
                    None => fresh = true,
                    Some(e) => {
                        if opt_vec_eq(&atts[e].prefix, &d.prefix) {
                            continue;
                        }
                        let u = match &uri {
                            Some(u) => u.clone(),
                            None => Vec::new(),
                        };
                        let m = cat(&[b"Namespaced Attribute ", d.name.as_slice(), b" in '", u.as_slice(), b"' redefined\n"]);
                        self.ns_err(NS_ERR_ATTRIBUTE_REDEFINED, &m, Some(d.name.as_slice()), opt_slice(&uri), None);
                    }
                }
            }
            self.entity_check(d.expanded_size);
            if atts.len().saturating_mul(5).saturating_add(5) > self.maxatts && !self.grow_attrs() {
                // libxml2 returns no element here (`localname = NULL`).
                return None;
            }
            if self.sink.validate() && self.sink.standalone() == 1 && d.external {
                let m = cat(&[b"standalone: attribute ", d.name.as_slice(), b" on ", local.as_slice(), b" defaulted from external subset\n"]);
                self.validity_error(DTD_STANDALONE_DEFAULTED, &m, Some(d.name.as_slice()), Some(local.as_slice()));
            }
            // The hash entry for a new name is the attribute added here.
            if fresh {
                table.push(atts.len());
            }
            atts.push(Att { name: d.name.clone(), prefix: d.prefix.clone(), ns, value: d.value.clone() });
            nbdef = nbdef.saturating_add(1);
        }

        // Duplicate QNames, when the namespace check reported several.
        if num_dup == 0 && num_ns > 1 {
            let mut seen: Vec<usize> = Vec::new();
            let mut j: usize = 0;
            while j < nratts
                invariant
                    self.wf(),
                    self.fuel == f1,
                    f1 <= old(self).fuel,
                    self.names == old(self).names,
                    nratts <= atts@.len(),
                    forall|t: int| 0 <= t < seen@.len() ==> seen@[t] < atts@.len(),
                decreases nratts - j,
            {
                if atts[j].prefix.is_some() {
                    let mut found = false;
                    let mut t: usize = 0;
                    while t < seen.len()
                        invariant
                            forall|t: int| 0 <= t < seen@.len() ==> seen@[t] < atts@.len(),
                            j < atts@.len(),
                        decreases seen@.len() - t,
                    {
                        let e = seen[t];
                        if crate::lenient::bytes_eq(&atts[e].name, &atts[j].name) && opt_vec_eq(&atts[e].prefix, &atts[j].prefix) {
                            found = true;
                            break;
                        }
                        t = t + 1;
                    }
                    if found {
                        let p = atts[j].prefix.clone();
                        let n = atts[j].name.clone();
                        self.err_attribute_dup(opt_slice(&p), &n);
                    } else {
                        seen.push(j);
                    }
                }
                j = j + 1;
            }
        }

        let uri = self.ns_lookup_uri(opt_slice(&prefix));
        match &prefix {
            None => {}
            Some(p) => {
                if uri.is_none() {
                    let m = cat(&[b"Namespace prefix ", p.as_slice(), b" on ", local.as_slice(), b" is not defined\n"]);
                    self.ns_err(NS_ERR_UNDEFINED_NAMESPACE, &m, Some(p.as_slice()), Some(local.as_slice()), None);
                }
            }
        }
        if self.sax_on() {
            let mut uris: Vec<Option<Vec<u8>>> = Vec::new();
            let mut k: usize = 0;
            while k < atts.len()
                invariant
                    uris@.len() == k,
                    k <= atts@.len(),
                decreases atts@.len() - k,
            {
                uris.push(self.ns_uri_of(atts[k].ns));
                k = k + 1;
            }
            let n = self.nsdb.tab.len();
            let first = n - if nb_ns <= n { nb_ns } else { n };
            let mut nss: Vec<(Option<Vec<u8>>, Vec<u8>)> = Vec::new();
            let mut k = first;
            while k < n
                invariant
                    n == self.nsdb.tab@.len(),
                decreases n - k,
            {
                let e = &self.nsdb.tab[k];
                nss.push((e.prefix.clone(), e.uri.clone()));
                k = k + 1;
            }
            self.sync();
            let mut nsv: Vec<(Option<&[u8]>, &[u8])> = Vec::new();
            let mut k: usize = 0;
            while k < nss.len()
                decreases nss@.len() - k,
            {
                nsv.push((opt_slice(&nss[k].0), nss[k].1.as_slice()));
                k = k + 1;
            }
            let mut av: Vec<NsAttr<'_>> = Vec::new();
            let mut k: usize = 0;
            while k < atts.len()
                invariant
                    uris@.len() == atts@.len(),
                decreases atts@.len() - k,
            {
                av.push(NsAttr { local: atts[k].name.as_slice(), prefix: opt_slice(&atts[k].prefix), uri: opt_slice(&uris[k]), value: atts[k].value.as_slice() });
                k = k + 1;
            }
            self.sink.start_element_ns(&local, opt_slice(&prefix), opt_slice(&uri), &nsv, &av, nbdef);
        }
        Some((local, prefix, uri, nb_ns))
    }

    /// `xmlParseEndTag2` for the element on top of the name stack.
    fn parse_end_tag2(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).evolves(old(self)),
            final(self).names == old(self).names,
    {
        let nn = self.names.len();
        if nn == 0 {
            return;
        }
        let tag = clone_name(&self.names[nn - 1]);
        self.grow();
        if self.cur() != b'<' || self.nxt(1) != b'/' {
            self.fatal(ERR_LTSLASH_REQUIRED, None);
            return;
        }
        self.skip(2);
        let r = match &tag.prefix {
            None => self.parse_name_and_compare(&tag.name),
            Some(p) => self.parse_qname_and_compare(&tag.name, p),
        };
        self.grow();
        self.skip_blanks();
        if !is_byte_char(self.cur()) || self.cur() != b'>' {
            self.fatal(ERR_GT_REQUIRED, None);
        } else {
            self.next1();
        }
        match r {
            Err(got) => self.tag_mismatch(tag.line, got),
            Ok(()) => {}
        }
        if self.sax_on() {
            self.sync();
            self.sink.end_element_ns(&tag.name, opt_slice(&tag.prefix), opt_slice(&tag.uri));
        }
        self.space_pop();
        if tag.ns_nr != 0 {
            self.ns_pop(tag.ns_nr);
        }
    }

    /// `xmlParseCDSect`.
    pub fn parse_cdsect(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).advances(old(self)),
    {
        let max = if self.options & PARSE_HUGE != 0 { MAX_HUGE_LENGTH } else { MAX_TEXT_LENGTH };
        if self.cur() != b'<' || self.nxt(1) != b'!' || self.nxt(2) != b'[' {
            return;
        }
        self.skip(3);
        if !self.cmp(b"CDATA[") {
            return;
        }
        self.skip(6);
        let c0 = self.current_char_recover();
        let mut r = c0.0;
        if !is_char(r) {
            self.fatal(ERR_CDATA_NOT_FINISHED, None);
            return;
        }
        self.nextl(c0.1);
        let c1 = self.current_char_recover();
        let mut s = c1.0;
        if !is_char(s) {
            self.fatal(ERR_CDATA_NOT_FINISHED, None);
            return;
        }
        self.nextl(c1.1);
        let c2 = self.current_char_recover();
        let mut cur = c2.0;
        let mut l = c2.1;
        let mut buf: Vec<u8> = Vec::new();
        let mut size = PARSER_BUFFER_SIZE;
        while is_char(cur) && (r != 0x5D || s != 0x5D || cur != 0x3E)
            invariant
                self.advances(old(self)),
            decreases self.fuel,
        {
            if !self.step() {
                return;
            }
            if buf.len().saturating_add(5) >= size {
                match grow_capacity_min(size, 1, max) {
                    None => {
                        self.fatal_msg(ERR_CDATA_NOT_FINISHED, b"CData section too big found\n");
                        return;
                    }
                    Some(n) => size = n,
                }
            }
            push_char(&mut buf, r);
            r = s;
            s = cur;
            self.nextl(l);
            let c = self.current_char_recover();
            cur = c.0;
            l = c.1;
        }
        if cur != 0x3E {
            let m = cat(&[b"CData section not finished\n", crate::lenient::prefix_n(&buf, 50), b"\n"]);
            self.fatal_str(ERR_CDATA_NOT_FINISHED, &m, Some(buf.as_slice()));
            return;
        }
        self.nextl(l);
        if self.sax_on() {
            self.sync();
            if self.sink.has_cdata_block() && self.options & PARSE_NOCDATA == 0 {
                self.sink.cdata_block(&buf);
            } else if self.sink.has_characters() {
                self.sink.characters(&buf);
            }
        }
    }

    /// `xmlParseContentInternal`.
    pub fn parse_content_internal(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).evolves(old(self)),
        decreases old(self).fuel, 0int,
    {
        let old_name_nr = self.names.len();
        let old_space_nr = self.space_nr;
        let old_node_nr = self.sink.node_nr();
        self.grow();
        while !self.at_end() && !self.stopped()
            invariant
                self.evolves(old(self)),
            decreases self.fuel,
        {
            if !self.step() {
                break;
            }
            let c = self.cur();
            if c == b'<' && self.nxt(1) == b'?' {
                self.parse_pi();
            } else if self.cmp(b"<![CDATA[") {
                self.parse_cdsect();
            } else if c == b'<' && self.nxt(1) == b'!' && self.nxt(2) == b'-' && self.nxt(3) == b'-' {
                self.parse_comment();
            } else if c == b'<' {
                if self.nxt(1) == b'/' {
                    if self.names.len() <= old_name_nr {
                        break;
                    }
                    self.parse_element_end();
                } else {
                    self.parse_element_start();
                }
            } else if c == b'&' {
                self.parse_reference();
            } else {
                self.parse_char_data_internal(false);
            }
            self.shrink();
            self.grow();
        }
        if self.names.len() > old_name_nr && self.at_end() && self.sink.well_formed() {
            self.premature_end();
        }
        // One `nodePop` per node the content left open.
        let mut k = self.sink.node_nr().saturating_sub(old_node_nr);
        while k > 0 && self.sink.node_nr() > old_node_nr
            invariant
                self.evolves(old(self)),
            decreases k,
        {
            self.sink.node_pop();
            k = k - 1;
        }
        while self.names.len() > old_name_nr
            invariant
                self.evolves(old(self)),
            decreases self.names@.len(),
        {
            let n = self.names.len();
            let ns_nr = self.names[n - 1].ns_nr;
            if ns_nr != 0 {
                self.ns_pop(ns_nr);
            }
            self.name_pop();
        }
        while self.space_nr > old_space_nr
            invariant
                self.evolves(old(self)),
            decreases self.space_nr,
        {
            self.space_pop();
        }
    }

    fn premature_end(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).only_sink(old(self)),
    {
        let nn = self.names.len();
        if nn == 0 {
            return;
        }
        let t = clone_name(&self.names[nn - 1]);
        let m = cat(&[b"Premature end of data in tag ", t.name.as_slice(), b" line ", itoa(t.line as i64).as_slice(), b"\n"]);
        self.fatal_sis(ERR_TAG_NOT_FINISHED, &m, Some(t.name.as_slice()), t.line, None);
    }

    /// `xmlParseElement`.
    pub fn parse_element(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).evolves(old(self)),
    {
        if self.parse_element_start() != 0 {
            return;
        }
        self.parse_content_internal();
        if self.at_end() {
            if self.sink.well_formed() {
                self.premature_end();
            }
            return;
        }
        self.parse_element_end();
    }

    /// `xmlParseElementStart`: 0 when content follows, 1 for an empty
    /// element, -1 on error.
    pub fn parse_element_start(&mut self) -> i32
        requires
            old(self).wf(),
        ensures
            final(self).evolves(old(self)),
    {
        let max_depth: usize = if self.options & PARSE_HUGE != 0 { 2048 } else { 256 };
        if self.names.len() > max_depth {
            let n = self.names.len() as i64;
            let m = cat(&[b"Excessive depth in document: ", itoa(n).as_slice(), b" use XML_PARSE_HUGE option\n"]);
            self.fatal_int(ERR_RESOURCE_LIMIT, &m, n as i32);
            return -1;
        }
        if self.space_nr == 0 || self.space() == -2 {
            self.space_push(-1);
        } else {
            let v = self.space();
            self.space_push(v);
        }
        let line = self.inp().line;
        let parsed = if self.sax2 {
            self.parse_start_tag2()
        } else {
            match self.parse_start_tag() {
                None => None,
                Some(n) => Some((n, None, None, 0)),
            }
        };
        let (name, prefix, uri, nb_ns) = match parsed {
            None => {
                self.space_pop();
                return -1;
            }
            Some(p) => p,
        };
        self.name_ns_push(name.clone(), prefix.clone(), uri.clone(), line, nb_ns);
        if self.sink.validate() && self.sink.well_formed() {
            self.sink.validate_root();
        }
        if self.cur() == b'/' && self.nxt(1) == b'>' {
            self.skip(2);
            if self.sax_on() {
                self.sync();
                if self.sax2 {
                    self.sink.end_element_ns(&name, opt_slice(&prefix), opt_slice(&uri));
                } else {
                    self.sink.end_element(&name);
                }
            }
            self.name_pop();
            self.space_pop();
            if nb_ns > 0 {
                self.ns_pop(nb_ns);
            }
            return 1;
        }
        if self.cur() == b'>' {
            self.next1();
        } else {
            let m = cat(&[b"Couldn't find end of Start Tag ", name.as_slice(), b" line ", itoa(line as i64).as_slice(), b"\n"]);
            self.fatal_sis(ERR_GT_REQUIRED, &m, Some(name.as_slice()), line, None);
            self.sink.node_pop();
            self.name_pop();
            self.space_pop();
            if nb_ns > 0 {
                self.ns_pop(nb_ns);
            }
            return -1;
        }
        0
    }

    /// `xmlParseElementEnd`.
    pub fn parse_element_end(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).evolves(old(self)),
    {
        if self.names.len() == 0 {
            if self.cur() == b'<' && self.nxt(1) == b'/' {
                self.skip(2);
            }
            return;
        }
        if self.sax2 {
            self.parse_end_tag2();
            self.name_pop();
        } else {
            self.parse_end_tag1(0);
        }
    }
}

} // verus!
