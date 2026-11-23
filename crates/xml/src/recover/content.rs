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

impl<S: Sink> Parser<S> {
    // --- the name and space stacks ---

    /// `nameNsPush`.
    #[verifier::external_body]
    pub fn name_ns_push(&mut self, name: Vec<u8>, prefix: Option<Vec<u8>>, uri: Option<Vec<u8>>, line: i32, ns_nr: usize) {
        self.names.push(NameEntry { name, prefix, uri, line, ns_nr });
    }

    /// `namePop`.
    #[verifier::external_body]
    pub fn name_pop(&mut self) {
        self.names.pop();
    }

    /// `ctxt->name`.
    #[verifier::external_body]
    pub fn cur_name(&self) -> Vec<u8> {
        match self.names.last() {
            Some(n) => n.name.clone(),
            None => Vec::new(),
        }
    }

    /// `spacePush`.
    #[verifier::external_body]
    pub fn space_push(&mut self, v: i32) {
        if self.space_nr < self.spaces.len() {
            self.spaces[self.space_nr] = v;
        } else {
            self.spaces.push(v);
        }
        self.space_nr += 1;
    }

    /// `spacePop`.
    #[verifier::external_body]
    pub fn space_pop(&mut self) {
        if self.space_nr == 0 {
            return;
        }
        self.space_nr -= 1;
        let n = self.space_nr;
        if n < self.spaces.len() {
            self.spaces[n] = -1;
        }
    }

    #[verifier::external_body]
    fn space_slot(&self) -> usize {
        if self.space_nr > 0 { self.space_nr - 1 } else { 0 }
    }

    /// `*ctxt->space`.
    #[verifier::external_body]
    pub fn space(&self) -> i32 {
        let k = self.space_slot();
        if k < self.spaces.len() { self.spaces[k] } else { -1 }
    }

    #[verifier::external_body]
    pub fn set_space(&mut self, v: i32) {
        let k = self.space_slot();
        if k < self.spaces.len() {
            self.spaces[k] = v;
        } else {
            self.spaces.push(v);
        }
    }

    // --- character data ---

    /// `areBlanks`.
    #[verifier::external_body]
    fn are_blanks(&mut self, s: &[u8], blank_chars: bool) -> bool {
        let sp = self.space();
        if sp == 1 || sp == -2 {
            return false;
        }
        if !blank_chars {
            let mut i = 0;
            while i < s.len() {
                if !blank(s[i]) {
                    return false;
                }
                i += 1;
            }
        }
        let next = [self.cur(), self.nxt(1)];
        self.sink.blanks_ignorable_in_tree(next)
    }

    /// `xmlCharacters`.
    #[verifier::external_body]
    pub fn characters(&mut self, s: &[u8], is_blank: bool) {
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

    #[verifier::external_body]
    fn chars_from_input(&mut self, in_: usize, is_blank: bool) {
        while in_ > self.inp().cur {
            let start = self.inp().cur;
            let mut n = in_ - start;
            if n > MAX_ITEMS {
                n = MAX_ITEMS;
            }
            self.inp_mut().cur = start + n;
            let s = self.slice(start, start + n);
            self.characters(&s, is_blank);
        }
    }

    /// `xmlParseCharDataInternal`.
    #[verifier::external_body]
    pub fn parse_char_data_internal(&mut self, partial: bool) {
        let mut line = self.inp().line;
        let mut col = self.inp().col;
        let mut terminate = false;
        self.grow();
        let b = |s: &Self, k: usize| at(&s.inp().buf, k);
        let mut in_ = self.inp().cur;
        loop {
            if !self.step() {
                return;
            }
            // get_more_space:
            loop {
                while b(self, in_) == 0x20 {
                    in_ += 1;
                    let i = self.inp_mut();
                    i.col = i.col.saturating_add(1);
                }
                if b(self, in_) == 0x0A {
                    while b(self, in_) == 0x0A {
                        let i = self.inp_mut();
                        i.line = i.line.saturating_add(1);
                        i.col = 1;
                        in_ += 1;
                    }
                    continue;
                }
                break;
            }
            if b(self, in_) == b'<' {
                self.chars_from_input(in_, true);
                return;
            }
            // get_more:
            loop {
                let mut ccol = self.inp().col;
                while test_char_data(b(self, in_)) {
                    in_ += 1;
                    ccol = ccol.saturating_add(1);
                }
                self.inp_mut().col = ccol;
                if b(self, in_) == 0x0A {
                    while b(self, in_) == 0x0A {
                        let i = self.inp_mut();
                        i.line = i.line.saturating_add(1);
                        i.col = 1;
                        in_ += 1;
                    }
                    continue;
                }
                if b(self, in_) == b']' {
                    let avail = self.inp().buf.len().saturating_sub(in_);
                    if partial && avail < 2 {
                        terminate = true;
                        break;
                    }
                    if b(self, in_ + 1) == b']' {
                        if partial && avail < 3 {
                            terminate = true;
                            break;
                        }
                        if b(self, in_ + 2) == b'>' {
                            self.fatal(ERR_MISPLACED_CDATA_END, None);
                        }
                    }
                    in_ += 1;
                    let i = self.inp_mut();
                    i.col = i.col.saturating_add(1);
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
            self.inp_mut().cur = in_;
            if b(self, in_) == 0x0D && b(self, in_ + 1) == 0x0A {
                in_ += 1;
                self.inp_mut().cur = in_;
                in_ += 1;
                let i = self.inp_mut();
                i.line = i.line.saturating_add(1);
                i.col = 1;
                let c = b(self, in_);
                if (0x20..=0x7F).contains(&c) || c == 0x09 || c == 0x0A {
                    continue;
                }
                break;
            }
            let c = b(self, in_);
            if c == b'<' || c == b'&' || terminate {
                return;
            }
            self.shrink();
            self.grow();
            in_ = self.inp().cur;
            let c = b(self, in_);
            if !((0x20..=0x7F).contains(&c) || c == 0x09 || c == 0x0A) {
                break;
            }
        }
        {
            let i = self.inp_mut();
            i.line = line;
            i.col = col;
        }
        self.parse_char_data_complex(partial);
    }

    /// `xmlParseCharDataComplex`.
    #[verifier::external_body]
    fn parse_char_data_complex(&mut self, partial: bool) {
        let mut buf: Vec<u8> = Vec::with_capacity(PARSER_BIG_BUFFER_SIZE + 5);
        let (mut cur, mut l) = self.current_char_recover();
        while cur != b'<' as u32 && cur != b'&' as u32 && is_char(cur) {
            if !self.step() {
                return;
            }
            if cur == b']' as u32 {
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
                let s = core::mem::take(&mut buf);
                self.characters(&s, false);
                self.shrink();
            }
            (cur, l) = self.current_char_recover();
        }
        if !buf.is_empty() {
            self.characters(&buf, false);
        }
        if !self.at_end() {
            let c = self.cur();
            if cur == 0 && c != 0 {
                if !partial {
                    let m = cat(&[b"Incomplete UTF-8 sequence starting with ", &hex2(c), b"\n"]);
                    self.fatal_int(ERR_INVALID_CHAR, &m, c as i32);
                    self.nextl(1);
                }
            } else if cur != b'<' as u32 && cur != b'&' as u32 && cur != b']' as u32 {
                let m = cat(&[b"PCDATA invalid Char value ", &itoa(cur as i64), b"\n"]);
                self.fatal_int(ERR_INVALID_CHAR, &m, cur as i32);
                self.nextl(l);
            }
        }
    }

    // --- SAX1 tags ---

    #[verifier::external_body]
    fn xml_space_value(&mut self, val: &[u8]) {
        if val == b"default" {
            self.set_space(0);
        } else if val == b"preserve" {
            self.set_space(1);
        } else {
            let m = cat(&[b"Invalid value \"", val, b"\" for xml:space : \"default\" or \"preserve\" expected\n"]);
            self.warning(WAR_SPACE_VALUE, &m, Some(val), None);
        }
    }

    #[verifier::external_body]
    fn lang_value(&mut self, val: &[u8]) {
        if !check_language_id(val) {
            let m = cat(&[b"Malformed value for xml:lang : ", val, b"\n"]);
            self.warning(WAR_LANG_VALUE, &m, Some(val), None);
        }
    }

    /// `xmlParseAttribute` (SAX1): the name, and the value when it parsed.
    #[verifier::external_body]
    fn parse_attribute(&mut self) -> Option<(Vec<u8>, Option<Vec<u8>>)> {
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
            let m = cat(&[b"Specification mandates value for attribute ", &name, b"\n"]);
            self.fatal_str(ERR_ATTRIBUTE_WITHOUT_VALUE, &m, Some(&name));
            return Some((name, None));
        }
        self.next();
        self.skip_blanks();
        let val = self.parse_att_value();
        if self.options & PARSE_PEDANTIC != 0 && name.as_slice() == b"xml:lang" {
            let v = val.clone().unwrap_or_default();
            self.lang_value(&v);
        }
        if name.as_slice() == b"xml:space" {
            let v = val.clone().unwrap_or_default();
            self.xml_space_value(&v);
        }
        Some((name, val))
    }

    /// `xmlParseStartTag` (SAX1).
    #[verifier::external_body]
    fn parse_start_tag(&mut self) -> Option<Vec<u8>> {
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
        while self.cur() != b'>' && (self.cur() != b'/' || self.nxt(1) != b'>') && is_byte_char(self.cur()) && !self.stopped() {
            if !self.step() {
                break;
            }
            let (attname, attvalue) = match self.parse_attribute() {
                None => break,
                Some(a) => a,
            };
            if let Some(v) = attvalue {
                let mut dup = false;
                let mut i = 0;
                while i < atts.len() {
                    if atts[i].0 == attname {
                        self.err_attribute_dup(None, &attname);
                        dup = true;
                        break;
                    }
                    i += 1;
                }
                if !dup {
                    let nbatts = atts.len() * 2;
                    let mut ok = true;
                    if nbatts + 4 > self.maxatts {
                        match grow_capacity_min(self.maxatts, 11, MAX_ATTRS) {
                            None => {
                                self.sink.mem_error();
                                ok = false;
                            }
                            Some(n) => self.maxatts = n * 2,
                        }
                    }
                    if ok {
                        atts.push((attname, v));
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
            let v: Vec<(&[u8], Option<&[u8]>)> = atts.iter().map(|(n, v)| (n.as_slice(), Some(v.as_slice()))).collect();
            self.sink.start_element(&name, &v);
        }
        Some(name)
    }

    #[verifier::external_body]
    fn tag_mismatch(&mut self, line: i32, got: Option<Vec<u8>>) {
        let name = got.unwrap_or_else(|| b"unparsable".to_vec());
        let open = self.cur_name();
        let m = cat(&[b"Opening and ending tag mismatch: ", &open, b" line ", &itoa(line as i64), b" and ", &name, b"\n"]);
        self.fatal_sis(ERR_TAG_NAME_MISMATCH, &m, Some(&open), line, Some(&name));
    }

    /// `xmlParseEndTag1`.
    #[verifier::external_body]
    fn parse_end_tag1(&mut self, line: i32) {
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
        if let Err(got) = r {
            self.tag_mismatch(line, got);
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
    #[verifier::external_body]
    fn parse_qname(&mut self) -> (Option<Vec<u8>>, Option<Vec<u8>>) {
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
            let m = cat(&[b"Failed to parse QName '", &name, b"'\n"]);
            self.ns_err(NS_ERR_QNAME, &m, Some(&name), None, None);
            return (Some(name), None);
        }
        (l, p)
    }

    /// `xmlParseQNameAndCompare`.
    #[verifier::external_body]
    fn parse_qname_and_compare(&mut self, name: &[u8], prefix: &[u8]) -> Result<(), Option<Vec<u8>>> {
        self.grow();
        let mut in_ = self.inp().cur;
        let b = |s: &Self, k: usize| at(&s.inp().buf, k);
        let mut k = 0;
        while b(self, in_) != 0 && k < prefix.len() && b(self, in_) == prefix[k] {
            in_ += 1;
            k += 1;
        }
        if k == prefix.len() && b(self, in_) == b':' {
            in_ += 1;
            let mut k = 0;
            while b(self, in_) != 0 && k < name.len() && b(self, in_) == name[k] {
                in_ += 1;
                k += 1;
            }
            if k == name.len() && (b(self, in_) == b'>' || blank(b(self, in_))) {
                let i = self.inp_mut();
                i.col = i.col.saturating_add((in_ - i.cur) as i32);
                i.cur = in_;
                return Ok(());
            }
        }
        let (ret, prefix2) = self.parse_qname();
        match ret {
            None => Err(None),
            Some(r) => {
                if r.as_slice() == name && prefix2.as_deref() == Some(prefix) {
                    Ok(())
                } else {
                    Err(Some(r))
                }
            }
        }
    }

    /// `xmlParseAttribute2`: None when no name parsed, else the name,
    /// prefix and (when it parsed) the value.
    #[verifier::external_body]
    fn parse_attribute2(&mut self, pref: Option<&[u8]>, elem: &[u8]) -> Option<(Vec<u8>, Option<Vec<u8>>, Option<Vec<u8>>)> {
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
        if !self.atts_special.is_empty() {
            let fe = match pref {
                Some(p) => cat(&[p, b":", elem]),
                None => elem.to_vec(),
            };
            let fa = match prefix.as_ref() {
                Some(p) => cat(&[p, b":", &name]),
                None => name.clone(),
            };
            special = self.special_lookup(&fe, &fa).unwrap_or(0);
        }
        self.skip_blanks();
        if self.cur() != b'=' {
            let m = cat(&[b"Specification mandates value for attribute ", &name, b"\n"]);
            self.fatal_str(ERR_ATTRIBUTE_WITHOUT_VALUE, &m, Some(&name));
            return Some((name, prefix, None));
        }
        self.next();
        self.skip_blanks();
        let is_ns = (prefix.is_none() && name.as_slice() == b"xmlns") || prefix.as_deref() == Some(b"xmlns");
        let (val, flags) = match self.parse_att_value_internal(special, is_ns) {
            None => return Some((name, prefix, None)),
            Some(v) => v,
        };
        if self.sink.validate() && self.sink.standalone() == 1 && special & SPECIAL_EXTERNAL != 0 && flags & ATTVAL_NORM_CHANGE != 0 {
            let m = cat(&[b"standalone: normalization of attribute ", &name, b" on ", elem, b" by external subset declaration\n"]);
            self.validity_error(DTD_NOT_STANDALONE, &m, Some(&name), Some(elem));
        }
        if prefix.as_deref() == Some(b"xml") {
            if self.options & PARSE_PEDANTIC != 0 && name.as_slice() == b"lang" {
                self.lang_value(&val);
            }
            if name.as_slice() == b"space" {
                self.xml_space_value(&val);
            }
        }
        Some((name, prefix, Some(val)))
    }

    /// `xmlCtxtGrowAttrs`, on the count only.
    #[verifier::external_body]
    fn grow_attrs(&mut self) -> bool {
        match grow_capacity_min(self.maxatts / 5, 10, MAX_ATTRS) {
            None => {
                self.fatal(ERR_RESOURCE_LIMIT, Some(b"Maximum number of attributes exceeded"));
                false
            }
            Some(n) => {
                self.maxatts = n * 5;
                true
            }
        }
    }

    #[verifier::external_body]
    fn ns_uri_of(&self, ns: NsIdx) -> Option<Vec<u8>> {
        match ns {
            NsIdx::Empty => None,
            NsIdx::Xml => Some(xml_ns().to_vec()),
            NsIdx::At(i) => Some(self.nsdb.tab[i].uri.clone()),
        }
    }

    #[verifier::external_body]
    fn check_ns_uri(&mut self, uri: &[u8], attname: Option<&[u8]>, pedantic_only: bool) {
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
    #[verifier::external_body]
    fn parse_start_tag2(&mut self) -> Option<(Vec<u8>, Option<Vec<u8>>, Option<Vec<u8>>, usize)> {
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
        while self.cur() != b'>' && (self.cur() != b'/' || self.nxt(1) != b'>') && is_byte_char(self.cur()) && !self.stopped() {
            if !self.step() {
                break;
            }
            let (attname, aprefix, attvalue) = match self.parse_attribute2(prefix.as_deref(), &local) {
                None => break,
                Some(a) => a,
            };
            if let Some(v) = attvalue {
                if attname.as_slice() == b"xmlns" && aprefix.is_none() {
                    let uri = v;
                    let mut push = true;
                    if !uri.is_empty() {
                        self.check_ns_uri(&uri, None, false);
                        if uri.as_slice() == xml_ns() {
                            // attname is "xmlns" here, never "xml".
                            self.ns_err(NS_ERR_XML_NAMESPACE, b"xml namespace URI cannot be the default namespace\n", None, None, None);
                            push = false;
                        } else if uri.as_slice() == xmlns_ns() {
                            self.ns_err(NS_ERR_XML_NAMESPACE, b"reuse of the xmlns namespace name is forbidden\n", None, None, None);
                            push = false;
                        }
                    }
                    if push && self.ns_push(None, &uri, false) > 0 {
                        nb_ns += 1;
                    }
                } else if aprefix.as_deref() == Some(b"xmlns") {
                    let uri = v;
                    let push = if attname.as_slice() == b"xml" {
                        if uri.as_slice() != xml_ns() {
                            self.ns_err(NS_ERR_XML_NAMESPACE, b"xml namespace prefix mapped to wrong URI\n", None, None, None);
                        }
                        false
                    } else if uri.as_slice() == xml_ns() {
                        self.ns_err(NS_ERR_XML_NAMESPACE, b"xml namespace URI mapped to wrong prefix\n", None, None, None);
                        false
                    } else if attname.as_slice() == b"xmlns" {
                        self.ns_err(NS_ERR_XML_NAMESPACE, b"redefinition of the xmlns prefix is forbidden\n", None, None, None);
                        false
                    } else if uri.as_slice() == xmlns_ns() {
                        self.ns_err(NS_ERR_XML_NAMESPACE, b"reuse of the xmlns namespace name is forbidden\n", None, None, None);
                        false
                    } else if uri.is_empty() {
                        let m = cat(&[b"xmlns:", &attname, b": Empty XML namespace is not allowed\n"]);
                        self.ns_err(NS_ERR_XML_NAMESPACE, &m, Some(&attname), None, None);
                        false
                    } else {
                        self.check_ns_uri(&uri, Some(&attname), true);
                        true
                    };
                    if push && self.ns_push(Some(&attname), &uri, false) > 0 {
                        nb_ns += 1;
                    }
                } else {
                    let ok = if atts.len() * 5 + 5 > self.maxatts { self.grow_attrs() } else { true };
                    if ok {
                        atts.push(Att { name: attname, prefix: aprefix, ns: NsIdx::Empty, value: v });
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
        let defaults: Vec<DefAttr> = {
            let key = (local.clone(), prefix.clone());
            let mut found = Vec::new();
            let mut k = 0;
            while k < self.atts_default.len() {
                if self.atts_default[k].0 == key {
                    found = self.atts_default[k].1.clone();
                    break;
                }
                k += 1;
            }
            found
        };
        let mut di = 0;
        while di < defaults.len() {
            let d = &defaults[di];
            if d.name.as_slice() == b"xmlns" && d.prefix.is_none() {
                self.entity_check(d.expanded_size);
                if self.ns_push(None, &d.value, true) > 0 {
                    nb_ns += 1;
                }
            } else if d.prefix.as_deref() == Some(b"xmlns") {
                self.entity_check(d.expanded_size);
                if self.ns_push(Some(&d.name), &d.value, true) > 0 {
                    nb_ns += 1;
                }
            } else {
                if nratts + nb_total_def >= MAX_ATTRS {
                    self.fatal(ERR_RESOURCE_LIMIT, Some(b"Maximum number of attributes exceeded"));
                    break;
                }
                nb_total_def += 1;
            }
            di += 1;
        }

        // Resolve the attributes' prefixes.
        let mut i = 0;
        while i < atts.len() {
            let ns = match atts[i].prefix.as_deref() {
                None => NsIdx::Empty,
                Some(b"xml") => NsIdx::Xml,
                Some(p) => {
                    let k = self.nsdb.lookup(Some(p));
                    if k == nsdb::NONE || k < self.nsdb.min {
                        let p = p.to_vec();
                        let a = atts[i].name.clone();
                        let m = cat(&[b"Namespace prefix ", &p, b" for ", &a, b" on ", &local, b" is not defined\n"]);
                        self.ns_err(NS_ERR_UNDEFINED_NAMESPACE, &m, Some(&p), Some(&a), Some(&local));
                        NsIdx::Empty
                    } else {
                        NsIdx::At(k)
                    }
                }
            };
            atts[i].ns = ns;
            i += 1;
        }

        // Duplicates: the entries of the attribute hash, by index.
        let max_atts = nratts + nb_total_def;
        let mut table: Vec<usize> = Vec::new();
        let mut num_dup = 0;
        let mut num_ns = 0;
        if max_atts > 1 {
            let mut j = 0;
            while j < nratts {
                if atts[j].ns == NsIdx::Empty && atts[j].prefix.is_some() {
                    j += 1;
                    continue;
                }
                let uri = self.ns_uri_of(atts[j].ns);
                let mut res: Option<usize> = None;
                let mut t = 0;
                while t < table.len() {
                    let e = table[t];
                    if atts[e].name == atts[j].name && self.ns_uri_of(atts[e].ns) == uri {
                        res = Some(e);
                        break;
                    }
                    t += 1;
                }
                match res {
                    None => table.push(j),
                    Some(e) => {
                        if atts[e].prefix == atts[j].prefix {
                            let (p, n) = (atts[j].prefix.clone(), atts[j].name.clone());
                            self.err_attribute_dup(p.as_deref(), &n);
                            num_dup += 1;
                        } else {
                            let n = atts[j].name.clone();
                            let u = uri.clone().unwrap_or_default();
                            let m = cat(&[b"Namespaced Attribute ", &n, b" in '", &u, b"' redefined\n"]);
                            self.ns_err(NS_ERR_ATTRIBUTE_REDEFINED, &m, Some(&n), uri.as_deref(), None);
                            num_ns += 1;
                        }
                    }
                }
                j += 1;
            }
        }

        // The default attributes themselves.
        let mut di = 0;
        while di < defaults.len() {
            let d = defaults[di].clone();
            di += 1;
            if d.name.as_slice() == b"xmlns" && d.prefix.is_none() {
                continue;
            }
            if d.prefix.as_deref() == Some(b"xmlns") {
                continue;
            }
            let ns = match d.prefix.as_deref() {
                None => NsIdx::Empty,
                Some(b"xml") => NsIdx::Xml,
                Some(p) => {
                    let k = self.nsdb.lookup(Some(p));
                    if k == nsdb::NONE || k < self.nsdb.min {
                        let m = cat(&[b"Namespace prefix ", p, b" for ", &d.name, b" on ", &local, b" is not defined\n"]);
                        self.ns_err(NS_ERR_UNDEFINED_NAMESPACE, &m, Some(p), Some(&d.name), Some(&local));
                        NsIdx::Empty
                    } else {
                        NsIdx::At(k)
                    }
                }
            };
            if max_atts > 1 {
                let uri = self.ns_uri_of(ns);
                let mut res: Option<usize> = None;
                let mut t = 0;
                while t < table.len() {
                    let e = table[t];
                    if atts[e].name == d.name && self.ns_uri_of(atts[e].ns) == uri {
                        res = Some(e);
                        break;
                    }
                    t += 1;
                }
                match res {
                    None => table.push(atts.len()),
                    Some(e) => {
                        if atts[e].prefix == d.prefix {
                            continue;
                        }
                        let u = uri.clone().unwrap_or_default();
                        let m = cat(&[b"Namespaced Attribute ", &d.name, b" in '", &u, b"' redefined\n"]);
                        self.ns_err(NS_ERR_ATTRIBUTE_REDEFINED, &m, Some(&d.name), uri.as_deref(), None);
                    }
                }
            }
            self.entity_check(d.expanded_size);
            if atts.len() * 5 + 5 > self.maxatts && !self.grow_attrs() {
                // libxml2 returns no element here (`localname = NULL`).
                return None;
            }
            if self.sink.validate() && self.sink.standalone() == 1 && d.external {
                let m = cat(&[b"standalone: attribute ", &d.name, b" on ", &local, b" defaulted from external subset\n"]);
                self.validity_error(DTD_STANDALONE_DEFAULTED, &m, Some(&d.name), Some(&local));
            }
            atts.push(Att { name: d.name, prefix: d.prefix, ns, value: d.value });
            nbdef += 1;
        }

        // Duplicate QNames, when the namespace check reported several.
        if num_dup == 0 && num_ns > 1 {
            let mut seen: Vec<usize> = Vec::new();
            let mut j = 0;
            while j < nratts {
                if atts[j].prefix.is_some() {
                    let mut found = false;
                    let mut t = 0;
                    while t < seen.len() {
                        let e = seen[t];
                        if atts[e].name == atts[j].name && atts[e].prefix == atts[j].prefix {
                            found = true;
                            break;
                        }
                        t += 1;
                    }
                    if found {
                        let (p, n) = (atts[j].prefix.clone(), atts[j].name.clone());
                        self.err_attribute_dup(p.as_deref(), &n);
                    } else {
                        seen.push(j);
                    }
                }
                j += 1;
            }
        }

        let uri = self.ns_lookup_uri(prefix.as_deref());
        if let Some(p) = prefix.as_ref() {
            if uri.is_none() {
                let p = p.clone();
                let m = cat(&[b"Namespace prefix ", &p, b" on ", &local, b" is not defined\n"]);
                self.ns_err(NS_ERR_UNDEFINED_NAMESPACE, &m, Some(&p), Some(&local), None);
            }
        }
        if self.sax_on() {
            let uris: Vec<Option<Vec<u8>>> = atts.iter().map(|a| self.ns_uri_of(a.ns)).collect();
            let n = self.nsdb.tab.len();
            let first = n - if nb_ns <= n { nb_ns } else { n };
            let nss: Vec<(Option<Vec<u8>>, Vec<u8>)> = self.nsdb.tab[first..].iter().map(|e| (e.prefix.clone(), e.uri.clone())).collect();
            self.sync();
            let nsv: Vec<(Option<&[u8]>, &[u8])> = nss.iter().map(|(p, u)| (p.as_deref(), u.as_slice())).collect();
            let av: Vec<NsAttr<'_>> = atts
                .iter()
                .zip(uris.iter())
                .map(|(a, u)| NsAttr { local: &a.name, prefix: a.prefix.as_deref(), uri: u.as_deref(), value: &a.value })
                .collect();
            self.sink.start_element_ns(&local, prefix.as_deref(), uri.as_deref(), &nsv, &av, nbdef);
        }
        Some((local, prefix, uri, nb_ns))
    }

    /// `xmlParseEndTag2` for the element on top of the name stack.
    #[verifier::external_body]
    fn parse_end_tag2(&mut self) {
        let tag = match self.names.last() {
            Some(t) => t.clone(),
            None => return,
        };
        self.grow();
        if self.cur() != b'<' || self.nxt(1) != b'/' {
            self.fatal(ERR_LTSLASH_REQUIRED, None);
            return;
        }
        self.skip(2);
        let r = match tag.prefix.as_ref() {
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
        if let Err(got) = r {
            self.tag_mismatch(tag.line, got);
        }
        if self.sax_on() {
            self.sync();
            self.sink.end_element_ns(&tag.name, tag.prefix.as_deref(), tag.uri.as_deref());
        }
        self.space_pop();
        if tag.ns_nr != 0 {
            self.ns_pop(tag.ns_nr);
        }
    }

    /// `xmlParseCDSect`.
    #[verifier::external_body]
    pub fn parse_cdsect(&mut self) {
        let max = if self.options & PARSE_HUGE != 0 { MAX_HUGE_LENGTH } else { MAX_TEXT_LENGTH };
        if self.cur() != b'<' || self.nxt(1) != b'!' || self.nxt(2) != b'[' {
            return;
        }
        self.skip(3);
        if !self.cmp(b"CDATA[") {
            return;
        }
        self.skip(6);
        let (mut r, mut rl) = self.current_char_recover();
        if !is_char(r) {
            self.fatal(ERR_CDATA_NOT_FINISHED, None);
            return;
        }
        self.nextl(rl);
        let (mut s, mut sl) = self.current_char_recover();
        if !is_char(s) {
            self.fatal(ERR_CDATA_NOT_FINISHED, None);
            return;
        }
        self.nextl(sl);
        let (mut cur, mut l) = self.current_char_recover();
        let mut buf: Vec<u8> = Vec::new();
        let mut size = PARSER_BUFFER_SIZE;
        while is_char(cur) && (r != b']' as u32 || s != b']' as u32 || cur != b'>' as u32) {
            if !self.step() {
                return;
            }
            if buf.len() + 5 >= size {
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
            rl = sl;
            s = cur;
            sl = l;
            self.nextl(l);
            (cur, l) = self.current_char_recover();
        }
        let _ = (rl, sl);
        if cur != b'>' as u32 {
            let m = cat(&[b"CData section not finished\n", super::dtd::prefix_n(&buf, 50), b"\n"]);
            self.fatal_str(ERR_CDATA_NOT_FINISHED, &m, Some(&buf));
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
    #[verifier::external_body]
    pub fn parse_content_internal(&mut self) {
        let old_name_nr = self.names.len();
        let old_space_nr = self.space_nr;
        let old_node_nr = self.sink.node_nr();
        self.grow();
        while !self.at_end() && !self.stopped() {
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
        while self.sink.node_nr() > old_node_nr {
            self.sink.node_pop();
        }
        while self.names.len() > old_name_nr {
            let n = self.names.len();
            let ns_nr = self.names[n - 1].ns_nr;
            if ns_nr != 0 {
                self.ns_pop(ns_nr);
            }
            self.name_pop();
        }
        while self.space_nr > old_space_nr {
            self.space_pop();
        }
    }

    #[verifier::external_body]
    fn premature_end(&mut self) {
        let t = match self.names.last() {
            Some(t) => t.clone(),
            None => return,
        };
        let m = cat(&[b"Premature end of data in tag ", &t.name, b" line ", &itoa(t.line as i64), b"\n"]);
        self.fatal_sis(ERR_TAG_NOT_FINISHED, &m, Some(&t.name), t.line, None);
    }

    /// `xmlParseElement`.
    #[verifier::external_body]
    pub fn parse_element(&mut self) {
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
    #[verifier::external_body]
    pub fn parse_element_start(&mut self) -> i32 {
        let max_depth: usize = if self.options & PARSE_HUGE != 0 { 2048 } else { 256 };
        if self.names.len() > max_depth {
            let n = self.names.len() as i64;
            let m = cat(&[b"Excessive depth in document: ", &itoa(n), b" use XML_PARSE_HUGE option\n"]);
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
            self.parse_start_tag().map(|n| (n, None, None, 0))
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
                    self.sink.end_element_ns(&name, prefix.as_deref(), uri.as_deref());
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
            let m = cat(&[b"Couldn't find end of Start Tag ", &name, b" line ", &itoa(line as i64), b"\n"]);
            self.fatal_sis(ERR_GT_REQUIRED, &m, Some(&name), line, None);
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
    #[verifier::external_body]
    pub fn parse_element_end(&mut self) {
        if self.names.is_empty() {
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
