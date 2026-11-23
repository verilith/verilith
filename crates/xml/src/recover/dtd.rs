//! Literals, comments, processing instructions and the DTD (parser.c
//! 4350-4480, 4792-5420, 5447-7117, 7971-8090, 1054-1230).
use super::codes::*;
use super::names::*;
use super::refs::*;
use super::*;
use vstd::prelude::*;

verus! {


/// `xmlAttributeType` and `xmlAttributeDefault`.
pub const ATTRIBUTE_ID: i32 = 2;
pub const ATTRIBUTE_IDREF: i32 = 3;
pub const ATTRIBUTE_IDREFS: i32 = 4;
pub const ATTRIBUTE_ENTITY: i32 = 5;
pub const ATTRIBUTE_ENTITIES: i32 = 6;
pub const ATTRIBUTE_NMTOKEN: i32 = 7;
pub const ATTRIBUTE_NMTOKENS: i32 = 8;
pub const ATTRIBUTE_ENUMERATION: i32 = 9;
pub const ATTRIBUTE_NOTATION: i32 = 10;
pub const ATTRIBUTE_NONE: i32 = 1;
pub const ATTRIBUTE_REQUIRED: i32 = 2;
pub const ATTRIBUTE_IMPLIED: i32 = 3;
pub const ATTRIBUTE_FIXED: i32 = 4;

/// `xmlElementTypeVal`, `xmlElementContentType`, `xmlElementContentOccur`.
pub const ELEMENT_TYPE_EMPTY: i32 = 1;
pub const ELEMENT_TYPE_ANY: i32 = 2;
pub const ELEMENT_TYPE_MIXED: i32 = 3;
pub const ELEMENT_TYPE_ELEMENT: i32 = 4;
pub const CONTENT_PCDATA: i32 = 1;
pub const CONTENT_ELEMENT: i32 = 2;
pub const CONTENT_SEQ: i32 = 3;
pub const CONTENT_OR: i32 = 4;
pub const OCUR_ONCE: i32 = 1;
pub const OCUR_OPT: i32 = 2;
pub const OCUR_MULT: i32 = 3;
pub const OCUR_PLUS: i32 = 4;

// Verified (`crate::lenient`).
pub use crate::lenient::{grow_capacity, prefix_n, split_qname3};

/// Whether `v` holds the byte `b`.
pub fn has_byte(v: &[u8], b: u8) -> bool {
    let mut k: usize = 0;
    while k < v.len()
        decreases v@.len() - k,
    {
        if v[k] == b {
            return true;
        }
        k = k + 1;
    }
    false
}

/// Whether `v` holds the name `n`.
pub fn has_name(v: &Vec<Vec<u8>>, n: &[u8]) -> bool {
    let mut k: usize = 0;
    while k < v.len()
        decreases v@.len() - k,
    {
        if crate::lenient::bytes_eq(v[k].as_slice(), n) {
            return true;
        }
        k = k + 1;
    }
    false
}

/// The validity error of a conditional section across entities.
pub fn condsec_bound() -> &'static [u8] {
    b"All markup of the conditional section is not in the same entity\n"
}

/// `xmlAttrNormalizeSpace`, in place.
pub fn attr_normalize_space(v: &mut Vec<u8>) {
    let r = crate::lenient::attr_normalize_space(v);
    *v = r;
}

impl<S: Sink> Parser<S> {
    /// `xmlParseSystemLiteral`.
    pub fn parse_system_literal(&mut self) -> Option<Vec<u8>>
        requires
            old(self).wf(),
        ensures
            final(self).advances(old(self)),
    {
        let max = if self.options & PARSE_HUGE != 0 { MAX_TEXT_LENGTH } else { MAX_NAME_LENGTH };
        let q = self.cur();
        if q != b'"' && q != b'\'' {
            self.fatal(ERR_LITERAL_NOT_STARTED, None);
            return None;
        }
        let stop = q;
        self.next();
        let mut buf: Vec<u8> = Vec::new();
        let mut size = PARSER_BUFFER_SIZE;
        let c0 = self.current_char_recover();
        let mut c = c0.0;
        let mut l = c0.1;
        while is_char(c) && c != stop as u32
            invariant
                self.advances(old(self)),
            decreases self.fuel,
        {
            if !self.step() {
                return None;
            }
            if buf.len().saturating_add(5) >= size {
                match grow_capacity(size, max) {
                    None => {
                        self.fatal(ERR_NAME_TOO_LONG, Some(b"SystemLiteral"));
                        return None;
                    }
                    Some(n) => size = n,
                }
            }
            push_char(&mut buf, c);
            self.nextl(l);
            let r = self.current_char_recover();
            c = r.0;
            l = r.1;
        }
        if !is_char(c) {
            self.fatal(ERR_LITERAL_NOT_FINISHED, None);
        } else {
            self.next();
        }
        Some(buf)
    }

    /// `xmlParsePubidLiteral`.
    pub fn parse_pubid_literal(&mut self) -> Option<Vec<u8>>
        requires
            old(self).wf(),
        ensures
            final(self).advances(old(self)),
    {
        let max = if self.options & PARSE_HUGE != 0 { MAX_TEXT_LENGTH } else { MAX_NAME_LENGTH };
        let q = self.cur();
        if q != b'"' && q != b'\'' {
            self.fatal(ERR_LITERAL_NOT_STARTED, None);
            return None;
        }
        let stop = q;
        self.next();
        let mut buf: Vec<u8> = Vec::new();
        let mut size = PARSER_BUFFER_SIZE;
        let mut c = self.cur();
        while is_pubid_char(c) && c != stop && !self.stopped()
            invariant
                self.advances(old(self)),
            decreases self.fuel,
        {
            if !self.step() {
                return None;
            }
            if buf.len().saturating_add(1) >= size {
                match grow_capacity(size, max) {
                    None => {
                        self.fatal(ERR_NAME_TOO_LONG, Some(b"Public ID"));
                        return None;
                    }
                    Some(n) => size = n,
                }
            }
            buf.push(c);
            self.next();
            c = self.cur();
        }
        if c != stop {
            self.fatal(ERR_LITERAL_NOT_FINISHED, None);
        } else {
            self.nextl(1);
        }
        Some(buf)
    }

    /// `xmlParseExternalID`: (system ID, public ID).
    pub fn parse_external_id(&mut self, strict: bool) -> (Option<Vec<u8>>, Option<Vec<u8>>)
        requires
            old(self).wf(),
        ensures
            final(self).advances(old(self)),
    {
        let mut uri = None;
        let mut public = None;
        if self.cmp(b"SYSTEM") {
            self.skip(6);
            if self.skip_blanks() == 0 {
                self.fatal_msg(ERR_SPACE_REQUIRED, b"Space required after 'SYSTEM'\n");
            }
            uri = self.parse_system_literal();
            if uri.is_none() {
                self.fatal(ERR_URI_REQUIRED, None);
            }
        } else if self.cmp(b"PUBLIC") {
            self.skip(6);
            if self.skip_blanks() == 0 {
                self.fatal_msg(ERR_SPACE_REQUIRED, b"Space required after 'PUBLIC'\n");
            }
            public = self.parse_pubid_literal();
            if public.is_none() {
                self.fatal(ERR_PUBID_REQUIRED, None);
            }
            if strict {
                if self.skip_blanks() == 0 {
                    self.fatal_msg(ERR_SPACE_REQUIRED, b"Space required after the Public Identifier\n");
                }
            } else {
                if self.skip_blanks() == 0 {
                    return (None, public);
                }
                if self.cur() != b'\'' && self.cur() != b'"' {
                    return (None, public);
                }
            }
            uri = self.parse_system_literal();
            if uri.is_none() {
                self.fatal(ERR_URI_REQUIRED, None);
            }
        }
        (uri, public)
    }

    /// `xmlParseCommentComplex`.
    fn parse_comment_complex(&mut self, buf: Vec<u8>, size: usize)
        requires
            old(self).wf(),
        ensures
            final(self).advances(old(self)),
    {
        let mut buf = buf;
        let mut size = size;
        let max = self.max_length(MAX_TEXT_LENGTH);
        let c0 = self.current_char_recover();
        let mut q = c0.0;
        if q == 0 {
            self.fatal_str(ERR_COMMENT_NOT_FINISHED, b"Comment not terminated\n", None);
            return;
        }
        if !is_char(q) {
            let m = cat(&[b"xmlParseComment: invalid xmlChar value ", itoa(q as i64).as_slice(), b"\n"]);
            self.fatal_int(ERR_INVALID_CHAR, &m, q as i32);
            return;
        }
        self.nextl(c0.1);
        let c1 = self.current_char_recover();
        let mut r = c1.0;
        if r == 0 {
            self.fatal_str(ERR_COMMENT_NOT_FINISHED, b"Comment not terminated\n", None);
            return;
        }
        if !is_char(r) {
            let m = cat(&[b"xmlParseComment: invalid xmlChar value ", itoa(r as i64).as_slice(), b"\n"]);
            self.fatal_int(ERR_INVALID_CHAR, &m, r as i32);
            return;
        }
        self.nextl(c1.1);
        let c2 = self.current_char_recover();
        let mut cur = c2.0;
        let mut l = c2.1;
        if cur == 0 {
            self.fatal_str(ERR_COMMENT_NOT_FINISHED, b"Comment not terminated\n", None);
            return;
        }
        while is_char(cur) && (cur != 0x3E || r != 0x2D || q != 0x2D)
            invariant
                self.advances(old(self)),
            decreases self.fuel,
        {
            if !self.step() {
                return;
            }
            if r == 0x2D && q == 0x2D {
                self.fatal(ERR_HYPHEN_IN_COMMENT, None);
            }
            if buf.len().saturating_add(5) >= size {
                match grow_capacity(size, max) {
                    None => {
                        self.fatal_str(ERR_COMMENT_NOT_FINISHED, b"Comment too big found", None);
                        return;
                    }
                    Some(n) => size = n,
                }
            }
            push_char(&mut buf, q);
            q = r;
            r = cur;
            self.nextl(l);
            let c = self.current_char_recover();
            cur = c.0;
            l = c.1;
        }
        if cur == 0 {
            let m = cat(&[b"Comment not terminated \n<!--", prefix_n(&buf, 50), b"\n"]);
            self.fatal_str(ERR_COMMENT_NOT_FINISHED, &m, Some(buf.as_slice()));
        } else if !is_char(cur) {
            let m = cat(&[b"xmlParseComment: invalid xmlChar value ", itoa(cur as i64).as_slice(), b"\n"]);
            self.fatal_int(ERR_INVALID_CHAR, &m, cur as i32);
        } else {
            self.next();
            if self.sax_on() {
                self.sync();
                self.sink.comment(&buf);
            }
        }
    }

    /// `xmlParseComment`.
    pub fn parse_comment(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).advances(old(self)),
    {
        let max = self.max_length(MAX_TEXT_LENGTH);
        if self.cur() != b'<' || self.nxt(1) != b'!' {
            return;
        }
        self.skip(2);
        if self.cur() != b'-' || self.nxt(1) != b'-' {
            return;
        }
        self.skip(2);
        self.grow();
        // `buf` is libxml2's buffer once it is allocated (`has_buf`).
        let mut buf: Vec<u8> = Vec::new();
        let mut has_buf = false;
        let mut size: usize = PARSER_BUFFER_SIZE;
        let mut p = self.inp().cur;
        loop
            invariant
                self.advances(old(self)),
                p >= self.top().cur,
            decreases self.fuel,
        {
            if !self.step() {
                return;
            }
            let ghost f1 = self.fuel;
            {
                let ghost b0 = self.top().buf@;
                let _bl = self.inp().buf.len();
                if self.bat(p) == 0x0A {
                    while self.bat(p) == 0x0A
                        invariant
                            self.advances(old(self)),
                            self.fuel == f1,
                            self.top().buf@ == b0,
                            _bl == b0.len(),
                            self.top().cur <= p <= b0.len(),
                        decreases b0.len() - p,
                    {
                        self.line_inc();
                        p = p + 1;
                    }
                }
            }
            // get_more:
            loop
                invariant
                    self.advances(old(self)),
                    self.fuel <= f1,
                    p >= self.top().cur,
                decreases self.fuel,
            {
                if !self.step() {
                    return;
                }
                let ghost f2 = self.fuel;
                let ghost b0 = self.top().buf@;
                let _bl = self.inp().buf.len();
                let mut ccol = self.inp().col;
                loop
                    invariant
                        self.advances(old(self)),
                        self.fuel == f2,
                        self.top().buf@ == b0,
                        _bl == b0.len(),
                        p >= self.top().cur,
                    decreases b0.len() - p,
                {
                    let c = self.bat(p);
                    if (c > 0x2D && c <= 0x7F) || (c >= 0x20 && c < 0x2D) || c == 0x09 {
                        p = p + 1;
                        ccol = sat_add_i32(ccol, 1);
                    } else {
                        break;
                    }
                }
                let line = self.inp().line;
                self.set_pos(line, ccol);
                if self.bat(p) == 0x0A {
                    while self.bat(p) == 0x0A
                        invariant
                            self.advances(old(self)),
                            self.fuel == f2,
                            self.top().buf@ == b0,
                            _bl == b0.len(),
                            self.top().cur <= p <= b0.len(),
                        decreases b0.len() - p,
                    {
                        self.line_inc();
                        p = p + 1;
                    }
                    continue;
                }
                let start = self.inp().cur;
                let nbchar = p - start;
                if nbchar > 0 {
                    let len = buf.len();
                    if nbchar > max.saturating_sub(len) {
                        self.fatal_str(ERR_COMMENT_NOT_FINISHED, b"Comment too big found", None);
                        return;
                    }
                    if !has_buf {
                        size = if self.bat(p) == 0x2D && crate::lenient::at_off(&self.inp().buf, p, 1) == 0x2D { nbchar.saturating_add(1) } else { PARSER_BUFFER_SIZE.saturating_add(nbchar) };
                        buf = self.slice(start, p);
                        has_buf = true;
                    } else {
                        if buf.len().saturating_add(nbchar).saturating_add(1) >= size {
                            size = size.saturating_add(buf.len()).saturating_add(nbchar).saturating_add(PARSER_BUFFER_SIZE);
                        }
                        let t = self.slice(start, p);
                        buf.extend_from_slice(&t);
                    }
                }
                self.set_cur(p);
                if self.bat(p) == 0x0A {
                    p = p + 1;
                    self.line_inc();
                }
                if self.bat(p) == 0x0D {
                    p = p + 1;
                    if self.bat(p) == 0x0A {
                        self.set_cur(p);
                        p = p + 1;
                        self.line_inc();
                        continue;
                    }
                    // `in--`: p is reloaded from cur below.
                }
                self.shrink();
                self.grow();
                p = self.inp().cur;
                let _bl = self.inp().buf.len();
                if self.bat(p) == 0x2D {
                    if crate::lenient::at_off(&self.inp().buf, p, 1) == 0x2D {
                        if crate::lenient::at_off(&self.inp().buf, p, 2) == 0x3E {
                            self.skip(3);
                            if self.sax_on() {
                                self.sync();
                                if has_buf {
                                    self.sink.comment(&buf);
                                } else {
                                    self.sink.comment(b"");
                                }
                            }
                            return;
                        }
                        if has_buf {
                            let m = cat(&[b"Double hyphen within comment: <!--", prefix_n(&buf, 50), b"\n"]);
                            self.fatal_str(ERR_HYPHEN_IN_COMMENT, &m, Some(buf.as_slice()));
                        } else {
                            self.fatal_str(ERR_HYPHEN_IN_COMMENT, b"Double hyphen within comment\n", None);
                        }
                        p = p + 1;
                        self.col_inc();
                    }
                    p = p + 1;
                    self.col_inc();
                    continue;
                }
                break;
            }
            let c = self.bat(p);
            if !((0x20 <= c && c <= 0x7F) || c == 0x09 || c == 0x0A) {
                break;
            }
        }
        if !has_buf {
            size = PARSER_BUFFER_SIZE;
        }
        self.parse_comment_complex(buf, size);
    }

    /// `xmlParsePITarget`.
    pub fn parse_pi_target(&mut self) -> Option<Vec<u8>>
        requires
            old(self).wf(),
        ensures
            final(self).advances(old(self)),
    {
        let name = self.parse_name();
        match &name {
            None => {}
            Some(n) => {
                if n.len() >= 3 && (n[0] == b'x' || n[0] == b'X') && (n[1] == b'm' || n[1] == b'M') && (n[2] == b'l' || n[2] == b'L') {
                    if crate::lenient::bytes_eq(n, b"xml") {
                        self.fatal_msg(ERR_RESERVED_XML_NAME, b"XML declaration allowed only at the start of the document\n");
                        return name;
                    } else if n.len() == 3 {
                        self.fatal(ERR_RESERVED_XML_NAME, None);
                        return name;
                    }
                    if crate::lenient::bytes_eq(n, b"xml-stylesheet") || crate::lenient::bytes_eq(n, b"xml-model") {
                        return name;
                    }
                    self.warning(ERR_RESERVED_XML_NAME, b"xmlParsePITarget: invalid name prefix 'xml'\n", None, None);
                }
                let mut colon = false;
                let mut k: usize = 0;
                while k < n.len()
                    decreases n@.len() - k,
                {
                    if n[k] == b':' {
                        colon = true;
                    }
                    k = k + 1;
                }
                if colon {
                    let m = cat(&[b"colons are forbidden from PI names '", n.as_slice(), b"'\n"]);
                    self.ns_err(NS_ERR_COLON, &m, Some(n.as_slice()), None, None);
                }
            }
        }
        name
    }

    /// `xmlParsePI`.
    pub fn parse_pi(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).advances(old(self)),
    {
        let max = self.max_length(MAX_TEXT_LENGTH);
        if self.cur() != b'<' || self.nxt(1) != b'?' {
            return;
        }
        self.skip(2);
        let target = match self.parse_pi_target() {
            None => {
                self.fatal(ERR_PI_NOT_STARTED, None);
                return;
            }
            Some(t) => t,
        };
        if self.cur() == b'?' && self.nxt(1) == b'>' {
            self.skip(2);
            if self.sax_on() {
                self.sync();
                self.sink.processing_instruction(&target, None);
            }
            return;
        }
        let mut buf: Vec<u8> = Vec::new();
        let mut size = PARSER_BUFFER_SIZE;
        if self.skip_blanks() == 0 {
            let m = cat(&[b"ParsePI: PI ", target.as_slice(), b" space expected\n"]);
            self.fatal_str(ERR_SPACE_REQUIRED, &m, Some(target.as_slice()));
        }
        let c0 = self.current_char_recover();
        let mut c = c0.0;
        let mut l = c0.1;
        while is_char(c) && (c != 0x3F || self.nxt(1) != b'>')
            invariant
                self.advances(old(self)),
            decreases self.fuel,
        {
            if !self.step() {
                return;
            }
            if buf.len().saturating_add(5) >= size {
                match grow_capacity(size, max) {
                    None => {
                        let m = cat(&[b"PI ", target.as_slice(), b" too big found"]);
                        self.fatal_str(ERR_PI_NOT_FINISHED, &m, Some(target.as_slice()));
                        return;
                    }
                    Some(n) => size = n,
                }
            }
            push_char(&mut buf, c);
            self.nextl(l);
            let r = self.current_char_recover();
            c = r.0;
            l = r.1;
        }
        if c != 0x3F {
            let m = cat(&[b"ParsePI: PI ", target.as_slice(), b" never end ...\n"]);
            self.fatal_str(ERR_PI_NOT_FINISHED, &m, Some(target.as_slice()));
        } else {
            self.skip(2);
            if self.sax_on() {
                self.sync();
                self.sink.processing_instruction(&target, Some(buf.as_slice()));
            }
        }
    }

    /// `xmlParseNotationDecl`.
    pub fn parse_notation_decl(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).evolves(old(self)),
    {
        if self.cur() != b'<' || self.nxt(1) != b'!' {
            return;
        }
        self.skip(2);
        if !self.cmp(b"NOTATION") {
            return;
        }
        let old_nr = self.inputs.len();
        self.skip(8);
        if self.skip_blanks_pe() == 0 {
            self.fatal_msg(ERR_SPACE_REQUIRED, b"Space required after '<!NOTATION'\n");
            return;
        }
        let name = match self.parse_name() {
            None => {
                self.fatal(ERR_NOTATION_NOT_STARTED, None);
                return;
            }
            Some(n) => n,
        };
        if has_byte(&name, b':') {
            let m = cat(&[b"colons are forbidden from notation names '", name.as_slice(), b"'\n"]);
            self.ns_err(NS_ERR_COLON, &m, Some(name.as_slice()), None, None);
        }
        if self.skip_blanks_pe() == 0 {
            self.fatal_msg(ERR_SPACE_REQUIRED, b"Space required after the NOTATION name'\n");
            return;
        }
        let (system, public) = self.parse_external_id(false);
        self.skip_blanks_pe();
        if self.cur() == b'>' {
            if self.sink.validate() && self.inputs.len() > old_nr {
                self.validity_error(ERR_ENTITY_BOUNDARY, b"Notation declaration doesn't start and stop in the same entity\n", None, None);
            }
            self.next();
            if self.sax_on() {
                self.sync();
                self.sink.notation_decl(&name, opt_slice(&public), opt_slice(&system));
            }
        } else {
            self.fatal(ERR_NOTATION_NOT_FINISHED, None);
        }
    }

    /// `xmlParseEntityDecl`.
    pub fn parse_entity_decl(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).evolves(old(self)),
    {
        if self.cur() != b'<' || self.nxt(1) != b'!' {
            return;
        }
        self.skip(2);
        if !self.cmp(b"ENTITY") {
            return;
        }
        let old_nr = self.inputs.len();
        let mut is_param = false;
        let mut orig: Option<Vec<u8>> = None;
        self.skip(6);
        if self.skip_blanks_pe() == 0 {
            self.fatal_msg(ERR_SPACE_REQUIRED, b"Space required after '<!ENTITY'\n");
        }
        if self.cur() == b'%' {
            self.next();
            if self.skip_blanks_pe() == 0 {
                self.fatal_msg(ERR_SPACE_REQUIRED, b"Space required after '%'\n");
            }
            is_param = true;
        }
        let name = match self.parse_name() {
            None => {
                self.fatal_msg(ERR_NAME_REQUIRED, b"xmlParseEntityDecl: no name\n");
                return;
            }
            Some(n) => n,
        };
        if has_byte(&name, b':') {
            let m = cat(&[b"colons are forbidden from entities names '", name.as_slice(), b"'\n"]);
            self.ns_err(NS_ERR_COLON, &m, Some(name.as_slice()), None, None);
        }
        if self.skip_blanks_pe() == 0 {
            self.fatal_msg(ERR_SPACE_REQUIRED, b"Space required after the entity name\n");
        }
        if is_param {
            if self.cur() == b'"' || self.cur() == b'\'' {
                let (value, o) = self.parse_entity_value();
                orig = o;
                match &value {
                    Some(v) => {
                        if self.sax_on() {
                            self.sync();
                            self.sink.entity_decl(&name, INTERNAL_PARAMETER_ENTITY, None, None, Some(v.as_slice()));
                        }
                    }
                    None => {}
                }
            } else {
                let (uri, literal) = self.parse_external_id(true);
                if uri.is_none() && literal.is_none() {
                    self.fatal(ERR_VALUE_REQUIRED, None);
                }
                match &uri {
                    Some(u) => {
                        if has_byte(u, b'#') {
                            self.fatal(ERR_URI_FRAGMENT, None);
                        } else if self.sax_on() {
                            self.sync();
                            self.sink.entity_decl(&name, EXTERNAL_PARAMETER_ENTITY, opt_slice(&literal), Some(u.as_slice()), None);
                        }
                    }
                    None => {}
                }
            }
        } else {
            if self.cur() == b'"' || self.cur() == b'\'' {
                let (value, o) = self.parse_entity_value();
                orig = o;
                if self.sax_on() {
                    self.sync();
                    self.sink.entity_decl(&name, INTERNAL_GENERAL_ENTITY, None, None, opt_slice(&value));
                }
                self.sink.compat_entity_decl(&name, INTERNAL_GENERAL_ENTITY, None, None, opt_slice(&value));
            } else {
                let (uri, literal) = self.parse_external_id(true);
                if uri.is_none() && literal.is_none() {
                    self.fatal(ERR_VALUE_REQUIRED, None);
                }
                match &uri {
                    Some(u) => {
                        if has_byte(u, b'#') {
                            self.fatal(ERR_URI_FRAGMENT, None);
                        }
                    }
                    None => {}
                }
                if self.cur() != b'>' && self.skip_blanks_pe() == 0 {
                    self.fatal_msg(ERR_SPACE_REQUIRED, b"Space required before 'NDATA'\n");
                }
                if self.cmp(b"NDATA") {
                    self.skip(5);
                    if self.skip_blanks_pe() == 0 {
                        self.fatal_msg(ERR_SPACE_REQUIRED, b"Space required after 'NDATA'\n");
                    }
                    let ndata = self.parse_name();
                    if self.sax_on() && self.sink.has_unparsed_entity_decl() {
                        self.sync();
                        self.sink.unparsed_entity_decl(&name, opt_slice(&literal), opt_slice(&uri), opt_slice(&ndata));
                    }
                } else {
                    if self.sax_on() {
                        self.sync();
                        self.sink.entity_decl(&name, EXTERNAL_GENERAL_PARSED_ENTITY, opt_slice(&literal), opt_slice(&uri), None);
                    }
                    if self.replace_entities {
                        self.sink.compat_entity_decl(&name, EXTERNAL_GENERAL_PARSED_ENTITY, opt_slice(&literal), opt_slice(&uri), None);
                    }
                }
            }
        }
        self.skip_blanks_pe();
        if self.cur() != b'>' {
            let m = cat(&[b"xmlParseEntityDecl: entity ", name.as_slice(), b" not terminated\n"]);
            self.fatal_str(ERR_ENTITY_NOT_FINISHED, &m, Some(name.as_slice()));
        } else {
            if self.sink.validate() && self.inputs.len() > old_nr {
                self.validity_error(ERR_ENTITY_BOUNDARY, b"Entity declaration doesn't start and stop in the same entity\n", None, None);
            }
            self.next();
        }
        match orig {
            Some(o) => self.sink.entity_orig(is_param, &name, &o),
            None => {}
        }
    }

    /// `xmlParseDefaultDecl`: the default kind and value.
    pub fn parse_default_decl(&mut self) -> (i32, Option<Vec<u8>>)
        requires
            old(self).wf(),
        ensures
            final(self).evolves(old(self)),
    {
        if self.cmp(b"#REQUIRED") {
            self.skip(9);
            return (ATTRIBUTE_REQUIRED, None);
        }
        if self.cmp(b"#IMPLIED") {
            self.skip(8);
            return (ATTRIBUTE_IMPLIED, None);
        }
        let mut val = ATTRIBUTE_NONE;
        if self.cmp(b"#FIXED") {
            self.skip(6);
            val = ATTRIBUTE_FIXED;
            if self.skip_blanks_pe() == 0 {
                self.fatal_msg(ERR_SPACE_REQUIRED, b"Space required after '#FIXED'\n");
            }
        }
        let ret = self.parse_att_value();
        if ret.is_none() {
            let code = self.sink.err_no();
            self.fatal_msg(code, b"Attribute default value declaration error\n");
        }
        (val, ret)
    }

    /// `xmlParseNotationType`.
    pub fn parse_notation_type(&mut self) -> Option<Vec<Vec<u8>>>
        requires
            old(self).wf(),
        ensures
            final(self).evolves(old(self)),
    {
        if self.cur() != b'(' {
            self.fatal(ERR_NOTATION_NOT_STARTED, None);
            return None;
        }
        let mut ret: Vec<Vec<u8>> = Vec::new();
        loop
            invariant
                self.evolves(old(self)),
            decreases self.fuel,
        {
            if !self.step() {
                return None;
            }
            self.next();
            self.skip_blanks_pe();
            let name = match self.parse_name() {
                None => {
                    self.fatal_msg(ERR_NAME_REQUIRED, b"Name expected in NOTATION declaration\n");
                    return None;
                }
                Some(n) => n,
            };
            let mut dup = false;
            if self.sink.validate() && has_name(&ret, &name) {
                let m = cat(&[b"standalone: attribute notation value token ", name.as_slice(), b" duplicated\n"]);
                self.validity_error(DTD_DUP_TOKEN, &m, Some(name.as_slice()), None);
                dup = true;
            }
            if !dup {
                ret.push(name);
            }
            self.skip_blanks_pe();
            if self.cur() != b'|' {
                break;
            }
        }
        if self.cur() != b')' {
            self.fatal(ERR_NOTATION_NOT_FINISHED, None);
            return None;
        }
        self.next();
        Some(ret)
    }

    /// `xmlParseEnumerationType`.
    pub fn parse_enumeration_type(&mut self) -> Option<Vec<Vec<u8>>>
        requires
            old(self).wf(),
        ensures
            final(self).evolves(old(self)),
    {
        if self.cur() != b'(' {
            self.fatal(ERR_ATTLIST_NOT_STARTED, None);
            return None;
        }
        let mut ret: Vec<Vec<u8>> = Vec::new();
        loop
            invariant
                self.evolves(old(self)),
            decreases self.fuel,
        {
            if !self.step() {
                return None;
            }
            self.next();
            self.skip_blanks_pe();
            let name = match self.parse_nmtoken() {
                None => {
                    self.fatal(ERR_NMTOKEN_REQUIRED, None);
                    return if ret.len() == 0 { None } else { Some(ret) };
                }
                Some(n) => n,
            };
            let mut dup = false;
            if self.sink.validate() && has_name(&ret, &name) {
                let m = cat(&[b"standalone: attribute enumeration value token ", name.as_slice(), b" duplicated\n"]);
                self.validity_error(DTD_DUP_TOKEN, &m, Some(name.as_slice()), None);
                dup = true;
            }
            if !dup {
                ret.push(name);
            }
            self.skip_blanks_pe();
            if self.cur() != b'|' {
                break;
            }
        }
        if self.cur() != b')' {
            self.fatal(ERR_ATTLIST_NOT_FINISHED, None);
            return if ret.len() == 0 { None } else { Some(ret) };
        }
        self.next();
        if ret.len() == 0 { None } else { Some(ret) }
    }

    /// `xmlParseEnumeratedType`.
    pub fn parse_enumerated_type(&mut self) -> (i32, Option<Vec<Vec<u8>>>)
        requires
            old(self).wf(),
        ensures
            final(self).evolves(old(self)),
    {
        if self.cmp(b"NOTATION") {
            self.skip(8);
            if self.skip_blanks_pe() == 0 {
                self.fatal_msg(ERR_SPACE_REQUIRED, b"Space required after 'NOTATION'\n");
                return (0, None);
            }
            let t = self.parse_notation_type();
            let empty = match &t {
                None => true,
                Some(v) => v.len() == 0,
            };
            if empty {
                return (0, None);
            }
            return (ATTRIBUTE_NOTATION, t);
        }
        let t = self.parse_enumeration_type();
        if t.is_none() {
            return (0, None);
        }
        (ATTRIBUTE_ENUMERATION, t)
    }

    /// `xmlParseAttributeType`.
    pub fn parse_attribute_type(&mut self) -> (i32, Option<Vec<Vec<u8>>>)
        requires
            old(self).wf(),
        ensures
            final(self).evolves(old(self)),
    {
        if self.cmp(b"CDATA") {
            self.skip(5);
            (ATTRIBUTE_CDATA, None)
        } else if self.cmp(b"IDREFS") {
            self.skip(6);
            (ATTRIBUTE_IDREFS, None)
        } else if self.cmp(b"IDREF") {
            self.skip(5);
            (ATTRIBUTE_IDREF, None)
        } else if self.cur() == b'I' && self.nxt(1) == b'D' {
            self.skip(2);
            (ATTRIBUTE_ID, None)
        } else if self.cmp(b"ENTITY") {
            self.skip(6);
            (ATTRIBUTE_ENTITY, None)
        } else if self.cmp(b"ENTITIES") {
            self.skip(8);
            (ATTRIBUTE_ENTITIES, None)
        } else if self.cmp(b"NMTOKENS") {
            self.skip(8);
            (ATTRIBUTE_NMTOKENS, None)
        } else if self.cmp(b"NMTOKEN") {
            self.skip(7);
            (ATTRIBUTE_NMTOKEN, None)
        } else {
            self.parse_enumerated_type()
        }
    }

    /// `xmlParseAttributeListDecl`.
    pub fn parse_attribute_list_decl(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).evolves(old(self)),
    {
        if self.cur() != b'<' || self.nxt(1) != b'!' {
            return;
        }
        self.skip(2);
        if !self.cmp(b"ATTLIST") {
            return;
        }
        let old_nr = self.inputs.len();
        self.skip(7);
        if self.skip_blanks_pe() == 0 {
            self.fatal_msg(ERR_SPACE_REQUIRED, b"Space required after '<!ATTLIST'\n");
        }
        let elem = match self.parse_name() {
            None => {
                self.fatal_msg(ERR_NAME_REQUIRED, b"ATTLIST: no name for Element\n");
                return;
            }
            Some(n) => n,
        };
        self.skip_blanks_pe();
        self.grow();
        while self.cur() != b'>' && !self.stopped()
            invariant
                self.evolves(old(self)),
            decreases self.fuel,
        {
            if !self.step() {
                return;
            }
            self.grow();
            let attr = match self.parse_name() {
                None => {
                    self.fatal_msg(ERR_NAME_REQUIRED, b"ATTLIST: no name for Attribute\n");
                    break;
                }
                Some(n) => n,
            };
            self.grow();
            if self.skip_blanks_pe() == 0 {
                self.fatal_msg(ERR_SPACE_REQUIRED, b"Space required after the attribute name\n");
                break;
            }
            let (atype, tree) = self.parse_attribute_type();
            if atype <= 0 {
                break;
            }
            self.grow();
            if self.skip_blanks_pe() == 0 {
                self.fatal_msg(ERR_SPACE_REQUIRED, b"Space required after the attribute type\n");
                break;
            }
            let (def, default) = self.parse_default_decl();
            if def <= 0 {
                break;
            }
            let default = match default {
                Some(v) => {
                    let mut v = v;
                    if atype != ATTRIBUTE_CDATA {
                        attr_normalize_space(&mut v);
                    }
                    Some(v)
                }
                None => None,
            };
            self.grow();
            if self.cur() != b'>' && self.skip_blanks_pe() == 0 {
                self.fatal_msg(ERR_SPACE_REQUIRED, b"Space required after the attribute default value\n");
                break;
            }
            if self.sax_on() {
                self.sync();
                self.sink.attribute_decl(&elem, &attr, atype, def, opt_slice(&default), tree);
            }
            if self.sax2 && def != ATTRIBUTE_IMPLIED && def != ATTRIBUTE_REQUIRED {
                match &default {
                    Some(v) => self.add_def_attrs(&elem, &attr, v),
                    None => {}
                }
            }
            if self.sax2 {
                self.add_special_attr(&elem, &attr, atype);
            }
            self.grow();
        }
        if self.cur() == b'>' {
            if self.sink.validate() && self.inputs.len() > old_nr {
                self.validity_error(ERR_ENTITY_BOUNDARY, b"Attribute list declaration doesn't start and stop in the same entity\n", None, None);
            }
            self.next();
        }
    }

    /// `xmlAddDefAttrs`.
    pub fn add_def_attrs(&mut self, fullname: &[u8], fullattr: &[u8], value: &[u8])
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).inputs == old(self).inputs,
            final(self).fuel == old(self).fuel,
    {
        if self.special_lookup(fullname, fullattr).is_some() {
            return;
        }
        let (eprefix, ename) = match split_qname3(fullname) {
            None => (None, crate::lenient::vec_of(fullname)),
            Some((p, l)) => (Some(crate::lenient::vec_of(p)), crate::lenient::vec_of(l)),
        };
        let (aprefix, aname) = match split_qname3(fullattr) {
            None => (None, crate::lenient::vec_of(fullattr)),
            Some((p, l)) => (Some(crate::lenient::vec_of(p)), crate::lenient::vec_of(l)),
        };
        let mut expanded = aname.len() as u64;
        match &aprefix {
            Some(p) => expanded = expanded.saturating_add(p.len() as u64),
            None => {}
        }
        expanded = expanded.saturating_add(value.len() as u64);
        let external = self.external();
        let d = DefAttr { prefix: aprefix, name: aname, value: crate::lenient::vec_of(value), external, expanded_size: expanded };
        let mut k: usize = 0;
        while k < self.atts_default.len()
            invariant
                self.wf(),
                self.inputs == old(self).inputs,
                self.fuel == old(self).fuel,
            decreases self.atts_default@.len() - k,
        {
            if crate::lenient::bytes_eq(self.atts_default[k].0.0.as_slice(), ename.as_slice()) && crate::lenient::opt_eq(opt_slice(&self.atts_default[k].0.1), opt_slice(&eprefix)) {
                self.atts_default[k].1.push(d);
                return;
            }
            k = k + 1;
        }
        let mut v: Vec<DefAttr> = Vec::new();
        v.push(d);
        self.atts_default.push(((ename, eprefix), v));
    }

    pub fn special_lookup(&self, elem: &[u8], attr: &[u8]) -> Option<i32> {
        let mut k: usize = 0;
        while k < self.atts_special.len()
            decreases self.atts_special@.len() - k,
        {
            let e = &self.atts_special[k];
            if crate::lenient::bytes_eq(e.0.0.as_slice(), elem) && crate::lenient::bytes_eq(e.0.1.as_slice(), attr) {
                return Some(e.1);
            }
            k = k + 1;
        }
        None
    }

    /// `xmlAddSpecialAttr` (`xmlHashAdd2`: the first declaration stays).
    pub fn add_special_attr(&mut self, elem: &[u8], attr: &[u8], atype: i32)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).inputs == old(self).inputs,
            final(self).fuel == old(self).fuel,
    {
        let t = if self.external() { atype | SPECIAL_EXTERNAL } else { atype };
        if self.special_lookup(elem, attr).is_none() {
            self.atts_special.push(((crate::lenient::vec_of(elem), crate::lenient::vec_of(attr)), t));
        }
    }

    /// `xmlCleanSpecialAttr`.
    pub fn clean_special_attr(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).inputs == old(self).inputs,
            final(self).fuel == old(self).fuel,
    {
        let mut all: Vec<((Vec<u8>, Vec<u8>), i32)> = Vec::new();
        std::mem::swap(&mut all, &mut self.atts_special);
        let mut k: usize = 0;
        while k < all.len()
            invariant
                self.wf(),
                self.inputs == old(self).inputs,
                self.fuel == old(self).fuel,
            decreases all@.len() - k,
        {
            if all[k].1 != ATTRIBUTE_CDATA {
                let e = ((all[k].0.0.clone(), all[k].0.1.clone()), all[k].1);
                self.atts_special.push(e);
            }
            k = k + 1;
        }
    }

    /// `xmlPopPE`.
    pub fn pop_pe(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).evolves(old(self)),
            final(self).inputs@.len() <= old(self).inputs@.len(),
    {
        let ent = match self.inp().entity {
            None => return,
            Some(e) => e,
        };
        let info = self.sink.ent_info(ent);
        self.sink.ent_set_flags(ent, info.flags & !ENT_EXPANDING);
        if info.flags & ENT_CHECKED == 0 {
            loop
                invariant
                    self.evolves(old(self)),
                    self.inputs@.len() == old(self).inputs@.len(),
                decreases self.fuel,
            {
                if !self.step() {
                    break;
                }
                let n = self.inp().buf.len();
                self.set_cur(n);
                self.shrink();
                if self.grow_now() <= 0 {
                    break;
                }
            }
            let consumed = {
                let i = self.inp();
                i.consumed.saturating_add(i.buf.len() as u64)
            };
            let info = self.sink.ent_info(ent);
            self.sink.ent_set_expanded_size(ent, info.expanded_size.saturating_add(consumed));
            if info.etype == EXTERNAL_PARAMETER_ENTITY {
                self.sink.add_sizeentities(consumed);
            }
            let f = self.sink.ent_info(ent).flags;
            self.sink.ent_set_flags(ent, f | ENT_CHECKED);
        }
        self.pop_input();
        let es = self.sink.ent_info(ent).expanded_size;
        self.entity_check(es);
        self.grow();
    }

    /// `xmlSkipBlankCharsPE` (`SKIP_BLANKS_PE`).
    pub fn skip_blanks_pe(&mut self) -> usize
        requires
            old(self).wf(),
        ensures
            final(self).evolves(old(self)),
    {
        let mut res: usize = 0;
        let mut in_param = self.in_pe();
        let mut expand = self.external();
        if !in_param && !expand {
            return self.skip_blanks();
        }
        while !self.stopped()
            invariant
                self.evolves(old(self)),
            decreases self.fuel,
        {
            if !self.step() {
                break;
            }
            let c = self.cur();
            if blank(c) {
                self.next();
            } else if c == b'%' {
                if !expand || blank(self.nxt(1)) || self.nxt(1) == 0 {
                    break;
                }
                self.parse_pe_ref_internal(false);
                in_param = self.in_pe();
                expand = self.external();
            } else if c == 0 {
                if !in_param {
                    break;
                }
                if self.inp().flags & INPUT_MARKUP_DECL != 0 {
                    break;
                }
                self.pop_pe();
                in_param = self.in_pe();
                expand = self.external();
            } else {
                break;
            }
            res = res.saturating_add(1);
        }
        res
    }

    /// `xmlSkipBlankCharsPEBalanced`.
    fn skip_blanks_pe_balanced(&mut self, open_nr: usize)
        requires
            old(self).wf(),
        ensures
            final(self).evolves(old(self)),
    {
        self.skip_blanks();
        self.grow();
        if !self.external() && !self.in_pe() {
            return;
        }
        while !self.stopped()
            invariant
                self.evolves(old(self)),
            decreases self.fuel,
        {
            if !self.step() {
                break;
            }
            if self.at_end() {
                if self.sink.validate() && self.inputs.len() <= open_nr {
                    self.validity_error(ERR_ENTITY_BOUNDARY, b"Element content declaration doesn't start and stop in the same entity\n", None, None);
                }
                if self.in_pe() {
                    self.pop_pe();
                } else {
                    break;
                }
            } else if self.cur() == b'%' {
                self.parse_pe_ref_internal(false);
            } else {
                break;
            }
            self.skip_blanks();
            self.grow();
        }
    }

    fn content_boundary(&mut self, open_nr: usize)
        requires
            old(self).wf(),
        ensures
            final(self).only_sink(old(self)),
    {
        if self.sink.validate() && self.inputs.len() > open_nr {
            self.validity_error(ERR_ENTITY_BOUNDARY, b"Element content declaration doesn't start and stop in the same entity\n", None, None);
        }
    }

    /// `xmlParseElementMixedContentDecl`.
    pub fn parse_mixed_content_decl(&mut self, m: &mut ContentModel, open_nr: usize) -> (r: Option<usize>)
        requires
            old(self).wf(),
            old(m).ok(),
        ensures
            final(self).evolves(old(self)),
            final(m).ok(),
            final(m).nodes@.len() >= old(m).nodes@.len(),
            r matches Some(k) ==> k < final(m).nodes@.len(),
    {
        self.grow();
        if !self.cmp(b"#PCDATA") {
            self.fatal(ERR_PCDATA_REQUIRED, None);
            return None;
        }
        self.skip(7);
        self.skip_blanks_pe_balanced(open_nr);
        if self.cur() == b')' {
            self.content_boundary(open_nr);
            self.next();
            let r = m.add(CONTENT_PCDATA, None);
            if self.cur() == b'*' {
                m.set_ocur(r, OCUR_MULT);
                self.next();
            }
            return Some(r);
        }
        let mut ret: Option<usize> = None;
        let mut cur: Option<usize> = None;
        if self.cur() == b'(' || self.cur() == b'|' {
            let r = m.add(CONTENT_PCDATA, None);
            ret = Some(r);
            cur = Some(r);
        }
        let mut elem: Option<Vec<u8>> = None;
        while self.cur() == b'|' && !self.stopped()
            invariant
                self.evolves(old(self)),
                m.ok(),
                m.nodes@.len() >= old(m).nodes@.len(),
                ret matches Some(k) ==> k < m.nodes@.len(),
                cur matches Some(k) ==> k < m.nodes@.len(),
            decreases self.fuel,
        {
            if !self.step() {
                return None;
            }
            self.next();
            let n = m.add(CONTENT_OR, None);
            let mut taken: Option<Vec<u8>> = None;
            std::mem::swap(&mut taken, &mut elem);
            match taken {
                None => {
                    m.set_c1(n, cur);
                    match cur {
                        Some(c) => m.set_parent(c, Some(n)),
                        None => {}
                    }
                    ret = Some(n);
                    cur = Some(n);
                }
                Some(e) => {
                    let c = match cur {
                        Some(c) => c,
                        None => n,
                    };
                    m.set_c2(c, Some(n));
                    m.set_parent(n, Some(c));
                    let leaf = m.add(CONTENT_ELEMENT, Some(e));
                    m.set_c1(n, Some(leaf));
                    m.set_parent(leaf, Some(n));
                    cur = Some(n);
                }
            }
            self.skip_blanks_pe_balanced(open_nr);
            elem = self.parse_name();
            if elem.is_none() {
                self.fatal_msg(ERR_NAME_REQUIRED, b"xmlParseElementMixedContentDecl : Name expected\n");
                return None;
            }
            self.skip_blanks_pe_balanced(open_nr);
        }
        if self.cur() == b')' && self.nxt(1) == b'*' {
            match elem {
                Some(e) => match cur {
                    Some(c) => {
                        let leaf = m.add(CONTENT_ELEMENT, Some(e));
                        m.set_c2(c, Some(leaf));
                        m.set_parent(leaf, Some(c));
                    }
                    None => {}
                },
                None => {}
            }
            match ret {
                Some(r) => m.set_ocur(r, OCUR_MULT),
                None => {}
            }
            self.content_boundary(open_nr);
            self.skip(2);
        } else {
            self.fatal(ERR_MIXED_NOT_STARTED, None);
            return None;
        }
        ret
    }

    fn content_ocur(&mut self, m: &mut ContentModel, n: usize)
        requires
            old(self).wf(),
            old(m).ok(),
            n < old(m).nodes@.len(),
        ensures
            final(self).evolves(old(self)),
            final(m).ok(),
            final(m).nodes@.len() == old(m).nodes@.len(),
    {
        let c = self.cur();
        let o = if c == b'?' {
            OCUR_OPT
        } else if c == b'*' {
            OCUR_MULT
        } else if c == b'+' {
            OCUR_PLUS
        } else {
            OCUR_ONCE
        };
        m.set_ocur(n, o);
        if o != OCUR_ONCE {
            self.next();
        }
    }

    /// `xmlParseElementChildrenContentDeclPriv`.
    pub fn parse_children_content_decl(&mut self, m: &mut ContentModel, open_nr: usize, depth: i32) -> (r: Option<usize>)
        requires
            old(self).wf(),
            old(m).ok(),
        ensures
            final(self).evolves(old(self)),
            final(m).ok(),
            final(m).nodes@.len() >= old(m).nodes@.len(),
            r matches Some(k) ==> k < final(m).nodes@.len(),
        decreases 2049 - depth,
    {
        let max_depth = if self.options & PARSE_HUGE != 0 { 2048 } else { 256 };
        if depth > max_depth {
            let msg = cat(&[b"xmlParseElementChildrenContentDecl : depth ", itoa(depth as i64).as_slice(), b" too deep, use XML_PARSE_HUGE\n"]);
            self.fatal_int(ERR_RESOURCE_LIMIT, &msg, depth);
            return None;
        }
        let mut ret: usize;
        let mut cur: usize;
        let mut last: Option<usize> = None;
        let mut typ: u8 = 0;
        self.skip_blanks_pe_balanced(open_nr);
        if self.cur() == b'(' {
            let nr = self.inputs.len();
            self.next();
            ret = match self.parse_children_content_decl(m, nr, depth + 1) {
                None => return None,
                Some(r) => r,
            };
            cur = ret;
        } else {
            let elem = match self.parse_name() {
                None => {
                    self.fatal(ERR_ELEMCONTENT_NOT_STARTED, None);
                    return None;
                }
                Some(e) => e,
            };
            ret = m.add(CONTENT_ELEMENT, Some(elem));
            cur = ret;
            self.grow();
            self.content_ocur(m, cur);
            self.grow();
        }
        while !self.stopped()
            invariant
                self.evolves(old(self)),
                m.ok(),
                m.nodes@.len() >= old(m).nodes@.len(),
                ret < m.nodes@.len(),
                cur < m.nodes@.len(),
                last matches Some(k) ==> k < m.nodes@.len(),
                depth <= max_depth,
                max_depth <= 2048,
            decreases self.fuel,
        {
            if !self.step() {
                return None;
            }
            self.skip_blanks_pe_balanced(open_nr);
            let c = self.cur();
            if c == b')' {
                break;
            }
            if c == b',' || c == b'|' {
                if typ == 0 {
                    typ = c;
                } else if typ != c {
                    let mut tv: Vec<u8> = Vec::new();
                    tv.push(typ);
                    let msg = cat(&[b"xmlParseElementChildrenContentDecl : '", tv.as_slice(), b"' expected\n"]);
                    self.fatal_int(ERR_SEPARATOR_REQUIRED, &msg, typ as i32);
                    return None;
                }
                self.next();
                let op = m.add(if c == b',' { CONTENT_SEQ } else { CONTENT_OR }, None);
                match last {
                    None => {
                        m.set_c1(op, Some(ret));
                        m.set_parent(ret, Some(op));
                        ret = op;
                        cur = op;
                    }
                    Some(l) => {
                        m.set_c2(cur, Some(op));
                        m.set_parent(op, Some(cur));
                        m.set_c1(op, Some(l));
                        m.set_parent(l, Some(op));
                        cur = op;
                    }
                }
            } else {
                self.fatal(ERR_ELEMCONTENT_NOT_FINISHED, None);
                return None;
            }
            self.skip_blanks_pe_balanced(open_nr);
            if self.cur() == b'(' {
                let nr = self.inputs.len();
                self.next();
                last = match self.parse_children_content_decl(m, nr, depth + 1) {
                    None => return None,
                    Some(l) => Some(l),
                };
            } else {
                let elem = match self.parse_name() {
                    None => {
                        self.fatal(ERR_ELEMCONTENT_NOT_STARTED, None);
                        return None;
                    }
                    Some(e) => e,
                };
                let l = m.add(CONTENT_ELEMENT, Some(elem));
                self.content_ocur(m, l);
                last = Some(l);
            }
        }
        match last {
            Some(l) => {
                m.set_c2(cur, Some(l));
                m.set_parent(l, Some(cur));
            }
            None => {}
        }
        self.content_boundary(open_nr);
        self.next();
        let c = self.cur();
        if c == b'?' {
            let o = m.nodes[ret].ocur;
            m.set_ocur(ret, if o == OCUR_PLUS || o == OCUR_MULT { OCUR_MULT } else { OCUR_OPT });
            self.next();
        } else if c == b'*' {
            m.set_ocur(ret, OCUR_MULT);
            let mut c = Some(ret);
            // The c2 chain of a model is shorter than the model.
            let mut left = m.nodes.len();
            while left > 0
                invariant
                    m.ok(),
                    m.nodes@.len() >= old(m).nodes@.len(),
                    ret < m.nodes@.len(),
                    c matches Some(k) ==> k < m.nodes@.len(),
                decreases left,
            {
                left = left - 1;
                let ci = match c {
                    None => break,
                    Some(ci) => ci,
                };
                if m.nodes[ci].ctype != CONTENT_OR {
                    break;
                }
                let c1 = m.nodes[ci].c1;
                let c2 = m.nodes[ci].c2;
                proof {
                    assert(node_ok(m.nodes@[ci as int], m.nodes@.len()));
                }
                m.once_if_opt(c1, false);
                m.once_if_opt(c2, false);
                proof {
                    assert(node_ok(m.nodes@[ci as int], m.nodes@.len()));
                }
                c = m.nodes[ci].c2;
            }
            self.next();
        } else if c == b'+' {
            let o = m.nodes[ret].ocur;
            m.set_ocur(ret, if o == OCUR_OPT || o == OCUR_MULT { OCUR_MULT } else { OCUR_PLUS });
            // libxml2 walks from `cur` here, not from `ret`.
            let mut found = false;
            let mut c = Some(cur);
            let mut left = m.nodes.len();
            while left > 0
                invariant
                    m.ok(),
                    m.nodes@.len() >= old(m).nodes@.len(),
                    ret < m.nodes@.len(),
                    c matches Some(k) ==> k < m.nodes@.len(),
                decreases left,
            {
                left = left - 1;
                let ci = match c {
                    None => break,
                    Some(ci) => ci,
                };
                if m.nodes[ci].ctype != CONTENT_OR {
                    break;
                }
                let c1 = m.nodes[ci].c1;
                let c2 = m.nodes[ci].c2;
                proof {
                    assert(node_ok(m.nodes@[ci as int], m.nodes@.len()));
                }
                if m.once_if_opt(c1, true) {
                    found = true;
                }
                if m.once_if_opt(c2, true) {
                    found = true;
                }
                proof {
                    assert(node_ok(m.nodes@[ci as int], m.nodes@.len()));
                }
                c = m.nodes[ci].c2;
            }
            if found {
                m.set_ocur(ret, OCUR_MULT);
            }
            self.next();
        }
        Some(ret)
    }

    /// `xmlParseElementContentDecl`.
    pub fn parse_element_content_decl(&mut self, name: &[u8], m: &mut ContentModel) -> i32
        requires
            old(self).wf(),
            old(m).ok(),
        ensures
            final(self).evolves(old(self)),
            final(m).ok(),
    {
        let open_nr = self.inputs.len();
        if self.cur() != b'(' {
            let msg = cat(&[b"xmlParseElementContentDecl : ", name, b" '(' expected\n"]);
            self.fatal_str(ERR_ELEMCONTENT_NOT_STARTED, &msg, Some(name));
            return -1;
        }
        self.next();
        self.skip_blanks_pe_balanced(open_nr);
        let (tree, res) = if self.cmp(b"#PCDATA") {
            (self.parse_mixed_content_decl(m, open_nr), ELEMENT_TYPE_MIXED)
        } else {
            (self.parse_children_content_decl(m, open_nr, 1), ELEMENT_TYPE_ELEMENT)
        };
        match tree {
            None => -1,
            Some(r) => {
                m.root = Some(r);
                self.skip_blanks_pe();
                res
            }
        }
    }

    /// `xmlParseElementDecl`.
    pub fn parse_element_decl(&mut self) -> i32
        requires
            old(self).wf(),
        ensures
            final(self).evolves(old(self)),
    {
        if self.cur() != b'<' || self.nxt(1) != b'!' {
            return -1;
        }
        self.skip(2);
        if !self.cmp(b"ELEMENT") {
            return -1;
        }
        let old_nr = self.inputs.len();
        self.skip(7);
        if self.skip_blanks_pe() == 0 {
            self.fatal_msg(ERR_SPACE_REQUIRED, b"Space required after 'ELEMENT'\n");
            return -1;
        }
        let name = match self.parse_name() {
            None => {
                self.fatal_msg(ERR_NAME_REQUIRED, b"xmlParseElementDecl: no name for Element\n");
                return -1;
            }
            Some(n) => n,
        };
        if self.skip_blanks_pe() == 0 {
            self.fatal_msg(ERR_SPACE_REQUIRED, b"Space required after the element name\n");
        }
        let mut model = ContentModel { nodes: Vec::new(), root: None };
        let ret;
        if self.cmp(b"EMPTY") {
            self.skip(5);
            ret = ELEMENT_TYPE_EMPTY;
        } else if self.cur() == b'A' && self.nxt(1) == b'N' && self.nxt(2) == b'Y' {
            self.skip(3);
            ret = ELEMENT_TYPE_ANY;
        } else if self.cur() == b'(' {
            ret = self.parse_element_content_decl(&name, &mut model);
            if ret <= 0 {
                return -1;
            }
        } else {
            self.fatal_msg(ERR_ELEMCONTENT_NOT_STARTED, b"xmlParseElementDecl: 'EMPTY', 'ANY' or '(' expected\n");
            return -1;
        }
        self.skip_blanks_pe();
        if self.cur() != b'>' {
            self.fatal(ERR_GT_REQUIRED, None);
        } else {
            if self.sink.validate() && self.inputs.len() > old_nr {
                self.validity_error(ERR_ENTITY_BOUNDARY, b"Element declaration doesn't start and stop in the same entity\n", None, None);
            }
            self.next();
            if self.sax_on() {
                self.sync();
                self.sink.element_decl(&name, ret, &model);
            }
        }
        ret
    }

    /// `xmlParseConditionalSections`.
    pub fn parse_conditional_sections(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).evolves(old(self)),
    {
        let mut depth: usize = 0;
        let mut fresh_pe = false;
        let old_nr = self.inputs.len();
        let mut decl_nr = self.inputs.len();
        while !self.stopped()
            invariant
                self.evolves(old(self)),
            decreases self.fuel,
        {
            if !self.step() {
                return;
            }
            let ghost f1 = self.fuel;
            if self.at_end() {
                if self.inputs.len() <= old_nr {
                    self.fatal(ERR_EXT_SUBSET_NOT_FINISHED, None);
                    return;
                }
                self.pop_pe();
                decl_nr = self.inputs.len();
            } else if self.cur() == b'<' && self.nxt(1) == b'!' && self.nxt(2) == b'[' {
                self.skip(3);
                self.skip_blanks_pe();
                fresh_pe = false;
                if self.cmp(b"INCLUDE") {
                    self.skip(7);
                    self.skip_blanks_pe();
                    if self.cur() != b'[' {
                        self.fatal(ERR_CONDSEC_INVALID, None);
                        return;
                    }
                    if self.sink.validate() && self.inputs.len() > decl_nr {
                        self.validity_error(ERR_ENTITY_BOUNDARY, condsec_bound(), None, None);
                    }
                    self.next();
                    depth = depth.saturating_add(1);
                } else if self.cmp(b"IGNORE") {
                    let mut ignore_depth: usize = 0;
                    self.skip(6);
                    self.skip_blanks_pe();
                    if self.cur() != b'[' {
                        self.fatal(ERR_CONDSEC_INVALID, None);
                        return;
                    }
                    if self.sink.validate() && self.inputs.len() > decl_nr {
                        self.validity_error(ERR_ENTITY_BOUNDARY, condsec_bound(), None, None);
                    }
                    self.next();
                    while !self.stopped()
                        invariant
                            self.evolves(old(self)),
                            self.fuel <= f1,
                        decreases self.fuel,
                    {
                        if !self.step() {
                            return;
                        }
                        if self.cur() == 0 {
                            self.fatal(ERR_CONDSEC_NOT_FINISHED, None);
                            return;
                        }
                        if self.cur() == b'<' && self.nxt(1) == b'!' && self.nxt(2) == b'[' {
                            self.skip(3);
                            ignore_depth = ignore_depth.saturating_add(1);
                        } else if self.cur() == b']' && self.nxt(1) == b']' && self.nxt(2) == b'>' {
                            self.skip(3);
                            if ignore_depth == 0 {
                                break;
                            }
                            ignore_depth = ignore_depth - 1;
                        } else {
                            self.next();
                        }
                    }
                    if self.sink.validate() && self.inputs.len() > decl_nr {
                        self.validity_error(ERR_ENTITY_BOUNDARY, condsec_bound(), None, None);
                    }
                } else {
                    self.fatal(ERR_CONDSEC_INVALID_KEYWORD, None);
                    return;
                }
            } else if depth > 0 && self.cur() == b']' && self.nxt(1) == b']' && self.nxt(2) == b'>' {
                if fresh_pe {
                    self.fatal_msg(ERR_CONDSEC_INVALID, b"Parameter entity must match extSubsetDecl\n");
                    return;
                }
                depth = depth - 1;
                if self.sink.validate() && self.inputs.len() > decl_nr {
                    self.validity_error(ERR_ENTITY_BOUNDARY, condsec_bound(), None, None);
                }
                self.skip(3);
            } else if self.cur() == b'<' && (self.nxt(1) == b'!' || self.nxt(1) == b'?') {
                fresh_pe = false;
                self.parse_markup_decl();
            } else if self.cur() == b'%' {
                self.parse_pe_ref_internal(true);
                if self.inputs.len() > decl_nr {
                    fresh_pe = true;
                    decl_nr = self.inputs.len();
                }
            } else {
                self.fatal(ERR_EXT_SUBSET_NOT_FINISHED, None);
                return;
            }
            if depth == 0 {
                break;
            }
            self.skip_blanks();
            self.shrink();
            self.grow();
        }
    }

    /// `xmlParseMarkupDecl`.
    pub fn parse_markup_decl(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).evolves(old(self)),
    {
        self.grow();
        if self.cur() != b'<' {
            return;
        }
        if self.nxt(1) == b'!' {
            let c = self.nxt(2);
            if c == b'E' {
                if self.nxt(3) == b'L' {
                    self.parse_element_decl();
                } else if self.nxt(3) == b'N' {
                    self.parse_entity_decl();
                } else {
                    self.skip(2);
                }
            } else if c == b'A' {
                self.parse_attribute_list_decl();
            } else if c == b'N' {
                self.parse_notation_decl();
            } else if c == b'-' {
                self.parse_comment();
            } else {
                let code = if self.sink.in_subset() == 2 { ERR_EXT_SUBSET_NOT_FINISHED } else { ERR_INT_SUBSET_NOT_FINISHED };
                self.fatal(code, None);
                self.skip(2);
            }
        } else if self.nxt(1) == b'?' {
            self.parse_pi();
        }
    }

    /// `xmlParseTextDecl`.
    pub fn parse_text_decl(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).evolves(old(self)),
            final(self).inputs@.len() == old(self).inputs@.len(),
    {
        if self.cmp(b"<?xml") && blank(self.nxt(5)) {
            self.skip(5);
        } else {
            self.fatal(ERR_XMLDECL_NOT_STARTED, None);
            return;
        }
        if self.skip_blanks() == 0 {
            self.fatal_msg(ERR_SPACE_REQUIRED, b"Space needed after '<?xml'\n");
        }
        let version = match self.parse_version_info() {
            None => crate::lenient::vec_of(b"1.0"),
            Some(v) => {
                if self.skip_blanks() == 0 {
                    self.fatal_msg(ERR_SPACE_REQUIRED, b"Space needed here\n");
                }
                v
            }
        };
        {
            let i = self.inp_mut();
            i.version = Some(version);
        }
        self.parse_encoding_decl();
        self.skip_blanks();
        if self.cur() == b'?' && self.nxt(1) == b'>' {
            self.skip(2);
        } else if self.cur() == b'>' {
            self.fatal(ERR_XMLDECL_NOT_FINISHED, None);
            self.next();
        } else {
            self.fatal(ERR_XMLDECL_NOT_FINISHED, None);
            let ghost n0 = self.inputs@.len();
            while !self.stopped()
                invariant
                    self.evolves(old(self)),
                    self.inputs@.len() == n0,
                decreases self.fuel,
            {
                if !self.step() {
                    break;
                }
                let c = self.cur();
                if c == 0 {
                    break;
                }
                self.next();
                if c == b'>' {
                    break;
                }
            }
        }
    }

    /// `xmlParseDocTypeDecl`.
    pub fn parse_doctype_decl(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).evolves(old(self)),
    {
        self.skip(9);
        if self.skip_blanks() == 0 {
            self.fatal_msg(ERR_SPACE_REQUIRED, b"Space required after 'DOCTYPE'\n");
        }
        let name = self.parse_name();
        if name.is_none() {
            self.fatal_msg(ERR_NAME_REQUIRED, b"xmlParseDocTypeDecl : no DOCTYPE name !\n");
        }
        self.int_sub_name = name.clone();
        self.skip_blanks();
        let (uri, public) = self.parse_external_id(true);
        if uri.is_some() || public.is_some() {
            self.sink.set_has_ext_subset(true);
        }
        self.ext_sub_uri = uri.clone();
        self.ext_sub_system = public.clone();
        self.sink.set_int_subset(opt_slice(&name), opt_slice(&public), opt_slice(&uri));
        self.skip_blanks();
        if self.sax_on() {
            self.sync();
            self.sink.internal_subset(opt_slice(&name), opt_slice(&public), opt_slice(&uri));
        }
        if self.cur() != b'[' && self.cur() != b'>' {
            self.fatal(ERR_DOCTYPE_NOT_FINISHED, None);
        }
    }

    /// `xmlParseInternalSubset`.
    pub fn parse_internal_subset(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).evolves(old(self)),
    {
        if self.cur() == b'[' {
            let old_nr = self.inputs.len();
            self.next();
            self.skip_blanks();
            loop
                invariant
                    self.evolves(old(self)),
                decreases self.fuel,
            {
                if !self.step() {
                    return;
                }
                if self.stopped() {
                    return;
                } else if self.at_end() {
                    if self.inputs.len() <= old_nr {
                        self.fatal(ERR_INT_SUBSET_NOT_FINISHED, None);
                        return;
                    }
                    self.pop_pe();
                } else if self.cur() == b']' && self.inputs.len() <= old_nr {
                    self.next();
                    self.skip_blanks();
                    break;
                } else if self.external() && self.cur() == b'<' && self.nxt(1) == b'!' && self.nxt(2) == b'[' {
                    self.parse_conditional_sections();
                } else if self.cur() == b'<' && (self.nxt(1) == b'!' || self.nxt(1) == b'?') {
                    self.parse_markup_decl();
                } else if self.cur() == b'%' {
                    self.parse_pe_ref_internal(true);
                } else {
                    self.fatal(ERR_INT_SUBSET_NOT_FINISHED, None);
                    self.pop_pes_to(old_nr);
                    return;
                }
                self.skip_blanks();
                self.shrink();
                self.grow();
            }
        }
        if self.cur() != b'>' {
            self.fatal(ERR_DOCTYPE_NOT_FINISHED, None);
            return;
        }
        self.next();
    }

    /// Pops parameter entities until `nr` inputs are left.
    pub fn pop_pes_to(&mut self, nr: usize)
        requires
            old(self).wf(),
        ensures
            final(self).evolves(old(self)),
    {
        while self.inputs.len() > nr
            invariant
                self.evolves(old(self)),
            decreases self.inputs@.len(),
        {
            let n = self.inputs.len();
            self.pop_pe();
            // Every input above the subset's is an entity's, so each
            // pop takes one.
            if self.inputs.len() >= n {
                break;
            }
        }
    }
}

/// A content node's links are to one of `len` nodes.
pub open spec fn node_ok(n: ContentNode, len: nat) -> bool {
    &&& n.c1 matches Some(k) ==> k < len
    &&& n.c2 matches Some(k) ==> k < len
    &&& n.parent matches Some(k) ==> k < len
}

impl ContentModel {
    /// Every link of the model is to one of its nodes.
    pub open spec fn ok(&self) -> bool {
        &&& self.root matches Some(r) ==> r < self.nodes@.len()
        &&& forall|i: int| 0 <= i < self.nodes@.len() ==> #[trigger] node_ok(self.nodes@[i], self.nodes@.len())
    }

    pub open spec fn link_ok(&self, o: Option<usize>) -> bool {
        o matches Some(k) ==> k < self.nodes@.len()
    }

    pub fn add(&mut self, ctype: i32, name: Option<Vec<u8>>) -> (r: usize)
        requires
            old(self).ok(),
        ensures
            final(self).ok(),
            final(self).nodes@.len() == old(self).nodes@.len() + 1,
            r == old(self).nodes@.len(),
    {
        // xmlNewDocElementContent splits a QName: prefix and local name.
        let (prefix, local) = match name {
            None => (None, None),
            Some(n) => match split_qname3(&n) {
                Some((p, l)) => (Some(crate::lenient::vec_of(p)), Some(crate::lenient::vec_of(l))),
                None => (None, Some(n)),
            },
        };
        let ghost old_nodes = self.nodes@;
        self.nodes.push(ContentNode { ctype, ocur: OCUR_ONCE, name: local, prefix, c1: None, c2: None, parent: None });
        proof {
            assert forall|i: int| 0 <= i < self.nodes@.len() implies #[trigger] node_ok(self.nodes@[i], self.nodes@.len()) by {
                if i < old_nodes.len() {
                    assert(self.nodes@[i] == old_nodes[i]);
                    assert(node_ok(old_nodes[i], old_nodes.len()));
                }
            }
        }
        self.nodes.len() - 1
    }

    /// Sets a node's occurrence.
    pub fn set_ocur(&mut self, n: usize, o: i32)
        requires
            old(self).ok(),
            n < old(self).nodes@.len(),
        ensures
            final(self).ok(),
            final(self).nodes@.len() == old(self).nodes@.len(),
    {
        let ghost old_nodes = self.nodes@;
        self.nodes[n].ocur = o;
        proof {
            assert forall|i: int| 0 <= i < self.nodes@.len() implies #[trigger] node_ok(self.nodes@[i], self.nodes@.len()) by {
                if i != n {
                    assert(self.nodes@[i] == old_nodes[i]);
                    assert(node_ok(old_nodes[i], old_nodes.len()));
                } else {
                    assert(node_ok(old_nodes[i], old_nodes.len()));
                }
            }
        }
    }

    /// Sets a node's first child.
    pub fn set_c1(&mut self, n: usize, c: Option<usize>)
        requires
            old(self).ok(),
            n < old(self).nodes@.len(),
            old(self).link_ok(c),
        ensures
            final(self).ok(),
            final(self).nodes@.len() == old(self).nodes@.len(),
    {
        let ghost old_nodes = self.nodes@;
        self.nodes[n].c1 = c;
        proof {
            assert forall|i: int| 0 <= i < self.nodes@.len() implies #[trigger] node_ok(self.nodes@[i], self.nodes@.len()) by {
                if i != n {
                    assert(self.nodes@[i] == old_nodes[i]);
                    assert(node_ok(old_nodes[i], old_nodes.len()));
                } else {
                    assert(node_ok(old_nodes[i], old_nodes.len()));
                }
            }
        }
    }

    /// Sets a node's second child.
    pub fn set_c2(&mut self, n: usize, c: Option<usize>)
        requires
            old(self).ok(),
            n < old(self).nodes@.len(),
            old(self).link_ok(c),
        ensures
            final(self).ok(),
            final(self).nodes@.len() == old(self).nodes@.len(),
    {
        let ghost old_nodes = self.nodes@;
        self.nodes[n].c2 = c;
        proof {
            assert forall|i: int| 0 <= i < self.nodes@.len() implies #[trigger] node_ok(self.nodes@[i], self.nodes@.len()) by {
                if i != n {
                    assert(self.nodes@[i] == old_nodes[i]);
                    assert(node_ok(old_nodes[i], old_nodes.len()));
                } else {
                    assert(node_ok(old_nodes[i], old_nodes.len()));
                }
            }
        }
    }

    /// Sets a node's parent.
    pub fn set_parent(&mut self, n: usize, c: Option<usize>)
        requires
            old(self).ok(),
            n < old(self).nodes@.len(),
            old(self).link_ok(c),
        ensures
            final(self).ok(),
            final(self).nodes@.len() == old(self).nodes@.len(),
    {
        let ghost old_nodes = self.nodes@;
        self.nodes[n].parent = c;
        proof {
            assert forall|i: int| 0 <= i < self.nodes@.len() implies #[trigger] node_ok(self.nodes@[i], self.nodes@.len()) by {
                if i != n {
                    assert(self.nodes@[i] == old_nodes[i]);
                    assert(node_ok(old_nodes[i], old_nodes.len()));
                } else {
                    assert(node_ok(old_nodes[i], old_nodes.len()));
                }
            }
        }
    }

    /// Makes an optional or repeated particle once; whether it was.
    fn once_if_opt(&mut self, n: Option<usize>, _plus: bool) -> bool
        requires
            old(self).ok(),
            old(self).link_ok(n),
        ensures
            final(self).ok(),
            final(self).nodes@.len() == old(self).nodes@.len(),
    {
        match n {
            Some(i) => {
                let o = self.nodes[i].ocur;
                if o == OCUR_OPT || o == OCUR_MULT {
                    self.set_ocur(i, OCUR_ONCE);
                    return true;
                }
            }
            None => {}
        }
        false
    }
}

} // verus!
