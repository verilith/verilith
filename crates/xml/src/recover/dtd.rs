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

/// `xmlAttrNormalizeSpace`, in place.
#[verifier::external_body]
pub fn attr_normalize_space(v: &mut Vec<u8>) {
    *v = crate::lenient::attr_normalize_space(v);
}

impl<S: Sink> Parser<S> {
    /// `xmlParseSystemLiteral`.
    #[verifier::external_body]
    pub fn parse_system_literal(&mut self) -> Option<Vec<u8>> {
        let max = if self.options & PARSE_HUGE != 0 { MAX_TEXT_LENGTH } else { MAX_NAME_LENGTH };
        let stop = match self.cur() {
            b'"' => b'"',
            b'\'' => b'\'',
            _ => {
                self.fatal(ERR_LITERAL_NOT_STARTED, None);
                return None;
            }
        };
        self.next();
        let mut buf: Vec<u8> = Vec::new();
        let mut size = PARSER_BUFFER_SIZE;
        let (mut c, mut l) = self.current_char_recover();
        while is_char(c) && c != stop as u32 {
            if buf.len() + 5 >= size {
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
            (c, l) = self.current_char_recover();
        }
        if !is_char(c) {
            self.fatal(ERR_LITERAL_NOT_FINISHED, None);
        } else {
            self.next();
        }
        Some(buf)
    }

    /// `xmlParsePubidLiteral`.
    #[verifier::external_body]
    pub fn parse_pubid_literal(&mut self) -> Option<Vec<u8>> {
        let max = if self.options & PARSE_HUGE != 0 { MAX_TEXT_LENGTH } else { MAX_NAME_LENGTH };
        let stop = match self.cur() {
            b'"' => b'"',
            b'\'' => b'\'',
            _ => {
                self.fatal(ERR_LITERAL_NOT_STARTED, None);
                return None;
            }
        };
        self.next();
        let mut buf: Vec<u8> = Vec::new();
        let mut size = PARSER_BUFFER_SIZE;
        let mut c = self.cur();
        while is_pubid_char(c) && c != stop && !self.stopped() {
            if buf.len() + 1 >= size {
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
    #[verifier::external_body]
    pub fn parse_external_id(&mut self, strict: bool) -> (Option<Vec<u8>>, Option<Vec<u8>>) {
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
    #[verifier::external_body]
    fn parse_comment_complex(&mut self, mut buf: Vec<u8>, mut size: usize) {
        let max = self.max_length(MAX_TEXT_LENGTH);
        let (mut q, mut ql) = self.current_char_recover();
        if q == 0 {
            self.fatal_str(ERR_COMMENT_NOT_FINISHED, b"Comment not terminated\n", None);
            return;
        }
        if !is_char(q) {
            let m = cat(&[b"xmlParseComment: invalid xmlChar value ", &itoa(q as i64), b"\n"]);
            self.fatal_int(ERR_INVALID_CHAR, &m, q as i32);
            return;
        }
        self.nextl(ql);
        let (mut r, mut rl) = self.current_char_recover();
        if r == 0 {
            self.fatal_str(ERR_COMMENT_NOT_FINISHED, b"Comment not terminated\n", None);
            return;
        }
        if !is_char(r) {
            let m = cat(&[b"xmlParseComment: invalid xmlChar value ", &itoa(r as i64), b"\n"]);
            self.fatal_int(ERR_INVALID_CHAR, &m, r as i32);
            return;
        }
        self.nextl(rl);
        let (mut cur, mut l) = self.current_char_recover();
        if cur == 0 {
            self.fatal_str(ERR_COMMENT_NOT_FINISHED, b"Comment not terminated\n", None);
            return;
        }
        while is_char(cur) && (cur != b'>' as u32 || r != b'-' as u32 || q != b'-' as u32) {
            if r == b'-' as u32 && q == b'-' as u32 {
                self.fatal(ERR_HYPHEN_IN_COMMENT, None);
            }
            if buf.len() + 5 >= size {
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
            ql = rl;
            r = cur;
            rl = l;
            self.nextl(l);
            (cur, l) = self.current_char_recover();
        }
        let _ = (ql, rl);
        if cur == 0 {
            let m = cat(&[b"Comment not terminated \n<!--", prefix_n(&buf, 50), b"\n"]);
            self.fatal_str(ERR_COMMENT_NOT_FINISHED, &m, Some(&buf));
        } else if !is_char(cur) {
            let m = cat(&[b"xmlParseComment: invalid xmlChar value ", &itoa(cur as i64), b"\n"]);
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
    #[verifier::external_body]
    pub fn parse_comment(&mut self) {
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
        let mut buf: Option<Vec<u8>> = None;
        let mut size: usize = PARSER_BUFFER_SIZE;
        let mut p = self.inp().cur;
        let b = |s: &Self, k: usize| at(&s.inp().buf, k);
        loop {
            if !self.step() {
                return;
            }
            if b(self, p) == 0x0A {
                while b(self, p) == 0x0A {
                    let i = self.inp_mut();
                    i.line = sat_add_i32(i.line, 1);
                    i.col = 1;
                    p += 1;
                }
            }
            // get_more:
            loop {
                let mut ccol = self.inp().col;
                loop {
                    let c = b(self, p);
                    if (c > b'-' && c <= 0x7F) || (c >= 0x20 && c < b'-') || c == 0x09 {
                        p += 1;
                        ccol = sat_add_i32(ccol, 1);
                    } else {
                        break;
                    }
                }
                self.inp_mut().col = ccol;
                if b(self, p) == 0x0A {
                    while b(self, p) == 0x0A {
                        let i = self.inp_mut();
                        i.line = sat_add_i32(i.line, 1);
                        i.col = 1;
                        p += 1;
                    }
                    continue;
                }
                let start = self.inp().cur;
                let nbchar = p - start;
                if nbchar > 0 {
                    let len = buf.as_ref().map_or(0, |v| v.len());
                    if nbchar > max - len {
                        self.fatal_str(ERR_COMMENT_NOT_FINISHED, b"Comment too big found", None);
                        return;
                    }
                    match buf.as_mut() {
                        None => {
                            size = if b(self, p) == b'-' && b(self, p + 1) == b'-' { nbchar + 1 } else { PARSER_BUFFER_SIZE + nbchar };
                            buf = Some(self.slice(start, p));
                        }
                        Some(v) => {
                            if v.len() + nbchar + 1 >= size {
                                size += v.len() + nbchar + PARSER_BUFFER_SIZE;
                            }
                            let t = &self.inputs[self.inputs.len() - 1].buf;
                            let to = if p < t.len() { p } else { t.len() };
                            if start < to {
                                v.extend_from_slice(&t[start..to]);
                            }
                        }
                    }
                }
                self.inp_mut().cur = p;
                if b(self, p) == 0x0A {
                    p += 1;
                    let i = self.inp_mut();
                    i.line = sat_add_i32(i.line, 1);
                    i.col = 1;
                }
                if b(self, p) == 0x0D {
                    p += 1;
                    if b(self, p) == 0x0A {
                        self.inp_mut().cur = p;
                        p += 1;
                        let i = self.inp_mut();
                        i.line = sat_add_i32(i.line, 1);
                        i.col = 1;
                        continue;
                    }
                    // `in--`: p is reloaded from cur below.
                }
                self.shrink();
                self.grow();
                p = self.inp().cur;
                if b(self, p) == b'-' {
                    if b(self, p + 1) == b'-' {
                        if b(self, p + 2) == b'>' {
                            self.skip(3);
                            if self.sax_on() {
                                self.sync();
                                match buf.as_ref() {
                                    Some(v) => {
                                        let v = v.clone();
                                        self.sink.comment(&v);
                                    }
                                    None => self.sink.comment(b""),
                                }
                            }
                            return;
                        }
                        match buf.as_ref() {
                            Some(v) => {
                                let v = v.clone();
                                let m = cat(&[b"Double hyphen within comment: <!--", prefix_n(&v, 50), b"\n"]);
                                self.fatal_str(ERR_HYPHEN_IN_COMMENT, &m, Some(&v));
                            }
                            None => self.fatal_str(ERR_HYPHEN_IN_COMMENT, b"Double hyphen within comment\n", None),
                        }
                        p += 1;
                        let i = self.inp_mut();
                        i.col = sat_add_i32(i.col, 1);
                    }
                    p += 1;
                    let i = self.inp_mut();
                    i.col = sat_add_i32(i.col, 1);
                    continue;
                }
                break;
            }
            let c = b(self, p);
            if !((0x20..=0x7F).contains(&c) || c == 0x09 || c == 0x0A) {
                break;
            }
        }
        let v = match buf {
            Some(v) => v,
            None => {
                size = PARSER_BUFFER_SIZE;
                Vec::new()
            }
        };
        self.parse_comment_complex(v, size);
    }

    /// `xmlParsePITarget`.
    #[verifier::external_body]
    pub fn parse_pi_target(&mut self) -> Option<Vec<u8>> {
        let name = self.parse_name();
        if let Some(n) = name.as_ref() {
            if n.len() >= 3 && (n[0] == b'x' || n[0] == b'X') && (n[1] == b'm' || n[1] == b'M') && (n[2] == b'l' || n[2] == b'L') {
                if n.as_slice() == b"xml" {
                    self.fatal_msg(ERR_RESERVED_XML_NAME, b"XML declaration allowed only at the start of the document\n");
                    return name;
                } else if n.len() == 3 {
                    self.fatal(ERR_RESERVED_XML_NAME, None);
                    return name;
                }
                if n.as_slice() == b"xml-stylesheet" || n.as_slice() == b"xml-model" {
                    return name;
                }
                self.warning(ERR_RESERVED_XML_NAME, b"xmlParsePITarget: invalid name prefix 'xml'\n", None, None);
            }
            if n.contains(&b':') {
                let n = n.clone();
                let m = cat(&[b"colons are forbidden from PI names '", &n, b"'\n"]);
                self.ns_err(NS_ERR_COLON, &m, Some(&n), None, None);
            }
        }
        name
    }

    /// `xmlParsePI`.
    #[verifier::external_body]
    pub fn parse_pi(&mut self) {
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
            let m = cat(&[b"ParsePI: PI ", &target, b" space expected\n"]);
            self.fatal_str(ERR_SPACE_REQUIRED, &m, Some(&target));
        }
        let (mut c, mut l) = self.current_char_recover();
        while is_char(c) && (c != b'?' as u32 || self.nxt(1) != b'>') {
            if buf.len() + 5 >= size {
                match grow_capacity(size, max) {
                    None => {
                        let m = cat(&[b"PI ", &target, b" too big found"]);
                        self.fatal_str(ERR_PI_NOT_FINISHED, &m, Some(&target));
                        return;
                    }
                    Some(n) => size = n,
                }
            }
            push_char(&mut buf, c);
            self.nextl(l);
            (c, l) = self.current_char_recover();
        }
        if c != b'?' as u32 {
            let m = cat(&[b"ParsePI: PI ", &target, b" never end ...\n"]);
            self.fatal_str(ERR_PI_NOT_FINISHED, &m, Some(&target));
        } else {
            self.skip(2);
            if self.sax_on() {
                self.sync();
                self.sink.processing_instruction(&target, Some(&buf));
            }
        }
    }

    /// `xmlParseNotationDecl`.
    #[verifier::external_body]
    pub fn parse_notation_decl(&mut self) {
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
        if name.contains(&b':') {
            let m = cat(&[b"colons are forbidden from notation names '", &name, b"'\n"]);
            self.ns_err(NS_ERR_COLON, &m, Some(&name), None, None);
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
                self.sink.notation_decl(&name, public.as_deref(), system.as_deref());
            }
        } else {
            self.fatal(ERR_NOTATION_NOT_FINISHED, None);
        }
    }

    /// `xmlParseEntityDecl`.
    #[verifier::external_body]
    pub fn parse_entity_decl(&mut self) {
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
        if name.contains(&b':') {
            let m = cat(&[b"colons are forbidden from entities names '", &name, b"'\n"]);
            self.ns_err(NS_ERR_COLON, &m, Some(&name), None, None);
        }
        if self.skip_blanks_pe() == 0 {
            self.fatal_msg(ERR_SPACE_REQUIRED, b"Space required after the entity name\n");
        }
        if is_param {
            if self.cur() == b'"' || self.cur() == b'\'' {
                let (value, o) = self.parse_entity_value();
                orig = o;
                if let Some(v) = value.as_ref() {
                    if self.sax_on() {
                        self.sync();
                        self.sink.entity_decl(&name, INTERNAL_PARAMETER_ENTITY, None, None, Some(v));
                    }
                }
            } else {
                let (uri, literal) = self.parse_external_id(true);
                if uri.is_none() && literal.is_none() {
                    self.fatal(ERR_VALUE_REQUIRED, None);
                }
                if let Some(u) = uri.as_ref() {
                    if u.contains(&b'#') {
                        self.fatal(ERR_URI_FRAGMENT, None);
                    } else if self.sax_on() {
                        self.sync();
                        self.sink.entity_decl(&name, EXTERNAL_PARAMETER_ENTITY, literal.as_deref(), Some(u), None);
                    }
                }
            }
        } else {
            if self.cur() == b'"' || self.cur() == b'\'' {
                let (value, o) = self.parse_entity_value();
                orig = o;
                if self.sax_on() {
                    self.sync();
                    self.sink.entity_decl(&name, INTERNAL_GENERAL_ENTITY, None, None, value.as_deref());
                }
                self.sink.compat_entity_decl(&name, INTERNAL_GENERAL_ENTITY, None, None, value.as_deref());
            } else {
                let (uri, literal) = self.parse_external_id(true);
                if uri.is_none() && literal.is_none() {
                    self.fatal(ERR_VALUE_REQUIRED, None);
                }
                if let Some(u) = uri.as_ref() {
                    if u.contains(&b'#') {
                        self.fatal(ERR_URI_FRAGMENT, None);
                    }
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
                        self.sink.unparsed_entity_decl(&name, literal.as_deref(), uri.as_deref(), ndata.as_deref());
                    }
                } else {
                    if self.sax_on() {
                        self.sync();
                        self.sink.entity_decl(&name, EXTERNAL_GENERAL_PARSED_ENTITY, literal.as_deref(), uri.as_deref(), None);
                    }
                    if self.replace_entities {
                        self.sink.compat_entity_decl(&name, EXTERNAL_GENERAL_PARSED_ENTITY, literal.as_deref(), uri.as_deref(), None);
                    }
                }
            }
        }
        self.skip_blanks_pe();
        if self.cur() != b'>' {
            let m = cat(&[b"xmlParseEntityDecl: entity ", &name, b" not terminated\n"]);
            self.fatal_str(ERR_ENTITY_NOT_FINISHED, &m, Some(&name));
        } else {
            if self.sink.validate() && self.inputs.len() > old_nr {
                self.validity_error(ERR_ENTITY_BOUNDARY, b"Entity declaration doesn't start and stop in the same entity\n", None, None);
            }
            self.next();
        }
        if let Some(o) = orig {
            self.sink.entity_orig(is_param, &name, &o);
        }
    }

    /// `xmlParseDefaultDecl`: the default kind and value.
    #[verifier::external_body]
    pub fn parse_default_decl(&mut self) -> (i32, Option<Vec<u8>>) {
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
    #[verifier::external_body]
    pub fn parse_notation_type(&mut self) -> Option<Vec<Vec<u8>>> {
        if self.cur() != b'(' {
            self.fatal(ERR_NOTATION_NOT_STARTED, None);
            return None;
        }
        let mut ret: Vec<Vec<u8>> = Vec::new();
        loop {
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
            if self.sink.validate() && ret.contains(&name) {
                let m = cat(&[b"standalone: attribute notation value token ", &name, b" duplicated\n"]);
                self.validity_error(DTD_DUP_TOKEN, &m, Some(&name), None);
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
    #[verifier::external_body]
    pub fn parse_enumeration_type(&mut self) -> Option<Vec<Vec<u8>>> {
        if self.cur() != b'(' {
            self.fatal(ERR_ATTLIST_NOT_STARTED, None);
            return None;
        }
        let mut ret: Vec<Vec<u8>> = Vec::new();
        loop {
            if !self.step() {
                return None;
            }
            self.next();
            self.skip_blanks_pe();
            let name = match self.parse_nmtoken() {
                None => {
                    self.fatal(ERR_NMTOKEN_REQUIRED, None);
                    return if ret.is_empty() { None } else { Some(ret) };
                }
                Some(n) => n,
            };
            let mut dup = false;
            if self.sink.validate() && ret.contains(&name) {
                let m = cat(&[b"standalone: attribute enumeration value token ", &name, b" duplicated\n"]);
                self.validity_error(DTD_DUP_TOKEN, &m, Some(&name), None);
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
            return if ret.is_empty() { None } else { Some(ret) };
        }
        self.next();
        if ret.is_empty() { None } else { Some(ret) }
    }

    /// `xmlParseEnumeratedType`.
    #[verifier::external_body]
    pub fn parse_enumerated_type(&mut self) -> (i32, Option<Vec<Vec<u8>>>) {
        if self.cmp(b"NOTATION") {
            self.skip(8);
            if self.skip_blanks_pe() == 0 {
                self.fatal_msg(ERR_SPACE_REQUIRED, b"Space required after 'NOTATION'\n");
                return (0, None);
            }
            let t = self.parse_notation_type();
            if t.as_ref().is_none_or(|v| v.is_empty()) {
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
    #[verifier::external_body]
    pub fn parse_attribute_type(&mut self) -> (i32, Option<Vec<Vec<u8>>>) {
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
    #[verifier::external_body]
    pub fn parse_attribute_list_decl(&mut self) {
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
        while self.cur() != b'>' && !self.stopped() {
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
            let (def, mut default) = self.parse_default_decl();
            if def <= 0 {
                break;
            }
            if atype != ATTRIBUTE_CDATA {
                if let Some(v) = default.as_mut() {
                    attr_normalize_space(v);
                }
            }
            self.grow();
            if self.cur() != b'>' && self.skip_blanks_pe() == 0 {
                self.fatal_msg(ERR_SPACE_REQUIRED, b"Space required after the attribute default value\n");
                break;
            }
            if self.sax_on() {
                self.sync();
                self.sink.attribute_decl(&elem, &attr, atype, def, default.as_deref(), tree);
            }
            if self.sax2 && def != ATTRIBUTE_IMPLIED && def != ATTRIBUTE_REQUIRED {
                if let Some(v) = default.as_ref() {
                    let v = v.clone();
                    self.add_def_attrs(&elem, &attr, &v);
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
    #[verifier::external_body]
    pub fn add_def_attrs(&mut self, fullname: &[u8], fullattr: &[u8], value: &[u8]) {
        if self.special_lookup(fullname, fullattr).is_some() {
            return;
        }
        let (eprefix, ename) = match split_qname3(fullname) {
            None => (None, fullname.to_vec()),
            Some((p, l)) => (Some(p.to_vec()), l.to_vec()),
        };
        let (aprefix, aname) = match split_qname3(fullattr) {
            None => (None, fullattr.to_vec()),
            Some((p, l)) => (Some(p.to_vec()), l.to_vec()),
        };
        let mut expanded = aname.len() as u64;
        if let Some(p) = aprefix.as_ref() {
            expanded += p.len() as u64;
        }
        expanded += value.len() as u64;
        let external = self.external();
        let d = DefAttr { prefix: aprefix, name: aname, value: value.to_vec(), external, expanded_size: expanded };
        let key = (ename, eprefix);
        let mut k = 0;
        while k < self.atts_default.len() {
            if self.atts_default[k].0 == key {
                self.atts_default[k].1.push(d);
                return;
            }
            k += 1;
        }
        self.atts_default.push((key, vec![d]));
    }

    #[verifier::external_body]
    pub fn special_lookup(&self, elem: &[u8], attr: &[u8]) -> Option<i32> {
        let mut k = 0;
        while k < self.atts_special.len() {
            let e = &self.atts_special[k];
            if e.0 .0 == elem && e.0 .1 == attr {
                return Some(e.1);
            }
            k += 1;
        }
        None
    }

    /// `xmlAddSpecialAttr` (`xmlHashAdd2`: the first declaration stays).
    #[verifier::external_body]
    pub fn add_special_attr(&mut self, elem: &[u8], attr: &[u8], atype: i32) {
        let t = if self.external() { atype | SPECIAL_EXTERNAL } else { atype };
        if self.special_lookup(elem, attr).is_none() {
            self.atts_special.push(((elem.to_vec(), attr.to_vec()), t));
        }
    }

    /// `xmlCleanSpecialAttr`.
    #[verifier::external_body]
    pub fn clean_special_attr(&mut self) {
        self.atts_special.retain(|e| e.1 != ATTRIBUTE_CDATA);
    }

    /// `xmlPopPE`.
    #[verifier::external_body]
    pub fn pop_pe(&mut self) {
        let ent = match self.inp().entity {
            None => return,
            Some(e) => e,
        };
        let info = self.sink.ent_info(ent);
        self.sink.ent_set_flags(ent, info.flags & !ENT_EXPANDING);
        if info.flags & ENT_CHECKED == 0 {
            loop {
                {
                    let i = self.inp_mut();
                    i.cur = i.buf.len();
                }
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
    #[verifier::external_body]
    pub fn skip_blanks_pe(&mut self) -> usize {
        let mut res: usize = 0;
        let mut in_param = self.in_pe();
        let mut expand = self.external();
        if !in_param && !expand {
            return self.skip_blanks();
        }
        while !self.stopped() {
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
    #[verifier::external_body]
    fn skip_blanks_pe_balanced(&mut self, open_nr: usize) {
        self.skip_blanks();
        self.grow();
        if !self.external() && !self.in_pe() {
            return;
        }
        while !self.stopped() {
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

    #[verifier::external_body]
    fn content_boundary(&mut self, open_nr: usize) {
        if self.sink.validate() && self.inputs.len() > open_nr {
            self.validity_error(ERR_ENTITY_BOUNDARY, b"Element content declaration doesn't start and stop in the same entity\n", None, None);
        }
    }

    /// `xmlParseElementMixedContentDecl`.
    #[verifier::external_body]
    pub fn parse_mixed_content_decl(&mut self, m: &mut ContentModel, open_nr: usize) -> Option<usize> {
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
                m.nodes[r].ocur = OCUR_MULT;
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
        while self.cur() == b'|' && !self.stopped() {
            if !self.step() {
                return None;
            }
            self.next();
            let n = m.add(CONTENT_OR, None);
            match elem.take() {
                None => {
                    m.nodes[n].c1 = cur;
                    if let Some(c) = cur {
                        m.nodes[c].parent = Some(n);
                    }
                    ret = Some(n);
                    cur = Some(n);
                }
                Some(e) => {
                    let c = cur.unwrap_or(n);
                    m.nodes[c].c2 = Some(n);
                    m.nodes[n].parent = Some(c);
                    let leaf = m.add(CONTENT_ELEMENT, Some(e));
                    m.nodes[n].c1 = Some(leaf);
                    m.nodes[leaf].parent = Some(n);
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
            if let Some(e) = elem {
                if let Some(c) = cur {
                    let leaf = m.add(CONTENT_ELEMENT, Some(e));
                    m.nodes[c].c2 = Some(leaf);
                    m.nodes[leaf].parent = Some(c);
                }
            }
            if let Some(r) = ret {
                m.nodes[r].ocur = OCUR_MULT;
            }
            self.content_boundary(open_nr);
            self.skip(2);
        } else {
            self.fatal(ERR_MIXED_NOT_STARTED, None);
            return None;
        }
        ret
    }

    #[verifier::external_body]
    fn content_ocur(&mut self, m: &mut ContentModel, n: usize) {
        let o = match self.cur() {
            b'?' => OCUR_OPT,
            b'*' => OCUR_MULT,
            b'+' => OCUR_PLUS,
            _ => OCUR_ONCE,
        };
        m.nodes[n].ocur = o;
        if o != OCUR_ONCE {
            self.next();
        }
    }

    /// `xmlParseElementChildrenContentDeclPriv`.
    #[verifier::external_body]
    pub fn parse_children_content_decl(&mut self, m: &mut ContentModel, open_nr: usize, depth: i32) -> Option<usize> {
        let max_depth = if self.options & PARSE_HUGE != 0 { 2048 } else { 256 };
        if depth > max_depth {
            let msg = cat(&[b"xmlParseElementChildrenContentDecl : depth ", &itoa(depth as i64), b" too deep, use XML_PARSE_HUGE\n"]);
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
            ret = self.parse_children_content_decl(m, nr, depth + 1)?;
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
        while !self.stopped() {
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
                    let msg = cat(&[b"xmlParseElementChildrenContentDecl : '", &[typ], b"' expected\n"]);
                    self.fatal_int(ERR_SEPARATOR_REQUIRED, &msg, typ as i32);
                    return None;
                }
                self.next();
                let op = m.add(if c == b',' { CONTENT_SEQ } else { CONTENT_OR }, None);
                match last {
                    None => {
                        m.nodes[op].c1 = Some(ret);
                        m.nodes[ret].parent = Some(op);
                        ret = op;
                        cur = op;
                    }
                    Some(l) => {
                        m.nodes[cur].c2 = Some(op);
                        m.nodes[op].parent = Some(cur);
                        m.nodes[op].c1 = Some(l);
                        m.nodes[l].parent = Some(op);
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
                last = Some(self.parse_children_content_decl(m, nr, depth + 1)?);
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
        if let Some(l) = last {
            m.nodes[cur].c2 = Some(l);
            m.nodes[l].parent = Some(cur);
        }
        self.content_boundary(open_nr);
        self.next();
        match self.cur() {
            b'?' => {
                let o = m.nodes[ret].ocur;
                m.nodes[ret].ocur = if o == OCUR_PLUS || o == OCUR_MULT { OCUR_MULT } else { OCUR_OPT };
                self.next();
            }
            b'*' => {
                m.nodes[ret].ocur = OCUR_MULT;
                let mut c = Some(ret);
                while let Some(ci) = c {
                    if m.nodes[ci].ctype != CONTENT_OR {
                        break;
                    }
                    m.once_if_opt(m.nodes[ci].c1, false);
                    m.once_if_opt(m.nodes[ci].c2, false);
                    c = m.nodes[ci].c2;
                }
                self.next();
            }
            b'+' => {
                let o = m.nodes[ret].ocur;
                m.nodes[ret].ocur = if o == OCUR_OPT || o == OCUR_MULT { OCUR_MULT } else { OCUR_PLUS };
                // libxml2 walks from `cur` here, not from `ret`.
                let mut found = false;
                let mut c = Some(cur);
                while let Some(ci) = c {
                    if m.nodes[ci].ctype != CONTENT_OR {
                        break;
                    }
                    found |= m.once_if_opt(m.nodes[ci].c1, true);
                    found |= m.once_if_opt(m.nodes[ci].c2, true);
                    c = m.nodes[ci].c2;
                }
                if found {
                    m.nodes[ret].ocur = OCUR_MULT;
                }
                self.next();
            }
            _ => {}
        }
        Some(ret)
    }

    /// `xmlParseElementContentDecl`.
    #[verifier::external_body]
    pub fn parse_element_content_decl(&mut self, name: &[u8], m: &mut ContentModel) -> i32 {
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
    #[verifier::external_body]
    pub fn parse_element_decl(&mut self) -> i32 {
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
        let mut model = ContentModel::default();
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
    #[verifier::external_body]
    pub fn parse_conditional_sections(&mut self) {
        let mut depth: usize = 0;
        let mut fresh_pe = false;
        let old_nr = self.inputs.len();
        let mut decl_nr = self.inputs.len();
        let bound = b"All markup of the conditional section is not in the same entity\n";
        while !self.stopped() {
            if !self.step() {
                return;
            }
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
                        self.validity_error(ERR_ENTITY_BOUNDARY, bound, None, None);
                    }
                    self.next();
                    depth += 1;
                } else if self.cmp(b"IGNORE") {
                    let mut ignore_depth: usize = 0;
                    self.skip(6);
                    self.skip_blanks_pe();
                    if self.cur() != b'[' {
                        self.fatal(ERR_CONDSEC_INVALID, None);
                        return;
                    }
                    if self.sink.validate() && self.inputs.len() > decl_nr {
                        self.validity_error(ERR_ENTITY_BOUNDARY, bound, None, None);
                    }
                    self.next();
                    while !self.stopped() {
                        if self.cur() == 0 {
                            self.fatal(ERR_CONDSEC_NOT_FINISHED, None);
                            return;
                        }
                        if self.cur() == b'<' && self.nxt(1) == b'!' && self.nxt(2) == b'[' {
                            self.skip(3);
                            ignore_depth += 1;
                        } else if self.cur() == b']' && self.nxt(1) == b']' && self.nxt(2) == b'>' {
                            self.skip(3);
                            if ignore_depth == 0 {
                                break;
                            }
                            ignore_depth -= 1;
                        } else {
                            self.next();
                        }
                    }
                    if self.sink.validate() && self.inputs.len() > decl_nr {
                        self.validity_error(ERR_ENTITY_BOUNDARY, bound, None, None);
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
                depth -= 1;
                if self.sink.validate() && self.inputs.len() > decl_nr {
                    self.validity_error(ERR_ENTITY_BOUNDARY, bound, None, None);
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
    #[verifier::external_body]
    pub fn parse_markup_decl(&mut self) {
        self.grow();
        if self.cur() != b'<' {
            return;
        }
        if self.nxt(1) == b'!' {
            match self.nxt(2) {
                b'E' => {
                    if self.nxt(3) == b'L' {
                        self.parse_element_decl();
                    } else if self.nxt(3) == b'N' {
                        self.parse_entity_decl();
                    } else {
                        self.skip(2);
                    }
                }
                b'A' => self.parse_attribute_list_decl(),
                b'N' => self.parse_notation_decl(),
                b'-' => self.parse_comment(),
                _ => {
                    let code = if self.sink.in_subset() == 2 { ERR_EXT_SUBSET_NOT_FINISHED } else { ERR_INT_SUBSET_NOT_FINISHED };
                    self.fatal(code, None);
                    self.skip(2);
                }
            }
        } else if self.nxt(1) == b'?' {
            self.parse_pi();
        }
    }

    /// `xmlParseTextDecl`.
    #[verifier::external_body]
    pub fn parse_text_decl(&mut self) {
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
            None => b"1.0".to_vec(),
            Some(v) => {
                if self.skip_blanks() == 0 {
                    self.fatal_msg(ERR_SPACE_REQUIRED, b"Space needed here\n");
                }
                v
            }
        };
        self.inp_mut().version = Some(version);
        self.parse_encoding_decl();
        self.skip_blanks();
        if self.cur() == b'?' && self.nxt(1) == b'>' {
            self.skip(2);
        } else if self.cur() == b'>' {
            self.fatal(ERR_XMLDECL_NOT_FINISHED, None);
            self.next();
        } else {
            self.fatal(ERR_XMLDECL_NOT_FINISHED, None);
            while !self.stopped() {
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
    #[verifier::external_body]
    pub fn parse_doctype_decl(&mut self) {
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
        self.sink.set_int_subset(name.as_deref(), public.as_deref(), uri.as_deref());
        self.skip_blanks();
        if self.sax_on() {
            self.sync();
            self.sink.internal_subset(name.as_deref(), public.as_deref(), uri.as_deref());
        }
        if self.cur() != b'[' && self.cur() != b'>' {
            self.fatal(ERR_DOCTYPE_NOT_FINISHED, None);
        }
    }

    /// `xmlParseInternalSubset`.
    #[verifier::external_body]
    pub fn parse_internal_subset(&mut self) {
        if self.cur() == b'[' {
            let old_nr = self.inputs.len();
            self.next();
            self.skip_blanks();
            loop {
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
                    while self.inputs.len() > old_nr {
                        self.pop_pe();
                    }
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
}

impl ContentModel {
    #[verifier::external_body]
    pub fn add(&mut self, ctype: i32, name: Option<Vec<u8>>) -> usize {
        // xmlNewDocElementContent splits a QName: prefix and local name.
        let (prefix, local) = match name {
            None => (None, None),
            Some(n) => match split_qname3(&n) {
                Some((p, l)) => (Some(p.to_vec()), Some(l.to_vec())),
                None => (None, Some(n)),
            },
        };
        self.nodes.push(ContentNode { ctype, ocur: OCUR_ONCE, name: local, prefix, c1: None, c2: None, parent: None });
        self.nodes.len() - 1
    }

    /// Makes an optional or repeated particle once; whether it was.
    #[verifier::external_body]
    fn once_if_opt(&mut self, n: Option<usize>, _plus: bool) -> bool {
        if let Some(i) = n {
            let o = self.nodes[i].ocur;
            if o == OCUR_OPT || o == OCUR_MULT {
                self.nodes[i].ocur = OCUR_ONCE;
                return true;
            }
        }
        false
    }
}

} // verus!
