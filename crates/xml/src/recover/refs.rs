//! Entity and attribute values, and references (parser.c 3497-4340,
//! 7133-7960, 11700-11902).
use super::codes::*;
use super::*;
use vstd::prelude::*;

verus! {


/// `XML_ATTVAL_ALLOC`, `XML_ATTVAL_NORM_CHANGE`.
pub const ATTVAL_ALLOC: u32 = 1;
pub const ATTVAL_NORM_CHANGE: u32 = 2;
pub const SPECIAL_EXTERNAL: i32 = 1 << 20;
pub const SPECIAL_TYPE_MASK: i32 = 0xFFFFF;
/// `XML_ATTRIBUTE_CDATA`.
pub const ATTRIBUTE_CDATA: i32 = 1;

use crate::lenient::is_byte_char;

impl<S: Sink> Parser<S> {
    /// `xmlExpandPEsInEntityValue`.
    #[verifier::external_body]
    pub fn expand_pes_in_entity_value(&mut self, buf: &mut SBuf, s: &[u8], depth: i32) {
        let max_depth = if self.options & PARSE_HUGE != 0 { 40 } else { 20 };
        let depth = depth + 1;
        if depth > max_depth {
            self.fatal_msg(ERR_RESOURCE_LIMIT, b"Maximum entity nesting depth exceeded");
            return;
        }
        let end = s.len();
        let mut p = 0usize;
        let mut chunk = 0usize;
        while p < end && !self.stopped() {
            let c = s[p];
            if c >= 0x80 {
                let l = self.str_multibyte_len(s, p, b"invalid character in entity value\n");
                if l == 0 {
                    if chunk < p {
                        buf.add(&s[chunk..p]);
                    }
                    buf.add_repl();
                    p += 1;
                    chunk = p;
                } else {
                    p += l;
                }
            } else if c == b'&' {
                if at(s, p + 1) == b'#' {
                    if chunk < p {
                        buf.add(&s[chunk..p]);
                    }
                    let v = self.parse_string_char_ref(s, &mut p);
                    if v == 0 {
                        return;
                    }
                    buf.add_char(v);
                    chunk = p;
                } else {
                    p += 1;
                    let name = self.parse_string_name(s, &mut p);
                    let semi = at(s, p) == b';';
                    p += 1;
                    if name.is_none() || !semi {
                        self.fatal_msg(ERR_ENTITY_CHAR_ERROR, b"EntityValue: '&' forbidden except for entities references\n");
                        return;
                    }
                }
            } else if c == b'%' {
                if chunk < p {
                    buf.add(&s[chunk..p]);
                }
                let ent = match self.parse_string_pe_reference(s, &mut p) {
                    None => return,
                    Some(e) => e,
                };
                if !self.external() {
                    self.fatal(ERR_ENTITY_PE_INTERNAL, None);
                    return;
                }
                let mut info = self.sink.ent_info(ent);
                if !info.has_content {
                    if self.options & PARSE_NO_XXE == 0 && (self.replace_entities || self.sink.validate()) {
                        self.load_entity_content(ent);
                    } else {
                        let name = self.sink.ent_name(ent);
                        let m = cat(&[b"not validating will not read content for PE entity ", &name, b"\n"]);
                        self.warning(ERR_ENTITY_PROCESSING, &m, Some(&name), None);
                    }
                    info = self.sink.ent_info(ent);
                }
                if self.entity_check(info.length as u64) {
                    return;
                }
                let info = self.sink.ent_info(ent);
                if info.flags & ENT_EXPANDING != 0 {
                    self.fatal(ERR_ENTITY_LOOP, None);
                    return;
                }
                self.sink.ent_set_flags(ent, info.flags | ENT_EXPANDING);
                if info.has_content {
                    let content = self.sink.ent_content(ent);
                    self.expand_pes_in_entity_value(buf, &content, depth);
                }
                let f = self.sink.ent_info(ent).flags;
                self.sink.ent_set_flags(ent, f & !ENT_EXPANDING);
                chunk = p;
            } else {
                if !is_byte_char(c) {
                    self.fatal_msg(ERR_INVALID_CHAR, b"invalid character in entity value\n");
                    if chunk < p {
                        buf.add(&s[chunk..p]);
                    }
                    buf.add_repl();
                    p += 1;
                    chunk = p;
                } else {
                    p += 1;
                }
            }
        }
        if chunk < p && p <= s.len() {
            buf.add(&s[chunk..p]);
        }
    }

    /// `xmlUTF8MultibyteLen` over a string.
    #[verifier::external_body]
    fn str_multibyte_len(&mut self, s: &[u8], p: usize, err_msg: &[u8]) -> usize {
        let (c, c1, c2, c3) = (at(s, p), at(s, p + 1), at(s, p + 2), at(s, p + 3));
        let r = multibyte_len(c, c1, c2, c3);
        if r == 33 {
            self.fatal_msg(ERR_INVALID_CHAR, err_msg);
            return 3;
        }
        if r == 0 && self.inp().flags & INPUT_ENCODING_ERROR == 0 {
            self.err_io(ERR_INVALID_ENCODING);
            self.inp_mut().flags |= INPUT_ENCODING_ERROR;
        }
        r
    }

    /// `xmlParseEntityValue`: the value and its literal text (`orig`).
    #[verifier::external_body]
    pub fn parse_entity_value(&mut self) -> (Option<Vec<u8>>, Option<Vec<u8>>) {
        let max = self.max_length(MAX_TEXT_LENGTH);
        let mut buf = SBuf::new(max);
        self.grow();
        let quote = self.cur();
        if quote != b'"' && quote != b'\'' {
            self.fatal(ERR_ATTRIBUTE_NOT_STARTED, None);
            return (None, None);
        }
        self.inp_mut().cur += 1;
        let mut length = 0usize;
        loop {
            if self.stopped() {
                self.sbuf_cleanup(buf, b"entity length too long");
                return (None, None);
            }
            if self.at_end() {
                // xmlFatalErrMsg with no message: printf's "(null)".
                self.fatal_msg(ERR_ENTITY_NOT_FINISHED, b"(null)");
                self.sbuf_cleanup(buf, b"entity length too long");
                return (None, None);
            }
            let c = self.cur();
            if c == 0 {
                self.fatal_msg(ERR_INVALID_CHAR, b"invalid character in entity value\n");
                self.sbuf_cleanup(buf, b"entity length too long");
                return (None, None);
            }
            if c == quote {
                break;
            }
            self.nextl(1);
            length += 1;
            if self.avail() < 10 {
                self.grow();
            }
        }
        let cur = self.inp().cur;
        let start = cur - length;
        let text = self.slice(start, cur);
        let n = self.inputs.len() as i32;
        self.expand_pes_in_entity_value(&mut buf, &text, n);
        self.nextl(1);
        let v = self.sbuf_finish(buf, b"entity length too long");
        (v, Some(text))
    }

    /// `xmlCheckEntityInAttValue`.
    #[verifier::external_body]
    pub fn check_entity_in_att_value(&mut self, pent: Ent, depth: i32) {
        let max_depth = if self.options & PARSE_HUGE != 0 { 40 } else { 20 };
        let pinfo = self.sink.ent_info(pent);
        let mut expanded: u64 = pinfo.length as u64;
        let depth = depth + 1;
        if depth > max_depth {
            self.fatal_msg(ERR_RESOURCE_LIMIT, b"Maximum entity nesting depth exceeded");
            return;
        }
        if pinfo.flags & ENT_EXPANDING != 0 {
            self.fatal(ERR_ENTITY_LOOP, None);
            return;
        }
        let flags = if self.sink.in_subset() == 0 { ENT_CHECKED | ENT_VALIDATED } else { ENT_VALIDATED };
        if pinfo.has_content {
            let s = self.sink.ent_content(pent);
            let mut p = 0usize;
            while !self.stopped() {
                let c = at(&s, p);
                if c != b'&' {
                    if c == 0 {
                        break;
                    }
                    if c == b'<' {
                        let name = self.sink.ent_name(pent);
                        let m = cat(&[b"'<' in entity '", &name, b"' is not allowed in attributes values\n"]);
                        self.fatal_str(ERR_LT_IN_ATTRIBUTE, &m, Some(&name));
                    }
                    p += 1;
                } else if at(&s, p + 1) == b'#' {
                    let v = self.parse_string_char_ref(&s, &mut p);
                    if v == 0 {
                        self.sink.ent_truncate_content(pent);
                        break;
                    }
                } else {
                    let name = match self.parse_string_entity_ref(&s, &mut p) {
                        None => {
                            self.sink.ent_truncate_content(pent);
                            break;
                        }
                        Some(n) => n,
                    };
                    let ent = self.lookup_general_entity(&name, true);
                    if let Some(ent) = ent {
                        let info = self.sink.ent_info(ent);
                        if info.etype != INTERNAL_PREDEFINED_ENTITY {
                            if info.flags & flags != flags {
                                let f = self.sink.ent_info(pent).flags;
                                self.sink.ent_set_flags(pent, f | ENT_EXPANDING);
                                self.check_entity_in_att_value(ent, depth);
                                let f = self.sink.ent_info(pent).flags;
                                self.sink.ent_set_flags(pent, f & !ENT_EXPANDING);
                            }
                            let info = self.sink.ent_info(ent);
                            expanded = expanded.saturating_add(info.expanded_size).saturating_add(ENT_FIXED_COST);
                        }
                    }
                }
            }
        }
        if self.sink.in_subset() == 0 {
            self.sink.ent_set_expanded_size(pent, expanded);
        }
        let f = self.sink.ent_info(pent).flags;
        self.sink.ent_set_flags(pent, f | flags);
    }

    /// `xmlExpandEntityInAttValue`: whether normalization changed the value.
    #[verifier::external_body]
    pub fn expand_entity_in_att_value(&mut self, buf: &mut SBuf, s: &[u8], pent: Option<Ent>, normalize: bool, in_space: &mut bool, depth: i32, check: bool) -> bool {
        let max_depth = if self.options & PARSE_HUGE != 0 { 40 } else { 20 };
        let mut norm_change = false;
        let depth = depth + 1;
        if depth > max_depth {
            self.fatal_msg(ERR_RESOURCE_LIMIT, b"Maximum entity nesting depth exceeded");
            return false;
        }
        if let Some(pe) = pent {
            let info = self.sink.ent_info(pe);
            if info.flags & ENT_EXPANDING != 0 {
                self.fatal(ERR_ENTITY_LOOP, None);
                return false;
            }
            if check && self.entity_check(info.length as u64) {
                return false;
            }
        }
        let mut chunk: usize = 0;
        let mut p = 0usize;
        while !self.stopped() {
            let c = at(s, p);
            if c != b'&' {
                if c == 0 {
                    break;
                }
                if let Some(pe) = pent {
                    if c == b'<' {
                        let name = self.sink.ent_name(pe);
                        let m = cat(&[b"'<' in entity '", &name, b"' is not allowed in attributes values\n"]);
                        self.fatal_str(ERR_LT_IN_ATTRIBUTE, &m, Some(&name));
                        break;
                    }
                }
                if c <= 0x20 {
                    if normalize && *in_space {
                        if chunk > 0 {
                            buf.add(&s[p - chunk..p]);
                            chunk = 0;
                        }
                        norm_change = true;
                    } else if c < 0x20 {
                        if chunk > 0 {
                            buf.add(&s[p - chunk..p]);
                            chunk = 0;
                        }
                        buf.add(b" ");
                    } else {
                        chunk += 1;
                    }
                    *in_space = true;
                } else {
                    chunk += 1;
                    *in_space = false;
                }
                p += 1;
            } else if at(s, p + 1) == b'#' {
                if chunk > 0 {
                    buf.add(&s[p - chunk..p]);
                    chunk = 0;
                }
                let v = self.parse_string_char_ref(s, &mut p);
                if v == 0 {
                    if let Some(pe) = pent {
                        self.sink.ent_truncate_content(pe);
                    }
                    break;
                }
                if v == b' ' as u32 {
                    if normalize && *in_space {
                        norm_change = true;
                    } else {
                        buf.add(b" ");
                    }
                    *in_space = true;
                } else {
                    buf.add_char(v);
                    *in_space = false;
                }
            } else {
                if chunk > 0 {
                    buf.add(&s[p - chunk..p]);
                    chunk = 0;
                }
                let name = match self.parse_string_entity_ref(s, &mut p) {
                    None => {
                        if let Some(pe) = pent {
                            self.sink.ent_truncate_content(pe);
                        }
                        break;
                    }
                    Some(n) => n,
                };
                let ent = self.lookup_general_entity(&name, true);
                if let Some(ent) = ent {
                    let info = self.sink.ent_info(ent);
                    if info.etype == INTERNAL_PREDEFINED_ENTITY {
                        if !info.has_content {
                            self.fatal_msg(ERR_INTERNAL_ERROR, b"predefined entity has no content\n");
                            break;
                        }
                        let content = self.sink.ent_content(ent);
                        buf.add(&content);
                        *in_space = false;
                    } else if info.has_content {
                        if let Some(pe) = pent {
                            let f = self.sink.ent_info(pe).flags;
                            self.sink.ent_set_flags(pe, f | ENT_EXPANDING);
                        }
                        let content = self.sink.ent_content(ent);
                        norm_change |= self.expand_entity_in_att_value(buf, &content, Some(ent), normalize, in_space, depth, check);
                        if let Some(pe) = pent {
                            let f = self.sink.ent_info(pe).flags;
                            self.sink.ent_set_flags(pe, f & !ENT_EXPANDING);
                        }
                    }
                }
            }
        }
        if chunk > 0 && p >= chunk {
            buf.add(&s[p - chunk..p]);
        }
        norm_change
    }

    /// `xmlParseAttValueInternal`: the value and its `XML_ATTVAL_*` flags.
    #[verifier::external_body]
    pub fn parse_att_value_internal(&mut self, special: i32, is_ns: bool) -> Option<(Vec<u8>, u32)> {
        let max = self.max_length(MAX_TEXT_LENGTH);
        let normalize = (special & SPECIAL_TYPE_MASK) > ATTRIBUTE_CDATA;
        let mut flags: u32 = 0;
        let replace = self.replace_entities || is_ns;
        let mut buf = SBuf::new(max);
        self.grow();
        let quote = self.cur();
        if quote != b'"' && quote != b'\'' {
            self.fatal(ERR_ATTRIBUTE_NOT_STARTED, None);
            return None;
        }
        self.nextl(1);
        let ent_flags = if self.sink.in_subset() == 0 { ENT_CHECKED | ENT_VALIDATED } else { ENT_VALIDATED };
        let mut in_space = true;
        let mut chunk: usize = 0;
        loop {
            if self.stopped() {
                self.sbuf_cleanup(buf, b"AttValue length too long");
                return None;
            }
            if self.at_end() {
                self.fatal_msg(ERR_ATTRIBUTE_NOT_FINISHED, b"AttValue: ' expected\n");
                self.sbuf_cleanup(buf, b"AttValue length too long");
                return None;
            }
            if self.avail() < 10 {
                self.grow();
            }
            let c = self.cur();
            let cp = self.inp().cur;
            if c >= 0x80 {
                let l = self.utf8_multibyte_len(cp, b"invalid character in attribute value\n");
                if l == 0 {
                    if chunk > 0 {
                        let t = self.slice(cp - chunk, cp);
                        buf.add(&t);
                        chunk = 0;
                    }
                    buf.add_repl();
                    self.nextl(1);
                } else {
                    chunk += l;
                    self.nextl(l);
                }
                in_space = false;
            } else if c != b'&' {
                if c > 0x20 {
                    if c == quote {
                        break;
                    }
                    if c == b'<' {
                        self.fatal(ERR_LT_IN_ATTRIBUTE, None);
                    }
                    chunk += 1;
                    in_space = false;
                } else if !is_byte_char(c) {
                    self.fatal_msg(ERR_INVALID_CHAR, b"invalid character in attribute value\n");
                    if chunk > 0 {
                        let t = self.slice(cp - chunk, cp);
                        buf.add(&t);
                        chunk = 0;
                    }
                    buf.add_repl();
                    in_space = false;
                } else {
                    if normalize && in_space {
                        if chunk > 0 {
                            let t = self.slice(cp - chunk, cp);
                            buf.add(&t);
                            chunk = 0;
                        }
                        flags |= ATTVAL_NORM_CHANGE;
                    } else if c < 0x20 {
                        if chunk > 0 {
                            let t = self.slice(cp - chunk, cp);
                            buf.add(&t);
                            chunk = 0;
                        }
                        buf.add(b" ");
                    } else {
                        chunk += 1;
                    }
                    in_space = true;
                    if c == 0x0D && self.nxt(1) == 0x0A {
                        self.inp_mut().cur += 1;
                    }
                }
                self.nextl(1);
            } else if self.nxt(1) == b'#' {
                if chunk > 0 {
                    let t = self.slice(cp - chunk, cp);
                    buf.add(&t);
                    chunk = 0;
                }
                let v = self.parse_char_ref();
                if v == 0 {
                    self.sbuf_cleanup(buf, b"AttValue length too long");
                    return None;
                }
                if v == b'&' as u32 && !replace {
                    buf.add(b"&#38;");
                    in_space = false;
                } else if v == b' ' as u32 {
                    if normalize && in_space {
                        flags |= ATTVAL_NORM_CHANGE;
                    } else {
                        buf.add(b" ");
                    }
                    in_space = true;
                } else {
                    buf.add_char(v);
                    in_space = false;
                }
            } else {
                if chunk > 0 {
                    let t = self.slice(cp - chunk, cp);
                    buf.add(&t);
                    chunk = 0;
                }
                let name = match self.parse_entity_ref_internal() {
                    None => continue,
                    Some(n) => n,
                };
                let ent = match self.lookup_general_entity(&name, true) {
                    None => continue,
                    Some(e) => e,
                };
                let info = self.sink.ent_info(ent);
                if info.etype == INTERNAL_PREDEFINED_ENTITY {
                    let content = self.sink.ent_content(ent);
                    if at(&content, 0) == b'&' && !replace {
                        buf.add(b"&#38;");
                    } else {
                        buf.add(&content);
                    }
                    in_space = false;
                } else if replace {
                    let content = if info.has_content { self.sink.ent_content(ent) } else { Vec::new() };
                    if info.has_content {
                        let n = self.inputs.len() as i32;
                        if self.expand_entity_in_att_value(&mut buf, &content, Some(ent), normalize, &mut in_space, n, true) {
                            flags |= ATTVAL_NORM_CHANGE;
                        }
                    }
                } else {
                    if info.flags & ent_flags != ent_flags {
                        let n = self.inputs.len() as i32;
                        self.check_entity_in_att_value(ent, n);
                    }
                    let es = self.sink.ent_info(ent).expanded_size;
                    if self.entity_check(es) {
                        self.sink.ent_truncate_content(ent);
                        self.sbuf_cleanup(buf, b"AttValue length too long");
                        return None;
                    }
                    let ename = self.sink.ent_name(ent);
                    buf.add(b"&");
                    buf.add(&ename);
                    buf.add(b";");
                    in_space = false;
                }
            }
        }
        let cp = self.inp().cur;
        let ret;
        if !buf.alloc {
            let mut len = chunk;
            if normalize && in_space && chunk > 0 {
                flags |= ATTVAL_NORM_CHANGE;
                len -= 1;
            }
            ret = self.slice(cp - chunk, cp - chunk + len);
            self.sbuf_cleanup(buf, b"AttValue length too long");
        } else {
            if chunk > 0 {
                let t = self.slice(cp - chunk, cp);
                buf.add(&t);
            }
            if normalize && in_space && !buf.mem.is_empty() {
                flags |= ATTVAL_NORM_CHANGE;
                buf.mem.pop();
            }
            let r = self.sbuf_finish(buf, b"AttValue length too long");
            flags |= ATTVAL_ALLOC;
            match r {
                None => {
                    self.nextl(1);
                    return None;
                }
                Some(v) => ret = v,
            }
        }
        self.nextl(1);
        Some((ret, flags))
    }

    /// `xmlParseAttValue`.
    #[verifier::external_body]
    pub fn parse_att_value(&mut self) -> Option<Vec<u8>> {
        // With no out-flags, the value is always built in the buffer.
        let r = self.parse_att_value_internal(0, false);
        r.map(|(v, _)| v)
    }

    /// `xmlHandleUndeclaredEntity`.
    #[verifier::external_body]
    pub fn handle_undeclared_entity(&mut self, name: &[u8]) {
        let m = cat(&[b"Entity '", name, b"' not defined\n"]);
        if self.sink.standalone() == 1 || (!self.sink.has_ext_subset() && !self.sink.has_perefs()) {
            self.fatal_str(ERR_UNDECLARED_ENTITY, &m, Some(name));
        } else if self.sink.validate() {
            self.validity_error(ERR_UNDECLARED_ENTITY, &m, Some(name), None);
        } else if self.options & (PARSE_DTDLOAD | PARSE_DTDATTR | PARSE_DTDVALID) != 0 || (self.replace_entities && self.options & PARSE_NO_XXE == 0) {
            self.err_str(WAR_UNDECLARED_ENTITY, &m, Some(name));
        } else {
            self.warning(WAR_UNDECLARED_ENTITY, &m, Some(name), None);
        }
        self.sink.set_valid(false);
    }

    /// `xmlLookupGeneralEntity`.
    #[verifier::external_body]
    pub fn lookup_general_entity(&mut self, name: &[u8], in_attr: bool) -> Option<Ent> {
        let mut ent: Option<Ent> = None;
        if self.options & PARSE_OLDSAX == 0 {
            if let Some(e) = self.sink.predefined_entity(name) {
                return Some(e);
            }
        }
        if self.sink.has_get_entity() {
            ent = self.sink.get_entity(name);
        }
        if self.sink.well_formed() && ent.is_none() && self.options & PARSE_OLDSAX != 0 {
            ent = self.sink.predefined_entity(name);
        }
        if self.sink.well_formed() && ent.is_none() {
            ent = self.sink.sax2_get_entity(name);
        }
        match ent {
            None => {
                self.handle_undeclared_entity(name);
                None
            }
            Some(e) => {
                let t = self.sink.ent_info(e).etype;
                if t == EXTERNAL_GENERAL_UNPARSED_ENTITY {
                    let m = cat(&[b"Entity reference to unparsed entity ", name, b"\n"]);
                    self.fatal_str(ERR_UNPARSED_ENTITY, &m, Some(name));
                    None
                } else if t == EXTERNAL_GENERAL_PARSED_ENTITY && in_attr {
                    let m = cat(&[b"Attribute references external entity '", name, b"'\n"]);
                    self.fatal_str(ERR_ENTITY_IS_EXTERNAL, &m, Some(name));
                    None
                } else {
                    Some(e)
                }
            }
        }
    }

    /// `xmlParseEntityRefInternal`.
    #[verifier::external_body]
    pub fn parse_entity_ref_internal(&mut self) -> Option<Vec<u8>> {
        self.grow();
        if self.cur() != b'&' {
            return None;
        }
        self.next();
        let name = match self.parse_name() {
            None => {
                self.fatal_msg(ERR_NAME_REQUIRED, b"xmlParseEntityRef: no name\n");
                return None;
            }
            Some(n) => n,
        };
        if self.cur() != b';' {
            self.fatal(ERR_ENTITYREF_SEMICOL_MISSING, None);
            return None;
        }
        self.next();
        Some(name)
    }

    /// `xmlParseStringEntityRef`.
    #[verifier::external_body]
    pub fn parse_string_entity_ref(&mut self, s: &[u8], i: &mut usize) -> Option<Vec<u8>> {
        let mut p = *i;
        if at(s, p) != b'&' {
            return None;
        }
        p += 1;
        let name = match self.parse_string_name(s, &mut p) {
            None => {
                self.fatal_msg(ERR_NAME_REQUIRED, b"xmlParseStringEntityRef: no name\n");
                *i = p;
                return None;
            }
            Some(n) => n,
        };
        if at(s, p) != b';' {
            self.fatal(ERR_ENTITYREF_SEMICOL_MISSING, None);
            *i = p;
            return None;
        }
        p += 1;
        *i = p;
        Some(name)
    }

    /// `xmlParseStringPEReference`.
    #[verifier::external_body]
    pub fn parse_string_pe_reference(&mut self, s: &[u8], i: &mut usize) -> Option<Ent> {
        let mut p = *i;
        if at(s, p) != b'%' {
            return None;
        }
        p += 1;
        let name = match self.parse_string_name(s, &mut p) {
            None => {
                self.fatal_msg(ERR_NAME_REQUIRED, b"xmlParseStringPEReference: no name\n");
                *i = p;
                return None;
            }
            Some(n) => n,
        };
        if at(s, p) != b';' {
            self.fatal(ERR_ENTITYREF_SEMICOL_MISSING, None);
            *i = p;
            return None;
        }
        p += 1;
        self.sink.set_has_perefs(true);
        let mut entity = None;
        if self.sink.has_get_parameter_entity() {
            entity = self.sink.get_parameter_entity(&name);
        }
        match entity {
            None => self.handle_undeclared_entity(&name),
            Some(e) => {
                let t = self.sink.ent_info(e).etype;
                if t != INTERNAL_PARAMETER_ENTITY && t != EXTERNAL_PARAMETER_ENTITY {
                    let m = cat(&[b"%", &name, b"; is not a parameter entity\n"]);
                    self.warning(WAR_UNDECLARED_ENTITY, &m, Some(&name), None);
                }
            }
        }
        *i = p;
        entity
    }

    /// `xmlParsePERefInternal`.
    #[verifier::external_body]
    pub fn parse_pe_ref_internal(&mut self, markup_decl: bool) {
        if self.cur() != b'%' {
            return;
        }
        self.next();
        let name = match self.parse_name() {
            None => {
                self.fatal_msg(ERR_PEREF_NO_NAME, b"PEReference: no name\n");
                return;
            }
            Some(n) => n,
        };
        if self.cur() != b';' {
            self.fatal(ERR_PEREF_SEMICOL_MISSING, None);
            return;
        }
        self.next();
        self.sink.set_has_perefs(true);
        let mut entity = None;
        if self.sink.has_get_parameter_entity() {
            entity = self.sink.get_parameter_entity(&name);
        }
        let e = match entity {
            None => {
                self.handle_undeclared_entity(&name);
                return;
            }
            Some(e) => e,
        };
        let info = self.sink.ent_info(e);
        if info.etype != INTERNAL_PARAMETER_ENTITY && info.etype != EXTERNAL_PARAMETER_ENTITY {
            let m = cat(&[b"Internal: %", &name, b"; is not a parameter entity\n"]);
            self.warning(WAR_UNDECLARED_ENTITY, &m, Some(&name), None);
            return;
        }
        if info.etype == EXTERNAL_PARAMETER_ENTITY
            && (self.options & PARSE_NO_XXE != 0 || (self.options & (PARSE_DTDLOAD | PARSE_DTDATTR | PARSE_DTDVALID) == 0 && !self.replace_entities && !self.sink.validate()))
        {
            return;
        }
        if info.flags & ENT_EXPANDING != 0 {
            self.fatal(ERR_ENTITY_LOOP, None);
            return;
        }
        let input = match self.entity_input(e) {
            None => return,
            Some(i) => i,
        };
        if self.push_input(input) < 0 {
            return;
        }
        let f = self.sink.ent_info(e).flags;
        self.sink.ent_set_flags(e, f | ENT_EXPANDING);
        if markup_decl {
            self.inp_mut().flags |= INPUT_MARKUP_DECL;
        }
        self.grow();
        if info.etype == EXTERNAL_PARAMETER_ENTITY {
            self.detect_encoding();
            if self.cmp(b"<?xml") && blank(self.nxt(5)) {
                self.parse_text_decl();
            }
        }
    }

    /// `xmlLoadEntityContent`: reads an external entity's text into its
    /// content. 0, or -1.
    #[verifier::external_body]
    pub fn load_entity_content(&mut self, e: Ent) -> i32 {
        let info = self.sink.ent_info(e);
        if (info.etype != EXTERNAL_PARAMETER_ENTITY && info.etype != EXTERNAL_GENERAL_PARSED_ENTITY) || info.has_content {
            self.fatal(ERR_ARGUMENT, Some(b"xmlLoadEntityContent parameter error"));
            return -1;
        }
        let input = match self.entity_input(e) {
            None => return -1,
            Some(i) => i,
        };
        // The entity is read on an input stack of its own.
        let saved = core::mem::take(&mut self.inputs);
        let saved_enc = self.encoding.take();
        self.inputs.push(input);
        self.sync();
        let mut ret = -1;
        'body: {
            self.detect_encoding();
            if self.cmp(b"<?xml") && blank(self.nxt(5)) {
                self.parse_text_decl();
            }
            let length = self.inp().cur as u64;
            self.sink.add_sizeentities(length);
            // Read it all.
            loop {
                let r = {
                    let input = self.inp_mut();
                    match input.src.as_mut() {
                        None => 0,
                        Some(src) => enc::buffer_grow(&mut input.buf, src, 4096),
                    }
                };
                if r < 0 {
                    let code = self.inp().src.as_ref().map_or(ERR_INTERNAL_ERROR, |s| s.error);
                    self.err_io(code);
                    break 'body;
                }
                if r == 0 {
                    break;
                }
            }
            let start = self.inp().cur;
            let content = self.slice(start, self.inp().buf.len());
            let mut i = 0usize;
            while i < content.len() {
                match utf8_char(&content, i, content.len() - i) {
                    Some((c, l)) if is_char(c) => i += l,
                    _ => {
                        let b = content[i];
                        let m = cat(&[b"xmlLoadEntityContent: invalid char value ", &itoa(b as i64), b"\n"]);
                        self.fatal_int(ERR_INVALID_CHAR, &m, b as i32);
                        break 'body;
                    }
                }
            }
            self.sink.add_sizeentities(content.len() as u64);
            self.sink.ent_set_content(e, content);
            ret = 0;
        }
        self.inputs = saved;
        self.encoding = saved_enc;
        self.sync();
        ret
    }

    /// `xmlParseReference`.
    #[verifier::external_body]
    pub fn parse_reference(&mut self) {
        if self.cur() != b'&' {
            return;
        }
        if self.nxt(1) == b'#' {
            let v = self.parse_char_ref();
            if v == 0 {
                return;
            }
            let mut out = Vec::new();
            push_char(&mut out, v);
            if self.sax_on() {
                self.sync();
                self.sink.characters(&out);
            }
            return;
        }
        let name = match self.parse_entity_ref_internal() {
            None => return,
            Some(n) => n,
        };
        let ent = match self.lookup_general_entity(&name, false) {
            None => {
                if !self.replace_entities && self.sax_on() && self.sink.has_reference() {
                    self.sync();
                    self.sink.reference(&name);
                }
                return;
            }
            Some(e) => e,
        };
        if !self.sink.well_formed() {
            return;
        }
        let info = self.sink.ent_info(ent);
        if info.etype == INTERNAL_PREDEFINED_ENTITY {
            if !info.has_content {
                return;
            }
            let v = self.sink.ent_content(ent);
            if self.sax_on() {
                self.sync();
                self.sink.characters(&v);
            }
            return;
        }
        if info.flags & ENT_PARSED == 0 && info.has_children {
            self.sink.ent_set_flags(ent, info.flags | ENT_PARSED);
        }
        let info = self.sink.ent_info(ent);
        if info.etype == INTERNAL_GENERAL_ENTITY || (self.options & PARSE_NO_XXE == 0 && (self.replace_entities || self.sink.validate())) {
            if info.flags & ENT_PARSED == 0 {
                self.ctxt_parse_entity(ent);
            } else if !info.has_children {
                self.ctxt_parse_entity(ent);
            }
        }
        let es = self.sink.ent_info(ent).expanded_size;
        if self.entity_check(es) {
            return;
        }
        if !self.sax_on() {
            return;
        }
        self.sync();
        if !self.replace_entities {
            if self.sink.has_reference() {
                let n = self.sink.ent_name(ent);
                self.sink.reference(&n);
            }
        } else if self.sink.ent_info(ent).has_children && self.sink.has_node() {
            self.sink.reference_tree(ent, true);
        }
    }

    /// `xmlCtxtParseEntity`.
    #[verifier::external_body]
    pub fn ctxt_parse_entity(&mut self, ent: Ent) {
        let info = self.sink.ent_info(ent);
        let is_external = info.etype == EXTERNAL_GENERAL_PARSED_ENTITY;
        let build_tree = self.sink.has_node();
        'body: {
            if info.flags & ENT_EXPANDING != 0 {
                self.fatal(ERR_ENTITY_LOOP, None);
                break 'body;
            }
            let input = match self.entity_input(ent) {
                None => break 'body,
                Some(i) => i,
            };
            let old_min = self.nsdb.min;
            if build_tree {
                let n = self.nsdb.tab.len();
                self.set_ns_min(n);
            }
            self.sink.ent_tree(TreeOp::SaveText, ent);
            let f = self.sink.ent_info(ent).flags;
            self.sink.ent_set_flags(ent, f | ENT_EXPANDING);
            let (consumed, kept) = self.ctxt_parse_content_internal(input, is_external, build_tree);
            let f = self.sink.ent_info(ent).flags;
            self.sink.ent_set_flags(ent, f & !ENT_EXPANDING);
            self.set_ns_min(old_min);
            self.sink.ent_tree(TreeOp::RestoreText, ent);
            let info = self.sink.ent_info(ent);
            if info.flags & ENT_CHECKED == 0 {
                self.sink.ent_set_expanded_size(ent, info.expanded_size.saturating_add(consumed));
            }
            if info.flags & ENT_PARSED == 0 {
                if is_external {
                    self.sink.add_sizeentities(consumed);
                }
                if kept {
                    self.sink.ent_tree(TreeOp::KeepList, ent);
                } else {
                    self.sink.ent_tree(TreeOp::ClearChildren, ent);
                }
            } else {
                self.sink.ent_tree(TreeOp::FreeList, ent);
            }
        }
        let f = self.sink.ent_info(ent).flags;
        self.sink.ent_set_flags(ent, f | ENT_PARSED | ENT_CHECKED);
    }

    /// `xmlCtxtParseContentInternal` for an entity: the bytes the input
    /// held, and whether a node list was taken from the temporary root.
    #[verifier::external_body]
    fn ctxt_parse_content_internal(&mut self, input: Input, has_text_decl: bool, build_tree: bool) -> (u64, bool) {
        let mut kept = false;
        let all = input.consumed.saturating_add(input.buf.len() as u64);
        if build_tree {
            self.sink.ent_tree(TreeOp::NewRoot, 0);
        }
        if self.push_input(input) < 0 {
            if build_tree {
                self.sink.ent_tree(TreeOp::FreeRoot, 0);
            }
            return (all, false);
        }
        self.name_ns_push(b"#root".to_vec(), None, None, 0, 0);
        self.space_push(-1);
        if build_tree {
            self.sink.ent_tree(TreeOp::PushRoot, 0);
        }
        if has_text_decl {
            self.detect_encoding();
            if self.cmp(b"<?xml") && blank(self.nxt(5)) {
                self.parse_text_decl();
                let doc10 = self.version.as_deref() == Some(b"1.0");
                let ent10 = self.inp().version.as_deref() == Some(b"1.0");
                if doc10 && !ent10 {
                    self.fatal_msg(ERR_VERSION_MISMATCH, b"Version mismatch between document and entity\n");
                }
            }
        }
        self.parse_content_internal();
        if !self.at_end() {
            self.fatal(ERR_NOT_WELL_BALANCED, None);
        }
        if self.sink.well_formed() || (self.sink.recovery() && !self.sink.catastrophic()) {
            if build_tree {
                self.sink.ent_tree(TreeOp::TakeList, 0);
                kept = true;
            }
        }
        // Read the rest of the input, to count all of it.
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
        if build_tree {
            self.sink.ent_tree(TreeOp::PopRoot, 0);
        }
        self.name_pop();
        self.space_pop();
        self.pop_input();
        if build_tree {
            self.sink.ent_tree(TreeOp::FreeRoot, 0);
        }
        (consumed, kept)
    }
}

pub use crate::lenient::multibyte_len;

/// The tree side of parsing an entity's content (`xmlCtxtParseEntity`,
/// `xmlCtxtParseContentInternal`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TreeOp {
    /// Save and zero `nodelen`/`nodemem`.
    SaveText,
    RestoreText,
    /// `xmlNewDocNode(doc, NULL, "#root", NULL)`.
    NewRoot,
    /// `nodePush(root)`.
    PushRoot,
    /// Take the root's children as the parsed list.
    TakeList,
    /// `nodePop`.
    PopRoot,
    /// `xmlFreeNode(root)`.
    FreeRoot,
    /// The list becomes the entity's children.
    KeepList,
    /// No list: the entity's children are NULL.
    ClearChildren,
    /// The entity had been parsed: free the list.
    FreeList,
}

} // verus!
