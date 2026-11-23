//! The XML declaration, the prolog and the document (parser.c 9905-10526,
//! 7064-7117; SAX2.c 272-380 for the external subset).
use super::codes::*;
use super::content::grow_capacity_min;
use super::*;
use vstd::prelude::*;

verus! {


impl<S: Sink> Parser<S> {
    /// `xmlParseVersionNum`.
    #[verifier::external_body]
    pub fn parse_version_num(&mut self) -> Option<Vec<u8>> {
        let max = if self.options & PARSE_HUGE != 0 { MAX_TEXT_LENGTH } else { MAX_NAME_LENGTH };
        let mut size: usize = 10;
        let mut buf: Vec<u8> = Vec::new();
        let mut cur = self.cur();
        if !cur.is_ascii_digit() {
            return None;
        }
        buf.push(cur);
        self.next();
        cur = self.cur();
        if cur != b'.' {
            return None;
        }
        buf.push(cur);
        self.next();
        cur = self.cur();
        while cur.is_ascii_digit() {
            if !self.step() {
                return None;
            }
            if buf.len() + 1 >= size {
                match grow_capacity_min(size, 1, max) {
                    None => {
                        self.fatal(ERR_NAME_TOO_LONG, Some(b"VersionNum"));
                        return None;
                    }
                    Some(n) => size = n,
                }
            }
            buf.push(cur);
            self.next();
            cur = self.cur();
        }
        Some(buf)
    }

    /// `xmlParseVersionInfo`.
    #[verifier::external_body]
    pub fn parse_version_info(&mut self) -> Option<Vec<u8>> {
        let mut version = None;
        if self.cmp(b"version") {
            self.skip(7);
            self.skip_blanks();
            if self.cur() != b'=' {
                self.fatal(ERR_EQUAL_REQUIRED, None);
                return None;
            }
            self.next();
            self.skip_blanks();
            let q = self.cur();
            if q == b'"' || q == b'\'' {
                self.next();
                version = self.parse_version_num();
                if self.cur() != q {
                    self.fatal(ERR_STRING_NOT_CLOSED, None);
                } else {
                    self.next();
                }
            } else {
                self.fatal(ERR_STRING_NOT_STARTED, None);
            }
        }
        version
    }

    /// `xmlParseEncName`.
    #[verifier::external_body]
    pub fn parse_enc_name(&mut self) -> Option<Vec<u8>> {
        let max = if self.options & PARSE_HUGE != 0 { MAX_TEXT_LENGTH } else { MAX_NAME_LENGTH };
        let mut size: usize = 10;
        let mut cur = self.cur();
        if !cur.is_ascii_alphabetic() {
            self.fatal(ERR_ENCODING_NAME, None);
            return None;
        }
        let mut buf: Vec<u8> = vec![cur];
        self.next();
        cur = self.cur();
        while cur.is_ascii_alphanumeric() || cur == b'.' || cur == b'_' || cur == b'-' {
            if !self.step() {
                return None;
            }
            if buf.len() + 1 >= size {
                match grow_capacity_min(size, 1, max) {
                    None => {
                        self.fatal(ERR_NAME_TOO_LONG, Some(b"EncName"));
                        return None;
                    }
                    Some(n) => size = n,
                }
            }
            buf.push(cur);
            self.next();
            cur = self.cur();
        }
        Some(buf)
    }

    /// `xmlParseEncodingDecl`.
    #[verifier::external_body]
    pub fn parse_encoding_decl(&mut self) {
        self.skip_blanks();
        if !self.cmp(b"encoding") {
            return;
        }
        self.skip(8);
        self.skip_blanks();
        if self.cur() != b'=' {
            self.fatal(ERR_EQUAL_REQUIRED, None);
            return;
        }
        self.next();
        self.skip_blanks();
        let q = self.cur();
        let encoding;
        if q == b'"' || q == b'\'' {
            self.next();
            encoding = self.parse_enc_name();
            if self.cur() != q {
                self.fatal(ERR_STRING_NOT_CLOSED, None);
                return;
            }
            self.next();
        } else {
            self.fatal(ERR_STRING_NOT_STARTED, None);
            return;
        }
        if let Some(e) = encoding {
            self.set_declared_encoding(e);
        }
    }

    /// `xmlParseSDDecl`.
    #[verifier::external_body]
    pub fn parse_sd_decl(&mut self) -> i32 {
        let mut standalone = -2;
        self.skip_blanks();
        if self.cmp(b"standalone") {
            self.skip(10);
            self.skip_blanks();
            if self.cur() != b'=' {
                self.fatal(ERR_EQUAL_REQUIRED, None);
                return standalone;
            }
            self.next();
            self.skip_blanks();
            let q = self.cur();
            if q == b'\'' || q == b'"' {
                self.next();
                if self.cur() == b'n' && self.nxt(1) == b'o' {
                    standalone = 0;
                    self.skip(2);
                } else if self.cur() == b'y' && self.nxt(1) == b'e' && self.nxt(2) == b's' {
                    standalone = 1;
                    self.skip(3);
                } else {
                    self.fatal(ERR_STANDALONE_VALUE, None);
                }
                if self.cur() != q {
                    self.fatal(ERR_STRING_NOT_CLOSED, None);
                } else {
                    self.next();
                }
            } else {
                self.fatal(ERR_STRING_NOT_STARTED, None);
            }
        }
        standalone
    }

    /// `xmlParseXMLDecl`.
    #[verifier::external_body]
    pub fn parse_xml_decl(&mut self) {
        self.sink.set_standalone(-2);
        self.skip(5);
        if !blank(self.cur()) {
            self.fatal_msg(ERR_SPACE_REQUIRED, b"Blank needed after '<?xml'\n");
        }
        self.skip_blanks();
        match self.parse_version_info() {
            None => self.fatal(ERR_VERSION_MISSING, None),
            Some(v) => {
                if v.as_slice() != b"1.0" {
                    let m = cat(&[b"Unsupported version '", &v, b"'\n"]);
                    if self.options & PARSE_OLD10 != 0 {
                        self.fatal_str(ERR_UNKNOWN_VERSION, &m, Some(&v));
                    } else if at(&v, 0) == b'1' && at(&v, 1) == b'.' {
                        self.warning(WAR_UNKNOWN_VERSION, &m, Some(&v), None);
                    } else {
                        self.fatal_str(ERR_UNKNOWN_VERSION, &m, Some(&v));
                    }
                }
                self.sink.set_version(&v);
                self.version = Some(v);
            }
        }
        if !blank(self.cur()) {
            if self.cur() == b'?' && self.nxt(1) == b'>' {
                self.skip(2);
                return;
            }
            self.fatal_msg(ERR_SPACE_REQUIRED, b"Blank needed here\n");
        }
        self.parse_encoding_decl();
        if self.encoding.is_some() && !blank(self.cur()) {
            if self.cur() == b'?' && self.nxt(1) == b'>' {
                self.skip(2);
                return;
            }
            self.fatal_msg(ERR_SPACE_REQUIRED, b"Blank needed here\n");
        }
        self.grow();
        self.skip_blanks();
        let sd = self.parse_sd_decl();
        self.sink.set_standalone(sd);
        self.skip_blanks();
        if self.cur() == b'?' && self.nxt(1) == b'>' {
            self.skip(2);
        } else if self.cur() == b'>' {
            self.fatal(ERR_XMLDECL_NOT_FINISHED, None);
            self.next();
        } else {
            self.fatal(ERR_XMLDECL_NOT_FINISHED, None);
            while !self.stopped() {
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

    /// `xmlParseMisc`.
    #[verifier::external_body]
    pub fn parse_misc(&mut self) {
        while !self.stopped() {
            if !self.step() {
                break;
            }
            self.skip_blanks();
            self.grow();
            if self.cur() == b'<' && self.nxt(1) == b'?' {
                self.parse_pi();
            } else if self.cmp(b"<!--") {
                self.parse_comment();
            } else {
                break;
            }
        }
    }

    /// `xmlParseExternalSubset`.
    #[verifier::external_body]
    pub fn parse_external_subset(&mut self) {
        self.detect_encoding();
        if self.cmp(b"<?xml") {
            self.parse_text_decl();
        }
        self.sink.ensure_doc_for_subset(self.ext_sub_system.as_deref(), self.ext_sub_uri.as_deref());
        self.sink.set_in_subset(2);
        let old_nr = self.inputs.len();
        self.skip_blanks();
        while !self.stopped() {
            if !self.step() {
                break;
            }
            if self.at_end() {
                if self.inputs.len() <= old_nr {
                    self.check_eof(ERR_EXT_SUBSET_NOT_FINISHED);
                    break;
                }
                self.pop_pe();
            } else if self.cur() == b'<' && self.nxt(1) == b'!' && self.nxt(2) == b'[' {
                self.parse_conditional_sections();
            } else if self.cur() == b'<' && (self.nxt(1) == b'!' || self.nxt(1) == b'?') {
                self.parse_markup_decl();
            } else if self.cur() == b'%' {
                self.parse_pe_ref_internal(true);
            } else {
                self.fatal(ERR_EXT_SUBSET_NOT_FINISHED, None);
                while self.inputs.len() > old_nr {
                    self.pop_pe();
                }
                break;
            }
            self.skip_blanks();
            self.shrink();
            self.grow();
        }
    }

    /// `xmlSAX2ExternalSubset`: the sink loads the subset (or declines),
    /// the parser reads it on an input stack of its own.
    #[verifier::external_body]
    fn external_subset(&mut self) {
        let name = self.int_sub_name.clone();
        let public = self.ext_sub_system.clone();
        let system = self.ext_sub_uri.clone();
        if !self.sax_on() {
            return;
        }
        self.sync();
        let loaded = self.sink.external_subset(name.as_deref(), public.as_deref(), system.as_deref());
        let l = match loaded {
            None => return,
            Some(l) => l,
        };
        let old_inputs = core::mem::take(&mut self.inputs);
        let old_encoding = self.encoding.take();
        let mut input = Input::from_bytes(Vec::new());
        input.src = Some(Source { raw: l.bytes, delivered: 0, pos: 0, mode: if l.stream { Mode::Stream } else { Mode::Memory }, enc: None, error: 0, eof: false });
        input.filename = l.filename;
        enc::init_buffer(&mut input);
        self.inputs.push(input);
        self.input_id = sat_add_i32(self.input_id, 1);
        self.sync();
        self.parse_external_subset();
        while self.inputs.len() > 1 {
            self.inputs.pop();
        }
        let consumed = {
            let i = self.inp();
            i.consumed.saturating_add(i.cur.saturating_sub(i.base) as u64)
        };
        self.sink.add_sizeentities(consumed);
        self.inputs = old_inputs;
        self.encoding = old_encoding.clone();
        self.sink.set_encoding(old_encoding.as_deref());
        self.sync();
    }

    /// `xmlParseDocument`.
    #[verifier::external_body]
    pub fn parse_document(&mut self) -> i32 {
        self.grow();
        self.detect_encoding();
        if self.cur() == 0 {
            self.fatal(ERR_DOCUMENT_EMPTY, None);
            return -1;
        }
        self.grow();
        if self.cmp(b"<?xml") && blank(self.nxt(5)) {
            self.parse_xml_decl();
            self.skip_blanks();
        } else {
            self.version = Some(b"1.0".to_vec());
            self.sink.set_version(b"1.0");
        }
        if self.sax_on() {
            self.sync();
            self.sink.start_document();
        }
        self.parse_misc();
        self.grow();
        if self.cmp(b"<!DOCTYPE") {
            self.sink.set_in_subset(1);
            self.parse_doctype_decl();
            if self.cur() == b'[' {
                self.parse_internal_subset();
            } else if self.cur() == b'>' {
                self.next();
            }
            self.sink.set_in_subset(2);
            self.external_subset();
            self.sink.set_in_subset(0);
            self.clean_special_attr();
            self.parse_misc();
        }
        self.grow();
        if self.cur() != b'<' {
            if self.sink.well_formed() {
                self.fatal_msg(ERR_DOCUMENT_EMPTY, b"Start tag expected, '<' not found\n");
            }
        } else {
            self.parse_element();
            self.parse_misc();
            self.check_eof(ERR_DOCUMENT_END);
        }
        self.instate_eof = true;
        self.sink.set_instate_eof();
        self.sync();
        self.sink.end_document();
        if !self.sink.well_formed() {
            self.sink.set_valid(false);
            return -1;
        }
        0
    }
}

/// Parses a document read from `raw` (`Memory`: a whole buffer; `Stream`:
/// a file or descriptor read in chunks), reporting to `sink`; `forced` is
/// an encoding the caller gave (`xmlSwitchEncodingName` before parsing).
#[verifier::external_body]
pub fn parse<S: Sink>(sink: S, raw: Vec<u8>, mode: Mode, filename: Option<Vec<u8>>, forced: Option<&[u8]>) -> S {
    let mut input = Input::from_bytes(Vec::new());
    input.src = Some(Source { raw, delivered: 0, pos: 0, mode, enc: None, error: 0, eof: false });
    input.filename = filename;
    enc::init_buffer(&mut input);
    let mut p = Parser::new(sink, input);
    p.sync();
    if let Some(e) = forced {
        p.switch_encoding_name(e);
    }
    p.parse_document();
    p.sync();
    p.sink
}

} // verus!
