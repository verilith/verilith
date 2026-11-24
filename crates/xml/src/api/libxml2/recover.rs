//! The recovering parser's view of the parser context: `recover::Sink`
//! over `ParserCtxt`, its SAX handler, its error channel and SAX2's tree.
//!
//! When the verified parser rejects a document, `crate::recover` reads it
//! again as libxml2's parser.c does and reports what libxml2 reports; this
//! is the context it reads into. The verified verdict stays: the document is
//! not well-formed whatever the recovering parser makes of it.
use super::codes::*;
use super::parser::*;
use super::sax2::*;
use super::tree::*;
use super::*;
use crate::recover::{self, ContentModel, Ent, EntInfo, InputView, Loaded, NsAttr, Report, Sink};

/// `ParserInput.flags`: the input decodes through an encoder (libxml2's
/// `input->buf->encoder != NULL`), for `xmlFormatError`.
pub const INPUT_ENCODER: c_int = 1 << 28;

pub struct CtxSink {
    c: *mut ParserCtxt,
    /// The entities met, by `Ent`.
    ents: Vec<*mut Entity>,
    /// The inputs shown in `inputTab`; the first is the document's own.
    inputs: Vec<*mut ParserInput>,
    tab: Vec<*mut ParserInput>,
    saved_tab: *mut *mut ParserInput,
    saved_nr: c_int,
    saved_max: c_int,
    /// Saved `nodelen`/`nodemem` (`TreeOp::SaveText`).
    texts: Vec<(c_int, c_int)>,
    /// Temporary roots and the lists taken from them, innermost last.
    roots: Vec<*mut Node>,
    lists: Vec<*mut Node>,
}

unsafe fn handler_of<'a>(c: *mut ParserCtxt) -> Option<&'a SaxHandler> {
    unsafe { if (*c).sax.is_null() { None } else { Some(&*(*c).sax) } }
}

fn cat(parts: &[&[u8]]) -> Vec<u8> {
    parts.concat()
}

fn z(s: &[u8]) -> Vec<u8> {
    nul(s)
}

fn zp(s: &Option<Vec<u8>>) -> *const XChar {
    s.as_ref().map_or(null(), |v| v.as_ptr())
}

impl CtxSink {
    unsafe fn new(c: *mut ParserCtxt) -> CtxSink {
        unsafe {
            CtxSink {
                c,
                ents: Vec::new(),
                inputs: vec![(*c).input],
                tab: Vec::new(),
                saved_tab: (*c).inputTab,
                saved_nr: (*c).inputNr,
                saved_max: (*c).inputMax,
                texts: Vec::new(),
                roots: Vec::new(),
                lists: Vec::new(),
            }
        }
    }

    fn ent(&self, e: Ent) -> *mut Entity {
        if e < self.ents.len() { self.ents[e] } else { null_mut() }
    }

    fn ent_id(&mut self, p: *mut Entity) -> Option<Ent> {
        if p.is_null() {
            return None;
        }
        let mut i = 0;
        while i < self.ents.len() {
            if self.ents[i] == p {
                return Some(i);
            }
            i += 1;
        }
        self.ents.push(p);
        Some(self.ents.len() - 1)
    }

    unsafe fn ud(&self) -> *mut c_void {
        unsafe { (*self.c).userData }
    }

    unsafe fn dict(&self, s: &[u8]) -> *const XChar {
        unsafe { xmlDictLookup((*self.c).dict, s.as_ptr(), s.len() as c_int) }
    }

    unsafe fn dict_opt(&self, s: Option<&[u8]>) -> *const XChar {
        match s {
            None => null(),
            Some(v) => unsafe { self.dict(v) },
        }
    }

    /// Puts the context's input stack back as it was, the document's input
    /// at the end of its bytes.
    unsafe fn restore(&mut self) {
        unsafe {
            let c = self.c;
            let mut k = 1;
            while k < self.inputs.len() {
                let i = self.inputs[k];
                xfree((*i).filename as *mut c_void);
                xfree(i as *mut c_void);
                k += 1;
            }
            self.inputs.truncate(1);
            (*c).inputTab = self.saved_tab;
            (*c).inputNr = self.saved_nr;
            (*c).inputMax = self.saved_max;
            (*c).input = self.inputs[0];
        }
    }

    unsafe fn text_cb(&self, cur: *mut Node) {
        unsafe {
            let c = self.c;
            let Some(h) = handler_of(c) else { return };
            let len = xmlStrlen((*cur).content);
            if (*cur).type_ == TEXT_NODE || (*c).options & PARSE_NOCDATA != 0 {
                if let Some(f) = h.characters {
                    f(self.ud(), (*cur).content, len);
                }
            } else if let Some(f) = h.cdataBlock {
                f(self.ud(), (*cur).content, len);
            }
        }
    }

    unsafe fn content_tree(&self, m: &ContentModel, k: usize) -> *mut ElementContent {
        unsafe {
            let n = &m.nodes[k];
            let full = match (&n.prefix, &n.name) {
                (Some(p), Some(l)) => Some([p.as_slice(), b":", l.as_slice()].concat()),
                (None, Some(l)) => Some(l.clone()),
                _ => None,
            };
            let name = full.as_ref().map(|f| z(f));
            let e = xmlNewDocElementContent((*self.c).myDoc, zp(&name), n.ctype);
            if e.is_null() {
                return e;
            }
            (*e).ocur = n.ocur;
            if let Some(c1) = n.c1 {
                (*e).c1 = self.content_tree(m, c1);
                if !(*e).c1.is_null() {
                    (*(*e).c1).parent = e;
                }
            }
            if let Some(c2) = n.c2 {
                (*e).c2 = self.content_tree(m, c2);
                if !(*e).c2.is_null() {
                    (*(*e).c2).parent = e;
                }
            }
            e
        }
    }

    /// `xmlParseEntityDecl`'s compatibility document: whether there is one
    /// to add the entity to.
    unsafe fn compat_doc(&mut self) -> bool {
        unsafe {
            let c = self.c;
            let doc = (*c).myDoc;
            if !doc.is_null() && copt((*doc).version) != Some(SAX_COMPAT) {
                return false;
            }
            if doc.is_null() {
                let v = z(SAX_COMPAT);
                (*c).myDoc = xmlNewDoc(v.as_ptr());
                if (*c).myDoc.is_null() {
                    return false;
                }
                (*(*c).myDoc).properties = 64;
            }
            let doc = (*c).myDoc;
            if (*doc).intSubset.is_null() {
                (*doc).intSubset = xmlNewDtd(doc, c"fake".as_ptr() as *const XChar, null(), null());
            }
            !(*doc).intSubset.is_null()
        }
    }
}

impl Sink for CtxSink {
    fn options(&self) -> u32 {
        unsafe { (*self.c).options as u32 }
    }
    fn replace_entities(&self) -> bool {
        unsafe { (*self.c).replaceEntities != 0 }
    }
    fn keep_blanks(&self) -> bool {
        unsafe { (*self.c).keepBlanks != 0 }
    }
    fn sax2(&self) -> bool {
        unsafe { (*self.c).sax2 != 0 }
    }
    fn validate(&self) -> bool {
        unsafe { (*self.c).validate != 0 }
    }
    fn recovery(&self) -> bool {
        unsafe { (*self.c).recovery != 0 }
    }
    fn html(&self) -> bool {
        unsafe { (*self.c).html != 0 }
    }
    fn max_ampl(&self) -> u32 {
        unsafe { (*self.c).maxAmpl }
    }
    fn disable_sax(&self) -> i32 {
        unsafe { (*self.c).disableSAX }
    }
    fn well_formed(&self) -> bool {
        unsafe { (*self.c).wellFormed != 0 }
    }
    fn set_well_formed(&mut self, v: bool) {
        unsafe { (*self.c).wellFormed = v as c_int }
    }
    fn err_no(&self) -> i32 {
        unsafe { (*self.c).errNo }
    }
    fn set_ns_well_formed(&mut self, v: bool) {
        unsafe { (*self.c).nsWellFormed = v as c_int }
    }
    fn set_valid(&mut self, v: bool) {
        unsafe { (*self.c).valid = v as c_int }
    }
    fn in_subset(&self) -> i32 {
        unsafe { (*self.c).inSubset }
    }
    fn set_in_subset(&mut self, v: i32) {
        unsafe { (*self.c).inSubset = v }
    }
    fn set_has_ext_subset(&mut self, v: bool) {
        unsafe { (*self.c).hasExternalSubset = v as c_int }
    }
    fn has_ext_subset(&self) -> bool {
        unsafe { (*self.c).hasExternalSubset != 0 }
    }
    fn set_has_perefs(&mut self, v: bool) {
        unsafe { (*self.c).hasPErefs = v as c_int }
    }
    fn has_perefs(&self) -> bool {
        unsafe { (*self.c).hasPErefs != 0 }
    }
    fn set_standalone(&mut self, v: i32) {
        unsafe { (*self.c).standalone = v }
    }
    fn standalone(&self) -> i32 {
        unsafe { (*self.c).standalone }
    }
    fn set_version(&mut self, v: &[u8]) {
        unsafe {
            xfree((*self.c).version as *mut c_void);
            (*self.c).version = xstrdup(v);
        }
    }
    fn set_encoding(&mut self, v: Option<&[u8]>) {
        unsafe {
            xfree((*self.c).encoding as *mut c_void);
            (*self.c).encoding = xstrdup_opt(v);
        }
    }
    fn set_int_subset(&mut self, name: Option<&[u8]>, ext_id: Option<&[u8]>, sys_id: Option<&[u8]>) {
        unsafe {
            let c = self.c;
            (*c).intSubName = self.dict_opt(name);
            xfree((*c).extSubURI as *mut c_void);
            xfree((*c).extSubSystem as *mut c_void);
            (*c).extSubURI = xstrdup_opt(sys_id);
            (*c).extSubSystem = xstrdup_opt(ext_id);
        }
    }
    fn set_instate_eof(&mut self) {
        unsafe { (*self.c).instate = -1 }
    }
    fn halt(&mut self) {
        unsafe { (*self.c).disableSAX = 2 }
    }
    fn stop(&mut self) {
        unsafe { (*self.c).disableSAX = 2 }
    }
    fn mem_error(&mut self) {
        unsafe { ctx_err(self.c, null_mut(), FROM_PARSER, ERR_NO_MEMORY, ERR_FATAL, None, None, None, 0, b"Out of memory\n") }
    }

    fn sync(&mut self, views: &[InputView<'_>]) {
        unsafe {
            let c = self.c;
            while self.inputs.len() > views.len().max(1) {
                let i = self.inputs.pop().unwrap_or(null_mut());
                if !i.is_null() {
                    xfree((*i).filename as *mut c_void);
                    xfree(i as *mut c_void);
                }
            }
            while self.inputs.len() < views.len() {
                let i: *mut ParserInput = xnew();
                self.inputs.push(i);
            }
            let mut k = 0;
            while k < views.len() {
                let v = &views[k];
                let i = self.inputs[k];
                if i.is_null() {
                    k += 1;
                    continue;
                }
                let p = v.buf.as_ptr();
                let len = v.buf.len();
                (*i).base = p.add(v.base.min(len));
                (*i).cur = p.add(v.cur.min(len));
                (*i).end = p.add(len);
                (*i).length = len as c_int;
                (*i).line = v.line;
                (*i).col = v.col;
                (*i).entity = self.ent(v.entity.unwrap_or(usize::MAX));
                if v.encoder {
                    (*i).flags |= INPUT_ENCODER;
                } else {
                    (*i).flags &= !INPUT_ENCODER;
                }
                if k > 0 || v.filename.is_some() {
                    let want = v.filename;
                    if copt((*i).filename as *const XChar) != want {
                        xfree((*i).filename as *mut c_void);
                        (*i).filename = xstrdup_opt(want) as *const c_char;
                    }
                }
                k += 1;
            }
            self.tab.clear();
            self.tab.extend_from_slice(&self.inputs[..views.len().max(1).min(self.inputs.len())]);
            (*c).inputTab = self.tab.as_mut_ptr();
            (*c).inputNr = self.tab.len() as c_int;
            (*c).inputMax = self.tab.len() as c_int;
            (*c).input = *self.tab.last().unwrap_or(&null_mut());
        }
    }

    fn report(&mut self, r: &Report<'_>) {
        let msg = match r.msg {
            Some(m) => m.to_vec(),
            None => {
                let base = message_for(r.code).to_bytes();
                match r.s1 {
                    Some(s) if r.domain != recover::FROM_IO => [base, b": ", s, b"\n"].concat(),
                    _ => [base, b"\n"].concat(),
                }
            }
        };
        unsafe { ctx_err(self.c, null_mut(), r.domain, r.code, r.level, r.s1, r.s2, r.s3, r.int1, &msg) }
    }
    fn sizeentities(&self) -> u64 {
        unsafe { (*self.c).sizeentities as u64 }
    }
    fn sizeentcopy(&self) -> u64 {
        unsafe { (*self.c).sizeentcopy as u64 }
    }
    fn set_sizeentcopy(&mut self, v: u64) {
        unsafe { (*self.c).sizeentcopy = v as c_ulong }
    }
    fn add_sizeentities(&mut self, v: u64) {
        unsafe { (*self.c).sizeentities = ((*self.c).sizeentities as u64).saturating_add(v) as c_ulong }
    }

    // --- SAX ---

    fn start_document(&mut self) {
        unsafe {
            if let Some(f) = handler_of(self.c).and_then(|h| h.startDocument) {
                f(self.ud());
            }
        }
    }
    fn internal_subset(&mut self, name: Option<&[u8]>, ext_id: Option<&[u8]>, sys_id: Option<&[u8]>) {
        unsafe {
            let c = self.c;
            let _ = (name, ext_id, sys_id);
            if let Some(f) = handler_of(c).and_then(|h| h.internalSubset) {
                f(self.ud(), (*c).intSubName, (*c).extSubSystem, (*c).extSubURI);
            }
        }
    }
    fn external_subset(&mut self, _name: Option<&[u8]>, _ext_id: Option<&[u8]>, _sys_id: Option<&[u8]>) -> Option<Loaded> {
        // This ABI does not load DTDs (xmlSAX2ExternalSubset reads
        // nothing); a handler of the caller's is called as libxml2 calls it.
        unsafe {
            let c = self.c;
            if let Some(f) = handler_of(c).and_then(|h| h.externalSubset) {
                f(self.ud(), (*c).intSubName, (*c).extSubSystem, (*c).extSubURI);
            }
        }
        None
    }
    fn ensure_doc_for_subset(&mut self, ext_id: Option<&[u8]>, sys_id: Option<&[u8]>) {
        unsafe {
            let c = self.c;
            if (*c).myDoc.is_null() {
                (*c).myDoc = xmlNewDoc(c"1.0".as_ptr() as *const XChar);
                if (*c).myDoc.is_null() {
                    return;
                }
                (*(*c).myDoc).properties = 64;
            }
            if (*(*c).myDoc).intSubset.is_null() {
                let e = ext_id.map(z);
                let s = sys_id.map(z);
                xmlCreateIntSubset((*c).myDoc, null(), zp(&e), zp(&s));
            }
        }
    }
    fn end_document(&mut self) {
        unsafe {
            let c = self.c;
            if let Some(f) = handler_of(c).and_then(|h| h.endDocument) {
                f(self.ud());
            }
            let doc = (*c).myDoc;
            if !doc.is_null() && copt((*doc).version) == Some(SAX_COMPAT) {
                xmlFreeDoc(doc);
                (*c).myDoc = null_mut();
            }
        }
    }
    fn has_external_subset_cb(&mut self) -> bool {
        unsafe { handler_of(self.c).is_some_and(|h| h.externalSubset.is_some()) }
    }
    fn has_internal_subset_cb(&mut self) -> bool {
        unsafe { handler_of(self.c).is_some_and(|h| h.internalSubset.is_some()) }
    }
    fn entity_decl(&mut self, name: &[u8], etype: i32, public_id: Option<&[u8]>, system_id: Option<&[u8]>, content: Option<&[u8]>) {
        unsafe {
            if let Some(f) = handler_of(self.c).and_then(|h| h.entityDecl) {
                let n = self.dict(name);
                let p = public_id.map(z);
                let s = system_id.map(z);
                let mut v = content.map(z);
                let vp = v.as_mut().map_or(null_mut(), |v| v.as_mut_ptr());
                f(self.ud(), n, etype, zp(&p), zp(&s), vp);
            }
        }
    }
    fn unparsed_entity_decl(&mut self, name: &[u8], public_id: Option<&[u8]>, system_id: Option<&[u8]>, notation: Option<&[u8]>) {
        unsafe {
            if let Some(f) = handler_of(self.c).and_then(|h| h.unparsedEntityDecl) {
                let n = self.dict(name);
                let p = public_id.map(z);
                let s = system_id.map(z);
                let nd = self.dict_opt(notation);
                f(self.ud(), n, zp(&p), zp(&s), nd);
            }
        }
    }
    fn has_unparsed_entity_decl(&self) -> bool {
        unsafe { handler_of(self.c).is_some_and(|h| h.unparsedEntityDecl.is_some()) }
    }
    fn compat_entity_decl(&mut self, name: &[u8], etype: i32, public_id: Option<&[u8]>, system_id: Option<&[u8]>, content: Option<&[u8]>) {
        unsafe {
            if !self.compat_doc() {
                return;
            }
            let n = self.dict(name);
            let p = public_id.map(z);
            let s = system_id.map(z);
            let mut v = content.map(z);
            let vp = v.as_mut().map_or(null_mut(), |v| v.as_mut_ptr());
            xmlSAX2EntityDecl(self.c as Ctx, n, etype, zp(&p), zp(&s), vp);
        }
    }
    fn entity_orig(&mut self, is_pe: bool, name: &[u8], orig: &[u8]) {
        unsafe {
            let c = self.c;
            let n = self.dict(name);
            let ud = self.ud();
            let mut cur: *mut Entity = null_mut();
            if let Some(h) = handler_of(c) {
                if is_pe {
                    if let Some(f) = h.getParameterEntity {
                        cur = f(ud, n);
                    }
                } else {
                    if let Some(f) = h.getEntity {
                        cur = f(ud, n);
                    }
                    if cur.is_null() && ud == c as *mut c_void {
                        cur = xmlSAX2GetEntity(c as Ctx, n);
                    }
                }
            }
            if !cur.is_null() && (*cur).orig.is_null() {
                (*cur).orig = xstrdup(orig);
            }
        }
    }
    fn notation_decl(&mut self, name: &[u8], public_id: Option<&[u8]>, system_id: Option<&[u8]>) {
        unsafe {
            if let Some(f) = handler_of(self.c).and_then(|h| h.notationDecl) {
                let n = self.dict(name);
                let p = public_id.map(z);
                let s = system_id.map(z);
                f(self.ud(), n, zp(&p), zp(&s));
            }
        }
    }
    fn attribute_decl(&mut self, elem: &[u8], name: &[u8], atype: i32, def: i32, default: Option<&[u8]>, tree: Option<Vec<Vec<u8>>>) {
        unsafe {
            let mut head: *mut Enumeration = null_mut();
            let mut last: *mut Enumeration = null_mut();
            for t in tree.iter().flatten() {
                let v = z(t);
                let e = xmlCreateEnumeration(v.as_ptr());
                if last.is_null() {
                    head = e;
                } else {
                    (*last).next = e;
                }
                last = e;
            }
            match handler_of(self.c).and_then(|h| h.attributeDecl) {
                Some(f) => {
                    let e = self.dict(elem);
                    let n = self.dict(name);
                    let d = default.map(z);
                    f(self.ud(), e, n, atype, def, zp(&d), head);
                }
                None => xmlFreeEnumeration(head),
            }
        }
    }
    fn element_decl(&mut self, name: &[u8], etype: i32, content: &ContentModel) {
        unsafe {
            let tree = match content.root {
                Some(r) => self.content_tree(content, r),
                None => null_mut(),
            };
            if let Some(f) = handler_of(self.c).and_then(|h| h.elementDecl) {
                let n = self.dict(name);
                f(self.ud(), n, etype, tree);
            }
            xmlFreeDocElementContent((*self.c).myDoc, tree);
        }
    }
    fn start_element_ns(&mut self, local: &[u8], prefix: Option<&[u8]>, uri: Option<&[u8]>, nss: &[(Option<&[u8]>, &[u8])], atts: &[NsAttr<'_>], nb_defaulted: usize) {
        unsafe {
            let Some(f) = handler_of(self.c).and_then(|h| h.startElementNs) else { return };
            let l = self.dict(local);
            let p = self.dict_opt(prefix);
            let u = self.dict_opt(uri);
            let mut ns: Vec<*const XChar> = Vec::with_capacity(nss.len() * 2);
            for (np, nu) in nss {
                ns.push(self.dict_opt(*np));
                ns.push(self.dict(nu));
            }
            let vals: Vec<Vec<u8>> = atts.iter().map(|a| z(a.value)).collect();
            let mut av: Vec<*const XChar> = Vec::with_capacity(atts.len() * 5);
            for (a, v) in atts.iter().zip(vals.iter()) {
                av.push(self.dict(a.local));
                av.push(self.dict_opt(a.prefix));
                av.push(self.dict_opt(a.uri));
                av.push(v.as_ptr());
                av.push(v.as_ptr().add(a.value.len()));
            }
            let nsp = if ns.is_empty() { null_mut() } else { ns.as_mut_ptr() };
            f(self.ud(), l, p, u, nss.len() as c_int, nsp, atts.len() as c_int, nb_defaulted as c_int, av.as_mut_ptr());
        }
    }
    fn end_element_ns(&mut self, local: &[u8], prefix: Option<&[u8]>, uri: Option<&[u8]>) {
        unsafe {
            if let Some(f) = handler_of(self.c).and_then(|h| h.endElementNs) {
                let l = self.dict(local);
                let p = self.dict_opt(prefix);
                let u = self.dict_opt(uri);
                f(self.ud(), l, p, u);
            }
        }
    }
    fn start_element(&mut self, name: &[u8], atts: &[(&[u8], Option<&[u8]>)]) {
        unsafe {
            let Some(f) = handler_of(self.c).and_then(|h| h.startElement) else { return };
            let n = self.dict(name);
            let vals: Vec<Option<Vec<u8>>> = atts.iter().map(|(_, v)| v.map(z)).collect();
            let mut av: Vec<*const XChar> = Vec::with_capacity(atts.len() * 2 + 2);
            for ((an, _), v) in atts.iter().zip(vals.iter()) {
                av.push(self.dict(an));
                av.push(zp(v));
            }
            if av.is_empty() {
                f(self.ud(), n, null_mut());
            } else {
                av.push(null());
                av.push(null());
                f(self.ud(), n, av.as_mut_ptr());
            }
        }
    }
    fn end_element(&mut self, name: &[u8]) {
        unsafe {
            if let Some(f) = handler_of(self.c).and_then(|h| h.endElement) {
                let n = self.dict(name);
                f(self.ud(), n);
            }
        }
    }
    fn characters(&mut self, s: &[u8]) {
        unsafe {
            if let Some(f) = handler_of(self.c).and_then(|h| h.characters) {
                f(self.ud(), s.as_ptr(), s.len() as c_int);
            }
        }
    }
    fn ignorable_whitespace(&mut self, s: &[u8]) {
        unsafe {
            if let Some(f) = handler_of(self.c).and_then(|h| h.ignorableWhitespace) {
                f(self.ud(), s.as_ptr(), s.len() as c_int);
            }
        }
    }
    fn blanks_same_as_chars(&self) -> bool {
        unsafe { handler_of(self.c).is_some_and(|h| h.ignorableWhitespace.map(|f| f as usize) == h.characters.map(|f| f as usize)) }
    }
    fn has_characters(&self) -> bool {
        unsafe { handler_of(self.c).is_some_and(|h| h.characters.is_some()) }
    }
    fn cdata_block(&mut self, s: &[u8]) {
        unsafe {
            if let Some(f) = handler_of(self.c).and_then(|h| h.cdataBlock) {
                let v = z(s);
                f(self.ud(), v.as_ptr(), s.len() as c_int);
            }
        }
    }
    fn has_cdata_block(&self) -> bool {
        unsafe { handler_of(self.c).is_some_and(|h| h.cdataBlock.is_some()) }
    }
    fn processing_instruction(&mut self, target: &[u8], data: Option<&[u8]>) {
        unsafe {
            if let Some(f) = handler_of(self.c).and_then(|h| h.processingInstruction) {
                let t = self.dict(target);
                let d = data.map(z);
                f(self.ud(), t, zp(&d));
            }
        }
    }
    fn comment(&mut self, s: &[u8]) {
        unsafe {
            if let Some(f) = handler_of(self.c).and_then(|h| h.comment) {
                let v = z(s);
                f(self.ud(), v.as_ptr());
            }
        }
    }
    fn reference(&mut self, name: &[u8]) {
        unsafe {
            if let Some(f) = handler_of(self.c).and_then(|h| h.reference) {
                let n = self.dict(name);
                f(self.ud(), n);
            }
        }
    }
    fn has_reference(&self) -> bool {
        unsafe { handler_of(self.c).is_some_and(|h| h.reference.is_some()) }
    }

    // --- entities ---

    fn get_entity(&mut self, name: &[u8]) -> Option<Ent> {
        unsafe {
            let f = handler_of(self.c).and_then(|h| h.getEntity)?;
            let n = self.dict(name);
            let p = f(self.ud(), n);
            self.ent_id(p)
        }
    }
    fn has_get_entity(&self) -> bool {
        unsafe { handler_of(self.c).is_some_and(|h| h.getEntity.is_some()) }
    }
    fn get_parameter_entity(&mut self, name: &[u8]) -> Option<Ent> {
        unsafe {
            let f = handler_of(self.c).and_then(|h| h.getParameterEntity)?;
            let n = self.dict(name);
            let p = f(self.ud(), n);
            self.ent_id(p)
        }
    }
    fn has_get_parameter_entity(&self) -> bool {
        unsafe { handler_of(self.c).is_some_and(|h| h.getParameterEntity.is_some()) }
    }
    fn sax2_get_entity(&mut self, name: &[u8]) -> Option<Ent> {
        unsafe {
            if self.ud() != self.c as *mut c_void {
                return None;
            }
            let n = self.dict(name);
            let p = xmlSAX2GetEntity(self.c as Ctx, n);
            self.ent_id(p)
        }
    }
    fn predefined_entity(&mut self, name: &[u8]) -> Option<Ent> {
        unsafe {
            let n = z(name);
            let p = xmlGetPredefinedEntity(n.as_ptr());
            self.ent_id(p)
        }
    }
    fn ent_info(&self, e: Ent) -> EntInfo {
        let p = self.ent(e);
        if p.is_null() {
            return EntInfo { etype: 0, flags: 0, expanded_size: 0, has_content: false, length: 0, has_children: false, has_uri: false };
        }
        unsafe {
            EntInfo {
                etype: (*p).etype,
                flags: (*p).flags as u32,
                expanded_size: (*p).expandedSize as u64,
                has_content: !(*p).content.is_null(),
                length: (*p).length.max(0) as usize,
                has_children: !(*p).children.is_null(),
                has_uri: !(*p).URI.is_null(),
            }
        }
    }
    fn ent_content(&self, e: Ent) -> Vec<u8> {
        let p = self.ent(e);
        if p.is_null() {
            return Vec::new();
        }
        unsafe { copt((*p).content).map_or(Vec::new(), |v| v.to_vec()) }
    }
    fn ent_name(&self, e: Ent) -> Vec<u8> {
        let p = self.ent(e);
        if p.is_null() {
            return Vec::new();
        }
        unsafe { copt((*p).name).map_or(Vec::new(), |v| v.to_vec()) }
    }
    fn ent_set_flags(&mut self, e: Ent, flags: u32) {
        let p = self.ent(e);
        if !p.is_null() {
            unsafe { (*p).flags = flags as c_int }
        }
    }
    fn ent_set_expanded_size(&mut self, e: Ent, v: u64) {
        let p = self.ent(e);
        if !p.is_null() {
            unsafe { (*p).expandedSize = v as c_ulong }
        }
    }
    fn ent_truncate_content(&mut self, e: Ent) {
        let p = self.ent(e);
        unsafe {
            if !p.is_null() && !(*p).content.is_null() {
                *(*p).content = 0;
            }
        }
    }
    fn load_entity(&mut self, e: Ent) -> Option<Loaded> {
        unsafe {
            let p = self.ent(e);
            if p.is_null() {
                return None;
            }
            let uri = copt((*p).URI)?.to_vec();
            let c = self.c;
            if (*c).options & PARSE_NO_XXE != 0 {
                let msg = cat(&[b"failed to load \"", &uri[..], b"\": ", message_for(IO_UNKNOWN).to_bytes(), b"\n"]);
                ctx_err(c, null_mut(), FROM_IO, IO_UNKNOWN, if (*c).validate == 0 { ERR_WARNING } else { ERR_ERROR }, Some(&uri), None, None, 0, &msg);
                return None;
            }
            match load_resource(&uri) {
                Ok(bytes) => Some(Loaded { bytes, stream: true, filename: Some(uri) }),
                Err(code) => {
                    let level = if code == IO_ENOENT || code == IO_UNKNOWN {
                        if (*c).validate == 0 { ERR_WARNING } else { ERR_ERROR }
                    } else {
                        ERR_FATAL
                    };
                    let msg = cat(&[b"failed to load \"", &uri[..], b"\": ", message_for(code).to_bytes(), b"\n"]);
                    ctx_err(c, null_mut(), FROM_IO, code, level, Some(&uri), None, None, 0, &msg);
                    None
                }
            }
        }
    }
    fn ent_set_content(&mut self, e: Ent, content: Vec<u8>) {
        let p = self.ent(e);
        if p.is_null() {
            return;
        }
        unsafe {
            xfree((*p).content as *mut c_void);
            (*p).content = xstrdup(&content);
            (*p).length = content.len() as c_int;
        }
    }
    fn reference_tree(&mut self, e: Ent, _first: bool) {
        unsafe {
            let c = self.c;
            let ent = self.ent(e);
            if ent.is_null() || (*ent).children.is_null() || (*c).node.is_null() {
                return;
            }
            let mut cur = (*ent).children;
            if matches!((*cur).type_, TEXT_NODE | CDATA_SECTION_NODE) {
                self.text_cb(cur);
                cur = (*cur).next;
            }
            while !cur.is_null() {
                if (*cur).next.is_null() && matches!((*cur).type_, TEXT_NODE | CDATA_SECTION_NODE) {
                    self.text_cb(cur);
                    break;
                }
                (*c).nodemem = 0;
                (*c).nodelen = 0;
                let copy = xmlDocCopyNode(cur, (*c).myDoc, 1);
                if copy.is_null() {
                    self.mem_error();
                    break;
                }
                let node = (*c).node;
                (*copy).parent = node;
                let last = (*node).last;
                if last.is_null() {
                    (*node).children = copy;
                } else {
                    (*last).next = copy;
                    (*copy).prev = last;
                }
                (*node).last = copy;
                cur = (*cur).next;
            }
        }
    }
    fn ent_tree(&mut self, op: recover::refs::TreeOp, e: Ent) {
        use recover::refs::TreeOp::*;
        unsafe {
            let c = self.c;
            match op {
                SaveText => {
                    self.texts.push(((*c).nodelen, (*c).nodemem));
                    (*c).nodelen = 0;
                    (*c).nodemem = 0;
                }
                RestoreText => {
                    if let Some((l, m)) = self.texts.pop() {
                        (*c).nodelen = l;
                        (*c).nodemem = m;
                    }
                }
                NewRoot => {
                    let r = xmlNewDocNode((*c).myDoc, null_mut(), c"#root".as_ptr() as *const XChar, null());
                    self.roots.push(r);
                    self.lists.push(null_mut());
                }
                PushRoot => {
                    let r = self.roots.last().copied().unwrap_or(null_mut());
                    if !r.is_null() {
                        node_push(c, r);
                    }
                }
                TakeList => {
                    let r = self.roots.last().copied().unwrap_or(null_mut());
                    if !r.is_null() {
                        let list = (*r).children;
                        (*r).children = null_mut();
                        (*r).last = null_mut();
                        let mut x = list;
                        while !x.is_null() {
                            (*x).parent = null_mut();
                            x = (*x).next;
                        }
                        if let Some(l) = self.lists.last_mut() {
                            *l = list;
                        }
                    }
                }
                PopRoot => {
                    node_pop(c);
                }
                FreeRoot => {
                    if let Some(r) = self.roots.pop() {
                        xmlFreeNode(r);
                    }
                }
                KeepList | ClearChildren | FreeList => {
                    let list = self.lists.pop().unwrap_or(null_mut());
                    let ent = self.ent(e);
                    if ent.is_null() {
                        xmlFreeNodeList(list);
                        return;
                    }
                    if op == FreeList {
                        xmlFreeNodeList(list);
                        return;
                    }
                    let list = if op == ClearChildren { null_mut() } else { list };
                    (*ent).children = list;
                    let mut x = list;
                    while !x.is_null() {
                        (*x).parent = ent as *mut Node;
                        if (*x).doc != (*ent).doc {
                            xmlSetTreeDoc(x, (*ent).doc);
                        }
                        if (*x).next.is_null() {
                            (*ent).last = x;
                        }
                        x = (*x).next;
                    }
                }
            }
        }
    }
    fn has_node(&self) -> bool {
        unsafe { !(*self.c).node.is_null() }
    }
    fn node_nr(&self) -> usize {
        unsafe { (*self.c).nodeNr.max(0) as usize }
    }
    fn node_pop(&mut self) {
        unsafe {
            node_pop(self.c);
        }
    }
    fn validate_root(&mut self) {
        // This ABI does not validate (there is no xmlValidateRoot).
    }
    fn catastrophic(&self) -> bool {
        unsafe { xmlIsCatastrophicError((*self.c).lastError.level, (*self.c).lastError.code) != 0 }
    }
    fn blanks_ignorable_in_tree(&mut self, next: [u8; 2]) -> bool {
        unsafe {
            let c = self.c;
            let node = (*c).node;
            if node.is_null() {
                return false;
            }
            let doc = (*c).myDoc;
            if !doc.is_null() {
                let prefix = if (*node).ns.is_null() { null() } else { (*(*node).ns).prefix };
                let mut decl = null_mut();
                if !(*doc).intSubset.is_null() {
                    decl = xmlGetDtdQElementDesc((*doc).intSubset, (*node).name, prefix);
                }
                if decl.is_null() && !(*doc).extSubset.is_null() {
                    decl = xmlGetDtdQElementDesc((*doc).extSubset, (*node).name, prefix);
                }
                if !decl.is_null() {
                    match (*decl).etype {
                        ELEMENT_TYPE_ELEMENT => return true,
                        ELEMENT_TYPE_ANY | ELEMENT_TYPE_MIXED => return false,
                        _ => {}
                    }
                }
            }
            if next[0] != b'<' && next[0] != 0x0D {
                return false;
            }
            if (*node).children.is_null() && next[0] == b'<' && next[1] == b'/' {
                return false;
            }
            let last = xmlGetLastChild(node);
            if last.is_null() {
                if (*node).type_ != ELEMENT_NODE && !(*node).content.is_null() {
                    return false;
                }
            } else if xmlNodeIsText(last) != 0 || (!(*node).children.is_null() && xmlNodeIsText((*node).children) != 0) {
                return false;
            }
            true
        }
    }

    // --- namespaces ---

    fn ns_pushed(&mut self, prefix: Option<&[u8]>, uri: &[u8]) {
        unsafe {
            let p = self.dict_opt(prefix);
            let u = self.dict(uri);
            ns_mirror_push(self.c, p, u);
        }
    }
    fn ns_popped(&mut self, n: usize) {
        unsafe { ns_mirror_pop(self.c, n) }
    }
    fn ns_min(&mut self, min: usize) {
        unsafe { ns_mirror_min(self.c, min) }
    }
    fn uri_check(&self, uri: &[u8]) -> (bool, bool) {
        parser_uri_check(uri)
    }
}

/// An external resource's bytes (`xmlLoadResource` with the default
/// loader: the I/O callbacks, then the file), or the I/O error code.
pub(crate) fn load_resource(uri: &[u8]) -> Result<Vec<u8>, c_int> {
    match unsafe { super::io::read_by_callbacks(uri) } {
        Some(Some(d)) => Ok(d),
        Some(None) => Err(IO_UNKNOWN),
        None => match read_resource(uri) {
            Ok(d) => Ok(d),
            Err(e) => Err(if e.kind() == std::io::ErrorKind::NotFound { IO_ENOENT } else { IO_UNKNOWN }),
        },
    }
}

/// Parses the document at the context's input with the recovering parser:
/// `raw` as read (`stream` for a file or descriptor, read in chunks).
pub unsafe fn recover_document(c: *mut ParserCtxt, raw: Vec<u8>, stream: bool, forced: Option<&[u8]>) {
    unsafe {
        let filename = {
            let i = (*c).input;
            if i.is_null() { None } else { copt((*i).filename as *const XChar).map(|v| v.to_vec()) }
        };
        let sink = CtxSink::new(c);
        let mode = if stream { recover::Mode::Stream } else { recover::Mode::Memory };
        let mut sink = recover::parse(sink, raw, mode, filename, forced);
        sink.restore();
    }
}
