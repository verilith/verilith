//! libxml2's default SAX2 handlers (SAX2.c): the tree builder.
use super::parser::{ctx_err, ns_lookup_sax, ns_update_sax, node_pop, node_push, ParserCtxt};
use super::tree::*;
use super::*;

unsafe fn c(ctx: Ctx) -> *mut ParserCtxt {
    ctx as *mut ParserCtxt
}

fn err_memory(ctxt: *mut ParserCtxt) {
    unsafe { ctx_err(ctxt, null_mut(), FROM_PARSER, ERR_NO_MEMORY, ERR_FATAL, None, None, None, 0, b"Out of memory\n") };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAX2GetPublicId(_ctx: Ctx) -> *const XChar {
    null()
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAX2GetSystemId(ctx: Ctx) -> *const XChar {
    let ctxt = unsafe { c(ctx) };
    if ctxt.is_null() || unsafe { (*ctxt).input }.is_null() {
        return null();
    }
    unsafe { (*(*ctxt).input).filename as *const XChar }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAX2GetLineNumber(ctx: Ctx) -> c_int {
    let ctxt = unsafe { c(ctx) };
    if ctxt.is_null() || unsafe { (*ctxt).input }.is_null() {
        return 0;
    }
    unsafe { (*(*ctxt).input).line }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAX2GetColumnNumber(ctx: Ctx) -> c_int {
    let ctxt = unsafe { c(ctx) };
    if ctxt.is_null() || unsafe { (*ctxt).input }.is_null() {
        return 0;
    }
    unsafe { (*(*ctxt).input).col }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAX2IsStandalone(ctx: Ctx) -> c_int {
    let ctxt = unsafe { c(ctx) };
    if ctxt.is_null() || unsafe { (*ctxt).myDoc }.is_null() {
        return 0;
    }
    (unsafe { (*(*ctxt).myDoc).standalone } == 1) as c_int
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAX2HasInternalSubset(ctx: Ctx) -> c_int {
    let ctxt = unsafe { c(ctx) };
    if ctxt.is_null() || unsafe { (*ctxt).myDoc }.is_null() {
        return 0;
    }
    (!unsafe { (*(*ctxt).myDoc).intSubset }.is_null()) as c_int
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAX2HasExternalSubset(ctx: Ctx) -> c_int {
    let ctxt = unsafe { c(ctx) };
    if ctxt.is_null() || unsafe { (*ctxt).myDoc }.is_null() {
        return 0;
    }
    (!unsafe { (*(*ctxt).myDoc).extSubset }.is_null()) as c_int
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAX2InternalSubset(ctx: Ctx, name: *const XChar, pubid: *const XChar, sysid: *const XChar) {
    let ctxt = unsafe { c(ctx) };
    if ctxt.is_null() {
        return;
    }
    unsafe {
        let doc = (*ctxt).myDoc;
        if doc.is_null() {
            return;
        }
        let dtd = xmlGetIntSubset(doc);
        if !dtd.is_null() {
            xmlUnlinkNode(dtd as *mut Node);
            xmlFreeDtd(dtd);
            (*doc).intSubset = null_mut();
        }
        (*doc).intSubset = xmlCreateIntSubset(doc, name, pubid, sysid);
        if (*doc).intSubset.is_null() {
            err_memory(ctxt);
        }
    }
}

/// The external subset is not read: this ABI does not load DTDs.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAX2ExternalSubset(_ctx: Ctx, _name: *const XChar, _pubid: *const XChar, _sysid: *const XChar) {}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAX2ResolveEntity(_ctx: Ctx, _pubid: *const XChar, _sysid: *const XChar) -> *mut c_void {
    null_mut()
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAX2GetEntity(ctx: Ctx, name: *const XChar) -> *mut Entity {
    let ctxt = unsafe { c(ctx) };
    if ctxt.is_null() {
        return null_mut();
    }
    unsafe {
        if (*ctxt).inSubset == 0 {
            let r = xmlGetPredefinedEntity(name);
            if !r.is_null() {
                return r;
            }
        }
        let doc = (*ctxt).myDoc;
        if !doc.is_null() && (*doc).standalone == 1 {
            if (*ctxt).inSubset == 2 {
                (*doc).standalone = 0;
                let r = xmlGetDocEntity(doc, name);
                (*doc).standalone = 1;
                return r;
            }
            let mut r = xmlGetDocEntity(doc, name);
            if r.is_null() {
                (*doc).standalone = 0;
                r = xmlGetDocEntity(doc, name);
                if !r.is_null() {
                    let n = cbytes(name);
                    let msg = [b"Entity(".as_slice(), n, b") document marked standalone but requires external subset\n"].concat();
                    ctx_err(ctxt, null_mut(), FROM_PARSER, 1, ERR_FATAL, Some(n), None, None, 0, &msg);
                }
                (*doc).standalone = 1;
            }
            return r;
        }
        xmlGetDocEntity(doc, name)
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAX2GetParameterEntity(ctx: Ctx, name: *const XChar) -> *mut Entity {
    let ctxt = unsafe { c(ctx) };
    if ctxt.is_null() {
        return null_mut();
    }
    unsafe { xmlGetParameterEntity((*ctxt).myDoc, name) }
}

fn warn(ctxt: *mut ParserCtxt, code: c_int, msg: &[u8], s1: Option<&[u8]>) {
    unsafe { ctx_err(ctxt, null_mut(), FROM_PARSER, code, ERR_WARNING, s1, None, None, 0, msg) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAX2EntityDecl(ctx: Ctx, name: *const XChar, ty: c_int, pubid: *const XChar, sysid: *const XChar, content: *mut XChar) {
    let ctxt = unsafe { c(ctx) };
    if ctxt.is_null() || unsafe { (*ctxt).myDoc }.is_null() {
        return;
    }
    unsafe {
        let ext = (*ctxt).inSubset == 2;
        let mut ent = null_mut();
        let res = xmlAddEntity((*ctxt).myDoc, ext as c_int, name, ty, pubid, sysid, content, &mut ent);
        let n = cbytes(name);
        match res {
            0 => {}
            ERR_NO_MEMORY => return err_memory(ctxt),
            WAR_ENTITY_REDEFINED => {
                if (*ctxt).pedantic != 0 {
                    let w = if ext { b"external".as_slice() } else { b"internal" };
                    let msg = [b"Entity(".as_slice(), n, b") already defined in the ", w, b" subset\n"].concat();
                    warn(ctxt, res, &msg, Some(n));
                }
                return;
            }
            ERR_REDECL_PREDEF_ENTITY => {
                let msg = [b"Invalid redeclaration of predefined entity '".as_slice(), n, b"'"].concat();
                warn(ctxt, res, &msg, Some(n));
                return;
            }
            _ => {
                ctx_err(ctxt, null_mut(), FROM_PARSER, ERR_INTERNAL_ERROR, ERR_FATAL, None, None, None, 0, b"Unexpected error code from xmlAddEntity\n");
                return;
            }
        }
        if (*ent).URI.is_null() && !sysid.is_null() {
            let base = super::parser::base_uri(ctxt);
            let uri = super::parser::build_uri(cbytes(sysid), base.as_deref());
            (*ent).URI = xstrdup(&uri);
        }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAX2AttributeDecl(
    ctx: Ctx,
    elem: *const XChar,
    fullname: *const XChar,
    ty: c_int,
    def: c_int,
    default: *const XChar,
    tree: *mut Enumeration,
) {
    let ctxt = unsafe { c(ctx) };
    if ctxt.is_null() || unsafe { (*ctxt).myDoc }.is_null() {
        unsafe { xmlFreeEnumeration(tree) };
        return;
    }
    unsafe {
        let full = cbytes(fullname);
        if full == b"xml:id" && ty != ATTRIBUTE_ID {
            ctx_err(ctxt, null_mut(), FROM_VALID, 541, ERR_ERROR, None, None, None, 0, b"xml:id : attribute type should be ID\n");
        }
        // xmlSplitQName4: a prefix only before a colon that is not first.
        let (prefix, name): (Option<&[u8]>, &[u8]) = match full.iter().position(|&x| x == b':') {
            Some(k) if k > 0 && k + 1 < full.len() => (Some(&full[..k]), &full[k + 1..]),
            _ => (None, full),
        };
        let dtd = match (*ctxt).inSubset {
            1 => (*(*ctxt).myDoc).intSubset,
            2 => (*(*ctxt).myDoc).extSubset,
            _ => {
                let msg = [b"SAX.xmlSAX2AttributeDecl(".as_slice(), name, b") called while not in subset\n"].concat();
                ctx_err(ctxt, null_mut(), FROM_PARSER, ERR_INTERNAL_ERROR, ERR_FATAL, Some(name), None, None, 0, &msg);
                xmlFreeEnumeration(tree);
                return;
            }
        };
        let a = add_attribute_decl(dtd, cbytes(elem), name, prefix, ty, def, copt(default), tree);
        if a.is_null() {
            // A redeclaration: libxml2 warns only when validating.
        }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAX2ElementDecl(ctx: Ctx, name: *const XChar, ty: c_int, content: *mut ElementContent) {
    let ctxt = unsafe { c(ctx) };
    if ctxt.is_null() || unsafe { (*ctxt).myDoc }.is_null() {
        return;
    }
    unsafe {
        let dtd = match (*ctxt).inSubset {
            1 => (*(*ctxt).myDoc).intSubset,
            2 => (*(*ctxt).myDoc).extSubset,
            _ => {
                let n = cbytes(name);
                let msg = [b"SAX.xmlSAX2ElementDecl(".as_slice(), n, b") called while not in subset\n"].concat();
                ctx_err(ctxt, null_mut(), FROM_PARSER, ERR_INTERNAL_ERROR, ERR_FATAL, Some(n), None, None, 0, &msg);
                return;
            }
        };
        let e = add_element_decl(dtd, cbytes(name), ty, content);
        if e.is_null() {
            (*ctxt).valid = 0;
        }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAX2NotationDecl(ctx: Ctx, name: *const XChar, pubid: *const XChar, sysid: *const XChar) {
    let ctxt = unsafe { c(ctx) };
    if ctxt.is_null() || unsafe { (*ctxt).myDoc }.is_null() {
        return;
    }
    unsafe {
        let n = cbytes(name);
        if pubid.is_null() && sysid.is_null() {
            let msg = [b"SAX.xmlSAX2NotationDecl(".as_slice(), n, b") externalID or PublicID missing\n"].concat();
            ctx_err(ctxt, null_mut(), FROM_PARSER, 105, ERR_FATAL, Some(n), None, None, 0, &msg);
            return;
        }
        let dtd = match (*ctxt).inSubset {
            1 => (*(*ctxt).myDoc).intSubset,
            2 => (*(*ctxt).myDoc).extSubset,
            _ => {
                let msg = [b"SAX.xmlSAX2NotationDecl(".as_slice(), n, b") called while not in subset\n"].concat();
                ctx_err(ctxt, null_mut(), FROM_PARSER, 105, ERR_FATAL, Some(n), None, None, 0, &msg);
                return;
            }
        };
        if add_notation(dtd, n, copt(pubid), copt(sysid)).is_null() {
            (*ctxt).valid = 0;
        }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAX2UnparsedEntityDecl(ctx: Ctx, name: *const XChar, pubid: *const XChar, sysid: *const XChar, notation: *const XChar) {
    unsafe { xmlSAX2EntityDecl(ctx, name, EXTERNAL_GENERAL_UNPARSED_ENTITY, pubid, sysid, notation as *mut XChar) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAX2SetDocumentLocator(_ctx: Ctx, _loc: *mut SaxLocator) {}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAX2StartDocument(ctx: Ctx) {
    let ctxt = unsafe { c(ctx) };
    if ctxt.is_null() {
        return;
    }
    unsafe {
        let doc = xmlNewDoc((*ctxt).version);
        (*ctxt).myDoc = doc;
        if doc.is_null() {
            return err_memory(ctxt);
        }
        (*doc).properties = 0;
        if (*ctxt).options & PARSE_OLD10 != 0 {
            (*doc).properties |= DOC_OLD10;
        }
        (*doc).parseFlags = (*ctxt).options;
        (*doc).standalone = (*ctxt).standalone;
        if (*ctxt).dictNames != 0 {
            (*doc).dict = (*ctxt).dict as *mut c_void;
            xmlDictReference((*doc).dict as *mut Dict);
        }
        let input = (*ctxt).input;
        if (*doc).URL.is_null() && !input.is_null() && !(*input).filename.is_null() {
            (*doc).URL = xstrdup(&super::parser::path_to_uri(cbytes((*input).filename as *const XChar)));
        }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAX2EndDocument(ctx: Ctx) {
    let ctxt = unsafe { c(ctx) };
    if ctxt.is_null() {
        return;
    }
    unsafe {
        let doc = (*ctxt).myDoc;
        if doc.is_null() {
            return;
        }
        if (*doc).encoding.is_null() {
            if let Some(e) = super::parser::actual_encoding(ctxt) {
                (*doc).encoding = xstrdup(&e);
            }
        }
        if (*ctxt).wellFormed != 0 {
            (*doc).properties |= DOC_WELLFORMED;
            if (*ctxt).valid != 0 {
                (*doc).properties |= DOC_DTDVALID;
            }
            if (*ctxt).nsWellFormed != 0 {
                (*doc).properties |= DOC_NSVALID;
            }
        }
        if (*ctxt).options & PARSE_OLD10 != 0 {
            (*doc).properties |= DOC_OLD10;
        }
    }
}

/// xmlSAX2AppendChild: under the subset being read, the current node, or
/// the document.
pub unsafe fn append_child(ctxt: *mut ParserCtxt, node: *mut Node) {
    unsafe {
        let parent: *mut Node = match (*ctxt).inSubset {
            1 => (*(*ctxt).myDoc).intSubset as *mut Node,
            2 => (*(*ctxt).myDoc).extSubset as *mut Node,
            _ => {
                if (*ctxt).node.is_null() {
                    (*ctxt).myDoc as *mut Node
                } else {
                    (*ctxt).node
                }
            }
        };
        if parent.is_null() {
            xmlFreeNode(node);
            return;
        }
        append(parent, node);
        if (*node).type_ != TEXT_NODE && !(*ctxt).input.is_null() {
            let l = (*(*ctxt).input).line;
            (*node).line = if (l as u32) < 65535 { l as c_ushort } else { 65535 };
        }
    }
}

unsafe fn text_node(ctxt: *mut ParserCtxt, doc: *mut Doc, s: &[u8]) -> *mut Node {
    let _ = ctxt;
    new_text(doc, s)
}

/// SAX1: the namespace declarations of a start tag become the element's,
/// then the element's namespace and its attributes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAX2StartElement(ctx: Ctx, fullname: *const XChar, atts: *mut *const XChar) {
    let ctxt = unsafe { c(ctx) };
    if ctxt.is_null() || fullname.is_null() || unsafe { (*ctxt).myDoc }.is_null() {
        return;
    }
    unsafe {
        let doc = (*ctxt).myDoc;
        let full = cbytes(fullname);
        let (prefix, local) = split_qname(full);
        let n = new_node(doc, ELEMENT_NODE, node_name(doc, if prefix.is_some() { local } else { full }));
        if n.is_null() {
            return err_memory(ctxt);
        }
        let n = {
            if let Some(f) = (*globals()).register_node {
                f(n);
            }
            n
        };
        append_child(ctxt, n);
        if node_push(ctxt, n) < 0 {
            xmlUnlinkNode(n);
            xmlFreeNode(n);
            return;
        }
        // Namespace declarations.
        let mut pairs: Vec<(&[u8], &[u8])> = Vec::new();
        if !atts.is_null() {
            let mut i = 0;
            while !(*atts.add(i)).is_null() {
                let an = cbytes(*atts.add(i));
                let av = copt(*atts.add(i + 1)).unwrap_or(b"");
                pairs.push((an, av));
                i += 2;
            }
        }
        for &(an, av) in &pairs {
            if an == b"xmlns" {
                xmlNewNs(n, av.as_ptr_nul().as_ptr(), null());
            } else if let Some(p) = an.strip_prefix(b"xmlns:") {
                if av.is_empty() {
                    let msg = [b"xmlns:".as_slice(), p, b": Empty XML namespace is not allowed\n"].concat();
                    ctx_err(ctxt, null_mut(), FROM_NAMESPACE, 201, ERR_ERROR, Some(p), None, None, 0, &msg);
                    continue;
                }
                let z = nul(p);
                xmlNewNs(n, av.as_ptr_nul().as_ptr(), z.as_ptr());
            }
        }
        // The element's namespace.
        let pz = prefix.map(nul);
        let mut ns = xmlSearchNs(doc, n, pz.as_ref().map_or(null(), |p| p.as_ptr()));
        if ns.is_null() {
            if let Some(p) = prefix {
                let msg = [b"Namespace prefix ".as_slice(), p, b" is not defined\n"].concat();
                ctx_err(ctxt, null_mut(), FROM_NAMESPACE, 201, ERR_ERROR, Some(p), None, None, 0, &msg);
                ns = new_ns(n, None, Some(p));
            }
        }
        (*n).ns = ns;
        for &(an, av) in &pairs {
            if an == b"xmlns" || an.starts_with(b"xmlns:") {
                continue;
            }
            let (ap, al) = split_qname(an);
            let mut ans: *mut Ns = null_mut();
            let mut aname = an;
            if let Some(p) = ap {
                let z = nul(p);
                ans = xmlSearchNs(doc, n, z.as_ptr());
                if ans.is_null() {
                    let msg = [b"Namespace prefix ".as_slice(), p, b" of attribute ", al, b" is not defined\n"].concat();
                    ctx_err(ctxt, null_mut(), FROM_NAMESPACE, 201, ERR_ERROR, Some(p), Some(al), None, 0, &msg);
                } else {
                    aname = al;
                }
            }
            let a = new_prop(n, ans, aname, None, None);
            if a.is_null() {
                continue;
            }
            let kids = if (*ctxt).replaceEntities == 0 {
                string_get_node_list(doc, av, false)
            } else {
                new_text(doc, av)
            };
            let mut k = kids;
            (*a).children = kids;
            while !k.is_null() {
                (*k).parent = a as *mut Node;
                (*a).last = k;
                k = (*k).next;
            }
        }
    }
}

trait AsNul {
    fn as_ptr_nul(&self) -> Vec<u8>;
}

impl AsNul for [u8] {
    fn as_ptr_nul(&self) -> Vec<u8> {
        nul(self)
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAX2EndElement(ctx: Ctx, _name: *const XChar) {
    let ctxt = unsafe { c(ctx) };
    if ctxt.is_null() {
        return;
    }
    unsafe {
        (*ctxt).nodemem = -1;
        node_pop(ctxt);
    }
}

/// xmlSAX2AttributeNs: an attribute of the current node.
unsafe fn attribute_ns(ctxt: *mut ParserCtxt, localname: *const XChar, prefix: *const XChar, value: *const XChar, valueend: *const XChar) -> *mut Attr {
    unsafe {
        let mut ns: *mut Ns = null_mut();
        if !prefix.is_null() {
            ns = ns_lookup_sax(ctxt, prefix);
            if ns.is_null() && cbytes(prefix) == b"xml" {
                ns = xmlSearchNs((*(*ctxt).node).doc, (*ctxt).node, prefix);
            }
        }
        let a: *mut Attr = xnew();
        if a.is_null() {
            err_memory(ctxt);
            return a;
        }
        let node = (*ctxt).node;
        (*a).type_ = ATTRIBUTE_NODE;
        (*a).parent = node;
        (*a).doc = (*node).doc;
        (*a).ns = ns;
        (*a).name = if (*ctxt).dictNames != 0 { localname } else { xstrdup(cbytes(localname)) };
        if let Some(f) = (*globals()).register_node {
            f(a as *mut Node);
        }
        let len = valueend.offset_from(value) as usize;
        let v = std::slice::from_raw_parts(value, len);
        let doc = (*a).doc;
        let kids = if (*ctxt).replaceEntities == 0 && *valueend == 0 {
            if len > 0 { string_get_node_list(doc, v, false) } else { null_mut() }
        } else {
            text_node(ctxt, doc, v)
        };
        let mut k = kids;
        (*a).children = kids;
        while !k.is_null() {
            (*k).parent = a as *mut Node;
            (*a).last = k;
            k = (*k).next;
        }
        // IDs: xml:id, and attributes declared ID.
        let kids = (*a).children;
        if (*ctxt).loadsubset & SKIP_IDS == 0 && !kids.is_null() && (*kids).type_ == TEXT_NODE && (*kids).next.is_null() {
            let content = (*kids).content;
            let is_xml = !prefix.is_null() && cbytes(prefix) == b"xml";
            if is_xml && cbytes(localname) == b"id" {
                if xmlValidateNCName(content, 1) != 0 {
                    let msg = [b"xml:id : attribute value ".as_slice(), cbytes(content), b" is not an NCName\n"].concat();
                    ctx_err(ctxt, null_mut(), FROM_VALID, 540, ERR_ERROR, Some(cbytes(content)), None, None, 0, &msg);
                }
                xmlAddIDSafe(a, content);
            } else if xmlIsID((*ctxt).myDoc, node, a) > 0 {
                xmlAddIDSafe(a, content);
            }
        }
        a
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAX2StartElementNs(
    ctx: Ctx,
    localname: *const XChar,
    prefix: *const XChar,
    uri: *const XChar,
    nb_namespaces: c_int,
    namespaces: *mut *const XChar,
    nb_attributes: c_int,
    nb_defaulted: c_int,
    attributes: *mut *const XChar,
) {
    let ctxt = unsafe { c(ctx) };
    if ctxt.is_null() {
        return;
    }
    unsafe {
        let doc = (*ctxt).myDoc;
        let dict = (*ctxt).dictNames != 0;
        let mut name: *const XChar = localname;
        let mut owned = false;
        if !prefix.is_null() && uri.is_null() {
            let q = [cbytes(prefix), b":", cbytes(localname)].concat();
            if dict {
                name = xmlDictLookup((*ctxt).dict as *mut Dict, q.as_ptr(), q.len() as c_int);
            } else {
                name = xstrdup(&q);
                owned = true;
            }
        } else if !dict {
            name = xstrdup(cbytes(localname));
            owned = true;
        }
        let _ = owned;
        let ret = new_node(doc, ELEMENT_NODE, name);
        if ret.is_null() {
            return err_memory(ctxt);
        }
        if let Some(f) = (*globals()).register_node {
            f(ret);
        }
        let mut last: *mut Ns = null_mut();
        for j in 0..nb_namespaces as usize {
            let pref = *namespaces.add(2 * j);
            let u = *namespaces.add(2 * j + 1);
            let ns = new_ns(null_mut(), copt(u), copt(pref));
            if ns.is_null() {
                err_memory(ctxt);
                continue;
            }
            if last.is_null() {
                (*ret).nsDef = ns;
            } else {
                (*last).next = ns;
            }
            last = ns;
            if !uri.is_null() && prefix == pref {
                (*ret).ns = ns;
            }
            ns_update_sax(ctxt, pref, ns);
        }
        (*ctxt).nodemem = -1;
        append_child(ctxt, ret);
        if node_push(ctxt, ret) < 0 {
            xmlUnlinkNode(ret);
            xmlFreeNode(ret);
            return;
        }
        let mut nb = nb_attributes;
        if nb_defaulted != 0 && (*ctxt).loadsubset & COMPLETE_ATTRS == 0 {
            nb -= nb_defaulted;
        }
        if !uri.is_null() && (*ret).ns.is_null() {
            (*ret).ns = ns_lookup_sax(ctxt, prefix);
            if (*ret).ns.is_null() && copt(prefix) == Some(b"xml") {
                (*ret).ns = xmlSearchNs(doc, ret, prefix);
            }
            if (*ret).ns.is_null() {
                let ns = new_ns(ret, None, copt(prefix));
                if ns.is_null() {
                    return err_memory(ctxt);
                }
                match copt(prefix) {
                    Some(p) => {
                        let msg = [b"Namespace prefix ".as_slice(), p, b" was not found\n"].concat();
                        ctx_err(ctxt, null_mut(), FROM_NAMESPACE, NS_ERR_UNDEFINED_NAMESPACE, ERR_WARNING, Some(p), None, None, 0, &msg);
                    }
                    None => {
                        ctx_err(ctxt, null_mut(), FROM_NAMESPACE, NS_ERR_UNDEFINED_NAMESPACE, ERR_WARNING, None, None, None, 0, b"Namespace default prefix was not found\n");
                    }
                }
            }
        }
        let mut prev: *mut Attr = null_mut();
        for i in 0..nb.max(0) as usize {
            let at = attributes.add(5 * i);
            let (an, ap, au, av, ave) = (*at, *at.add(1), *at.add(2), *at.add(3), *at.add(4));
            let attr = if !ap.is_null() && au.is_null() {
                let q = [cbytes(ap), b":", cbytes(an)].concat();
                if dict {
                    let full = xmlDictLookup((*ctxt).dict as *mut Dict, q.as_ptr(), q.len() as c_int);
                    attribute_ns(ctxt, full, null(), av, ave)
                } else {
                    let z = nul(&q);
                    let a = attribute_ns(ctxt, z.as_ptr(), null(), av, ave);
                    // attribute_ns copied the name.
                    a
                }
            } else {
                attribute_ns(ctxt, an, ap, av, ave)
            };
            if attr.is_null() {
                continue;
            }
            if prev.is_null() {
                (*(*ctxt).node).properties = attr;
            } else {
                (*prev).next = attr;
                (*attr).prev = prev;
            }
            prev = attr;
        }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAX2EndElementNs(ctx: Ctx, _l: *const XChar, _p: *const XChar, _u: *const XChar) {
    let ctxt = unsafe { c(ctx) };
    if ctxt.is_null() {
        return;
    }
    unsafe {
        (*ctxt).nodemem = -1;
        node_pop(ctxt);
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAX2Reference(ctx: Ctx, name: *const XChar) {
    let ctxt = unsafe { c(ctx) };
    if ctxt.is_null() {
        return;
    }
    unsafe {
        let r = xmlNewReference((*ctxt).myDoc, name);
        if r.is_null() {
            return err_memory(ctxt);
        }
        append_child(ctxt, r);
    }
}

/// xmlSAX2Text: text appended to the current node, merged into its last
/// text node.
unsafe fn sax2_text(ctxt: *mut ParserCtxt, ch: *const XChar, len: c_int, ty: c_int) {
    unsafe {
        let parent = (*ctxt).node;
        if parent.is_null() || len < 0 {
            return;
        }
        let s = std::slice::from_raw_parts(ch, len as usize);
        let last = (*parent).last;
        if last.is_null() || (*last).type_ != ty || ty != TEXT_NODE || (*last).name != xmlStringText.as_ptr() {
            let node = if ty == TEXT_NODE { text_node(ctxt, (*parent).doc, s) } else { xmlNewCDataBlock((*parent).doc, ch, len) };
            if node.is_null() {
                return err_memory(ctxt);
            }
            if last.is_null() {
                (*parent).children = node;
                (*parent).last = node;
                (*node).parent = parent;
            } else {
                append_child(ctxt, node);
            }
            (*ctxt).nodelen = len;
            (*ctxt).nodemem = len + 1;
            if ty == TEXT_NODE && !(*ctxt).input.is_null() {
                let l = (*(*ctxt).input).line;
                (*node).line = if (l as u32) < 65535 { l as c_ushort } else { 65535 };
            }
            return;
        }
        let content = (*last).content;
        let old = cbytes(content).len();
        let mut cap = (*ctxt).nodemem;
        let new_len = old + len as usize;
        let owned_by_us = cap > 0 && (*ctxt).nodelen as usize == old && !dict_owns((*(*last).doc).dict_or_null(), content);
        if owned_by_us && (new_len as c_int) < cap {
            std::ptr::copy_nonoverlapping(ch, content.add(old), len as usize);
            *content.add(new_len) = 0;
        } else {
            cap = if new_len <= 20 { 40 } else { (new_len * 2).min(i32::MAX as usize) as c_int };
            let p = if owned_by_us {
                xrealloc(content as *mut c_void, cap as usize) as *mut XChar
            } else {
                let p = xmalloc(cap as usize) as *mut XChar;
                if !p.is_null() {
                    std::ptr::copy_nonoverlapping(content, p, old);
                    if !dict_owns((*(*last).doc).dict_or_null(), content) {
                        xfree(content as *mut c_void);
                    }
                }
                p
            };
            if p.is_null() {
                return err_memory(ctxt);
            }
            std::ptr::copy_nonoverlapping(ch, p.add(old), len as usize);
            *p.add(new_len) = 0;
            (*last).content = p;
            (*ctxt).nodemem = cap;
        }
        (*ctxt).nodelen = new_len as c_int;
        if !(*ctxt).input.is_null() {
            let l = (*(*ctxt).input).line;
            (*last).line = if (l as u32) < 65535 { l as c_ushort } else { 65535 };
        }
    }
}

trait DictOrNull {
    fn dict_or_null(&self) -> *mut c_void;
}

impl DictOrNull for Doc {
    fn dict_or_null(&self) -> *mut c_void {
        self.dict
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAX2Characters(ctx: Ctx, ch: *const XChar, len: c_int) {
    unsafe { sax2_text(c(ctx), ch, len, TEXT_NODE) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAX2IgnorableWhitespace(_ctx: Ctx, _ch: *const XChar, _len: c_int) {}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAX2ProcessingInstruction(ctx: Ctx, target: *const XChar, data: *const XChar) {
    let ctxt = unsafe { c(ctx) };
    if ctxt.is_null() {
        return;
    }
    unsafe {
        let n = xmlNewDocPI((*ctxt).myDoc, target, data);
        if n.is_null() {
            return err_memory(ctxt);
        }
        append_child(ctxt, n);
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAX2Comment(ctx: Ctx, value: *const XChar) {
    let ctxt = unsafe { c(ctx) };
    if ctxt.is_null() {
        return;
    }
    unsafe {
        let n = xmlNewDocComment((*ctxt).myDoc, value);
        if n.is_null() {
            return err_memory(ctxt);
        }
        append_child(ctxt, n);
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAX2CDataBlock(ctx: Ctx, value: *const XChar, len: c_int) {
    unsafe { sax2_text(c(ctx), value, len, CDATA_SECTION_NODE) };
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlSAXDefaultVersion(version: c_int) -> c_int {
    if version != 2 { -1 } else { 2 }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAXVersion(h: *mut SaxHandler, version: c_int) -> c_int {
    if h.is_null() {
        return -1;
    }
    let h = unsafe { &mut *h };
    match version {
        2 => {
            h.startElementNs = Some(xmlSAX2StartElementNs);
            h.endElementNs = Some(xmlSAX2EndElementNs);
            h.serror = None;
            h.initialized = SAX2_MAGIC;
        }
        1 => h.initialized = 1,
        _ => return -1,
    }
    h.startElement = Some(xmlSAX2StartElement);
    h.endElement = Some(xmlSAX2EndElement);
    h.internalSubset = Some(xmlSAX2InternalSubset);
    h.externalSubset = Some(xmlSAX2ExternalSubset);
    h.isStandalone = Some(xmlSAX2IsStandalone);
    h.hasInternalSubset = Some(xmlSAX2HasInternalSubset);
    h.hasExternalSubset = Some(xmlSAX2HasExternalSubset);
    h.resolveEntity = Some(xmlSAX2ResolveEntity);
    h.getEntity = Some(xmlSAX2GetEntity);
    h.getParameterEntity = Some(xmlSAX2GetParameterEntity);
    h.entityDecl = Some(xmlSAX2EntityDecl);
    h.attributeDecl = Some(xmlSAX2AttributeDecl);
    h.elementDecl = Some(xmlSAX2ElementDecl);
    h.notationDecl = Some(xmlSAX2NotationDecl);
    h.unparsedEntityDecl = Some(xmlSAX2UnparsedEntityDecl);
    h.setDocumentLocator = Some(xmlSAX2SetDocumentLocator);
    h.startDocument = Some(xmlSAX2StartDocument);
    h.endDocument = Some(xmlSAX2EndDocument);
    h.reference = Some(xmlSAX2Reference);
    h.characters = Some(xmlSAX2Characters);
    h.cdataBlock = Some(xmlSAX2CDataBlock);
    h.ignorableWhitespace = Some(xmlSAX2Characters);
    h.processingInstruction = Some(xmlSAX2ProcessingInstruction);
    h.comment = Some(xmlSAX2Comment);
    h.warning = Some(as_msg_fn(xmlParserWarning));
    h.error = Some(as_msg_fn(xmlParserError));
    h.fatalError = Some(as_msg_fn(xmlParserError));
    0
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAX2InitDefaultSAXHandler(h: *mut SaxHandler, warning: c_int) {
    if h.is_null() || unsafe { (*h).initialized } != 0 {
        return;
    }
    unsafe {
        xmlSAXVersion(h, 2);
        if warning == 0 {
            (*h).warning = None;
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlDefaultSAXHandlerInit() {}

#[unsafe(no_mangle)]
pub extern "C" fn xmlSAX2InitHtmlDefaultSAXHandler(_h: *mut SaxHandler) {}
