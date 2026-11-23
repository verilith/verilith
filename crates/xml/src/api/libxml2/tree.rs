//! The tree: libxml2's nodes, made, linked, read, copied and freed as
//! tree.c, entities.c and valid.c do, for the parts of their API this ABI
//! provides.
use super::*;

// --- making and freeing nodes ----------------------------------------------------

/// Calls the registration callback for a new node, as libxml2 does.
fn registered(n: *mut Node) -> *mut Node {
    if !n.is_null() {
        if let Some(f) = unsafe { (*globals()).register_node } {
            unsafe { f(n) };
        }
    }
    n
}

pub fn new_node(doc: *mut Doc, ty: c_int, name: *const XChar) -> *mut Node {
    let n: *mut Node = xnew();
    if n.is_null() {
        return n;
    }
    unsafe {
        (*n).type_ = ty;
        (*n).doc = doc;
        (*n).name = name;
    }
    n
}

/// A name for a node: from the document's dictionary if it has one.
pub fn node_name(doc: *mut Doc, name: &[u8]) -> *const XChar {
    if !doc.is_null() && !unsafe { (*doc).dict }.is_null() {
        unsafe { xmlDictLookup((*doc).dict as *mut Dict, name.as_ptr(), name.len() as c_int) }
    } else {
        xstrdup(name)
    }
}

pub static TEXT_NAME: [u8; 5] = *b"text\0";
pub static TEXT_NOENC_NAME: [u8; 10] = *b"textnoenc\0";
pub static COMMENT_NAME: [u8; 8] = *b"comment\0";

#[unsafe(no_mangle)]
pub static xmlStringText: [u8; 5] = TEXT_NAME;
#[unsafe(no_mangle)]
pub static xmlStringTextNoenc: [u8; 10] = TEXT_NOENC_NAME;
#[unsafe(no_mangle)]
pub static xmlStringComment: [u8; 8] = COMMENT_NAME;

/// Whether a node's name is one of the static names above (not freed).
fn static_name(p: *const XChar) -> bool {
    p == xmlStringText.as_ptr() || p == xmlStringTextNoenc.as_ptr() || p == xmlStringComment.as_ptr()
}

pub fn new_text(doc: *mut Doc, s: &[u8]) -> *mut Node {
    let n = new_node(doc, TEXT_NODE, xmlStringText.as_ptr());
    if !n.is_null() {
        unsafe { (*n).content = xstrdup(s) };
    }
    registered(n)
}

pub fn new_ns(node: *mut Node, href: Option<&[u8]>, prefix: Option<&[u8]>) -> *mut Ns {
    if prefix == Some(b"xml") && node.is_null() {
        // Not xmlNewNs's business to reject; tree code does below.
    }
    let ns: *mut Ns = xnew();
    if ns.is_null() {
        return ns;
    }
    unsafe {
        (*ns).type_ = NAMESPACE_DECL;
        (*ns).href = xstrdup_opt(href);
        (*ns).prefix = xstrdup_opt(prefix);
    }
    if !node.is_null() {
        unsafe {
            let mut prev = (*node).nsDef;
            if prev.is_null() {
                (*node).nsDef = ns;
            } else {
                loop {
                    if bytes_eq((*prev).prefix, (*ns).prefix) {
                        xmlFreeNs(ns);
                        return null_mut();
                    }
                    if (*prev).next.is_null() {
                        break;
                    }
                    prev = (*prev).next;
                }
                (*prev).next = ns;
            }
        }
    }
    ns
}

fn bytes_eq(a: *const XChar, b: *const XChar) -> bool {
    unsafe { copt(a) == copt(b) }
}

fn free_str(doc: *mut Doc, p: *const XChar) {
    if p.is_null() || static_name(p) {
        return;
    }
    let dict = if doc.is_null() { null_mut() } else { unsafe { (*doc).dict } };
    if !dict_owns(dict, p) {
        xfree(p as *mut c_void);
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlFreeNs(ns: *mut Ns) {
    if ns.is_null() {
        return;
    }
    unsafe {
        xfree((*ns).href as *mut c_void);
        xfree((*ns).prefix as *mut c_void);
    }
    xfree(ns as *mut c_void);
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlFreeNsList(mut ns: *mut Ns) {
    while !ns.is_null() {
        let next = unsafe { (*ns).next };
        unsafe { xmlFreeNs(ns) };
        ns = next;
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlFreeProp(a: *mut Attr) {
    if a.is_null() {
        return;
    }
    unsafe {
        if let Some(f) = (*globals()).deregister_node {
            f(a as *mut Node);
        }
        let doc = (*a).doc;
        if !doc.is_null() && (*a).atype == ATTRIBUTE_ID {
            remove_id(doc, a);
        }
        xmlFreeNodeList((*a).children);
        free_str(doc, (*a).name);
    }
    xfree(a as *mut c_void);
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlFreePropList(mut a: *mut Attr) {
    while !a.is_null() {
        let next = unsafe { (*a).next };
        unsafe { xmlFreeProp(a) };
        a = next;
    }
}

/// Frees one node and what it owns, its children included (iteratively).
unsafe fn free_one(n: *mut Node) {
    unsafe {
        let ty = (*n).type_;
        if let Some(f) = (*globals()).deregister_node {
            f(n);
        }
        let doc = (*n).doc;
        match ty {
            DOCUMENT_NODE | HTML_DOCUMENT_NODE => {
                xmlFreeDoc(n as *mut Doc);
                return;
            }
            DTD_NODE => {
                xmlFreeDtd(n as *mut Dtd);
                return;
            }
            ATTRIBUTE_NODE => {
                xmlFreeProp(n as *mut Attr);
                return;
            }
            NAMESPACE_DECL => {
                xmlFreeNs(n as *mut Ns);
                return;
            }
            ENTITY_DECL => {
                xmlFreeEntity(n as *mut Entity);
                return;
            }
            ELEMENT_DECL => {
                free_element_decl(n as *mut ElementDecl);
                return;
            }
            ATTRIBUTE_DECL => {
                free_attribute_decl(n as *mut AttributeDecl);
                return;
            }
            _ => {}
        }
        if ty == ELEMENT_NODE || ty == XINCLUDE_START || ty == XINCLUDE_END {
            xmlFreePropList((*n).properties);
            xmlFreeNsList((*n).nsDef);
        }
        if ty != ELEMENT_NODE && ty != ENTITY_REF_NODE && !(*n).content.is_null() {
            free_str(doc, (*n).content);
        }
        if ty != TEXT_NODE && ty != COMMENT_NODE {
            free_str(doc, (*n).name);
        }
    }
    xfree(n as *mut c_void);
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlFreeNodeList(cur: *mut Node) {
    if cur.is_null() {
        return;
    }
    // An explicit walk: children before their parent, no recursion.
    let mut stack: Vec<*mut Node> = Vec::new();
    let mut n = cur;
    while !n.is_null() {
        stack.push(n);
        n = unsafe { (*n).next };
    }
    while let Some(n) = stack.pop() {
        let ty = unsafe { (*n).type_ };
        let kids = unsafe { (*n).children };
        let owns_kids = !matches!(ty, ENTITY_REF_NODE | DOCUMENT_NODE | HTML_DOCUMENT_NODE | DTD_NODE | ATTRIBUTE_NODE)
            && !matches!(ty, ENTITY_DECL | ELEMENT_DECL | ATTRIBUTE_DECL);
        if owns_kids && !kids.is_null() {
            unsafe { (*n).children = null_mut() };
            stack.push(n);
            let mut k = kids;
            while !k.is_null() {
                stack.push(k);
                k = unsafe { (*k).next };
            }
            continue;
        }
        unsafe { free_one(n) };
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlFreeNode(n: *mut Node) {
    if n.is_null() {
        return;
    }
    let ty = unsafe { (*n).type_ };
    if matches!(ty, DTD_NODE | ATTRIBUTE_NODE | NAMESPACE_DECL | ENTITY_DECL | DOCUMENT_NODE | HTML_DOCUMENT_NODE) {
        unsafe { free_one(n) };
        return;
    }
    let kids = unsafe { (*n).children };
    if ty != ENTITY_REF_NODE && !kids.is_null() {
        unsafe {
            (*n).children = null_mut();
            xmlFreeNodeList(kids);
        }
    }
    unsafe { free_one(n) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewDoc(version: *const XChar) -> *mut Doc {
    let d: *mut Doc = xnew();
    if d.is_null() {
        return d;
    }
    unsafe {
        (*d).type_ = DOCUMENT_NODE;
        (*d).version = xstrdup(copt(version).unwrap_or(b"1.0"));
        (*d).standalone = -1;
        (*d).compression = -1;
        (*d).doc = d;
        (*d).parseFlags = 0;
        (*d).properties = DOC_USERBUILT;
        (*d).charset = 1;
    }
    registered(d as *mut Node);
    d
}

const DOC_USERBUILT: c_int = 1 << 5;

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlFreeDoc(d: *mut Doc) {
    if d.is_null() {
        return;
    }
    unsafe {
        if let Some(f) = (*globals()).deregister_node {
            f(d as *mut Node);
        }
        free_ids(d);
        let ext = (*d).extSubset;
        let int = (*d).intSubset;
        if !ext.is_null() && ext != int {
            xmlUnlinkNode(ext as *mut Node);
            (*d).extSubset = null_mut();
            xmlFreeDtd(ext);
        }
        if !int.is_null() {
            xmlUnlinkNode(int as *mut Node);
            (*d).intSubset = null_mut();
            xmlFreeDtd(int);
        }
        xmlFreeNodeList((*d).children);
        xmlFreeNsList((*d).oldNs);
        xfree((*d).version as *mut c_void);
        xfree((*d).name as *mut c_void);
        xfree((*d).encoding as *mut c_void);
        xfree((*d).URL as *mut c_void);
        let dict = (*d).dict;
        xfree(d as *mut c_void);
        if !dict.is_null() {
            xmlDictFree(dict as *mut Dict);
        }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewDtd(doc: *mut Doc, name: *const XChar, ext: *const XChar, sys: *const XChar) -> *mut Dtd {
    if !doc.is_null() && unsafe { !(*doc).extSubset.is_null() } {
        return null_mut();
    }
    let d = unsafe { make_dtd(doc, name, ext, sys) };
    if !doc.is_null() && !d.is_null() {
        unsafe { (*doc).extSubset = d };
    }
    d
}

unsafe fn make_dtd(doc: *mut Doc, name: *const XChar, ext: *const XChar, sys: *const XChar) -> *mut Dtd {
    let d: *mut Dtd = xnew();
    if d.is_null() {
        return d;
    }
    unsafe {
        (*d).type_ = DTD_NODE;
        (*d).name = xstrdup_opt(copt(name));
        (*d).ExternalID = xstrdup_opt(copt(ext));
        (*d).SystemID = xstrdup_opt(copt(sys));
        (*d).doc = doc;
    }
    registered(d as *mut Node);
    d
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCreateIntSubset(doc: *mut Doc, name: *const XChar, ext: *const XChar, sys: *const XChar) -> *mut Dtd {
    if !doc.is_null() && !unsafe { xmlGetIntSubset(doc) }.is_null() {
        return null_mut();
    }
    let d = unsafe { make_dtd(doc, name, ext, sys) };
    if d.is_null() || doc.is_null() {
        return d;
    }
    unsafe {
        (*doc).intSubset = d;
        (*d).parent = doc;
        // Before the document's first element (or at the end).
        let first = (*doc).children;
        if first.is_null() {
            (*doc).children = d as *mut Node;
            (*doc).last = d as *mut Node;
        } else if (*doc).type_ == HTML_DOCUMENT_NODE {
            (*d).next = first;
            (*first).prev = d as *mut Node;
            (*doc).children = d as *mut Node;
        } else {
            let mut prev = first;
            while !prev.is_null() && (*prev).type_ != ELEMENT_NODE {
                prev = (*prev).next;
            }
            if prev.is_null() {
                (*d).prev = (*doc).last;
                (*(*doc).last).next = d as *mut Node;
                (*doc).last = d as *mut Node;
            } else {
                (*d).next = prev;
                (*d).prev = (*prev).prev;
                if (*prev).prev.is_null() {
                    (*doc).children = d as *mut Node;
                } else {
                    (*(*prev).prev).next = d as *mut Node;
                }
                (*prev).prev = d as *mut Node;
            }
        }
    }
    d
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlGetIntSubset(doc: *const Doc) -> *mut Dtd {
    if doc.is_null() {
        return null_mut();
    }
    unsafe {
        let mut c = (*doc).children;
        while !c.is_null() {
            if (*c).type_ == DTD_NODE {
                return c as *mut Dtd;
            }
            c = (*c).next;
        }
        (*doc).intSubset
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlFreeDtd(d: *mut Dtd) {
    if d.is_null() {
        return;
    }
    unsafe {
        if let Some(f) = (*globals()).deregister_node {
            f(d as *mut Node);
        }
        // Comments and PIs are the DTD's children alone; declarations are
        // also in the tables, which free them.
        let mut c = (*d).children;
        while !c.is_null() {
            let next = (*c).next;
            let ty = (*c).type_;
            // Unlinked first, so that freeing one touches no other.
            (*c).next = null_mut();
            (*c).prev = null_mut();
            (*c).parent = null_mut();
            if !matches!(ty, ENTITY_DECL | ELEMENT_DECL | ATTRIBUTE_DECL | 12) {
                xmlFreeNode(c);
            }
            c = next;
        }
        (*d).children = null_mut();
        (*d).last = null_mut();
        free_table((*d).notations as *mut Hash, |p| free_notation(p as *mut Notation));
        free_table((*d).elements as *mut Hash, |p| free_element_decl(p as *mut ElementDecl));
        free_table((*d).attributes as *mut Hash, |p| free_attribute_decl(p as *mut AttributeDecl));
        free_table((*d).entities as *mut Hash, |p| xmlFreeEntity(p as *mut Entity));
        free_table((*d).pentities as *mut Hash, |p| xmlFreeEntity(p as *mut Entity));
        xfree((*d).name as *mut c_void);
        xfree((*d).ExternalID as *mut c_void);
        xfree((*d).SystemID as *mut c_void);
    }
    xfree(d as *mut c_void);
}

unsafe fn free_table(h: *mut Hash, f: impl Fn(*mut c_void)) {
    if h.is_null() {
        return;
    }
    let h = unsafe { Box::from_raw(h) };
    for v in h.values() {
        f(v);
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewNode(ns: *mut Ns, name: *const XChar) -> *mut Node {
    if name.is_null() {
        return null_mut();
    }
    let n = new_node(null_mut(), ELEMENT_NODE, xstrdup(unsafe { cbytes(name) }));
    if !n.is_null() {
        unsafe { (*n).ns = ns };
    }
    registered(n)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewNodeEatName(ns: *mut Ns, name: *mut XChar) -> *mut Node {
    if name.is_null() {
        return null_mut();
    }
    let n = new_node(null_mut(), ELEMENT_NODE, name);
    if !n.is_null() {
        unsafe { (*n).ns = ns };
    }
    registered(n)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewDocNode(doc: *mut Doc, ns: *mut Ns, name: *const XChar, content: *const XChar) -> *mut Node {
    if name.is_null() {
        return null_mut();
    }
    let n = new_node(doc, ELEMENT_NODE, node_name(doc, unsafe { cbytes(name) }));
    if n.is_null() {
        return n;
    }
    unsafe {
        (*n).ns = ns;
        if !content.is_null() {
            let kids = string_get_node_list(doc, cbytes(content), false);
            set_children(n, kids);
        }
    }
    registered(n)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewDocNodeEatName(doc: *mut Doc, ns: *mut Ns, name: *mut XChar, content: *const XChar) -> *mut Node {
    if name.is_null() {
        return null_mut();
    }
    let n = new_node(doc, ELEMENT_NODE, name);
    if n.is_null() {
        return n;
    }
    unsafe {
        (*n).ns = ns;
        if !content.is_null() {
            let kids = string_get_node_list(doc, cbytes(content), false);
            set_children(n, kids);
        }
    }
    registered(n)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewDocRawNode(doc: *mut Doc, ns: *mut Ns, name: *const XChar, content: *const XChar) -> *mut Node {
    let n = unsafe { xmlNewDocNode(doc, ns, name, null()) };
    if !n.is_null() && !content.is_null() {
        let t = new_text(doc, unsafe { cbytes(content) });
        unsafe { set_children(n, t) };
    }
    n
}

unsafe fn set_children(n: *mut Node, kids: *mut Node) {
    unsafe {
        (*n).children = kids;
        let mut k = kids;
        let mut last = null_mut();
        while !k.is_null() {
            (*k).parent = n;
            last = k;
            k = (*k).next;
        }
        (*n).last = last;
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewDocFragment(doc: *mut Doc) -> *mut Node {
    registered(new_node(doc, DOCUMENT_FRAG_NODE, null()))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewText(content: *const XChar) -> *mut Node {
    let n = new_node(null_mut(), TEXT_NODE, xmlStringText.as_ptr());
    if !n.is_null() && !content.is_null() {
        unsafe { (*n).content = xstrdup(cbytes(content)) };
    }
    registered(n)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewDocText(doc: *const Doc, content: *const XChar) -> *mut Node {
    let n = unsafe { xmlNewText(content) };
    if !n.is_null() {
        unsafe { (*n).doc = doc as *mut Doc };
    }
    n
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewTextLen(content: *const XChar, len: c_int) -> *mut Node {
    let n = new_node(null_mut(), TEXT_NODE, xmlStringText.as_ptr());
    if !n.is_null() && !content.is_null() {
        unsafe { (*n).content = xmlStrndup(content, len) };
    }
    registered(n)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewDocTextLen(doc: *mut Doc, content: *const XChar, len: c_int) -> *mut Node {
    let n = unsafe { xmlNewTextLen(content, len) };
    if !n.is_null() {
        unsafe { (*n).doc = doc };
    }
    n
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewCDataBlock(doc: *mut Doc, content: *const XChar, len: c_int) -> *mut Node {
    let n = new_node(doc, CDATA_SECTION_NODE, null());
    if !n.is_null() && !content.is_null() {
        unsafe { (*n).content = xmlStrndup(content, len) };
    }
    registered(n)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewComment(content: *const XChar) -> *mut Node {
    let n = new_node(null_mut(), COMMENT_NODE, xmlStringComment.as_ptr());
    if !n.is_null() && !content.is_null() {
        unsafe { (*n).content = xstrdup(cbytes(content)) };
    }
    registered(n)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewDocComment(doc: *mut Doc, content: *const XChar) -> *mut Node {
    let n = unsafe { xmlNewComment(content) };
    if !n.is_null() {
        unsafe { (*n).doc = doc };
    }
    n
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewDocPI(doc: *mut Doc, name: *const XChar, content: *const XChar) -> *mut Node {
    if name.is_null() {
        return null_mut();
    }
    let n = new_node(doc, PI_NODE, node_name(doc, unsafe { cbytes(name) }));
    if !n.is_null() && !content.is_null() {
        unsafe { (*n).content = xstrdup(cbytes(content)) };
    }
    registered(n)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewPI(name: *const XChar, content: *const XChar) -> *mut Node {
    unsafe { xmlNewDocPI(null_mut(), name, content) }
}

/// An entity reference node: named for the entity, its children the
/// entity's (shared, not owned).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewReference(doc: *const Doc, name: *const XChar) -> *mut Node {
    if name.is_null() {
        return null_mut();
    }
    let mut nm = unsafe { cbytes(name) };
    if nm.first() == Some(&b'&') {
        nm = &nm[1..];
    }
    if nm.last() == Some(&b';') {
        nm = &nm[..nm.len() - 1];
    }
    let doc = doc as *mut Doc;
    let n = new_node(doc, ENTITY_REF_NODE, node_name(doc, nm));
    if n.is_null() {
        return n;
    }
    let z = nul(nm);
    let ent = unsafe { xmlGetDocEntity(doc, z.as_ptr()) };
    if !ent.is_null() {
        unsafe {
            (*n).content = (*ent).content;
            (*n).children = ent as *mut Node;
            (*n).last = ent as *mut Node;
        }
    }
    registered(n)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewCharRef(doc: *mut Doc, name: *const XChar) -> *mut Node {
    if name.is_null() {
        return null_mut();
    }
    let mut nm = unsafe { cbytes(name) };
    if nm.first() == Some(&b'&') {
        nm = &nm[1..];
    }
    if nm.last() == Some(&b';') {
        nm = &nm[..nm.len() - 1];
    }
    registered(new_node(doc, ENTITY_REF_NODE, node_name(doc, nm)))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewNs(node: *mut Node, href: *const XChar, prefix: *const XChar) -> *mut Ns {
    if !node.is_null() && unsafe { (*node).type_ } != ELEMENT_NODE {
        return null_mut();
    }
    if unsafe { copt(prefix) } == Some(b"xml") {
        return null_mut();
    }
    new_ns(node, unsafe { copt(href) }, unsafe { copt(prefix) })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSetNs(node: *mut Node, ns: *mut Ns) {
    if node.is_null() {
        return;
    }
    unsafe {
        if matches!((*node).type_, ELEMENT_NODE | ATTRIBUTE_NODE) {
            (*node).ns = ns;
        }
    }
}

/// An attribute on `node`, after its others.
pub unsafe fn new_prop(node: *mut Node, ns: *mut Ns, name: &[u8], value: Option<&[u8]>, eat: Option<*mut XChar>) -> *mut Attr {
    let a: *mut Attr = xnew();
    if a.is_null() {
        return a;
    }
    let doc = if node.is_null() { null_mut() } else { unsafe { (*node).doc } };
    unsafe {
        (*a).type_ = ATTRIBUTE_NODE;
        (*a).name = match eat {
            Some(p) => p,
            None => node_name(doc, name),
        };
        (*a).ns = ns;
        (*a).parent = node;
        (*a).doc = doc;
        if let Some(v) = value {
            let t = new_text(doc, v);
            (*a).children = t;
            (*a).last = t;
            if !t.is_null() {
                (*t).parent = a as *mut Node;
            }
        }
        if !node.is_null() {
            let mut p = (*node).properties;
            if p.is_null() {
                (*node).properties = a;
            } else {
                while !(*p).next.is_null() {
                    p = (*p).next;
                }
                (*p).next = a;
                (*a).prev = p;
            }
        }
    }
    registered(a as *mut Node);
    a
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewProp(node: *mut Node, name: *const XChar, value: *const XChar) -> *mut Attr {
    if name.is_null() || (!node.is_null() && unsafe { (*node).type_ } != ELEMENT_NODE) {
        return null_mut();
    }
    unsafe { new_prop(node, null_mut(), cbytes(name), copt(value), None) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewNsProp(node: *mut Node, ns: *mut Ns, name: *const XChar, value: *const XChar) -> *mut Attr {
    if name.is_null() || (!node.is_null() && unsafe { (*node).type_ } != ELEMENT_NODE) {
        return null_mut();
    }
    unsafe { new_prop(node, ns, cbytes(name), copt(value), None) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewNsPropEatName(node: *mut Node, ns: *mut Ns, name: *mut XChar, value: *const XChar) -> *mut Attr {
    if name.is_null() {
        return null_mut();
    }
    unsafe { new_prop(node, ns, cbytes(name), copt(value), Some(name)) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewDocProp(doc: *mut Doc, name: *const XChar, value: *const XChar) -> *mut Attr {
    if name.is_null() {
        return null_mut();
    }
    let a = unsafe { new_prop(null_mut(), null_mut(), cbytes(name), None, None) };
    if a.is_null() {
        return a;
    }
    unsafe {
        (*a).doc = doc;
        if !value.is_null() {
            let kids = string_get_node_list(doc, cbytes(value), false);
            set_children(a as *mut Node, kids);
        }
    }
    a
}

// --- linking -------------------------------------------------------------------------

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlUnlinkNode(n: *mut Node) {
    if n.is_null() {
        return;
    }
    unsafe {
        let ty = (*n).type_;
        if ty == NAMESPACE_DECL {
            return;
        }
        let parent = (*n).parent;
        if ty == DTD_NODE {
            let doc = (*n).doc;
            if !doc.is_null() {
                if (*doc).intSubset == n as *mut Dtd {
                    (*doc).intSubset = null_mut();
                }
                if (*doc).extSubset == n as *mut Dtd {
                    (*doc).extSubset = null_mut();
                }
            }
        }
        if ty == ENTITY_DECL && !parent.is_null() {
            let dtd = parent as *mut Dtd;
            let e = n as *mut Entity;
            let table = if matches!((*e).etype, INTERNAL_PARAMETER_ENTITY | EXTERNAL_PARAMETER_ENTITY) {
                (*dtd).pentities
            } else {
                (*dtd).entities
            } as *mut Hash;
            if !table.is_null() {
                let k = (cbytes((*e).name).to_vec(), Vec::new(), Vec::new());
                if (*table).get(&k) == n as *mut c_void {
                    (*table).remove(&k);
                }
            }
        }
        if !parent.is_null() {
            if ty == ATTRIBUTE_NODE {
                let a = n as *mut Attr;
                if (*parent).properties == a {
                    (*parent).properties = (*a).next;
                }
            } else {
                if (*parent).children == n {
                    (*parent).children = (*n).next;
                }
                if (*parent).last == n {
                    (*parent).last = (*n).prev;
                }
            }
        }
        if ty == ATTRIBUTE_NODE {
            let a = n as *mut Attr;
            if !(*a).next.is_null() {
                (*(*a).next).prev = (*a).prev;
            }
            if !(*a).prev.is_null() {
                (*(*a).prev).next = (*a).next;
            }
            (*a).next = null_mut();
            (*a).prev = null_mut();
        } else {
            if !(*n).next.is_null() {
                (*(*n).next).prev = (*n).prev;
            }
            if !(*n).prev.is_null() {
                (*(*n).prev).next = (*n).next;
            }
            (*n).next = null_mut();
            (*n).prev = null_mut();
        }
        (*n).parent = null_mut();
    }
}

/// Sets the document of a subtree.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSetTreeDoc(tree: *mut Node, doc: *mut Doc) -> c_int {
    if tree.is_null() {
        return 0;
    }
    let mut stack = vec![tree];
    while let Some(n) = stack.pop() {
        unsafe {
            if (*n).type_ == NAMESPACE_DECL {
                continue;
            }
            (*n).doc = doc;
            if (*n).type_ == ELEMENT_NODE {
                let mut a = (*n).properties;
                while !a.is_null() {
                    (*a).doc = doc;
                    let mut k = (*a).children;
                    while !k.is_null() {
                        (*k).doc = doc;
                        k = (*k).next;
                    }
                    a = (*a).next;
                }
            }
            if (*n).type_ != ENTITY_REF_NODE {
                let mut k = (*n).children;
                while !k.is_null() {
                    stack.push(k);
                    k = (*k).next;
                }
            }
        }
    }
    0
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSetListDoc(list: *mut Node, doc: *mut Doc) -> c_int {
    let mut n = list;
    while !n.is_null() {
        unsafe {
            xmlSetTreeDoc(n, doc);
            n = (*n).next;
        }
    }
    0
}

/// Merges text into a text node; true if `cur` was merged (and freed).
unsafe fn merge_text(target: *mut Node, cur: *mut Node) -> bool {
    unsafe {
        if target.is_null() || (*target).type_ != TEXT_NODE || (*cur).type_ != TEXT_NODE || (*target).name != (*cur).name {
            return false;
        }
        let add = cbytes((*cur).content).to_vec();
        let mut v = cbytes((*target).content).to_vec();
        v.extend_from_slice(&add);
        free_str((*target).doc, (*target).content);
        (*target).content = xstrdup(&v);
        xmlFreeNode(cur);
        true
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlAddChild(parent: *mut Node, cur: *mut Node) -> *mut Node {
    if parent.is_null() || cur.is_null() || parent == cur {
        return null_mut();
    }
    unsafe {
        if (*cur).type_ == ATTRIBUTE_NODE {
            if (*parent).type_ != ELEMENT_NODE {
                return null_mut();
            }
            xmlUnlinkNode(cur);
            let a = cur as *mut Attr;
            // An attribute of the same name is replaced.
            let old = find_prop(parent, cbytes((*a).name), if (*a).ns.is_null() { None } else { copt((*(*a).ns).href) }, true);
            if !old.is_null() && old != a {
                xmlUnlinkNode(old as *mut Node);
                xmlFreeProp(old);
            }
            (*a).parent = parent;
            if (*a).doc != (*parent).doc {
                xmlSetTreeDoc(cur, (*parent).doc);
            }
            let mut p = (*parent).properties;
            if p.is_null() {
                (*parent).properties = a;
            } else {
                while !(*p).next.is_null() {
                    p = (*p).next;
                }
                (*p).next = a;
                (*a).prev = p;
            }
            return cur;
        }
        if (*cur).type_ == DOCUMENT_FRAG_NODE {
            let kids = (*cur).children;
            (*cur).children = null_mut();
            (*cur).last = null_mut();
            xmlFreeNode(cur);
            return xmlAddChildList(parent, kids);
        }
        xmlUnlinkNode(cur);
        if (*cur).type_ == TEXT_NODE {
            if (*parent).type_ == TEXT_NODE && !(*parent).content.is_null() && (*parent).name == (*cur).name {
                let v = [cbytes((*parent).content), cbytes((*cur).content)].concat();
                free_str((*parent).doc, (*parent).content);
                (*parent).content = xstrdup(&v);
                xmlFreeNode(cur);
                return parent;
            }
            if merge_text((*parent).last, cur) {
                return (*parent).last;
            }
        }
        if (*cur).doc != (*parent).doc {
            xmlSetTreeDoc(cur, (*parent).doc);
        }
        (*cur).parent = parent;
        let last = (*parent).last;
        if last.is_null() {
            (*parent).children = cur;
        } else {
            (*last).next = cur;
            (*cur).prev = last;
        }
        (*parent).last = cur;
    }
    cur
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlAddChildList(parent: *mut Node, list: *mut Node) -> *mut Node {
    if parent.is_null() || list.is_null() {
        return null_mut();
    }
    let mut n = list;
    let mut last = null_mut();
    while !n.is_null() {
        let next = unsafe { (*n).next };
        unsafe {
            (*n).next = null_mut();
            (*n).prev = null_mut();
            (*n).parent = null_mut();
        }
        let r = unsafe { xmlAddChild(parent, n) };
        if !r.is_null() {
            last = r;
        }
        n = next;
    }
    last
}

unsafe fn insert_sibling(at: *mut Node, cur: *mut Node, after: bool) -> *mut Node {
    if at.is_null() || cur.is_null() || at == cur {
        return null_mut();
    }
    unsafe {
        xmlUnlinkNode(cur);
        if (*cur).type_ == TEXT_NODE {
            let neighbour = if after { at } else { at };
            if (*neighbour).type_ == TEXT_NODE && (*neighbour).name == (*cur).name {
                let v = if after {
                    [cbytes((*at).content), cbytes((*cur).content)].concat()
                } else {
                    [cbytes((*cur).content), cbytes((*at).content)].concat()
                };
                free_str((*at).doc, (*at).content);
                (*at).content = xstrdup(&v);
                xmlFreeNode(cur);
                return at;
            }
        }
        if (*cur).doc != (*at).doc {
            xmlSetTreeDoc(cur, (*at).doc);
        }
        let parent = (*at).parent;
        (*cur).parent = parent;
        if after {
            (*cur).prev = at;
            (*cur).next = (*at).next;
            if !(*at).next.is_null() {
                (*(*at).next).prev = cur;
            }
            (*at).next = cur;
            if !parent.is_null() && (*parent).last == at {
                (*parent).last = cur;
            }
        } else {
            (*cur).next = at;
            (*cur).prev = (*at).prev;
            if !(*at).prev.is_null() {
                (*(*at).prev).next = cur;
            }
            (*at).prev = cur;
            if !parent.is_null() && (*parent).children == at {
                (*parent).children = cur;
            }
        }
    }
    cur
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlAddNextSibling(at: *mut Node, cur: *mut Node) -> *mut Node {
    unsafe { insert_sibling(at, cur, true) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlAddPrevSibling(at: *mut Node, cur: *mut Node) -> *mut Node {
    unsafe { insert_sibling(at, cur, false) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlAddSibling(node: *mut Node, cur: *mut Node) -> *mut Node {
    if node.is_null() {
        return null_mut();
    }
    let mut last = node;
    unsafe {
        while !(*last).next.is_null() {
            last = (*last).next;
        }
        insert_sibling(last, cur, true)
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlReplaceNode(old: *mut Node, cur: *mut Node) -> *mut Node {
    if old.is_null() || old == cur {
        return null_mut();
    }
    if cur.is_null() {
        unsafe { xmlUnlinkNode(old) };
        return old;
    }
    unsafe {
        xmlUnlinkNode(cur);
        let parent = (*old).parent;
        (*cur).parent = parent;
        (*cur).next = (*old).next;
        (*cur).prev = (*old).prev;
        if !(*cur).next.is_null() {
            (*(*cur).next).prev = cur;
        }
        if !(*cur).prev.is_null() {
            (*(*cur).prev).next = cur;
        }
        if !parent.is_null() {
            if (*parent).children == old {
                (*parent).children = cur;
            }
            if (*parent).last == old {
                (*parent).last = cur;
            }
        }
        (*old).next = null_mut();
        (*old).prev = null_mut();
        (*old).parent = null_mut();
    }
    old
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlDocGetRootElement(doc: *const Doc) -> *mut Node {
    if doc.is_null() {
        return null_mut();
    }
    unsafe {
        let mut c = (*doc).children;
        while !c.is_null() {
            if (*c).type_ == ELEMENT_NODE {
                return c;
            }
            c = (*c).next;
        }
    }
    null_mut()
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlDocSetRootElement(doc: *mut Doc, root: *mut Node) -> *mut Node {
    if doc.is_null() || root.is_null() || unsafe { (*root).type_ } != ELEMENT_NODE {
        return null_mut();
    }
    unsafe {
        xmlUnlinkNode(root);
        xmlSetTreeDoc(root, doc);
        (*root).parent = doc as *mut Node;
        let old = xmlDocGetRootElement(doc);
        if old.is_null() {
            xmlAddChild(doc as *mut Node, root);
        } else {
            xmlReplaceNode(old, root);
        }
        old
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewChild(parent: *mut Node, ns: *mut Ns, name: *const XChar, content: *const XChar) -> *mut Node {
    if parent.is_null() || name.is_null() {
        return null_mut();
    }
    unsafe {
        let doc = if (*parent).type_ == DOCUMENT_NODE { parent as *mut Doc } else { (*parent).doc };
        let ns = if ns.is_null() && (*parent).type_ == ELEMENT_NODE { (*parent).ns } else { ns };
        let n = xmlNewDocNode(doc, ns, name, content);
        if n.is_null() {
            return n;
        }
        xmlAddChild(parent, n)
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewTextChild(parent: *mut Node, ns: *mut Ns, name: *const XChar, content: *const XChar) -> *mut Node {
    if parent.is_null() || name.is_null() {
        return null_mut();
    }
    unsafe {
        let doc = if (*parent).type_ == DOCUMENT_NODE { parent as *mut Doc } else { (*parent).doc };
        let ns = if ns.is_null() && (*parent).type_ == ELEMENT_NODE { (*parent).ns } else { ns };
        let n = xmlNewDocRawNode(doc, ns, name, content);
        if n.is_null() {
            return n;
        }
        xmlAddChild(parent, n)
    }
}

// --- navigation ----------------------------------------------------------------------

unsafe fn element_step(mut n: *mut Node, next: bool) -> *mut Node {
    while !n.is_null() {
        if unsafe { (*n).type_ } == ELEMENT_NODE {
            return n;
        }
        n = if next { unsafe { (*n).next } } else { unsafe { (*n).prev } };
    }
    null_mut()
}

fn has_children(n: *mut Node) -> bool {
    !n.is_null() && matches!(unsafe { (*n).type_ }, ELEMENT_NODE | DOCUMENT_NODE | HTML_DOCUMENT_NODE | DOCUMENT_FRAG_NODE | 6 | DTD_NODE)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlFirstElementChild(n: *mut Node) -> *mut Node {
    if !has_children(n) {
        return null_mut();
    }
    unsafe { element_step((*n).children, true) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlLastElementChild(n: *mut Node) -> *mut Node {
    if !has_children(n) {
        return null_mut();
    }
    unsafe { element_step((*n).last, false) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNextElementSibling(n: *mut Node) -> *mut Node {
    if n.is_null() {
        return null_mut();
    }
    unsafe { element_step((*n).next, true) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlPreviousElementSibling(n: *mut Node) -> *mut Node {
    if n.is_null() {
        return null_mut();
    }
    unsafe { element_step((*n).prev, false) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlChildElementCount(n: *mut Node) -> c_ulong {
    if !has_children(n) {
        return 0;
    }
    let mut c = unsafe { (*n).children };
    let mut k = 0;
    while !c.is_null() {
        if unsafe { (*c).type_ } == ELEMENT_NODE {
            k += 1;
        }
        c = unsafe { (*c).next };
    }
    k
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlGetLastChild(n: *const Node) -> *mut Node {
    if n.is_null() { null_mut() } else { unsafe { (*n).last } }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNodeIsText(n: *const Node) -> c_int {
    (!n.is_null() && unsafe { (*n).type_ } == TEXT_NODE) as c_int
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlIsBlankNode(n: *const Node) -> c_int {
    if n.is_null() || !matches!(unsafe { (*n).type_ }, TEXT_NODE | CDATA_SECTION_NODE) {
        return 0;
    }
    unsafe { cbytes((*n).content) }.iter().all(|&c| matches!(c, b' ' | b'\t' | b'\n' | b'\r')) as c_int
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlGetLineNo(n: *const Node) -> c_long {
    if n.is_null() { -1 } else { unsafe { (*n).line as c_long } }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNodeSetName(n: *mut Node, name: *const XChar) {
    if n.is_null() || name.is_null() {
        return;
    }
    unsafe {
        let doc = (*n).doc;
        let old = (*n).name;
        (*n).name = node_name(doc, cbytes(name));
        free_str(doc, old);
    }
}

// --- namespaces ----------------------------------------------------------------------

/// The xml namespace, kept on the document (`oldNs`), as libxml2 does.
pub unsafe fn xml_ns(doc: *mut Doc) -> *mut Ns {
    if doc.is_null() {
        return null_mut();
    }
    unsafe {
        if (*doc).oldNs.is_null() {
            let ns: *mut Ns = xnew();
            if ns.is_null() {
                return ns;
            }
            (*ns).type_ = NAMESPACE_DECL;
            (*ns).href = xstrdup(XML_XML_NAMESPACE);
            (*ns).prefix = xstrdup(b"xml");
            (*doc).oldNs = ns;
        }
        (*doc).oldNs
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSearchNs(doc: *mut Doc, node: *mut Node, prefix: *const XChar) -> *mut Ns {
    if node.is_null() {
        return null_mut();
    }
    let p = unsafe { copt(prefix) };
    unsafe {
        let doc = if doc.is_null() { (*node).doc } else { doc };
        if p == Some(b"xml") {
            return xml_ns(doc);
        }
        let mut n = node;
        while !n.is_null() {
            let ty = (*n).type_;
            if matches!(ty, ENTITY_REF_NODE | 6 | ENTITY_DECL) {
                return null_mut();
            }
            if ty == ELEMENT_NODE {
                let mut ns = (*n).nsDef;
                while !ns.is_null() {
                    if copt((*ns).prefix) == p && !(*ns).href.is_null() {
                        return ns;
                    }
                    ns = (*ns).next;
                }
                if n != node {
                    let ns = (*n).ns;
                    if !ns.is_null() && copt((*ns).prefix) == p && !(*ns).href.is_null() {
                        return ns;
                    }
                }
            }
            n = (*n).parent;
        }
    }
    null_mut()
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSearchNsByHref(doc: *mut Doc, node: *mut Node, href: *const XChar) -> *mut Ns {
    if node.is_null() || href.is_null() {
        return null_mut();
    }
    let h = unsafe { cbytes(href) };
    unsafe {
        let doc = if doc.is_null() { (*node).doc } else { doc };
        if h == XML_XML_NAMESPACE {
            return xml_ns(doc);
        }
        let mut n = node;
        while !n.is_null() {
            if (*n).type_ == ELEMENT_NODE {
                let mut ns = (*n).nsDef;
                while !ns.is_null() {
                    if copt((*ns).href) == Some(h) && xmlSearchNs(doc, node, (*ns).prefix) == ns {
                        return ns;
                    }
                    ns = (*ns).next;
                }
            }
            n = (*n).parent;
        }
    }
    null_mut()
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSearchNsSafe(node: *mut Node, prefix: *const XChar, out: *mut *mut Ns) -> c_int {
    if out.is_null() {
        return -1;
    }
    unsafe { *out = xmlSearchNs(null_mut(), node, prefix) };
    0
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlGetNsList(_doc: *const Doc, node: *const Node) -> *mut *mut Ns {
    let mut v: Vec<*mut Ns> = Vec::new();
    let mut n = node as *mut Node;
    unsafe {
        while !n.is_null() {
            if (*n).type_ == ELEMENT_NODE {
                let mut ns = (*n).nsDef;
                while !ns.is_null() {
                    if !v.iter().any(|&x| copt((*x).prefix) == copt((*ns).prefix)) {
                        v.push(ns);
                    }
                    ns = (*ns).next;
                }
            }
            n = (*n).parent;
        }
    }
    if v.is_empty() {
        return null_mut();
    }
    let out = xmalloc((v.len() + 1) * std::mem::size_of::<*mut Ns>()) as *mut *mut Ns;
    if !out.is_null() {
        for (i, ns) in v.iter().enumerate() {
            unsafe { *out.add(i) = *ns };
        }
        unsafe { *out.add(v.len()) = null_mut() };
    }
    out
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlBuildQName(ncname: *const XChar, prefix: *const XChar, memory: *mut XChar, len: c_int) -> *mut XChar {
    if ncname.is_null() {
        return null_mut();
    }
    let n = unsafe { cbytes(ncname) };
    let Some(p) = (unsafe { copt(prefix) }) else { return ncname as *mut XChar };
    let mut q = p.to_vec();
    q.push(b':');
    q.extend_from_slice(n);
    if !memory.is_null() && (q.len() as c_int) < len {
        unsafe {
            std::ptr::copy_nonoverlapping(q.as_ptr(), memory, q.len());
            *memory.add(q.len()) = 0;
        }
        return memory;
    }
    xstrdup(&q)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSplitQName2(name: *const XChar, prefix: *mut *mut XChar) -> *mut XChar {
    if prefix.is_null() {
        return null_mut();
    }
    unsafe { *prefix = null_mut() };
    let b = unsafe { cbytes(name) };
    if b.first() == Some(&b':') {
        return null_mut();
    }
    let Some(c) = b.iter().position(|&x| x == b':') else { return null_mut() };
    unsafe { *prefix = xstrdup(&b[..c]) };
    xstrdup(&b[c + 1..])
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSplitQName3(name: *const XChar, len: *mut c_int) -> *const XChar {
    let b = unsafe { cbytes(name) };
    if b.first() == Some(&b':') || len.is_null() {
        return null();
    }
    let Some(c) = b.iter().position(|&x| x == b':') else { return null() };
    unsafe {
        *len = c as c_int;
        name.add(c + 1)
    }
}

/// `prefix:local` split at the first colon, if it is a QName with a prefix.
pub fn split_qname(q: &[u8]) -> (Option<&[u8]>, &[u8]) {
    match q.iter().position(|&c| c == b':') {
        Some(c) if c > 0 && c + 1 < q.len() && !q[c + 1..].contains(&b':') => (Some(&q[..c]), &q[c + 1..]),
        _ => (None, q),
    }
}

fn is_name_start(c: char) -> bool {
    c == ':' || c == '_' || c.is_ascii_alphabetic() || (c as u32 >= 0xC0 && !matches!(c as u32, 0xD7 | 0xF7 | 0x37E | 0x2000..=0x200B | 0x200E..=0x206F | 0x2190..=0x2BFF | 0x2FF0..=0x3000 | 0xD800..=0xF8FF | 0xFDD0..=0xFDEF | 0xFFFE..=0xFFFF))
}

fn is_name_char(c: char) -> bool {
    is_name_start(c) || c == '-' || c == '.' || c.is_ascii_digit() || c as u32 == 0xB7 || matches!(c as u32, 0x300..=0x36F | 0x203F..=0x2040)
}

fn valid_name(s: &[u8], colons: bool, nmtoken: bool) -> bool {
    let Ok(t) = std::str::from_utf8(s) else { return false };
    let mut it = t.chars();
    let Some(first) = it.next() else { return false };
    if !nmtoken && (!is_name_start(first) || (!colons && first == ':')) {
        return false;
    }
    if nmtoken && !is_name_char(first) {
        return false;
    }
    t.chars().all(|c| is_name_char(c) && (colons || c != ':'))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlValidateNCName(v: *const XChar, _space: c_int) -> c_int {
    if v.is_null() {
        return -1;
    }
    if valid_name(unsafe { cbytes(v) }, false, false) { 0 } else { 1 }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlValidateQName(v: *const XChar, _space: c_int) -> c_int {
    if v.is_null() {
        return -1;
    }
    let b = unsafe { cbytes(v) };
    let ok = match b.iter().position(|&c| c == b':') {
        None => valid_name(b, false, false),
        Some(c) => valid_name(&b[..c], false, false) && valid_name(&b[c + 1..], false, false),
    };
    if ok { 0 } else { 1 }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlValidateName(v: *const XChar, _space: c_int) -> c_int {
    if v.is_null() {
        return -1;
    }
    if valid_name(unsafe { cbytes(v) }, true, false) { 0 } else { 1 }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlValidateNMToken(v: *const XChar, _space: c_int) -> c_int {
    if v.is_null() {
        return -1;
    }
    if valid_name(unsafe { cbytes(v) }, true, true) { 0 } else { 1 }
}

// --- properties --------------------------------------------------------------------------

/// The attribute `name` of `node` in namespace `href` (`None`: no
/// namespace; with `any`, any namespace).
pub unsafe fn find_prop(node: *mut Node, name: &[u8], href: Option<&[u8]>, any_ok: bool) -> *mut Attr {
    if node.is_null() || unsafe { (*node).type_ } != ELEMENT_NODE {
        return null_mut();
    }
    let mut a = unsafe { (*node).properties };
    while !a.is_null() {
        unsafe {
            if cbytes((*a).name) == name {
                let ah = if (*a).ns.is_null() { None } else { copt((*(*a).ns).href) };
                if ah == href || (any_ok && href.is_none()) {
                    return a;
                }
            }
            a = (*a).next;
        }
    }
    null_mut()
}

/// An attribute's value, for xmlGetProp and its kind.
unsafe fn prop_value(a: *mut Attr) -> *mut XChar {
    if a.is_null() {
        return null_mut();
    }
    unsafe { xmlNodeGetContent(a as *const Node) }
}

/// The attribute default declared for an element, as xmlHasProp finds it.
unsafe fn default_prop(node: *mut Node, name: &[u8], href: Option<&[u8]>) -> *mut Attr {
    unsafe {
        let doc = (*node).doc;
        if doc.is_null() {
            return null_mut();
        }
        let ename = cbytes((*node).name);
        let eprefix = if (*node).ns.is_null() { None } else { copt((*(*node).ns).prefix) };
        let full: Vec<u8> = match eprefix {
            Some(p) => [p, b":", ename].concat(),
            None => ename.to_vec(),
        };
        for dtd in [(*doc).intSubset, (*doc).extSubset] {
            if dtd.is_null() || (*dtd).attributes.is_null() {
                continue;
            }
            let t = &*((*dtd).attributes as *mut Hash);
            for v in t.values() {
                let ad = v as *mut AttributeDecl;
                let elem = cbytes((*ad).elem);
                if (elem == full.as_slice() || elem == ename) && cbytes((*ad).name) == name && !(*ad).defaultValue.is_null() {
                    let p = copt((*ad).prefix);
                    let ok = match (href, p) {
                        (None, None) => true,
                        (Some(_), Some(_)) => true,
                        _ => false,
                    };
                    if ok {
                        return ad as *mut Attr;
                    }
                }
            }
        }
    }
    null_mut()
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlHasProp(node: *const Node, name: *const XChar) -> *mut Attr {
    if node.is_null() || name.is_null() {
        return null_mut();
    }
    let node = node as *mut Node;
    let n = unsafe { cbytes(name) };
    let a = unsafe { find_prop(node, n, None, true) };
    if !a.is_null() {
        return a;
    }
    unsafe { default_prop(node, n, None) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlHasNsProp(node: *const Node, name: *const XChar, href: *const XChar) -> *mut Attr {
    if node.is_null() || name.is_null() {
        return null_mut();
    }
    let node = node as *mut Node;
    let n = unsafe { cbytes(name) };
    let h = unsafe { copt(href) };
    let a = unsafe { find_prop(node, n, h, false) };
    if !a.is_null() {
        return a;
    }
    unsafe { default_prop(node, n, h) }
}

unsafe fn value_of_found(a: *mut Attr) -> *mut XChar {
    if a.is_null() {
        return null_mut();
    }
    unsafe {
        if (*a).type_ == ATTRIBUTE_DECL {
            return xstrdup(cbytes((*(a as *mut AttributeDecl)).defaultValue));
        }
        prop_value(a)
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlGetProp(node: *const Node, name: *const XChar) -> *mut XChar {
    unsafe { value_of_found(xmlHasProp(node, name)) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlGetNsProp(node: *const Node, name: *const XChar, href: *const XChar) -> *mut XChar {
    unsafe { value_of_found(xmlHasNsProp(node, name, href)) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlGetNoNsProp(node: *const Node, name: *const XChar) -> *mut XChar {
    if node.is_null() || name.is_null() {
        return null_mut();
    }
    unsafe {
        let node = node as *mut Node;
        let n = cbytes(name);
        let a = find_prop(node, n, None, false);
        if !a.is_null() {
            return prop_value(a);
        }
        value_of_found(default_prop(node, n, None))
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNodeGetAttrValue(node: *const Node, name: *const XChar, href: *const XChar, out: *mut *mut XChar) -> c_int {
    if out.is_null() {
        return -1;
    }
    unsafe {
        *out = null_mut();
        let a = find_prop(node as *mut Node, cbytes(name), copt(href), false);
        if a.is_null() {
            return 1;
        }
        *out = prop_value(a);
    }
    0
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSetNsProp(node: *mut Node, ns: *mut Ns, name: *const XChar, value: *const XChar) -> *mut Attr {
    if node.is_null() || name.is_null() || unsafe { (*node).type_ } != ELEMENT_NODE {
        return null_mut();
    }
    unsafe {
        let href = if ns.is_null() { None } else { copt((*ns).href) };
        let a = find_prop(node, cbytes(name), href, false);
        if !a.is_null() {
            xmlFreeNodeList((*a).children);
            (*a).children = null_mut();
            (*a).last = null_mut();
            (*a).ns = ns;
            if let Some(v) = copt(value) {
                let t = new_text((*node).doc, v);
                (*a).children = t;
                (*a).last = t;
                if !t.is_null() {
                    (*t).parent = a as *mut Node;
                }
            }
            return a;
        }
        new_prop(node, ns, cbytes(name), copt(value), None)
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSetProp(node: *mut Node, name: *const XChar, value: *const XChar) -> *mut Attr {
    if node.is_null() || name.is_null() {
        return null_mut();
    }
    let n = unsafe { cbytes(name) };
    let (p, local) = split_qname(n);
    unsafe {
        if let Some(p) = p {
            let z = nul(p);
            let ns = xmlSearchNs((*node).doc, node, z.as_ptr());
            if !ns.is_null() {
                let l = nul(local);
                return xmlSetNsProp(node, ns, l.as_ptr(), value);
            }
        }
        xmlSetNsProp(node, null_mut(), name, value)
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlUnsetNsProp(node: *mut Node, ns: *mut Ns, name: *const XChar) -> c_int {
    unsafe {
        let href = if ns.is_null() { None } else { copt((*ns).href) };
        let a = find_prop(node, cbytes(name), href, false);
        if a.is_null() {
            return -1;
        }
        xmlUnlinkNode(a as *mut Node);
        xmlFreeProp(a);
    }
    0
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlUnsetProp(node: *mut Node, name: *const XChar) -> c_int {
    unsafe { xmlUnsetNsProp(node, null_mut(), name) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlRemoveProp(a: *mut Attr) -> c_int {
    if a.is_null() {
        return -1;
    }
    unsafe {
        if (*a).parent.is_null() {
            return -1;
        }
        xmlUnlinkNode(a as *mut Node);
        xmlFreeProp(a);
    }
    0
}

// --- content ------------------------------------------------------------------------------

/// The text of a node list: text and CDATA content, entity references as
/// `&name;` (`refs`) or as the entity's text.
pub unsafe fn list_string(list: *mut Node, refs: bool) -> Vec<u8> {
    let mut out = Vec::new();
    let mut n = list;
    while !n.is_null() {
        unsafe {
            match (*n).type_ {
                TEXT_NODE | CDATA_SECTION_NODE => out.extend_from_slice(cbytes((*n).content)),
                ENTITY_REF_NODE => {
                    if refs {
                        out.push(b'&');
                        out.extend_from_slice(cbytes((*n).name));
                        out.push(b';');
                    } else {
                        let ent = xmlGetDocEntity((*n).doc, (*n).name);
                        if !ent.is_null() {
                            node_text(ent as *mut Node, &mut out);
                        }
                    }
                }
                _ => {}
            }
            n = (*n).next;
        }
    }
    out
}

/// The text of a subtree, entities expanded (xmlNodeGetContent).
/// `xmlBufGetEntityRefContent`: the text of the entity a reference names.
unsafe fn entity_ref_content(r: *mut Node, normalize: bool, out: &mut Vec<u8>) {
    unsafe {
        let ent = if !(*r).children.is_null() { (*r).children as *mut Entity } else { xmlGetDocEntity((*r).doc, (*r).name) };
        if ent.is_null() {
            return;
        }
        if (*ent).etype == INTERNAL_PREDEFINED_ENTITY {
            out.extend_from_slice(cbytes((*ent).content));
            return;
        }
        if (*ent).flags & ENT_EXPANDING != 0 {
            return;
        }
        (*ent).flags |= ENT_EXPANDING;
        child_content(ent as *mut Node, normalize, out);
        (*ent).flags &= !ENT_EXPANDING;
    }
}

/// `xmlBufGetChildContent`: the text under `tree`, entity references
/// followed; with `normalize` (an attribute's value), each control
/// character in a text as a space.
unsafe fn child_content(tree: *mut Node, normalize: bool, out: &mut Vec<u8>) {
    unsafe {
        let mut cur = (*tree).children;
        while !cur.is_null() {
            match (*cur).type_ {
                TEXT_NODE | CDATA_SECTION_NODE => {
                    let t = cbytes((*cur).content);
                    if normalize {
                        out.extend(t.iter().map(|&c| if c < 0x20 { b' ' } else { c }));
                    } else {
                        out.extend_from_slice(t);
                    }
                }
                ENTITY_REF_NODE => entity_ref_content(cur, normalize, out),
                _ => {
                    if !(*cur).children.is_null() {
                        cur = (*cur).children;
                        continue;
                    }
                }
            }
            while (*cur).next.is_null() {
                cur = (*cur).parent;
                if cur == tree || cur.is_null() {
                    return;
                }
            }
            cur = (*cur).next;
        }
    }
}

pub unsafe fn node_text(n: *mut Node, out: &mut Vec<u8>) {
    // Explicit stack over (node, visited children).
    let mut stack: Vec<*mut Node> = Vec::new();
    unsafe {
        let mut k = (*n).last;
        while !k.is_null() {
            stack.push(k);
            k = (*k).prev;
        }
        let mut depth = 0usize;
        while let Some(c) = stack.pop() {
            match (*c).type_ {
                TEXT_NODE | CDATA_SECTION_NODE => out.extend_from_slice(cbytes((*c).content)),
                ELEMENT_NODE | DOCUMENT_FRAG_NODE => {
                    let mut k = (*c).last;
                    while !k.is_null() {
                        stack.push(k);
                        k = (*k).prev;
                    }
                }
                ENTITY_REF_NODE => {
                    depth += 1;
                    if depth > 40 {
                        continue;
                    }
                    let ent = xmlGetDocEntity((*c).doc, (*c).name);
                    if !ent.is_null() {
                        let mut k = (*ent).last;
                        while !k.is_null() {
                            stack.push(k);
                            k = (*k).prev;
                        }
                    }
                }
                _ => {}
            }
        }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNodeGetContent(n: *const Node) -> *mut XChar {
    if n.is_null() {
        return null_mut();
    }
    let n = n as *mut Node;
    unsafe {
        match (*n).type_ {
            ELEMENT_NODE | DOCUMENT_FRAG_NODE | DOCUMENT_NODE | HTML_DOCUMENT_NODE | ENTITY_DECL | ATTRIBUTE_NODE => {
                let kids = (*n).children;
                let doc_node = matches!((*n).type_, DOCUMENT_NODE | HTML_DOCUMENT_NODE);
                if !doc_node {
                    if kids.is_null() {
                        return xstrdup(b"");
                    }
                    // A single text, as it is.
                    if matches!((*kids).type_, TEXT_NODE | CDATA_SECTION_NODE) && (*kids).next.is_null() {
                        return xstrdup(copt((*kids).content).unwrap_or(b""));
                    }
                }
                let mut out = Vec::new();
                child_content(n, (*n).type_ == ATTRIBUTE_NODE, &mut out);
                xstrdup(&out)
            }
            ENTITY_REF_NODE => {
                let mut out = Vec::new();
                entity_ref_content(n, false, &mut out);
                xstrdup(&out)
            }
            NAMESPACE_DECL => xstrdup(cbytes((*(n as *mut Ns)).href)),
            TEXT_NODE | CDATA_SECTION_NODE | COMMENT_NODE | PI_NODE => {
                if (*n).content.is_null() {
                    null_mut()
                } else {
                    xstrdup(cbytes((*n).content))
                }
            }
            _ => null_mut(),
        }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNodeListGetString(doc: *mut Doc, list: *const Node, inline: c_int) -> *mut XChar {
    let _ = doc;
    if list.is_null() {
        return xstrdup(b"");
    }
    let s = unsafe { list_string(list as *mut Node, inline == 0) };
    xstrdup(&s)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNodeListGetRawString(doc: *const Doc, list: *const Node, inline: c_int) -> *mut XChar {
    unsafe { xmlNodeListGetString(doc as *mut Doc, list, inline) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNodeSetContent(n: *mut Node, content: *const XChar) -> c_int {
    if n.is_null() {
        return 1;
    }
    unsafe {
        match (*n).type_ {
            ELEMENT_NODE | ATTRIBUTE_NODE | DOCUMENT_FRAG_NODE => {
                xmlFreeNodeList((*n).children);
                (*n).children = null_mut();
                (*n).last = null_mut();
                if let Some(c) = copt(content) {
                    let kids = string_get_node_list((*n).doc, c, false);
                    set_children(n, kids);
                }
            }
            TEXT_NODE | CDATA_SECTION_NODE | COMMENT_NODE | PI_NODE => {
                free_str((*n).doc, (*n).content);
                (*n).content = xstrdup_opt(copt(content));
            }
            _ => {}
        }
    }
    0
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNodeAddContentLen(n: *mut Node, content: *const XChar, len: c_int) -> c_int {
    if n.is_null() || content.is_null() || len <= 0 {
        return 0;
    }
    let add = unsafe { std::slice::from_raw_parts(content, len as usize) };
    unsafe {
        match (*n).type_ {
            ELEMENT_NODE | DOCUMENT_FRAG_NODE => {
                let t = new_text((*n).doc, add);
                xmlAddChild(n, t);
            }
            TEXT_NODE | CDATA_SECTION_NODE | COMMENT_NODE | PI_NODE => {
                let v = [cbytes((*n).content), add].concat();
                free_str((*n).doc, (*n).content);
                (*n).content = xstrdup(&v);
            }
            _ => {}
        }
    }
    0
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNodeAddContent(n: *mut Node, content: *const XChar) -> c_int {
    unsafe { xmlNodeAddContentLen(n, content, cbytes(content).len() as c_int) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNodeGetLang(n: *const Node) -> *mut XChar {
    let mut c = n as *mut Node;
    while !c.is_null() {
        unsafe {
            let a = find_prop(c, b"lang", Some(XML_XML_NAMESPACE), false);
            if !a.is_null() {
                return prop_value(a);
            }
            c = (*c).parent;
        }
    }
    null_mut()
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNodeGetSpacePreserve(n: *const Node) -> c_int {
    let mut c = n as *mut Node;
    while !c.is_null() {
        unsafe {
            let a = find_prop(c, b"space", Some(XML_XML_NAMESPACE), false);
            if !a.is_null() {
                let v = prop_value(a);
                let r = match cbytes(v) {
                    b"preserve" => 1,
                    b"default" => 0,
                    _ => -2,
                };
                xfree(v as *mut c_void);
                if r != -2 {
                    return r;
                }
            }
            c = (*c).parent;
        }
    }
    -1
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNodeGetBase(doc: *const Doc, n: *const Node) -> *mut XChar {
    unsafe {
        let doc = if doc.is_null() && !n.is_null() { (*n).doc } else { doc as *mut Doc };
        let mut c = n as *mut Node;
        while !c.is_null() {
            let a = find_prop(c, b"base", Some(XML_XML_NAMESPACE), false);
            if !a.is_null() {
                return prop_value(a);
            }
            c = (*c).parent;
        }
        if !doc.is_null() && !(*doc).URL.is_null() {
            return xstrdup(cbytes((*doc).URL));
        }
    }
    null_mut()
}

/// Text with `&name;` entity references and character references to a node
/// list (text nodes and entity reference nodes), as xmlNodeParseAttValue
/// makes an attribute's children. With `chars_only`, `&...;` other than
/// character references is kept as text.
pub unsafe fn string_get_node_list(doc: *mut Doc, s: &[u8], chars_only: bool) -> *mut Node {
    let mut head: *mut Node = null_mut();
    let mut tail: *mut Node = null_mut();
    let mut buf: Vec<u8> = Vec::new();
    let push = |n: *mut Node, head: &mut *mut Node, tail: &mut *mut Node| {
        if n.is_null() {
            return;
        }
        unsafe {
            if tail.is_null() {
                *head = n;
            } else {
                (**tail).next = n;
                (*n).prev = *tail;
            }
        }
        *tail = n;
    };
    let mut i = 0;
    while i < s.len() {
        let c = s[i];
        if c == b'&' {
            let semi = s[i..].iter().position(|&x| x == b';').map(|k| i + k);
            let Some(e) = semi else {
                buf.extend_from_slice(&s[i..]);
                break;
            };
            let body = &s[i + 1..e];
            if let Some(num) = body.strip_prefix(b"#") {
                let v = if let Some(h) = num.strip_prefix(b"x") {
                    u32::from_str_radix(std::str::from_utf8(h).unwrap_or("x"), 16).ok()
                } else {
                    std::str::from_utf8(num).ok().and_then(|d| d.parse::<u32>().ok())
                };
                if let Some(ch) = v.and_then(char::from_u32) {
                    let mut tmp = [0u8; 4];
                    buf.extend_from_slice(ch.encode_utf8(&mut tmp).as_bytes());
                }
                i = e + 1;
                continue;
            }
            if chars_only || body.is_empty() {
                buf.extend_from_slice(&s[i..=e]);
                i = e + 1;
                continue;
            }
            let z = nul(body);
            let pre = unsafe { xmlGetPredefinedEntity(z.as_ptr()) };
            if !pre.is_null() {
                buf.extend_from_slice(unsafe { cbytes((*pre).content) });
                i = e + 1;
                continue;
            }
            let ent = unsafe { xmlGetDocEntity(doc, z.as_ptr()) };
            if !ent.is_null() && unsafe { (*ent).flags } & ENT_EXPANDING != 0 {
                // A reference inside its own expansion: dropped.
                i = e + 1;
                continue;
            }
            if !buf.is_empty() {
                push(new_text(doc, &buf), &mut head, &mut tail);
                buf.clear();
            }
            unsafe {
                // The entity's own nodes, parsed once, as an attribute
                // value's (what the reference's text is read from).
                if !ent.is_null() && (*ent).flags & ENT_PARSED == 0 && !(*ent).content.is_null() {
                    (*ent).flags |= ENT_EXPANDING;
                    let kids = string_get_node_list(doc, cbytes((*ent).content), false);
                    (*ent).flags &= !ENT_EXPANDING;
                    set_children(ent as *mut Node, kids);
                    (*ent).flags |= ENT_PARSED;
                }
            }
            let r = unsafe { xmlNewReference(doc, z.as_ptr()) };
            push(r, &mut head, &mut tail);
            i = e + 1;
            continue;
        }
        buf.push(c);
        i += 1;
    }
    if !buf.is_empty() || head.is_null() {
        push(new_text(doc, &buf), &mut head, &mut tail);
    }
    head
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlStringGetNodeList(doc: *const Doc, value: *const XChar) -> *mut Node {
    if value.is_null() {
        return null_mut();
    }
    unsafe { string_get_node_list(doc as *mut Doc, cbytes(value), false) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlStringLenGetNodeList(doc: *const Doc, value: *const XChar, len: c_int) -> *mut Node {
    if value.is_null() || len < 0 {
        return null_mut();
    }
    unsafe { string_get_node_list(doc as *mut Doc, std::slice::from_raw_parts(value, len as usize), false) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNodeParseAttValue(doc: *const Doc, attr: *mut Attr, value: *const XChar, len: usize, out: *mut *mut Node) -> c_int {
    let s = unsafe { std::slice::from_raw_parts(value, len) };
    let kids = unsafe { string_get_node_list(doc as *mut Doc, s, false) };
    if !attr.is_null() {
        unsafe { set_children(attr as *mut Node, kids) };
    } else if !out.is_null() {
        unsafe { *out = kids };
    }
    0
}

// --- copying ----------------------------------------------------------------------------

/// Copies a node (and its subtree with `recursive` 1, or its properties and
/// namespaces only with 2) into `doc`, under `parent`.
unsafe fn copy_node(n: *mut Node, doc: *mut Doc, parent: *mut Node, recursive: c_int) -> *mut Node {
    if n.is_null() {
        return null_mut();
    }
    unsafe {
        match (*n).type_ {
            ATTRIBUTE_NODE => return copy_prop(parent, n as *mut Attr, doc) as *mut Node,
            NAMESPACE_DECL => return xmlCopyNamespace(n as *mut Ns) as *mut Node,
            DOCUMENT_NODE | HTML_DOCUMENT_NODE => return xmlCopyDoc(n as *mut Doc, recursive) as *mut Node,
            DTD_NODE | ENTITY_DECL | ELEMENT_DECL | ATTRIBUTE_DECL => return null_mut(),
            _ => {}
        }
        // The root, then its subtree, with an explicit stack.
        let root = copy_shallow(n, doc, parent);
        if root.is_null() || recursive == 0 {
            return root;
        }
        if (*n).type_ == ELEMENT_NODE {
            copy_attrs_ns(n, root, doc);
        }
        if recursive == 2 || (*n).type_ == ENTITY_REF_NODE {
            return root;
        }
        let mut stack: Vec<(*mut Node, *mut Node)> = vec![((*n).children, root)];
        while let Some((src, dst_parent)) = stack.pop() {
            let mut s = src;
            // Children are appended in order; descend after each.
            let mut pending: Vec<(*mut Node, *mut Node)> = Vec::new();
            while !s.is_null() {
                let c = copy_shallow(s, doc, dst_parent);
                if !c.is_null() {
                    let last = (*dst_parent).last;
                    if last.is_null() {
                        (*dst_parent).children = c;
                    } else {
                        (*last).next = c;
                        (*c).prev = last;
                    }
                    (*dst_parent).last = c;
                    if (*s).type_ == ELEMENT_NODE {
                        copy_attrs_ns(s, c, doc);
                    }
                    if (*s).type_ != ENTITY_REF_NODE && !(*s).children.is_null() {
                        pending.push(((*s).children, c));
                    }
                }
                s = (*s).next;
            }
            stack.extend(pending.into_iter().rev());
        }
        root
    }
}

unsafe fn copy_shallow(n: *mut Node, doc: *mut Doc, parent: *mut Node) -> *mut Node {
    unsafe {
        let ty = (*n).type_;
        let name = if (*n).name.is_null() {
            null()
        } else if static_name((*n).name) {
            (*n).name
        } else {
            node_name(doc, cbytes((*n).name))
        };
        let c = new_node(doc, ty, name);
        if c.is_null() {
            return c;
        }
        (*c).parent = parent;
        (*c).line = (*n).line;
        (*c).extra = (*n).extra;
        match ty {
            ELEMENT_NODE => {}
            ENTITY_REF_NODE => {
                let ent = if doc.is_null() { null_mut() } else { xmlGetDocEntity(doc, (*n).name) };
                let ent = if ent.is_null() { (*n).children as *mut Entity } else { ent };
                (*c).children = ent as *mut Node;
                (*c).last = ent as *mut Node;
                if !ent.is_null() {
                    (*c).content = (*ent).content;
                }
            }
            _ => {
                if !(*n).content.is_null() {
                    (*c).content = xstrdup(cbytes((*n).content));
                }
            }
        }
        registered(c)
    }
}

/// The namespace in scope at `node` for `ns`, in the copy's tree: one
/// declared there, or a new declaration on the copy's root.
unsafe fn copy_ns_ref(ns: *mut Ns, dst: *mut Node, doc: *mut Doc) -> *mut Ns {
    if ns.is_null() {
        return null_mut();
    }
    unsafe {
        let found = xmlSearchNs(doc, dst, (*ns).prefix);
        if !found.is_null() && copt((*found).href) == copt((*ns).href) {
            return found;
        }
        // Declare it on the copy's top.
        let mut root = dst;
        while !(*root).parent.is_null() && (*(*root).parent).type_ == ELEMENT_NODE {
            root = (*root).parent;
        }
        let made = new_ns(root, copt((*ns).href), copt((*ns).prefix));
        if made.is_null() { found } else { made }
    }
}

unsafe fn copy_attrs_ns(src: *mut Node, dst: *mut Node, doc: *mut Doc) {
    unsafe {
        let mut ns = (*src).nsDef;
        let mut last: *mut Ns = null_mut();
        while !ns.is_null() {
            let c = xmlCopyNamespace(ns);
            if !c.is_null() {
                if last.is_null() {
                    (*dst).nsDef = c;
                } else {
                    (*last).next = c;
                }
                last = c;
            }
            ns = (*ns).next;
        }
        if !(*src).ns.is_null() {
            (*dst).ns = copy_ns_ref((*src).ns, dst, doc);
        }
        let mut a = (*src).properties;
        while !a.is_null() {
            copy_prop(dst, a, doc);
            a = (*a).next;
        }
    }
}

unsafe fn copy_prop(target: *mut Node, a: *mut Attr, doc: *mut Doc) -> *mut Attr {
    if a.is_null() {
        return null_mut();
    }
    unsafe {
        let doc = if doc.is_null() && !target.is_null() { (*target).doc } else { doc };
        let c: *mut Attr = xnew();
        if c.is_null() {
            return c;
        }
        (*c).type_ = ATTRIBUTE_NODE;
        (*c).name = node_name(doc, cbytes((*a).name));
        (*c).doc = doc;
        (*c).parent = target;
        (*c).atype = 0;
        if !(*a).ns.is_null() && !target.is_null() {
            (*c).ns = copy_ns_ref((*a).ns, target, doc);
        }
        let mut k = (*a).children;
        while !k.is_null() {
            let kc = copy_shallow(k, doc, c as *mut Node);
            if !kc.is_null() {
                let last = (*c).last;
                if last.is_null() {
                    (*c).children = kc;
                } else {
                    (*last).next = kc;
                    (*kc).prev = last;
                }
                (*c).last = kc;
            }
            k = (*k).next;
        }
        if !target.is_null() {
            let mut p = (*target).properties;
            if p.is_null() {
                (*target).properties = c;
            } else {
                while !(*p).next.is_null() {
                    p = (*p).next;
                }
                (*p).next = c;
                (*c).prev = p;
            }
        }
        registered(c as *mut Node);
        c
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCopyNamespace(ns: *mut Ns) -> *mut Ns {
    if ns.is_null() {
        return null_mut();
    }
    unsafe { new_ns(null_mut(), copt((*ns).href), copt((*ns).prefix)) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCopyNamespaceList(mut ns: *mut Ns) -> *mut Ns {
    let mut head: *mut Ns = null_mut();
    let mut last: *mut Ns = null_mut();
    while !ns.is_null() {
        let c = unsafe { xmlCopyNamespace(ns) };
        if !c.is_null() {
            if last.is_null() {
                head = c;
            } else {
                unsafe { (*last).next = c };
            }
            last = c;
        }
        ns = unsafe { (*ns).next };
    }
    head
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCopyProp(target: *mut Node, a: *mut Attr) -> *mut Attr {
    unsafe { copy_prop_detached(target, a) }
}

/// xmlCopyProp: a copy for `target`, not linked to it.
unsafe fn copy_prop_detached(target: *mut Node, a: *mut Attr) -> *mut Attr {
    if a.is_null() {
        return null_mut();
    }
    unsafe {
        let doc = if target.is_null() { (*a).doc } else { (*target).doc };
        let c = copy_prop(null_mut(), a, doc);
        if !c.is_null() {
            (*c).parent = target;
            if !(*a).ns.is_null() && !target.is_null() {
                (*c).ns = copy_ns_ref((*a).ns, target, doc);
            }
        }
        c
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCopyPropList(target: *mut Node, mut a: *mut Attr) -> *mut Attr {
    let mut head: *mut Attr = null_mut();
    let mut last: *mut Attr = null_mut();
    while !a.is_null() {
        let c = unsafe { copy_prop_detached(target, a) };
        if !c.is_null() {
            if last.is_null() {
                head = c;
            } else {
                unsafe {
                    (*last).next = c;
                    (*c).prev = last;
                }
            }
            last = c;
        }
        a = unsafe { (*a).next };
    }
    head
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCopyNode(n: *mut Node, recursive: c_int) -> *mut Node {
    if n.is_null() {
        return null_mut();
    }
    unsafe { copy_node(n, (*n).doc, null_mut(), recursive) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlDocCopyNode(n: *mut Node, doc: *mut Doc, recursive: c_int) -> *mut Node {
    unsafe { copy_node(n, doc, null_mut(), recursive) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlDocCopyNodeList(doc: *mut Doc, mut n: *mut Node) -> *mut Node {
    let mut head: *mut Node = null_mut();
    let mut last: *mut Node = null_mut();
    while !n.is_null() {
        let c = unsafe { copy_node(n, doc, null_mut(), 1) };
        if !c.is_null() {
            if last.is_null() {
                head = c;
            } else {
                unsafe {
                    (*last).next = c;
                    (*c).prev = last;
                }
            }
            last = c;
        }
        n = unsafe { (*n).next };
    }
    head
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCopyNodeList(n: *mut Node) -> *mut Node {
    if n.is_null() {
        return null_mut();
    }
    unsafe { xmlDocCopyNodeList((*n).doc, n) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCopyDtd(dtd: *mut Dtd) -> *mut Dtd {
    if dtd.is_null() {
        return null_mut();
    }
    unsafe { copy_dtd(dtd, null_mut()) }
}

unsafe fn copy_dtd(dtd: *mut Dtd, doc: *mut Doc) -> *mut Dtd {
    unsafe {
        let c = make_dtd(doc, (*dtd).name, (*dtd).ExternalID, (*dtd).SystemID);
        if c.is_null() {
            return c;
        }
        let mut k = (*dtd).children;
        while !k.is_null() {
            match (*k).type_ {
                ENTITY_DECL => {
                    let e = k as *mut Entity;
                    let mut out = null_mut();
                    add_entity_to(c, cbytes((*e).name), (*e).etype, copt((*e).ExternalID), copt((*e).SystemID), copt((*e).content), &mut out);
                    if !out.is_null() {
                        (*out).orig = xstrdup_opt(copt((*e).orig));
                        (*out).URI = xstrdup_opt(copt((*e).URI));
                        // Its nodes too (xmlCopyEntity), which an
                        // attribute's reference reads its text from.
                        if !(*e).children.is_null() {
                            let kids = xmlDocCopyNodeList(doc, (*e).children);
                            set_children(out as *mut Node, kids);
                        }
                    }
                }
                ELEMENT_DECL => {
                    let e = k as *mut ElementDecl;
                    let full = qname_of((*e).prefix, (*e).name);
                    add_element_decl(c, &full, (*e).etype, (*e).content);
                }
                ATTRIBUTE_DECL => {
                    let a = k as *mut AttributeDecl;
                    let tree = xmlCopyEnumeration((*a).tree);
                    add_attribute_decl(
                        c,
                        cbytes((*a).elem),
                        cbytes((*a).name),
                        copt((*a).prefix),
                        (*a).atype,
                        (*a).def,
                        copt((*a).defaultValue),
                        tree,
                    );
                }
                COMMENT_NODE | PI_NODE => {
                    let n = copy_node(k, doc, c as *mut Node, 1);
                    if !n.is_null() {
                        append(c as *mut Node, n);
                    }
                }
                _ => {}
            }
            k = (*k).next;
        }
        if !(*dtd).notations.is_null() {
            for v in (*((*dtd).notations as *mut Hash)).values() {
                let n = v as *mut Notation;
                add_notation(c, cbytes((*n).name), copt((*n).PublicID), copt((*n).SystemID));
            }
        }
        c
    }
}

fn qname_of(prefix: *const XChar, name: *const XChar) -> Vec<u8> {
    unsafe {
        match copt(prefix) {
            Some(p) => [p, b":", cbytes(name)].concat(),
            None => cbytes(name).to_vec(),
        }
    }
}

/// Appends a child, with no merging.
pub unsafe fn append(parent: *mut Node, n: *mut Node) {
    unsafe {
        (*n).parent = parent;
        let last = (*parent).last;
        if last.is_null() {
            (*parent).children = n;
        } else {
            (*last).next = n;
            (*n).prev = last;
        }
        (*parent).last = n;
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCopyDoc(doc: *mut Doc, recursive: c_int) -> *mut Doc {
    if doc.is_null() {
        return null_mut();
    }
    unsafe {
        let c = xmlNewDoc((*doc).version);
        if c.is_null() {
            return c;
        }
        (*c).type_ = (*doc).type_;
        (*c).name = xstrdup_opt(copt((*doc).name as *const XChar)) as *mut c_char;
        (*c).encoding = xstrdup_opt(copt((*doc).encoding));
        (*c).URL = xstrdup_opt(copt((*doc).URL));
        (*c).charset = (*doc).charset;
        (*c).compression = (*doc).compression;
        (*c).standalone = (*doc).standalone;
        (*c).parseFlags = (*doc).parseFlags;
        (*c).properties = (*doc).properties;
        if recursive == 0 {
            return c;
        }
        if !(*doc).intSubset.is_null() {
            let d = copy_dtd((*doc).intSubset, c);
            if !d.is_null() {
                (*d).parent = c;
                (*c).intSubset = d;
            }
        }
        let mut k = (*doc).children;
        while !k.is_null() {
            if (*k).type_ == DTD_NODE {
                if k as *mut Dtd == (*doc).intSubset && !(*c).intSubset.is_null() {
                    append(c as *mut Node, (*c).intSubset as *mut Node);
                }
            } else {
                let n = copy_node(k, c, c as *mut Node, 1);
                if !n.is_null() {
                    append(c as *mut Node, n);
                }
            }
            k = (*k).next;
        }
        c
    }
}

// --- entities (entities.c) ------------------------------------------------------------

struct Predefined([*mut Entity; 5]);
unsafe impl Sync for Predefined {}
unsafe impl Send for Predefined {}

static PREDEFINED: std::sync::OnceLock<Predefined> = std::sync::OnceLock::new();

fn predefined() -> &'static Predefined {
    PREDEFINED.get_or_init(|| {
        let mk = |name: &'static [u8], content: &'static [u8]| -> *mut Entity {
            let e = Box::into_raw(Box::new(unsafe { std::mem::zeroed::<Entity>() }));
            unsafe {
                (*e).type_ = ENTITY_DECL;
                (*e).name = name.as_ptr();
                (*e).content = content.as_ptr() as *mut XChar;
                (*e).orig = content.as_ptr() as *mut XChar;
                (*e).length = (content.len() - 1) as c_int;
                (*e).etype = INTERNAL_PREDEFINED_ENTITY;
                (*e).flags = ENT_PARSED | ENT_CHECKED;
            }
            e
        };
        Predefined([
            mk(b"lt\0", b"<\0"),
            mk(b"gt\0", b">\0"),
            mk(b"amp\0", b"&\0"),
            mk(b"apos\0", b"'\0"),
            mk(b"quot\0", b"\"\0"),
        ])
    })
}

pub fn predefined_value(name: &[u8]) -> Option<u8> {
    match name {
        b"lt" => Some(b'<'),
        b"gt" => Some(b'>'),
        b"amp" => Some(b'&'),
        b"apos" => Some(b'\''),
        b"quot" => Some(b'"'),
        _ => None,
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlGetPredefinedEntity(name: *const XChar) -> *mut Entity {
    let i = match unsafe { cbytes(name) } {
        b"lt" => 0,
        b"gt" => 1,
        b"amp" => 2,
        b"apos" => 3,
        b"quot" => 4,
        _ => return null_mut(),
    };
    predefined().0[i]
}

fn is_predefined(e: *mut Entity) -> bool {
    predefined().0.contains(&e)
}

unsafe fn create_entity(doc: *mut Doc, name: &[u8], ty: c_int, pubid: Option<&[u8]>, sysid: Option<&[u8]>, content: Option<&[u8]>) -> *mut Entity {
    let e: *mut Entity = xnew();
    if e.is_null() {
        return e;
    }
    unsafe {
        (*e).doc = doc;
        (*e).type_ = ENTITY_DECL;
        (*e).etype = ty;
        (*e).name = node_name(doc, name);
        (*e).ExternalID = xstrdup_opt(pubid);
        (*e).SystemID = xstrdup_opt(sysid);
        if let Some(c) = content {
            (*e).length = c.len() as c_int;
            (*e).content = xstrdup(c);
        }
    }
    e
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewEntity(
    doc: *mut Doc,
    name: *const XChar,
    ty: c_int,
    pubid: *const XChar,
    sysid: *const XChar,
    content: *const XChar,
) -> *mut Entity {
    if name.is_null() {
        return null_mut();
    }
    if !doc.is_null() && unsafe { !(*doc).intSubset.is_null() } {
        let mut out = null_mut();
        unsafe { xmlAddEntity(doc, 0, name, ty, pubid, sysid, content, &mut out) };
        return out;
    }
    unsafe { create_entity(doc, cbytes(name), ty, copt(pubid), copt(sysid), copt(content)) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlFreeEntity(e: *mut Entity) {
    if e.is_null() || is_predefined(e) {
        return;
    }
    unsafe {
        let doc = (*e).doc;
        if !(*e).children.is_null() && (*e).owner == 0 && (*e).children as *mut Entity != e {
            // The parsed content: the entity's own.
            let kids = (*e).children;
            if (*kids).parent == e as *mut Node {
                xmlFreeNodeList(kids);
            }
        }
        free_str(doc, (*e).name);
        xfree((*e).ExternalID as *mut c_void);
        xfree((*e).SystemID as *mut c_void);
        xfree((*e).URI as *mut c_void);
        xfree((*e).content as *mut c_void);
        xfree((*e).orig as *mut c_void);
    }
    xfree(e as *mut c_void);
}

/// xmlAddEntity on a DTD: the libxml2 error code, and the entity made.
pub unsafe fn add_entity_to(
    dtd: *mut Dtd,
    name: &[u8],
    ty: c_int,
    pubid: Option<&[u8]>,
    sysid: Option<&[u8]>,
    content: Option<&[u8]>,
    out: &mut *mut Entity,
) -> c_int {
    *out = null_mut();
    if dtd.is_null() {
        return 506; // XML_DTD_NO_DTD
    }
    unsafe {
        let table: *mut *mut c_void = match ty {
            INTERNAL_GENERAL_ENTITY | EXTERNAL_GENERAL_PARSED_ENTITY | EXTERNAL_GENERAL_UNPARSED_ENTITY => {
                if let Some(pre) = predefined_value(name) {
                    let ok = ty == INTERNAL_GENERAL_ENTITY
                        && content.is_some_and(|c| {
                            (c.len() == 1 && c[0] == pre && matches!(pre, b'>' | b'\'' | b'"'))
                                || predefined_ref(c) == Some(pre as u32)
                        });
                    if !ok {
                        return ERR_REDECL_PREDEF_ENTITY;
                    }
                }
                &raw mut (*dtd).entities
            }
            INTERNAL_PARAMETER_ENTITY | EXTERNAL_PARAMETER_ENTITY => &raw mut (*dtd).pentities,
            _ => return ERR_ARGUMENT,
        };
        if (*table).is_null() {
            *table = Hash::new() as *mut c_void;
        }
        let h = &mut *(*table as *mut Hash);
        let k = (name.to_vec(), Vec::new(), Vec::new());
        if !h.get(&k).is_null() {
            return WAR_ENTITY_REDEFINED;
        }
        let e = create_entity((*dtd).doc, name, ty, pubid, sysid, content);
        if e.is_null() {
            return ERR_NO_MEMORY;
        }
        h.add(k, e as *mut c_void);
        (*e).parent = dtd;
        (*e).doc = (*dtd).doc;
        append(dtd as *mut Node, e as *mut Node);
        *out = e;
    }
    0
}

/// The character a reference `&#NN;` or `&#xHH;` stands for.
fn predefined_ref(c: &[u8]) -> Option<u32> {
    let body = c.strip_prefix(b"&#")?.strip_suffix(b";")?;
    if let Some(h) = body.strip_prefix(b"x") {
        u32::from_str_radix(std::str::from_utf8(h).ok()?, 16).ok()
    } else {
        std::str::from_utf8(body).ok()?.parse().ok()
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlAddEntity(
    doc: *mut Doc,
    ext: c_int,
    name: *const XChar,
    ty: c_int,
    pubid: *const XChar,
    sysid: *const XChar,
    content: *const XChar,
    out: *mut *mut Entity,
) -> c_int {
    if doc.is_null() || name.is_null() {
        return ERR_ARGUMENT;
    }
    let dtd = unsafe { if ext != 0 { (*doc).extSubset } else { (*doc).intSubset } };
    let mut e = null_mut();
    let r = unsafe { add_entity_to(dtd, cbytes(name), ty, copt(pubid), copt(sysid), copt(content), &mut e) };
    if !out.is_null() {
        unsafe { *out = e };
    }
    r
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlAddDocEntity(
    doc: *mut Doc,
    name: *const XChar,
    ty: c_int,
    pubid: *const XChar,
    sysid: *const XChar,
    content: *const XChar,
) -> *mut Entity {
    let mut e = null_mut();
    unsafe { xmlAddEntity(doc, 0, name, ty, pubid, sysid, content, &mut e) };
    e
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlAddDtdEntity(
    doc: *mut Doc,
    name: *const XChar,
    ty: c_int,
    pubid: *const XChar,
    sysid: *const XChar,
    content: *const XChar,
) -> *mut Entity {
    let mut e = null_mut();
    unsafe { xmlAddEntity(doc, 1, name, ty, pubid, sysid, content, &mut e) };
    e
}

unsafe fn lookup_entity(dtd: *mut Dtd, name: &[u8], pe: bool) -> *mut Entity {
    if dtd.is_null() {
        return null_mut();
    }
    let t = unsafe { if pe { (*dtd).pentities } else { (*dtd).entities } } as *mut Hash;
    if t.is_null() {
        return null_mut();
    }
    unsafe { (*t).get1(name) as *mut Entity }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlGetDocEntity(doc: *const Doc, name: *const XChar) -> *mut Entity {
    if name.is_null() {
        return null_mut();
    }
    let n = unsafe { cbytes(name) };
    unsafe {
        if !doc.is_null() {
            let e = lookup_entity((*doc).intSubset, n, false);
            if !e.is_null() {
                return e;
            }
            if (*doc).standalone != 1 {
                let e = lookup_entity((*doc).extSubset, n, false);
                if !e.is_null() {
                    return e;
                }
            }
        }
        xmlGetPredefinedEntity(name)
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlGetDtdEntity(doc: *mut Doc, name: *const XChar) -> *mut Entity {
    if doc.is_null() || name.is_null() {
        return null_mut();
    }
    unsafe { lookup_entity((*doc).extSubset, cbytes(name), false) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlGetParameterEntity(doc: *mut Doc, name: *const XChar) -> *mut Entity {
    if doc.is_null() || name.is_null() {
        return null_mut();
    }
    let n = unsafe { cbytes(name) };
    unsafe {
        let e = lookup_entity((*doc).intSubset, n, true);
        if !e.is_null() {
            return e;
        }
        lookup_entity((*doc).extSubset, n, true)
    }
}

fn encode_entities(s: &[u8], attr_quot: bool, non_ascii: bool) -> Vec<u8> {
    let mut out = Vec::with_capacity(s.len());
    let t = std::str::from_utf8(s).ok();
    match t {
        Some(t) => {
            for ch in t.chars() {
                match ch {
                    '<' => out.extend_from_slice(b"&lt;"),
                    '>' => out.extend_from_slice(b"&gt;"),
                    '&' => out.extend_from_slice(b"&amp;"),
                    '"' if attr_quot => out.extend_from_slice(b"&quot;"),
                    '\r' => out.extend_from_slice(b"&#13;"),
                    c if non_ascii && (c as u32) >= 0x80 => out.extend_from_slice(format!("&#x{:X};", c as u32).as_bytes()),
                    c => {
                        let mut tmp = [0u8; 4];
                        out.extend_from_slice(c.encode_utf8(&mut tmp).as_bytes());
                    }
                }
            }
        }
        None => out.extend_from_slice(s),
    }
    out
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlEncodeEntitiesReentrant(doc: *mut Doc, input: *const XChar) -> *mut XChar {
    if input.is_null() {
        return null_mut();
    }
    let non_ascii = !doc.is_null() && unsafe { (*doc).encoding.is_null() };
    xstrdup(&encode_entities(unsafe { cbytes(input) }, false, non_ascii))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlEncodeSpecialChars(_doc: *const Doc, input: *const XChar) -> *mut XChar {
    if input.is_null() {
        return null_mut();
    }
    xstrdup(&encode_entities(unsafe { cbytes(input) }, true, false))
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlCreateEntitiesTable() -> *mut Hash {
    Hash::new()
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlFreeEntitiesTable(t: *mut Hash) {
    unsafe { free_table(t, |p| xmlFreeEntity(p as *mut Entity)) };
}

// --- DTD declarations (valid.c) -------------------------------------------------------

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewDocElementContent(_doc: *mut Doc, name: *const XChar, ty: c_int) -> *mut ElementContent {
    let c: *mut ElementContent = xnew();
    if c.is_null() {
        return c;
    }
    unsafe {
        (*c).type_ = ty;
        (*c).ocur = CONTENT_ONCE;
        if let Some(n) = copt(name) {
            let (p, l) = split_qname(n);
            (*c).name = xstrdup(l);
            (*c).prefix = xstrdup_opt(p);
        }
    }
    c
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewElementContent(name: *const XChar, ty: c_int) -> *mut ElementContent {
    unsafe { xmlNewDocElementContent(null_mut(), name, ty) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlFreeDocElementContent(_doc: *mut Doc, c: *mut ElementContent) {
    if c.is_null() {
        return;
    }
    let mut stack = vec![c];
    while let Some(n) = stack.pop() {
        unsafe {
            if !(*n).c1.is_null() {
                stack.push((*n).c1);
            }
            if !(*n).c2.is_null() {
                stack.push((*n).c2);
            }
            xfree((*n).name as *mut c_void);
            xfree((*n).prefix as *mut c_void);
        }
        xfree(n as *mut c_void);
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlFreeElementContent(c: *mut ElementContent) {
    unsafe { xmlFreeDocElementContent(null_mut(), c) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCopyDocElementContent(_doc: *mut Doc, c: *mut ElementContent) -> *mut ElementContent {
    if c.is_null() {
        return null_mut();
    }
    unsafe {
        let n: *mut ElementContent = xnew();
        if n.is_null() {
            return n;
        }
        (*n).type_ = (*c).type_;
        (*n).ocur = (*c).ocur;
        (*n).name = xstrdup_opt(copt((*c).name));
        (*n).prefix = xstrdup_opt(copt((*c).prefix));
        // Content models nest as deep as the DTD writes them (libxml2's
        // parser caps that at 256 levels, 2048 with XML_PARSE_HUGE).
        if !(*c).c1.is_null() {
            (*n).c1 = xmlCopyDocElementContent(null_mut(), (*c).c1);
            if !(*n).c1.is_null() {
                (*(*n).c1).parent = n;
            }
        }
        if !(*c).c2.is_null() {
            (*n).c2 = xmlCopyDocElementContent(null_mut(), (*c).c2);
            if !(*n).c2.is_null() {
                (*(*n).c2).parent = n;
            }
        }
        n
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCopyElementContent(c: *mut ElementContent) -> *mut ElementContent {
    unsafe { xmlCopyDocElementContent(null_mut(), c) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCreateEnumeration(name: *const XChar) -> *mut Enumeration {
    let e: *mut Enumeration = xnew();
    if !e.is_null() {
        unsafe { (*e).name = xstrdup_opt(copt(name)) };
    }
    e
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlFreeEnumeration(mut e: *mut Enumeration) {
    while !e.is_null() {
        let next = unsafe { (*e).next };
        unsafe { xfree((*e).name as *mut c_void) };
        xfree(e as *mut c_void);
        e = next;
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCopyEnumeration(mut e: *mut Enumeration) -> *mut Enumeration {
    let mut head: *mut Enumeration = null_mut();
    let mut last: *mut Enumeration = null_mut();
    while !e.is_null() {
        let c = unsafe { xmlCreateEnumeration((*e).name) };
        if last.is_null() {
            head = c;
        } else {
            unsafe { (*last).next = c };
        }
        last = c;
        e = unsafe { (*e).next };
    }
    head
}

unsafe fn free_element_decl(e: *mut ElementDecl) {
    if e.is_null() {
        return;
    }
    unsafe {
        xmlUnlinkNode(e as *mut Node);
        xmlFreeDocElementContent(null_mut(), (*e).content);
        free_str((*e).doc, (*e).name);
        xfree((*e).prefix as *mut c_void);
    }
    xfree(e as *mut c_void);
}

unsafe fn free_attribute_decl(a: *mut AttributeDecl) {
    if a.is_null() {
        return;
    }
    unsafe {
        xmlUnlinkNode(a as *mut Node);
        xmlFreeEnumeration((*a).tree);
        free_str((*a).doc, (*a).name);
        free_str((*a).doc, (*a).elem);
        xfree((*a).prefix as *mut c_void);
        xfree((*a).defaultValue as *mut c_void);
    }
    xfree(a as *mut c_void);
}

unsafe fn free_notation(n: *mut Notation) {
    if n.is_null() {
        return;
    }
    unsafe {
        xfree((*n).name as *mut c_void);
        xfree((*n).PublicID as *mut c_void);
        xfree((*n).SystemID as *mut c_void);
    }
    xfree(n as *mut c_void);
}

/// The element declaration for `name` (`prefix:local`), made as a
/// placeholder (type UNDEFINED, not in the DTD's children) when there is
/// none, as xmlGetDtdElementDesc2 does for an attribute list.
unsafe fn element_desc(dtd: *mut Dtd, name: &[u8], create: bool) -> *mut ElementDecl {
    unsafe {
        if (*dtd).elements.is_null() {
            if !create {
                return null_mut();
            }
            (*dtd).elements = Hash::new() as *mut c_void;
        }
        let t = &mut *((*dtd).elements as *mut Hash);
        let (p, l) = split_qname(name);
        let k = (l.to_vec(), p.unwrap_or(b"").to_vec(), Vec::new());
        let e = t.get(&k) as *mut ElementDecl;
        if !e.is_null() || !create {
            return e;
        }
        let e: *mut ElementDecl = xnew();
        if e.is_null() {
            return e;
        }
        (*e).type_ = ELEMENT_DECL;
        (*e).name = xstrdup(l);
        (*e).prefix = xstrdup_opt(p);
        (*e).etype = 0;
        (*e).doc = (*dtd).doc;
        t.add(k, e as *mut c_void);
        e
    }
}

pub unsafe fn add_element_decl(dtd: *mut Dtd, name: &[u8], ty: c_int, content: *mut ElementContent) -> *mut ElementDecl {
    if dtd.is_null() {
        return null_mut();
    }
    match ty {
        ELEMENT_TYPE_EMPTY | ELEMENT_TYPE_ANY if !content.is_null() => return null_mut(),
        ELEMENT_TYPE_MIXED | ELEMENT_TYPE_ELEMENT if content.is_null() => return null_mut(),
        ELEMENT_TYPE_EMPTY | ELEMENT_TYPE_ANY | ELEMENT_TYPE_MIXED | ELEMENT_TYPE_ELEMENT => {}
        _ => return null_mut(),
    }
    unsafe {
        let mut old_attrs: *mut AttributeDecl = null_mut();
        let doc = (*dtd).doc;
        let (p, l) = split_qname(name);
        let k = (l.to_vec(), p.unwrap_or(b"").to_vec(), Vec::new());
        // A placeholder in the internal subset gives way to a declaration.
        if !doc.is_null() && !(*doc).intSubset.is_null() && (*doc).intSubset != dtd && !(*(*doc).intSubset).elements.is_null() {
            let it = &mut *((*(*doc).intSubset).elements as *mut Hash);
            let e = it.get(&k) as *mut ElementDecl;
            if !e.is_null() && (*e).etype == 0 {
                old_attrs = (*e).attributes;
                (*e).attributes = null_mut();
                it.remove(&k);
                free_element_decl(e);
            }
        }
        let e = element_desc(dtd, name, true);
        if e.is_null() {
            return e;
        }
        if (*e).etype != 0 {
            return null_mut();
        }
        if !old_attrs.is_null() {
            (*e).attributes = old_attrs;
        }
        (*e).etype = ty;
        if !content.is_null() {
            (*e).content = xmlCopyDocElementContent(doc, content);
        }
        (*e).parent = dtd;
        (*e).doc = doc;
        append(dtd as *mut Node, e as *mut Node);
        e
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlAddElementDecl(_v: *mut c_void, dtd: *mut Dtd, name: *const XChar, ty: c_int, content: *mut ElementContent) -> *mut ElementDecl {
    if name.is_null() {
        return null_mut();
    }
    unsafe { add_element_decl(dtd, cbytes(name), ty, content) }
}

#[allow(clippy::too_many_arguments)]
pub unsafe fn add_attribute_decl(
    dtd: *mut Dtd,
    elem: &[u8],
    name: &[u8],
    prefix: Option<&[u8]>,
    ty: c_int,
    def: c_int,
    default: Option<&[u8]>,
    tree: *mut Enumeration,
) -> *mut AttributeDecl {
    if dtd.is_null() {
        unsafe { xmlFreeEnumeration(tree) };
        return null_mut();
    }
    unsafe {
        let doc = (*dtd).doc;
        let k = (name.to_vec(), prefix.unwrap_or(b"").to_vec(), elem.to_vec());
        if !doc.is_null() && (*doc).extSubset == dtd && !(*doc).intSubset.is_null() && !(*(*doc).intSubset).attributes.is_null() {
            let it = &*((*(*doc).intSubset).attributes as *mut Hash);
            if !it.get(&k).is_null() {
                xmlFreeEnumeration(tree);
                return null_mut();
            }
        }
        if (*dtd).attributes.is_null() {
            (*dtd).attributes = Hash::new() as *mut c_void;
        }
        let t = &mut *((*dtd).attributes as *mut Hash);
        if !t.get(&k).is_null() {
            xmlFreeEnumeration(tree);
            return null_mut();
        }
        let a: *mut AttributeDecl = xnew();
        if a.is_null() {
            xmlFreeEnumeration(tree);
            return a;
        }
        (*a).type_ = ATTRIBUTE_DECL;
        (*a).atype = ty;
        (*a).doc = doc;
        (*a).name = node_name(doc, name);
        (*a).elem = node_name(doc, elem);
        (*a).prefix = xstrdup_opt(prefix);
        (*a).def = def;
        (*a).tree = tree;
        (*a).defaultValue = xstrdup_opt(default);
        let ed = element_desc(dtd, elem, true);
        t.add(k, a as *mut c_void);
        if !ed.is_null() {
            let is_ns = name == b"xmlns" || prefix == Some(b"xmlns");
            if is_ns || (*ed).attributes.is_null() {
                (*a).nexth = (*ed).attributes;
                (*ed).attributes = a;
            } else {
                let mut tmp = (*ed).attributes;
                while !(*tmp).nexth.is_null() && (cbytes((*tmp).name) == b"xmlns" || copt((*tmp).prefix) == Some(b"xmlns")) {
                    tmp = (*tmp).nexth;
                }
                (*a).nexth = (*tmp).nexth;
                (*tmp).nexth = a;
            }
        }
        (*a).parent = dtd;
        append(dtd as *mut Node, a as *mut Node);
        a
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlAddAttributeDecl(
    _v: *mut c_void,
    dtd: *mut Dtd,
    elem: *const XChar,
    name: *const XChar,
    ns: *const XChar,
    ty: c_int,
    def: c_int,
    default: *const XChar,
    tree: *mut Enumeration,
) -> *mut AttributeDecl {
    if elem.is_null() || name.is_null() {
        unsafe { xmlFreeEnumeration(tree) };
        return null_mut();
    }
    unsafe { add_attribute_decl(dtd, cbytes(elem), cbytes(name), copt(ns), ty, def, copt(default), tree) }
}

pub unsafe fn add_notation(dtd: *mut Dtd, name: &[u8], pubid: Option<&[u8]>, sysid: Option<&[u8]>) -> *mut Notation {
    if dtd.is_null() || (pubid.is_none() && sysid.is_none()) {
        return null_mut();
    }
    unsafe {
        if (*dtd).notations.is_null() {
            (*dtd).notations = Hash::new() as *mut c_void;
        }
        let t = &mut *((*dtd).notations as *mut Hash);
        let k = (name.to_vec(), Vec::new(), Vec::new());
        if !t.get(&k).is_null() {
            return null_mut();
        }
        let n: *mut Notation = xnew();
        if n.is_null() {
            return n;
        }
        (*n).name = xstrdup(name);
        (*n).PublicID = xstrdup_opt(pubid);
        (*n).SystemID = xstrdup_opt(sysid);
        t.add(k, n as *mut c_void);
        n
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlAddNotationDecl(_v: *mut c_void, dtd: *mut Dtd, name: *const XChar, pubid: *const XChar, sysid: *const XChar) -> *mut Notation {
    if name.is_null() {
        return null_mut();
    }
    unsafe { add_notation(dtd, cbytes(name), copt(pubid), copt(sysid)) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlGetDtdElementDesc(dtd: *mut Dtd, name: *const XChar) -> *mut ElementDecl {
    if dtd.is_null() || name.is_null() {
        return null_mut();
    }
    let e = unsafe { element_desc(dtd, cbytes(name), false) };
    if !e.is_null() && unsafe { (*e).etype } == 0 { null_mut() } else { e }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlGetDtdQElementDesc(dtd: *mut Dtd, name: *const XChar, prefix: *const XChar) -> *mut ElementDecl {
    let q = qname_of(prefix, name);
    let z = nul(&q);
    unsafe { xmlGetDtdElementDesc(dtd, z.as_ptr()) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlGetDtdQAttrDesc(dtd: *mut Dtd, elem: *const XChar, name: *const XChar, prefix: *const XChar) -> *mut AttributeDecl {
    if dtd.is_null() || unsafe { (*dtd).attributes }.is_null() {
        return null_mut();
    }
    let k = unsafe { (cbytes(name).to_vec(), cbytes(prefix).to_vec(), cbytes(elem).to_vec()) };
    unsafe { (*((*dtd).attributes as *mut Hash)).get(&k) as *mut AttributeDecl }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlGetDtdAttrDesc(dtd: *mut Dtd, elem: *const XChar, name: *const XChar) -> *mut AttributeDecl {
    if name.is_null() {
        return null_mut();
    }
    let n = unsafe { cbytes(name) };
    let (p, l) = split_qname(n);
    let zl = nul(l);
    let zp = p.map(nul);
    unsafe { xmlGetDtdQAttrDesc(dtd, elem, zl.as_ptr(), zp.as_ref().map_or(null(), |x| x.as_ptr())) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlGetDtdNotationDesc(dtd: *mut Dtd, name: *const XChar) -> *mut Notation {
    if dtd.is_null() || name.is_null() || unsafe { (*dtd).notations }.is_null() {
        return null_mut();
    }
    unsafe { (*((*dtd).notations as *mut Hash)).get1(cbytes(name)) as *mut Notation }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlFreeElementTable(t: *mut Hash) {
    unsafe { free_table(t, |p| free_element_decl(p as *mut ElementDecl)) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlFreeAttributeTable(t: *mut Hash) {
    unsafe { free_table(t, |p| free_attribute_decl(p as *mut AttributeDecl)) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlFreeNotationTable(t: *mut Hash) {
    unsafe { free_table(t, |p| free_notation(p as *mut Notation)) };
}

// --- IDs ---------------------------------------------------------------------------------

/// Whether `attr` on `elem` is an ID: xml:id, or declared ID.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlIsID(doc: *mut Doc, elem: *mut Node, attr: *mut Attr) -> c_int {
    if attr.is_null() || unsafe { (*attr).name }.is_null() {
        return 0;
    }
    unsafe {
        let name = cbytes((*attr).name);
        if name == b"id" && !(*attr).ns.is_null() && copt((*(*attr).ns).prefix) == Some(b"xml") {
            return 1;
        }
        if doc.is_null() || elem.is_null() || (*elem).type_ != ELEMENT_NODE {
            return 0;
        }
        let full_e = qname_of(if (*elem).ns.is_null() { null() } else { (*(*elem).ns).prefix }, (*elem).name);
        let prefix = if (*attr).ns.is_null() { None } else { copt((*(*attr).ns).prefix) };
        for dtd in [(*doc).intSubset, (*doc).extSubset] {
            if dtd.is_null() || (*dtd).attributes.is_null() {
                continue;
            }
            let t = &*((*dtd).attributes as *mut Hash);
            let k = (name.to_vec(), prefix.unwrap_or(b"").to_vec(), full_e.clone());
            let a = t.get(&k) as *mut AttributeDecl;
            if !a.is_null() && (*a).atype == ATTRIBUTE_ID {
                return 1;
            }
        }
    }
    0
}

fn ids(doc: *mut Doc) -> *mut Hash {
    unsafe {
        if (*doc).ids.is_null() {
            (*doc).ids = Hash::new() as *mut c_void;
        }
        (*doc).ids as *mut Hash
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlAddIDSafe(attr: *mut Attr, value: *const XChar) -> c_int {
    if attr.is_null() || value.is_null() {
        return -1;
    }
    unsafe {
        let doc = (*attr).doc;
        if doc.is_null() {
            return -1;
        }
        let t = &mut *ids(doc);
        let k = (cbytes(value).to_vec(), Vec::new(), Vec::new());
        if !t.get(&k).is_null() {
            return 0;
        }
        let id: *mut Id = xnew();
        if id.is_null() {
            return -1;
        }
        (*id).value = xstrdup(cbytes(value));
        (*id).attr = attr;
        (*id).doc = doc;
        (*attr).atype = ATTRIBUTE_ID;
        (*attr).id = id;
        t.add(k, id as *mut c_void);
    }
    1
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlAddID(_v: *mut c_void, _doc: *mut Doc, value: *const XChar, attr: *mut Attr) -> *mut Id {
    unsafe {
        if xmlAddIDSafe(attr, value) == 1 { (*attr).id } else { null_mut() }
    }
}

unsafe fn remove_id(doc: *mut Doc, a: *mut Attr) {
    unsafe {
        let id = (*a).id;
        if id.is_null() || (*doc).ids.is_null() {
            return;
        }
        let t = &mut *((*doc).ids as *mut Hash);
        let k = (cbytes((*id).value).to_vec(), Vec::new(), Vec::new());
        if t.get(&k) == id as *mut c_void {
            t.remove(&k);
            xfree((*id).value as *mut c_void);
            xfree(id as *mut c_void);
        }
        (*a).id = null_mut();
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlRemoveID(doc: *mut Doc, attr: *mut Attr) -> c_int {
    if doc.is_null() || attr.is_null() || unsafe { (*attr).id }.is_null() {
        return -1;
    }
    unsafe {
        remove_id(doc, attr);
        (*attr).atype = 0;
    }
    0
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlGetID(doc: *mut Doc, id: *const XChar) -> *mut Attr {
    if doc.is_null() || id.is_null() || unsafe { (*doc).ids }.is_null() {
        return null_mut();
    }
    let i = unsafe { (*((*doc).ids as *mut Hash)).get1(cbytes(id)) } as *mut Id;
    if i.is_null() { null_mut() } else { unsafe { (*i).attr } }
}

unsafe fn free_ids(doc: *mut Doc) {
    unsafe {
        let t = (*doc).ids as *mut Hash;
        if t.is_null() {
            return;
        }
        (*doc).ids = null_mut();
        let h = Box::from_raw(t);
        for v in h.values() {
            let id = v as *mut Id;
            if !(*id).attr.is_null() {
                (*(*id).attr).id = null_mut();
            }
            xfree((*id).value as *mut c_void);
            xfree(id as *mut c_void);
        }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlFreeIDTable(t: *mut Hash) {
    if t.is_null() {
        return;
    }
    let h = unsafe { Box::from_raw(t) };
    for v in h.values() {
        let id = v as *mut Id;
        unsafe { xfree((*id).value as *mut c_void) };
        xfree(id as *mut c_void);
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlIsRef(_doc: *mut Doc, _elem: *mut Node, _attr: *mut Attr) -> c_int {
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlAddRef(_v: *mut c_void, _doc: *mut Doc, _value: *const XChar, _attr: *mut Attr) -> *mut c_void {
    null_mut()
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlIsMixedElement(_doc: *mut Doc, _name: *const XChar) -> c_int {
    -1
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNodeGetPath(_n: *const Node) -> *mut XChar {
    null_mut()
}
