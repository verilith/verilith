//! The parser context (parser.h) and the walk over the verified tape that
//! makes libxml2's SAX calls (parser.c, parserInternals.c).
//!
//! The verified parser reads the whole document first; this code then
//! makes the calls libxml2 would make reading it, in its order and with its
//! arguments: character data cut where libxml2 cuts it, attribute values in
//! the form libxml2 passes them, entity references looked up through the
//! handler and their content parsed (and reported) as libxml2 does, and the
//! namespace processing of `xmlParseStartTag2`.
use super::codes::*;
use super::sax2::*;
use super::tree::*;
use super::*;
use crate::api::{Document, Src};
use crate::tape::{Kind, Tok};
use std::borrow::Cow;

// --- the structs (parser.h, valid.h) ---------------------------------------------

#[repr(C)]
pub struct ParserInput {
    pub buf: *mut c_void,
    pub filename: *const c_char,
    pub directory: *const c_char,
    pub base: *const XChar,
    pub cur: *const XChar,
    pub end: *const XChar,
    pub length: c_int,
    pub line: c_int,
    pub col: c_int,
    pub consumed: c_ulong,
    pub free: Option<unsafe extern "C" fn(*mut XChar)>,
    pub encoding: *const XChar,
    pub version: *const XChar,
    pub flags: c_int,
    pub id: c_int,
    pub parentConsumed: c_ulong,
    pub entity: *mut Entity,
}

/// `flags`: the bytes at `base` are the caller's (XML_INPUT_BUF_STATIC).
const INPUT_STATIC: c_int = 1 << 1;
/// This library's: `base` holds the raw bytes, from `xmlMalloc`, and the
/// text the walk reads is kept by the context.
const INPUT_OWNED: c_int = 1 << 30;

#[repr(C)]
pub struct ValidCtxt {
    pub userData: *mut c_void,
    pub error: MsgF,
    pub warning: MsgF,
    pub node: *mut Node,
    pub nodeNr: c_int,
    pub nodeMax: c_int,
    pub nodeTab: *mut *mut Node,
    pub flags: c_uint,
    pub doc: *mut Doc,
    pub valid: c_int,
    pub vstate: *mut c_void,
    pub vstateNr: c_int,
    pub vstateMax: c_int,
    pub vstateTab: *mut c_void,
    pub am: *mut c_void,
    pub state: *mut c_void,
}

#[repr(C)]
pub struct NodeInfoSeq {
    pub maximum: c_ulong,
    pub length: c_ulong,
    pub buffer: *mut c_void,
}

#[repr(C)]
pub struct ParserCtxt {
    pub sax: *mut SaxHandler,
    pub userData: *mut c_void,
    pub myDoc: *mut Doc,
    pub wellFormed: c_int,
    pub replaceEntities: c_int,
    pub version: *mut XChar,
    pub encoding: *mut XChar,
    pub standalone: c_int,
    pub html: c_int,
    pub input: *mut ParserInput,
    pub inputNr: c_int,
    pub inputMax: c_int,
    pub inputTab: *mut *mut ParserInput,
    pub node: *mut Node,
    pub nodeNr: c_int,
    pub nodeMax: c_int,
    pub nodeTab: *mut *mut Node,
    pub record_info: c_int,
    pub node_seq: NodeInfoSeq,
    pub errNo: c_int,
    pub hasExternalSubset: c_int,
    pub hasPErefs: c_int,
    pub external: c_int,
    pub valid: c_int,
    pub validate: c_int,
    pub vctxt: ValidCtxt,
    pub instate: c_int,
    pub token: c_int,
    pub directory: *mut c_char,
    pub name: *const XChar,
    pub nameNr: c_int,
    pub nameMax: c_int,
    pub nameTab: *mut *const XChar,
    pub nbChars: c_long,
    pub checkIndex: c_long,
    pub keepBlanks: c_int,
    pub disableSAX: c_int,
    pub inSubset: c_int,
    pub intSubName: *const XChar,
    pub extSubURI: *mut XChar,
    pub extSubSystem: *mut XChar,
    pub space: *mut c_int,
    pub spaceNr: c_int,
    pub spaceMax: c_int,
    pub spaceTab: *mut c_int,
    pub depth: c_int,
    pub entity: *mut ParserInput,
    pub charset: c_int,
    pub nodelen: c_int,
    pub nodemem: c_int,
    pub pedantic: c_int,
    pub _private: *mut c_void,
    pub loadsubset: c_int,
    pub linenumbers: c_int,
    pub catalogs: *mut c_void,
    pub recovery: c_int,
    pub progressive: c_int,
    pub dict: *mut Dict,
    pub atts: *mut *const XChar,
    pub maxatts: c_int,
    pub docdict: c_int,
    pub str_xml: *const XChar,
    pub str_xmlns: *const XChar,
    pub str_xml_ns: *const XChar,
    pub sax2: c_int,
    pub nsNr: c_int,
    pub nsMax: c_int,
    pub nsTab: *mut *const XChar,
    pub attallocs: *mut c_uint,
    pub pushTab: *mut c_void,
    pub attsDefault: *mut c_void,
    pub attsSpecial: *mut c_void,
    pub nsWellFormed: c_int,
    pub options: c_int,
    pub dictNames: c_int,
    pub freeElemsNr: c_int,
    pub freeElems: *mut Node,
    pub freeAttrsNr: c_int,
    pub freeAttrs: *mut Attr,
    pub lastError: XmlError,
    pub parseMode: c_int,
    pub nbentities: c_ulong,
    pub sizeentities: c_ulong,
    pub nodeInfo: *mut c_void,
    pub nodeInfoNr: c_int,
    pub nodeInfoMax: c_int,
    pub nodeInfoTab: *mut c_void,
    pub input_id: c_int,
    pub sizeentcopy: c_ulong,
    pub endCheckState: c_int,
    pub nbErrors: c_ushort,
    pub nbWarnings: c_ushort,
    pub maxAmpl: c_uint,
    pub nsdb: *mut c_void,
    pub attrHashMax: c_uint,
    pub attrHash: *mut c_void,
    pub errorHandler: StructuredErrorF,
    pub errorCtxt: *mut c_void,
    pub resourceLoader: *mut c_void,
    pub resourceCtxt: *mut c_void,
    pub convImpl: *mut c_void,
    pub convCtxt: *mut c_void,
    /// This library's state; not in libxml2's struct, after all of it.
    pub st: *mut State,
}

macro_rules! offsets {
    ($t:ty; $($f:ident),*) => {
        vec![std::mem::size_of::<$t>(), $(std::mem::offset_of!($t, $f)),*]
    };
}

/// The layout of `ParserCtxt`, up to its last libxml2 field, for
/// tests/c/libxml2_layout.c (the size is that of libxml2's struct).
pub fn ctxt_layout() -> Vec<usize> {
    let mut v = offsets!(ParserCtxt; sax, userData, myDoc, wellFormed, replaceEntities, version, encoding, standalone, html, input, inputNr, inputMax, inputTab, node, nodeNr, nodeMax, nodeTab, record_info, node_seq, errNo, hasExternalSubset, hasPErefs, external, valid, validate, vctxt, instate, token, directory, name, nameNr, nameMax, nameTab, nbChars, checkIndex, keepBlanks, disableSAX, inSubset, intSubName, extSubURI, extSubSystem, space, spaceNr, spaceMax, spaceTab, depth, entity, charset, nodelen, nodemem, pedantic, _private, loadsubset, linenumbers, catalogs, recovery, progressive, dict, atts, maxatts, docdict, str_xml, str_xmlns, str_xml_ns, sax2, nsNr, nsMax, nsTab, attallocs, pushTab, attsDefault, attsSpecial, nsWellFormed, options, dictNames, freeElemsNr, freeElems, freeAttrsNr, freeAttrs, lastError, parseMode, nbentities, sizeentities, nodeInfo, nodeInfoNr, nodeInfoMax, nodeInfoTab, input_id, sizeentcopy, endCheckState, nbErrors, nbWarnings, maxAmpl, nsdb, attrHashMax, attrHash, errorHandler, errorCtxt, resourceLoader, resourceCtxt, convImpl, convCtxt);
    v[0] = std::mem::offset_of!(ParserCtxt, st);
    v
}

// --- this library's state ------------------------------------------------------------

/// A namespace binding in scope: prefix and URI (dictionary strings, NULL
/// for none), and what the SAX handler stored with it.
#[derive(Clone, Copy)]
struct NsBinding {
    prefix: *const XChar,
    uri: *const XChar,
    sax: *mut Ns,
}

pub struct State {
    /// The encoding the document declares, when the text read is a
    /// conversion whose declaration names UTF-8 instead.
    declared: Option<Vec<u8>>,
    /// What was read or pushed, raw.
    raw: Vec<u8>,
    /// The parsed document; it borrows `raw`, so it is dropped first.
    doc: Option<Box<Document<'static>>>,
    ns: Vec<NsBinding>,
    /// Bindings below this are not visible (an entity's content, §4.4.3).
    min_ns: usize,
    /// For each open element, how many bindings it pushed.
    ns_counts: Vec<usize>,
    nodes: Vec<*mut Node>,
    spaces: Vec<c_int>,
    /// Line tracking over the document text: offset, line, column there.
    at: (usize, c_int, c_int),
    /// Entities being expanded (their index), against loops.
    expanding: Vec<usize>,
    /// Bytes copied from entity expansions, against amplification.
    copied: u64,
    /// The push parser was given its last chunk.
    terminated: bool,
    /// The input bytes are external (`xmlCtxtReadFd`, ...) and in `raw`.
    pushed: bool,
    /// A filename for the push parser's input.
    push_name: Option<Vec<u8>>,
}

impl State {
    fn new() -> Box<State> {
        Box::new(State {
            declared: None,
            raw: Vec::new(),
            doc: None,
            ns: Vec::new(),
            min_ns: 0,
            ns_counts: Vec::new(),
            nodes: Vec::new(),
            spaces: Vec::new(),
            at: (0, 1, 1),
            expanding: Vec::new(),
            copied: 0,
            terminated: false,
            pushed: false,
            push_name: None,
        })
    }

    fn clear(&mut self) {
        self.doc = None;
        self.raw = Vec::new();
        self.ns.clear();
        self.min_ns = 0;
        self.ns_counts.clear();
        self.nodes.clear();
        self.spaces.clear();
        self.at = (0, 1, 1);
        self.expanding.clear();
        self.copied = 0;
        self.terminated = false;
        self.pushed = false;
    }
}

unsafe fn st<'a>(ctxt: *mut ParserCtxt) -> &'a mut State {
    unsafe { &mut *(*ctxt).st }
}

// --- the namespace database, as SAX2.c uses it ------------------------------------

/// `xmlParserNsLookupSax`: what the handler stored with the binding of
/// `prefix` in scope.
pub unsafe fn ns_lookup_sax(ctxt: *mut ParserCtxt, prefix: *const XChar) -> *mut Ns {
    unsafe {
        if ctxt.is_null() || (*ctxt).st.is_null() {
            return null_mut();
        }
        let s = st(ctxt);
        let p = copt(prefix);
        for i in (s.min_ns..s.ns.len()).rev() {
            if copt(s.ns[i].prefix) == p {
                return s.ns[i].sax;
            }
        }
        null_mut()
    }
}

/// `xmlParserNsUpdateSax`.
pub unsafe fn ns_update_sax(ctxt: *mut ParserCtxt, prefix: *const XChar, ns: *mut Ns) {
    unsafe {
        if ctxt.is_null() || (*ctxt).st.is_null() {
            return;
        }
        let s = st(ctxt);
        let p = copt(prefix);
        for i in (s.min_ns..s.ns.len()).rev() {
            if copt(s.ns[i].prefix) == p {
                s.ns[i].sax = ns;
                return;
            }
        }
    }
}

/// The URI `prefix` is bound to, if it is bound (and not to "").
fn ns_uri(s: &State, prefix: &[u8]) -> Option<*const XChar> {
    for i in (s.min_ns..s.ns.len()).rev() {
        let b = &s.ns[i];
        if unsafe { cbytes(b.prefix) } == prefix && (b.prefix.is_null() == prefix.is_empty()) {
            if b.uri.is_null() || unsafe { *b.uri } == 0 {
                return None;
            }
            return Some(b.uri);
        }
    }
    None
}

fn ns_bound(s: &State, prefix: &[u8]) -> bool {
    (s.min_ns..s.ns.len()).rev().any(|i| !s.ns[i].prefix.is_null() && unsafe { cbytes(s.ns[i].prefix) } == prefix)
}

// --- the node stack ---------------------------------------------------------------------

/// `nodePush`, with libxml2's depth limit.
pub unsafe fn node_push(ctxt: *mut ParserCtxt, n: *mut Node) -> c_int {
    unsafe {
        let max = if (*ctxt).options & PARSE_HUGE != 0 { 2048 } else { 256 };
        if (*ctxt).nodeNr >= max {
            let msg = format!("Excessive depth in document: {} use XML_PARSE_HUGE option\n", (*ctxt).nodeNr);
            ctx_err(ctxt, null_mut(), FROM_PARSER, ERR_RESOURCE_LIMIT, ERR_FATAL, None, None, None, (*ctxt).nodeNr, msg.as_bytes());
            return -1;
        }
        let s = st(ctxt);
        s.nodes.push(n);
        (*ctxt).nodeNr = s.nodes.len() as c_int;
        (*ctxt).node = n;
        0
    }
}

pub unsafe fn node_pop(ctxt: *mut ParserCtxt) -> *mut Node {
    unsafe {
        let s = st(ctxt);
        let r = s.nodes.pop().unwrap_or(null_mut());
        (*ctxt).nodeNr = s.nodes.len() as c_int;
        (*ctxt).node = s.nodes.last().copied().unwrap_or(null_mut());
        r
    }
}

// --- errors --------------------------------------------------------------------------------

fn catastrophic(e: &XmlError) -> bool {
    xmlIsCatastrophicError(e.level, e.code) != 0
}

/// `xmlCtxtErr`: counts the error in the context, then reports it to the
/// handler in effect, with the input's file and line.
#[allow(clippy::too_many_arguments)]
pub unsafe fn ctx_err(
    ctxt: *mut ParserCtxt,
    node: *mut Node,
    domain: c_int,
    code: c_int,
    level: c_int,
    str1: Option<&[u8]>,
    str2: Option<&[u8]>,
    str3: Option<&[u8]>,
    int1: c_int,
    msg: &[u8],
) {
    unsafe {
        if ctxt.is_null() {
            let r = Raised { domain, code, level, message: msg, file: None, line: 0, col: 0, str1, str2, str3, int1, ctxt: null_mut(), node: node as *mut c_void };
            raise(&r, None, null_mut(), None, null_mut());
            return;
        }
        let c = &mut *ctxt;
        if code == ERR_NO_MEMORY {
            c.errNo = ERR_NO_MEMORY;
            c.wellFormed = 0;
            c.disableSAX = 2;
        } else {
            if c.disableSAX > 1 {
                return;
            }
            if catastrophic(&c.lastError) {
                return;
            }
            if level == ERR_WARNING {
                if c.nbWarnings >= 100 {
                    return;
                }
                c.nbWarnings += 1;
            } else {
                if xmlIsCatastrophicError(level, code) != 0 || code == ERR_RESOURCE_LIMIT || code == ERR_ENTITY_LOOP {
                    c.disableSAX = 2;
                } else {
                    if c.nbErrors >= 100 && (level < ERR_FATAL || c.wellFormed == 0) {
                        return;
                    }
                    if level == ERR_FATAL && c.recovery == 0 {
                        c.disableSAX = 1;
                    }
                }
                if level == ERR_FATAL {
                    c.wellFormed = 0;
                }
                c.errNo = code;
                c.nbErrors = c.nbErrors.saturating_add(1);
            }
        }
        let mut schannel: StructuredErrorF = None;
        let mut channel: MsgF = None;
        let mut data: *mut c_void = null_mut();
        if c.options & PARSE_NOERROR == 0 && (level != ERR_WARNING || c.options & PARSE_NOWARNING == 0) {
            let sax = c.sax;
            if c.errorHandler.is_some() {
                schannel = c.errorHandler;
                data = c.errorCtxt;
            } else if !sax.is_null() && (*sax).initialized == SAX2_MAGIC && (*sax).serror.is_some() {
                schannel = (*sax).serror;
                data = c.userData;
            } else if domain == FROM_VALID || domain == FROM_DTD {
                channel = if level == ERR_WARNING { c.vctxt.warning } else { c.vctxt.error };
                data = c.vctxt.userData;
            } else if !sax.is_null() {
                channel = if level == ERR_WARNING { (*sax).warning } else { (*sax).error };
                data = c.userData;
            }
        }
        let (mut file, mut line, mut col) = (None, 0, 0);
        if !c.input.is_null() {
            let mut input = c.input;
            if (*input).filename.is_null() && c.inputNr > 1 {
                input = *c.inputTab.add(c.inputNr as usize - 2);
            }
            file = copt((*input).filename as *const XChar);
            line = (*input).line;
            col = (*input).col;
        }
        if (*globals()).get_warnings == 0 && level == ERR_WARNING {
            return;
        }
        let r = Raised { domain, code, level, message: msg, file, line, col, str1, str2, str3, int1, ctxt: ctxt as *mut c_void, node: node as *mut c_void };
        fill_error(&r, &mut c.lastError);
        let g = globals();
        copy_error(&c.lastError, &mut (*g).last_error);
        let e = &c.lastError as *const XmlError;
        if let Some(s) = schannel {
            s(data, e);
        } else if let Some(s) = (*g).structured {
            s((*g).structured_ctx, e);
        } else if let Some(ch) = channel {
            let p = ch as usize;
            let legacy = [
                xmlParserError as *const () as usize,
                xmlParserWarning as *const () as usize,
                xmlParserValidityError as *const () as usize,
                xmlParserValidityWarning as *const () as usize,
                xmlGenericErrorDefaultFunc as *const () as usize,
            ];
            if legacy.contains(&p) {
                let genf = (*g).generic_error.unwrap_or(as_msg_fn(xmlGenericErrorDefaultFunc));
                format_error(&*e, genf, (*g).generic_ctx);
            } else {
                ch(data, c"%s".as_ptr(), (*e).message);
            }
        }
    }
}

/// The text around the input's position, for an error message: the line
/// (at most 80 bytes of it) and the column in it (xmlParserInputGetWindow).
pub fn window(input: &ParserInput) -> (Vec<u8>, usize) {
    if input.base.is_null() || input.cur.is_null() {
        return (Vec::new(), 0);
    }
    let size = 80usize;
    unsafe {
        let base = input.base;
        let end = input.end;
        let at = |p: *const XChar| if p < end { *p } else { 0 };
        let mut cur = input.cur;
        while cur > base && (at(cur) == b'\n' || at(cur) == b'\r') {
            cur = cur.sub(1);
        }
        let mut n = 0;
        while n < size && cur > base && at(cur) != b'\n' && at(cur) != b'\r' {
            cur = cur.sub(1);
            n += 1;
        }
        if n > 0 && (at(cur) == b'\n' || at(cur) == b'\r') {
            cur = cur.add(1);
        } else {
            while cur < input.cur && at(cur) & 0xC0 == 0x80 {
                cur = cur.add(1);
            }
        }
        let mut col = input.cur.offset_from(cur).max(0) as usize;
        let start = cur;
        n = 0;
        while cur < end && at(cur) != 0 && at(cur) != b'\n' && at(cur) != b'\r' {
            let rest = std::slice::from_raw_parts(cur, end.offset_from(cur) as usize);
            let len = match crate::chars::ex_cp_at_hi(rest, 0) {
                _ if rest[0] < 0x80 => 1,
                Some((_, l)) => l,
                None => break,
            };
            if n + len > size {
                break;
            }
            cur = cur.add(len);
            n += len;
        }
        if col >= n {
            col = if n < size { n } else { size - 1 };
        }
        (std::slice::from_raw_parts(start, n).to_vec(), col)
    }
}

/// `xmlErrString`.
pub fn message_for(code: c_int) -> &'static CStr {
    match code {
        0 => c"Unregistered error message",
        1 => c"internal error",
        4 => c"Document is empty",
        5 => c"Extra content at the end of the document",
        6 => c"CharRef: invalid hexadecimal value",
        7 => c"CharRef: invalid decimal value",
        8 => c"CharRef: invalid value",
        9 => c"Invalid character",
        18 => c"PEReference at end of document",
        19 => c"PEReference in prolog",
        20 => c"PEReference in epilog",
        21 => c"PEReference: forbidden within markup decl in internal subset",
        23 => c"EntityRef: expecting ';'",
        24 => c"PEReference: no name",
        25 => c"PEReference: expecting ';'",
        32 => c"Unsupported encoding",
        33 => c"String not started expecting ' or \"",
        34 => c"String not closed expecting \" or '",
        36 => c"EntityValue: \" or ' expected",
        37 => c"EntityValue: \" or ' expected",
        38 => c"Unescaped '<' not allowed in attributes values",
        39 => c"AttValue: \" or ' expected",
        43 => c"SystemLiteral \" or ' expected",
        44 => c"Unfinished System or Public ID \" or ' expected",
        46 => c"xmlParsePI : no target name",
        48 => c"NOTATION: Name expected here",
        49 => c"'>' required to close NOTATION declaration",
        50 => c"'(' required to start ATTLIST enumeration",
        51 => c"')' required to finish ATTLIST enumeration",
        52 => c"MixedContentDecl : '|' or ')*' expected",
        54 => c"ContentDecl : Name or '(' expected",
        55 => c"ContentDecl : ',' '|' or ')' expected",
        56 => c"Text declaration '<?xml' required",
        57 => c"parsing XML declaration: '?>' expected",
        59 => c"XML conditional section not closed",
        60 => c"Content error in the external subset",
        61 => c"DOCTYPE improperly terminated",
        62 => c"Sequence ']]>' not allowed in content",
        64 => c"Invalid PI name",
        67 => c"NmToken expected in ATTLIST enumeration",
        69 => c"MixedContentDecl : '#PCDATA' expected",
        70 => c"SYSTEM or PUBLIC, the URI is missing",
        71 => c"PUBLIC, the Public Identifier is missing",
        73 => c"expected '>'",
        74 => c"EndTag: '</' not found",
        75 => c"expected '='",
        78 => c"standalone accepts only 'yes' or 'no'",
        79 => c"Invalid XML encoding name",
        80 => c"Comment must not contain '--' (double-hyphen)",
        81 => c"Invalid bytes in character encoding",
        82 => c"external parsed entities cannot be standalone",
        83 => c"XML conditional section '[' expected",
        84 => c"Entity value required",
        85 => c"chunk is not well balanced",
        86 => c"extra content at the end of well balanced chunk",
        88 => c"PEReferences forbidden in internal subset",
        89 => c"Detected an entity reference loop",
        92 => c"Fragment not allowed",
        95 => c"conditional section INCLUDE or IGNORE keyword expected",
        96 => c"Malformed declaration expecting version",
        110 => c"Name too long",
        114 => c"Resource limit exceeded",
        115 => c"Invalid argument",
        116 => c"Out of system resources",
        117 => c"Invalid redeclaration of predefined entity",
        118 => c"Content error in the internal subset",
        1500 => c"Unknown IO error",
        1501 => c"Permission denied",
        1502 => c"Resource temporarily unavailable",
        1503 => c"Bad file descriptor",
        1504 => c"Bad message",
        1505 => c"Resource busy",
        1506 => c"Operation canceled",
        1507 => c"No child processes",
        1508 => c"Resource deadlock avoided",
        1509 => c"Domain error",
        1510 => c"File exists",
        1511 => c"Bad address",
        1512 => c"File too large",
        1513 => c"Operation in progress",
        1514 => c"Interrupted function call",
        1515 => c"Invalid argument",
        1516 => c"Input/output error",
        1517 => c"Is a directory",
        1518 => c"Too many open files",
        1519 => c"Too many links",
        1520 => c"Inappropriate message buffer length",
        1521 => c"Filename too long",
        1522 => c"Too many open files in system",
        1523 => c"No such device",
        1524 => c"No such file or directory",
        1525 => c"Exec format error",
        1526 => c"No locks available",
        1527 => c"Not enough space",
        1528 => c"No space left on device",
        1529 => c"Function not implemented",
        1530 => c"Not a directory",
        1531 => c"Directory not empty",
        1532 => c"Not supported",
        1533 => c"Inappropriate I/O control operation",
        1534 => c"No such device or address",
        1535 => c"Operation not permitted",
        1536 => c"Broken pipe",
        1537 => c"Result too large",
        1538 => c"Read-only file system",
        1539 => c"Invalid seek",
        1540 => c"No such process",
        1541 => c"Operation timed out",
        1542 => c"Improper link",
        1543 => c"Attempt to load network entity",
        1544 => c"encoder error",
        1545 => c"flush error",
        1546 => c"write error",
        1547 => c"no input",
        1548 => c"buffer full",
        1549 => c"loading error",
        1550 => c"not a socket",
        1551 => c"already connected",
        1552 => c"connection refused",
        1553 => c"unreachable network",
        1554 => c"address in use",
        1555 => c"already in use",
        1556 => c"unknown address family",
        1557 => c"unsupported protocol",
        _ => c"Unregistered error message",
    }
}

// --- the walk ----------------------------------------------------------------------

const SAX_COMPAT: &[u8] = b"SAX compatibility mode document";

/// The handler, if SAX events are to be made.
unsafe fn handler<'a>(ctxt: *mut ParserCtxt) -> Option<&'a SaxHandler> {
    unsafe { if (*ctxt).sax.is_null() || (*ctxt).disableSAX != 0 { None } else { Some(&*(*ctxt).sax) } }
}

unsafe fn dict(ctxt: *mut ParserCtxt, s: &[u8]) -> *const XChar {
    unsafe { xmlDictLookup((*ctxt).dict, s.as_ptr(), s.len() as c_int) }
}

unsafe fn ns_err(ctxt: *mut ParserCtxt, code: c_int, msg: &[u8], s1: Option<&[u8]>, s2: Option<&[u8]>, s3: Option<&[u8]>) {
    unsafe {
        (*ctxt).nsWellFormed = 0;
        ctx_err(ctxt, null_mut(), FROM_NAMESPACE, code, ERR_ERROR, s1, s2, s3, 0, msg);
    }
}

unsafe fn ns_warn(ctxt: *mut ParserCtxt, code: c_int, msg: &[u8], s1: Option<&[u8]>, s2: Option<&[u8]>) {
    unsafe { ctx_err(ctxt, null_mut(), FROM_NAMESPACE, code, ERR_WARNING, s1, s2, None, 0, msg) };
}

unsafe fn fatal(ctxt: *mut ParserCtxt, code: c_int, msg: &[u8], s1: Option<&[u8]>) {
    unsafe { ctx_err(ctxt, null_mut(), FROM_PARSER, code, ERR_FATAL, s1, None, None, 0, msg) };
}

unsafe fn warning(ctxt: *mut ParserCtxt, code: c_int, msg: &[u8], s1: Option<&[u8]>, s2: Option<&[u8]>) {
    unsafe { ctx_err(ctxt, null_mut(), FROM_PARSER, code, ERR_WARNING, s1, s2, None, 0, msg) };
}

fn cat(parts: &[&[u8]]) -> Vec<u8> {
    parts.concat()
}

fn is_blank(c: u8) -> bool {
    matches!(c, 0x20 | 0x09 | 0x0A | 0x0D)
}

/// The bytes of libxml2's fast path for character data.
fn plain_char(c: u8) -> bool {
    c == 0x09 || (0x20..0x80).contains(&c) && c != b'<' && c != b'&' && c != b']'
}

/// `text` with line ends normalized (CRLF and CR to LF).
fn eol(text: &[u8]) -> Cow<'_, [u8]> {
    if !text.contains(&b'\r') {
        return Cow::Borrowed(text);
    }
    let mut out = Vec::with_capacity(text.len());
    let mut i = 0;
    while i < text.len() {
        if text[i] == b'\r' {
            out.push(b'\n');
            if text.get(i + 1) == Some(&b'\n') {
                i += 1;
            }
        } else {
            out.push(text[i]);
        }
        i += 1;
    }
    Cow::Owned(out)
}

fn utf8_of(cp: u32) -> Vec<u8> {
    char::from_u32(cp).map(|c| c.to_string().into_bytes()).unwrap_or_default()
}

/// A character reference at `s[i..]` ("&#...;"): its character and length.
fn char_ref(s: &[u8], i: usize) -> Option<(u32, usize)> {
    let end = i + s[i..].iter().position(|&c| c == b';')?;
    let body = &s[i + 2..end];
    let v = if let Some(h) = body.strip_prefix(b"x") {
        u32::from_str_radix(std::str::from_utf8(h).ok()?, 16).ok()?
    } else {
        std::str::from_utf8(body).ok()?.parse().ok()?
    };
    Some((v, end + 1 - i))
}

/// An entity reference at `s[i..]` ("&name;"): the name and the length.
fn ent_ref(s: &[u8], i: usize) -> Option<(&[u8], usize)> {
    let end = i + s[i..].iter().position(|&c| c == b';')?;
    Some((&s[i + 1..end], end + 1 - i))
}

/// An entity value as libxml2 keeps it (`xmlParseEntityValue`): character
/// references replaced, everything else as written.
fn entity_value(raw: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(raw.len());
    let mut i = 0;
    while i < raw.len() {
        if raw[i] == b'&' && raw.get(i + 1) == Some(&b'#') {
            if let Some((v, l)) = char_ref(raw, i) {
                out.extend_from_slice(&utf8_of(v));
                i += l;
                continue;
            }
        }
        out.push(raw[i]);
        i += 1;
    }
    out
}

/// A QName split as `xmlParseQNameHashed` does: (prefix, local).
fn qname(name: &[u8]) -> (Option<&[u8]>, &[u8]) {
    match name.iter().position(|&c| c == b':') {
        Some(k) if k > 0 && k + 1 < name.len() && !name[k + 1..].contains(&b':') => (Some(&name[..k]), &name[k + 1..]),
        _ => (None, name),
    }
}

/// Whether `s` parses as a URI reference (`xmlParseURISafe`), and whether
/// it has a scheme.
fn uri_check(s: &[u8]) -> (bool, bool) {
    let mut ok = true;
    let mut i = 0;
    while i < s.len() {
        let c = s[i];
        let allowed = c.is_ascii_alphanumeric() || b"-._~:/?#[]@!$&'()*+,;=".contains(&c);
        if c == b'%' {
            if !(i + 2 < s.len() + 0 && s.get(i + 1).is_some_and(|x| x.is_ascii_hexdigit()) && s.get(i + 2).is_some_and(|x| x.is_ascii_hexdigit())) {
                ok = false;
            }
        } else if !allowed {
            ok = false;
        }
        i += 1;
    }
    let scheme = match s.iter().position(|&c| c == b':') {
        Some(k) if k > 0 => s[0].is_ascii_alphabetic() && s[..k].iter().all(|c| c.is_ascii_alphanumeric() || b"+-.".contains(c)),
        _ => false,
    };
    (ok, scheme)
}

/// An attribute value as libxml2 passes it: in the input (`valueend` on
/// a byte that is not NUL), or made (`valueend` on its NUL).
enum Val<'a> {
    In(&'a [u8]),
    Made(Vec<u8>),
}

/// A defaulted attribute: its name and its value as made (NUL-terminated).
struct DefAttr {
    name: Vec<u8>,
    value: Vec<u8>,
}

/// What the DTD gave: attribute types and defaults, by element and
/// attribute (first declaration binding).
#[derive(Default)]
struct DtdInfo {
    types: FastMap<(Vec<u8>, Vec<u8>), c_int>,
    defaults: FastMap<Vec<u8>, Vec<DefAttr>>,
}

/// An open element: what its end tag needs.
struct Open {
    local: *const XChar,
    prefix: *const XChar,
    uri: *const XChar,
    name: *const XChar,
    nb_ns: usize,
}

struct Walk<'d> {
    ctxt: *mut ParserCtxt,
    doc: &'d Document<'d>,
    text: &'d [u8],
    dtd: DtdInfo,
    /// Each entity's expanded size, once known.
    sizes: Vec<Option<u64>>,
    /// Bytes the walk has passed in the document, for the amplification
    /// check.
    consumed: usize,
    /// Pushed (`xmlParseChunk`): the text is the push parser's window,
    /// which begins at `pbase` in the input.
    push: bool,
    pbase: usize,
    /// Where the document type declaration ends, when the text goes on
    /// past it.
    dt_end: Option<usize>,
    /// Pushed: character data (or, `pend_cdata`, a CDATA section) read and
    /// not yet reported, as libxml2's push parser waits for its end; and
    /// where in the text it ends.
    pend: Vec<u8>,
    pend_cdata: bool,
    pend_end: usize,
}

const ENT_VALIDATED: c_int = 4;

impl<'d> Walk<'d> {
    fn new(ctxt: *mut ParserCtxt, doc: &'d Document<'d>) -> Walk<'d> {
        let n = doc.dtd.ents.len();
        Walk {
            ctxt,
            doc,
            text: doc.text(),
            dtd: DtdInfo::default(),
            sizes: vec![None; n],
            consumed: 0,
            push: false,
            pbase: 0,
            dt_end: None,
            pend: Vec::new(),
            pend_cdata: false,
            pend_end: 0,
        }
    }

    /// Moves the input's position to `off` in the document's text.
    unsafe fn at(&mut self, off: usize) {
        unsafe {
            let ctxt = self.ctxt;
            let input = (*ctxt).input;
            if input.is_null() {
                return;
            }
            let off = off.min(self.text.len());
            self.consumed = self.consumed.max(self.pbase + off);
            let (line, col) = count_lines(st(ctxt), self.text, off);
            (*input).cur = self.text.as_ptr().add(off);
            (*input).line = line;
            (*input).col = col;
        }
    }

    fn buf(&self, src: Src) -> &'d [u8] {
        self.doc.buf(src)
    }
}

/// The line and column at `off` in `text`, counted on from the last place
/// asked for (`State::at`).
fn count_lines(s: &mut State, text: &[u8], off: usize) -> (c_int, c_int) {
    {
        {
            let (mut o, mut line, mut col) = s.at;
            if off < o {
                (o, line, col) = (0, 1, 1);
            }
            let run = &text[o..off];
            if run.len() < 32 {
                for &c in run {
                    if c == b'\n' {
                        line += 1;
                        col = 1;
                    } else {
                        col += (c & 0xC0 != 0x80) as c_int;
                    }
                }
            } else {
                // Long runs eight bytes at a time.
                match count_newlines(run) {
                    0 => col += (run.len() - count_continuations(run)) as c_int,
                    nl => {
                        line += nl as c_int;
                        let last = run.iter().rposition(|&c| c == b'\n').unwrap_or(0);
                        let tail = &run[last + 1..];
                        col = 1 + (tail.len() - count_continuations(tail)) as c_int;
                    }
                }
            }
            s.at = (off, line, col);
            (line, col)
        }
    }
}

impl<'d> Walk<'d> {

    fn toks(&self, src: Src) -> &'d [Tok] {
        self.doc.toks(src)
    }

    // --- entities -----------------------------------------------------------------

    /// `xmlHandleUndeclaredEntity`.
    unsafe fn undeclared(&mut self, name: &[u8]) {
        unsafe {
            let c = self.ctxt;
            let msg = cat(&[b"Entity '", name, b"' not defined\n"]);
            if (*c).standalone == 1 || ((*c).hasExternalSubset == 0 && (*c).hasPErefs == 0) {
                fatal(c, ERR_UNDECLARED_ENTITY, &msg, Some(name));
            } else if (*c).validate != 0 {
                (*c).valid = 0;
                ctx_err(c, null_mut(), FROM_DTD, ERR_UNDECLARED_ENTITY, ERR_ERROR, Some(name), None, None, 0, &msg);
            } else if (*c).loadsubset & !SKIP_IDS != 0 || ((*c).replaceEntities != 0 && (*c).options & PARSE_NO_XXE == 0) {
                ctx_err(c, null_mut(), FROM_PARSER, WAR_UNDECLARED_ENTITY, ERR_ERROR, Some(name), None, None, 0, &msg);
            } else {
                warning(c, WAR_UNDECLARED_ENTITY, &msg, Some(name), None);
            }
            (*c).valid = 0;
        }
    }

    /// `xmlLookupGeneralEntity`: through the handler.
    unsafe fn lookup(&mut self, name: &[u8]) -> *mut Entity {
        unsafe {
            let c = self.ctxt;
            let n = dict(c, name);
            let oldsax = (*c).options & PARSE_OLDSAX != 0;
            if !oldsax {
                let e = xmlGetPredefinedEntity(n);
                if !e.is_null() {
                    return e;
                }
            }
            let mut ent = null_mut();
            if !(*c).sax.is_null() {
                if let Some(f) = (*(*c).sax).getEntity {
                    ent = f((*c).userData, n);
                }
                if (*c).wellFormed == 1 && ent.is_null() && oldsax {
                    ent = xmlGetPredefinedEntity(n);
                }
                if (*c).wellFormed == 1 && ent.is_null() && (*c).userData == c as *mut c_void {
                    ent = xmlSAX2GetEntity(c as Ctx, n);
                }
            }
            if ent.is_null() {
                self.undeclared(name);
            }
            ent
        }
    }

    /// The index of the internal entity `name` in the document's DTD.
    fn ent_index(&self, name: &[u8]) -> Option<usize> {
        let env = self.doc.env();
        let j = crate::lex::ex_find_ent(&env, self.doc.dtd.ents.len(), name, 0, name.len())?;
        (self.doc.dtd.ents[j].kind == 0).then_some(j)
    }

    /// The size of entity `k` with its references expanded.
    fn size_of(&mut self, k: usize, depth: usize) -> u64 {
        if let Some(s) = self.sizes[k] {
            return s;
        }
        if depth > 40 {
            return 0;
        }
        let rt = &self.doc.dtd.rts[k];
        let mut total = rt.len() as u64;
        let mut i = 0;
        while i < rt.len() {
            if rt[i] == b'&' && rt.get(i + 1) != Some(&b'#') {
                if let Some((name, l)) = ent_ref(rt, i) {
                    if let Some(j) = self.ent_index(name) {
                        total = total.saturating_add(self.size_of(j, depth + 1)).saturating_add(20);
                    }
                    i += l;
                    continue;
                }
            }
            i += 1;
        }
        self.sizes[k] = Some(total);
        total
    }

    /// `xmlParserEntityCheck` for a copy of `extra` bytes: false, after a
    /// fatal error, if expansion has grown too far past the input.
    unsafe fn amplification(&mut self, extra: u64) -> bool {
        unsafe {
            let c = self.ctxt;
            (*c).sizeentcopy = (*c).sizeentcopy.saturating_add(extra as c_ulong).saturating_add(20);
            let total = (*c).sizeentcopy as u64;
            let ampl = if (*c).maxAmpl == 0 { 5 } else { (*c).maxAmpl } as u64;
            if total > 1_000_000 && total / ampl > self.consumed as u64 {
                fatal(c, ERR_RESOURCE_LIMIT, b"Maximum entity amplification factor exceeded, see xmlCtxtSetMaxAmplification.\n", None);
                (*c).disableSAX = 2;
                return false;
            }
            true
        }
    }

    // --- attribute values ---------------------------------------------------------------

    /// `xmlCheckEntityInAttValue`: looks up the references in an entity's
    /// value, once.
    unsafe fn check_ent_in_att(&mut self, pent: *mut Entity, depth: usize) {
        unsafe {
            let c = self.ctxt;
            if depth > 20 {
                fatal(c, ERR_RESOURCE_LIMIT, b"Maximum entity nesting depth exceeded", None);
                return;
            }
            if (*pent).flags & ENT_EXPANDING != 0 {
                fatal(c, ERR_ENTITY_LOOP, b"Detected an entity reference loop\n", None);
                return;
            }
            let flags = if (*c).inSubset == 0 { ENT_CHECKED | ENT_VALIDATED } else { ENT_VALIDATED };
            let s = cbytes((*pent).content).to_vec();
            let mut i = 0;
            while i < s.len() && (*c).disableSAX < 2 {
                if s[i] == b'&' && s.get(i + 1) != Some(&b'#') {
                    if let Some((name, l)) = ent_ref(&s, i) {
                        let ent = self.lookup(name);
                        if !ent.is_null() && (*ent).etype != INTERNAL_PREDEFINED_ENTITY && (*ent).flags & flags != flags {
                            (*pent).flags |= ENT_EXPANDING;
                            self.check_ent_in_att(ent, depth + 1);
                            (*pent).flags &= !ENT_EXPANDING;
                        }
                        i += l;
                        continue;
                    }
                }
                i += 1;
            }
            (*pent).flags |= flags;
        }
    }

    /// `xmlExpandEntityInAttValue`: an entity's value, expanded, into `out`.
    unsafe fn expand_in_att(&mut self, out: &mut Vec<u8>, pent: *mut Entity, normalize: bool, in_space: &mut bool, depth: usize) {
        unsafe {
            let c = self.ctxt;
            if depth > 20 {
                fatal(c, ERR_RESOURCE_LIMIT, b"Maximum entity nesting depth exceeded", None);
                return;
            }
            if (*pent).flags & ENT_EXPANDING != 0 {
                fatal(c, ERR_ENTITY_LOOP, b"Detected an entity reference loop\n", None);
                return;
            }
            if out.len() > 10_000_000 && (*c).options & PARSE_HUGE == 0 {
                fatal(c, ERR_RESOURCE_LIMIT, b"Maximum entity amplification factor exceeded, see xmlCtxtSetMaxAmplification.\n", None);
                (*c).disableSAX = 2;
                return;
            }
            (*pent).flags |= ENT_EXPANDING;
            let s = cbytes((*pent).content).to_vec();
            let mut i = 0;
            while i < s.len() && (*c).disableSAX < 2 {
                let ch = s[i];
                if ch != b'&' {
                    if ch <= 0x20 {
                        if !(normalize && *in_space) {
                            out.push(b' ');
                        }
                        *in_space = true;
                    } else {
                        out.push(ch);
                        *in_space = false;
                    }
                    i += 1;
                } else if s.get(i + 1) == Some(&b'#') {
                    match char_ref(&s, i) {
                        Some((v, l)) => {
                            if v == 0x20 {
                                if !(normalize && *in_space) {
                                    out.push(b' ');
                                }
                                *in_space = true;
                            } else {
                                out.extend_from_slice(&utf8_of(v));
                                *in_space = false;
                            }
                            i += l;
                        }
                        None => break,
                    }
                } else {
                    let Some((name, l)) = ent_ref(&s, i) else { break };
                    let name = name.to_vec();
                    i += l;
                    let ent = self.lookup(&name);
                    if ent.is_null() {
                        continue;
                    }
                    if (*ent).etype == INTERNAL_PREDEFINED_ENTITY {
                        out.extend_from_slice(cbytes((*ent).content));
                        *in_space = false;
                    } else {
                        self.expand_in_att(out, ent, normalize, in_space, depth + 1);
                    }
                }
            }
            (*pent).flags &= !ENT_EXPANDING;
        }
    }

    /// `xmlParseAttValueInternal` over the raw value `raw` (the text
    /// between the quotes).
    #[allow(unused_assignments)] // a macro resets state that its last use leaves unread
    unsafe fn att_value<'r>(&mut self, raw: &'r [u8], normalize: bool, is_ns: bool) -> Val<'r> {
        unsafe {
            let c = self.ctxt;
            let replace = (*c).replaceEntities != 0 || is_ns;
            // xmlParseAttValueInternal: runs of the input are kept as a chunk
            // and copied out only once something else must be added; a
            // value that never needed a copy is passed in the input.
            let ent_flags = if (*c).inSubset == 0 { ENT_CHECKED | ENT_VALIDATED } else { ENT_VALIDATED };
            let mut out: Vec<u8> = Vec::new();
            let (mut cs, mut cl) = (0usize, 0usize);
            macro_rules! flush {
                () => {
                    if cl > 0 {
                        out.extend_from_slice(&raw[cs..cs + cl]);
                        cl = 0;
                    }
                };
            }
            macro_rules! take {
                ($i:expr) => {
                    if cl == 0 {
                        cs = $i;
                    }
                    cl += 1;
                };
            }
            let mut in_space = true;
            let mut i = 0;
            while i < raw.len() {
                let ch = raw[i];
                if ch >= 0x80 || (ch > 0x20 && ch != b'&') {
                    take!(i);
                    in_space = false;
                    i += 1;
                } else if ch != b'&' {
                    if normalize && in_space {
                        flush!();
                    } else if ch < 0x20 {
                        flush!();
                        out.push(b' ');
                    } else {
                        take!(i);
                    }
                    in_space = true;
                    if ch == 0x0D && raw.get(i + 1) == Some(&0x0A) {
                        i += 1;
                    }
                    i += 1;
                } else if raw.get(i + 1) == Some(&b'#') {
                    flush!();
                    let Some((v, l)) = char_ref(raw, i) else { break };
                    i += l;
                    if v == u32::from(b'&') && !replace {
                        out.extend_from_slice(b"&#38;");
                        in_space = false;
                    } else if v == 0x20 {
                        if !(normalize && in_space) {
                            out.push(b' ');
                        }
                        in_space = true;
                    } else {
                        out.extend_from_slice(&utf8_of(v));
                        in_space = false;
                    }
                } else {
                    flush!();
                    let Some((name, l)) = ent_ref(raw, i) else { break };
                    i += l;
                    let ent = self.lookup(name);
                    if ent.is_null() {
                        continue;
                    }
                    if (*ent).etype == INTERNAL_PREDEFINED_ENTITY {
                        let v = cbytes((*ent).content);
                        if v.first() == Some(&b'&') && !replace {
                            out.extend_from_slice(b"&#38;");
                        } else {
                            out.extend_from_slice(v);
                        }
                        in_space = false;
                    } else if replace {
                        self.expand_in_att(&mut out, ent, normalize, &mut in_space, 1);
                    } else {
                        if (*ent).flags & ent_flags != ent_flags {
                            self.check_ent_in_att(ent, 1);
                        }
                        out.push(b'&');
                        out.extend_from_slice(cbytes((*ent).name));
                        out.push(b';');
                        in_space = false;
                    }
                }
            }
            if out.is_empty() {
                // Nothing copied: the chunk, in the input (at the closing
                // quote when it is empty).
                if cl == 0 {
                    cs = raw.len();
                }
                if normalize && in_space && cl > 0 {
                    cl -= 1;
                }
                return Val::In(&raw[cs..cs + cl]);
            }
            flush!();
            if normalize && in_space && !out.is_empty() {
                out.pop();
            }
            Val::Made(out)
        }
    }
}

// --- content models (xmlParseElementContentDecl) ---------------------------------

struct Spec<'a> {
    s: &'a [u8],
    i: usize,
    doc: *mut Doc,
}

impl Spec<'_> {
    fn ws(&mut self) {
        while self.i < self.s.len() && is_blank(self.s[self.i]) {
            self.i += 1;
        }
    }

    fn peek(&self) -> u8 {
        self.s.get(self.i).copied().unwrap_or(0)
    }

    fn name(&mut self) -> Vec<u8> {
        let a = self.i;
        while self.i < self.s.len() && !is_blank(self.s[self.i]) && !b"()|,?*+>".contains(&self.s[self.i]) {
            self.i += 1;
        }
        let mut v = self.s[a..self.i].to_vec();
        v.push(0);
        v
    }

    unsafe fn new(&self, name: Option<&[u8]>, ty: c_int) -> *mut ElementContent {
        unsafe { xmlNewDocElementContent(self.doc, name.map_or(null(), |n| n.as_ptr()), ty) }
    }

    fn ocur(&mut self) -> c_int {
        match self.peek() {
            b'?' => {
                self.i += 1;
                CONTENT_OPT
            }
            b'*' => {
                self.i += 1;
                CONTENT_MULT
            }
            b'+' => {
                self.i += 1;
                CONTENT_PLUS
            }
            _ => CONTENT_ONCE,
        }
    }

    /// After "(#PCDATA".
    unsafe fn mixed(&mut self) -> *mut ElementContent {
        unsafe {
            self.ws();
            if self.peek() == b')' {
                self.i += 1;
                let ret = self.new(None, CONTENT_PCDATA);
                if self.peek() == b'*' {
                    (*ret).ocur = CONTENT_MULT;
                    self.i += 1;
                }
                return ret;
            }
            let mut ret = self.new(None, CONTENT_PCDATA);
            let mut cur = ret;
            let mut elem: Option<Vec<u8>> = None;
            while self.peek() == b'|' {
                self.i += 1;
                let n = self.new(None, CONTENT_OR);
                match &elem {
                    None => {
                        (*n).c1 = cur;
                        (*cur).parent = n;
                        ret = n;
                        cur = n;
                    }
                    Some(e) => {
                        (*cur).c2 = n;
                        (*n).parent = cur;
                        (*n).c1 = self.new(Some(e), CONTENT_ELEMENT);
                        (*(*n).c1).parent = n;
                        cur = n;
                    }
                }
                self.ws();
                elem = Some(self.name());
                self.ws();
            }
            if let Some(e) = &elem {
                (*cur).c2 = self.new(Some(e), CONTENT_ELEMENT);
                (*(*cur).c2).parent = cur;
            }
            (*ret).ocur = CONTENT_MULT;
            self.i += 2;
            ret
        }
    }

    /// After a '(' of element content.
    #[allow(unused_assignments)] // the loop resets `last` as xmlParseElementChildrenContentDecl does
    unsafe fn children(&mut self, depth: usize) -> *mut ElementContent {
        unsafe {
            let (mut ret, mut cur);
            let mut last: *mut ElementContent = null_mut();
            let mut ty = 0u8;
            self.ws();
            if self.peek() == b'(' {
                self.i += 1;
                ret = self.children(depth + 1);
                cur = ret;
            } else {
                let e = self.name();
                ret = self.new(Some(&e), CONTENT_ELEMENT);
                cur = ret;
                (*cur).ocur = self.ocur();
            }
            loop {
                self.ws();
                let ch = self.peek();
                if ch == b')' || ch == 0 {
                    break;
                }
                if ch == b',' || ch == b'|' {
                    if ty == 0 {
                        ty = ch;
                    }
                    self.i += 1;
                    let op = self.new(None, if ch == b',' { CONTENT_SEQ } else { CONTENT_OR });
                    if last.is_null() {
                        (*op).c1 = ret;
                        (*ret).parent = op;
                        ret = op;
                        cur = op;
                    } else {
                        (*cur).c2 = op;
                        (*op).parent = cur;
                        (*op).c1 = last;
                        (*last).parent = op;
                        cur = op;
                        last = null_mut();
                    }
                } else {
                    break;
                }
                self.ws();
                if self.peek() == b'(' {
                    self.i += 1;
                    last = self.children(depth + 1);
                } else {
                    let e = self.name();
                    last = self.new(Some(&e), CONTENT_ELEMENT);
                    (*last).ocur = self.ocur();
                }
            }
            if !cur.is_null() && !last.is_null() {
                (*cur).c2 = last;
                (*last).parent = cur;
            }
            self.i += 1;
            match self.peek() {
                b'?' => {
                    (*ret).ocur = if matches!((*ret).ocur, CONTENT_PLUS | CONTENT_MULT) { CONTENT_MULT } else { CONTENT_OPT };
                    self.i += 1;
                }
                b'*' => {
                    (*ret).ocur = CONTENT_MULT;
                    let mut c = ret;
                    while !c.is_null() && (*c).type_ == CONTENT_OR {
                        for k in [(*c).c1, (*c).c2] {
                            if !k.is_null() && matches!((*k).ocur, CONTENT_OPT | CONTENT_MULT) {
                                (*k).ocur = CONTENT_ONCE;
                            }
                        }
                        c = (*c).c2;
                    }
                    self.i += 1;
                }
                b'+' => {
                    (*ret).ocur = if matches!((*ret).ocur, CONTENT_OPT | CONTENT_MULT) { CONTENT_MULT } else { CONTENT_PLUS };
                    let mut found = false;
                    let mut c = cur;
                    while !c.is_null() && (*c).type_ == CONTENT_OR {
                        for k in [(*c).c1, (*c).c2] {
                            if !k.is_null() && matches!((*k).ocur, CONTENT_OPT | CONTENT_MULT) {
                                (*k).ocur = CONTENT_ONCE;
                                found = true;
                            }
                        }
                        c = (*c).c2;
                    }
                    if found {
                        (*ret).ocur = CONTENT_MULT;
                    }
                    self.i += 1;
                }
                _ => {}
            }
            ret
        }
    }
}

/// The type and content of an element declaration, from the text after
/// its name.
unsafe fn content_spec(doc: *mut Doc, s: &[u8]) -> (c_int, *mut ElementContent) {
    unsafe {
        let mut p = Spec { s, i: 0, doc };
        p.ws();
        if s[p.i..].starts_with(b"EMPTY") {
            return (ELEMENT_TYPE_EMPTY, null_mut());
        }
        if s[p.i..].starts_with(b"ANY") {
            return (ELEMENT_TYPE_ANY, null_mut());
        }
        p.i += 1;
        p.ws();
        if s[p.i..].starts_with(b"#PCDATA") {
            p.i += 7;
            (ELEMENT_TYPE_MIXED, p.mixed())
        } else {
            (ELEMENT_TYPE_ELEMENT, p.children(1))
        }
    }
}

/// The enumeration of an attribute type ("(a|b)" or "NOTATION (a|b)"), from
/// the text after the attribute's name.
unsafe fn enumeration(s: &[u8]) -> *mut Enumeration {
    unsafe {
        let Some(open) = s.iter().position(|&c| c == b'(') else { return null_mut() };
        let close = open + s[open..].iter().position(|&c| c == b')').unwrap_or(s.len() - open);
        let mut head: *mut Enumeration = null_mut();
        let mut last: *mut Enumeration = null_mut();
        for part in s[open + 1..close].split(|&c| c == b'|') {
            let a = part.iter().position(|&c| !is_blank(c)).unwrap_or(part.len());
            let b = part.iter().rposition(|&c| !is_blank(c)).map_or(a, |e| e + 1);
            let z = nul(&part[a..b]);
            let e = xmlCreateEnumeration(z.as_ptr());
            if last.is_null() {
                head = e;
            } else {
                (*last).next = e;
            }
            last = e;
        }
        head
    }
}

impl<'d> Walk<'d> {
    // --- the prolog and the DTD ----------------------------------------------------------

    unsafe fn comment(&mut self, src: Src, t: Tok) {
        unsafe {
            let c = self.ctxt;
            if src == Src::Doc {
                self.at(t.b() + 3);
            }
            if let Some(f) = handler(c).and_then(|h| h.comment) {
                let v = nul(&eol(&self.buf(src)[t.a()..t.b()]));
                f((*c).userData, v.as_ptr());
            }
        }
    }

    unsafe fn pi(&mut self, src: Src, t: Tok, d: Tok) {
        unsafe {
            let c = self.ctxt;
            let buf = self.buf(src);
            if src == Src::Doc {
                self.at(d.b() + 2);
            }
            let target = dict(c, &buf[t.a()..t.b()]);
            if let Some(f) = handler(c).and_then(|h| h.processingInstruction) {
                if buf[t.b()..].starts_with(b"?>") {
                    f((*c).userData, target, null());
                } else {
                    let v = nul(&eol(&buf[d.a()..d.b()]));
                    f((*c).userData, target, v.as_ptr());
                }
            }
        }
    }

    /// The prolog: from the XML declaration up to the root element's start
    /// tag, whose index this returns.
    unsafe fn prolog(&mut self) -> usize {
        unsafe {
            let i = self.decl_start();
            self.prolog_from(i)
        }
    }

    /// The XML declaration, if the tokens begin with it, then
    /// startDocument; returns the index after the declaration.
    unsafe fn decl_start(&mut self) -> usize {
        unsafe {
            let c = self.ctxt;
            let toks = self.toks(Src::Doc);
            let text = self.text;
            let mut i = 0;
            // The XML declaration, then startDocument.
            if toks.first().is_some_and(|t| t.kind == Kind::XmlDecl) {
                let t = toks[0];
                (*c).standalone = -2;
                let version = &text[t.a()..t.b()];
                xfree((*c).version as *mut c_void);
                (*c).version = xstrdup(version);
                if version != b"1.0" {
                    let msg = cat(&[b"Unsupported version '", version, b"'\n"]);
                    if (*c).options & PARSE_OLD10 == 0 && version.starts_with(b"1.") {
                        warning(c, 97, &msg, Some(version), None);
                    } else {
                        fatal(c, ERR_UNKNOWN_VERSION, &msg, Some(version));
                    }
                }
                i = 1;
                if toks.get(1).is_some_and(|t| t.kind == Kind::Encoding) {
                    let e = toks[1];
                    xfree((*c).encoding as *mut c_void);
                    let declared = st(c).declared.clone();
                    (*c).encoding = xstrdup(declared.as_deref().unwrap_or(&text[e.a()..e.b()]));
                    i = 2;
                }
                (*c).standalone = match t.f {
                    1 => 1,
                    2 => 0,
                    _ => -2,
                };
                let end = text.windows(2).position(|w| w == b"?>").map_or(text.len(), |e| e + 2);
                self.at(end);
            } else {
                (*c).version = xstrdup(b"1.0");
            }
            if let Some(f) = handler(c).and_then(|h| h.startDocument) {
                f((*c).userData);
            }
            i
        }
    }

    /// The prolog from token `i` up to the root element's start tag (or
    /// the end of the tokens), whose index this returns.
    unsafe fn prolog_from(&mut self, mut i: usize) -> usize {
        unsafe {
            let toks = self.toks(Src::Doc);
            while i < toks.len() {
                let t = toks[i];
                match t.kind {
                    Kind::STag => return i,
                    Kind::Comment => self.comment(Src::Doc, t),
                    Kind::PI => {
                        self.pi(Src::Doc, t, toks[i + 1]);
                        i += 1;
                    }
                    Kind::Doctype => {
                        i = self.doctype(i);
                        continue;
                    }
                    _ => {}
                }
                i += 1;
            }
            i
        }
    }

    /// The document type declaration at `i`; returns the index after it.
    unsafe fn doctype(&mut self, i: usize) -> usize {
        unsafe {
            let c = self.ctxt;
            let toks = self.toks(Src::Doc);
            let text = self.text;
            let t = toks[i];
            (*c).inSubset = 1;
            let name = dict(c, &text[t.a()..t.b()]);
            (*c).intSubName = name;
            let mut j = i + 1;
            let (mut pubid, mut sysid) = (None, None);
            let mut last = t.b();
            while j < toks.len() && matches!(toks[j].kind, Kind::PubId | Kind::SysId) {
                let u = toks[j];
                if u.kind == Kind::PubId {
                    pubid = Some(&text[u.a()..u.b()]);
                } else {
                    sysid = Some(&text[u.a()..u.b()]);
                }
                last = u.b() + 1;
                j += 1;
            }
            if pubid.is_some() || sysid.is_some() {
                (*c).hasExternalSubset = 1;
            }
            xfree((*c).extSubURI as *mut c_void);
            xfree((*c).extSubSystem as *mut c_void);
            (*c).extSubURI = xstrdup_opt(sysid);
            (*c).extSubSystem = xstrdup_opt(pubid);
            self.at(last);
            if let Some(f) = handler(c).and_then(|h| h.internalSubset) {
                f((*c).userData, name, (*c).extSubSystem, (*c).extSubURI);
            }
            while j < toks.len() && toks[j].kind != Kind::DoctypeEnd {
                j = self.decl(j);
            }
            // The end of the declaration: '>' after the subset.
            if j < toks.len() {
                let next = toks.get(j + 1).map_or(self.dt_end.unwrap_or(text.len()), |n| n.a());
                let gt = text[..next].iter().rposition(|&ch| ch == b'>').map_or(next, |g| g + 1);
                self.at(gt);
            }
            (*c).inSubset = 2;
            if let Some(f) = handler(c).and_then(|h| h.externalSubset) {
                f((*c).userData, (*c).intSubName, (*c).extSubSystem, (*c).extSubURI);
            }
            (*c).inSubset = 0;
            j + 1
        }
    }

    /// The markup declaration (or comment, PI, PE reference) at `i` in the
    /// internal subset; returns the index after it.
    unsafe fn decl(&mut self, i: usize) -> usize {
        unsafe {
            let c = self.ctxt;
            let toks = self.toks(Src::Doc);
            let text = self.text;
            let t = toks[i];
            match t.kind {
                Kind::Comment => self.comment(Src::Doc, t),
                Kind::PI => {
                    self.pi(Src::Doc, t, toks[i + 1]);
                    return i + 2;
                }
                Kind::ElementDecl => {
                    let end = text[t.b()..].iter().position(|&ch| ch == b'>').map_or(text.len(), |e| t.b() + e);
                    self.at(end + 1);
                    let name = dict(c, &text[t.a()..t.b()]);
                    let (ty, content) = content_spec((*c).myDoc, &text[t.b()..end]);
                    if let Some(f) = handler(c).and_then(|h| h.elementDecl) {
                        f((*c).userData, name, ty, content);
                    }
                    xmlFreeDocElementContent((*c).myDoc, content);
                }
                Kind::AttlistDecl => {
                    let elem = &text[t.a()..t.b()];
                    let mut j = i + 1;
                    while j + 1 < toks.len() && toks[j].kind == Kind::AttDef {
                        self.att_def(elem, toks[j], toks[j + 1]);
                        j += 2;
                    }
                    return j;
                }
                Kind::EntityDecl => return self.entity_decl(i),
                Kind::NotationDecl => {
                    let mut j = i + 1;
                    let (mut pubid, mut sysid) = (None, None);
                    while j < toks.len() && matches!(toks[j].kind, Kind::PubId | Kind::SysId) {
                        let u = toks[j];
                        let v = nul(&text[u.a()..u.b()]);
                        if u.kind == Kind::PubId {
                            pubid = Some(v);
                        } else {
                            sysid = Some(v);
                        }
                        j += 1;
                    }
                    self.at(toks[j - 1].b() + 1);
                    let name = dict(c, &text[t.a()..t.b()]);
                    if let Some(f) = handler(c).and_then(|h| h.notationDecl) {
                        f((*c).userData, name, pubid.as_ref().map_or(null(), |v| v.as_ptr()), sysid.as_ref().map_or(null(), |v| v.as_ptr()));
                    }
                    return j;
                }
                Kind::PERef => {
                    self.at(t.b() + 1);
                    let name = &text[t.a()..t.b()];
                    (*c).hasPErefs = 1;
                    let n = dict(c, name);
                    let mut ent = null_mut();
                    if !(*c).sax.is_null() {
                        if let Some(f) = (*(*c).sax).getParameterEntity {
                            ent = f((*c).userData, n);
                        }
                    }
                    if ent.is_null() {
                        self.undeclared(name);
                    } else if (*ent).etype != INTERNAL_PARAMETER_ENTITY && (*ent).etype != EXTERNAL_PARAMETER_ENTITY {
                        let msg = cat(&[b"Internal: %", name, b"; is not a parameter entity\n"]);
                        warning(c, WAR_UNDECLARED_ENTITY, &msg, Some(name), None);
                    }
                }
                _ => {}
            }
            i + 1
        }
    }

    unsafe fn att_def(&mut self, elem: &[u8], t: Tok, d: Tok) {
        unsafe {
            let c = self.ctxt;
            let text = self.text;
            self.at(if d.f >= 3 { d.b() + 1 } else { d.b() });
            let name = &text[t.a()..t.b()];
            let ty = match t.f {
                9 => ATTRIBUTE_NOTATION,
                10 => ATTRIBUTE_ENUMERATION,
                n => n as c_int,
            };
            let def = match d.f {
                1 => ATTRIBUTE_REQUIRED,
                2 => ATTRIBUTE_IMPLIED,
                3 => ATTRIBUTE_FIXED,
                _ => ATTRIBUTE_NONE,
            };
            let tree = if ty == ATTRIBUTE_ENUMERATION || ty == ATTRIBUTE_NOTATION {
                let from = t.b();
                let to = if d.f >= 3 { d.a() } else { d.a().max(from) };
                enumeration(&text[from..to])
            } else {
                null_mut()
            };
            let mut value: Option<Vec<u8>> = None;
            if d.f >= 3 {
                let raw = &text[d.a()..d.b()];
                let mut v = match self.att_value(raw, false, false) {
                    Val::In(s) => s.to_vec(),
                    Val::Made(v) => v,
                };
                if ty != ATTRIBUTE_CDATA {
                    v = v.split(|&ch| ch == b' ').filter(|w| !w.is_empty()).collect::<Vec<_>>().join(&b' ');
                }
                value = Some(v);
            }
            let key = (elem.to_vec(), name.to_vec());
            if (*c).sax2 != 0 {
                if let (Some(v), true) = (&value, def != ATTRIBUTE_IMPLIED && def != ATTRIBUTE_REQUIRED) {
                    let list = self.dtd.defaults.entry(elem.to_vec()).or_default();
                    if !list.iter().any(|a| a.name == name) {
                        list.push(DefAttr { name: name.to_vec(), value: v.clone() });
                    }
                }
            }
            self.dtd.types.entry(key).or_insert(ty);
            let e = dict(c, elem);
            let n = dict(c, name);
            match handler(c).and_then(|h| h.attributeDecl) {
                Some(f) => {
                    let v = value.as_ref().map(|v| nul(v));
                    f((*c).userData, e, n, ty, def, v.as_ref().map_or(null(), |v| v.as_ptr()), tree);
                }
                None => xmlFreeEnumeration(tree),
            }
        }
    }

    unsafe fn entity_decl(&mut self, i: usize) -> usize {
        unsafe {
            let c = self.ctxt;
            let toks = self.toks(Src::Doc);
            let text = self.text;
            let t = toks[i];
            let pe = t.f != 0;
            let mut j = i + 1;
            let (mut value, mut pubid, mut sysid, mut ndata) = (None, None, None, None);
            while j < toks.len() {
                let u = toks[j];
                let s = &text[u.a()..u.b()];
                match u.kind {
                    Kind::EntityValue => value = Some(s),
                    Kind::PubId => pubid = Some(nul(s)),
                    Kind::SysId => sysid = Some(nul(s)),
                    Kind::NData => ndata = Some(s),
                    _ => break,
                }
                j += 1;
            }
            let last = toks[j - 1];
            let end = text[last.b()..].iter().position(|&ch| ch == b'>').map_or(text.len(), |e| last.b() + e + 1);
            self.at(end);
            let name_b = &text[t.a()..t.b()];
            let name = dict(c, name_b);
            if name_b.contains(&b':') {
                let msg = cat(&[b"colons are forbidden from entities names '", name_b, b"'\n"]);
                ns_err(c, NS_ERR_COLON, &msg, Some(name_b), None, None);
            }
            let p = |v: &Option<Vec<u8>>| v.as_ref().map_or(null(), |v| v.as_ptr());
            let ud = (*c).userData;
            let mut orig: Option<&[u8]> = None;
            if pe {
                if let Some(raw) = value {
                    let mut v = nul(&entity_value(raw));
                    if let Some(f) = handler(c).and_then(|h| h.entityDecl) {
                        f(ud, name, INTERNAL_PARAMETER_ENTITY, null(), null(), v.as_mut_ptr());
                    }
                    orig = Some(raw);
                } else if sysid.is_some() {
                    if let Some(f) = handler(c).and_then(|h| h.entityDecl) {
                        f(ud, name, EXTERNAL_PARAMETER_ENTITY, p(&pubid), p(&sysid), null_mut());
                    }
                }
            } else if let Some(raw) = value {
                let mut v = nul(&entity_value(raw));
                if let Some(f) = handler(c).and_then(|h| h.entityDecl) {
                    f(ud, name, INTERNAL_GENERAL_ENTITY, null(), null(), v.as_mut_ptr());
                }
                if self.compat_doc() {
                    xmlSAX2EntityDecl(c as Ctx, name, INTERNAL_GENERAL_ENTITY, null(), null(), v.as_mut_ptr());
                }
                orig = Some(raw);
            } else if let Some(nd) = ndata {
                let nd = dict(c, nd);
                if let Some(f) = handler(c).and_then(|h| h.unparsedEntityDecl) {
                    f(ud, name, p(&pubid), p(&sysid), nd);
                }
            } else {
                if let Some(f) = handler(c).and_then(|h| h.entityDecl) {
                    f(ud, name, EXTERNAL_GENERAL_PARSED_ENTITY, p(&pubid), p(&sysid), null_mut());
                }
                if (*c).replaceEntities != 0 && self.compat_doc() {
                    xmlSAX2EntityDecl(c as Ctx, name, EXTERNAL_GENERAL_PARSED_ENTITY, p(&pubid), p(&sysid), null_mut());
                }
            }
            if let Some(o) = orig {
                let mut cur: *mut Entity = null_mut();
                if !(*c).sax.is_null() {
                    if pe {
                        if let Some(f) = (*(*c).sax).getParameterEntity {
                            cur = f(ud, name);
                        }
                    } else {
                        if let Some(f) = (*(*c).sax).getEntity {
                            cur = f(ud, name);
                        }
                        if cur.is_null() && ud == c as *mut c_void {
                            cur = xmlSAX2GetEntity(c as Ctx, name);
                        }
                    }
                }
                if !cur.is_null() && (*cur).orig.is_null() {
                    (*cur).orig = xstrdup(o);
                }
            }
            j
        }
    }

    /// For a declaration with no document to hold it (a SAX parse): the
    /// "SAX compatibility mode" document libxml2 keeps entities in.
    unsafe fn compat_doc(&mut self) -> bool {
        unsafe {
            let c = self.ctxt;
            let doc = (*c).myDoc;
            if !doc.is_null() && copt((*doc).version) != Some(SAX_COMPAT) {
                return false;
            }
            if doc.is_null() {
                let z = nul(SAX_COMPAT);
                (*c).myDoc = xmlNewDoc(z.as_ptr());
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

impl<'d> Walk<'d> {
    // --- content ------------------------------------------------------------------------

    /// `xmlCharacters`, for a run of character data whose next bytes in the
    /// input are `next`.
    unsafe fn characters(&mut self, s: &[u8], blank: bool, next: [u8; 2]) {
        unsafe {
            let c = self.ctxt;
            let Some(h) = handler(c) else { return };
            let check = (*c).keepBlanks == 0 || h.ignorableWhitespace.map(|f| f as usize) != h.characters.map(|f| f as usize);
            if check && self.are_blanks(s, blank, next) {
                if let Some(f) = h.ignorableWhitespace {
                    if (*c).keepBlanks != 0 {
                        f((*c).userData, s.as_ptr(), s.len() as c_int);
                    }
                }
            } else {
                if let Some(f) = h.characters {
                    f((*c).userData, s.as_ptr(), s.len() as c_int);
                }
                let sp = &mut st(c).spaces;
                if check && sp.last() == Some(&-1) {
                    *sp.last_mut().unwrap() = -2;
                }
            }
        }
    }

    unsafe fn are_blanks(&self, s: &[u8], blank: bool, next: [u8; 2]) -> bool {
        unsafe {
            let c = self.ctxt;
            match st(c).spaces.last() {
                None | Some(1) | Some(-2) => return false,
                _ => {}
            }
            if !blank && !s.iter().all(|&ch| is_blank(ch)) {
                return false;
            }
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

    /// Character data `s`, followed in its input by `after` (the next two
    /// bytes: '<' or '&' and what follows, or NULs at the end), cut where
    /// libxml2 cuts it (`xmlParseCharDataInternal`).
    unsafe fn char_data(&mut self, s: &[u8], after: [u8; 2]) {
        unsafe {
            let n = s.len();
            let get = |i: usize| -> u8 {
                if i < n {
                    s[i]
                } else if i == n {
                    after[0]
                } else if i == n + 1 {
                    after[1]
                } else {
                    0
                }
            };
            let next = |i: usize| [get(i), get(i + 1)];
            let mut cur = 0;
            let mut i = 0;
            'fast: loop {
                loop {
                    while get(i) == b' ' {
                        i += 1;
                    }
                    if get(i) == b'\n' {
                        while get(i) == b'\n' {
                            i += 1;
                        }
                        continue;
                    }
                    break;
                }
                if get(i) == b'<' {
                    if i > cur {
                        self.characters(&s[cur..i], true, next(i));
                    }
                    return;
                }
                loop {
                    while i < n && plain_char(s[i]) {
                        i += 1;
                    }
                    if i < n && s[i] == b'\n' {
                        while i < n && s[i] == b'\n' {
                            i += 1;
                        }
                        continue;
                    }
                    if i < n && s[i] == b']' {
                        i += 1;
                        continue;
                    }
                    break;
                }
                if i > cur {
                    self.characters(&s[cur..i], false, next(i));
                }
                cur = i;
                if i < n && s[i] == 0x0D && get(i + 1) == 0x0A {
                    cur = i + 1;
                    i += 2;
                    let ch = get(i);
                    if (0x20..=0x7F).contains(&ch) || ch == 0x09 || ch == 0x0A {
                        continue 'fast;
                    }
                    break 'fast;
                }
                if i >= n {
                    return;
                }
                break;
            }
            // The other path: characters copied, line ends normalized, in
            // pieces of 300 bytes.
            let mut buf: Vec<u8> = Vec::with_capacity(305);
            let mut j = cur;
            while j < n {
                if s[j] == 0x0D {
                    buf.push(b'\n');
                    j += if get(j + 1) == 0x0A { 2 } else { 1 };
                } else {
                    let l = if s[j] < 0x80 { 1 } else { crate::chars::ex_cp_at_hi(s, j).map_or(1, |x| x.1) };
                    buf.extend_from_slice(&s[j..j + l]);
                    j += l;
                }
                if buf.len() >= 300 {
                    self.characters(&buf, false, next(j));
                    buf.clear();
                }
            }
            if !buf.is_empty() {
                self.characters(&buf, false, next(j));
            }
        }
    }

    /// The content of `src` from token `i` to `end`, elements and all.
    unsafe fn content(&mut self, src: Src, i: usize, end: usize) {
        unsafe {
            let mut open: Vec<(Open, usize)> = Vec::new();
            self.content_in(&mut open, src, i, end);
        }
    }

    /// Pushed: the character data read so far, reported (it has ended, or
    /// grown to what libxml2 reports in one go).
    unsafe fn flush_text(&mut self) {
        unsafe {
            if self.pend.is_empty() && !self.pend_cdata {
                return;
            }
            let v = std::mem::take(&mut self.pend);
            let e = self.pend_end;
            self.at(e);
            if self.pend_cdata {
                self.pend_cdata = false;
                self.cdata_block(&v);
            } else {
                let after = [self.text.get(e).copied().unwrap_or(0), self.text.get(e + 1).copied().unwrap_or(0)];
                self.char_data(&v, after);
            }
            self.pend = v;
            self.pend.clear();
        }
    }

    unsafe fn cdata_block(&mut self, raw: &[u8]) {
        unsafe {
            let c = self.ctxt;
            if let Some(h) = handler(c) {
                // A copy with a NUL after it, as xmlParseCDSect passes.
                let v = nul(&eol(raw));
                let n = (v.len() - 1) as c_int;
                if h.cdataBlock.is_some() && (*c).options & PARSE_NOCDATA == 0 {
                    (h.cdataBlock.unwrap())((*c).userData, v.as_ptr(), n);
                } else if let Some(f) = h.characters {
                    f((*c).userData, v.as_ptr(), n);
                }
            }
        }
    }

    /// The content of `src` from token `i` to `end`, inside the elements
    /// `open` (which it leaves open where the tokens end).
    unsafe fn content_in(&mut self, open: &mut Vec<(Open, usize)>, src: Src, mut i: usize, end: usize) {
        unsafe {
            let c = self.ctxt;
            let toks = self.toks(src);
            let buf = self.buf(src);
            let pushed = self.push && src == Src::Doc;
            while i < end && (*c).disableSAX < 2 {
                let t = toks[i];
                if pushed {
                    match t.kind {
                        // Character data and CDATA sections come in pieces:
                        // reported when they end (or have grown to 300
                        // bytes, for character data), as libxml2's push
                        // parser reports them.
                        Kind::Text => {
                            self.pend.extend_from_slice(&buf[t.a()..t.b()]);
                            self.pend_end = t.b();
                            if self.pend.len() >= 300 {
                                self.flush_text();
                            }
                            i += 1;
                            continue;
                        }
                        Kind::CData => {
                            if t.f & crate::stream::P_FIRST != 0 {
                                self.flush_text();
                                self.pend_cdata = true;
                            }
                            self.pend.extend_from_slice(&buf[t.a()..t.b()]);
                            self.pend_end = t.b();
                            if t.f & crate::stream::P_LAST != 0 {
                                self.pend_end = t.b() + 3;
                                self.flush_text();
                            }
                            i += 1;
                            continue;
                        }
                        _ => self.flush_text(),
                    }
                }
                match t.kind {
                    Kind::STag => {
                        let (o, next) = self.start_tag(src, i);
                        match o {
                            Some(o) => {
                                open.push((o, t.c()));
                                i = next;
                            }
                            None => {
                                // Too deep: stop.
                                return;
                            }
                        }
                        continue;
                    }
                    Kind::ETag => {
                        if let Some((o, _)) = open.pop() {
                            if pushed {
                                // The end tag's span (none for `<a/>`).
                                if t.b() > 0 {
                                    self.at(t.b());
                                }
                            } else if src == Src::Doc {
                                // An ETag carries no offsets: the end tag, if
                                // the element has one (not `<a/>`), starts
                                // where the walk is.
                                let cur = st(c).at.0;
                                if buf.get(cur..).is_some_and(|r| r.starts_with(b"</")) {
                                    if let Some(g) = buf[cur..].iter().position(|&ch| ch == b'>') {
                                        self.at(cur + g + 1);
                                    }
                                }
                            }
                            self.end_tag(o);
                        }
                    }
                    Kind::Text => {
                        // Runs of character data up to the next '<' or '&'.
                        let a = t.a();
                        let mut b = t.b();
                        while i + 1 < end && toks[i + 1].kind == Kind::Text && toks[i + 1].a() == b {
                            i += 1;
                            b = toks[i].b();
                        }
                        if src == Src::Doc {
                            self.at(b);
                        }
                        let after = [buf.get(b).copied().unwrap_or(0), buf.get(b + 1).copied().unwrap_or(0)];
                        self.char_data(&buf[a..b], after);
                    }
                    Kind::CData => {
                        if src == Src::Doc {
                            self.at(t.b() + 3);
                        }
                        self.cdata_block(&buf[t.a()..t.b()]);
                    }
                    Kind::CharRef => {
                        let semi = buf[t.a()..].iter().position(|&ch| ch == b';').map_or(t.a(), |e| t.a() + e + 1);
                        if src == Src::Doc {
                            self.at(semi);
                        }
                        let v = utf8_of(t.b() as u32);
                        if buf.get(t.a() + 1) == Some(&b'#') {
                            if let Some(f) = handler(c).and_then(|h| h.characters) {
                                f((*c).userData, v.as_ptr(), v.len() as c_int);
                            }
                        } else {
                            // A predefined entity.
                            self.predefined(&buf[t.a() + 1..semi - 1], &v);
                        }
                    }
                    Kind::Comment => self.comment(src, t),
                    Kind::PI => {
                        self.pi(src, t, toks[i + 1]);
                        i += 1;
                    }
                    Kind::EntRef => {
                        if src == Src::Doc {
                            self.at(t.b() + 1);
                        }
                        self.reference(src, t);
                    }
                    _ => {}
                }
                i += 1;
            }
        }
    }

    unsafe fn predefined(&mut self, name: &[u8], v: &[u8]) {
        unsafe {
            let c = self.ctxt;
            if (*c).options & PARSE_OLDSAX != 0 {
                let ent = self.lookup(name);
                if ent.is_null() {
                    return;
                }
                if let Some(f) = handler(c).and_then(|h| h.characters) {
                    f((*c).userData, (*ent).content, xmlStrlen((*ent).content));
                }
                return;
            }
            if let Some(f) = handler(c).and_then(|h| h.characters) {
                f((*c).userData, v.as_ptr(), v.len() as c_int);
            }
        }
    }

    /// A reference to a general entity in content (`xmlParseReference`).
    unsafe fn reference(&mut self, src: Src, t: Tok) {
        unsafe {
            let c = self.ctxt;
            let name = &self.buf(src)[t.a()..t.b()];
            let ent = self.lookup(name);
            if ent.is_null() {
                if (*c).replaceEntities == 0 {
                    if let Some(f) = handler(c).and_then(|h| h.reference) {
                        f((*c).userData, dict(c, name));
                    }
                }
                return;
            }
            if (*c).wellFormed == 0 {
                return;
            }
            if (*ent).name.is_null() || (*ent).etype == INTERNAL_PREDEFINED_ENTITY {
                if !(*ent).content.is_null() {
                    if let Some(f) = handler(c).and_then(|h| h.characters) {
                        f((*c).userData, (*ent).content, xmlStrlen((*ent).content));
                    }
                }
                return;
            }
            if (*ent).flags & ENT_PARSED == 0 && !(*ent).children.is_null() {
                (*ent).flags |= ENT_PARSED;
            }
            let k = self.ent_index(name);
            if (*ent).etype == INTERNAL_GENERAL_ENTITY
                || ((*c).options & PARSE_NO_XXE == 0 && ((*c).replaceEntities != 0 || (*c).validate != 0))
            {
                if (*ent).flags & ENT_PARSED == 0 || (*ent).children.is_null() {
                    self.parse_entity(ent, k);
                }
            }
            let size = k.map_or((*ent).length as u64, |k| self.size_of(k, 0));
            if !self.amplification(size) {
                return;
            }
            let Some(h) = handler(c) else { return };
            if (*c).replaceEntities == 0 {
                if let Some(f) = h.reference {
                    f((*c).userData, (*ent).name);
                }
            } else if !(*ent).children.is_null() && !(*c).node.is_null() {
                self.copy_entity(ent);
            }
        }
    }

    /// The entity's tree, copied into the current node (`xmlParseReference`
    /// with entities replaced): the first and last text through the
    /// handler, so that they merge with the text around them.
    unsafe fn copy_entity(&mut self, ent: *mut Entity) {
        unsafe {
            let c = self.ctxt;
            let h = &*(*c).sax;
            let mut cur = (*ent).children;
            let text_cb = move |cur: *mut Node| {
                let len = xmlStrlen((*cur).content);
                if (*cur).type_ == TEXT_NODE || (*c).options & PARSE_NOCDATA != 0 {
                    if let Some(f) = h.characters {
                        f((*c).userData, (*cur).content, len);
                    }
                } else if let Some(f) = h.cdataBlock {
                    f((*c).userData, (*cur).content, len);
                }
            };
            if matches!((*cur).type_, TEXT_NODE | CDATA_SECTION_NODE) {
                text_cb(cur);
                cur = (*cur).next;
            }
            while !cur.is_null() {
                if (*cur).next.is_null() && matches!((*cur).type_, TEXT_NODE | CDATA_SECTION_NODE) {
                    text_cb(cur);
                    break;
                }
                (*c).nodemem = 0;
                (*c).nodelen = 0;
                let copy = xmlDocCopyNode(cur, (*c).myDoc, 1);
                if copy.is_null() {
                    ctx_err(c, null_mut(), FROM_PARSER, ERR_NO_MEMORY, ERR_FATAL, None, None, None, 0, b"Out of memory\n");
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

    /// `xmlCtxtParseEntity`: the entity's content parsed, its SAX events
    /// made, and (when a tree is being built) its tree kept in the entity.
    unsafe fn parse_entity(&mut self, ent: *mut Entity, k: Option<usize>) {
        unsafe {
            let c = self.ctxt;
            let build = !(*c).node.is_null();
            if (*ent).flags & ENT_EXPANDING != 0 {
                fatal(c, ERR_ENTITY_LOOP, b"Detected an entity reference loop\n", None);
                (*ent).flags |= ENT_PARSED | ENT_CHECKED;
                return;
            }
            let tape_len = match k {
                Some(k) if (*ent).etype == INTERNAL_GENERAL_ENTITY => self.doc.ent_tape(k).map(|t| t.toks.len()),
                _ => None,
            };
            let Some(n) = tape_len else {
                // An external entity: not read.
                (*ent).flags |= ENT_PARSED | ENT_CHECKED;
                return;
            };
            let k = k.unwrap();
            let s = st(c);
            let old_min = s.min_ns;
            if build {
                s.min_ns = s.ns.len();
            }
            let (old_len, old_mem) = ((*c).nodelen, (*c).nodemem);
            (*c).nodelen = 0;
            (*c).nodemem = 0;
            (*ent).flags |= ENT_EXPANDING;
            let root = if build { xmlNewDocNode((*c).myDoc, null_mut(), c"#root".as_ptr() as *const XChar, null()) } else { null_mut() };
            st(c).spaces.push(-1);
            let mut pushed = false;
            if !root.is_null() {
                pushed = node_push(c, root) == 0;
            }
            self.content(Src::Ent(k), 0, n);
            let mut list = null_mut();
            if !root.is_null() && ((*c).wellFormed != 0 || ((*c).recovery != 0 && !catastrophic(&(*c).lastError))) {
                list = (*root).children;
                (*root).children = null_mut();
                (*root).last = null_mut();
                let mut x = list;
                while !x.is_null() {
                    (*x).parent = null_mut();
                    x = (*x).next;
                }
            }
            if pushed {
                node_pop(c);
            }
            st(c).spaces.pop();
            (*ent).flags &= !ENT_EXPANDING;
            st(c).min_ns = old_min;
            (*c).nodelen = old_len;
            (*c).nodemem = old_mem;
            if (*ent).flags & ENT_PARSED == 0 {
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
            } else {
                xmlFreeNodeList(list);
            }
            xmlFreeNode(root);
            (*ent).flags |= ENT_PARSED | ENT_CHECKED;
        }
    }
}

impl<'d> Walk<'d> {
    /// `xmlParserNsPush`: false if the prefix was bound by this element
    /// already (an error, unless the binding is a default).
    unsafe fn ns_push(&mut self, prefix: *const XChar, uri: *const XChar, def: bool, mine: usize) -> bool {
        unsafe {
            let c = self.ctxt;
            let s = st(c);
            let p = copt(prefix);
            if p == Some(b"xml") {
                return false;
            }
            let from = s.ns.len() - mine;
            if s.ns[from..].iter().any(|b| copt(b.prefix) == p) {
                if !def {
                    let msg = match p {
                        None => b"Attribute xmlns redefined\n".to_vec(),
                        Some(p) => cat(&[b"Attribute xmlns:", p, b" redefined\n"]),
                    };
                    match p {
                        None => fatal(c, ERR_ATTRIBUTE_REDEFINED, &msg, Some(b"xmlns")),
                        Some(pp) => ctx_err(c, null_mut(), FROM_PARSER, ERR_ATTRIBUTE_REDEFINED, ERR_FATAL, Some(b"xmlns"), Some(pp), None, 0, &msg),
                    }
                }
                return false;
            }
            if (*c).options & PARSE_NSCLEAN != 0 {
                let s = st(c);
                if let Some(b) = s.ns.iter().rev().find(|b| copt(b.prefix) == p) {
                    if b.uri == uri {
                        return false;
                    }
                }
            }
            st(c).ns.push(NsBinding { prefix, uri, sax: null_mut() });
            true
        }
    }

    /// The start tag at `i` (`xmlParseStartTag2`, or `xmlParseStartTag` for
    /// SAX1): its SAX call. Returns what its end tag needs and the index of
    /// the token after its attributes; `None` if the depth limit stopped
    /// the parse.
    unsafe fn start_tag(&mut self, src: Src, i: usize) -> (Option<Open>, usize) {
        unsafe {
            let c = self.ctxt;
            let toks = self.toks(src);
            let buf = self.buf(src);
            let t = toks[i];
            let qn = &buf[t.a()..t.b()];
            let max = if (*c).options & PARSE_HUGE != 0 { 2048 } else { 256 };
            let depth = st(c).ns_counts.len();
            if depth > max {
                let msg = format!("Excessive depth in document: {depth} use XML_PARSE_HUGE option\n");
                ctx_err(c, null_mut(), FROM_PARSER, ERR_RESOURCE_LIMIT, ERR_FATAL, None, None, None, depth as c_int, msg.as_bytes());
                return (None, i + 1);
            }
            // The attributes' tokens, and where the tag ends.
            let mut j = i + 1;
            let mut atts: Vec<(Tok, Tok)> = Vec::new();
            while j + 1 < toks.len() && toks[j].kind == Kind::Attr {
                atts.push((toks[j], toks[j + 1]));
                j += 2;
            }
            let tag_end = {
                let from = atts.last().map_or(t.b(), |(_, v)| v.b() + 1);
                buf[from..].iter().position(|&ch| ch == b'>' || ch == b'/').map_or(from, |e| from + e)
            };
            let sp = *st(c).spaces.last().unwrap_or(&-1);
            st(c).spaces.push(if sp == -2 { -1 } else { sp });
            if (*c).sax2 == 0 {
                return (self.start_tag_sax1(src, qn, &atts, tag_end), j);
            }
            let (prefix_b, local_b) = qname(qn);
            if prefix_b.is_none() && qn.contains(&b':') {
                if src == Src::Doc {
                    self.at(t.b());
                }
                let msg = cat(&[b"Failed to parse QName '", qn, b"'\n"]);
                ns_err(c, NS_ERR_QNAME, &msg, Some(qn), None, None);
            }
            let local = dict(c, local_b);
            let prefix = prefix_b.map_or(null(), |p| dict(c, p));
            let elem_types = !self.dtd.types.is_empty();
            let mut mine = 0usize;
            let mut nb_ns = 0usize;
            // name, prefix, value; the value either in the input or made.
            let mut regular: Vec<(&[u8], Option<&[u8]>, Val)> = Vec::new();
            if src == Src::Doc {
                self.at(tag_end);
            }
            for (n, v) in &atts {
                let aq = &buf[n.a()..n.b()];
                let (ap, al) = qname(aq);
                if ap.is_none() && aq.contains(&b':') {
                    if src == Src::Doc {
                        self.at(n.b());
                    }
                    let msg = cat(&[b"Failed to parse QName '", aq, b"'\n"]);
                    ns_err(c, NS_ERR_QNAME, &msg, Some(aq), None, None);
                    if src == Src::Doc {
                        self.at(tag_end);
                    }
                }
                let raw = &buf[v.a()..v.b()];
                let is_ns = (ap.is_none() && al == b"xmlns") || ap == Some(b"xmlns");
                let normalize = elem_types && self.dtd.types.get(&(qn.to_vec(), aq.to_vec())).is_some_and(|&ty| ty > ATTRIBUTE_CDATA);
                let val = self.att_value(raw, normalize, is_ns);
                let vb: &[u8] = match &val {
                    Val::In(s) => s,
                    Val::Made(m) => m,
                };
                if ap == Some(b"xml") && al == b"space" {
                    let sp = st(c).spaces.last_mut().unwrap();
                    if vb == b"default" {
                        *sp = 0;
                    } else if vb == b"preserve" {
                        *sp = 1;
                    } else {
                        let msg = cat(&[b"Invalid value \"", vb, b"\" for xml:space : \"default\" or \"preserve\" expected\n"]);
                        warning(c, 102, &msg, Some(vb), None);
                    }
                }
                if ap.is_none() && al == b"xmlns" {
                    let uri = dict(c, vb);
                    if !vb.is_empty() {
                        let (ok, scheme) = uri_check(vb);
                        if !ok {
                            let msg = cat(&[b"xmlns: '", vb, b"' is not a valid URI\n"]);
                            ns_err(c, 99, &msg, Some(vb), None, None);
                        } else if !scheme {
                            let msg = cat(&[b"xmlns: URI ", vb, b" is not absolute\n"]);
                            ns_warn(c, 100, &msg, Some(vb), None);
                        }
                        if vb == XML_XML_NAMESPACE {
                            ns_err(c, NS_ERR_XML_NAMESPACE, b"xml namespace URI cannot be the default namespace\n", None, None, None);
                            continue;
                        }
                        if vb == b"http://www.w3.org/2000/xmlns/" {
                            ns_err(c, NS_ERR_XML_NAMESPACE, b"reuse of the xmlns namespace name is forbidden\n", None, None, None);
                            continue;
                        }
                    }
                    if self.ns_push(null(), uri, false, mine) {
                        mine += 1;
                        nb_ns += 1;
                    }
                } else if ap == Some(b"xmlns") {
                    let uri = dict(c, vb);
                    if al == b"xml" {
                        if vb != XML_XML_NAMESPACE {
                            ns_err(c, NS_ERR_XML_NAMESPACE, b"xml namespace prefix mapped to wrong URI\n", None, None, None);
                        }
                        continue;
                    }
                    if vb == XML_XML_NAMESPACE {
                        ns_err(c, NS_ERR_XML_NAMESPACE, b"xml namespace URI mapped to wrong prefix\n", None, None, None);
                        continue;
                    }
                    if al == b"xmlns" {
                        ns_err(c, NS_ERR_XML_NAMESPACE, b"redefinition of the xmlns prefix is forbidden\n", None, None, None);
                        continue;
                    }
                    if vb == b"http://www.w3.org/2000/xmlns/" {
                        ns_err(c, NS_ERR_XML_NAMESPACE, b"reuse of the xmlns namespace name is forbidden\n", None, None, None);
                        continue;
                    }
                    if vb.is_empty() {
                        let msg = cat(&[b"xmlns:", al, b": Empty XML namespace is not allowed\n"]);
                        ns_err(c, NS_ERR_XML_NAMESPACE, &msg, Some(al), None, None);
                        continue;
                    }
                    let (ok, scheme) = uri_check(vb);
                    if !ok {
                        let msg = cat(&[b"xmlns:", al, b": '", vb, b"' is not a valid URI\n"]);
                        ns_err(c, 99, &msg, Some(al), Some(vb), None);
                    } else if (*c).pedantic != 0 && !scheme {
                        let msg = cat(&[b"xmlns:", al, b": URI ", vb, b" is not absolute\n"]);
                        ns_warn(c, 100, &msg, Some(al), Some(vb));
                    }
                    if self.ns_push(dict(c, al), uri, false, mine) {
                        mine += 1;
                        nb_ns += 1;
                    }
                } else {
                    regular.push((al, ap, val));
                }
            }
            // Namespaces from defaulted attributes.
            let defaults: Vec<(Vec<u8>, Vec<u8>)> = self
                .dtd
                .defaults
                .get(qn)
                .map(|l| l.iter().map(|d| (d.name.clone(), d.value.clone())).collect())
                .unwrap_or_default();
            for (dn, dv) in &defaults {
                let (dp, dl) = qname(dn);
                if dp.is_none() && dl == b"xmlns" {
                    if self.ns_push(null(), dict(c, dv), true, mine) {
                        mine += 1;
                        nb_ns += 1;
                    }
                } else if dp == Some(b"xmlns") && self.ns_push(dict(c, dl), dict(c, dv), true, mine) {
                    mine += 1;
                    nb_ns += 1;
                }
            }
            st(c).ns_counts.push(mine);
            // Resolve the attributes' namespaces, then check that their
            // names are unique.
            let s = st(c);
            let mut out: Vec<[*const XChar; 5]> = Vec::with_capacity(regular.len() + defaults.len());
            let mut keys: Vec<(Option<*const XChar>, &[u8], Option<&[u8]>)> = Vec::new();
            let mut dup_err = 0;
            let mut ns_errs = 0;
            let mut owned: Vec<Vec<u8>> = Vec::new();
            for (al, ap, val) in regular.iter() {
                let uri: Option<*const XChar> = match ap {
                    None => None,
                    Some(b"xml") => Some((*c).str_xml_ns),
                    Some(p) => match ns_uri(s, p) {
                        Some(u) => Some(u),
                        None => {
                            let msg = cat(&[b"Namespace prefix ", p, b" for ", al, b" on ", local_b, b" is not defined\n"]);
                            ns_err(c, NS_ERR_UNDEFINED_NAMESPACE, &msg, Some(p), Some(al), Some(local_b));
                            None
                        }
                    },
                };
                let ukey = uri.map(|u| u as usize);
                if ap.is_none() || uri.is_some() {
                    if let Some((_, _, prev_p)) = keys.iter().find(|(u, n, _)| u.map(|x| x as usize) == ukey && *n == *al) {
                        if *prev_p == *ap {
                            let msg = match ap {
                                None => cat(&[b"Attribute ", al, b" redefined\n"]),
                                Some(p) => cat(&[b"Attribute ", p, b":", al, b" redefined\n"]),
                            };
                            match ap {
                                None => fatal(c, ERR_ATTRIBUTE_REDEFINED, &msg, Some(al)),
                                Some(p) => ctx_err(c, null_mut(), FROM_PARSER, ERR_ATTRIBUTE_REDEFINED, ERR_FATAL, Some(p), Some(al), None, 0, &msg),
                            }
                            dup_err += 1;
                        } else {
                            let u = uri.map_or(&b""[..], |u| cbytes(u));
                            let msg = cat(&[b"Namespaced Attribute ", al, b" in '", u, b"' redefined\n"]);
                            ns_err(c, NS_ERR_ATTRIBUTE_REDEFINED, &msg, Some(al), Some(u), None);
                            ns_errs += 1;
                        }
                    } else {
                        keys.push((uri, al, *ap));
                    }
                }
                let (v, ve) = match val {
                    Val::In(sl) => (sl.as_ptr(), sl.as_ptr().add(sl.len())),
                    Val::Made(m) => {
                        let z = nul(m);
                        owned.push(z);
                        let z = owned.last().unwrap();
                        (z.as_ptr(), z.as_ptr().add(z.len() - 1))
                    }
                };
                out.push([dict(c, al), ap.map_or(null(), |p| dict(c, p)), uri.unwrap_or(null()), v, ve]);
            }
            if dup_err == 0 && ns_errs > 1 {
                let mut seen: Vec<(&[u8], &[u8])> = Vec::new();
                for (al, ap, _) in regular.iter() {
                    if let Some(p) = ap {
                        if seen.contains(&(p, al)) {
                            let msg = cat(&[b"Attribute ", p, b":", al, b" redefined\n"]);
                            ctx_err(c, null_mut(), FROM_PARSER, ERR_ATTRIBUTE_REDEFINED, ERR_FATAL, Some(p), Some(al), None, 0, &msg);
                        } else {
                            seen.push((p, al));
                        }
                    }
                }
            }
            // Defaulted attributes.
            let mut nb_def = 0;
            for (dn, dv) in &defaults {
                let (dp, dl) = qname(dn);
                if (dp.is_none() && dl == b"xmlns") || dp == Some(b"xmlns") {
                    continue;
                }
                let s = st(c);
                let uri: Option<*const XChar> = match dp {
                    None => None,
                    Some(b"xml") => Some((*c).str_xml_ns),
                    Some(p) => match ns_uri(s, p) {
                        Some(u) => Some(u),
                        None => {
                            let msg = cat(&[b"Namespace prefix ", p, b" for ", dl, b" on ", local_b, b" is not defined\n"]);
                            ns_err(c, NS_ERR_UNDEFINED_NAMESPACE, &msg, Some(p), Some(dl), Some(local_b));
                            None
                        }
                    },
                };
                let ukey = uri.map(|u| u as usize);
                if let Some((_, _, prev_p)) = keys.iter().find(|(u, n, _)| u.map(|x| x as usize) == ukey && *n == dl) {
                    if *prev_p == dp {
                        continue;
                    }
                    let u = uri.map_or(&b""[..], |u| cbytes(u));
                    let msg = cat(&[b"Namespaced Attribute ", dl, b" in '", u, b"' redefined\n"]);
                    ns_err(c, NS_ERR_ATTRIBUTE_REDEFINED, &msg, Some(dl), Some(u), None);
                }
                let z = nul(dv);
                owned.push(z);
                let z = owned.last().unwrap();
                out.push([dict(c, dl), dp.map_or(null(), |p| dict(c, p)), uri.unwrap_or(null()), z.as_ptr(), z.as_ptr().add(z.len() - 1)]);
                nb_def += 1;
            }
            let s = st(c);
            let uri = match prefix_b {
                Some(b"xml") => (*c).str_xml_ns,
                Some(p) => ns_uri(s, p).unwrap_or(null()),
                None => {
                    let mut u = null();
                    for k in (s.min_ns..s.ns.len()).rev() {
                        if s.ns[k].prefix.is_null() {
                            if !s.ns[k].uri.is_null() && *s.ns[k].uri != 0 {
                                u = s.ns[k].uri;
                            }
                            break;
                        }
                    }
                    u
                }
            };
            if let (Some(p), true) = (prefix_b, uri.is_null()) {
                let msg = cat(&[b"Namespace prefix ", p, b" on ", local_b, b" is not defined\n"]);
                ns_err(c, NS_ERR_UNDEFINED_NAMESPACE, &msg, Some(p), Some(local_b), None);
            }
            if let Some(f) = handler(c).and_then(|h| h.startElementNs) {
                let s = st(c);
                let mut nss: Vec<*const XChar> = Vec::with_capacity(2 * nb_ns);
                for b in &s.ns[s.ns.len() - nb_ns..] {
                    nss.push(b.prefix);
                    nss.push(b.uri);
                }
                let mut flat: Vec<*const XChar> = out.iter().flatten().copied().collect();
                f(
                    (*c).userData,
                    local,
                    prefix,
                    uri,
                    nb_ns as c_int,
                    if nb_ns > 0 { nss.as_mut_ptr() } else { null_mut() },
                    out.len() as c_int,
                    nb_def,
                    if flat.is_empty() { null_mut() } else { flat.as_mut_ptr() },
                );
            }
            drop(owned);
            (Some(Open { local, prefix, uri, name: null(), nb_ns: mine }), j)
        }
    }

    unsafe fn start_tag_sax1(&mut self, src: Src, qn: &[u8], atts: &[(Tok, Tok)], tag_end: usize) -> Option<Open> {
        unsafe {
            let c = self.ctxt;
            let buf = self.buf(src);
            if src == Src::Doc {
                self.at(tag_end);
            }
            let name = dict(c, qn);
            let mut vals: Vec<Vec<u8>> = Vec::new();
            let mut names: Vec<&[u8]> = Vec::new();
            for (n, v) in atts {
                let an = &buf[n.a()..n.b()];
                let raw = &buf[v.a()..v.b()];
                let val = match self.att_value(raw, false, false) {
                    Val::In(s) => nul(s),
                    Val::Made(m) => nul(&m),
                };
                if an == b"xml:space" {
                    let vb = &val[..val.len() - 1];
                    let sp = st(c).spaces.last_mut().unwrap();
                    if vb == b"default" {
                        *sp = 0;
                    } else if vb == b"preserve" {
                        *sp = 1;
                    } else {
                        let msg = cat(&[b"Invalid value \"", vb, b"\" for xml:space : \"default\" or \"preserve\" expected\n"]);
                        warning(c, 102, &msg, Some(vb), None);
                    }
                }
                if names.contains(&an) {
                    let msg = cat(&[b"Attribute ", an, b" redefined\n"]);
                    fatal(c, ERR_ATTRIBUTE_REDEFINED, &msg, Some(an));
                    continue;
                }
                names.push(an);
                vals.push(val);
            }
            st(c).ns_counts.push(0);
            if let Some(f) = handler(c).and_then(|h| h.startElement) {
                let mut arr: Vec<*const XChar> = Vec::new();
                for (n, v) in names.iter().zip(&vals) {
                    arr.push(dict(c, n));
                    arr.push(v.as_ptr());
                }
                if arr.is_empty() {
                    f((*c).userData, name, null_mut());
                } else {
                    arr.push(null());
                    arr.push(null());
                    f((*c).userData, name, arr.as_mut_ptr());
                }
            }
            Some(Open { local: null(), prefix: null(), uri: null(), name, nb_ns: 0 })
        }
    }

    unsafe fn end_tag(&mut self, o: Open) {
        unsafe {
            let c = self.ctxt;
            if (*c).sax2 != 0 {
                if let Some(f) = handler(c).and_then(|h| h.endElementNs) {
                    f((*c).userData, o.local, o.prefix, o.uri);
                }
            } else if let Some(f) = handler(c).and_then(|h| h.endElement) {
                f((*c).userData, o.name);
            }
            let s = st(c);
            s.spaces.pop();
            s.ns_counts.pop();
            let n = s.ns.len();
            s.ns.truncate(n - o.nb_ns);
        }
    }
}

// --- inputs ----------------------------------------------------------------------

/// A new input over `len` bytes at `data`: copied unless `keep`.
unsafe fn new_input(filename: Option<&[u8]>, data: *const u8, len: usize, keep: bool) -> *mut ParserInput {
    unsafe {
        let input: *mut ParserInput = xnew();
        if input.is_null() {
            return input;
        }
        let base = if keep {
            data
        } else {
            let p = xmalloc(len + 1) as *mut u8;
            if p.is_null() {
                xfree(input as *mut c_void);
                return null_mut();
            }
            if len > 0 {
                std::ptr::copy_nonoverlapping(data, p, len);
            }
            *p.add(len) = 0;
            (*input).flags |= INPUT_OWNED;
            p as *const u8
        };
        (*input).base = base;
        (*input).cur = base;
        (*input).end = base.add(len);
        (*input).line = 1;
        (*input).col = 1;
        if let Some(f) = filename {
            (*input).filename = xstrdup(f) as *const c_char;
        }
        input
    }
}

unsafe fn input_bytes<'a>(input: *mut ParserInput) -> &'a [u8] {
    unsafe {
        if (*input).base.is_null() {
            return &[];
        }
        std::slice::from_raw_parts((*input).base, (*input).end.offset_from((*input).base) as usize)
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlFreeInputStream(input: *mut ParserInput) {
    unsafe {
        if input.is_null() {
            return;
        }
        xfree((*input).filename as *mut c_void);
        xfree((*input).directory as *mut c_void);
        xfree((*input).version as *mut c_void);
        xfree((*input).encoding as *mut c_void);
        if (*input).flags & INPUT_OWNED != 0 {
            xfree((*input).base as *mut c_void);
        }
        xfree(input as *mut c_void);
    }
}

/// `XML_INPUT_BUF_STATIC`: the caller's bytes stay valid while the input
/// is in use.
const BUF_STATIC: c_int = 1 << 1;

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewInputFromMemory(url: *const c_char, mem: *const c_void, size: usize, flags: c_int) -> *mut ParserInput {
    unsafe {
        if mem.is_null() && size > 0 {
            return null_mut();
        }
        new_input(copt(url as *const XChar), mem as *const u8, size, flags & BUF_STATIC != 0)
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewInputFromString(url: *const c_char, s: *const c_char, flags: c_int) -> *mut ParserInput {
    unsafe {
        if s.is_null() {
            return null_mut();
        }
        let b = cbytes(s as *const XChar);
        new_input(copt(url as *const XChar), b.as_ptr(), b.len(), flags & BUF_STATIC != 0)
    }
}

/// An input's declared or given encoding, kept to override the document's.
unsafe fn set_input_encoding(input: *mut ParserInput, encoding: *const c_char) {
    unsafe {
        if !input.is_null() && !encoding.is_null() {
            (*input).encoding = xstrdup(cbytes(encoding as *const XChar));
        }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCtxtNewInputFromMemory(
    _ctxt: *mut ParserCtxt,
    url: *const c_char,
    mem: *const c_void,
    size: usize,
    encoding: *const c_char,
    flags: c_int,
) -> *mut ParserInput {
    unsafe {
        let i = xmlNewInputFromMemory(url, mem, size, flags);
        set_input_encoding(i, encoding);
        i
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCtxtNewInputFromString(
    _ctxt: *mut ParserCtxt,
    url: *const c_char,
    s: *const c_char,
    encoding: *const c_char,
    flags: c_int,
) -> *mut ParserInput {
    unsafe {
        let i = xmlNewInputFromString(url, s, flags);
        set_input_encoding(i, encoding);
        i
    }
}

/// The file at `path` (a path, or a file: URI).
fn read_path(path: &[u8]) -> std::io::Result<Vec<u8>> {
    use std::os::unix::ffi::OsStrExt;
    let p = if let Some(r) = path.strip_prefix(b"file://localhost") {
        r
    } else if let Some(r) = path.strip_prefix(b"file://") {
        r
    } else if let Some(r) = path.strip_prefix(b"file:") {
        r
    } else {
        path
    };
    let raw = std::fs::read(std::ffi::OsStr::from_bytes(p))?;
    // A gzip file: libxml2 reads it through zlib, which this does not
    // link; it is reported as an unreadable file.
    Ok(raw)
}

/// An input from a file, or NULL after an I/O error on `ctxt`.
unsafe fn file_input(ctxt: *mut ParserCtxt, filename: *const c_char, encoding: *const c_char) -> *mut ParserInput {
    unsafe {
        if filename.is_null() {
            return null_mut();
        }
        let name = cbytes(filename as *const XChar);
        let read = match super::io::read_by_callbacks(name) {
            Some(Some(d)) => Ok(d),
            Some(None) => Err(std::io::Error::other("callback")),
            None => read_path(name),
        };
        match read {
            Ok(data) => {
                let i = new_input(Some(name), data.as_ptr(), data.len(), false);
                set_input_encoding(i, encoding);
                i
            }
            Err(e) => {
                let code = if e.kind() == std::io::ErrorKind::NotFound { IO_ENOENT } else { IO_UNKNOWN };
                io_err(ctxt, code, Some(name));
                null_mut()
            }
        }
    }
}

/// `xmlCtxtErrIO`.
unsafe fn io_err(ctxt: *mut ParserCtxt, code: c_int, uri: Option<&[u8]>) {
    unsafe {
        let level = if code == IO_ENOENT || code == IO_UNKNOWN {
            if !ctxt.is_null() && (*ctxt).validate == 0 { ERR_WARNING } else { ERR_ERROR }
        } else {
            ERR_FATAL
        };
        let errstr = message_for(code).to_bytes();
        let msg = match uri {
            None => cat(&[errstr, b"\n"]),
            Some(u) => cat(&[b"failed to load \"", u, b"\": ", errstr, b"\n"]),
        };
        ctx_err(ctxt, null_mut(), FROM_IO, code, level, uri, None, None, 0, &msg);
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCtxtNewInputFromUrl(
    ctxt: *mut ParserCtxt,
    url: *const c_char,
    _public_id: *const c_char,
    encoding: *const c_char,
    _flags: c_int,
) -> *mut ParserInput {
    unsafe { file_input(ctxt, url, encoding) }
}

unsafe extern "C" {
    fn read(fd: c_int, buf: *mut c_void, n: usize) -> isize;
}

fn read_fd(fd: c_int) -> Option<Vec<u8>> {
    let mut out = Vec::new();
    let mut buf = [0u8; 65536];
    loop {
        let n = unsafe { read(fd, buf.as_mut_ptr() as *mut c_void, buf.len()) };
        if n < 0 {
            return None;
        }
        if n == 0 {
            return Some(out);
        }
        out.extend_from_slice(&buf[..n as usize]);
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCtxtNewInputFromFd(ctxt: *mut ParserCtxt, url: *const c_char, fd: c_int, encoding: *const c_char, _flags: c_int) -> *mut ParserInput {
    unsafe {
        match read_fd(fd) {
            Some(data) => {
                let i = new_input(copt(url as *const XChar), data.as_ptr(), data.len(), false);
                set_input_encoding(i, encoding);
                i
            }
            None => {
                io_err(ctxt, IO_UNKNOWN, copt(url as *const XChar));
                null_mut()
            }
        }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCtxtPushInput(ctxt: *mut ParserCtxt, input: *mut ParserInput) -> c_int {
    unsafe {
        if ctxt.is_null() || input.is_null() {
            return -1;
        }
        let c = &mut *ctxt;
        if c.inputNr >= c.inputMax {
            let n = (c.inputMax.max(2) * 2) as usize;
            let p = xrealloc(c.inputTab as *mut c_void, n * std::mem::size_of::<*mut ParserInput>()) as *mut *mut ParserInput;
            if p.is_null() {
                return -1;
            }
            c.inputTab = p;
            c.inputMax = n as c_int;
        }
        *c.inputTab.add(c.inputNr as usize) = input;
        c.inputNr += 1;
        c.input = input;
        c.inputNr - 1
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCtxtPopInput(ctxt: *mut ParserCtxt) -> *mut ParserInput {
    unsafe {
        if ctxt.is_null() || (*ctxt).inputNr <= 0 {
            return null_mut();
        }
        let c = &mut *ctxt;
        c.inputNr -= 1;
        let r = *c.inputTab.add(c.inputNr as usize);
        *c.inputTab.add(c.inputNr as usize) = null_mut();
        c.input = if c.inputNr > 0 { *c.inputTab.add(c.inputNr as usize - 1) } else { null_mut() };
        r
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn inputPush(ctxt: *mut ParserCtxt, input: *mut ParserInput) -> c_int {
    unsafe { xmlCtxtPushInput(ctxt, input) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn inputPop(ctxt: *mut ParserCtxt) -> *mut ParserInput {
    unsafe { xmlCtxtPopInput(ctxt) }
}

unsafe fn free_inputs(ctxt: *mut ParserCtxt) {
    unsafe {
        loop {
            let i = xmlCtxtPopInput(ctxt);
            if i.is_null() {
                break;
            }
            xmlFreeInputStream(i);
        }
    }
}

// --- the context -----------------------------------------------------------------------

unsafe fn init_ctxt(ctxt: *mut ParserCtxt, sax: *const SaxHandler, user: *mut c_void) -> c_int {
    unsafe {
        let c = &mut *ctxt;
        c.dict = xmlDictCreate();
        c.sax = xnew();
        if c.dict.is_null() || c.sax.is_null() {
            return -1;
        }
        if sax.is_null() {
            xmlSAXVersion(c.sax, 2);
            c.userData = ctxt as *mut c_void;
        } else {
            if (*sax).initialized == SAX2_MAGIC {
                *c.sax = *sax;
            } else {
                // xmlSAXHandlerV1: the fields up to `initialized`.
                let n = std::mem::offset_of!(SaxHandler, initialized) + std::mem::size_of::<c_uint>();
                std::ptr::copy_nonoverlapping(sax as *const u8, c.sax as *mut u8, n);
            }
            c.userData = if user.is_null() { ctxt as *mut c_void } else { user };
        }
        c.inputTab = xmalloc(5 * std::mem::size_of::<*mut ParserInput>()) as *mut *mut ParserInput;
        c.inputMax = 5;
        c.standalone = -1;
        c.wellFormed = 1;
        c.nsWellFormed = 1;
        c.valid = 1;
        c.options = PARSE_NODICT;
        let g = &*globals();
        c.loadsubset = g.load_ext_dtd;
        if c.loadsubset != 0 {
            c.options |= PARSE_DTDLOAD;
        }
        c.validate = g.do_validity;
        if c.validate != 0 {
            c.options |= PARSE_DTDVALID;
        }
        c.pedantic = g.pedantic;
        if c.pedantic != 0 {
            c.options |= PARSE_PEDANTIC;
        }
        c.keepBlanks = g.keep_blanks;
        if c.keepBlanks == 0 {
            (*c.sax).ignorableWhitespace = Some(xmlSAX2IgnorableWhitespace);
            c.options |= PARSE_NOBLANKS;
        }
        c.replaceEntities = g.substitute;
        if c.replaceEntities != 0 {
            c.options |= PARSE_NOENT;
        }
        if g.get_warnings == 0 {
            c.options |= PARSE_NOWARNING;
        }
        c.vctxt.flags = 1;
        c.vctxt.userData = ctxt as *mut c_void;
        c.vctxt.error = Some(as_msg_fn(xmlParserValidityError));
        c.vctxt.warning = Some(as_msg_fn(xmlParserValidityWarning));
        c.linenumbers = g.line_numbers;
        c.input_id = 1;
        c.maxAmpl = 5;
        c.st = Box::into_raw(State::new());
        0
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewSAXParserCtxt(sax: *const SaxHandler, user: *mut c_void) -> *mut ParserCtxt {
    unsafe {
        let ctxt: *mut ParserCtxt = xnew();
        if ctxt.is_null() {
            return ctxt;
        }
        if init_ctxt(ctxt, sax, user) < 0 {
            xmlFreeParserCtxt(ctxt);
            return null_mut();
        }
        ctxt
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlNewParserCtxt() -> *mut ParserCtxt {
    unsafe { xmlNewSAXParserCtxt(null(), null_mut()) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlInitParserCtxt(ctxt: *mut ParserCtxt) -> c_int {
    if ctxt.is_null() {
        return -1;
    }
    unsafe { init_ctxt(ctxt, null(), null_mut()) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlFreeParserCtxt(ctxt: *mut ParserCtxt) {
    unsafe {
        if ctxt.is_null() {
            return;
        }
        free_inputs(ctxt);
        let c = &mut *ctxt;
        xfree(c.inputTab as *mut c_void);
        xfree(c.version as *mut c_void);
        xfree(c.encoding as *mut c_void);
        xfree(c.extSubURI as *mut c_void);
        xfree(c.extSubSystem as *mut c_void);
        xfree(c.directory as *mut c_void);
        xfree(c.sax as *mut c_void);
        if !c.dict.is_null() {
            xmlDictFree(c.dict);
        }
        reset_error(&mut c.lastError);
        if !c.st.is_null() {
            drop(Box::from_raw(c.st));
        }
        xfree(ctxt as *mut c_void);
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCtxtReset(ctxt: *mut ParserCtxt) {
    unsafe {
        if ctxt.is_null() {
            return;
        }
        free_inputs(ctxt);
        let c = &mut *ctxt;
        c.node = null_mut();
        c.nodeNr = 0;
        c.nameNr = 0;
        c.name = null();
        c.nsNr = 0;
        for p in [&mut c.version, &mut c.encoding, &mut c.extSubURI, &mut c.extSubSystem] {
            xfree(*p as *mut c_void);
            *p = null_mut();
        }
        xfree(c.directory as *mut c_void);
        c.directory = null_mut();
        if !c.myDoc.is_null() {
            xmlFreeDoc(c.myDoc);
        }
        c.myDoc = null_mut();
        c.standalone = -1;
        c.hasExternalSubset = 0;
        c.hasPErefs = 0;
        c.html = (c.html != 0) as c_int;
        c.wellFormed = 1;
        c.nsWellFormed = 1;
        c.disableSAX = 0;
        c.valid = 1;
        c.record_info = 0;
        c.inSubset = 0;
        c.errNo = ERR_OK;
        c.depth = 0;
        c.sizeentities = 0;
        c.sizeentcopy = 0;
        c.nbErrors = 0;
        c.nbWarnings = 0;
        c.intSubName = null();
        if c.lastError.code != ERR_OK {
            reset_error(&mut c.lastError);
        }
        if !c.st.is_null() {
            (*c.st).clear();
        }
    }
}

unsafe fn set_options(ctxt: *mut ParserCtxt, options: c_int, keep: c_int) -> c_int {
    unsafe {
        if ctxt.is_null() {
            return -1;
        }
        let all = PARSE_RECOVER
            | PARSE_NOENT
            | PARSE_DTDLOAD
            | PARSE_DTDATTR
            | PARSE_DTDVALID
            | PARSE_NOERROR
            | PARSE_NOWARNING
            | PARSE_PEDANTIC
            | PARSE_NOBLANKS
            | PARSE_SAX1
            | (1 << 11)
            | PARSE_NODICT
            | PARSE_NSCLEAN
            | PARSE_NOCDATA
            | (1 << 16)
            | PARSE_OLD10
            | PARSE_HUGE
            | PARSE_OLDSAX
            | PARSE_IGNORE_ENC
            | PARSE_BIG_LINES
            | PARSE_NO_XXE
            | (1 << 24)
            | (1 << 25)
            | (1 << 26);
        let c = &mut *ctxt;
        c.options = (c.options & keep) | (options & all);
        c.recovery = (options & PARSE_RECOVER != 0) as c_int;
        c.replaceEntities = (options & PARSE_NOENT != 0) as c_int;
        c.loadsubset = if options & PARSE_DTDLOAD != 0 { DETECT_IDS } else { 0 };
        c.loadsubset |= if options & PARSE_DTDATTR != 0 { COMPLETE_ATTRS } else { 0 };
        c.loadsubset |= if options & PARSE_SKIP_IDS != 0 { SKIP_IDS } else { 0 };
        c.validate = (options & PARSE_DTDVALID != 0) as c_int;
        c.pedantic = (options & PARSE_PEDANTIC != 0) as c_int;
        c.keepBlanks = (options & PARSE_NOBLANKS == 0) as c_int;
        c.dictNames = (options & PARSE_NODICT == 0) as c_int;
        options & !all
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCtxtSetOptions(ctxt: *mut ParserCtxt, options: c_int) -> c_int {
    unsafe { set_options(ctxt, options, 0) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCtxtUseOptions(ctxt: *mut ParserCtxt, options: c_int) -> c_int {
    let keep = PARSE_NOERROR
        | PARSE_NOWARNING
        | (1 << 11)
        | PARSE_NSCLEAN
        | PARSE_NOCDATA
        | (1 << 16)
        | PARSE_OLD10
        | PARSE_HUGE
        | PARSE_OLDSAX
        | PARSE_IGNORE_ENC
        | PARSE_BIG_LINES;
    unsafe { set_options(ctxt, options, keep) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCtxtGetOptions(ctxt: *mut ParserCtxt) -> c_int {
    if ctxt.is_null() { -1 } else { unsafe { (*ctxt).options } }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCtxtSetErrorHandler(ctxt: *mut ParserCtxt, handler: StructuredErrorF, data: *mut c_void) {
    unsafe {
        if ctxt.is_null() {
            return;
        }
        (*ctxt).errorHandler = handler;
        (*ctxt).errorCtxt = data;
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCtxtGetLastError(ctxt: *mut c_void) -> *const XmlError {
    let c = ctxt as *mut ParserCtxt;
    unsafe {
        if c.is_null() || (*c).lastError.code == ERR_OK {
            return null();
        }
        &raw const (*c).lastError
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCtxtResetLastError(ctxt: *mut c_void) {
    let c = ctxt as *mut ParserCtxt;
    unsafe {
        if c.is_null() {
            return;
        }
        (*c).errNo = ERR_OK;
        if (*c).lastError.code != ERR_OK {
            reset_error(&mut (*c).lastError);
        }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCtxtGetStatus(ctxt: *mut ParserCtxt) -> c_int {
    unsafe {
        if ctxt.is_null() {
            return 1 << 3;
        }
        let mut r = 0;
        if (*ctxt).wellFormed == 0 {
            r |= 1;
        }
        if (*ctxt).nsWellFormed == 0 {
            r |= 2;
        }
        if (*ctxt).valid == 0 {
            r |= 4;
        }
        if catastrophic(&(*ctxt).lastError) {
            r |= 8;
        }
        r
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCtxtSetMaxAmplification(ctxt: *mut ParserCtxt, max: c_uint) {
    unsafe {
        if !ctxt.is_null() {
            (*ctxt).maxAmpl = max;
        }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlStopParser(ctxt: *mut ParserCtxt) {
    unsafe {
        if ctxt.is_null() {
            return;
        }
        (*ctxt).disableSAX = 2;
        if (*ctxt).errNo == ERR_OK {
            (*ctxt).errNo = ERR_USER_STOP;
            (*ctxt).lastError.code = ERR_USER_STOP;
            (*ctxt).wellFormed = 0;
        }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCtxtIsHtml(_ctxt: *mut ParserCtxt) -> c_int {
    0
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCtxtIsStopped(ctxt: *mut ParserCtxt) -> c_int {
    if ctxt.is_null() { 0 } else { unsafe { ((*ctxt).disableSAX > 1) as c_int } }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCtxtGetDocument(ctxt: *mut ParserCtxt) -> *mut Doc {
    unsafe {
        if ctxt.is_null() {
            return null_mut();
        }
        let c = &mut *ctxt;
        let doc;
        if c.wellFormed != 0 || ((c.recovery != 0 || c.html != 0) && !catastrophic(&c.lastError)) {
            doc = c.myDoc;
        } else {
            if c.errNo == ERR_OK {
                fatal(ctxt, ERR_INTERNAL_ERROR, b"unknown error\n", None);
            }
            doc = null_mut();
            xmlFreeDoc(c.myDoc);
        }
        c.myDoc = null_mut();
        doc
    }
}

unsafe fn initialize_late(ctxt: *mut ParserCtxt) {
    unsafe {
        let c = &mut *ctxt;
        let sax = c.sax;
        c.sax2 = 0;
        if c.options & PARSE_SAX1 == 0
            && !sax.is_null()
            && (*sax).initialized == SAX2_MAGIC
            && ((*sax).startElementNs.is_some() || (*sax).endElementNs.is_some() || ((*sax).startElement.is_none() && (*sax).endElement.is_none()))
        {
            c.sax2 = 1;
        }
        c.str_xml = dict(ctxt, b"xml");
        c.str_xmlns = dict(ctxt, b"xmlns");
        c.str_xml_ns = dict(ctxt, XML_XML_NAMESPACE);
    }
}

// --- helpers SAX2.c uses -----------------------------------------------------------------

/// The base for an entity's system id: the input's file name.
pub unsafe fn base_uri(ctxt: *mut ParserCtxt) -> Option<Vec<u8>> {
    unsafe {
        if !(*ctxt).input.is_null() {
            if let Some(f) = copt((*(*ctxt).input).filename as *const XChar) {
                return Some(f.to_vec());
            }
        }
        copt((*ctxt).directory as *const XChar).map(|d| d.to_vec())
    }
}

/// `xmlBuildURI`, for what entity declarations need: `uri` resolved
/// against `base`.
pub fn build_uri(uri: &[u8], base: Option<&[u8]>) -> Vec<u8> {
    let (_, scheme) = uri_check(uri);
    let Some(base) = base else { return uri.to_vec() };
    if scheme || uri.starts_with(b"/") || uri.is_empty() {
        return uri.to_vec();
    }
    match base.iter().rposition(|&c| c == b'/') {
        Some(k) => {
            let mut dir = base[..=k].to_vec();
            if dir.starts_with(b"./") {
                dir.drain(..2);
            }
            let mut u = uri;
            while let Some(r) = u.strip_prefix(b"./") {
                u = r;
            }
            dir.extend_from_slice(u);
            dir
        }
        None => uri.to_vec(),
    }
}

/// `xmlPathToURI`: a file name as the document's URL.
pub fn path_to_uri(path: &[u8]) -> Vec<u8> {
    path.to_vec()
}

/// The encoding the input was read in, for `doc->encoding` when the
/// document did not declare one.
pub unsafe fn actual_encoding(ctxt: *mut ParserCtxt) -> Option<Vec<u8>> {
    unsafe {
        if !(*ctxt).encoding.is_null() {
            return Some(cbytes((*ctxt).encoding).to_vec());
        }
        let input = (*ctxt).input;
        if !input.is_null() && !(*input).encoding.is_null() {
            return Some(cbytes((*input).encoding).to_vec());
        }
        // An encoding found from a byte order mark is not reported
        // (xmlGetActualEncoding with XML_INPUT_AUTO_ENCODING).
        None
    }
}

// --- parsing a document ---------------------------------------------------------------

/// The input in UTF-8 when an encoding was given for it that overrides its
/// own declaration (`xmlCtxtReadMemory`'s `encoding`): the bytes with the
/// declaration's encoding replaced. `None` to read the bytes as they are.
fn override_encoding(raw: &[u8], enc: &[u8]) -> Option<Vec<u8>> {
    let e = enc.to_ascii_uppercase();
    let body: Vec<u8> = match &e[..] {
        b"UTF-8" | b"UTF8" => return None,
        b"ISO-8859-1" | b"LATIN1" | b"ISO_8859-1" | b"ISO-LATIN-1" => raw.iter().flat_map(|&b| char::from(b).to_string().into_bytes()).collect(),
        b"US-ASCII" | b"ASCII" => return None,
        _ => return None,
    };
    Some(rewrite_decl_encoding(body))
}

/// `body` with its XML declaration's encoding named UTF-8: the text is
/// UTF-8 now.
fn rewrite_decl_encoding(body: Vec<u8>) -> Vec<u8> {
    let f = || -> Option<Vec<u8>> {
        if !body.starts_with(b"<?xml") {
            return None;
        }
        let end = body.windows(2).position(|w| w == b"?>")?;
        let decl = &body[..end];
        let k = decl.windows(8).position(|w| w == b"encoding")?;
        let rest = &decl[k + 8..];
        let q = rest.iter().position(|&c| c == b'"' || c == b'\'')?;
        let quote = rest[q];
        let close = rest[q + 1..].iter().position(|&c| c == quote)?;
        let mut out = body[..k].to_vec();
        out.extend_from_slice(b"encoding=\"UTF-8\"");
        out.extend_from_slice(&rest[q + 1 + close + 1..]);
        out.extend_from_slice(&body[end..]);
        Some(out)
    };
    f().unwrap_or(body)
}

/// `xmlParseDocument` over the context's input.
unsafe fn parse_document(ctxt: *mut ParserCtxt) -> c_int {
    unsafe {
        if ctxt.is_null() || (*ctxt).input.is_null() {
            return -1;
        }
        initialize_late(ctxt);
        let c = ctxt;
        if !(*c).sax.is_null() {
            if let Some(f) = (*(*c).sax).setDocumentLocator {
                f((*c).userData, &xmlDefaultSAXLocator as *const SaxLocator as *mut SaxLocator);
            }
        }
        let input = (*c).input;
        let raw: &[u8] = input_bytes(input);
        let (rb, rc, re) = ((*input).base, (*input).cur, (*input).end);
        let content = if raw.starts_with(&[0xEF, 0xBB, 0xBF]) { &raw[3..] } else { raw };
        if content.is_empty() || (content.len() >= 2 && content[..2] == [0xFF, 0xFE] || content.len() >= 2 && content[..2] == [0xFE, 0xFF]) && content.len() == 2 {
            fatal(c, ERR_DOCUMENT_EMPTY, b"Document is empty\n", None);
            return -1;
        }
        let converted = if (*c).options & PARSE_IGNORE_ENC == 0 {
            copt((*input).encoding).and_then(|e| override_encoding(raw, e))
        } else {
            None
        };
        // UTF-16, known by its byte order mark or first characters
        // (xmlDetectEncoding): decoded here, and read as UTF-8 with the
        // encoding it declares kept for the document (libxml2 takes
        // UTF-16LE and UTF-16BE after a byte order mark, and no mark).
        st(c).declared = None;
        let converted = converted.or_else(|| {
            let (le, from) = if raw.starts_with(&[0x3C, 0, 0x3F, 0]) {
                (true, 0)
            } else if raw.starts_with(&[0, 0x3C, 0, 0x3F]) {
                (false, 0)
            } else if raw.starts_with(&[0xFF, 0xFE, 0x3C, 0]) {
                (true, 2)
            } else if raw.starts_with(&[0xFE, 0xFF, 0, 0x3C]) {
                (false, 2)
            } else {
                return None;
            };
            let units = raw[from..].chunks_exact(2).map(|p| if le { u16::from_le_bytes([p[0], p[1]]) } else { u16::from_be_bytes([p[0], p[1]]) });
            let text: String = char::decode_utf16(units).map(|r| r.unwrap_or('\u{FFFD}')).collect();
            let body = text.into_bytes();
            let decl_end = if body.starts_with(b"<?xml") { body.windows(2).position(|w| w == b"?>") } else { None };
            st(c).declared = decl_end.and_then(|e| decl_attr(&body[..e], b"encoding"));
            Some(rewrite_decl_encoding(body))
        });
        let bytes: &[u8] = converted.as_deref().unwrap_or(raw);
        st(c).at = (0, 1, 1);
        match crate::api::parse(bytes) {
            Ok(doc) => {
                let text = doc.text();
                (*input).base = text.as_ptr();
                (*input).cur = text.as_ptr();
                (*input).end = text.as_ptr().add(text.len());
                let mut w = Walk::new(c, &doc);
                let toks = doc.toks(Src::Doc);
                let root = w.prolog();
                if root < toks.len() && toks[root].kind == Kind::STag {
                    let close = toks[root].c();
                    w.content(Src::Doc, root, close + 1);
                    let mut i = close + 1;
                    while i < toks.len() {
                        let t = toks[i];
                        match t.kind {
                            Kind::Comment => w.comment(Src::Doc, t),
                            Kind::PI => {
                                w.pi(Src::Doc, t, toks[i + 1]);
                                i += 1;
                            }
                            _ => {}
                        }
                        i += 1;
                    }
                    w.at(text.len());
                } else if (*c).wellFormed != 0 {
                    fatal(c, ERR_DOCUMENT_EMPTY, b"Start tag expected, '<' not found\n", None);
                }
                (*input).base = rb;
                (*input).cur = re;
                (*input).end = re;
                let _ = rc;
            }
            Err(e) => {
                malformed(c, bytes, &e);
                (*input).base = rb;
                (*input).cur = re;
                (*input).end = re;
            }
        }
        finish_document(c);
        if (*c).wellFormed == 0 {
            (*c).valid = 0;
            return -1;
        }
        0
    }
}

unsafe fn finish_document(c: *mut ParserCtxt) {
    unsafe {
        if !(*c).sax.is_null() {
            if let Some(f) = (*(*c).sax).endDocument {
                f((*c).userData);
            }
        }
        let doc = (*c).myDoc;
        if !doc.is_null() && copt((*doc).version) == Some(SAX_COMPAT) {
            xmlFreeDoc(doc);
            (*c).myDoc = null_mut();
        }
    }
}

/// A document the verified parser rejected: what libxml2 would report
/// first, as one fatal error at the place it was found.
unsafe fn malformed(c: *mut ParserCtxt, bytes: &[u8], e: &crate::api::Error) {
    unsafe {
        let text = bytes;
        let off = e.offset.min(text.len());
        // libxml2 has started the document unless the XML declaration is
        // what is wrong.
        let decl_end = if text.starts_with(b"<?xml") { text.windows(2).position(|w| w == b"?>").map_or(text.len(), |p| p + 2) } else { 0 };
        if off >= decl_end {
            if text.starts_with(b"<?xml") {
                if let Some(v) = decl_attr(&text[..decl_end], b"version") {
                    (*c).version = xstrdup(&v);
                }
                if let Some(v) = decl_attr(&text[..decl_end], b"encoding") {
                    (*c).encoding = xstrdup(&v);
                }
            } else {
                (*c).version = xstrdup(b"1.0");
            }
            if let Some(f) = handler(c).and_then(|h| h.startDocument) {
                f((*c).userData);
            }
        }
        let input = (*c).input;
        if !input.is_null() && e.kind == crate::api::ErrorKind::Syntax {
            (*input).base = text.as_ptr();
            (*input).end = text.as_ptr().add(text.len());
            (*input).cur = text.as_ptr().add(off);
            (*input).line = e.line as c_int;
            (*input).col = e.column as c_int;
            if let Some((_, _, _, at)) = duplicate_attribute(text, off) {
                let (line, col) = line_col(text, at);
                (*input).cur = text.as_ptr().add(at);
                (*input).line = line;
                (*input).col = col;
            }
        }
        let (code, msg, s1) = classify(text, off, e);
        ctx_err(c, null_mut(), FROM_PARSER, code, ERR_FATAL, s1.as_deref(), None, None, 0, &msg);
    }
}

/// A pseudo-attribute of an XML declaration.
pub fn decl_attr(decl: &[u8], name: &[u8]) -> Option<Vec<u8>> {
    let k = decl.windows(name.len()).position(|w| w == name)?;
    let rest = &decl[k + name.len()..];
    let q = rest.iter().position(|&c| c == b'"' || c == b'\'')?;
    let quote = rest[q];
    let close = rest[q + 1..].iter().position(|&c| c == quote)?;
    Some(rest[q + 1..q + 1 + close].to_vec())
}

/// The open elements at `off`: (name, line), by a scan of the tags before.
fn open_elements(text: &[u8], off: usize) -> Vec<(Vec<u8>, usize)> {
    let mut stack: Vec<(Vec<u8>, usize)> = Vec::new();
    let mut i = 0;
    let mut line = 1;
    let end = off.min(text.len());
    while i < end {
        let ch = text[i];
        if ch == b'\n' {
            line += 1;
        }
        if ch != b'<' {
            i += 1;
            continue;
        }
        let rest = &text[i..end];
        let skip = |pat: &[u8], from: usize| text[from..end].windows(pat.len()).position(|w| w == pat).map(|p| from + p + pat.len());
        let next = if rest.starts_with(b"<!--") {
            skip(b"-->", i + 4)
        } else if rest.starts_with(b"<![CDATA[") {
            skip(b"]]>", i + 9)
        } else if rest.starts_with(b"<?") {
            skip(b"?>", i + 2)
        } else if rest.starts_with(b"<!") {
            // A declaration, with its internal subset.
            let mut depth = 0;
            let mut j = i + 2;
            let mut q = 0u8;
            loop {
                if j >= end {
                    break None;
                }
                let x = text[j];
                if q != 0 {
                    if x == q {
                        q = 0;
                    }
                } else if x == b'"' || x == b'\'' {
                    q = x;
                } else if x == b'[' {
                    depth += 1;
                } else if x == b']' {
                    depth -= 1;
                } else if x == b'>' && depth <= 0 {
                    break Some(j + 1);
                }
                j += 1;
            }
        } else if rest.starts_with(b"</") {
            stack.pop();
            skip(b">", i + 2)
        } else {
            let a = i + 1;
            let mut b = a;
            while b < end && !is_blank(text[b]) && text[b] != b'>' && text[b] != b'/' {
                b += 1;
            }
            let name = text[a..b].to_vec();
            let l = line;
            let mut j = b;
            let mut q = 0u8;
            let mut empty = false;
            let close = loop {
                if j >= end {
                    break None;
                }
                let x = text[j];
                if q != 0 {
                    if x == q {
                        q = 0;
                    }
                } else if x == b'"' || x == b'\'' {
                    q = x;
                } else if x == b'>' {
                    empty = j > 0 && text[j - 1] == b'/';
                    break Some(j + 1);
                }
                j += 1;
            };
            if !empty {
                stack.push((name, l));
            }
            close
        };
        match next {
            Some(n) => {
                line += text[i + 1..n.min(end)].iter().filter(|&&x| x == b'\n').count();
                i = n;
            }
            None => break,
        }
    }
    stack
}

/// The line and column of `off` (columns in characters, from 1).
/// Bytes of `b` equal to `\n`, eight at a time.
fn count_newlines(b: &[u8]) -> usize {
    count_where(b, |w| {
        let x = w ^ 0x0A0A_0A0A_0A0A_0A0A;
        // High bit of each byte set where x's byte is zero.
        !(((x & 0x7F7F_7F7F_7F7F_7F7F).wrapping_add(0x7F7F_7F7F_7F7F_7F7F)) | x | 0x7F7F_7F7F_7F7F_7F7F)
    }, |c| c == b'\n')
}

/// UTF-8 continuation bytes (`10xxxxxx`) in `b`, eight at a time.
fn count_continuations(b: &[u8]) -> usize {
    count_where(b, |w| w & !(w << 1) & 0x8080_8080_8080_8080, |c| c & 0xC0 == 0x80)
}

#[inline]
fn count_where(b: &[u8], mask: impl Fn(u64) -> u64, one: impl Fn(u8) -> bool) -> usize {
    let mut c = b.chunks_exact(8);
    let mut n = 0usize;
    for w in &mut c {
        n += (mask(u64::from_le_bytes(w.try_into().unwrap())) & 0x8080_8080_8080_8080).count_ones() as usize;
    }
    n + c.remainder().iter().filter(|&&x| one(x)).count()
}

fn line_col(text: &[u8], off: usize) -> (c_int, c_int) {
    let mut line = 1;
    let mut col = 1;
    for &c in &text[..off.min(text.len())] {
        if c == b'\n' {
            line += 1;
            col = 1;
        } else if c & 0xC0 != 0x80 {
            col += 1;
        }
    }
    (line, col)
}

/// A start tag at `off` that names an attribute twice: libxml2's error for
/// it, which it reports where the tag's attributes end.
fn duplicate_attribute(text: &[u8], off: usize) -> Option<(c_int, Vec<u8>, Option<Vec<u8>>, usize)> {
    let rest = text.get(off..)?;
    if !rest.starts_with(b"<") || rest.get(1).is_none_or(|c| b"/!?".contains(c)) {
        return None;
    }
    let mut i = 1;
    while i < rest.len() && !is_blank(rest[i]) && rest[i] != b'>' && rest[i] != b'/' {
        i += 1;
    }
    let mut seen: Vec<&[u8]> = Vec::new();
    loop {
        while i < rest.len() && is_blank(rest[i]) {
            i += 1;
        }
        let a = i;
        while i < rest.len() && !is_blank(rest[i]) && !b"=>/".contains(&rest[i]) {
            i += 1;
        }
        if a == i {
            return None;
        }
        let name = &rest[a..i];
        while i < rest.len() && is_blank(rest[i]) {
            i += 1;
        }
        if rest.get(i) != Some(&b'=') {
            return None;
        }
        i += 1;
        while i < rest.len() && is_blank(rest[i]) {
            i += 1;
        }
        let q = *rest.get(i)?;
        if q != b'"' && q != b'\'' {
            return None;
        }
        let close = rest[i + 1..].iter().position(|&c| c == q)?;
        i += close + 2;
        if seen.contains(&name) {
            // Reported at the end of the attributes.
            let mut j = i;
            while j < rest.len() && rest[j] != b'>' && rest[j] != b'/' {
                j += 1;
            }
            let msg = cat(&[b"Attribute ", name, b" redefined\n"]);
            return Some((ERR_ATTRIBUTE_REDEFINED, msg, Some(name.to_vec()), off + j));
        }
        seen.push(name);
    }
}

/// The code and message libxml2 gives the first error in a document that
/// is not well-formed, as near as a look at the text can tell.
fn classify(text: &[u8], off: usize, e: &crate::api::Error) -> (c_int, Vec<u8>, Option<Vec<u8>>) {
    if e.kind == crate::api::ErrorKind::Encoding {
        let b: Vec<String> = (0..4).map(|k| format!("0x{:02X}", text.get(off + k).copied().unwrap_or(0))).collect();
        if std::str::from_utf8(&text[off.min(text.len())..(off + 4).min(text.len())]).is_err() {
            let msg = format!("Input is not proper UTF-8, indicate encoding !\nBytes: {} {} {} {}\n", b[0], b[1], b[2], b[3]);
            return (ERR_INVALID_ENCODING, msg.into_bytes(), None);
        }
        let cp = crate::chars::ex_cp_at_hi(text, off).map_or(text.get(off).copied().unwrap_or(0) as u32, |x| x.0);
        return (ERR_INVALID_CHAR, format!("PCDATA invalid Char value {cp}\n").into_bytes(), None);
    }
    let open = open_elements(text, off);
    let root_done = {
        // Whether the root element has ended before `off`.
        let mut seen_root = false;
        let mut i = 0;
        while i < off && i < text.len() {
            if text[i] == b'<' && text.get(i + 1).is_some_and(|c| c.is_ascii_alphabetic() || *c == b'_' || *c >= 0x80 || *c == b':') {
                seen_root = true;
                break;
            }
            i += 1;
        }
        seen_root && open.is_empty()
    };
    let rest = &text[off.min(text.len())..];
    if off >= text.len() {
        if let Some((name, line)) = open.last() {
            let msg = cat(&[b"Premature end of data in tag ", name, format!(" line {line}\n").as_bytes()]);
            return (ERR_TAG_NOT_FINISHED, msg, Some(name.clone()));
        }
        if !root_done {
            return (ERR_DOCUMENT_EMPTY, b"Start tag expected, '<' not found\n".to_vec(), None);
        }
    }
    if root_done && !rest.is_empty() {
        return (ERR_DOCUMENT_END, b"Extra content at the end of the document\n".to_vec(), None);
    }
    if rest.starts_with(b"</") {
        if let Some((name, line)) = open.last() {
            let b = rest[2..].iter().position(|&c| is_blank(c) || c == b'>').map_or(rest.len(), |p| p + 2);
            let got = &rest[2..b];
            let msg = cat(&[b"Opening and ending tag mismatch: ", name, format!(" line {line} and ").as_bytes(), got, b"\n"]);
            return (ERR_TAG_NAME_MISMATCH, msg, Some(name.clone()));
        }
    }
    if let Some((code, msg, s1, _)) = duplicate_attribute(text, off) {
        return (code, msg, s1);
    }
    if rest.starts_with(b"&") {
        return (ERR_ENTITYREF_SEMICOL_MISSING, b"EntityRef: expecting ';'\n".to_vec(), None);
    }
    if rest.starts_with(b"<") {
        return (ERR_NAME_REQUIRED, b"StartTag: invalid element name\n".to_vec(), None);
    }
    (ERR_NOT_WELL_BALANCED, b"chunk is not well balanced\n".to_vec(), None)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlParseDocument(ctxt: *mut ParserCtxt) -> c_int {
    unsafe { parse_document(ctxt) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCtxtParseDocument(ctxt: *mut ParserCtxt, input: *mut ParserInput) -> *mut Doc {
    unsafe {
        if ctxt.is_null() || input.is_null() {
            if !ctxt.is_null() {
                fatal(ctxt, ERR_ARGUMENT, b"Invalid argument\n", None);
            }
            xmlFreeInputStream(input);
            return null_mut();
        }
        free_inputs(ctxt);
        if xmlCtxtPushInput(ctxt, input) < 0 {
            xmlFreeInputStream(input);
            return null_mut();
        }
        parse_document(ctxt);
        let r = xmlCtxtGetDocument(ctxt);
        free_inputs(ctxt);
        r
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCtxtReadMemory(ctxt: *mut ParserCtxt, buf: *const c_char, size: c_int, url: *const c_char, encoding: *const c_char, options: c_int) -> *mut Doc {
    unsafe {
        if ctxt.is_null() || size < 0 {
            return null_mut();
        }
        xmlCtxtReset(ctxt);
        xmlCtxtUseOptions(ctxt, options);
        let i = xmlCtxtNewInputFromMemory(ctxt, url, buf as *const c_void, size as usize, encoding, BUF_STATIC);
        if i.is_null() {
            return null_mut();
        }
        xmlCtxtParseDocument(ctxt, i)
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCtxtReadDoc(ctxt: *mut ParserCtxt, s: *const XChar, url: *const c_char, encoding: *const c_char, options: c_int) -> *mut Doc {
    unsafe {
        if ctxt.is_null() {
            return null_mut();
        }
        xmlCtxtReset(ctxt);
        xmlCtxtUseOptions(ctxt, options);
        let i = xmlCtxtNewInputFromString(ctxt, url, s as *const c_char, encoding, BUF_STATIC);
        if i.is_null() {
            return null_mut();
        }
        xmlCtxtParseDocument(ctxt, i)
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCtxtReadFile(ctxt: *mut ParserCtxt, filename: *const c_char, encoding: *const c_char, options: c_int) -> *mut Doc {
    unsafe {
        if ctxt.is_null() {
            return null_mut();
        }
        xmlCtxtReset(ctxt);
        xmlCtxtUseOptions(ctxt, options);
        let i = file_input(ctxt, filename, encoding);
        if i.is_null() {
            return null_mut();
        }
        xmlCtxtParseDocument(ctxt, i)
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCtxtReadFd(ctxt: *mut ParserCtxt, fd: c_int, url: *const c_char, encoding: *const c_char, options: c_int) -> *mut Doc {
    unsafe {
        if ctxt.is_null() {
            return null_mut();
        }
        xmlCtxtReset(ctxt);
        xmlCtxtUseOptions(ctxt, options);
        let i = xmlCtxtNewInputFromFd(ctxt, url, fd, encoding, 0);
        if i.is_null() {
            return null_mut();
        }
        xmlCtxtParseDocument(ctxt, i)
    }
}

/// A fresh context, `f` on it, the context freed.
unsafe fn with_ctxt(options: c_int, f: impl FnOnce(*mut ParserCtxt) -> *mut ParserInput) -> *mut Doc {
    unsafe {
        let ctxt = xmlNewParserCtxt();
        if ctxt.is_null() {
            return null_mut();
        }
        xmlCtxtUseOptions(ctxt, options);
        let i = f(ctxt);
        let doc = if i.is_null() { null_mut() } else { xmlCtxtParseDocument(ctxt, i) };
        xmlFreeParserCtxt(ctxt);
        doc
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlReadMemory(buf: *const c_char, size: c_int, url: *const c_char, encoding: *const c_char, options: c_int) -> *mut Doc {
    if size < 0 {
        return null_mut();
    }
    unsafe { with_ctxt(options, |c| xmlCtxtNewInputFromMemory(c, url, buf as *const c_void, size as usize, encoding, BUF_STATIC)) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlReadDoc(s: *const XChar, url: *const c_char, encoding: *const c_char, options: c_int) -> *mut Doc {
    unsafe { with_ctxt(options, |c| xmlCtxtNewInputFromString(c, url, s as *const c_char, encoding, BUF_STATIC)) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlReadFile(filename: *const c_char, encoding: *const c_char, options: c_int) -> *mut Doc {
    unsafe {
        with_ctxt(options, |c| {
            if !filename.is_null() && cbytes(filename as *const XChar) == b"-" {
                xmlCtxtNewInputFromFd(c, filename, 0, encoding, 0)
            } else {
                file_input(c, filename, encoding)
            }
        })
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlReadFd(fd: c_int, url: *const c_char, encoding: *const c_char, options: c_int) -> *mut Doc {
    unsafe { with_ctxt(options, |c| xmlCtxtNewInputFromFd(c, url, fd, encoding, 0)) }
}

/// The old entry points: a SAX handler, recovery, and user data.
unsafe fn sax_parse(sax: *const SaxHandler, recovery: c_int, data: *mut c_void, f: impl FnOnce(*mut ParserCtxt) -> *mut ParserInput) -> *mut Doc {
    unsafe {
        let ctxt = xmlNewSAXParserCtxt(sax, null_mut());
        if ctxt.is_null() {
            return null_mut();
        }
        if !data.is_null() {
            (*ctxt)._private = data;
        }
        if recovery != 0 {
            (*ctxt).options |= PARSE_RECOVER;
            (*ctxt).recovery = 1;
        }
        let i = f(ctxt);
        let doc = if i.is_null() { null_mut() } else { xmlCtxtParseDocument(ctxt, i) };
        xmlFreeParserCtxt(ctxt);
        doc
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAXParseFileWithData(sax: *const SaxHandler, filename: *const c_char, recovery: c_int, data: *mut c_void) -> *mut Doc {
    unsafe { sax_parse(sax, recovery, data, |c| file_input(c, filename, null())) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAXParseFile(sax: *const SaxHandler, filename: *const c_char, recovery: c_int) -> *mut Doc {
    unsafe { xmlSAXParseFileWithData(sax, filename, recovery, null_mut()) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlParseFile(filename: *const c_char) -> *mut Doc {
    unsafe { xmlSAXParseFile(null(), filename, 0) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlRecoverFile(filename: *const c_char) -> *mut Doc {
    unsafe { xmlSAXParseFile(null(), filename, 1) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAXParseMemoryWithData(sax: *const SaxHandler, buf: *const c_char, size: c_int, recovery: c_int, data: *mut c_void) -> *mut Doc {
    if size < 0 {
        return null_mut();
    }
    unsafe { sax_parse(sax, recovery, data, |c| xmlCtxtNewInputFromMemory(c, null(), buf as *const c_void, size as usize, null(), BUF_STATIC)) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAXParseMemory(sax: *const SaxHandler, buf: *const c_char, size: c_int, recovery: c_int) -> *mut Doc {
    unsafe { xmlSAXParseMemoryWithData(sax, buf, size, recovery, null_mut()) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlParseMemory(buf: *const c_char, size: c_int) -> *mut Doc {
    unsafe { xmlSAXParseMemory(null(), buf, size, 0) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlRecoverMemory(buf: *const c_char, size: c_int) -> *mut Doc {
    unsafe { xmlSAXParseMemory(null(), buf, size, 1) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAXParseDoc(sax: *const SaxHandler, s: *const XChar, recovery: c_int) -> *mut Doc {
    unsafe { sax_parse(sax, recovery, null_mut(), |c| xmlCtxtNewInputFromString(c, null(), s as *const c_char, null(), BUF_STATIC)) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlParseDoc(s: *const XChar) -> *mut Doc {
    unsafe { xmlSAXParseDoc(null(), s, 0) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlRecoverDoc(s: *const XChar) -> *mut Doc {
    unsafe { xmlSAXParseDoc(null(), s, 1) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAXUserParseFile(sax: *const SaxHandler, user: *mut c_void, filename: *const c_char) -> c_int {
    unsafe {
        let ctxt = xmlCreateFileParserCtxt(filename);
        if ctxt.is_null() {
            return -1;
        }
        if !sax.is_null() {
            if (*sax).initialized == SAX2_MAGIC {
                *(*ctxt).sax = *sax;
            } else {
                *(*ctxt).sax = SaxHandler::zero();
                let n = std::mem::offset_of!(SaxHandler, initialized) + std::mem::size_of::<c_uint>();
                std::ptr::copy_nonoverlapping(sax as *const u8, (*ctxt).sax as *mut u8, n);
            }
            (*ctxt).userData = if user.is_null() { ctxt as *mut c_void } else { user };
        }
        parse_document(ctxt);
        let ret = if (*ctxt).wellFormed != 0 { 0 } else if (*ctxt).errNo != 0 { (*ctxt).errNo } else { -1 };
        xmlFreeDoc((*ctxt).myDoc);
        (*ctxt).myDoc = null_mut();
        xmlFreeParserCtxt(ctxt);
        ret
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlSAXUserParseMemory(sax: *const SaxHandler, user: *mut c_void, buf: *const c_char, size: c_int) -> c_int {
    unsafe {
        let ctxt = xmlCreateMemoryParserCtxt(buf, size);
        if ctxt.is_null() {
            return -1;
        }
        if !sax.is_null() {
            if (*sax).initialized == SAX2_MAGIC {
                *(*ctxt).sax = *sax;
            } else {
                *(*ctxt).sax = SaxHandler::zero();
                let n = std::mem::offset_of!(SaxHandler, initialized) + std::mem::size_of::<c_uint>();
                std::ptr::copy_nonoverlapping(sax as *const u8, (*ctxt).sax as *mut u8, n);
            }
            (*ctxt).userData = if user.is_null() { ctxt as *mut c_void } else { user };
        }
        parse_document(ctxt);
        let ret = if (*ctxt).wellFormed != 0 { 0 } else if (*ctxt).errNo != 0 { (*ctxt).errNo } else { -1 };
        xmlFreeDoc((*ctxt).myDoc);
        (*ctxt).myDoc = null_mut();
        xmlFreeParserCtxt(ctxt);
        ret
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCreateURLParserCtxt(filename: *const c_char, options: c_int) -> *mut ParserCtxt {
    unsafe {
        let ctxt = xmlNewParserCtxt();
        if ctxt.is_null() {
            return ctxt;
        }
        xmlCtxtUseOptions(ctxt, options);
        let i = file_input(ctxt, filename, null());
        if i.is_null() || xmlCtxtPushInput(ctxt, i) < 0 {
            xmlFreeInputStream(i);
            xmlFreeParserCtxt(ctxt);
            return null_mut();
        }
        ctxt
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCreateFileParserCtxt(filename: *const c_char) -> *mut ParserCtxt {
    unsafe { xmlCreateURLParserCtxt(filename, 0) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCreateMemoryParserCtxt(buf: *const c_char, size: c_int) -> *mut ParserCtxt {
    unsafe {
        if size < 0 {
            return null_mut();
        }
        let ctxt = xmlNewParserCtxt();
        if ctxt.is_null() {
            return ctxt;
        }
        let i = xmlCtxtNewInputFromMemory(ctxt, null(), buf as *const c_void, size as usize, null(), 0);
        if i.is_null() || xmlCtxtPushInput(ctxt, i) < 0 {
            xmlFreeInputStream(i);
            xmlFreeParserCtxt(ctxt);
            return null_mut();
        }
        ctxt
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCreateDocParserCtxt(s: *const XChar) -> *mut ParserCtxt {
    unsafe {
        if s.is_null() {
            return null_mut();
        }
        let b = cbytes(s);
        xmlCreateMemoryParserCtxt(b.as_ptr() as *const c_char, b.len() as c_int)
    }
}

// --- the push parser -------------------------------------------------------------------

/// The push parser keeps what it is given; the document is read when the
/// last chunk comes (so its SAX calls come then too).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCreatePushParserCtxt(sax: *const SaxHandler, user: *mut c_void, chunk: *const c_char, size: c_int, filename: *const c_char) -> *mut ParserCtxt {
    unsafe {
        let ctxt = xmlNewSAXParserCtxt(sax, user);
        if ctxt.is_null() {
            return ctxt;
        }
        (*ctxt).options &= !PARSE_NODICT;
        (*ctxt).dictNames = 1;
        let i = new_input(copt(filename as *const XChar), null(), 0, true);
        if i.is_null() || xmlCtxtPushInput(ctxt, i) < 0 {
            xmlFreeInputStream(i);
            xmlFreeParserCtxt(ctxt);
            return null_mut();
        }
        let s = st(ctxt);
        s.pushed = true;
        if !chunk.is_null() && size > 0 {
            s.raw.extend_from_slice(std::slice::from_raw_parts(chunk as *const u8, size as usize));
        }
        ctxt
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlParseChunk(ctxt: *mut ParserCtxt, chunk: *const c_char, size: c_int, terminate: c_int) -> c_int {
    unsafe {
        if ctxt.is_null() || size < 0 {
            return ERR_ARGUMENT;
        }
        if (*ctxt).disableSAX > 1 {
            return (*ctxt).errNo;
        }
        let s = st(ctxt);
        if s.terminated {
            return (*ctxt).errNo;
        }
        if !chunk.is_null() && size > 0 {
            s.raw.extend_from_slice(std::slice::from_raw_parts(chunk as *const u8, size as usize));
        }
        if terminate != 0 {
            s.terminated = true;
            let input = (*ctxt).input;
            if input.is_null() {
                return ERR_INTERNAL_ERROR;
            }
            let raw = std::mem::take(&mut s.raw);
            (*input).base = raw.as_ptr();
            (*input).cur = raw.as_ptr();
            (*input).end = raw.as_ptr().add(raw.len());
            parse_document(ctxt);
            // Keep the bytes as long as the input points at them.
            st(ctxt).raw = raw;
            if (*ctxt).wellFormed == 0 && (*ctxt).errNo == ERR_OK {
                return 1;
            }
        }
        (*ctxt).errNo
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCtxtResetPush(ctxt: *mut ParserCtxt, chunk: *const c_char, size: c_int, filename: *const c_char, encoding: *const c_char) -> c_int {
    unsafe {
        if ctxt.is_null() {
            return 1;
        }
        xmlCtxtReset(ctxt);
        let i = new_input(copt(filename as *const XChar), null(), 0, true);
        if i.is_null() || xmlCtxtPushInput(ctxt, i) < 0 {
            xmlFreeInputStream(i);
            return 1;
        }
        set_input_encoding(i, encoding);
        let s = st(ctxt);
        s.pushed = true;
        if !chunk.is_null() && size > 0 {
            s.raw.extend_from_slice(std::slice::from_raw_parts(chunk as *const u8, size as usize));
        }
        0
    }
}

// --- parsing content in a node's context ------------------------------------------------

/// The wrapper element content is parsed in.
const WRAP: &[u8] = b"vxml-content";

fn escape_value(v: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(v.len());
    for &c in v {
        match c {
            b'%' => out.extend_from_slice(b"&#37;"),
            b'"' => out.extend_from_slice(b"&#34;"),
            b'&' => out.extend_from_slice(b"&#38;"),
            _ => out.push(c),
        }
    }
    out
}

/// A document type declaration redeclaring `doc`'s entities, so that the
/// content's references mean what they mean in the document.
unsafe fn entity_prolog(doc: *mut Doc) -> Vec<u8> {
    unsafe {
        let mut out = Vec::new();
        let dtd = (*doc).intSubset;
        let ext = !(*doc).extSubset.is_null() || (!dtd.is_null() && (!(*dtd).ExternalID.is_null() || !(*dtd).SystemID.is_null()));
        if dtd.is_null() && !ext {
            return out;
        }
        out.extend_from_slice(b"<!DOCTYPE ");
        out.extend_from_slice(WRAP);
        if ext {
            out.extend_from_slice(b" SYSTEM \"\"");
        }
        out.extend_from_slice(b" [");
        if !dtd.is_null() {
            let mut n = (*dtd).children;
            while !n.is_null() {
                if (*n).type_ == ENTITY_DECL {
                    let e = n as *mut Entity;
                    let name = cbytes((*e).name);
                    match (*e).etype {
                        INTERNAL_GENERAL_ENTITY => {
                            out.extend_from_slice(b"<!ENTITY ");
                            out.extend_from_slice(name);
                            out.extend_from_slice(b" \"");
                            out.extend_from_slice(&escape_value(cbytes((*e).content)));
                            out.extend_from_slice(b"\">");
                        }
                        EXTERNAL_GENERAL_PARSED_ENTITY => {
                            out.extend_from_slice(b"<!ENTITY ");
                            out.extend_from_slice(name);
                            match copt((*e).ExternalID) {
                                Some(p) => {
                                    out.extend_from_slice(b" PUBLIC \"");
                                    out.extend_from_slice(p);
                                    out.extend_from_slice(b"\" \"");
                                }
                                None => out.extend_from_slice(b" SYSTEM \""),
                            }
                            out.extend_from_slice(cbytes((*e).SystemID));
                            out.extend_from_slice(b"\">");
                        }
                        _ => {}
                    }
                }
                n = (*n).next;
            }
        }
        out.extend_from_slice(b"]>");
        out
    }
}

/// `xmlCtxtParseContent`'s work: `data` parsed as content of `node`.
unsafe fn parse_content(ctxt: *mut ParserCtxt, data: &[u8], node: *mut Node) -> *mut Node {
    unsafe {
        let c = ctxt;
        let doc = (*node).doc;
        let mut text = entity_prolog(doc);
        text.push(b'<');
        text.extend_from_slice(WRAP);
        text.push(b'>');
        let start = text.len();
        text.extend_from_slice(data);
        text.extend_from_slice(b"</");
        text.extend_from_slice(WRAP);
        text.push(b'>');
        let parsed = crate::api::parse(&text);
        let d = match parsed {
            Ok(d) => d,
            Err(e) => {
                let (code, msg, s1) = classify(&text, e.offset.max(start), &e);
                ctx_err(c, null_mut(), FROM_PARSER, code, ERR_FATAL, s1.as_deref(), None, None, 0, &msg);
                return null_mut();
            }
        };
        let input = (*c).input;
        let t = d.text();
        if !input.is_null() {
            (*input).base = t.as_ptr();
            (*input).cur = t.as_ptr();
            (*input).end = t.as_ptr().add(t.len());
        }
        let mut w = Walk::new(c, &d);
        let toks = d.toks(Src::Doc);
        let Some(root) = toks.iter().position(|t| t.kind == Kind::STag) else { return null_mut() };
        let close = toks[root].c();
        // The namespaces in scope at the node.
        let mut cur = node;
        let mut pushed = 0;
        while !cur.is_null() && (*cur).type_ == ELEMENT_NODE {
            let mut ns = (*cur).nsDef;
            while !ns.is_null() {
                let p = (*ns).prefix;
                let s = st(c);
                let bound = s.ns.iter().any(|b| copt(b.prefix) == copt(p));
                if !bound && copt(p) != Some(b"xml") {
                    let pd = if p.is_null() { null() } else { dict(c, cbytes(p)) };
                    s.ns.push(NsBinding { prefix: pd, uri: dict(c, cbytes((*ns).href)), sax: ns });
                    pushed += 1;
                }
                ns = (*ns).next;
            }
            cur = (*cur).parent;
        }
        let rootn = xmlNewDocNode(doc, null_mut(), c"#root".as_ptr() as *const XChar, null());
        st(c).spaces.push(-1);
        node_push(c, rootn);
        w.content(Src::Doc, root + 1, close);
        let mut list = null_mut();
        if (*c).wellFormed != 0 || ((*c).recovery != 0 && !catastrophic(&(*c).lastError)) {
            list = (*rootn).children;
            (*rootn).children = null_mut();
            (*rootn).last = null_mut();
            let mut x = list;
            while !x.is_null() {
                (*x).parent = null_mut();
                x = (*x).next;
            }
        }
        node_pop(c);
        st(c).spaces.pop();
        let s = st(c);
        let n = s.ns.len();
        s.ns.truncate(n - pushed);
        xmlFreeNode(rootn);
        list
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCtxtParseContent(ctxt: *mut ParserCtxt, input: *mut ParserInput, node: *mut Node, _has_text_decl: c_int) -> *mut Node {
    unsafe {
        if ctxt.is_null() || input.is_null() || node.is_null() || (*node).doc.is_null() {
            if !ctxt.is_null() {
                fatal(ctxt, ERR_ARGUMENT, b"Invalid argument\n", None);
            }
            xmlFreeInputStream(input);
            return null_mut();
        }
        let mut node = node;
        match (*node).type_ {
            ELEMENT_NODE | DOCUMENT_NODE | HTML_DOCUMENT_NODE => {}
            ATTRIBUTE_NODE | TEXT_NODE | CDATA_SECTION_NODE | ENTITY_REF_NODE | PI_NODE | COMMENT_NODE => {
                let mut cur = (*node).parent;
                while !cur.is_null() {
                    if matches!((*cur).type_, ELEMENT_NODE | DOCUMENT_NODE | HTML_DOCUMENT_NODE) {
                        node = cur;
                        break;
                    }
                    cur = (*cur).parent;
                }
            }
            _ => {
                fatal(ctxt, ERR_ARGUMENT, b"Invalid argument\n", None);
                xmlFreeInputStream(input);
                return null_mut();
            }
        }
        let doc = (*node).doc;
        xmlCtxtReset(ctxt);
        let old_dict = (*ctxt).dict;
        let old_options = (*ctxt).options;
        let old_names = (*ctxt).dictNames;
        let old_load = (*ctxt).loadsubset;
        if !(*doc).dict.is_null() {
            (*ctxt).dict = (*doc).dict as *mut Dict;
        } else {
            (*ctxt).options |= PARSE_NODICT;
            (*ctxt).dictNames = 0;
        }
        (*ctxt).loadsubset |= SKIP_IDS;
        (*ctxt).options |= PARSE_SKIP_IDS;
        (*ctxt).myDoc = doc;
        initialize_late(ctxt);
        xmlCtxtPushInput(ctxt, input);
        let data = input_bytes(input).to_vec();
        let (b, e) = ((*input).base, (*input).end);
        let list = parse_content(ctxt, &data, node);
        (*input).base = b;
        (*input).cur = e;
        (*input).end = e;
        xmlCtxtPopInput(ctxt);
        (*ctxt).dict = old_dict;
        (*ctxt).options = old_options;
        (*ctxt).dictNames = old_names;
        (*ctxt).loadsubset = old_load;
        initialize_late(ctxt);
        (*ctxt).myDoc = null_mut();
        (*ctxt).node = null_mut();
        xmlFreeInputStream(input);
        list
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlParseInNodeContext(node: *mut Node, data: *const c_char, len: c_int, options: c_int, out: *mut *mut Node) -> c_int {
    unsafe {
        if out.is_null() {
            return ERR_INTERNAL_ERROR;
        }
        *out = null_mut();
        if node.is_null() || data.is_null() || len < 0 || (*node).doc.is_null() {
            return ERR_INTERNAL_ERROR;
        }
        let doc = (*node).doc;
        let ctxt = xmlNewParserCtxt();
        if ctxt.is_null() {
            return ERR_NO_MEMORY;
        }
        let input = xmlCtxtNewInputFromMemory(ctxt, null(), data as *const c_void, len as usize, (*doc).encoding as *const c_char, BUF_STATIC);
        if input.is_null() {
            xmlFreeParserCtxt(ctxt);
            return ERR_NO_MEMORY;
        }
        xmlCtxtUseOptions(ctxt, options);
        let list = xmlCtxtParseContent(ctxt, input, node, 0);
        let ret = if list.is_null() {
            let e = (*ctxt).errNo;
            if e == ERR_ARGUMENT { ERR_INTERNAL_ERROR } else { e }
        } else {
            ERR_OK
        };
        *out = list;
        xmlFreeParserCtxt(ctxt);
        ret
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlParseBalancedChunkMemory(doc: *mut Doc, sax: *const SaxHandler, user: *mut c_void, depth: c_int, s: *const XChar, list: *mut *mut Node) -> c_int {
    unsafe { xmlParseBalancedChunkMemoryRecover(doc, sax, user, depth, s, list, 0) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlParseBalancedChunkMemoryRecover(
    doc: *mut Doc,
    _sax: *const SaxHandler,
    _user: *mut c_void,
    _depth: c_int,
    s: *const XChar,
    list: *mut *mut Node,
    _recover: c_int,
) -> c_int {
    unsafe {
        if !list.is_null() {
            *list = null_mut();
        }
        if s.is_null() {
            return -1;
        }
        let own = doc.is_null();
        let d = if own { xmlNewDoc(c"1.0".as_ptr() as *const XChar) } else { doc };
        let holder = xmlNewDocNode(d, null_mut(), c"pseudoroot".as_ptr() as *const XChar, null());
        let b = cbytes(s);
        let mut out = null_mut();
        let ret = xmlParseInNodeContext(holder, b.as_ptr() as *const c_char, b.len() as c_int, 0, &mut out);
        if !list.is_null() {
            *list = out;
        } else {
            xmlFreeNodeList(out);
        }
        xmlFreeNode(holder);
        if own {
            if !list.is_null() {
                let mut x = *list;
                while !x.is_null() {
                    xmlSetTreeDoc(x, null_mut());
                    x = (*x).next;
                }
            }
            xmlFreeDoc(d);
        }
        if ret == 0 { 0 } else { -1 }
    }
}
