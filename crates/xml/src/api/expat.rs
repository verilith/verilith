//! expat's C ABI (libexpat 2.10.0) over verilith-xml: feature `expat-abi`.
//!
//! A caller built against expat's `expat.h` links this library in place of
//! libexpat and runs unchanged. The verified parser decides whether the
//! document is well-formed and writes its tape; this file turns the tape
//! into expat's callbacks, in document order, and keeps expat's parser
//! states (`XML_Parse`, `XML_StopParser`, `XML_ResumeParser`, ...).
//!
//! It is ordinary Rust, not verified. How it departs from libexpat is in
//! the crate's README ("The expat C ABI"); the main differences:
//!
//! * The document is checked whole: `XML_Parse` keeps the input until the
//!   call with `isFinal` set, then parses it and calls the handlers, so no
//!   handler runs before the last buffer arrives, and an error is found
//!   when that buffer arrives.
//! * Namespaces (`XML_ParserCreateNS`) are processed here, over the names
//!   the verified parser read.
//! * External entities go to the `ExternalEntityRefHandler`; the parser it
//!   makes with `XML_ExternalEntityParserCreate` reads an external parsed
//!   entity, with the parent's internal subset. An external DTD subset is
//!   offered to the handler but its declarations are not read.
use super::{Attribute, Document, Element, Src};
use crate::decode::ex_eol;
use crate::push::{Stream, R_ERR, R_LIMIT, R_MORE, R_OK, R_WHOLE};
use crate::reader::Reader;
use crate::tape::{Kind, Tok};
use crate::ns::{ex_decl_check, ex_decl_prefix, ex_expand, Bindings, NsErr};
use crate::walk::{Cursor, Item};
use std::borrow::Cow;
use std::collections::HashSet;
use std::ffi::{c_char, c_int, c_long, c_uchar, c_uint, c_ulong, c_void, CStr};
use std::ptr::{null, null_mut};

type XChar = c_char;
type XBool = c_uchar;

type StartElementH = Option<unsafe extern "C" fn(*mut c_void, *const XChar, *mut *const XChar)>;
type EndElementH = Option<unsafe extern "C" fn(*mut c_void, *const XChar)>;
type CharDataH = Option<unsafe extern "C" fn(*mut c_void, *const XChar, c_int)>;
type PiH = Option<unsafe extern "C" fn(*mut c_void, *const XChar, *const XChar)>;
type CommentH = Option<unsafe extern "C" fn(*mut c_void, *const XChar)>;
type VoidH = Option<unsafe extern "C" fn(*mut c_void)>;
type DefaultH = Option<unsafe extern "C" fn(*mut c_void, *const XChar, c_int)>;
type StartDoctypeH = Option<unsafe extern "C" fn(*mut c_void, *const XChar, *const XChar, *const XChar, c_int)>;
type EntityDeclH = Option<
    unsafe extern "C" fn(
        *mut c_void,
        *const XChar,
        c_int,
        *const XChar,
        c_int,
        *const XChar,
        *const XChar,
        *const XChar,
        *const XChar,
    ),
>;
type UnparsedH =
    Option<unsafe extern "C" fn(*mut c_void, *const XChar, *const XChar, *const XChar, *const XChar, *const XChar)>;
type NotationH = Option<unsafe extern "C" fn(*mut c_void, *const XChar, *const XChar, *const XChar, *const XChar)>;
type StartNsH = Option<unsafe extern "C" fn(*mut c_void, *const XChar, *const XChar)>;
type EndNsH = Option<unsafe extern "C" fn(*mut c_void, *const XChar)>;
type NotStandaloneH = Option<unsafe extern "C" fn(*mut c_void) -> c_int>;
type ExtRefH =
    Option<unsafe extern "C" fn(*mut Parser, *const XChar, *const XChar, *const XChar, *const XChar) -> c_int>;
type SkippedH = Option<unsafe extern "C" fn(*mut c_void, *const XChar, c_int)>;
type UnknownEncH = Option<unsafe extern "C" fn(*mut c_void, *const XChar, *mut XmlEncoding) -> c_int>;
type ElementDeclH = Option<unsafe extern "C" fn(*mut c_void, *const XChar, *mut XmlContent)>;
type AttlistDeclH =
    Option<unsafe extern "C" fn(*mut c_void, *const XChar, *const XChar, *const XChar, *const XChar, c_int)>;
type XmlDeclH = Option<unsafe extern "C" fn(*mut c_void, *const XChar, *const XChar, c_int)>;

/// `XML_Encoding`, for `XML_SetUnknownEncodingHandler`.
#[repr(C)]
pub struct XmlEncoding {
    map: [c_int; 256],
    data: *mut c_void,
    convert: Option<unsafe extern "C" fn(*mut c_void, *const c_char) -> c_int>,
    release: Option<unsafe extern "C" fn(*mut c_void)>,
}

/// `XML_Content` (`struct XML_cp`).
#[repr(C)]
pub struct XmlContent {
    ty: c_int,
    quant: c_int,
    name: *mut XChar,
    numchildren: c_uint,
    children: *mut XmlContent,
}

/// `XML_Memory_Handling_Suite`.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct MemSuite {
    malloc_fcn: Option<unsafe extern "C" fn(usize) -> *mut c_void>,
    realloc_fcn: Option<unsafe extern "C" fn(*mut c_void, usize) -> *mut c_void>,
    free_fcn: Option<unsafe extern "C" fn(*mut c_void)>,
}

unsafe extern "C" {
    fn malloc(n: usize) -> *mut c_void;
    fn realloc(p: *mut c_void, n: usize) -> *mut c_void;
    fn free(p: *mut c_void);
}
unsafe extern "C" fn sys_malloc(n: usize) -> *mut c_void {
    unsafe { malloc(n) }
}
unsafe extern "C" fn sys_realloc(p: *mut c_void, n: usize) -> *mut c_void {
    unsafe { realloc(p, n) }
}
unsafe extern "C" fn sys_free(p: *mut c_void) {
    unsafe { free(p) }
}
const SYS_MEM: MemSuite = MemSuite { malloc_fcn: Some(sys_malloc), realloc_fcn: Some(sys_realloc), free_fcn: Some(sys_free) };

// enum XML_Status
const STATUS_ERROR: c_int = 0;
const STATUS_OK: c_int = 1;
const STATUS_SUSPENDED: c_int = 2;

// enum XML_Error
const E_NONE: c_int = 0;
const E_NO_MEMORY: c_int = 1;
const E_SYNTAX: c_int = 2;
const E_NO_ELEMENTS: c_int = 3;
const E_INVALID_TOKEN: c_int = 4;
const E_UNCLOSED_TOKEN: c_int = 5;
const E_PARTIAL_CHAR: c_int = 6;
const E_TAG_MISMATCH: c_int = 7;
const E_DUPLICATE_ATTRIBUTE: c_int = 8;
const E_JUNK_AFTER_DOC_ELEMENT: c_int = 9;
const E_PARAM_ENTITY_REF: c_int = 10;
const E_UNDEFINED_ENTITY: c_int = 11;
const E_RECURSIVE_ENTITY_REF: c_int = 12;
const E_ASYNC_ENTITY: c_int = 13;
const E_BAD_CHAR_REF: c_int = 14;
const E_BINARY_ENTITY_REF: c_int = 15;
const E_ATTRIBUTE_EXTERNAL_ENTITY_REF: c_int = 16;
const E_MISPLACED_XML_PI: c_int = 17;
const E_UNKNOWN_ENCODING: c_int = 18;
const E_UNCLOSED_CDATA_SECTION: c_int = 20;
const E_EXTERNAL_ENTITY_HANDLING: c_int = 21;
const E_NOT_STANDALONE: c_int = 22;
const E_CANT_CHANGE_FEATURE_ONCE_PARSING: c_int = 26;
const E_UNBOUND_PREFIX: c_int = 27;
const E_UNDECLARING_PREFIX: c_int = 28;
const E_XML_DECL: c_int = 30;
const E_TEXT_DECL: c_int = 31;
const E_SUSPENDED: c_int = 33;
const E_NOT_SUSPENDED: c_int = 34;
const E_ABORTED: c_int = 35;
const E_FINISHED: c_int = 36;
const E_RESERVED_PREFIX_XML: c_int = 38;
const E_RESERVED_PREFIX_XMLNS: c_int = 39;
const E_RESERVED_NAMESPACE_URI: c_int = 40;
const E_INVALID_ARGUMENT: c_int = 41;
const E_NO_BUFFER: c_int = 42;
const E_NOT_STARTED: c_int = 44;

static ERROR_STRINGS: [&CStr; 45] = [
    c"",
    c"out of memory",
    c"syntax error",
    c"no element found",
    c"not well-formed (invalid token)",
    c"unclosed token",
    c"partial character",
    c"mismatched tag",
    c"duplicate attribute",
    c"junk after document element",
    c"illegal parameter entity reference",
    c"undefined entity",
    c"recursive entity reference",
    c"asynchronous entity",
    c"reference to invalid character number",
    c"reference to binary entity",
    c"reference to external entity in attribute",
    c"XML or text declaration not at start of entity",
    c"unknown encoding",
    c"encoding specified in XML declaration is incorrect",
    c"unclosed CDATA section",
    c"error in processing external entity reference",
    c"document is not standalone",
    c"unexpected parser state - please send a bug report",
    c"entity declared in parameter entity",
    c"requested feature requires XML_DTD support in Expat",
    c"cannot change setting once parsing has begun",
    c"unbound prefix",
    c"must not undeclare prefix",
    c"incomplete markup in parameter entity",
    c"XML declaration not well-formed",
    c"text declaration not well-formed",
    c"illegal character(s) in public id",
    c"parser suspended",
    c"parser not suspended",
    c"parsing aborted",
    c"parsing finished",
    c"cannot suspend in external parameter entity",
    c"reserved prefix (xml) must not be undeclared or bound to another namespace name",
    c"reserved prefix (xmlns) must not be declared or undeclared",
    c"prefix must not be bound to one of the reserved namespace names",
    c"invalid argument",
    c"a successful prior call to function XML_GetBuffer is required",
    c"limit on input amplification factor (from DTD and entities) breached",
    c"parser not started",
];

// enum XML_Parsing
const P_INITIALIZED: c_int = 0;
const P_PARSING: c_int = 1;
const P_FINISHED: c_int = 2;
const P_SUSPENDED: c_int = 3;

#[derive(Clone, Copy, Default)]
struct Handlers {
    start: StartElementH,
    end: EndElementH,
    chars: CharDataH,
    pi: PiH,
    comment: CommentH,
    start_cdata: VoidH,
    end_cdata: VoidH,
    default: DefaultH,
    default_expand: bool,
    start_doctype: StartDoctypeH,
    end_doctype: VoidH,
    entity_decl: EntityDeclH,
    unparsed: UnparsedH,
    notation: NotationH,
    start_ns: StartNsH,
    end_ns: EndNsH,
    not_standalone: NotStandaloneH,
    ext_ref: ExtRefH,
    ext_ref_arg: Option<*mut Parser>,
    skipped: SkippedH,
    unknown_enc: UnknownEncH,
    unknown_enc_data: Option<*mut c_void>,
    element_decl: ElementDeclH,
    attlist_decl: AttlistDeclH,
    xml_decl: XmlDeclH,
}

/// What a parser made by `XML_ExternalEntityParserCreate` reads.
enum Ext {
    /// The external DTD subset: accepted and not read.
    Dtd,
    /// An external parsed entity: read as content, after the parent's
    /// internal subset (`prefix`, which ends with the wrapper's start tag).
    Entity { prefix: Vec<u8>, bindings: Vec<(Vec<u8>, Vec<u8>)> },
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Phase {
    Prolog(usize),
    /// The declarations of the DTD read whole (`Document::flattened`), at a
    /// token of its tape; then the prolog on from `dt_resume`.
    Dtd(usize),
    Content,
    Epilog(usize),
    Done,
}

/// An open element, as `start_element` reported it; pushed on the walk's
/// `Start` and popped on its `End`, which the verified cursor proves are
/// well nested (`walk::lemma_items_balanced`).
enum Open {
    /// An element: its name as reported (NUL-terminated), and how many
    /// namespace bindings it made.
    Elem { name_at: usize, nb: usize, stag: usize, empty: bool },
    /// The wrapper element of an external entity read as a stream: its end
    /// is the entity's.
    Wrapper,
}

/// A tape being walked: the document's content (the first), or an internal
/// entity's replacement text, read in place of a reference. The verified
/// cursor (`walk::Cursor`) says which item comes next; `opens` is how many
/// elements were open when it began.
struct Seg {
    src: Src,
    cur: Cursor<'static>,
    opens: usize,
}

/// A parser (`XML_Parser`). `user_data` is first: expat.h's
/// `XML_GetUserData` macro reads the first pointer of the struct.
#[repr(C)]
pub struct Parser {
    user_data: *mut c_void,
    handler_arg: *mut c_void,
    arg_is_parser: bool,
    h: Handlers,
    mem: MemSuite,
    ns: Option<u8>,
    triplets: bool,
    param_parsing: c_int,
    foreign_dtd: bool,
    base: Option<Vec<u8>>,
    encoding: Option<Vec<u8>>,
    ext: Option<Ext>,
    // Input until the final buffer, then the document over it.
    input: Vec<u8>,
    /// expat's own input buffer, which `XML_GetBuffer` hands out.
    eb: EBuf,
    /// The last fill size the application asked for, and the bytes there
    /// were at the last parse attempt that read nothing (expat's reparse
    /// deferral heuristic).
    last_req: usize,
    partial_before: usize,
    doc: Option<Box<Document<'static>>>,
    owned_text: Option<Box<[u8]>>,
    /// The push parser, from the first chunk that is not the last: the
    /// document's text is then its window (`doc` is over it, and dropped
    /// before it), which begins at `sbase` in the input.
    stream: Option<Box<Reader>>,
    sbase: usize,
    /// The stream's verdict on what it was fed (`R_MORE`, ...).
    sverdict: u8,
    /// The stream failed in a token that the input has not finished: expat
    /// reports that only once the token is complete or the input ends, so
    /// what comes after it is held here until then.
    held: Option<Vec<u8>>,
    /// A CR at the end of the epilog read so far, not yet reported.
    epilog_cr: bool,
    /// `doc` has the stream's declarations, which are final.
    sdtd: bool,
    /// The stream handed the document back: it is read whole.
    whole: bool,
    /// The walk's place in the chunk's tokens.
    /// Offset in the input of what callers see (an external entity's
    /// content begins after the wrapper's prefix).
    origin: usize,
    /// The stream's input is not quite the caller's: `raw_pre` bytes come
    /// before theirs (an external entity's wrapper), and the first `raw_skip` of
    /// theirs are not in it (a byte order mark, a text declaration). The
    /// stream's progress maps to theirs by these.
    raw_pre: usize,
    raw_skip: usize,
    parsing: c_int,
    final_buffer: bool,
    error: c_int,
    // Where the current event is: a byte range of the document's text.
    ev: (usize, usize),
    /// Where the error is, in the text, once there is one.
    err_at: usize,
    /// Line counting from `line_at` (an offset in the input) where there
    /// is `line`, and `col`, the column there.
    /// the offset of the start of that line.
    line_at: usize,
    line: usize,
    col: usize,
    // The walk.
    phase: Phase,
    segs: Vec<Seg>,
    opens: Vec<Open>,
    ns_stack: Bindings,
    last_end: usize,
    attlist_elem: (usize, usize),
    dtd_skip: bool,
    seen_ents: HashSet<(bool, Vec<u8>)>,
    // Scratch for the strings and arrays handed to handlers.
    scratch: Vec<u8>,
    offs: Vec<usize>,
    atts: Vec<*const XChar>,
    nspecified: c_int,
    id_index: c_int,
    /// A handler is running: the calls that would parse re-entrantly, and
    /// freeing or resetting the parser, are refused.
    walking: bool,
    /// The unknown encoding's release callback and its data, called when the
    /// parser is freed or reset, as expat does.
    enc_release: Option<(unsafe extern "C" fn(*mut c_void), *mut c_void)>,
    /// How many internal entities' replacement texts are being read.
    ent_depth: usize,
    /// The names of the open elements, NUL-terminated, end to end.
    names: Vec<u8>,
    att_ks: Vec<(usize, usize)>,
    /// The external entities being read around this parser, and the one
    /// whose parser is being made: a reference to one of them is recursion.
    open_ents: Vec<Vec<u8>>,
    doctype_ext: Option<(Vec<u8>, Option<Vec<u8>>)>,
    pending_text_decl: Option<(Option<Vec<u8>>, Option<Vec<u8>>)>,
    base_c: Option<Vec<u8>>,
    props: Props,
    /// The declarations' tokens and text: the document's, or the DTD read
    /// whole (`Src::Pro`); and the prolog's token after it.
    dsrc: Src,
    dt_resume: usize,
    /// While the DTD is read whole: the text of the external entity the
    /// handler is asked for, as the parser it makes for it is given it,
    /// and the base URI set on that parser.
    collect: Option<Vec<u8>>,
    /// For each external entity of the DTD read so far: the base URI, the
    /// external entity reference handler and its argument of the parser
    /// that read it, which the entities it refers to are read with (the
    /// loader's URI for it is its index here, after '#').
    ext_tab: Vec<(Option<Vec<u8>>, ExtRefH, Option<*mut Parser>)>,
    collect_h: Option<(Option<Vec<u8>>, ExtRefH, Option<*mut Parser>)>,
    /// The parser made for the entity being read found it malformed.
    collect_err: bool,
    /// A parser made for the external subset or a parameter entity while
    /// the parent reads its DTD whole: what it is given goes to the
    /// parent's `collect`.
    collect_to: Option<*mut Parser>,
    /// The handler failed for an external entity of the DTD.
    ext_fail: bool,
    /// The external subset was read with the DTD (and is not offered to
    /// the handler again at the end of the document type declaration).
    ext_read: bool,
    /// An external entity's parser whose wrapper holds the parent's DTD
    /// read whole: it reads no external entity again.
    no_load: bool,
}

impl Parser {
    fn new(enc: *const XChar, mem: MemSuite, ns: Option<u8>) -> Box<Parser> {
        Box::new(Parser {
            user_data: null_mut(),
            handler_arg: null_mut(),
            arg_is_parser: false,
            h: Handlers::default(),
            mem,
            ns,
            triplets: false,
            param_parsing: 0,
            foreign_dtd: false,
            base: None,
            encoding: unsafe { opt_cstr(enc) },
            ext: None,
            input: Vec::new(),
            eb: EBuf::new(mem),
            last_req: 0,
            partial_before: 0,
            doc: None,
            owned_text: None,
            stream: None,
            sbase: 0,
            sverdict: 0,
            held: None,
            epilog_cr: false,
            sdtd: false,
            whole: false,
            origin: 0,
            raw_pre: 0,
            raw_skip: 0,
            parsing: P_INITIALIZED,
            final_buffer: false,
            error: E_NONE,
            ev: (0, 0),
            err_at: 0,
            line_at: 0,
            line: 1,
            col: 0,
            phase: Phase::Prolog(0),
            segs: Vec::new(),
            opens: Vec::new(),
            ns_stack: Bindings::new(),
            last_end: 0,
            attlist_elem: (0, 0),
            dtd_skip: false,
            seen_ents: HashSet::new(),
            scratch: Vec::new(),
            offs: Vec::new(),
            atts: Vec::new(),
            nspecified: 0,
            id_index: -1,
            walking: false,
            enc_release: None,
            ent_depth: 0,
            names: Vec::new(),
            att_ks: Vec::new(),
            open_ents: Vec::new(),
            doctype_ext: None,
            pending_text_decl: None,
            base_c: None,
            props: Props::default(),
            dsrc: Src::Doc,
            dt_resume: 0,
            collect: None,
            ext_tab: Vec::new(),
            collect_h: None,
            collect_err: false,
            collect_to: None,
            ext_fail: false,
            ext_read: false,
            no_load: false,
        })
    }

    fn reset(&mut self, enc: *const XChar) {
        self.release_encoding();
        self.doc = None;
        self.owned_text = None;
        let (mem, ns) = (self.mem, self.ns);
        let fresh = Parser::new(enc, mem, ns);
        *self = *fresh;
    }

    fn no_handlers(&self) -> bool {
        let h = &self.h;
        h.start.is_none()
            && h.end.is_none()
            && h.chars.is_none()
            && h.pi.is_none()
            && h.comment.is_none()
            && h.start_cdata.is_none()
            && h.end_cdata.is_none()
            && h.default.is_none()
            && h.start_doctype.is_none()
            && h.end_doctype.is_none()
            && h.entity_decl.is_none()
            && h.unparsed.is_none()
            && h.notation.is_none()
            && h.not_standalone.is_none()
            && h.ext_ref.is_none()
            && h.skipped.is_none()
            && h.element_decl.is_none()
            && h.attlist_decl.is_none()
            && h.xml_decl.is_none()
    }

    fn arg(&mut self) -> *mut c_void {
        if self.arg_is_parser { self as *mut Parser as *mut c_void } else { self.handler_arg }
    }

    fn text(&self) -> &[u8] {
        match (&self.doc, &self.owned_text) {
            (Some(d), _) => d.text(),
            (None, Some(t)) => t,
            (None, None) => &self.input,
        }
    }

    /// Line (from 1) and column (from 0) of `off`, counted in the text
    /// callers see.
    fn line_col(&mut self, off: usize) -> (usize, usize) {
        let sbase = self.sbase;
        let origin = self.origin.max(sbase);
        let off = off.max(origin - sbase);
        if sbase + off < self.line_at {
            self.line_at = origin;
            self.line = 1;
            self.col = 0;
        }
        // A carriage return the window ends with may be the first half of
        // a line end the next chunk finishes: counted, not kept.
        let open = self.stream.is_some() && !self.final_buffer;
        let (mut line, mut col) = (self.line, self.col);
        let mut keep = None;
        {
            let t = self.text();
            let end = off.min(t.len());
            let from = (self.line_at - sbase).min(end);
            for k in from..end {
                let c = t[k];
                if open && c == b'\r' && k + 1 == t.len() {
                    keep = Some((k, line, col));
                }
                // A line ends at LF, CR LF, or CR alone (2.11).
                if c == b'\n' || (c == b'\r' && t.get(k + 1) != Some(&b'\n')) {
                    line += 1;
                    col = 0;
                } else if c & 0xC0 != 0x80 {
                    // Columns count characters, as expat's do for UTF-8.
                    col += 1;
                }
            }
            let (k, l, c) = keep.unwrap_or((end, line, col));
            self.line_at = sbase + k;
            self.line = l;
            self.col = c;
        }
        (line, col)
    }

    fn position(&self) -> usize {
        if self.error != E_NONE { self.err_at } else { self.ev.0 }
    }

    fn fail(&mut self, code: c_int) -> c_int {
        self.error = code;
        self.parsing = P_FINISHED;
        STATUS_ERROR
    }

    /// The final buffer has arrived: parse, then walk.
    fn finish(&mut self) -> c_int {
        let raw = std::mem::take(&mut self.input);
        let (text, prefix_len) = match self.prepare(raw) {
            Ok(x) => x,
            Err(code) => return self.fail(code),
        };
        let boxed: Box<[u8]> = text.into_boxed_slice();
        // The document borrows the boxed text, which lives as long as it
        // does: `doc` is dropped before `owned_text` everywhere.
        let slice: &'static [u8] = unsafe { std::slice::from_raw_parts(boxed.as_ptr(), boxed.len()) };
        self.owned_text = Some(boxed);
        if self.ext.is_none() && self.ns.is_none() && self.no_handlers() && self.param_parsing == 0 {
            // Nothing to report: the verified check alone decides.
            let mut tape = crate::tape::Tape::new();
            if crate::enc::ex_parse(slice, &mut tape).is_some() {
                self.parsing = P_FINISHED;
                self.ev = (slice.len(), slice.len());
                return STATUS_OK;
            }
            let e = super::rejected(slice);
            let (code, at) = classify(slice, &e);
            self.err_at = at;
            return self.fail(code);
        }
        let parsed = self.parse_dtd(slice);
        if self.ext_fail {
            return self.fail(E_EXTERNAL_ENTITY_HANDLING);
        }
        match parsed {
            Ok(d) => {
                self.doc = Some(Box::new(d));
                self.origin = prefix_len;
                self.line_at = prefix_len;
                self.col = 0;
            }
            Err(e) => {
                self.origin = prefix_len;
                self.line_at = prefix_len;
                self.col = 0;
                let (code, at) = classify(slice, &e);
                let (code, at) = if self.ext.is_some() { ext_end_error(slice, code, at) } else { (code, at) };
                self.err_at = at.max(prefix_len);
                return self.fail(code);
            }
        }
        if let Some(Ext::Entity { bindings, .. }) = &self.ext {
            self.ns_stack = bindings_of(bindings);
        }
        let doc = self.doc.as_ref().unwrap();
        let root = doc.root;
        if self.ext.is_some() {
            let toks = doc.toks(Src::Doc);
            let close = toks[root].c();
            let mut i = root + 1;
            while i < close && matches!(toks[i].kind, Kind::Attr | Kind::AttVal) {
                i += 1;
            }
            self.start_content(Cursor::new(self.doc().toks(Src::Doc), i, close, 0, false), None);
            self.phase = Phase::Content;
            self.last_end = prefix_len;
        } else {
            self.phase = Phase::Prolog(0);
        }
        self.walk()
    }

    /// The document, as expat reads its DTD: parameter entities expanded
    /// unless parameter entity parsing is off (XML_PARAM_ENTITY_PARSING_NEVER,
    /// where a reference is skipped, and the declarations after it are
    /// not processed, §5.1); the external subset and external parameter
    /// entities read through the external entity reference handler.
    fn parse_dtd(&mut self, slice: &'static [u8]) -> Result<Document<'static>, super::Error> {
        if self.param_parsing == 0 {
            return plain_parse(slice);
        }
        let standalone = self.param_parsing == 1 && declares_standalone(slice);
        if self.h.ext_ref.is_none() || self.no_load || standalone {
            return super::parse(slice);
        }
        let me = self as *mut Parser;
        let mut ld = crate::pe::Loader::new(move |base: &[u8], sys: &[u8], pubid: &[u8]| unsafe { (*me).ext_dtd_entity(base, sys, pubid) });
        let r = super::parse_dtd_with(slice, &mut ld);
        // The handler was offered the external subset, if there is one.
        self.ext_read = true;
        r
    }

    /// The handler's text for an external entity of the DTD: the parser it
    /// makes for it (`XML_ExternalEntityParserCreate` with no context)
    /// keeps what it is given here (`collect`). `None` if the handler is
    /// not there or failed (`ext_fail`), and the entity is not read.
    fn ext_dtd_entity(&mut self, base: &[u8], sys: &[u8], pubid: &[u8]) -> Option<(Vec<u8>, Vec<u8>)> {
        // The parser that would read the reference: this one (for the
        // document), or the one that read the entity holding it.
        let (b, f, arg) = if base.is_empty() {
            (self.base.clone(), self.h.ext_ref, self.h.ext_ref_arg)
        } else {
            let k: usize = std::str::from_utf8(&base[1..]).ok()?.parse().ok()?;
            self.ext_tab.get(k)?.clone()
        };
        let f = f?;
        self.collect = Some(Vec::new());
        self.collect_h = None;
        self.collect_err = false;
        self.s_clear();
        let bk = b.map(|b| self.s_push(&b));
        let sk = self.s_push(sys);
        let pk = if pubid.is_empty() { None } else { Some(self.s_push(pubid)) };
        let me = arg.unwrap_or(self as *mut Parser);
        let ok = unsafe { f(me, null(), self.s_opt(bk), self.s_ptr(sk), self.s_opt(pk)) } != 0;
        let text = self.collect.take().unwrap_or_default();
        let h = self.collect_h.take().unwrap_or((None, None, None));
        if !ok {
            self.ext_fail = true;
            return None;
        }
        self.ext_tab.push(h);
        // An entity its parser rejected, which the handler let pass: as
        // far as the document goes, empty.
        let text = if std::mem::take(&mut self.collect_err) { Vec::new() } else { text };
        Some((text, format!("#{}", self.ext_tab.len() - 1).into_bytes()))
    }

    /// The text the verified parser reads: the input, or for an external
    /// entity the wrapper around it; and where the caller's text begins.
    fn prepare(&mut self, raw: Vec<u8>) -> Result<(Vec<u8>, usize), c_int> {
        let raw = self.unknown_encoding(raw)?;
        let raw = match (&self.encoding, &self.ext) {
            (Some(name), None) => transcode(raw, name)?,
            _ => raw,
        };
        match &self.ext {
            None => Ok((raw, 0)),
            Some(Ext::Dtd) => Ok((raw, 0)),
            Some(Ext::Entity { prefix, .. }) => {
                let content = ext_content(&raw)?;
                let (decl, body) = content;
                let mut t = prefix.clone();
                let n = t.len();
                t.extend_from_slice(&body);
                t.extend_from_slice(WRAP_END);
                self.pending_text_decl = decl;
                Ok((t, n))
            }
        }
    }
}

/// An external entity of the DTD read on its own, as the external subset
/// (its references to parameter entities declared elsewhere not read): the
/// error expat gives it, if it is malformed or refers to an entity whose
/// text is being read (`open`).
fn ext_dtd_check(text: &[u8], open: &[Vec<u8>]) -> Result<(), c_int> {
    let t = text.to_vec();
    let mut ld = crate::pe::Loader::new(move |b: &[u8], s: &[u8], _: &[u8]| (b.is_empty() && s == b"x").then(|| (t.clone(), b"#".to_vec())));
    if super::parse_dtd_with(b"<!DOCTYPE d SYSTEM 'x'><d/>", &mut ld).is_err() {
        return Err(ext_dtd_code(text));
    }
    let mut i = 0;
    while let Some(p) = text[i..].iter().position(|&c| c == b'%') {
        let a = i + p + 1;
        let e = a + text[a..].iter().take_while(|&&c| !is_ws(c) && !b"%;<>'\"&".contains(&c)).count();
        if e > a && text.get(e) == Some(&b';') && open.iter().any(|n| !n.is_empty() && n[..] == text[a..e]) {
            return Err(E_RECURSIVE_ENTITY_REF);
        }
        i = a;
    }
    Ok(())
}

/// The error code for a malformed external entity of the DTD.
fn ext_dtd_code(text: &[u8]) -> c_int {
    let t = text.strip_prefix(&[0xEF, 0xBB, 0xBF]).unwrap_or(text);
    if let Err(e) = std::str::from_utf8(t) {
        let at = e.valid_up_to();
        return if e.error_len().is_none() && at < t.len() { E_PARTIAL_CHAR } else { E_INVALID_TOKEN };
    }
    match crate::pe::ex_ext_text(text.to_vec()) {
        None => return E_TEXT_DECL,
        // Not read as a text declaration, but begun as one.
        Some((_, 0)) if t.starts_with(b"<?xml") && t.get(5).is_none_or(|&c| is_ws(c) || c == b'?') => return E_TEXT_DECL,
        _ => {}
    }
    // A literal that does not end.
    let mut q: Option<u8> = None;
    for &c in t {
        match q {
            Some(x) if c == x => q = None,
            None if c == b'"' || c == b'\'' => q = Some(c),
            _ => {}
        }
    }
    if q.is_some() {
        return E_UNCLOSED_TOKEN;
    }
    E_INVALID_TOKEN
}

/// The document with parameter entities not expanded (as the stream
/// reads it): for the error the stream's verdict is.
/// expat's error code for a namespace error.
fn ns_code(e: NsErr) -> c_int {
    match e {
        NsErr::InvalidToken => E_INVALID_TOKEN,
        NsErr::UnboundPrefix => E_UNBOUND_PREFIX,
        NsErr::ReservedPrefixXmlns => E_RESERVED_PREFIX_XMLNS,
        NsErr::ReservedPrefixXml => E_RESERVED_PREFIX_XML,
        NsErr::ReservedNamespaceUri => E_RESERVED_NAMESPACE_URI,
        NsErr::UndeclaringPrefix => E_UNDECLARING_PREFIX,
        NsErr::Syntax => E_SYNTAX,
    }
}

/// The bindings an external entity's parser starts with.
fn bindings_of(v: &[(Vec<u8>, Vec<u8>)]) -> Bindings {
    let mut b = Bindings::new();
    for (p, u) in v {
        b.push(p.clone(), u.clone());
    }
    b
}

fn plain_parse(t: &[u8]) -> Result<Document<'_>, super::Error> {
    let mut tape = crate::tape::Tape::new();
    match crate::enc::ex_parse(t, &mut tape) {
        Some((owned, dtd)) => Ok(Document::new(t, owned, tape, dtd, None)),
        None => Err(super::rejected(t)),
    }
}

/// Whether the text's XML declaration says `standalone="yes"`.
fn declares_standalone(t: &[u8]) -> bool {
    let t = t.strip_prefix(&[0xEF, 0xBB, 0xBF]).unwrap_or(t);
    if !t.starts_with(b"<?xml") {
        return false;
    }
    let Some(e) = find(t, 0, b"?>") else { return false };
    let d = &t[..e];
    let Some(k) = find(d, 0, b"standalone") else { return false };
    let rest = &d[k + 10..];
    let v: Vec<u8> = rest.iter().copied().filter(|c| !is_ws(*c) && *c != b'=').collect();
    v.starts_with(b"\"yes\"") || v.starts_with(b"'yes'")
}

/// `step`: the chunk's tokens are all read.
const NEED_MORE: c_int = -1;

const WRAP_NAME: &str = "vxml-external-entity";
const WRAP_END: &[u8] = b"</vxml-external-entity>";

/// An error in an external entity's wrapped text at the wrapper's end tag
/// is where the entity ends: an element it began is open (expat's
/// `XML_ERROR_ASYNC_ENTITY`), or a token is unfinished, which the entity
/// read on its own says.
fn ext_end_error(t: &[u8], code: c_int, at: usize) -> (c_int, usize) {
    if !t.ends_with(WRAP_END) {
        return (code, at);
    }
    let end = t.len() - WRAP_END.len();
    if code == E_TAG_MISMATCH && at >= end {
        return (E_ASYNC_ENTITY, at);
    }
    // Read without the wrapper's end tag, the first error is the same
    // unless the entity ends inside a token.
    let body = &t[..end];
    match plain_parse(body) {
        Err(e) => match classify(body, &e) {
            (c, a) if matches!(c, E_UNCLOSED_TOKEN | E_PARTIAL_CHAR | E_UNCLOSED_CDATA_SECTION) => (c, a),
            _ => (code, at),
        },
        Ok(_) => (code, at),
    }
}

/// How an external entity's first bytes are read.
enum ExtHead {
    /// Not enough yet to tell.
    Wait,
    /// Read whole, at the last chunk: another encoding than UTF-8.
    Whole,
    /// As it comes: the text declaration, and where the content begins.
    Stream(Option<(Option<Vec<u8>>, Option<Vec<u8>>)>, usize),
    Fail(c_int),
}

/// The byte order mark and text declaration an external entity begins
/// with (as `ext_content` reads them), once they are complete.
fn ext_head(raw: &[u8], last: bool, given: Option<&[u8]>) -> ExtHead {
    let utf8 = |n: &[u8]| n.eq_ignore_ascii_case(b"UTF-8") || n.eq_ignore_ascii_case(b"US-ASCII");
    if given.is_some_and(|n| !utf8(n)) {
        return ExtHead::Whole;
    }
    let prefix_of = |p: &[u8]| raw.len() < p.len() && p.starts_with(raw);
    if !last && (prefix_of(&[0xEF, 0xBB, 0xBF]) || prefix_of(&[0xFE, 0xFF]) || prefix_of(&[0xFF, 0xFE])) {
        return ExtHead::Wait;
    }
    if raw.starts_with(&[0xFE, 0xFF]) || raw.starts_with(&[0xFF, 0xFE]) {
        return ExtHead::Whole;
    }
    let skip = if raw.starts_with(&[0xEF, 0xBB, 0xBF]) { 3 } else { 0 };
    let s = &raw[skip..];
    if s.len() < 6 && !last && b"<?xml"[..s.len().min(5)] == s[..s.len().min(5)] {
        return ExtHead::Wait;
    }
    let has_decl = s.len() >= 6 && &s[..5] == b"<?xml" && matches!(s[5], b' ' | b'\t' | b'\n' | b'\r');
    if !has_decl {
        return ExtHead::Stream(None, skip);
    }
    let Some(end) = find(s, 0, b"?>") else {
        return if last { ExtHead::Whole } else { ExtHead::Wait };
    };
    match ext_content(&s[..end + 2]) {
        Err(c) => ExtHead::Fail(c),
        Ok((Some((v, Some(e))), _)) if utf8(&e) => ExtHead::Stream(Some((v, Some(e))), skip + end + 2),
        Ok(_) => ExtHead::Whole,
    }
}

/// An external parsed entity's bytes as UTF-8 content, and its text
/// declaration (version, encoding), if it has one.
fn ext_content(raw: &[u8]) -> Result<(Option<(Option<Vec<u8>>, Option<Vec<u8>>)>, Vec<u8>), c_int> {
    let utf8: Cow<[u8]> = if raw.starts_with(&[0xFE, 0xFF]) || raw.starts_with(&[0xFF, 0xFE]) {
        let be = raw[0] == 0xFE;
        let units: Vec<u16> = raw[2..]
            .chunks(2)
            .map(|c| if c.len() < 2 { 0xFFFF } else if be { u16::from_be_bytes([c[0], c[1]]) } else { u16::from_le_bytes([c[0], c[1]]) })
            .collect();
        match String::from_utf16(&units) {
            Ok(s) => Cow::Owned(s.into_bytes()),
            Err(_) => return Err(E_INVALID_TOKEN),
        }
    } else if raw.starts_with(&[0xEF, 0xBB, 0xBF]) {
        Cow::Borrowed(&raw[3..])
    } else {
        Cow::Borrowed(raw)
    };
    let s = &utf8[..];
    let has_decl = s.len() >= 6 && &s[..5] == b"<?xml" && matches!(s[5], b' ' | b'\t' | b'\n' | b'\r');
    if !has_decl {
        return Ok((None, s.to_vec()));
    }
    let end = match find(s, 0, b"?>") {
        Some(e) => e,
        None => return Err(E_UNCLOSED_TOKEN),
    };
    let decl = &s[5..end];
    let version = pseudo_attr(decl, b"version");
    let encoding = pseudo_attr(decl, b"encoding");
    if encoding.is_none() {
        // A text declaration must name the encoding (XML 1.0, 4.3.1).
        return Err(31); // XML_ERROR_TEXT_DECL
    }
    let body = &s[end + 2..];
    let enc = encoding.clone().unwrap().to_ascii_uppercase();
    let body: Vec<u8> = if enc == b"ISO-8859-1" || enc == b"LATIN1" {
        body.iter().flat_map(|&b| char::from(b).to_string().into_bytes()).collect()
    } else {
        body.to_vec()
    };
    Ok((Some((version, encoding)), body))
}

/// The input in the encoding the caller named (`XML_ParserCreate`,
/// `XML_SetEncoding`), which takes precedence over the document's own
/// declaration as external information does (XML 1.0, 4.3.3 and F.2): as
/// UTF-8, its declaration then naming UTF-8.
fn transcode(raw: Vec<u8>, name: &[u8]) -> Result<Vec<u8>, c_int> {
    let up = name.to_ascii_uppercase();
    let mut out: Vec<u8> = match up.as_slice() {
        b"UTF-8" => return Ok(raw),
        b"UTF-16" | b"UTF-16LE" | b"UTF-16BE" => {
            let mut r = &raw[..];
            let mut be = match up.as_slice() {
                b"UTF-16LE" => false,
                b"UTF-16BE" => true,
                _ => !(r.len() >= 2 && r[1] == 0 && r[0] != 0),
            };
            if r.starts_with(&[0xFE, 0xFF]) {
                be = true;
                r = &r[2..];
            } else if r.starts_with(&[0xFF, 0xFE]) {
                be = false;
                r = &r[2..];
            }
            if r.len() % 2 != 0 {
                return Err(E_PARTIAL_CHAR);
            }
            let units: Vec<u16> =
                r.chunks(2).map(|c| if be { u16::from_be_bytes([c[0], c[1]]) } else { u16::from_le_bytes([c[0], c[1]]) }).collect();
            match String::from_utf16(&units) {
                Ok(s) => s.into_bytes(),
                Err(_) => return Err(E_INVALID_TOKEN),
            }
        }
        b"ISO-8859-1" | b"LATIN1" => raw.iter().flat_map(|&b| char::from(b).to_string().into_bytes()).collect(),
        b"US-ASCII" | b"ASCII" => {
            if raw.iter().any(|&b| b >= 0x80) {
                return Err(E_INVALID_TOKEN);
            }
            raw
        }
        _ => return Err(E_UNKNOWN_ENCODING),
    };
    if out.starts_with(b"<?xml") {
        if let Some(end) = find(&out, 0, b"?>") {
            if let Some(e) = find(&out[..end], 0, b"encoding") {
                if let Some(q) = out[e..end].iter().position(|&c| c == b'"' || c == b'\'') {
                    let qa = e + q;
                    let qc = out[qa];
                    if let Some(l) = out[qa + 1..end].iter().position(|&c| c == qc) {
                        out.splice(qa + 1..qa + 1 + l, b"UTF-8".iter().copied());
                    }
                }
            }
        }
    }
    Ok(out)
}

fn pseudo_attr(decl: &[u8], name: &[u8]) -> Option<Vec<u8>> {
    let mut i = 0;
    while let Some(p) = find(decl, i, name) {
        let mut j = p + name.len();
        while j < decl.len() && decl[j].is_ascii_whitespace() {
            j += 1;
        }
        if j < decl.len() && decl[j] == b'=' {
            j += 1;
            while j < decl.len() && decl[j].is_ascii_whitespace() {
                j += 1;
            }
            if j < decl.len() && (decl[j] == b'"' || decl[j] == b'\'') {
                let q = decl[j];
                let k = decl[j + 1..].iter().position(|&c| c == q)? + j + 1;
                return Some(decl[j + 1..k].to_vec());
            }
        }
        i = p + 1;
    }
    None
}

fn find(s: &[u8], from: usize, pat: &[u8]) -> Option<usize> {
    if from > s.len() {
        return None;
    }
    s[from..].windows(pat.len()).position(|w| w == pat).map(|p| p + from)
}

fn is_ws(c: u8) -> bool {
    matches!(c, b' ' | b'\t' | b'\n' | b'\r')
}

unsafe fn opt_cstr(p: *const XChar) -> Option<Vec<u8>> {
    if p.is_null() { None } else { Some(unsafe { CStr::from_ptr(p) }.to_bytes().to_vec()) }
}

/// expat's error code for a document the verified parser rejected, from
/// what is at the place it stopped. The verdict is the verified parser's;
/// the code is a diagnostic, as expat's own are.
fn classify(text: &[u8], e: &super::Error) -> (c_int, usize) {
    let off = e.offset.min(text.len());
    if let Some(enc) = declared_encoding(text) {
        let up = enc.to_ascii_uppercase();
        let known: &[&[u8]] = &[b"UTF-8", b"UTF-16", b"ISO-8859-1", b"US-ASCII", b"UTF-16BE", b"UTF-16LE"];
        if !known.contains(&up.as_slice()) {
            let at = find(text, 0, b"encoding").and_then(|p| text[p..].iter().position(|&c| c == b'"' || c == b'\'').map(|q| p + q + 1));
            return (E_UNKNOWN_ENCODING, at.unwrap_or(0));
        }
    }
    let code = classify_code(text, e, off);
    let at = match code {
        E_TAG_MISMATCH => off + 2,
        E_NO_ELEMENTS => text.len(),
        E_DUPLICATE_ATTRIBUTE => duplicate_at(text, off).unwrap_or(off),
        _ => off,
    };
    (code, at)
}

/// Where the second of two equal attribute names is, in the start tag at
/// `off` (or the one that contains it).
fn duplicate_at(text: &[u8], off: usize) -> Option<usize> {
    let lt = text[..=off.min(text.len() - 1)].iter().rposition(|&c| c == b'<')?;
    let (end, _) = tag_end_scan(text, lt)?;
    let tag = &text[lt..end];
    let mut names: Vec<&[u8]> = Vec::new();
    let mut i = 1 + name_at(&tag[1..])?.len();
    loop {
        while i < tag.len() && is_ws(tag[i]) {
            i += 1;
        }
        let n = name_at(&tag[i..])?;
        if names.contains(&n) {
            return Some(lt + i);
        }
        names.push(n);
        let q = tag[i..].iter().position(|&c| c == b'"' || c == b'\'')? + i;
        let qc = tag[q];
        i = tag[q + 1..].iter().position(|&c| c == qc)? + q + 2;
    }
}

fn classify_code(text: &[u8], e: &super::Error, off: usize) -> c_int {
    let rest = &text[off..];
    if e.kind == super::ErrorKind::Encoding {
        // A truncated UTF-8 sequence at the end of the input.
        if !rest.is_empty() && rest[0] >= 0xC0 && rest.len() < utf8_len(rest[0]) {
            return E_PARTIAL_CHAR;
        }
        return E_INVALID_TOKEN;
    }
    if off == 0 && rest.starts_with(b"<?xml") {
        return E_XML_DECL;
    }
    if rest.starts_with(b"<?xml") && rest.len() > 5 && (is_ws(rest[5]) || rest[5] == b'?') {
        return E_MISPLACED_XML_PI;
    }
    // The verified parser points at an element's start tag when the tag is
    // wrong as a whole, or when the input ended inside the element.
    if rest == b"<" {
        // The input ends after '<'.
        return E_UNCLOSED_TOKEN;
    }
    if rest.starts_with(b"<") && !rest.starts_with(b"</") && !rest.starts_with(b"<?") && !rest.starts_with(b"<!") {
        // Not a name after '<'.
        if rest.len() > 1 && !(rest[1].is_ascii_alphabetic() || rest[1] == b'_' || rest[1] == b':' || rest[1] >= 0x80) {
            return E_INVALID_TOKEN;
        }
        if duplicate_at(text, off).is_some() {
            return E_DUPLICATE_ATTRIBUTE;
        }
        if tag_end_scan(text, off).is_some() && open_depth(text).map_or(false, |d| d > 0) && open_depth(&text[..off]).unwrap_or(0) < open_depth(text).unwrap() {
            return E_NO_ELEMENTS;
        }
    }
    let depth = open_depth(&text[..off]);
    if rest.is_empty() || rest.iter().all(|&c| is_ws(c)) {
        if depth.is_none() {
            return E_NO_ELEMENTS;
        }
        let tail = &text[..off];
        if let Some(lt) = tail.iter().rposition(|&c| c == b'<') {
            let after = &tail[lt..];
            if after.starts_with(b"<![CDATA[") && find(after, 0, b"]]>").is_none() {
                return E_UNCLOSED_CDATA_SECTION;
            }
            if !after.contains(&b'>') {
                return E_UNCLOSED_TOKEN;
            }
        }
        return E_NO_ELEMENTS;
    }
    if rest.starts_with(b"<![CDATA[") && find(rest, 0, b"]]>").is_none() {
        return E_UNCLOSED_CDATA_SECTION;
    }
    if rest.starts_with(b"</") {
        // The input ends inside the end tag.
        if !rest.contains(&b'>') && depth.map_or(false, |d| d > 0) {
            return E_UNCLOSED_TOKEN;
        }
        return if depth.map_or(false, |d| d > 0) { E_TAG_MISMATCH } else { E_INVALID_TOKEN };
    }
    if depth.is_none() && !rest.starts_with(b"<") && !is_ws(rest[0]) {
        return E_SYNTAX;
    }
    // Markup after the root element that the input ends inside of.
    if depth == Some(0) && rest[0] == b'<' && !rest.contains(&b'>') {
        return E_UNCLOSED_TOKEN;
    }
    if depth == Some(0) && !rest.starts_with(b"<!--") && !rest.starts_with(b"<?") && !is_ws(rest[0]) {
        return E_JUNK_AFTER_DOC_ELEMENT;
    }
    if rest[0] == b'&' {
        if rest.starts_with(b"&#") {
            return E_BAD_CHAR_REF;
        }
        let n = rest[1..].iter().position(|&c| c == b';').unwrap_or(0);
        let name = &rest[1..1 + n];
        return match declared_kind(text, name) {
            None => E_UNDEFINED_ENTITY,
            Some(Decl::Unparsed) => E_BINARY_ENTITY_REF,
            Some(Decl::External) if in_attribute(&text[..off]) => E_ATTRIBUTE_EXTERNAL_ENTITY_REF,
            // An element begun in the entity's text and not ended there,
            // or ended there and not begun.
            Some(Decl::Internal) if internal_value(text, name).is_some_and(|v| !balanced(v)) => E_ASYNC_ENTITY,
            Some(_) => E_RECURSIVE_ENTITY_REF,
        };
    }
    if rest[0] == b'%' {
        return E_PARAM_ENTITY_REF;
    }
    // An attribute named twice in a start tag.
    if let Some(n) = name_at(rest) {
        let tail = &text[..off];
        if let Some(lt) = tail.iter().rposition(|&c| c == b'<') {
            let tag = &tail[lt..];
            if tag.len() > 1 && !matches!(tag[1], b'!' | b'?' | b'/') && !tag.contains(&b'>') {
                let mut pat = Vec::from(b" ".as_slice());
                pat.extend_from_slice(n);
                let earlier = tag
                    .windows(n.len() + 1)
                    .enumerate()
                    .any(|(k, w)| (is_ws(w[0]) && &w[1..] == n) && tag[k + 1 + n.len()..].iter().find(|&&c| !is_ws(c)) == Some(&b'='));
                if earlier {
                    return E_DUPLICATE_ATTRIBUTE;
                }
            }
        }
    }
    E_INVALID_TOKEN
}

fn utf8_len(b: u8) -> usize {
    if b >= 0xF0 { 4 } else if b >= 0xE0 { 3 } else { 2 }
}

fn name_at(s: &[u8]) -> Option<&[u8]> {
    let n = s.iter().position(|&c| is_ws(c) || matches!(c, b'=' | b'>' | b'/' | b'<' | b'"' | b'\'')).unwrap_or(s.len());
    if n == 0 { None } else { Some(&s[..n]) }
}

fn in_attribute(before: &[u8]) -> bool {
    let lt = before.iter().rposition(|&c| c == b'<');
    let gt = before.iter().rposition(|&c| c == b'>');
    match (lt, gt) {
        (Some(l), Some(g)) => l > g,
        (Some(_), None) => true,
        _ => false,
    }
}

fn declared_encoding(text: &[u8]) -> Option<Vec<u8>> {
    if !text.starts_with(b"<?xml") {
        return None;
    }
    let end = find(text, 0, b"?>")?;
    pseudo_attr(&text[5..end], b"encoding")
}

enum Decl {
    Internal,
    External,
    Unparsed,
}

/// How the general entity `name` is declared, by a scan of the text (for
/// error codes only).
fn declared_kind(text: &[u8], name: &[u8]) -> Option<Decl> {
    let mut i = 0;
    while let Some(p) = find(text, i, b"<!ENTITY") {
        let mut j = p + 8;
        while j < text.len() && is_ws(text[j]) {
            j += 1;
        }
        if text[j..].starts_with(name) && text.get(j + name.len()).map_or(false, |&c| is_ws(c)) {
            let end = text[j..].iter().position(|&c| c == b'>').map_or(text.len(), |e| j + e);
            let decl = &text[j + name.len()..end];
            let t = decl.iter().position(|&c| !is_ws(c)).map_or(&b""[..], |k| &decl[k..]);
            return Some(if t.starts_with(b"\"") || t.starts_with(b"'") {
                Decl::Internal
            } else if find(decl, 0, b"NDATA").is_some() {
                Decl::Unparsed
            } else {
                Decl::External
            });
        }
        i = p + 1;
    }
    None
}

/// The literal value of the internal general entity `name`, by a scan of
/// the text (for error codes only).
fn internal_value<'a>(text: &'a [u8], name: &[u8]) -> Option<&'a [u8]> {
    let mut i = 0;
    while let Some(p) = find(text, i, b"<!ENTITY") {
        let mut j = p + 8;
        while j < text.len() && is_ws(text[j]) {
            j += 1;
        }
        if text[j..].starts_with(name) && text.get(j + name.len()).is_some_and(|&c| is_ws(c)) {
            let mut k = j + name.len();
            while k < text.len() && is_ws(text[k]) {
                k += 1;
            }
            let q = *text.get(k)?;
            if q != b'"' && q != b'\'' {
                return None;
            }
            let e = text[k + 1..].iter().position(|&c| c == q)? + k + 1;
            return Some(&text[k + 1..e]);
        }
        i = p + 1;
    }
    None
}

/// Whether the elements in `v` end where they begin.
fn balanced(v: &[u8]) -> bool {
    let mut depth = 0usize;
    let mut i = 0;
    while let Some(k) = v[i..].iter().position(|&c| c == b'<') {
        let t = &v[i + k..];
        let end = t.iter().position(|&c| c == b'>').map_or(t.len(), |e| e + 1);
        if t.starts_with(b"</") {
            if depth == 0 {
                return false;
            }
            depth -= 1;
        } else if !t.starts_with(b"<!") && !t.starts_with(b"<?") && !t[..end].ends_with(b"/>") {
            depth += 1;
        }
        i += k + end.max(1);
    }
    depth == 0
}

/// How many elements are open at the end of `s` (`None` before the root),
/// by a rough scan (for error codes only).
fn open_depth(s: &[u8]) -> Option<usize> {
    let mut depth = 0usize;
    let mut seen_root = false;
    let mut i = 0;
    while let Some(k) = s[i..].iter().position(|&c| c == b'<') {
        let p = i + k;
        let r = &s[p..];
        if r.starts_with(b"<!--") {
            i = find(s, p + 4, b"-->").map_or(s.len(), |e| e + 3);
        } else if r.starts_with(b"<![CDATA[") {
            i = find(s, p + 9, b"]]>").map_or(s.len(), |e| e + 3);
        } else if r.starts_with(b"<?") {
            i = find(s, p + 2, b"?>").map_or(s.len(), |e| e + 2);
        } else if r.starts_with(b"<!DOCTYPE") {
            // Skip to the end of the declaration, past an internal subset.
            let close = match find(s, p, b"]>") {
                Some(e) if s[p..e].contains(&b'[') => e + 2,
                _ => s[p..].iter().position(|&c| c == b'>').map_or(s.len(), |e| p + e + 1),
            };
            i = close;
        } else if r.starts_with(b"</") {
            depth = depth.saturating_sub(1);
            i = p + 2;
        } else {
            let end = tag_end_scan(s, p);
            match end {
                Some((e, empty)) => {
                    seen_root = true;
                    if !empty {
                        depth += 1;
                    }
                    i = e;
                }
                None => {
                    seen_root = true;
                    depth += 1;
                    i = s.len();
                }
            }
        }
        if i >= s.len() {
            break;
        }
    }
    if seen_root { Some(depth) } else { None }
}

/// The end of the start tag at `p` (after its `>`), quotes respected, and
/// whether it is an empty-element tag.
fn tag_end_scan(s: &[u8], p: usize) -> Option<(usize, bool)> {
    let mut q = 0u8;
    let mut j = p + 1;
    while j < s.len() {
        let c = s[j];
        if q != 0 {
            if c == q {
                q = 0;
            }
        } else if c == b'"' || c == b'\'' {
            q = c;
        } else if c == b'>' {
            return Some((j + 1, s[j - 1] == b'/'));
        }
        j += 1;
    }
    None
}

// ---------------------------------------------------------------------------
// The walk: one event per step, so that a handler can stop or suspend.
// ---------------------------------------------------------------------------

impl Parser {
    fn doc(&self) -> &'static Document<'static> {
        // The document is boxed; it stays where it is until the parser is
        // reset or freed, which no handler may do while it runs.
        let d: &Document<'static> = self.doc.as_ref().unwrap();
        unsafe { &*(d as *const Document<'static>) }
    }

    /// Walks until the document ends, an error, or a handler stops the
    /// parser.
    fn walk(&mut self) -> c_int {
        self.parsing = P_PARSING;
        self.set_walking(true);
        let r = self.walk_inner();
        self.set_walking(false);
        r
    }

    /// Mark whether a handler or callback may be running. The write is
    /// volatile so that it is not moved past the foreign call, which reads
    /// the flag through its own pointer to the parser.
    fn set_walking(&mut self, v: bool) -> bool {
        let w = self.walking;
        unsafe { std::ptr::write_volatile(&mut self.walking, v) };
        w
    }

    fn walk_inner(&mut self) -> c_int {
        loop {
            if self.parsing == P_SUSPENDED {
                return STATUS_SUSPENDED;
            }
            if self.parsing == P_FINISHED {
                // Stopped by a handler: a suspended parser stopped for good
                // is aborted, as libexpat's processors report it.
                if self.error == E_NONE {
                    self.error = E_ABORTED;
                    self.err_at = self.ev.0;
                }
                return STATUS_ERROR;
            }
            if self.phase == Phase::Done {
                let n = self.text().len().saturating_sub(if self.ext.is_some() { WRAP_END.len() } else { 0 });
                self.ev = (n, n);
                self.parsing = P_FINISHED;
                return STATUS_OK;
            }
            match self.step() {
                Ok(()) => {}
                Err(NEED_MORE) => return self.chunk_read(),
                Err(code) => {
                    self.err_at = self.ev.0;
                    return self.fail(code);
                }
            }
        }
    }

    fn step(&mut self) -> Result<(), c_int> {
        let doc = self.doc();
        if self.phase == Phase::Content && self.pending_text_decl.is_some() {
            // An external entity's text declaration, before its content.
            let (v, e) = self.pending_text_decl.take().unwrap();
            if let Some(f) = self.h.xml_decl {
                self.s_clear();
                let vk = v.map(|v| self.s_push(&v));
                let ek = e.map(|e| self.s_push(&e));
                let arg = self.arg();
                unsafe { f(arg, self.s_opt(vk), self.s_opt(ek), -1) };
            }
            return Ok(());
        }
        match self.phase {
            Phase::Prolog(i) if self.stream.is_some() && self.ext.is_some() => {
                // The wrapper's prolog and start tag: nothing to report.
                let toks = doc.toks(Src::Doc);
                if i >= toks.len() {
                    return Err(NEED_MORE);
                }
                if toks[i].kind == Kind::STag {
                    let mut k = i + 1;
                    while k + 1 < toks.len() && toks[k].kind == Kind::Attr {
                        k += 2;
                    }
                    self.start_content(Cursor::new(toks, k, toks.len(), 1, false), Some(Open::Wrapper));
                    self.phase = Phase::Content;
                    self.last_end = self.origin.saturating_sub(self.sbase);
                    return Ok(());
                }
                self.phase = Phase::Prolog(i + 1);
                Ok(())
            }
            Phase::Prolog(i) if self.stream.is_some() => {
                let toks = doc.toks(Src::Doc);
                if i >= toks.len() {
                    return Err(NEED_MORE);
                }
                if toks[i].kind == Kind::STag {
                    self.phase = Phase::Content;
                    self.start_content(Cursor::new(toks, i, toks.len(), 0, false), None);
                    return Ok(());
                }
                self.phase = Phase::Prolog(i + 1);
                self.prolog_tok(doc, toks, i)
            }
            Phase::Prolog(i) => {
                let toks = doc.toks(Src::Doc);
                if i >= doc.root {
                    self.phase = Phase::Content;
                    let close = toks[doc.root].c();
                    self.start_content(Cursor::new(toks, doc.root, close + 1, 0, false), None);
                    return Ok(());
                }
                self.phase = Phase::Prolog(i + 1);
                let r = self.prolog_tok(doc, toks, i);
                if toks[i].kind == Kind::Doctype && doc.flattened() {
                    // The declarations are the DTD read whole's.
                    let Phase::Prolog(j) = self.phase else { return r };
                    self.dt_resume = j + toks[j..].iter().position(|t| t.kind == Kind::DoctypeEnd).unwrap_or(toks.len() - j);
                    self.phase = Phase::Dtd(0);
                    self.dsrc = Src::Pro;
                }
                r
            }
            Phase::Dtd(k) => {
                let ftoks = doc.toks(Src::Pro);
                if k >= ftoks.len() {
                    self.dsrc = Src::Doc;
                    self.phase = Phase::Prolog(self.dt_resume);
                    return Ok(());
                }
                self.phase = Phase::Prolog(k + 1);
                // Positions stay the document type declaration's.
                let ev = self.ev;
                let r = self.prolog_tok(doc, ftoks, k);
                if let Phase::Prolog(n) = self.phase {
                    self.phase = Phase::Dtd(n);
                }
                self.ev = ev;
                r
            }
            Phase::Content => self.content_step(doc),
            Phase::Epilog(i) => {
                let toks = doc.toks(Src::Doc);
                self.epilog_space(doc, toks.get(i).copied());
                if self.parsing != P_PARSING {
                    return Ok(());
                }
                if i >= toks.len() {
                    if self.stream.is_some() && self.sverdict != R_OK {
                        return Err(NEED_MORE);
                    }
                    self.phase = Phase::Done;
                    return Ok(());
                }
                self.phase = Phase::Epilog(i + 1);
                let t = toks[i];
                match t.kind {
                    Kind::Comment => self.comment(doc, Src::Doc, t, true),
                    Kind::PI => {
                        self.phase = Phase::Epilog(i + 2);
                        self.pi(doc, Src::Doc, t, toks[i + 1], true)
                    }
                    _ => {}
                }
                Ok(())
            }
            Phase::Done => Ok(()),
        }
    }

    /// White space in the epilog before `next` (or, at the end of what
    /// has been read, all of it but a last CR that may begin a CR LF),
    /// to the default handler, as expat reports it.
    fn epilog_space(&mut self, doc: &'static Document<'static>, next: Option<Tok>) {
        if self.ext.is_some() || self.h.default.is_none() {
            return;
        }
        let text = doc.text();
        let a = self.last_end.min(text.len());
        let mut b = match next {
            Some(t) if t.kind == Kind::Comment => t.a() - 4,
            Some(t) => t.a() - 2,
            None => text.len(),
        };
        b = a + text[a..b.max(a)].iter().take_while(|&&c| is_ws(c)).count();
        // A CR that ends the input so far is reported with what follows it
        // (the window may not keep it).
        let hold = next.is_none() && self.stream.is_some() && !self.final_buffer && b > a && text[b - 1] == b'\r';
        let cr = std::mem::replace(&mut self.epilog_cr, hold);
        if b > a || cr {
            let e = if hold { b - 1 } else { b };
            self.set_ev(a, b);
            self.last_end = b;
            if cr {
                let mut v = vec![b'\r'];
                v.extend_from_slice(&text[a..e]);
                self.report_default_bytes(&v);
            } else if e > a {
                self.report_default(a, e);
            }
        }
    }

    fn set_ev(&mut self, a: usize, b: usize) {
        self.ev = (a, b);
    }

    fn report_default(&mut self, a: usize, b: usize) {
        if let Some(f) = self.h.default {
            let doc = self.doc();
            let t = &doc.text()[a..b];
            let arg = self.arg();
            for c in t.chunks(i32::MAX as usize) {
                unsafe { f(arg, c.as_ptr() as *const XChar, c.len() as c_int) };
            }
        }
    }

    fn report_default_bytes(&mut self, t: &[u8]) {
        if let Some(f) = self.h.default {
            let arg = self.arg();
            unsafe { f(arg, t.as_ptr() as *const XChar, t.len() as c_int) };
        }
    }

    // --- scratch strings -------------------------------------------------

    fn s_clear(&mut self) {
        self.scratch.clear();
        self.offs.clear();
    }

    /// Adds a NUL-terminated string to the scratch area; its index.
    fn s_push(&mut self, s: &[u8]) -> usize {
        self.offs.push(self.scratch.len());
        self.scratch.extend_from_slice(s);
        self.scratch.push(0);
        self.offs.len() - 1
    }

    fn s_ptr(&self, k: usize) -> *const XChar {
        unsafe { self.scratch.as_ptr().add(self.offs[k]) as *const XChar }
    }

    fn s_opt(&self, k: Option<usize>) -> *const XChar {
        k.map_or(null(), |k| self.s_ptr(k))
    }

    // --- the prolog and the DTD ------------------------------------------

    fn prolog_tok(&mut self, doc: &'static Document<'static>, toks: &'static [Tok], i: usize) -> Result<(), c_int> {
        let t = toks[i];
        let text = doc.buf(self.dsrc);
        let here = self.dsrc == Src::Doc;
        match t.kind {
            Kind::XmlDecl => {
                let end = find(text, 0, b"?>").map_or(text.len(), |e| e + 2);
                self.set_ev(0, end);
                let enc = if i + 1 < toks.len() && toks[i + 1].kind == Kind::Encoding { Some(toks[i + 1]) } else { None };
                if enc.is_some() {
                    self.phase = Phase::Prolog(i + 2);
                }
                if let Some(f) = self.h.xml_decl {
                    self.s_clear();
                    let v = self.s_push(&text[t.a()..t.b()]);
                    let e = enc.map(|e| self.s_push(&text[e.a()..e.b()]));
                    let sd = match t.f {
                        1 => 1,
                        2 => 0,
                        _ => -1,
                    };
                    let arg = self.arg();
                    unsafe { f(arg, self.s_ptr(v), self.s_opt(e), sd) };
                } else {
                    self.report_default(0, end);
                }
            }
            Kind::Comment => self.comment(doc, self.dsrc, t, here),
            Kind::PI => {
                self.phase = Phase::Prolog(i + 2);
                self.pi(doc, self.dsrc, t, toks[i + 1], here);
            }
            Kind::Doctype => {
                let mut j = i + 1;
                let (mut pubid, mut sysid) = (None, None);
                let mut last = t.b();
                while j < toks.len() && matches!(toks[j].kind, Kind::PubId | Kind::SysId) {
                    if toks[j].kind == Kind::PubId {
                        pubid = Some(toks[j]);
                    } else {
                        sysid = Some(toks[j]);
                    }
                    last = toks[j].b() + 1;
                    j += 1;
                }
                self.phase = Phase::Prolog(j);
                let mut k = last;
                while k < text.len() && is_ws(text[k]) {
                    k += 1;
                }
                let subset = k < text.len() && text[k] == b'[';
                self.set_ev(t.a().saturating_sub(10), k + 1);
                self.dtd_skip = false;
                if let Some(f) = self.h.start_doctype {
                    self.s_clear();
                    let n = self.s_push(&text[t.a()..t.b()]);
                    let s = sysid.map(|s| self.s_push(&text[s.a()..s.b()]));
                    let p = pubid.map(|p| self.s_push(&text[p.a()..p.b()]));
                    let arg = self.arg();
                    unsafe { f(arg, self.s_ptr(n), self.s_opt(s), self.s_opt(p), subset as c_int) };
                }
                self.doctype_ext = sysid.map(|s| (text[s.a()..s.b()].to_vec(), pubid.map(|p| text[p.a()..p.b()].to_vec())));
            }
            Kind::DoctypeEnd => {
                self.doctype_end(doc)?;
            }
            Kind::ElementDecl => {
                self.set_ev(t.a().saturating_sub(10), t.b());
                if let Some(f) = self.h.element_decl {
                    let end = text[t.b()..].iter().position(|&c| c == b'>').map_or(text.len(), |e| t.b() + e);
                    let model = content_model(&text[t.b()..end], self.mem);
                    if model.is_null() {
                        return Err(E_NO_MEMORY);
                    }
                    self.s_clear();
                    let n = self.s_push(&text[t.a()..t.b()]);
                    let arg = self.arg();
                    unsafe { f(arg, self.s_ptr(n), model) };
                }
            }
            Kind::AttlistDecl => {
                self.attlist_elem = (t.a(), t.b());
            }
            Kind::AttDef => {
                self.phase = Phase::Prolog(i + 2);
                let d = toks[i + 1];
                self.set_ev(t.a(), d.b());
                if self.dtd_skip {
                    return Ok(());
                }
                if let Some(f) = self.h.attlist_decl {
                    let ty = att_type(text, t);
                    let dflt = if d.f >= 3 {
                        Some(doc.value(self.dsrc, d.a(), d.b(), false, t.f, usize::MAX).unwrap_or(Cow::Borrowed(&[])))
                    } else {
                        None
                    };
                    self.s_clear();
                    let (ea, eb) = self.attlist_elem;
                    let e = self.s_push(&text[ea..eb]);
                    let n = self.s_push(&text[t.a()..t.b()]);
                    let ty = self.s_push(&ty);
                    let v = dflt.map(|v| self.s_push(&v));
                    let req = (d.f == 1 || d.f == 3) as c_int;
                    let arg = self.arg();
                    unsafe { f(arg, self.s_ptr(e), self.s_ptr(n), self.s_ptr(ty), self.s_opt(v), req) };
                }
            }
            Kind::EntityDecl => self.entity_decl(doc, toks, i)?,
            Kind::NotationDecl => {
                let mut j = i + 1;
                let (mut pubid, mut sysid) = (None, None);
                while j < toks.len() && matches!(toks[j].kind, Kind::PubId | Kind::SysId) {
                    if toks[j].kind == Kind::PubId {
                        pubid = Some(toks[j]);
                    } else {
                        sysid = Some(toks[j]);
                    }
                    j += 1;
                }
                self.phase = Phase::Prolog(j);
                self.set_ev(t.a().saturating_sub(11), t.b());
                if let Some(f) = self.h.notation {
                    self.s_clear();
                    let n = self.s_push(&text[t.a()..t.b()]);
                    let b = self.base.clone().map(|b| self.s_push(&b));
                    let s = sysid.map(|s| self.s_push(&text[s.a()..s.b()]));
                    let p = pubid.map(|p| self.s_push(&text[p.a()..p.b()]));
                    let arg = self.arg();
                    unsafe { f(arg, self.s_ptr(n), self.s_opt(b), self.s_opt(s), self.s_opt(p)) };
                }
            }
            Kind::PERef => {
                self.set_ev(t.a().saturating_sub(1), t.b() + 1);
                if !doc.standalone() {
                    self.dtd_skip = true;
                }
                if let Some(f) = self.h.skipped {
                    self.s_clear();
                    let n = self.s_push(&text[t.a()..t.b()]);
                    let arg = self.arg();
                    unsafe { f(arg, self.s_ptr(n), 1) };
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn doctype_end(&mut self, doc: &'static Document<'static>) -> Result<(), c_int> {
        // The external subset: offered to the handler, not read.
        let want_ext = self.param_parsing != 0 || self.foreign_dtd;
        let standalone = doc.standalone();
        if want_ext && !(self.param_parsing == 1 && standalone) {
            let ext = self.doctype_ext.take().filter(|_| !self.ext_read);
            if let (Some(f), Some((sys, pubid))) = (self.h.ext_ref, ext) {
                self.s_clear();
                let b = self.base.clone().map(|b| self.s_push(&b));
                let s = self.s_push(&sys);
                let p = pubid.map(|p| self.s_push(&p));
                let me = self.h.ext_ref_arg.unwrap_or(self as *mut Parser);
                if unsafe { f(me, null(), self.s_opt(b), self.s_ptr(s), self.s_opt(p)) } == 0 {
                    return Err(E_EXTERNAL_ENTITY_HANDLING);
                }
            }
        }
        if let Some(f) = self.h.end_doctype {
            let arg = self.arg();
            unsafe { f(arg) };
        }
        if !doc.dtd.wfc {
            if let Some(f) = self.h.not_standalone {
                let arg = self.arg();
                if unsafe { f(arg) } == 0 {
                    return Err(E_NOT_STANDALONE);
                }
            }
        }
        Ok(())
    }

    fn entity_decl(&mut self, doc: &'static Document<'static>, toks: &'static [Tok], i: usize) -> Result<(), c_int> {
        let text = doc.buf(self.dsrc);
        let t = toks[i];
        let pe = t.f != 0;
        let mut j = i + 1;
        let (mut value, mut pubid, mut sysid, mut ndata) = (None, None, None, None);
        while j < toks.len() {
            match toks[j].kind {
                Kind::EntityValue => value = Some(toks[j]),
                Kind::PubId => pubid = Some(toks[j]),
                Kind::SysId => sysid = Some(toks[j]),
                Kind::NData => ndata = Some(toks[j]),
                _ => break,
            }
            j += 1;
        }
        self.phase = Phase::Prolog(j);
        self.set_ev(t.a().saturating_sub(9), toks[j - 1].b());
        if self.dtd_skip {
            return Ok(());
        }
        let name = &text[t.a()..t.b()];
        if !self.seen_ents.insert((pe, name.to_vec())) {
            return Ok(());
        }
        let repl: Option<Cow<[u8]>> = value.map(|v| {
            if pe {
                Cow::Borrowed(&text[v.a()..v.b()])
            } else {
                match doc.dtd.ents.iter().position(|e| e.a == t.a()) {
                    Some(k) if k < doc.dtd.rts.len() => Cow::Borrowed(&doc.dtd.rts[k][..]),
                    _ => Cow::Borrowed(&text[v.a()..v.b()]),
                }
            }
        });
        if let Some(f) = self.h.entity_decl {
            self.s_clear();
            let n = self.s_push(name);
            let v = repl.as_ref().map(|r| self.s_push(r));
            let vlen = repl.as_ref().map_or(0, |r| r.len() as c_int);
            let b = if value.is_none() { self.base.clone().map(|b| self.s_push(&b)) } else { None };
            let s = sysid.map(|s| self.s_push(&text[s.a()..s.b()]));
            let p = pubid.map(|p| self.s_push(&text[p.a()..p.b()]));
            let nd = ndata.map(|d| self.s_push(&text[d.a()..d.b()]));
            let arg = self.arg();
            unsafe {
                f(arg, self.s_ptr(n), pe as c_int, self.s_opt(v), vlen, self.s_opt(b), self.s_opt(s), self.s_opt(p), self.s_opt(nd))
            };
        } else if let (Some(f), Some(nd)) = (self.h.unparsed, ndata) {
            self.s_clear();
            let n = self.s_push(name);
            let b = self.base.clone().map(|b| self.s_push(&b));
            let s = sysid.map(|s| self.s_push(&text[s.a()..s.b()]));
            let p = pubid.map(|p| self.s_push(&text[p.a()..p.b()]));
            let d = self.s_push(&text[nd.a()..nd.b()]);
            let arg = self.arg();
            unsafe { f(arg, self.s_ptr(n), self.s_opt(b), self.s_opt(s), self.s_opt(p), self.s_ptr(d)) };
        }
        Ok(())
    }

    // --- content -----------------------------------------------------------

    fn comment(&mut self, doc: &'static Document<'static>, src: Src, t: Tok, here: bool) {
        if here {
            self.set_ev(t.a() - 4, t.b() + 3);
            self.last_end = t.b() + 3;
        }
        if let Some(f) = self.h.comment {
            let v = doc.text_of(src, t);
            self.s_clear();
            let k = self.s_push(v.as_bytes());
            let arg = self.arg();
            unsafe { f(arg, self.s_ptr(k)) };
        } else if here {
            self.report_default(t.a() - 4, t.b() + 3);
        }
    }

    fn pi(&mut self, doc: &'static Document<'static>, src: Src, t: Tok, d: Tok, here: bool) {
        let buf = doc.buf(src);
        let end = find(buf, d.b().max(t.b()), b"?>").map_or(buf.len(), |e| e + 2);
        if here {
            self.set_ev(t.a() - 2, end);
            self.last_end = end;
        }
        if let Some(f) = self.h.pi {
            let v = doc.text_of(src, d);
            self.s_clear();
            let n = self.s_push(&buf[t.a()..t.b()]);
            let k = self.s_push(v.as_bytes());
            let arg = self.arg();
            unsafe { f(arg, self.s_ptr(n), self.s_ptr(k)) };
        } else if here {
            self.report_default(t.a() - 2, end);
        }
    }

    fn chars(&mut self, v: &[u8]) {
        if let Some(f) = self.h.chars {
            let arg = self.arg();
            for c in v.chunks(i32::MAX as usize) {
                unsafe { f(arg, c.as_ptr() as *const XChar, c.len() as c_int) };
            }
        }
    }

    /// Whether the current item is in the document itself (not in an
    /// entity's replacement text), so that it has a position of its own.
    fn here(&self) -> bool {
        self.ent_depth == 0
    }

    /// The content walk begins: the document's tape (or the stream's
    /// chunk of it), with the wrapper element open if there is one.
    fn start_content(&mut self, cur: Cursor<'static>, wrapper: Option<Open>) {
        self.opens.clear();
        self.opens.extend(wrapper);
        self.segs = vec![Seg { src: Src::Doc, cur, opens: 0 }];
        self.phase = Phase::Content;
    }

    /// The next item of content, from the verified cursor of the tape on
    /// top. A stream's chunk ends with `NEED_MORE`; the document's content
    /// ends with its root element (or an external entity's wrapper).
    fn content_step(&mut self, doc: &'static Document<'static>) -> Result<(), c_int> {
        let here = self.here();
        let streamed = self.stream.is_some() && here;
        let Some(seg) = self.segs.last_mut() else {
            self.phase = if self.ext.is_some() { Phase::Done } else { Phase::Epilog(0) };
            return Ok(());
        };
        let src = seg.src;
        let toks = seg.cur.toks();
        match seg.cur.next() {
            Item::Done => {
                if streamed {
                    return Err(NEED_MORE);
                }
                let seg = self.segs.pop().unwrap();
                // A tape ends with its elements closed (the cursor walks
                // balanced tapes); any left open are closed here.
                while self.opens.len() > seg.opens {
                    self.close_open(doc, None);
                }
                if self.segs.is_empty() {
                    let close = doc.toks(Src::Doc)[doc.root].c();
                    self.phase = if self.ext.is_some() { Phase::Done } else { Phase::Epilog(close + 1) };
                } else {
                    self.ent_depth -= 1;
                }
                Ok(())
            }
            Item::Start { at, next } => self.start_element(doc, src, at, next, here),
            Item::End { at } => {
                let t = toks[at];
                let span = if streamed && t.b() > 0 { Some((t.a(), t.b())) } else { None };
                let wrapper = self.close_open(doc, span);
                if streamed {
                    let pos = self.segs[0].cur.pos();
                    if wrapper {
                        // An external entity ends with the wrapper.
                        self.segs.clear();
                        self.phase = Phase::Done;
                    } else if self.ext.is_none() && self.opens.is_empty() {
                        self.segs.clear();
                        self.phase = Phase::Epilog(pos);
                    }
                }
                Ok(())
            }
            Item::Leaf { at, .. } => self.content_tok(doc, src, toks, at, here),
        }
    }

    /// The innermost open element ends; whether it was the wrapper.
    fn close_open(&mut self, doc: &'static Document<'static>, span: Option<(usize, usize)>) -> bool {
        match self.opens.pop() {
            Some(Open::Elem { name_at, nb, stag, empty }) => {
                self.end_element(doc, name_at, nb, stag, empty, span);
                false
            }
            Some(Open::Wrapper) => true,
            None => false,
        }
    }

    /// One item of content: the token at `i` of `src`'s.
    fn content_tok(&mut self, doc: &'static Document<'static>, src: Src, toks: &'static [Tok], i: usize, here: bool) -> Result<(), c_int> {
        let t = toks[i];
        match t.kind {
            Kind::Text | Kind::CData => {
                let raw = &doc.buf(src)[t.a()..t.b()];
                let v: Cow<[u8]> = if src == Src::Doc && t.f & 1 != 0 {
                    let mut out = Vec::with_capacity(t.b() - t.a());
                    ex_eol(doc.buf(src), t.a(), t.b(), &mut out);
                    Cow::Owned(out)
                } else {
                    Cow::Borrowed(raw)
                };
                let cdata = t.kind == Kind::CData;
                // A CDATA section from the stream comes in pieces: the first
                // and the last say so.
                let whole = self.stream.is_none() || src != Src::Doc;
                let first = cdata && (whole || t.f & 2 != 0);
                let last = cdata && (whole || t.f & 4 != 0);
                if here {
                    let a = if first { t.a() - 9 } else { t.a() };
                    let b = if last { t.b() + 3 } else { t.b() };
                    self.set_ev(a, b);
                    self.last_end = b;
                }
                if first {
                    if let Some(f) = self.h.start_cdata {
                        let arg = self.arg();
                        unsafe { f(arg) };
                    } else if here && self.h.default.is_some() {
                        self.report_default_bytes(b"<![CDATA[");
                    }
                }
                if self.h.chars.is_some() {
                    self.chars(&v);
                } else if here {
                    self.report_default(t.a(), t.b());
                } else if self.h.default.is_some() {
                    self.report_default_bytes(&v);
                }
                if last {
                    if let Some(f) = self.h.end_cdata {
                        let arg = self.arg();
                        unsafe { f(arg) };
                    } else if here && self.h.default.is_some() {
                        self.report_default_bytes(b"]]>");
                    }
                }
            }
            Kind::CharRef => {
                let buf = doc.buf(src);
                let e = buf[t.a()..].iter().position(|&c| c == b';').map_or(buf.len(), |k| t.a() + k + 1);
                if here {
                    self.set_ev(t.a(), e);
                    self.last_end = e;
                }
                let mut tmp = [0u8; 4];
                let s = char::from_u32(t.b() as u32).map_or(&[][..], |c| c.encode_utf8(&mut tmp).as_bytes());
                if self.h.chars.is_some() {
                    self.chars(s);
                } else if here {
                    self.report_default(t.a(), e);
                }
            }
            Kind::Comment => self.comment(doc, src, t, here),
            Kind::PI => {
                self.pi(doc, src, t, toks[i + 1], here);
            }
            Kind::EntRef => self.entity_ref(doc, src, t, here)?,
            _ => {}
        }
        Ok(())
    }

    fn entity_ref(&mut self, doc: &'static Document<'static>, src: Src, t: Tok, here: bool) -> Result<(), c_int> {
        if here {
            self.set_ev(t.a() - 1, t.b() + 1);
            self.last_end = t.b() + 1;
        }
        let buf = doc.buf(src);
        let name = &buf[t.a()..t.b()];
        match doc.entity(src, t.a(), t.b()) {
            Some((k, true)) => {
                if self.h.default.is_some() && !self.h.default_expand {
                    // expat reports the reference and does not expand it.
                    if here {
                        self.report_default(t.a() - 1, t.b() + 1);
                    } else {
                        let mut r = vec![b'&'];
                        r.extend_from_slice(name);
                        r.push(b';');
                        self.report_default_bytes(&r);
                    }
                    return Ok(());
                }
                let toks = doc.toks(Src::Ent(k));
                let cur = Cursor::new(toks, 0, toks.len(), 0, false);
                self.segs.push(Seg { src: Src::Ent(k), cur, opens: self.opens.len() });
                self.ent_depth += 1;
            }
            Some((k, false)) => {
                if self.open_ents.iter().any(|n| n == name) {
                    return Err(E_RECURSIVE_ENTITY_REF);
                }
                if let Some(f) = self.h.ext_ref {
                    let e = &doc.dtd.ents[k];
                    // A stream's declarations are in its prolog.
                    let (toks, text): (&[Tok], &[u8]) = match self.stream.as_ref() {
                        Some(st) => {
                            let st: &'static Stream = unsafe { &*(&st.st as *const Stream) };
                            (st.prolog_toks(), st.prolog())
                        }
                        None => {
                            let (src, toks) = doc.dtd_toks();
                            (toks, doc.buf(src))
                        }
                    };
                    let decl = toks.iter().position(|x| x.kind == Kind::EntityDecl && x.f == 0 && x.a() == e.a);
                    let (mut sys, mut pubid) = (None, None);
                    if let Some(d) = decl {
                        for x in &toks[d + 1..] {
                            match x.kind {
                                Kind::SysId => sys = Some(&text[x.a()..x.b()]),
                                Kind::PubId => pubid = Some(&text[x.a()..x.b()]),
                                _ => break,
                            }
                        }
                    }
                    let context = self.context(name);
                    self.s_clear();
                    let c = self.s_push(&context);
                    let b = self.base.clone().map(|b| self.s_push(&b));
                    let s = sys.map(|s| self.s_push(s));
                    let p = pubid.map(|p| self.s_push(p));
                    let me = self.h.ext_ref_arg.unwrap_or(self as *mut Parser);
                    self.open_ents.push(name.to_vec());
                    let r = unsafe { f(me, self.s_ptr(c), self.s_opt(b), self.s_opt(s), self.s_opt(p)) };
                    self.open_ents.pop();
                    if r == 0 {
                        return Err(E_EXTERNAL_ENTITY_HANDLING);
                    }
                } else if here {
                    self.report_default(t.a() - 1, t.b() + 1);
                }
            }
            None => {
                if let Some(f) = self.h.skipped {
                    self.s_clear();
                    let n = self.s_push(name);
                    let arg = self.arg();
                    unsafe { f(arg, self.s_ptr(n), 0) };
                } else if here {
                    self.report_default(t.a() - 1, t.b() + 1);
                }
            }
        }
        Ok(())
    }

    /// The context string for an external entity: the namespace bindings
    /// in scope (`prefix=uri`, `=uri` for the default), then the name,
    /// separated by form feeds, as expat writes it.
    fn context(&self, name: &[u8]) -> Vec<u8> {
        let mut c = Vec::new();
        if self.ns.is_some() {
            let mut seen: HashSet<&[u8]> = HashSet::new();
            for k in (0..self.ns_stack.len()).rev() {
                let (p, u) = self.ns_stack.get(k);
                if !seen.insert(p) || p == b"xml" {
                    continue;
                }
                c.extend_from_slice(p);
                c.push(b'=');
                c.extend_from_slice(u);
                c.push(0x0C);
            }
        }
        c.extend_from_slice(name);
        c
    }

    /// The start tag at `idx`, its attributes up to `k` (the cursor's
    /// `Start`).
    fn start_element(&mut self, doc: &'static Document<'static>, src: Src, idx: usize, k: usize, here: bool) -> Result<(), c_int> {
        let toks = doc.toks(src);
        let t = toks[idx];
        let buf = doc.buf(src);
        // Where the tag ends, and whether it is empty.
        let after = if k > idx + 1 { toks[k - 1].b() + 1 } else { t.b() };
        let (tag_end, empty) = match buf[after..].iter().position(|&c| c == b'>') {
            Some(p) => (after + p + 1, after + p > 0 && buf[after + p - 1] == b'/'),
            None => (buf.len(), false),
        };
        if here {
            self.set_ev(t.a() - 1, tag_end);
            self.last_end = tag_end;
        }
        let el = Element { doc, src, idx };
        let given = (k - idx - 1) / 2;
        let qname = &buf[t.a()..t.b()];
        self.s_clear();
        let mut nb = 0;
        let mut att_ks = std::mem::take(&mut self.att_ks);
        att_ks.clear();
        let mut nspec = 0;
        self.id_index = -1;
        let name_at = self.names.len();
        if let Some(sep) = self.ns {
            let attrs: Vec<Attribute<'static>> = el.attrs().collect();
            // Namespace declarations first.
            let mut decls: Vec<(Vec<u8>, Vec<u8>)> = Vec::new();
            for a in &attrs {
                let n = a.name.as_bytes();
                let v = a.value.as_bytes();
                // Which prefix it declares, and the constraints on the
                // declaration: verified (`ns::decl_prefix`, `ns::decl_check`).
                let Some(at) = ex_decl_prefix(n) else { continue };
                let p = &n[at..];
                ex_decl_check(p, v, sep).map_err(ns_code)?;
                decls.push((p.to_vec(), v.to_vec()));
            }
            for (p, u) in decls {
                if let Some(f) = self.h.start_ns {
                    let mut s = Vec::with_capacity(p.len() + u.len() + 2);
                    s.extend_from_slice(&p);
                    s.push(0);
                    let po = if p.is_empty() { None } else { Some(0) };
                    let uo = s.len();
                    s.extend_from_slice(&u);
                    s.push(0);
                    let arg = self.arg();
                    let pp = po.map_or(null(), |o| (unsafe { s.as_ptr().add(o) }) as *const XChar);
                    let up = if u.is_empty() { null() } else { (unsafe { s.as_ptr().add(uo) }) as *const XChar };
                    unsafe { f(arg, pp, up) };
                }
                self.ns_stack.push(p, u);
                nb += 1;
            }
            let en = self.expand(qname, true, sep)?;
            self.names.extend_from_slice(&en);
            let mut names: HashSet<Vec<u8>> = HashSet::new();
            for (j, a) in attrs.iter().enumerate() {
                let n = a.name.as_bytes();
                if n == b"xmlns" || n.starts_with(b"xmlns:") {
                    continue;
                }
                let en = self.expand(n, false, sep)?;
                if !names.insert(en.clone()) {
                    return Err(E_DUPLICATE_ATTRIBUTE);
                }
                if j < given {
                    nspec += 1;
                }
                let nk = self.s_push(&en);
                let vk = self.s_push(a.value.as_bytes());
                if self.is_id(doc, qname, n) {
                    self.id_index = (att_ks.len() * 2) as c_int;
                }
                att_ks.push((nk, vk));
            }
        } else {
            self.names.extend_from_slice(qname);
            let ids = doc.has_defs();
            for (j, a) in el.attrs().enumerate() {
                if j < given {
                    nspec += 1;
                }
                let nk = self.s_push(a.name.as_bytes());
                let vk = self.s_push(a.value.as_bytes());
                if ids && self.is_id(doc, qname, a.name.as_bytes()) {
                    self.id_index = (att_ks.len() * 2) as c_int;
                }
                att_ks.push((nk, vk));
            }
        }
        self.names.push(0);
        self.nspecified = nspec * 2;
        if let Some(f) = self.h.start {
            self.atts.clear();
            for &(nk, vk) in &att_ks {
                let (np, vp) = (self.s_ptr(nk), self.s_ptr(vk));
                self.atts.push(np);
                self.atts.push(vp);
            }
            self.atts.push(null());
            let arg = self.arg();
            let np = unsafe { self.names.as_ptr().add(name_at) } as *const XChar;
            unsafe { f(arg, np, self.atts.as_mut_ptr()) };
        } else if here {
            self.report_default(t.a() - 1, tag_end);
        }
        self.att_ks = att_ks;
        self.opens.push(Open::Elem { name_at, nb, stag: t.a() - 1, empty });
        Ok(())
    }

    fn is_id(&self, doc: &Document, elem: &[u8], name: &[u8]) -> bool {
        doc.def_for(elem, name).map_or(false, |d| d.ty == 2)
    }

    /// A name as expat reports it with namespaces: `uri SEP local`, and
    /// `SEP prefix` after it with triplets.
    /// (Verified: `ns::expand`.)
    fn expand(&self, qname: &[u8], element: bool, sep: u8) -> Result<Vec<u8>, c_int> {
        ex_expand(&self.ns_stack, qname, element, sep, self.triplets).map_err(ns_code)
    }

    fn end_element(&mut self, doc: &'static Document<'static>, name_at: usize, nb: usize, stag: usize, empty: bool, span: Option<(usize, usize)>) {
        if let (true, Some((a, b))) = (self.here(), span) {
            self.set_ev(a, b);
            self.last_end = b;
        } else if self.here() && empty {
            self.set_ev(self.last_end, self.last_end);
        } else if self.here() {
            let text = doc.text();
            let p = text[self.last_end.max(stag)..].iter().position(|&c| c == b'<').map(|p| p + self.last_end.max(stag));
            match p {
                Some(p) if text[p..].starts_with(b"</") && p >= self.last_end => {
                    let e = text[p..].iter().position(|&c| c == b'>').map_or(text.len(), |k| p + k + 1);
                    self.set_ev(p, e);
                    self.last_end = e;
                }
                _ => {
                    // An empty-element tag: no end tag of its own.
                    self.set_ev(self.last_end, self.last_end);
                }
            }
        }
        if let Some(f) = self.h.end {
            let arg = self.arg();
            unsafe { f(arg, self.names.as_ptr().add(name_at) as *const XChar) };
        } else if self.here() && self.ev.1 > self.ev.0 {
            self.report_default(self.ev.0, self.ev.1);
        }
        self.names.truncate(name_at);
        for _ in 0..nb {
            if let Some(k) = self.ns_stack.len().checked_sub(1) {
                let p = self.ns_stack.get(k).0.to_vec();
                self.ns_stack.pop();
                if let Some(f) = self.h.end_ns {
                    let mut s = p.clone();
                    s.push(0);
                    let arg = self.arg();
                    let pp = if p.is_empty() { null() } else { s.as_ptr() as *const XChar };
                    unsafe { f(arg, pp) };
                }
            }
        }
    }
}

/// The type of an attribute definition as expat's AttlistDeclHandler
/// gives it: `CDATA`, `ID`, ..., `(a|b)` or `NOTATION(a|b)`.
fn att_type(text: &[u8], t: Tok) -> Vec<u8> {
    let names: [&[u8]; 9] = [b"CDATA", b"ID", b"IDREF", b"IDREFS", b"ENTITY", b"ENTITIES", b"NMTOKEN", b"NMTOKENS", b"NOTATION"];
    if (1..=8).contains(&t.f) {
        return names[t.f as usize - 1].to_vec();
    }
    let mut out = Vec::new();
    let rest = &text[t.b()..];
    let open = rest.iter().position(|&c| c == b'(').unwrap_or(0);
    if t.f == 9 {
        out.extend_from_slice(b"NOTATION");
    }
    let close = rest.iter().position(|&c| c == b')').unwrap_or(rest.len().saturating_sub(1));
    out.extend(rest[open..=close.min(rest.len() - 1)].iter().copied().filter(|&c| !is_ws(c)));
    out
}

/// The content model of an element type declaration (the text after its
/// name), as one block from the parser's allocator, as expat allocates it:
/// the cells in breadth-first order, then the names.
fn content_model(spec: &[u8], mem: MemSuite) -> *mut XmlContent {
    struct Cell {
        ty: c_int,
        quant: c_int,
        name: Option<(usize, usize)>,
        kids: Vec<usize>,
    }
    let s: Vec<u8> = spec.to_vec();
    let mut cells: Vec<Cell> = Vec::new();
    let mut i = 0;
    let skip = |i: &mut usize| {
        while *i < s.len() && is_ws(s[*i]) {
            *i += 1;
        }
    };
    let quant = |i: &mut usize| -> c_int {
        let q = match s.get(*i) {
            Some(b'?') => 1,
            Some(b'*') => 2,
            Some(b'+') => 3,
            _ => return 0,
        };
        *i += 1;
        q
    };
    skip(&mut i);
    if s[i..].starts_with(b"EMPTY") {
        cells.push(Cell { ty: 1, quant: 0, name: None, kids: vec![] });
    } else if s[i..].starts_with(b"ANY") {
        cells.push(Cell { ty: 2, quant: 0, name: None, kids: vec![] });
    } else {
        // '(' ... ')': an explicit stack of the open groups.
        cells.push(Cell { ty: 6, quant: 0, name: None, kids: vec![] });
        let mut stack = vec![0usize];
        i += 1;
        loop {
            skip(&mut i);
            if i >= s.len() {
                break;
            }
            let c = s[i];
            if c == b'(' {
                let k = cells.len();
                cells.push(Cell { ty: 6, quant: 0, name: None, kids: vec![] });
                cells[*stack.last().unwrap()].kids.push(k);
                stack.push(k);
                i += 1;
            } else if c == b')' {
                i += 1;
                let k = stack.pop().unwrap();
                cells[k].quant = quant(&mut i);
                if stack.is_empty() {
                    break;
                }
            } else if c == b'|' {
                let k = *stack.last().unwrap();
                if cells[k].ty != 3 {
                    cells[k].ty = 5;
                }
                i += 1;
            } else if c == b',' {
                i += 1;
            } else if s[i..].starts_with(b"#PCDATA") {
                cells[*stack.last().unwrap()].ty = 3;
                i += 7;
            } else {
                let a = i;
                while i < s.len() && !is_ws(s[i]) && !matches!(s[i], b'|' | b',' | b')' | b'(' | b'?' | b'*' | b'+') {
                    i += 1;
                }
                let b = i;
                let q = quant(&mut i);
                let k = cells.len();
                cells.push(Cell { ty: 4, quant: q, name: Some((a, b)), kids: vec![] });
                cells[*stack.last().unwrap()].kids.push(k);
            }
        }
    }
    // Lay out breadth first, so that each cell's children are contiguous.
    let mut order = vec![0usize];
    let mut pos = vec![0usize; cells.len()];
    let mut q = 0;
    while q < order.len() {
        let c = order[q];
        pos[c] = q;
        for &k in &cells[c].kids {
            order.push(k);
        }
        q += 1;
    }
    let n = cells.len();
    let names: usize = cells.iter().map(|c| c.name.map_or(0, |(a, b)| b - a + 1)).sum();
    let bytes = n * std::mem::size_of::<XmlContent>() + names;
    let block = unsafe { (mem.malloc_fcn.unwrap())(bytes.max(1)) } as *mut XmlContent;
    if block.is_null() {
        return null_mut();
    }
    let mut str_at = unsafe { (block as *mut u8).add(n * std::mem::size_of::<XmlContent>()) };
    for (slot, &c) in order.iter().enumerate() {
        let cell = &cells[c];
        let name = match cell.name {
            Some((a, b)) => unsafe {
                std::ptr::copy_nonoverlapping(s[a..b].as_ptr(), str_at, b - a);
                *str_at.add(b - a) = 0;
                let p = str_at as *mut XChar;
                str_at = str_at.add(b - a + 1);
                p
            },
            None => null_mut(),
        };
        let first = cell.kids.first().map_or(0, |&k| pos[k]);
        unsafe {
            block.add(slot).write(XmlContent {
                ty: cell.ty,
                quant: cell.quant,
                name,
                numchildren: cell.kids.len() as c_uint,
                children: if cell.kids.is_empty() { null_mut() } else { block.add(first) },
            });
        }
    }
    block
}

impl Parser {
    /// A document in an encoding the verified parser does not read, with
    /// an `UnknownEncodingHandler`: converted to UTF-8 through the map the
    /// handler fills in, its declaration then naming UTF-8.
    /// Call the unknown encoding's release callback, with the parser
    /// protected against re-entrant calls while it runs.
    fn release_encoding(&mut self) {
        if let Some((r, data)) = self.enc_release.take() {
            let w = self.set_walking(true);
            unsafe { r(data) };
            self.set_walking(w);
        }
    }

    fn unknown_encoding(&mut self, raw: Vec<u8>) -> Result<Vec<u8>, c_int> {
        let Some(f) = self.h.unknown_enc else { return Ok(raw) };
        let name = match self.encoding.clone().or_else(|| declared_encoding(&raw)) {
            Some(n) => n,
            None => return Ok(raw),
        };
        let up = name.to_ascii_uppercase();
        let known: &[&[u8]] = &[b"UTF-8", b"UTF-16", b"ISO-8859-1", b"US-ASCII", b"UTF-16BE", b"UTF-16LE"];
        if known.contains(&up.as_slice()) {
            return Ok(raw);
        }
        let mut info = XmlEncoding { map: [0; 256], data: null_mut(), convert: None, release: None };
        let mut n = name.clone();
        n.push(0);
        let data = self.h.unknown_enc_data.unwrap_or(null_mut());
        let ok = unsafe { f(data, n.as_ptr() as *const XChar, &mut info) } != 0 && valid_map(&info);
        if !ok {
            if let Some(r) = info.release {
                unsafe { r(info.data) };
            }
            return Err(E_UNKNOWN_ENCODING);
        }
        self.release_encoding();
        self.enc_release = info.release.map(|r| (r, info.data));
        // The converter runs as a handler: calls that would parse
        // re-entrantly are refused while it runs.
        let w = self.set_walking(true);
        let mut out = Vec::with_capacity(raw.len());
        let mut i = 0;
        let mut bad = false;
        while i < raw.len() {
            let m = info.map[raw[i] as usize];
            let (cp, len) = if m >= 0 {
                (m, 1)
            } else if m == -1 || (-m) as usize > raw.len() - i || info.convert.is_none() {
                bad = true;
                break;
            } else {
                let c = unsafe { (info.convert.unwrap())(info.data, raw[i..].as_ptr() as *const c_char) };
                (c, (-m) as usize)
            };
            match char::from_u32(cp as u32) {
                Some(c) if cp >= 0 => out.extend_from_slice(c.encode_utf8(&mut [0; 4]).as_bytes()),
                _ => {
                    bad = true;
                    break;
                }
            }
            i += len;
        }
        self.set_walking(w);
        if bad {
            return Err(E_INVALID_TOKEN);
        }
        // Name UTF-8 in the declaration, which is ASCII in both.
        if let Some(p) = find(&out, 0, &name) {
            if out.starts_with(b"<?xml") && p < find(&out, 0, b"?>").unwrap_or(0) {
                out.splice(p..p + name.len(), b"UTF-8".iter().copied());
            }
        }
        Ok(out)
    }
}

/// Whether an unknown encoding's map is one expat accepts: the ASCII
/// characters that mean something in markup map to themselves, a
/// multi-byte lead has a converter, and every other entry is a character
/// up to U+FFFF or -1.
fn valid_map(e: &XmlEncoding) -> bool {
    let markup = |c: usize| matches!(c, 0x09 | 0x0A | 0x0D) || ((0x20..0x7F).contains(&c) && !matches!(c, 0x24 | 0x40 | 0x5C | 0x5E | 0x60 | 0x7B | 0x7D | 0x7E));
    for i in 0..128 {
        if markup(i) && e.map[i] != i as c_int {
            return false;
        }
    }
    for i in 0..256 {
        let c = e.map[i];
        if c == -1 {
            continue;
        }
        if c < 0 {
            if c < -4 || e.convert.is_none() {
                return false;
            }
        } else if c < 0x80 {
            if markup(c as usize) && c as usize != i {
                return false;
            }
        } else if c > 0xFFFF && char::from_u32(c as u32).is_some() {
            return false;
        }
    }
    true
}

// ---------------------------------------------------------------------------
// The C ABI.
// ---------------------------------------------------------------------------

macro_rules! parser {
    ($p:expr) => {
        match unsafe { $p.as_mut() } {
            Some(p) => p,
            None => return Default::default(),
        }
    };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_ParserCreate(encoding: *const XChar) -> *mut Parser {
    Box::into_raw(Parser::new(encoding, SYS_MEM, None))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_ParserCreateNS(encoding: *const XChar, sep: XChar) -> *mut Parser {
    Box::into_raw(Parser::new(encoding, SYS_MEM, Some(sep as u8)))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_ParserCreate_MM(
    encoding: *const XChar,
    mem: *const MemSuite,
    sep: *const XChar,
) -> *mut Parser {
    let mut m = SYS_MEM;
    if let Some(s) = unsafe { mem.as_ref() } {
        m = MemSuite {
            malloc_fcn: s.malloc_fcn.or(SYS_MEM.malloc_fcn),
            realloc_fcn: s.realloc_fcn.or(SYS_MEM.realloc_fcn),
            free_fcn: s.free_fcn.or(SYS_MEM.free_fcn),
        };
    }
    let ns = if sep.is_null() { None } else { Some(unsafe { *sep } as u8) };
    Box::into_raw(Parser::new(encoding, m, ns))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_ParserReset(p: *mut Parser, encoding: *const XChar) -> XBool {
    let p = parser!(p);
    if p.ext.is_some() || p.walking {
        return 0;
    }
    p.reset(encoding);
    1
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_ParserFree(p: *mut Parser) {
    if !p.is_null() && !unsafe { (*p).walking } {
        unsafe { (*p).release_encoding() };
        let mut b = unsafe { Box::from_raw(p) };
        b.doc = None;
        b.owned_text = None;
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_ExternalEntityParserCreate(
    parent: *mut Parser,
    context: *const XChar,
    encoding: *const XChar,
) -> *mut Parser {
    let pp = parser!(parent);
    let mut c = Parser::new(encoding, pp.mem, pp.ns);
    c.user_data = pp.user_data;
    c.handler_arg = pp.handler_arg;
    c.arg_is_parser = pp.arg_is_parser;
    c.h = pp.h;
    c.triplets = pp.triplets;
    c.param_parsing = pp.param_parsing;
    c.base = pp.base.clone();
    c.base_c = pp.base_c.clone();
    c.open_ents = pp.open_ents.clone();
    c.props.reparse = pp.props.reparse;
    if pp.handler_arg == parent as *mut c_void {
        c.arg_is_parser = true;
    }
    if context.is_null() {
        c.ext = Some(Ext::Dtd);
        if pp.collect.is_some() {
            c.collect_to = Some(parent);
        }
        return Box::into_raw(c);
    }
    let ctx = unsafe { CStr::from_ptr(context) }.to_bytes();
    let mut bindings = Vec::new();
    for part in ctx.split(|&b| b == 0x0C) {
        if let Some(eq) = part.iter().position(|&b| b == b'=') {
            bindings.push((part[..eq].to_vec(), part[eq + 1..].to_vec()));
        }
    }
    // The wrapper: the parent's internal subset, then a start tag.
    let mut prefix = Vec::new();
    let parts = match (pp.stream.as_ref(), pp.doc.as_ref()) {
        (Some(st), _) => {
            let toks = st.prolog_toks();
            let n = toks.iter().position(|t| t.kind == Kind::DoctypeEnd).map_or(0, |k| k + 1);
            Some((st.standalone(), &toks[..n], st.prolog()))
        }
        (None, Some(d)) => Some((d.standalone(), d.toks(Src::Doc), d.text())),
        _ => None,
    };
    let flat = pp.doc.as_ref().filter(|d| d.flattened()).map(|d| d.buf(Src::Pro));
    if let Some((standalone, toks, text)) = parts {
        if standalone {
            prefix.extend_from_slice(b"<?xml version=\"1.0\" standalone=\"yes\"?>");
        }
        if let Some((sub, has_ext)) = internal_subset_in(toks, text) {
            prefix.extend_from_slice(b"<!DOCTYPE ");
            prefix.extend_from_slice(WRAP_NAME.as_bytes());
            if has_ext {
                prefix.extend_from_slice(b" SYSTEM \"\"");
            }
            if let Some(f) = flat {
                // The DTD read whole (which ends with ']'), whose external
                // entities are not read again.
                prefix.extend_from_slice(b" [");
                prefix.extend_from_slice(f);
                c.no_load = true;
            } else if let Some((a, b)) = sub {
                prefix.extend_from_slice(b" [");
                prefix.extend_from_slice(&text[a..b]);
                prefix.extend_from_slice(b"]");
            }
            prefix.extend_from_slice(b">");
        }
    }
    prefix.extend_from_slice(b"<");
    prefix.extend_from_slice(WRAP_NAME.as_bytes());
    prefix.extend_from_slice(b">");
    c.ext = Some(Ext::Entity { prefix, bindings });
    Box::into_raw(c)
}

/// The internal subset in the prolog's tokens and text (its span in the
/// text), and whether the document type declaration has an external
/// identifier; `None` without a document type declaration. (A stream's
/// prolog ends with the document type declaration.)
fn internal_subset_in(toks: &[Tok], text: &[u8]) -> Option<(Option<(usize, usize)>, bool)> {
    let di = toks.iter().position(|t| t.kind == Kind::Doctype)?;
    let mut last = toks[di].b();
    let mut j = di + 1;
    let mut has_ext = false;
    while j < toks.len() && matches!(toks[j].kind, Kind::PubId | Kind::SysId) {
        last = toks[j].b() + 1;
        has_ext = true;
        j += 1;
    }
    let mut k = last;
    while k < text.len() && is_ws(text[k]) {
        k += 1;
    }
    if k >= text.len() || text[k] != b'[' {
        return Some((None, has_ext));
    }
    let start = k + 1;
    let e = toks.iter().position(|t| t.kind == Kind::DoctypeEnd)?;
    let m = match toks.get(e + 1) {
        Some(next) => match next.kind {
            Kind::STag => next.a() - 1,
            Kind::Comment => next.a() - 4,
            Kind::PI => next.a() - 2,
            _ => return Some((None, has_ext)),
        },
        None => text.len(),
    };
    let mut q = m;
    while q > start && is_ws(text[q - 1]) {
        q -= 1;
    }
    // At '>'; before it, white space and ']'.
    q = q.saturating_sub(1);
    while q > start && is_ws(text[q - 1]) {
        q -= 1;
    }
    let end = q.saturating_sub(1);
    Some((Some((start, end.max(start))), has_ext))
}

impl Parser {
    fn parse_chunk(&mut self, s: &[u8], is_final: bool) -> c_int {
        match self.parsing {
            P_SUSPENDED => {
                self.error = E_SUSPENDED;
                return STATUS_ERROR;
            }
            P_FINISHED => {
                if self.error == E_NONE {
                    self.error = E_FINISHED;
                }
                return STATUS_ERROR;
            }
            _ => {}
        }
        if let Some(pp) = self.collect_to {
            // For the parent, which reads its DTD whole.
            let pp = unsafe { &mut *pp };
            if let Some(v) = pp.collect.as_mut() {
                v.extend_from_slice(s);
                pp.collect_h = Some((self.base.clone(), self.h.ext_ref, self.h.ext_ref_arg));
                if is_final {
                    let text = v.clone();
                    // Its text declaration, to this parser's handler.
                    if let (Some(f), Ok((Some((ver, enc)), _))) = (self.h.xml_decl, ext_content(&text)) {
                        self.parsing = P_PARSING;
                        self.s_clear();
                        let vk = ver.map(|v| self.s_push(&v));
                        let ek = enc.map(|e| self.s_push(&e));
                        let arg = self.arg();
                        unsafe { f(arg, self.s_opt(vk), self.s_opt(ek), -1) };
                        if self.parsing != P_PARSING {
                            pp.collect_err = true;
                            if self.error == E_NONE {
                                self.error = E_ABORTED;
                            }
                            self.parsing = P_FINISHED;
                            return STATUS_ERROR;
                        }
                    }
                    // This parser's verdict on the entity, read as the
                    // external subset is (the parent reads it in place).
                    if let Err(code) = ext_dtd_check(&text, &crate::pe::open_entities()) {
                        pp.collect_err = true;
                        return self.fail(code);
                    }
                }
            }
            self.parsing = if is_final { P_FINISHED } else { P_PARSING };
            return STATUS_OK;
        }
        self.parsing = P_PARSING;
        self.input.extend_from_slice(s);
        if matches!(self.ext, Some(Ext::Entity { .. })) && !self.whole {
            return self.ext_chunk(is_final);
        }
        // Read as it comes.
        if self.stream.is_some() || self.can_stream() {
            return self.stream_chunk(is_final);
        }
        if !is_final {
            return STATUS_OK;
        }
        self.final_buffer = true;
        if matches!(self.ext, Some(Ext::Dtd)) {
            self.parsing = P_FINISHED;
            return STATUS_OK;
        }
        self.finish()
    }
}

impl Parser {
    /// The push parser reads this document: UTF-8 by its first bytes and
    /// what the caller says (the stream hands any other back, whole).
    fn can_stream(&self) -> bool {
        // (The stream does not expand parameter entities.)
        !self.whole && self.ext.is_none() && self.param_parsing == 0 && self.encoding.as_deref().is_none_or(|e| e.eq_ignore_ascii_case(b"UTF-8"))
    }

    /// An external entity's next chunk: once its text declaration is read,
    /// to the push parser in the wrapper (the parent's declarations, then a
    /// start tag), whose end tag follows the last chunk.
    fn ext_chunk(&mut self, is_final: bool) -> c_int {
        if self.stream.is_none() {
            match ext_head(&self.input, is_final, self.encoding.as_deref()) {
                ExtHead::Wait => return STATUS_OK,
                ExtHead::Whole => {
                    self.whole = true;
                    if !is_final {
                        return STATUS_OK;
                    }
                    self.final_buffer = true;
                    return self.finish();
                }
                ExtHead::Fail(code) => return self.fail(code),
                ExtHead::Stream(decl, skip) => {
                    let Some(Ext::Entity { prefix, bindings }) = &self.ext else { unreachable!() };
                    let mut t = prefix.clone();
                    t.extend_from_slice(&self.input[skip..]);
                    self.origin = prefix.len();
                    self.raw_pre = prefix.len();
                    self.raw_skip = skip;
                    self.line_at = prefix.len();
                    self.line = 1;
                    self.col = 0;
                    self.ns_stack = bindings_of(bindings);
                    self.pending_text_decl = decl;
                    self.input = t;
                }
            }
        }
        if is_final {
            self.input.extend_from_slice(WRAP_END);
        }
        self.stream_chunk(is_final)
    }

    /// The next chunk, to the push parser; then the walk over what it read.
    fn stream_chunk(&mut self, is_final: bool) -> c_int {
        if self.stream.is_none() {
            self.stream = Some(Box::new(Reader::new()));
            self.sbase = 0;
            self.sdtd = false;
            self.phase = Phase::Prolog(0);
        }
        if is_final {
            self.final_buffer = true;
        }
        if let Some(h) = self.held.as_mut() {
            h.extend_from_slice(&self.input);
            self.input.clear();
            return self.chunk_read();
        }
        // Lines are counted up to where the window is kept from, which no
        // event comes before.
        if self.doc.is_some() {
            let keep = self.stream.as_ref().unwrap().keep();
            self.line_col(keep);
        }
        let data = std::mem::take(&mut self.input);
        // `doc` points into the window, which the chunk moves.
        let old = self.doc.take();
        let st = self.stream.as_mut().unwrap();
        let base0 = st.base();
        let r = st.feed(&data, is_final);
        self.input = data;
        self.input.clear();
        let st = self.stream.as_mut().unwrap();
        if r == R_WHOLE && self.ext.is_some() {
            // The wrapper is UTF-8 and its declaration is complete.
            drop(old);
            return self.fail(E_SYNTAX);
        }
        if r == R_WHOLE {
            // Not UTF-8, or a declaration this parser reads whole: nothing
            // has been reported; the document is read at the last chunk.
            drop(old);
            self.input = st.whole_input().to_vec();
            self.stream = None;
            self.whole = true;
            self.phase = Phase::Prolog(0);
            if !is_final {
                return STATUS_OK;
            }
            return self.finish();
        }
        if r == R_LIMIT {
            drop(old);
            return self.fail(E_NO_MEMORY);
        }
        // Positions in the window move with it.
        let d = st.base() - base0;
        self.sbase = st.base();
        for x in [&mut self.ev.0, &mut self.ev.1, &mut self.last_end, &mut self.err_at] {
            *x = x.saturating_sub(d);
        }
        let mut doc = match old {
            Some(doc) if self.sdtd => doc,
            _ => {
                // Before the declarations are final, the document is made
                // again with what the prolog has so far.
                let st: &'static Stream = unsafe { &*(&st.st as *const Stream) };
                self.sdtd = st.dtd_read();
                Box::new(Document::chunk(st.dtd(), st.prolog(), st.prolog_toks(), st.standalone()))
            }
        };
        let st = self.stream.as_mut().unwrap();
        let tape = st.take_out();
        let w: &'static [u8] = unsafe { std::slice::from_raw_parts(st.window().as_ptr(), st.window().len()) };
        doc.set_chunk(w, tape);
        self.doc = Some(doc);
        self.sverdict = r;
        // The walk goes on in the new chunk, with the same elements open.
        if let Some(seg) = self.segs.first_mut() {
            let toks = self.doc.as_ref().unwrap().toks(Src::Doc);
            let toks: &'static [Tok] = unsafe { std::slice::from_raw_parts(toks.as_ptr(), toks.len()) };
            seg.cur = Cursor::new(toks, 0, toks.len(), seg.cur.depth(), false);
        }
        match self.phase {
            Phase::Prolog(_) => self.phase = Phase::Prolog(0),
            Phase::Epilog(_) => self.phase = Phase::Epilog(0),
            _ => {}
        }
        self.walk()
    }

    /// The walk has read the chunk: the stream's verdict.
    fn chunk_read(&mut self) -> c_int {
        match self.sverdict {
            R_MORE => STATUS_OK,
            R_OK => {
                // The walk ends where the document does.
                self.phase = Phase::Done;
                STATUS_OK
            }
            _ => {
                let (code, at, tail) = self.stream_error();
                if !self.final_buffer && tail {
                    self.held.get_or_insert_with(Vec::new);
                    return STATUS_OK;
                }
                self.err_at = at;
                self.fail(code)
            }
        }
    }

    /// Why the stream failed, where in the window, and whether the error
    /// is in a token that runs to the end of the input (which expat waits
    /// to see the end of).
    fn stream_error(&self) -> (c_int, usize, bool) {
        let st = self.stream.as_ref().unwrap();
        let (mut t, n, from) = st.diagnosis();
        if let Some(h) = &self.held {
            t.extend_from_slice(h);
        }
        match plain_parse(&t) {
            // The verified verdict is the stream's.
            Ok(_) => (E_SYNTAX, from, false),
            Err(e) => {
                let (code, at) = classify(&t, &e);
                let (code, at) = if self.ext.is_some() { ext_end_error(&t, code, at) } else { (code, at) };
                let tail = at >= n && at < t.len() && t[at..].iter().all(|&c| !is_ws(c) && !b"<>&;\"'=/?]".contains(&c));
                (code, if at >= n { from + (at - n) } else { from }, tail)
            }
        }
    }
}

/// expat's input buffer (libexpat's `m_buffer` .. `m_bufferLim`), kept as
/// libexpat keeps it, so that `XML_GetBuffer` and `XML_ParseBuffer` behave
/// as there: what it allocates, when it reparses, how much it may take.
/// `ptr` is where expat would have read to (the stream's progress), `fed`
/// how much has been handed to the parser.
struct EBuf {
    buf: *mut u8,
    size: usize,
    ptr: usize,
    fed: usize,
    end: usize,
    /// The offset in the input of `buf[0]`.
    abs0: usize,
    mem: MemSuite,
}

/// libexpat's `XML_CONTEXT_BYTES`, and its first buffer size.
const CONTEXT_BYTES: usize = 1024;
const INIT_BUFFER_SIZE: usize = 1024;

impl EBuf {
    fn new(mem: MemSuite) -> EBuf {
        EBuf { buf: null_mut(), size: 0, ptr: 0, fed: 0, end: 0, abs0: 0, mem }
    }

    /// `XML_GetBuffer`'s room for `len` more bytes: moved down within the
    /// buffer, or a buffer twice as large (or more), as libexpat does.
    fn room(&mut self, len: usize) -> Result<*mut u8, c_int> {
        if len <= self.size - self.end && !self.buf.is_null() {
            return Ok(unsafe { self.buf.add(self.end) });
        }
        let mut needed = len + (self.end - self.ptr);
        let keep = self.ptr.min(CONTEXT_BYTES);
        needed += keep;
        if needed > i32::MAX as usize {
            return Err(E_NO_MEMORY);
        }
        let off = self.ptr - keep;
        if !self.buf.is_null() && needed <= self.size {
            if off > 0 {
                unsafe { std::ptr::copy(self.buf.add(off), self.buf, self.end - off) };
            }
        } else {
            let mut size = if self.size == 0 { INIT_BUFFER_SIZE } else { self.size };
            loop {
                size *= 2;
                if size >= needed || size > i32::MAX as usize {
                    break;
                }
            }
            if size > i32::MAX as usize {
                return Err(E_NO_MEMORY);
            }
            let nb = unsafe { (self.mem.malloc_fcn.unwrap())(size) } as *mut u8;
            if nb.is_null() {
                return Err(E_NO_MEMORY);
            }
            // Every byte is defined, whatever the application writes.
            unsafe { std::ptr::write_bytes(nb, 0, size) };
            if !self.buf.is_null() {
                unsafe {
                    std::ptr::copy_nonoverlapping(self.buf.add(off), nb, self.end - off);
                    (self.mem.free_fcn.unwrap())(self.buf as *mut c_void);
                }
            }
            self.buf = nb;
            self.size = size;
        }
        self.ptr -= off;
        self.fed -= off;
        self.end -= off;
        self.abs0 += off;
        Ok(unsafe { self.buf.add(self.end) })
    }

    /// The bytes not yet handed on.
    fn unfed(&self) -> &'static [u8] {
        if self.buf.is_null() {
            return &[];
        }
        unsafe { std::slice::from_raw_parts(self.buf.add(self.fed), self.end - self.fed) }
    }
}

impl Drop for EBuf {
    fn drop(&mut self) {
        if !self.buf.is_null() {
            unsafe { (self.mem.free_fcn.unwrap())(self.buf as *mut c_void) };
        }
    }
}

/// expat's testing switches (libexpat's `XML_TESTING` build), which its
/// test suite reads and sets.
#[cfg(feature = "expat-testing")]
#[unsafe(no_mangle)]
pub static mut g_reparseDeferralEnabledDefault: u8 = 1;
#[cfg(feature = "expat-testing")]
#[unsafe(no_mangle)]
pub static mut g_bytesScanned: std::ffi::c_uint = 0;

fn reparse_default() -> XBool {
    #[cfg(feature = "expat-testing")]
    {
        unsafe { g_reparseDeferralEnabledDefault }
    }
    #[cfg(not(feature = "expat-testing"))]
    {
        1
    }
}

impl Parser {
    /// A parse attempt over the buffer, as libexpat's `callProcessor`: put
    /// off while a partial token has not grown enough (reparse deferral),
    /// else what has come is handed to the parser.
    fn attempt(&mut self, is_final: bool) -> c_int {
        let have_now = self.eb.end - self.eb.ptr;
        if self.props.reparse != 0 && !is_final {
            let avail = (self.eb.ptr - self.eb.ptr.min(CONTEXT_BYTES)) + (self.eb.size - self.eb.end);
            let enough = have_now >= 2 * self.partial_before || self.last_req > avail;
            if !enough {
                if self.parsing == P_INITIALIZED {
                    self.parsing = P_PARSING;
                }
                return STATUS_OK;
            }
        }
        #[cfg(feature = "expat-testing")]
        unsafe {
            g_bytesScanned = g_bytesScanned.wrapping_add(have_now as std::ffi::c_uint);
        }
        let data = self.eb.unfed();
        self.eb.fed = self.eb.end;
        let before = self.eb.ptr;
        let r = self.parse_chunk(data, is_final);
        // Read to: the stream's progress; all of it otherwise (it is held
        // in `input`).
        let to = match self.stream.as_ref() {
            Some(st) => (st.raw_progress().saturating_sub(self.raw_pre) + self.raw_skip).saturating_sub(self.eb.abs0),
            None => self.eb.end,
        };
        self.eb.ptr = to.clamp(self.eb.ptr, self.eb.end);
        if r != STATUS_ERROR {
            self.partial_before = if self.eb.ptr == before { have_now } else { 0 };
        }
        r
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_Parse(p: *mut Parser, s: *const c_char, len: c_int, is_final: c_int) -> c_int {
    let p = parser!(p);
    if p.walking {
        return STATUS_ERROR;
    }
    if len < 0 || (s.is_null() && len != 0) {
        p.error = E_INVALID_ARGUMENT;
        return STATUS_ERROR;
    }
    match p.parsing {
        P_SUSPENDED => {
            p.error = E_SUSPENDED;
            return STATUS_ERROR;
        }
        // After an error, expat keeps giving it.
        P_FINISHED => {
            if matches!(p.error, E_NONE | E_ABORTED) {
                p.error = E_FINISHED;
            }
            return STATUS_ERROR;
        }
        _ => {}
    }
    p.parsing = P_PARSING;
    // As libexpat: the bytes go into the buffer, which is then parsed.
    let b = unsafe { XML_GetBuffer(p, len) } as *mut u8;
    if b.is_null() {
        return STATUS_ERROR;
    }
    if len > 0 {
        unsafe { std::ptr::copy_nonoverlapping(s as *const u8, b, len as usize) };
    }
    unsafe { XML_ParseBuffer(p, len, is_final) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_GetBuffer(p: *mut Parser, len: c_int) -> *mut c_void {
    let p = parser!(p);
    if p.walking {
        return null_mut();
    }
    if len < 0 {
        p.error = E_NO_MEMORY;
        return null_mut();
    }
    match p.parsing {
        P_SUSPENDED => {
            p.error = E_SUSPENDED;
            return null_mut();
        }
        // After an error (not a stop), expat is still parsing.
        P_FINISHED if matches!(p.error, E_NONE | E_ABORTED) => {
            p.error = E_FINISHED;
            return null_mut();
        }
        _ => {}
    }
    p.last_req = len as usize;
    match p.eb.room(len as usize) {
        Ok(b) => b as *mut c_void,
        Err(code) => {
            p.error = code;
            null_mut()
        }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_ParseBuffer(p: *mut Parser, len: c_int, is_final: c_int) -> c_int {
    let p = parser!(p);
    if p.walking {
        return STATUS_ERROR;
    }
    if len < 0 {
        p.error = E_INVALID_ARGUMENT;
        return STATUS_ERROR;
    }
    match p.parsing {
        P_SUSPENDED => {
            p.error = E_SUSPENDED;
            return STATUS_ERROR;
        }
        P_FINISHED => {
            if matches!(p.error, E_NONE | E_ABORTED) {
                p.error = E_FINISHED;
            }
            return STATUS_ERROR;
        }
        P_INITIALIZED if p.eb.buf.is_null() => {
            p.error = E_NO_BUFFER;
            return STATUS_ERROR;
        }
        _ => {}
    }
    if len as usize > p.eb.size - p.eb.end {
        p.error = E_INVALID_ARGUMENT;
        return STATUS_ERROR;
    }
    p.eb.end += len as usize;
    p.attempt(is_final != 0)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_StopParser(p: *mut Parser, resumable: XBool) -> c_int {
    let p = parser!(p);
    match p.parsing {
        P_INITIALIZED => {
            p.error = E_NOT_STARTED;
            return STATUS_ERROR;
        }
        P_SUSPENDED => {
            if resumable != 0 {
                p.error = E_SUSPENDED;
                return STATUS_ERROR;
            }
            p.parsing = P_FINISHED;
        }
        P_FINISHED => {
            p.error = E_FINISHED;
            return STATUS_ERROR;
        }
        _ => {
            if resumable != 0 {
                p.parsing = P_SUSPENDED;
            } else {
                p.parsing = P_FINISHED;
                p.error = E_ABORTED;
                p.err_at = p.ev.0;
            }
        }
    }
    STATUS_OK
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_ResumeParser(p: *mut Parser) -> c_int {
    let p = parser!(p);
    if p.walking {
        return STATUS_ERROR;
    }
    if p.parsing != P_SUSPENDED {
        p.error = E_NOT_SUSPENDED;
        return STATUS_ERROR;
    }
    if p.doc.is_none() {
        // Suspended before the final buffer: nothing has been parsed.
        p.parsing = P_PARSING;
        return STATUS_OK;
    }
    p.walk()
}

#[repr(C)]
pub struct ParsingStatus {
    parsing: c_int,
    final_buffer: XBool,
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_GetParsingStatus(p: *mut Parser, status: *mut ParsingStatus) {
    let p = parser!(p);
    if let Some(s) = unsafe { status.as_mut() } {
        s.parsing = p.parsing;
        s.final_buffer = p.final_buffer as XBool;
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_GetErrorCode(p: *mut Parser) -> c_int {
    parser!(p).error
}

#[unsafe(no_mangle)]
pub extern "C" fn XML_ErrorString(code: c_int) -> *const c_char {
    if code <= 0 || code as usize >= ERROR_STRINGS.len() { null() } else { ERROR_STRINGS[code as usize].as_ptr() }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_GetCurrentLineNumber(p: *mut Parser) -> c_ulong {
    let p = parser!(p);
    if p.parsing == P_INITIALIZED && p.doc.is_none() && p.error == E_NONE {
        return 1;
    }
    let at = p.position();
    p.line_col(at).0 as c_ulong
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_GetCurrentLineNumber64(p: *mut Parser) -> u64 {
    unsafe { XML_GetCurrentLineNumber(p) as u64 }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_GetCurrentColumnNumber(p: *mut Parser) -> c_ulong {
    let p = parser!(p);
    if p.parsing == P_INITIALIZED && p.doc.is_none() && p.error == E_NONE {
        return 0;
    }
    let at = p.position();
    p.line_col(at).1 as c_ulong
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_GetCurrentColumnNumber64(p: *mut Parser) -> u64 {
    unsafe { XML_GetCurrentColumnNumber(p) as u64 }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_GetCurrentByteIndex(p: *mut Parser) -> c_long {
    let p = parser!(p);
    if p.doc.is_none() && p.error == E_NONE {
        return -1;
    }
    ((p.sbase + p.position()).saturating_sub(p.origin)) as c_long
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_GetCurrentByteIndex64(p: *mut Parser) -> i64 {
    unsafe { XML_GetCurrentByteIndex(p) as i64 }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_GetCurrentByteCount(p: *mut Parser) -> c_int {
    let p = parser!(p);
    if p.doc.is_none() || p.parsing == P_FINISHED { 0 } else { (p.ev.1 - p.ev.0) as c_int }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_GetCurrentByteCount64(p: *mut Parser) -> u64 {
    unsafe { XML_GetCurrentByteCount(p) as u64 }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_GetInputContext(p: *mut Parser, offset: *mut c_int, size: *mut c_int) -> *const c_char {
    let p = parser!(p);
    let Some(d) = p.doc.as_ref() else { return null() };
    let t = d.text();
    let at = p.position();
    let origin = p.origin.saturating_sub(p.sbase).min(t.len());
    unsafe {
        if let Some(o) = offset.as_mut() {
            *o = at.saturating_sub(origin) as c_int;
        }
        if let Some(s) = size.as_mut() {
            *s = (t.len() - origin) as c_int;
        }
        t.as_ptr().add(origin) as *const c_char
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_GetInputContext64(p: *mut Parser, offset: *mut i64, size: *mut u64) -> *const c_char {
    let (mut o, mut s) = (0, 0);
    let r = unsafe { XML_GetInputContext(p, &mut o, &mut s) };
    unsafe {
        if let Some(x) = offset.as_mut() {
            *x = o as i64;
        }
        if let Some(x) = size.as_mut() {
            *x = s as u64;
        }
    }
    r
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_GetSpecifiedAttributeCount(p: *mut Parser) -> c_int {
    parser!(p).nspecified
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_GetIdAttributeIndex(p: *mut Parser) -> c_int {
    match unsafe { p.as_ref() } {
        Some(p) => p.id_index,
        None => -1,
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_DefaultCurrent(p: *mut Parser) {
    let p = parser!(p);
    if p.doc.is_some() && p.ev.1 > p.ev.0 {
        let (a, b) = p.ev;
        p.report_default(a, b);
    }
}

macro_rules! setter {
    ($fname:ident, $field:ident, $ty:ty) => {
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $fname(p: *mut Parser, h: $ty) {
            parser!(p).h.$field = h;
        }
    };
}
setter!(XML_SetStartElementHandler, start, StartElementH);
setter!(XML_SetEndElementHandler, end, EndElementH);
setter!(XML_SetCharacterDataHandler, chars, CharDataH);
setter!(XML_SetProcessingInstructionHandler, pi, PiH);
setter!(XML_SetCommentHandler, comment, CommentH);
setter!(XML_SetStartCdataSectionHandler, start_cdata, VoidH);
setter!(XML_SetEndCdataSectionHandler, end_cdata, VoidH);
setter!(XML_SetStartDoctypeDeclHandler, start_doctype, StartDoctypeH);
setter!(XML_SetEndDoctypeDeclHandler, end_doctype, VoidH);
setter!(XML_SetEntityDeclHandler, entity_decl, EntityDeclH);
setter!(XML_SetUnparsedEntityDeclHandler, unparsed, UnparsedH);
setter!(XML_SetNotationDeclHandler, notation, NotationH);
setter!(XML_SetStartNamespaceDeclHandler, start_ns, StartNsH);
setter!(XML_SetEndNamespaceDeclHandler, end_ns, EndNsH);
setter!(XML_SetNotStandaloneHandler, not_standalone, NotStandaloneH);
setter!(XML_SetExternalEntityRefHandler, ext_ref, ExtRefH);
setter!(XML_SetSkippedEntityHandler, skipped, SkippedH);
setter!(XML_SetElementDeclHandler, element_decl, ElementDeclH);
setter!(XML_SetAttlistDeclHandler, attlist_decl, AttlistDeclH);
setter!(XML_SetXmlDeclHandler, xml_decl, XmlDeclH);

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_SetElementHandler(p: *mut Parser, s: StartElementH, e: EndElementH) {
    let p = parser!(p);
    p.h.start = s;
    p.h.end = e;
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_SetCdataSectionHandler(p: *mut Parser, s: VoidH, e: VoidH) {
    let p = parser!(p);
    p.h.start_cdata = s;
    p.h.end_cdata = e;
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_SetDoctypeDeclHandler(p: *mut Parser, s: StartDoctypeH, e: VoidH) {
    let p = parser!(p);
    p.h.start_doctype = s;
    p.h.end_doctype = e;
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_SetNamespaceDeclHandler(p: *mut Parser, s: StartNsH, e: EndNsH) {
    let p = parser!(p);
    p.h.start_ns = s;
    p.h.end_ns = e;
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_SetDefaultHandler(p: *mut Parser, h: DefaultH) {
    let p = parser!(p);
    p.h.default = h;
    p.h.default_expand = false;
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_SetDefaultHandlerExpand(p: *mut Parser, h: DefaultH) {
    let p = parser!(p);
    p.h.default = h;
    p.h.default_expand = true;
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_SetExternalEntityRefHandlerArg(p: *mut Parser, arg: *mut c_void) {
    let p = parser!(p);
    p.h.ext_ref_arg = if arg.is_null() { None } else { Some(arg as *mut Parser) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_SetUnknownEncodingHandler(p: *mut Parser, h: UnknownEncH, data: *mut c_void) {
    let p = parser!(p);
    p.h.unknown_enc = h;
    p.h.unknown_enc_data = Some(data);
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_SetUserData(p: *mut Parser, data: *mut c_void) {
    let p = parser!(p);
    if p.handler_arg == p.user_data {
        p.handler_arg = data;
    }
    p.user_data = data;
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_UseParserAsHandlerArg(p: *mut Parser) {
    let p = parser!(p);
    p.arg_is_parser = true;
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_SetBase(p: *mut Parser, base: *const XChar) -> c_int {
    let p = parser!(p);
    p.base = unsafe { opt_cstr(base) };
    p.base_c = p.base.clone().map(|mut b| {
        b.push(0);
        b
    });
    STATUS_OK
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_GetBase(p: *mut Parser) -> *const XChar {
    let p = parser!(p);
    p.base_c.as_ref().map_or(null(), |b| b.as_ptr() as *const XChar)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_SetEncoding(p: *mut Parser, enc: *const XChar) -> c_int {
    let p = parser!(p);
    if p.parsing == P_PARSING || p.parsing == P_SUSPENDED {
        return STATUS_ERROR;
    }
    p.encoding = unsafe { opt_cstr(enc) };
    STATUS_OK
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_UseForeignDTD(p: *mut Parser, use_dtd: XBool) -> c_int {
    let p = parser!(p);
    if p.parsing != P_INITIALIZED {
        return E_CANT_CHANGE_FEATURE_ONCE_PARSING;
    }
    p.foreign_dtd = use_dtd != 0;
    E_NONE
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_SetReturnNSTriplet(p: *mut Parser, v: c_int) {
    let p = parser!(p);
    if p.parsing == P_INITIALIZED {
        p.triplets = v != 0;
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_SetParamEntityParsing(p: *mut Parser, v: c_int) -> c_int {
    let p = parser!(p);
    if p.parsing != P_INITIALIZED || !(0..=2).contains(&v) {
        return 0;
    }
    p.param_parsing = v;
    1
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_SetHashSalt(p: *mut Parser, _salt: c_ulong) -> c_int {
    // The hash tables are seeded at random per document (see the README).
    let p = parser!(p);
    (p.parsing == P_INITIALIZED) as c_int
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_SetHashSalt16Bytes(p: *mut Parser, entropy: *const u8) -> XBool {
    let p = parser!(p);
    (p.parsing == P_INITIALIZED && !entropy.is_null()) as XBool
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_SetReparseDeferralEnabled(p: *mut Parser, enabled: XBool) -> XBool {
    let p = parser!(p);
    if enabled > 1 {
        return 0;
    }
    p.props.reparse = enabled;
    1
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_SetBillionLaughsAttackProtectionMaximumAmplification(p: *mut Parser, f: f32) -> XBool {
    // Content expands lazily and parsing is linear (see the README), so
    // there is no amplification to limit; arguments are checked as
    // expat checks them.
    let p = parser!(p);
    (p.ext.is_none() && !f.is_nan() && f >= 1.0) as XBool
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_SetBillionLaughsAttackProtectionActivationThreshold(p: *mut Parser, _t: u64) -> XBool {
    let p = parser!(p);
    p.ext.is_none() as XBool
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_SetAllocTrackerMaximumAmplification(p: *mut Parser, f: f32) -> XBool {
    let p = parser!(p);
    (p.ext.is_none() && !f.is_nan() && f >= 1.0) as XBool
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_SetAllocTrackerActivationThreshold(p: *mut Parser, _t: u64) -> XBool {
    let p = parser!(p);
    p.ext.is_none() as XBool
}

// enum XML_Prop_Error
const PROP_NONE: c_int = 0;
const PROP_INVALID_KEY: c_int = 1;
const PROP_INVALID_TYPE: c_int = 2;
const PROP_INVALID_VALUE: c_int = 3;
const PROP_PARSER_NULL: c_int = 4;
const PROP_PARSER_NOT_ROOT: c_int = 5;

fn prop_type(prop: c_int) -> Option<u8> {
    match prop {
        1 | 3 => Some(b'u'),
        2 | 4 => Some(b'd'),
        5 => Some(b'b'),
        _ => None,
    }
}

impl Parser {
    fn prop_check(p: *mut Parser, prop: c_int, ty: u8, root: bool) -> c_int {
        Parser::prop_check_out(p, prop, ty, root, true)
    }

    fn prop_check_out(p: *mut Parser, prop: c_int, ty: u8, root: bool, out_ok: bool) -> c_int {
        let Some(pp) = (unsafe { p.as_ref() }) else { return PROP_PARSER_NULL };
        if prop_type(prop).is_some() && !out_ok {
            return PROP_INVALID_VALUE;
        }
        match prop_type(prop) {
            None => PROP_INVALID_KEY,
            Some(t) if t != ty => PROP_INVALID_TYPE,
            _ if root && pp.ext.is_some() && prop != 5 => PROP_PARSER_NOT_ROOT,
            _ => PROP_NONE,
        }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_GetPropertyBool(p: *mut Parser, prop: c_int, out: *mut XBool) -> c_int {
    let r = Parser::prop_check_out(p, prop, b'b', false, !out.is_null());
    if r != PROP_NONE {
        return r;
    }
    let Some(o) = (unsafe { out.as_mut() }) else { return PROP_INVALID_VALUE };
    *o = unsafe { (*p).props.reparse };
    PROP_NONE
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_GetPropertyDouble(p: *mut Parser, prop: c_int, out: *mut f64) -> c_int {
    let r = Parser::prop_check_out(p, prop, b'd', false, !out.is_null());
    if r != PROP_NONE {
        return r;
    }
    let Some(o) = (unsafe { out.as_mut() }) else { return PROP_INVALID_VALUE };
    *o = unsafe { if prop == 2 { (*p).props.at_amp } else { (*p).props.bl_amp } };
    PROP_NONE
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_GetPropertyUInt64(p: *mut Parser, prop: c_int, out: *mut u64) -> c_int {
    let r = Parser::prop_check_out(p, prop, b'u', false, !out.is_null());
    if r != PROP_NONE {
        return r;
    }
    let Some(o) = (unsafe { out.as_mut() }) else { return PROP_INVALID_VALUE };
    *o = unsafe { if prop == 1 { (*p).props.at_thr } else { (*p).props.bl_thr } };
    PROP_NONE
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_SetPropertyBool(p: *mut Parser, prop: c_int, v: XBool) -> c_int {
    let r = Parser::prop_check(p, prop, b'b', true);
    if r != PROP_NONE {
        return r;
    }
    if v > 1 {
        return PROP_INVALID_VALUE;
    }
    unsafe { (*p).props.reparse = v };
    PROP_NONE
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_SetPropertyDouble(p: *mut Parser, prop: c_int, v: f64) -> c_int {
    let r = Parser::prop_check(p, prop, b'd', true);
    if r != PROP_NONE {
        return r;
    }
    if v.is_nan() || v < 1.0 {
        return PROP_INVALID_VALUE;
    }
    unsafe {
        if prop == 2 {
            (*p).props.at_amp = v
        } else {
            (*p).props.bl_amp = v
        }
    };
    PROP_NONE
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_SetPropertyUInt64(p: *mut Parser, prop: c_int, v: u64) -> c_int {
    let r = Parser::prop_check(p, prop, b'u', true);
    if r != PROP_NONE {
        return r;
    }
    unsafe {
        if prop == 1 {
            (*p).props.at_thr = v
        } else {
            (*p).props.bl_thr = v
        }
    };
    PROP_NONE
}

/// The values of expat's properties, kept and returned as set: verilith-xml
/// needs none of the limits they configure.
#[derive(Clone, Copy)]
struct Props {
    reparse: XBool,
    at_amp: f64,
    at_thr: u64,
    bl_amp: f64,
    bl_thr: u64,
}

impl Default for Props {
    fn default() -> Props {
        Props { reparse: reparse_default(), at_amp: 100.0, at_thr: 64 * 1024 * 1024, bl_amp: 100.0, bl_thr: 8 * 1024 * 1024 }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_FreeContentModel(p: *mut Parser, model: *mut XmlContent) {
    let p = parser!(p);
    if !model.is_null() {
        unsafe { (p.mem.free_fcn.unwrap())(model as *mut c_void) };
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_MemMalloc(p: *mut Parser, size: usize) -> *mut c_void {
    let p = parser!(p);
    unsafe { (p.mem.malloc_fcn.unwrap())(size) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_MemRealloc(p: *mut Parser, ptr: *mut c_void, size: usize) -> *mut c_void {
    let p = parser!(p);
    unsafe { (p.mem.realloc_fcn.unwrap())(ptr, size) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn XML_MemFree(p: *mut Parser, ptr: *mut c_void) {
    let p = parser!(p);
    unsafe { (p.mem.free_fcn.unwrap())(ptr) }
}

#[unsafe(no_mangle)]
pub extern "C" fn XML_ExpatVersion() -> *const c_char {
    c"expat_2.10.0".as_ptr()
}

#[repr(C)]
pub struct ExpatVersion {
    major: c_int,
    minor: c_int,
    micro: c_int,
}

#[unsafe(no_mangle)]
pub extern "C" fn XML_ExpatVersionInfo() -> ExpatVersion {
    ExpatVersion { major: 2, minor: 10, micro: 0 }
}

#[repr(C)]
pub struct Feature {
    feature: c_int,
    name: *const c_char,
    value: c_long,
}

struct Features([Feature; 9]);
unsafe impl Sync for Features {}

static FEATURES: Features = Features([
    Feature { feature: 6, name: c"sizeof(XML_Char)".as_ptr(), value: 1 },
    Feature { feature: 7, name: c"sizeof(XML_LChar)".as_ptr(), value: 1 },
    Feature { feature: 3, name: c"XML_DTD".as_ptr(), value: 0 },
    Feature { feature: 4, name: c"XML_CONTEXT_BYTES".as_ptr(), value: 1024 },
    Feature { feature: 8, name: c"XML_NS".as_ptr(), value: 0 },
    Feature { feature: 11, name: c"XML_BLAP_MAX_AMP".as_ptr(), value: 100 },
    Feature { feature: 12, name: c"XML_BLAP_ACT_THRES".as_ptr(), value: 8388608 },
    Feature { feature: 13, name: c"XML_GE".as_ptr(), value: 0 },
    Feature { feature: 0, name: null(), value: 0 },
]);

#[unsafe(no_mangle)]
pub extern "C" fn XML_GetFeatureList() -> *const Feature {
    FEATURES.0.as_ptr()
}
