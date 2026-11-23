//! libxml2's C ABI (libxml2 2.15.4) over verilith-xml: feature `libxml2-abi`.
//!
//! A caller built against libxml2's headers links this library in place of
//! libxml2 and runs unchanged, for the parts of libxml2 this covers: the XML
//! parser (`xmlReadMemory`, `xmlCtxtReadFile`, the push parser, SAX2 with
//! libxml2's own default handlers), the tree (`xmlDoc`, `xmlNode`, ... with
//! libxml2's struct layouts, so that callers walk them directly), the
//! serializer (`xmlDocDumpMemory`, `xmlSaveFile`, `xmlSaveTree`, ...) and the
//! helpers that go with them (memory, strings, hash tables, errors). HTML,
//! XPath, schemas, the reader and the rest of libxml2 are not provided.
//!
//! The verified parser decides whether the document is well-formed; this
//! code walks its tape and makes libxml2's SAX2 calls in document order.
//! It is ordinary Rust, not verified; how it departs from libxml2 is in the
//! crate's README ("The libxml2 C ABI").
#![allow(non_snake_case, non_upper_case_globals, clippy::missing_safety_doc)]

pub mod codes;
mod io;
mod scan;
mod parser;
mod sax2;
mod save;
mod tree;

use codes::*;
use std::cell::UnsafeCell;
use std::collections::HashMap;
use std::hash::{BuildHasher, Hasher};

/// A seeded multiply-fold hasher for the dictionaries and hash tables: SipHash
/// (std's default) was a tenth of a parse. The seed is random per table, as
/// libxml2 seeds its own, so the inputs that collide cannot be chosen ahead.
pub struct FastHasher(u64);

const K: u64 = 0x9E37_79B9_7F4A_7C15;

impl Hasher for FastHasher {
    #[inline]
    fn write(&mut self, b: &[u8]) {
        let mut h = self.0;
        let mut c = b.chunks_exact(8);
        for w in &mut c {
            h = (h ^ u64::from_le_bytes(w.try_into().unwrap())).wrapping_mul(K).rotate_left(29);
        }
        let r = c.remainder();
        if !r.is_empty() {
            let mut t = [0u8; 8];
            t[..r.len()].copy_from_slice(r);
            h = (h ^ u64::from_le_bytes(t) ^ ((r.len() as u64) << 59)).wrapping_mul(K).rotate_left(29);
        }
        self.0 = h;
    }
    #[inline]
    fn write_usize(&mut self, n: usize) {
        self.0 = (self.0 ^ n as u64).wrapping_mul(K).rotate_left(29);
    }
    #[inline]
    fn finish(&self) -> u64 {
        let m = (self.0 as u128).wrapping_mul(K as u128 | 1);
        (m as u64) ^ ((m >> 64) as u64)
    }
}

#[derive(Clone)]
pub struct FastState(u64);

impl FastState {
    pub fn new() -> FastState {
        FastState(std::collections::hash_map::RandomState::new().hash_one(0x6c69_6278_6d6c_32u64))
    }
}

impl Default for FastState {
    fn default() -> FastState {
        FastState::new()
    }
}

impl BuildHasher for FastState {
    type Hasher = FastHasher;
    #[inline]
    fn build_hasher(&self) -> FastHasher {
        FastHasher(self.0)
    }
}

pub type FastMap<K, V> = HashMap<K, V, FastState>;

pub fn fast_map<K, V>() -> FastMap<K, V> {
    HashMap::with_hasher(FastState::new())
}
use std::ffi::{c_char, c_int, c_long, c_uint, c_ulong, c_ushort, c_void, CStr};
use std::ptr::{null, null_mut};
use std::sync::atomic::{AtomicUsize, Ordering};

pub use parser::ParserCtxt;

pub type XChar = u8;

// --- node types (xmlElementType) --------------------------------------------

pub const ELEMENT_NODE: c_int = 1;
pub const ATTRIBUTE_NODE: c_int = 2;
pub const TEXT_NODE: c_int = 3;
pub const CDATA_SECTION_NODE: c_int = 4;
pub const ENTITY_REF_NODE: c_int = 5;
pub const PI_NODE: c_int = 7;
pub const COMMENT_NODE: c_int = 8;
pub const DOCUMENT_NODE: c_int = 9;
pub const DOCUMENT_FRAG_NODE: c_int = 11;
pub const HTML_DOCUMENT_NODE: c_int = 13;
pub const DTD_NODE: c_int = 14;
pub const ELEMENT_DECL: c_int = 15;
pub const ATTRIBUTE_DECL: c_int = 16;
pub const ENTITY_DECL: c_int = 17;
pub const NAMESPACE_DECL: c_int = 18;
pub const XINCLUDE_START: c_int = 19;
pub const XINCLUDE_END: c_int = 20;

// xmlEntityType
pub const INTERNAL_GENERAL_ENTITY: c_int = 1;
pub const EXTERNAL_GENERAL_PARSED_ENTITY: c_int = 2;
pub const EXTERNAL_GENERAL_UNPARSED_ENTITY: c_int = 3;
pub const INTERNAL_PARAMETER_ENTITY: c_int = 4;
pub const EXTERNAL_PARAMETER_ENTITY: c_int = 5;
pub const INTERNAL_PREDEFINED_ENTITY: c_int = 6;

// entity flags (private/entities.h)
pub const ENT_PARSED: c_int = 1;
pub const ENT_CHECKED: c_int = 2;
pub const ENT_EXPANDING: c_int = 8;

// xmlAttributeType, xmlAttributeDefault
pub const ATTRIBUTE_CDATA: c_int = 1;
pub const ATTRIBUTE_ID: c_int = 2;
pub const ATTRIBUTE_ENUMERATION: c_int = 9;
pub const ATTRIBUTE_NOTATION: c_int = 10;
pub const ATTRIBUTE_NONE: c_int = 1;
pub const ATTRIBUTE_REQUIRED: c_int = 2;
pub const ATTRIBUTE_IMPLIED: c_int = 3;
pub const ATTRIBUTE_FIXED: c_int = 4;

// xmlElementTypeVal, xmlElementContentType, xmlElementContentOccur
pub const ELEMENT_TYPE_EMPTY: c_int = 1;
pub const ELEMENT_TYPE_ANY: c_int = 2;
pub const ELEMENT_TYPE_MIXED: c_int = 3;
pub const ELEMENT_TYPE_ELEMENT: c_int = 4;
pub const CONTENT_PCDATA: c_int = 1;
pub const CONTENT_ELEMENT: c_int = 2;
pub const CONTENT_SEQ: c_int = 3;
pub const CONTENT_OR: c_int = 4;
pub const CONTENT_ONCE: c_int = 1;
pub const CONTENT_OPT: c_int = 2;
pub const CONTENT_MULT: c_int = 3;
pub const CONTENT_PLUS: c_int = 4;

// xmlParserOption
pub const PARSE_RECOVER: c_int = 1 << 0;
pub const PARSE_NOENT: c_int = 1 << 1;
pub const PARSE_DTDLOAD: c_int = 1 << 2;
pub const PARSE_DTDATTR: c_int = 1 << 3;
pub const PARSE_DTDVALID: c_int = 1 << 4;
pub const PARSE_NOERROR: c_int = 1 << 5;
pub const PARSE_NOWARNING: c_int = 1 << 6;
pub const PARSE_PEDANTIC: c_int = 1 << 7;
pub const PARSE_NOBLANKS: c_int = 1 << 8;
pub const PARSE_SAX1: c_int = 1 << 9;
pub const PARSE_NODICT: c_int = 1 << 12;
pub const PARSE_NSCLEAN: c_int = 1 << 13;
pub const PARSE_NOCDATA: c_int = 1 << 14;
pub const PARSE_OLD10: c_int = 1 << 17;
pub const PARSE_HUGE: c_int = 1 << 19;
pub const PARSE_OLDSAX: c_int = 1 << 20;
pub const PARSE_IGNORE_ENC: c_int = 1 << 21;
pub const PARSE_BIG_LINES: c_int = 1 << 22;
pub const PARSE_NO_XXE: c_int = 1 << 23;
pub const PARSE_SKIP_IDS: c_int = 1 << 27;

pub const DETECT_IDS: c_int = 2;
pub const COMPLETE_ATTRS: c_int = 4;
pub const SKIP_IDS: c_int = 8;

pub const SAX2_MAGIC: c_uint = 0xDEEDBEAF;

// xmlDocProperties
pub const DOC_WELLFORMED: c_int = 1;
pub const DOC_NSVALID: c_int = 2;
pub const DOC_OLD10: c_int = 4;
pub const DOC_DTDVALID: c_int = 8;

pub const XML_XML_NAMESPACE: &[u8] = b"http://www.w3.org/XML/1998/namespace";

// --- the tree's structs (tree.h, entities.h, valid.h) -----------------------

#[repr(C)]
pub struct Ns {
    pub next: *mut Ns,
    pub type_: c_int,
    pub href: *const XChar,
    pub prefix: *const XChar,
    pub _private: *mut c_void,
    pub context: *mut Doc,
}

#[repr(C)]
pub struct Node {
    pub _private: *mut c_void,
    pub type_: c_int,
    pub name: *const XChar,
    pub children: *mut Node,
    pub last: *mut Node,
    pub parent: *mut Node,
    pub next: *mut Node,
    pub prev: *mut Node,
    pub doc: *mut Doc,
    pub ns: *mut Ns,
    pub content: *mut XChar,
    pub properties: *mut Attr,
    pub nsDef: *mut Ns,
    pub psvi: *mut c_void,
    pub line: c_ushort,
    pub extra: c_ushort,
}

#[repr(C)]
pub struct Attr {
    pub _private: *mut c_void,
    pub type_: c_int,
    pub name: *const XChar,
    pub children: *mut Node,
    pub last: *mut Node,
    pub parent: *mut Node,
    pub next: *mut Attr,
    pub prev: *mut Attr,
    pub doc: *mut Doc,
    pub ns: *mut Ns,
    pub atype: c_int,
    pub psvi: *mut c_void,
    pub id: *mut Id,
}

#[repr(C)]
pub struct Doc {
    pub _private: *mut c_void,
    pub type_: c_int,
    pub name: *mut c_char,
    pub children: *mut Node,
    pub last: *mut Node,
    pub parent: *mut Node,
    pub next: *mut Node,
    pub prev: *mut Node,
    pub doc: *mut Doc,
    pub compression: c_int,
    pub standalone: c_int,
    pub intSubset: *mut Dtd,
    pub extSubset: *mut Dtd,
    pub oldNs: *mut Ns,
    pub version: *mut XChar,
    pub encoding: *mut XChar,
    pub ids: *mut c_void,
    pub refs: *mut c_void,
    pub URL: *mut XChar,
    pub charset: c_int,
    pub dict: *mut c_void,
    pub psvi: *mut c_void,
    pub parseFlags: c_int,
    pub properties: c_int,
}

#[repr(C)]
pub struct Dtd {
    pub _private: *mut c_void,
    pub type_: c_int,
    pub name: *const XChar,
    pub children: *mut Node,
    pub last: *mut Node,
    pub parent: *mut Doc,
    pub next: *mut Node,
    pub prev: *mut Node,
    pub doc: *mut Doc,
    pub notations: *mut c_void,
    pub elements: *mut c_void,
    pub attributes: *mut c_void,
    pub entities: *mut c_void,
    pub ExternalID: *mut XChar,
    pub SystemID: *mut XChar,
    pub pentities: *mut c_void,
}

#[repr(C)]
pub struct Entity {
    pub _private: *mut c_void,
    pub type_: c_int,
    pub name: *const XChar,
    pub children: *mut Node,
    pub last: *mut Node,
    pub parent: *mut Dtd,
    pub next: *mut Node,
    pub prev: *mut Node,
    pub doc: *mut Doc,
    pub orig: *mut XChar,
    pub content: *mut XChar,
    pub length: c_int,
    pub etype: c_int,
    pub ExternalID: *const XChar,
    pub SystemID: *const XChar,
    pub nexte: *mut Entity,
    pub URI: *const XChar,
    pub owner: c_int,
    pub flags: c_int,
    pub expandedSize: c_ulong,
}

#[repr(C)]
pub struct ElementDecl {
    pub _private: *mut c_void,
    pub type_: c_int,
    pub name: *const XChar,
    pub children: *mut Node,
    pub last: *mut Node,
    pub parent: *mut Dtd,
    pub next: *mut Node,
    pub prev: *mut Node,
    pub doc: *mut Doc,
    pub etype: c_int,
    pub content: *mut ElementContent,
    pub attributes: *mut AttributeDecl,
    pub prefix: *const XChar,
    pub contModel: *mut c_void,
}

#[repr(C)]
pub struct AttributeDecl {
    pub _private: *mut c_void,
    pub type_: c_int,
    pub name: *const XChar,
    pub children: *mut Node,
    pub last: *mut Node,
    pub parent: *mut Dtd,
    pub next: *mut Node,
    pub prev: *mut Node,
    pub doc: *mut Doc,
    pub nexth: *mut AttributeDecl,
    pub atype: c_int,
    pub def: c_int,
    pub defaultValue: *mut XChar,
    pub tree: *mut Enumeration,
    pub prefix: *const XChar,
    pub elem: *const XChar,
}

#[repr(C)]
pub struct ElementContent {
    pub type_: c_int,
    pub ocur: c_int,
    pub name: *const XChar,
    pub c1: *mut ElementContent,
    pub c2: *mut ElementContent,
    pub parent: *mut ElementContent,
    pub prefix: *const XChar,
}

#[repr(C)]
pub struct Enumeration {
    pub next: *mut Enumeration,
    pub name: *const XChar,
}

#[repr(C)]
pub struct Notation {
    pub name: *const XChar,
    pub PublicID: *const XChar,
    pub SystemID: *const XChar,
}

#[repr(C)]
pub struct Id {
    pub next: *mut Id,
    pub value: *mut XChar,
    pub attr: *mut Attr,
    pub name: *const XChar,
    pub lineno: c_int,
    pub doc: *mut Doc,
}

#[repr(C)]
pub struct Buffer {
    pub content: *mut XChar,
    pub use_: c_uint,
    pub size: c_uint,
    pub alloc: c_int,
    pub contentIO: *mut XChar,
}

/// `xmlError`.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct XmlError {
    pub domain: c_int,
    pub code: c_int,
    pub message: *mut c_char,
    pub level: c_int,
    pub file: *mut c_char,
    pub line: c_int,
    pub str1: *mut c_char,
    pub str2: *mut c_char,
    pub str3: *mut c_char,
    pub int1: c_int,
    pub int2: c_int,
    pub ctxt: *mut c_void,
    pub node: *mut c_void,
}

impl XmlError {
    pub const fn zero() -> XmlError {
        XmlError {
            domain: 0,
            code: 0,
            message: null_mut(),
            level: 0,
            file: null_mut(),
            line: 0,
            str1: null_mut(),
            str2: null_mut(),
            str3: null_mut(),
            int1: 0,
            int2: 0,
            ctxt: null_mut(),
            node: null_mut(),
        }
    }
}

// --- SAX (parser.h) -----------------------------------------------------------

pub type Ctx = *mut c_void;
pub type InternalSubsetF = Option<unsafe extern "C" fn(Ctx, *const XChar, *const XChar, *const XChar)>;
pub type IntF = Option<unsafe extern "C" fn(Ctx) -> c_int>;
pub type ResolveEntityF = Option<unsafe extern "C" fn(Ctx, *const XChar, *const XChar) -> *mut c_void>;
pub type GetEntityF = Option<unsafe extern "C" fn(Ctx, *const XChar) -> *mut Entity>;
pub type EntityDeclF = Option<unsafe extern "C" fn(Ctx, *const XChar, c_int, *const XChar, *const XChar, *mut XChar)>;
pub type NotationDeclF = Option<unsafe extern "C" fn(Ctx, *const XChar, *const XChar, *const XChar)>;
pub type AttributeDeclF =
    Option<unsafe extern "C" fn(Ctx, *const XChar, *const XChar, c_int, c_int, *const XChar, *mut Enumeration)>;
pub type ElementDeclF = Option<unsafe extern "C" fn(Ctx, *const XChar, c_int, *mut ElementContent)>;
pub type UnparsedEntityDeclF = Option<unsafe extern "C" fn(Ctx, *const XChar, *const XChar, *const XChar, *const XChar)>;
pub type LocatorF = Option<unsafe extern "C" fn(Ctx, *mut SaxLocator)>;
pub type VoidF = Option<unsafe extern "C" fn(Ctx)>;
pub type StartElementF = Option<unsafe extern "C" fn(Ctx, *const XChar, *mut *const XChar)>;
pub type NameF = Option<unsafe extern "C" fn(Ctx, *const XChar)>;
pub type CharsF = Option<unsafe extern "C" fn(Ctx, *const XChar, c_int)>;
pub type PiF = Option<unsafe extern "C" fn(Ctx, *const XChar, *const XChar)>;
pub type MsgF = Option<unsafe extern "C" fn(Ctx, *const c_char, ...)>;
pub type StartElementNsF = Option<
    unsafe extern "C" fn(Ctx, *const XChar, *const XChar, *const XChar, c_int, *mut *const XChar, c_int, c_int, *mut *const XChar),
>;
pub type EndElementNsF = Option<unsafe extern "C" fn(Ctx, *const XChar, *const XChar, *const XChar)>;
pub type StructuredErrorF = Option<unsafe extern "C" fn(*mut c_void, *const XmlError)>;
pub type GenericErrorF = Option<unsafe extern "C" fn(*mut c_void, *const c_char, ...)>;

#[repr(C)]
#[derive(Clone, Copy)]
pub struct SaxHandler {
    pub internalSubset: InternalSubsetF,
    pub isStandalone: IntF,
    pub hasInternalSubset: IntF,
    pub hasExternalSubset: IntF,
    pub resolveEntity: ResolveEntityF,
    pub getEntity: GetEntityF,
    pub entityDecl: EntityDeclF,
    pub notationDecl: NotationDeclF,
    pub attributeDecl: AttributeDeclF,
    pub elementDecl: ElementDeclF,
    pub unparsedEntityDecl: UnparsedEntityDeclF,
    pub setDocumentLocator: LocatorF,
    pub startDocument: VoidF,
    pub endDocument: VoidF,
    pub startElement: StartElementF,
    pub endElement: NameF,
    pub reference: NameF,
    pub characters: CharsF,
    pub ignorableWhitespace: CharsF,
    pub processingInstruction: PiF,
    pub comment: NameF,
    pub warning: MsgF,
    pub error: MsgF,
    pub fatalError: MsgF,
    pub getParameterEntity: GetEntityF,
    pub cdataBlock: CharsF,
    pub externalSubset: InternalSubsetF,
    pub initialized: c_uint,
    pub _private: *mut c_void,
    pub startElementNs: StartElementNsF,
    pub endElementNs: EndElementNsF,
    pub serror: StructuredErrorF,
}

impl SaxHandler {
    pub const fn zero() -> SaxHandler {
        SaxHandler {
            internalSubset: None,
            isStandalone: None,
            hasInternalSubset: None,
            hasExternalSubset: None,
            resolveEntity: None,
            getEntity: None,
            entityDecl: None,
            notationDecl: None,
            attributeDecl: None,
            elementDecl: None,
            unparsedEntityDecl: None,
            setDocumentLocator: None,
            startDocument: None,
            endDocument: None,
            startElement: None,
            endElement: None,
            reference: None,
            characters: None,
            ignorableWhitespace: None,
            processingInstruction: None,
            comment: None,
            warning: None,
            error: None,
            fatalError: None,
            getParameterEntity: None,
            cdataBlock: None,
            externalSubset: None,
            initialized: 0,
            _private: null_mut(),
            startElementNs: None,
            endElementNs: None,
            serror: None,
        }
    }
}

#[repr(C)]
pub struct SaxLocator {
    pub getPublicId: Option<unsafe extern "C" fn(Ctx) -> *const XChar>,
    pub getSystemId: Option<unsafe extern "C" fn(Ctx) -> *const XChar>,
    pub getLineNumber: Option<unsafe extern "C" fn(Ctx) -> c_int>,
    pub getColumnNumber: Option<unsafe extern "C" fn(Ctx) -> c_int>,
}

#[unsafe(no_mangle)]
pub static xmlDefaultSAXLocator: SaxLocator = SaxLocator {
    getPublicId: Some(sax2::xmlSAX2GetPublicId),
    getSystemId: Some(sax2::xmlSAX2GetSystemId),
    getLineNumber: Some(sax2::xmlSAX2GetLineNumber),
    getColumnNumber: Some(sax2::xmlSAX2GetColumnNumber),
};

#[unsafe(no_mangle)]
pub static xmlParserVersion: Version = Version(c"21504".as_ptr());

#[repr(transparent)]
pub struct Version(*const c_char);
unsafe impl Sync for Version {}
unsafe impl Sync for SaxLocator {}

// --- memory -------------------------------------------------------------------

pub type MallocFn = Option<unsafe extern "C" fn(usize) -> *mut c_void>;
pub type ReallocFn = Option<unsafe extern "C" fn(*mut c_void, usize) -> *mut c_void>;
pub type FreeFn = Option<unsafe extern "C" fn(*mut c_void)>;
pub type StrdupFn = Option<unsafe extern "C" fn(*const c_char) -> *mut c_char>;

unsafe extern "C" {
    fn malloc(n: usize) -> *mut c_void;
    fn realloc(p: *mut c_void, n: usize) -> *mut c_void;
    fn free(p: *mut c_void);
    fn strdup(s: *const c_char) -> *mut c_char;
}

#[unsafe(no_mangle)]
pub static mut xmlMalloc: MallocFn = Some(malloc);
#[unsafe(no_mangle)]
pub static mut xmlMallocAtomic: MallocFn = Some(malloc);
#[unsafe(no_mangle)]
pub static mut xmlRealloc: ReallocFn = Some(realloc);
#[unsafe(no_mangle)]
pub static mut xmlFree: FreeFn = Some(free);
#[unsafe(no_mangle)]
pub static mut xmlMemStrdup: StrdupFn = Some(strdup);

/// Allocates through `xmlMalloc`, as libxml2 does for everything a caller
/// may free with `xmlFree`.
pub fn xmalloc(n: usize) -> *mut c_void {
    unsafe {
        match xmlMalloc {
            Some(f) => f(n.max(1)),
            None => malloc(n.max(1)),
        }
    }
}

pub fn xrealloc(p: *mut c_void, n: usize) -> *mut c_void {
    unsafe {
        match xmlRealloc {
            Some(f) => f(p, n.max(1)),
            None => realloc(p, n.max(1)),
        }
    }
}

pub fn xfree(p: *mut c_void) {
    if p.is_null() {
        return;
    }
    unsafe {
        match xmlFree {
            Some(f) => f(p),
            None => free(p),
        }
    }
}

/// A zeroed `T` from `xmlMalloc`.
pub fn xnew<T>() -> *mut T {
    let p = xmalloc(std::mem::size_of::<T>()) as *mut T;
    if !p.is_null() {
        unsafe { std::ptr::write_bytes(p as *mut u8, 0, std::mem::size_of::<T>()) };
    }
    p
}

/// A NUL-terminated copy of `s` from `xmlMalloc`.
pub fn xstrdup(s: &[u8]) -> *mut XChar {
    let p = xmalloc(s.len() + 1) as *mut u8;
    if !p.is_null() {
        unsafe {
            std::ptr::copy_nonoverlapping(s.as_ptr(), p, s.len());
            *p.add(s.len()) = 0;
        }
    }
    p
}

pub fn xstrdup_opt(s: Option<&[u8]>) -> *mut XChar {
    s.map_or(null_mut(), xstrdup)
}

/// The bytes of a C string, without its NUL (empty for NULL).
pub unsafe fn cbytes<'a>(p: *const XChar) -> &'a [u8] {
    if p.is_null() { &[] } else { unsafe { CStr::from_ptr(p as *const c_char) }.to_bytes() }
}

pub unsafe fn copt<'a>(p: *const XChar) -> Option<&'a [u8]> {
    if p.is_null() { None } else { Some(unsafe { cbytes(p) }) }
}

// The debugging allocator (xmlMemMalloc, ...): each block carries its size
// before it, so that xmlMemUsed can say how much is allocated.
static MEM_USED: AtomicUsize = AtomicUsize::new(0);
static MEM_BLOCKS: AtomicUsize = AtomicUsize::new(0);
const MEM_HDR: usize = 16;

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlMemMalloc(n: usize) -> *mut c_void {
    let p = unsafe { malloc(n + MEM_HDR) } as *mut u8;
    if p.is_null() {
        return null_mut();
    }
    unsafe { (p as *mut usize).write(n) };
    MEM_USED.fetch_add(n, Ordering::Relaxed);
    MEM_BLOCKS.fetch_add(1, Ordering::Relaxed);
    unsafe { p.add(MEM_HDR) as *mut c_void }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlMallocLoc(n: usize, _file: *const c_char, _line: c_int) -> *mut c_void {
    unsafe { xmlMemMalloc(n) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlMallocAtomicLoc(n: usize, _file: *const c_char, _line: c_int) -> *mut c_void {
    unsafe { xmlMemMalloc(n) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlMemFree(p: *mut c_void) {
    if p.is_null() {
        return;
    }
    let base = unsafe { (p as *mut u8).sub(MEM_HDR) };
    let n = unsafe { (base as *mut usize).read() };
    MEM_USED.fetch_sub(n, Ordering::Relaxed);
    MEM_BLOCKS.fetch_sub(1, Ordering::Relaxed);
    unsafe { free(base as *mut c_void) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlMemRealloc(p: *mut c_void, n: usize) -> *mut c_void {
    if p.is_null() {
        return unsafe { xmlMemMalloc(n) };
    }
    let base = unsafe { (p as *mut u8).sub(MEM_HDR) };
    let old = unsafe { (base as *mut usize).read() };
    let q = unsafe { realloc(base as *mut c_void, n + MEM_HDR) } as *mut u8;
    if q.is_null() {
        return null_mut();
    }
    unsafe { (q as *mut usize).write(n) };
    MEM_USED.fetch_sub(old, Ordering::Relaxed);
    MEM_USED.fetch_add(n, Ordering::Relaxed);
    unsafe { q.add(MEM_HDR) as *mut c_void }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlReallocLoc(p: *mut c_void, n: usize, _file: *const c_char, _line: c_int) -> *mut c_void {
    unsafe { xmlMemRealloc(p, n) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlMemoryStrdup(s: *const c_char) -> *mut c_char {
    if s.is_null() {
        return null_mut();
    }
    let b = unsafe { CStr::from_ptr(s) }.to_bytes();
    let p = unsafe { xmlMemMalloc(b.len() + 1) } as *mut u8;
    if !p.is_null() {
        unsafe {
            std::ptr::copy_nonoverlapping(b.as_ptr(), p, b.len());
            *p.add(b.len()) = 0;
        }
    }
    p as *mut c_char
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlMemStrdupLoc(s: *const c_char, _file: *const c_char, _line: c_int) -> *mut c_char {
    unsafe { xmlMemoryStrdup(s) }
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlMemUsed() -> c_int {
    MEM_USED.load(Ordering::Relaxed) as c_int
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlMemSize(p: *mut c_void) -> usize {
    if p.is_null() {
        return 0;
    }
    unsafe { ((p as *mut u8).sub(MEM_HDR) as *mut usize).read() }
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlMemBlocks() -> c_int {
    MEM_BLOCKS.load(Ordering::Relaxed) as c_int
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlMemDisplay(_f: *mut c_void) {}

#[unsafe(no_mangle)]
pub extern "C" fn xmlMemDisplayLast(_f: *mut c_void, _n: c_long) {}

#[unsafe(no_mangle)]
pub extern "C" fn xmlMemShow(_f: *mut c_void, _n: c_int) {}

#[unsafe(no_mangle)]
pub extern "C" fn xmlMemoryDump() {}

#[unsafe(no_mangle)]
pub extern "C" fn xmlInitMemory() -> c_int {
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlCleanupMemory() {}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlMemSetup(f: FreeFn, m: MallocFn, r: ReallocFn, s: StrdupFn) -> c_int {
    if f.is_none() || m.is_none() || r.is_none() || s.is_none() {
        return -1;
    }
    unsafe {
        xmlFree = f;
        xmlMalloc = m;
        xmlMallocAtomic = m;
        xmlRealloc = r;
        xmlMemStrdup = s;
    }
    0
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlMemGet(f: *mut FreeFn, m: *mut MallocFn, r: *mut ReallocFn, s: *mut StrdupFn) -> c_int {
    unsafe {
        if !f.is_null() {
            *f = xmlFree;
        }
        if !m.is_null() {
            *m = xmlMalloc;
        }
        if !r.is_null() {
            *r = xmlRealloc;
        }
        if !s.is_null() {
            *s = xmlMemStrdup;
        }
    }
    0
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlGcMemSetup(f: FreeFn, m: MallocFn, _ma: MallocFn, r: ReallocFn, s: StrdupFn) -> c_int {
    unsafe { xmlMemSetup(f, m, r, s) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlGcMemGet(f: *mut FreeFn, m: *mut MallocFn, ma: *mut MallocFn, r: *mut ReallocFn, s: *mut StrdupFn) -> c_int {
    unsafe {
        if !ma.is_null() {
            *ma = xmlMallocAtomic;
        }
        xmlMemGet(f, m, r, s)
    }
}

// --- thread-local settings (globals.h) ---------------------------------------

pub struct Globals {
    pub do_validity: c_int,
    pub get_warnings: c_int,
    pub keep_blanks: c_int,
    pub line_numbers: c_int,
    pub load_ext_dtd: c_int,
    pub pedantic: c_int,
    pub substitute: c_int,
    pub indent_tree_output: c_int,
    pub tree_indent_string: *const c_char,
    pub save_no_empty_tags: c_int,
    pub last_error: XmlError,
    pub generic_error: GenericErrorF,
    pub generic_ctx: *mut c_void,
    pub structured: StructuredErrorF,
    pub structured_ctx: *mut c_void,
    pub register_node: Option<unsafe extern "C" fn(*mut Node)>,
    pub deregister_node: Option<unsafe extern "C" fn(*mut Node)>,
}

thread_local! {
    static GLOBALS: UnsafeCell<Globals> = const { UnsafeCell::new(Globals {
        do_validity: 0,
        get_warnings: 1,
        keep_blanks: 1,
        line_numbers: 0,
        load_ext_dtd: 0,
        pedantic: 0,
        substitute: 0,
        indent_tree_output: 1,
        tree_indent_string: c"  ".as_ptr(),
        save_no_empty_tags: 0,
        last_error: XmlError::zero(),
        generic_error: None,
        generic_ctx: null_mut(),
        structured: None,
        structured_ctx: null_mut(),
        register_node: None,
        deregister_node: None,
    }) };
}

/// This thread's settings. The pointer stays valid as long as the thread.
pub fn globals() -> *mut Globals {
    GLOBALS.with(|g| g.get())
}

macro_rules! global_fn {
    ($name:ident, $field:ident, $ty:ty) => {
        #[unsafe(no_mangle)]
        pub extern "C" fn $name() -> *mut $ty {
            unsafe { &raw mut (*globals()).$field }
        }
    };
}

global_fn!(__xmlDoValidityCheckingDefaultValue, do_validity, c_int);
global_fn!(__xmlGetWarningsDefaultValue, get_warnings, c_int);
global_fn!(__xmlKeepBlanksDefaultValue, keep_blanks, c_int);
global_fn!(__xmlLineNumbersDefaultValue, line_numbers, c_int);
global_fn!(__xmlLoadExtDtdDefaultValue, load_ext_dtd, c_int);
global_fn!(__xmlPedanticParserDefaultValue, pedantic, c_int);
global_fn!(__xmlSubstituteEntitiesDefaultValue, substitute, c_int);
global_fn!(__xmlIndentTreeOutput, indent_tree_output, c_int);
global_fn!(__xmlTreeIndentString, tree_indent_string, *const c_char);
global_fn!(__xmlSaveNoEmptyTags, save_no_empty_tags, c_int);
global_fn!(__xmlGenericError, generic_error, GenericErrorF);
global_fn!(__xmlGenericErrorContext, generic_ctx, *mut c_void);
global_fn!(__xmlStructuredError, structured, StructuredErrorF);
global_fn!(__xmlStructuredErrorContext, structured_ctx, *mut c_void);
global_fn!(__xmlRegisterNodeDefaultValue, register_node, Option<unsafe extern "C" fn(*mut Node)>);
global_fn!(__xmlDeregisterNodeDefaultValue, deregister_node, Option<unsafe extern "C" fn(*mut Node)>);

#[unsafe(no_mangle)]
pub extern "C" fn __xmlLastError() -> *const XmlError {
    unsafe { &raw const (*globals()).last_error }
}

macro_rules! default_setter {
    ($name:ident, $field:ident) => {
        #[unsafe(no_mangle)]
        pub extern "C" fn $name(v: c_int) -> c_int {
            unsafe {
                let g = globals();
                let old = (*g).$field;
                (*g).$field = v;
                old
            }
        }
    };
}

default_setter!(xmlKeepBlanksDefault, keep_blanks);
default_setter!(xmlSubstituteEntitiesDefault, substitute);
default_setter!(xmlLineNumbersDefault, line_numbers);
default_setter!(xmlPedanticParserDefault, pedantic);

#[unsafe(no_mangle)]
pub extern "C" fn xmlThrDefIndentTreeOutput(v: c_int) -> c_int {
    let g = globals();
    unsafe {
        let old = (*g).indent_tree_output;
        (*g).indent_tree_output = v;
        old
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlThrDefSaveNoEmptyTags(v: c_int) -> c_int {
    let g = globals();
    unsafe {
        let old = (*g).save_no_empty_tags;
        (*g).save_no_empty_tags = v;
        old
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlInitParser() {}

#[unsafe(no_mangle)]
pub extern "C" fn xmlInitGlobals() {}

#[unsafe(no_mangle)]
pub extern "C" fn xmlCleanupParser() {}

#[unsafe(no_mangle)]
pub extern "C" fn xmlCleanupGlobals() {}

#[unsafe(no_mangle)]
pub extern "C" fn xmlCheckVersion(_v: c_int) {}

#[unsafe(no_mangle)]
pub extern "C" fn xmlHasFeature(feature: c_int) -> c_int {
    // XML_WITH_THREAD 1, TREE 2, OUTPUT 3, PUSH 4, SAX1 7
    matches!(feature, 1 | 2 | 3 | 4 | 7) as c_int
}

// --- strings (xmlstring.h) ------------------------------------------------------

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlStrdup(s: *const XChar) -> *mut XChar {
    if s.is_null() { null_mut() } else { xstrdup(unsafe { cbytes(s) }) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCharStrdup(s: *const c_char) -> *mut XChar {
    unsafe { xmlStrdup(s as *const XChar) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlStrndup(s: *const XChar, n: c_int) -> *mut XChar {
    if s.is_null() || n < 0 {
        return null_mut();
    }
    xstrdup(unsafe { std::slice::from_raw_parts(s, n as usize) })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCharStrndup(s: *const c_char, n: c_int) -> *mut XChar {
    unsafe { xmlStrndup(s as *const XChar, n) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlStrsub(s: *const XChar, start: c_int, len: c_int) -> *mut XChar {
    if s.is_null() || start < 0 || len < 0 {
        return null_mut();
    }
    let b = unsafe { cbytes(s) };
    let a = b.iter().enumerate().filter(|(_, c)| **c & 0xC0 != 0x80).nth(start as usize).map(|(i, _)| i);
    let Some(a) = a else { return null_mut() };
    let rest = &b[a..];
    let e = rest.iter().enumerate().filter(|(_, c)| **c & 0xC0 != 0x80).nth(len as usize).map_or(rest.len(), |(i, _)| i);
    xstrdup(&rest[..e])
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlStrlen(s: *const XChar) -> c_int {
    unsafe { cbytes(s) }.len() as c_int
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlStrcmp(a: *const XChar, b: *const XChar) -> c_int {
    if a == b {
        return 0;
    }
    if a.is_null() {
        return -1;
    }
    if b.is_null() {
        return 1;
    }
    match unsafe { cbytes(a) }.cmp(unsafe { cbytes(b) }) {
        std::cmp::Ordering::Less => -1,
        std::cmp::Ordering::Equal => 0,
        std::cmp::Ordering::Greater => 1,
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlStrEqual(a: *const XChar, b: *const XChar) -> c_int {
    if a == b {
        return 1;
    }
    if a.is_null() || b.is_null() {
        return 0;
    }
    (unsafe { cbytes(a) } == unsafe { cbytes(b) }) as c_int
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlStrQEqual(pref: *const XChar, name: *const XChar, s: *const XChar) -> c_int {
    if pref.is_null() {
        return unsafe { xmlStrEqual(name, s) };
    }
    if name.is_null() || s.is_null() {
        return 0;
    }
    let mut q = unsafe { cbytes(pref) }.to_vec();
    q.push(b':');
    q.extend_from_slice(unsafe { cbytes(name) });
    (q == unsafe { cbytes(s) }) as c_int
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlStrncmp(a: *const XChar, b: *const XChar, n: c_int) -> c_int {
    if n <= 0 || a == b {
        return 0;
    }
    if a.is_null() {
        return -1;
    }
    if b.is_null() {
        return 1;
    }
    let (x, y) = unsafe { (cbytes(a), cbytes(b)) };
    let n = n as usize;
    match x[..x.len().min(n)].cmp(&y[..y.len().min(n)]) {
        std::cmp::Ordering::Less => -1,
        std::cmp::Ordering::Equal => 0,
        std::cmp::Ordering::Greater => 1,
    }
}

fn fold(b: &[u8]) -> Vec<u8> {
    b.to_ascii_lowercase()
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlStrcasecmp(a: *const XChar, b: *const XChar) -> c_int {
    if a == b {
        return 0;
    }
    if a.is_null() {
        return -1;
    }
    if b.is_null() {
        return 1;
    }
    match fold(unsafe { cbytes(a) }).cmp(&fold(unsafe { cbytes(b) })) {
        std::cmp::Ordering::Less => -1,
        std::cmp::Ordering::Equal => 0,
        std::cmp::Ordering::Greater => 1,
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlStrncasecmp(a: *const XChar, b: *const XChar, n: c_int) -> c_int {
    if n <= 0 || a == b {
        return 0;
    }
    if a.is_null() {
        return -1;
    }
    if b.is_null() {
        return 1;
    }
    let (x, y) = unsafe { (fold(cbytes(a)), fold(cbytes(b))) };
    let n = n as usize;
    match x[..x.len().min(n)].cmp(&y[..y.len().min(n)]) {
        std::cmp::Ordering::Less => -1,
        std::cmp::Ordering::Equal => 0,
        std::cmp::Ordering::Greater => 1,
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlStrchr(s: *const XChar, c: XChar) -> *const XChar {
    let b = unsafe { cbytes(s) };
    b.iter().position(|&x| x == c).map_or(null(), |i| unsafe { s.add(i) })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlStrstr(s: *const XChar, v: *const XChar) -> *const XChar {
    let (h, n) = unsafe { (cbytes(s), cbytes(v)) };
    if s.is_null() || v.is_null() {
        return null();
    }
    if n.is_empty() {
        return s;
    }
    h.windows(n.len()).position(|w| w == n).map_or(null(), |i| unsafe { s.add(i) })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlStrcasestr(s: *const XChar, v: *const XChar) -> *const XChar {
    if s.is_null() || v.is_null() {
        return null();
    }
    let (h, n) = unsafe { (fold(cbytes(s)), fold(cbytes(v))) };
    if n.is_empty() {
        return s;
    }
    h.windows(n.len()).position(|w| w == n.as_slice()).map_or(null(), |i| unsafe { s.add(i) })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlStrncat(cur: *mut XChar, add: *const XChar, len: c_int) -> *mut XChar {
    if add.is_null() || len == 0 {
        return cur;
    }
    if len < 0 {
        return null_mut();
    }
    if cur.is_null() {
        return unsafe { xmlStrndup(add, len) };
    }
    let n = unsafe { cbytes(cur) }.len();
    let p = xrealloc(cur as *mut c_void, n + len as usize + 1) as *mut u8;
    if p.is_null() {
        xfree(cur as *mut c_void);
        return null_mut();
    }
    unsafe {
        std::ptr::copy_nonoverlapping(add, p.add(n), len as usize);
        *p.add(n + len as usize) = 0;
    }
    p
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlStrcat(cur: *mut XChar, add: *const XChar) -> *mut XChar {
    if add.is_null() {
        return cur;
    }
    unsafe { xmlStrncat(cur, add, cbytes(add).len() as c_int) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlStrncatNew(a: *const XChar, b: *const XChar, len: c_int) -> *mut XChar {
    let bb = unsafe { cbytes(b) };
    let n = if len < 0 { bb.len() } else { (len as usize).min(bb.len()) };
    let mut v = unsafe { cbytes(a) }.to_vec();
    v.extend_from_slice(&bb[..n]);
    xstrdup(&v)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlUTF8Strlen(s: *const XChar) -> c_int {
    if s.is_null() {
        return -1;
    }
    unsafe { cbytes(s) }.iter().filter(|&&c| c & 0xC0 != 0x80).count() as c_int
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlUTF8Strsize(s: *const XChar, len: c_int) -> c_int {
    if s.is_null() || len <= 0 {
        return 0;
    }
    let b = unsafe { cbytes(s) };
    b.iter().enumerate().filter(|(_, c)| **c & 0xC0 != 0x80).nth(len as usize).map_or(b.len(), |(i, _)| i) as c_int
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlUTF8Strpos(s: *const XChar, pos: c_int) -> *const XChar {
    if s.is_null() || pos < 0 {
        return null();
    }
    let b = unsafe { cbytes(s) };
    b.iter().enumerate().filter(|(_, c)| **c & 0xC0 != 0x80).nth(pos as usize).map_or(null(), |(i, _)| unsafe { s.add(i) })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlUTF8Strndup(s: *const XChar, len: c_int) -> *mut XChar {
    let n = unsafe { xmlUTF8Strsize(s, len) };
    unsafe { xmlStrndup(s, n) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlUTF8Strsub(s: *const XChar, start: c_int, len: c_int) -> *mut XChar {
    unsafe { xmlStrsub(s, start, len) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlGetUTF8Char(s: *const u8, len: *mut c_int) -> c_int {
    if s.is_null() || len.is_null() {
        return -1;
    }
    let max = unsafe { *len };
    if max < 1 {
        unsafe { *len = 0 };
        return -1;
    }
    let c = unsafe { *s };
    let n = if c < 0x80 {
        1
    } else if c & 0xE0 == 0xC0 {
        2
    } else if c & 0xF0 == 0xE0 {
        3
    } else if c & 0xF8 == 0xF0 {
        4
    } else {
        0
    };
    if n == 0 || n > max {
        unsafe { *len = 0 };
        return -1;
    }
    let b = unsafe { std::slice::from_raw_parts(s, n as usize) };
    match std::str::from_utf8(b) {
        Ok(t) => {
            unsafe { *len = n };
            t.chars().next().map_or(-1, |ch| ch as c_int)
        }
        Err(_) => {
            unsafe { *len = 0 };
            -1
        }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCheckUTF8(s: *const XChar) -> c_int {
    if s.is_null() {
        return 0;
    }
    std::str::from_utf8(unsafe { cbytes(s) }).is_ok() as c_int
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCopyChar(_len: c_int, out: *mut XChar, val: c_int) -> c_int {
    unsafe { xmlCopyCharMultiByte(out, val) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCopyCharMultiByte(out: *mut XChar, val: c_int) -> c_int {
    if out.is_null() {
        return 0;
    }
    let Some(c) = char::from_u32(val as u32) else { return 0 };
    let mut tmp = [0u8; 4];
    let s = c.encode_utf8(&mut tmp);
    unsafe { std::ptr::copy_nonoverlapping(s.as_ptr(), out, s.len()) };
    s.len() as c_int
}

// --- hash tables (hash.h) ---------------------------------------------------------

type Key = (Vec<u8>, Vec<u8>, Vec<u8>);

/// `xmlHashTable`: entries in the order they were added.
pub struct Hash {
    map: FastMap<Key, usize>,
    entries: Vec<Option<(Key, *mut c_void)>>,
    live: usize,
}

pub type HashDeallocator = Option<unsafe extern "C" fn(*mut c_void, *const XChar)>;
pub type HashScanner = Option<unsafe extern "C" fn(*mut c_void, *mut c_void, *const XChar)>;
pub type HashScannerFull =
    Option<unsafe extern "C" fn(*mut c_void, *mut c_void, *const XChar, *const XChar, *const XChar)>;
pub type HashCopier = Option<unsafe extern "C" fn(*mut c_void, *const XChar) -> *mut c_void>;

impl Hash {
    pub fn new() -> *mut Hash {
        Box::into_raw(Box::new(Hash { map: fast_map(), entries: Vec::new(), live: 0 }))
    }

    fn key(a: *const XChar, b: *const XChar, c: *const XChar) -> Key {
        unsafe { (cbytes(a).to_vec(), cbytes(b).to_vec(), cbytes(c).to_vec()) }
    }

    pub fn get(&self, k: &Key) -> *mut c_void {
        self.map.get(k).and_then(|&i| self.entries[i].as_ref()).map_or(null_mut(), |e| e.1)
    }

    pub fn get1(&self, name: &[u8]) -> *mut c_void {
        self.get(&(name.to_vec(), Vec::new(), Vec::new()))
    }

    pub fn get2(&self, a: &[u8], b: &[u8]) -> *mut c_void {
        self.get(&(a.to_vec(), b.to_vec(), Vec::new()))
    }

    /// Adds an entry; false if the key is taken.
    pub fn add(&mut self, k: Key, v: *mut c_void) -> bool {
        if self.map.contains_key(&k) {
            return false;
        }
        self.map.insert(k.clone(), self.entries.len());
        self.entries.push(Some((k, v)));
        self.live += 1;
        true
    }

    fn update(&mut self, k: Key, v: *mut c_void, dealloc: HashDeallocator) {
        if let Some(&i) = self.map.get(&k) {
            if let Some(e) = self.entries[i].as_mut() {
                if let Some(f) = dealloc {
                    let name = nul(&e.0.0);
                    unsafe { f(e.1, name.as_ptr()) };
                }
                e.1 = v;
            }
        } else {
            self.add(k, v);
        }
    }

    fn remove(&mut self, k: &Key) -> Option<*mut c_void> {
        let i = self.map.remove(k)?;
        let e = self.entries[i].take()?;
        self.live -= 1;
        Some(e.1)
    }

    /// The values, in the order they were added.
    pub fn values(&self) -> Vec<*mut c_void> {
        self.entries.iter().flatten().map(|e| e.1).collect()
    }

    fn items(&self) -> Vec<(Key, *mut c_void)> {
        self.entries.iter().flatten().map(|(k, v)| (k.clone(), *v)).collect()
    }
}

/// `s` with a NUL after it.
pub fn nul(s: &[u8]) -> Vec<u8> {
    let mut v = Vec::with_capacity(s.len() + 1);
    v.extend_from_slice(s);
    v.push(0);
    v
}

fn opt_nul(s: &[u8]) -> Option<Vec<u8>> {
    if s.is_empty() { None } else { Some(nul(s)) }
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlHashCreate(_size: c_int) -> *mut Hash {
    Hash::new()
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlHashCreateDict(_size: c_int, _dict: *mut c_void) -> *mut Hash {
    Hash::new()
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlHashFree(h: *mut Hash, dealloc: HashDeallocator) {
    if h.is_null() {
        return;
    }
    let h = unsafe { Box::from_raw(h) };
    if let Some(f) = dealloc {
        for (k, v) in h.items() {
            let name = nul(&k.0);
            unsafe { f(v, name.as_ptr()) };
        }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlHashDefaultDeallocator(p: *mut c_void, _name: *const XChar) {
    xfree(p);
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlHashAddEntry3(
    h: *mut Hash,
    a: *const XChar,
    b: *const XChar,
    c: *const XChar,
    v: *mut c_void,
) -> c_int {
    if h.is_null() || a.is_null() {
        return -1;
    }
    if unsafe { &mut *h }.add(Hash::key(a, b, c), v) { 0 } else { -1 }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlHashAdd3(h: *mut Hash, a: *const XChar, b: *const XChar, c: *const XChar, v: *mut c_void) -> c_int {
    if h.is_null() || a.is_null() {
        return -1;
    }
    if unsafe { &mut *h }.add(Hash::key(a, b, c), v) { 1 } else { 0 }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlHashAddEntry2(h: *mut Hash, a: *const XChar, b: *const XChar, v: *mut c_void) -> c_int {
    unsafe { xmlHashAddEntry3(h, a, b, null(), v) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlHashAddEntry(h: *mut Hash, a: *const XChar, v: *mut c_void) -> c_int {
    unsafe { xmlHashAddEntry3(h, a, null(), null(), v) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlHashAdd(h: *mut Hash, a: *const XChar, v: *mut c_void) -> c_int {
    unsafe { xmlHashAdd3(h, a, null(), null(), v) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlHashAdd2(h: *mut Hash, a: *const XChar, b: *const XChar, v: *mut c_void) -> c_int {
    unsafe { xmlHashAdd3(h, a, b, null(), v) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlHashUpdateEntry3(
    h: *mut Hash,
    a: *const XChar,
    b: *const XChar,
    c: *const XChar,
    v: *mut c_void,
    dealloc: HashDeallocator,
) -> c_int {
    if h.is_null() || a.is_null() {
        return -1;
    }
    unsafe { &mut *h }.update(Hash::key(a, b, c), v, dealloc);
    0
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlHashUpdateEntry2(
    h: *mut Hash,
    a: *const XChar,
    b: *const XChar,
    v: *mut c_void,
    dealloc: HashDeallocator,
) -> c_int {
    unsafe { xmlHashUpdateEntry3(h, a, b, null(), v, dealloc) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlHashUpdateEntry(h: *mut Hash, a: *const XChar, v: *mut c_void, dealloc: HashDeallocator) -> c_int {
    unsafe { xmlHashUpdateEntry3(h, a, null(), null(), v, dealloc) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlHashLookup3(h: *mut Hash, a: *const XChar, b: *const XChar, c: *const XChar) -> *mut c_void {
    if h.is_null() || a.is_null() {
        return null_mut();
    }
    unsafe { &*h }.get(&Hash::key(a, b, c))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlHashLookup2(h: *mut Hash, a: *const XChar, b: *const XChar) -> *mut c_void {
    unsafe { xmlHashLookup3(h, a, b, null()) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlHashLookup(h: *mut Hash, a: *const XChar) -> *mut c_void {
    unsafe { xmlHashLookup3(h, a, null(), null()) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlHashQLookup(h: *mut Hash, prefix: *const XChar, name: *const XChar) -> *mut c_void {
    if prefix.is_null() {
        return unsafe { xmlHashLookup(h, name) };
    }
    let mut q = unsafe { cbytes(prefix) }.to_vec();
    q.push(b':');
    q.extend_from_slice(unsafe { cbytes(name) });
    q.push(0);
    unsafe { xmlHashLookup(h, q.as_ptr()) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlHashRemoveEntry3(
    h: *mut Hash,
    a: *const XChar,
    b: *const XChar,
    c: *const XChar,
    dealloc: HashDeallocator,
) -> c_int {
    if h.is_null() || a.is_null() {
        return -1;
    }
    match unsafe { &mut *h }.remove(&Hash::key(a, b, c)) {
        Some(v) => {
            if let Some(f) = dealloc {
                unsafe { f(v, a) };
            }
            0
        }
        None => -1,
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlHashRemoveEntry2(h: *mut Hash, a: *const XChar, b: *const XChar, d: HashDeallocator) -> c_int {
    unsafe { xmlHashRemoveEntry3(h, a, b, null(), d) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlHashRemoveEntry(h: *mut Hash, a: *const XChar, d: HashDeallocator) -> c_int {
    unsafe { xmlHashRemoveEntry3(h, a, null(), null(), d) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlHashSize(h: *mut Hash) -> c_int {
    if h.is_null() { -1 } else { unsafe { &*h }.live as c_int }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlHashScan(h: *mut Hash, f: HashScanner, data: *mut c_void) {
    if h.is_null() {
        return;
    }
    let Some(f) = f else { return };
    for (k, v) in unsafe { &*h }.items() {
        let a = nul(&k.0);
        unsafe { f(v, data, a.as_ptr()) };
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlHashScanFull(h: *mut Hash, f: HashScannerFull, data: *mut c_void) {
    if h.is_null() {
        return;
    }
    let Some(f) = f else { return };
    for (k, v) in unsafe { &*h }.items() {
        let a = nul(&k.0);
        let b = opt_nul(&k.1);
        let c = opt_nul(&k.2);
        unsafe {
            f(v, data, a.as_ptr(), b.as_ref().map_or(null(), |x| x.as_ptr()), c.as_ref().map_or(null(), |x| x.as_ptr()))
        };
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlHashCopySafe(h: *mut Hash, copy: HashCopier, dealloc: HashDeallocator) -> *mut Hash {
    if h.is_null() {
        return null_mut();
    }
    let Some(copy) = copy else { return null_mut() };
    let n = Hash::new();
    for (k, v) in unsafe { &*h }.items() {
        let a = nul(&k.0);
        let c = unsafe { copy(v, a.as_ptr()) };
        if c.is_null() {
            unsafe { xmlHashFree(n, dealloc) };
            return null_mut();
        }
        unsafe { &mut *n }.add(k, c);
    }
    n
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlHashCopy(h: *mut Hash, copy: HashCopier) -> *mut Hash {
    unsafe { xmlHashCopySafe(h, copy, None) }
}

// --- dictionaries (dict.h): interned strings, freed with the dictionary ------

/// `xmlDict`: interned strings, NUL-terminated, in pools freed with the
/// dictionary (so ownership is an address check), found through an
/// open-addressing table of (hash, string) with a per-dictionary seed. A
/// dictionary made with `xmlDictCreateSub` looks in its parent first, as
/// libxml2's does.
pub struct Dict {
    /// Slots: the string's hash (0 for empty), pointer and length.
    slots: Vec<(u64, *const XChar, usize)>,
    len: usize,
    /// String storage: each pool is filled, then a larger one is added.
    pools: Vec<Box<[u8]>>,
    used: usize,
    seed: FastState,
    parent: *mut Dict,
    refs: usize,
}

/// `p[..b.len()] == b`, without a call for short strings.
#[inline]
pub(crate) unsafe fn bytes_eq(p: *const u8, b: &[u8]) -> bool {
    unsafe {
        let n = b.len();
        let q = b.as_ptr();
        if n >= 8 && n <= 16 {
            let r8 = |x: *const u8, k: usize| std::ptr::read_unaligned(x.add(k) as *const u64);
            r8(p, 0) == r8(q, 0) && r8(p, n - 8) == r8(q, n - 8)
        } else if n >= 4 && n < 8 {
            let r4 = |x: *const u8, k: usize| std::ptr::read_unaligned(x.add(k) as *const u32);
            r4(p, 0) == r4(q, 0) && r4(p, n - 4) == r4(q, n - 4)
        } else if n < 8 {
            b.iter().enumerate().all(|(k, &c)| *p.add(k) == c)
        } else {
            std::slice::from_raw_parts(p, b.len()) == b
        }
    }
}

impl Dict {
    fn new(parent: *mut Dict) -> Dict {
        Dict { slots: vec![(0, null(), 0); 64], len: 0, pools: Vec::new(), used: 0, seed: FastState::new(), parent, refs: 1 }
    }

    #[inline]
    fn hash(&self, b: &[u8]) -> u64 {
        // FastHasher's mixing, with the tail read in one go.
        let mut h = self.seed.0;
        let n = b.len();
        let mut i = 0;
        while i + 8 <= n {
            let w = unsafe { std::ptr::read_unaligned(b.as_ptr().add(i) as *const u64) };
            h = (h ^ u64::from_le(w)).wrapping_mul(K).rotate_left(29);
            i += 8;
        }
        let r = n - i;
        let w = unsafe {
            let p = b.as_ptr().add(i);
            if r == 0 {
                0
            } else if n >= 8 {
                // The last eight bytes, overlapping the words before.
                std::ptr::read_unaligned(b.as_ptr().add(n - 8) as *const u64)
            } else if r >= 4 {
                let lo = std::ptr::read_unaligned(p as *const u32) as u64;
                let hi = std::ptr::read_unaligned(p.add(r - 4) as *const u32) as u64;
                lo | (hi << 32)
            } else {
                // 1 to 3 bytes: first, middle, last.
                (*p as u64) | ((*p.add(r / 2) as u64) << 8) | ((*p.add(r - 1) as u64) << 16)
            }
        };
        h = (h ^ w ^ ((n as u64) << 56)).wrapping_mul(K).rotate_left(29);
        let m = (h as u128).wrapping_mul(K as u128 | 1);
        ((m as u64) ^ ((m >> 64) as u64)) | 1
    }

    #[inline]
    fn find(&self, b: &[u8], h: u64) -> Result<*const XChar, usize> {
        let mask = self.slots.len() - 1;
        // The high bits pick the slot (the low bit is always set).
        let mut i = (h >> 32) as usize & mask;
        loop {
            let (sh, p, l) = self.slots[i];
            if sh == 0 {
                return Err(i);
            }
            if sh == h && l == b.len() && unsafe { bytes_eq(p, b) } {
                return Ok(p);
            }
            i = (i + 1) & mask;
        }
    }

    fn get(&self, b: &[u8]) -> Option<*const XChar> {
        self.find(b, self.hash(b)).ok()
    }

    fn store(&mut self, b: &[u8]) -> *const XChar {
        let need = b.len() + 1;
        let room = self.pools.last().map_or(0, |p| p.len() - self.used);
        if room < need {
            let size = self.pools.last().map_or(4096, |p| (p.len() * 2).min(1 << 20)).max(need);
            self.pools.push(vec![0u8; size].into_boxed_slice());
            self.used = 0;
        }
        let pool = self.pools.last_mut().unwrap();
        pool[self.used..self.used + b.len()].copy_from_slice(b);
        pool[self.used + b.len()] = 0;
        let p = pool[self.used..].as_ptr();
        self.used += need;
        p
    }

    fn lookup(&mut self, b: &[u8]) -> *const XChar {
        if !self.parent.is_null() {
            if let Some(p) = unsafe { &*self.parent }.get(b) {
                return p;
            }
        }
        let h = self.hash(b);
        match self.find(b, h) {
            Ok(p) => p,
            Err(mut i) => {
                if (self.len + 1) * 4 > self.slots.len() * 3 {
                    self.grow();
                    i = self.find(b, h).unwrap_err();
                }
                let p = self.store(b);
                self.slots[i] = (h, p, b.len());
                self.len += 1;
                p
            }
        }
    }

    fn grow(&mut self) {
        let old = std::mem::replace(&mut self.slots, vec![(0, null(), 0); 0]);
        self.slots = vec![(0, null(), 0); old.len() * 2];
        let mask = self.slots.len() - 1;
        for e in old {
            if e.0 != 0 {
                let mut i = (e.0 >> 32) as usize & mask;
                while self.slots[i].0 != 0 {
                    i = (i + 1) & mask;
                }
                self.slots[i] = e;
            }
        }
    }

    fn owns(&self, s: *const XChar) -> bool {
        let a = s as usize;
        self.pools.iter().rev().any(|p| (p.as_ptr() as usize..p.as_ptr() as usize + p.len()).contains(&a))
            || (!self.parent.is_null() && unsafe { &*self.parent }.owns(s))
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlDictCreate() -> *mut Dict {
    Box::into_raw(Box::new(Dict::new(null_mut())))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlDictCreateSub(sub: *mut Dict) -> *mut Dict {
    if !sub.is_null() {
        unsafe { (*sub).refs += 1 };
    }
    Box::into_raw(Box::new(Dict::new(sub)))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlDictReference(d: *mut Dict) -> c_int {
    if d.is_null() {
        return -1;
    }
    unsafe { (*d).refs += 1 };
    0
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlDictFree(d: *mut Dict) {
    if d.is_null() {
        return;
    }
    unsafe {
        (*d).refs -= 1;
        if (*d).refs > 0 {
            return;
        }
        let d = Box::from_raw(d);
        xmlDictFree(d.parent);
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlDictLookup(d: *mut Dict, s: *const XChar, len: c_int) -> *const XChar {
    if d.is_null() || s.is_null() {
        return null();
    }
    let b = if len < 0 { unsafe { cbytes(s) } } else { unsafe { std::slice::from_raw_parts(s, len as usize) } };
    unsafe { &mut *d }.lookup(b)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlDictExists(d: *mut Dict, s: *const XChar, len: c_int) -> *const XChar {
    if d.is_null() || s.is_null() {
        return null();
    }
    let b = if len < 0 { unsafe { cbytes(s) } } else { unsafe { std::slice::from_raw_parts(s, len as usize) } };
    let d = unsafe { &*d };
    if !d.parent.is_null() {
        if let Some(p) = unsafe { &*d.parent }.get(b) {
            return p;
        }
    }
    d.get(b).unwrap_or(null())
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlDictQLookup(d: *mut Dict, prefix: *const XChar, name: *const XChar) -> *const XChar {
    if prefix.is_null() {
        return unsafe { xmlDictLookup(d, name, -1) };
    }
    let mut q = unsafe { cbytes(prefix) }.to_vec();
    q.push(b':');
    q.extend_from_slice(unsafe { cbytes(name) });
    unsafe { xmlDictLookup(d, q.as_ptr(), q.len() as c_int) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlDictOwns(d: *mut Dict, s: *const XChar) -> c_int {
    if d.is_null() || s.is_null() {
        return -1;
    }
    unsafe { &*d }.owns(s) as c_int
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlDictSize(d: *mut Dict) -> c_int {
    if d.is_null() {
        return -1;
    }
    let d = unsafe { &*d };
    (d.len + if d.parent.is_null() { 0 } else { unsafe { &*d.parent }.len }) as c_int
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlDictSetLimit(_d: *mut Dict, _limit: usize) -> usize {
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlDictGetUsage(_d: *mut Dict) -> usize {
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlDictCleanup() {}

/// Whether `p` is a string of the dictionary `d` (which libxml2's tree code
/// must not free).
pub fn dict_owns(d: *mut c_void, p: *const XChar) -> bool {
    !d.is_null() && !p.is_null() && unsafe { xmlDictOwns(d as *mut Dict, p) } == 1
}

// --- errors (xmlerror.h) ----------------------------------------------------------

/// Frees the strings an error owns, and zeroes it.
pub fn reset_error(e: &mut XmlError) {
    unsafe {
        free(e.message as *mut c_void);
        free(e.file as *mut c_void);
        free(e.str1 as *mut c_void);
        free(e.str2 as *mut c_void);
        free(e.str3 as *mut c_void);
    }
    *e = XmlError::zero();
}

fn c_dup(s: Option<&[u8]>) -> *mut c_char {
    match s {
        None => null_mut(),
        Some(b) => {
            let p = unsafe { malloc(b.len() + 1) } as *mut u8;
            if !p.is_null() {
                unsafe {
                    std::ptr::copy_nonoverlapping(b.as_ptr(), p, b.len());
                    *p.add(b.len()) = 0;
                }
            }
            p as *mut c_char
        }
    }
}

/// Copies `src` into `dst`, strings and all (the strings come from the C
/// allocator, not `xmlMalloc`, as libxml2's do).
pub fn copy_error(src: &XmlError, dst: &mut XmlError) {
    if std::ptr::eq(src, dst) {
        return;
    }
    let msg = unsafe { copt(src.message as *const XChar) };
    let file = unsafe { copt(src.file as *const XChar) };
    let s1 = unsafe { copt(src.str1 as *const XChar) };
    let s2 = unsafe { copt(src.str2 as *const XChar) };
    let s3 = unsafe { copt(src.str3 as *const XChar) };
    let (m, f, a, b, c) = (c_dup(msg), c_dup(file), c_dup(s1), c_dup(s2), c_dup(s3));
    reset_error(dst);
    *dst = XmlError { message: m, file: f, str1: a, str2: b, str3: c, ..*src };
}

/// An error, as libxml2 makes one.
pub struct Raised<'a> {
    pub domain: c_int,
    pub code: c_int,
    pub level: c_int,
    pub message: &'a [u8],
    pub file: Option<&'a [u8]>,
    pub line: c_int,
    pub col: c_int,
    pub str1: Option<&'a [u8]>,
    pub str2: Option<&'a [u8]>,
    pub str3: Option<&'a [u8]>,
    pub int1: c_int,
    pub ctxt: *mut c_void,
    pub node: *mut c_void,
}

pub fn fill_error(r: &Raised, e: &mut XmlError) {
    reset_error(e);
    *e = XmlError {
        domain: r.domain,
        code: r.code,
        message: c_dup(Some(r.message)),
        level: r.level,
        file: c_dup(r.file),
        line: r.line,
        str1: c_dup(r.str1),
        str2: c_dup(r.str2),
        str3: c_dup(r.str3),
        int1: r.int1,
        int2: r.col,
        ctxt: r.ctxt,
        node: r.node,
    };
}

/// Reports an error with no parser context (or through one, from
/// `parser.rs`): the last error is set, then the structured handler or the
/// generic one gets it.
pub fn raise(r: &Raised, schannel: StructuredErrorF, sdata: *mut c_void, channel: GenericErrorF, data: *mut c_void) {
    let g = globals();
    let last = unsafe { &mut (*g).last_error };
    fill_error(r, last);
    let e = unsafe { (*g).last_error };
    unsafe {
        if let Some(s) = schannel {
            s(sdata, &e);
        } else if let Some(s) = (*g).structured {
            s((*g).structured_ctx, &e);
        } else if let Some(c) = channel {
            if is_default_channel(c) {
                format_error(&e, generic_channel(), (*g).generic_ctx);
            } else {
                c(data, c"%s".as_ptr(), e.message);
            }
        } else {
            format_error(&e, generic_channel(), (*g).generic_ctx);
        }
    }
}

unsafe extern "C" {
    static stderr: *mut c_void;
    fn fprintf(f: *mut c_void, fmt: *const c_char, ...) -> c_int;
    fn fwrite(p: *const c_void, size: usize, n: usize, f: *mut c_void) -> usize;
}

/// `xmlGenericErrorDefaultFunc`: writes to stderr. Only the format string
/// is printed; the arguments of libxml2's own calls are formatted before.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlGenericErrorDefaultFunc(_ctx: *mut c_void, msg: *const c_char) {
    unsafe { fprintf(stderr, c"%s".as_ptr(), msg) };
}

/// `xmlParserError` and its kind: the legacy handlers libxml2's default
/// SAX handler names; an error that would go to one is formatted instead.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlParserError(_ctx: *mut c_void, msg: *const c_char) {
    unsafe { xmlGenericErrorDefaultFunc(null_mut(), msg) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlParserWarning(_ctx: *mut c_void, msg: *const c_char) {
    unsafe { xmlGenericErrorDefaultFunc(null_mut(), msg) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlParserValidityError(_ctx: *mut c_void, msg: *const c_char) {
    unsafe { xmlGenericErrorDefaultFunc(null_mut(), msg) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlParserValidityWarning(_ctx: *mut c_void, msg: *const c_char) {
    unsafe { xmlGenericErrorDefaultFunc(null_mut(), msg) };
}

pub fn as_msg_fn(f: unsafe extern "C" fn(*mut c_void, *const c_char)) -> unsafe extern "C" fn(*mut c_void, *const c_char, ...) {
    // The handlers above take the format string alone; called with more
    // arguments (as a variadic function is), they ignore the rest.
    unsafe { std::mem::transmute(f) }
}

fn is_default_channel(c: unsafe extern "C" fn(*mut c_void, *const c_char, ...)) -> bool {
    let p = c as usize;
    [
        xmlParserError as *const () as usize,
        xmlParserWarning as *const () as usize,
        xmlParserValidityError as *const () as usize,
        xmlParserValidityWarning as *const () as usize,
        xmlGenericErrorDefaultFunc as *const () as usize,
    ]
    .contains(&p)
}

/// The generic error handler in effect.
fn generic_channel() -> unsafe extern "C" fn(*mut c_void, *const c_char, ...) {
    unsafe { (*globals()).generic_error }.unwrap_or(as_msg_fn(xmlGenericErrorDefaultFunc))
}

/// Writes `s` through a printf-like channel.
pub fn emit(channel: unsafe extern "C" fn(*mut c_void, *const c_char, ...), data: *mut c_void, s: &[u8]) {
    if s.is_empty() {
        return;
    }
    if channel as usize == xmlGenericErrorDefaultFunc as *const () as usize {
        unsafe { fwrite(s.as_ptr() as *const c_void, 1, s.len(), stderr) };
        return;
    }
    let z = nul(s);
    unsafe { channel(data, c"%s".as_ptr(), z.as_ptr()) };
}

fn domain_name(d: c_int) -> &'static [u8] {
    match d {
        1 => b"parser ",
        3 => b"namespace ",
        4 | 23 => b"validity ",
        5 => b"HTML parser ",
        6 => b"memory ",
        7 => b"output ",
        8 => b"I/O ",
        11 => b"XInclude ",
        12 => b"XPath ",
        13 => b"parser ",
        14 => b"regexp ",
        26 => b"module ",
        17 => b"Schemas validity ",
        16 => b"Schemas parser ",
        18 => b"Relax-NG parser ",
        19 => b"Relax-NG validity ",
        20 => b"Catalog ",
        21 => b"C14N ",
        22 => b"XSLT ",
        27 => b"encoding ",
        28 => b"schematron ",
        29 => b"internal buffer ",
        30 => b"URI ",
        _ => b"",
    }
}

/// `xmlFormatError`, through a printf-like channel.
pub unsafe fn format_error(e: &XmlError, channel: unsafe extern "C" fn(*mut c_void, *const c_char, ...), data: *mut c_void) {
    if e.code == ERR_OK {
        return;
    }
    let mut out: Vec<u8> = Vec::new();
    let domain = e.domain;
    let ctxt: *mut ParserCtxt = if matches!(domain, 1 | 5 | 4 | 3 | 8 | 23) { e.ctxt as *mut ParserCtxt } else { null_mut() };
    let node = e.node as *mut Node;
    let name = if !node.is_null() && unsafe { (*node).type_ } == ELEMENT_NODE && domain != 17 {
        Some(unsafe { cbytes((*node).name) })
    } else {
        None
    };
    let mut context: Option<(Vec<u8>, usize)> = None;
    if !ctxt.is_null() && !unsafe { (*ctxt).input }.is_null() {
        let input = unsafe { &*(*ctxt).input };
        if !input.filename.is_null() {
            out.extend_from_slice(unsafe { cbytes(input.filename as *const XChar) });
            out.extend_from_slice(format!(":{}: ", input.line).as_bytes());
        } else if e.line != 0 && domain == ERR_FROM_PARSER {
            out.extend_from_slice(format!("Entity: line {}: ", input.line).as_bytes());
        }
        context = Some(parser::window(input));
    } else if !e.file.is_null() {
        out.extend_from_slice(unsafe { cbytes(e.file as *const XChar) });
        out.extend_from_slice(format!(":{}: ", e.line).as_bytes());
    } else if e.line != 0 && matches!(domain, 1 | 17 | 16 | 4 | 18 | 19) {
        out.extend_from_slice(format!("Entity: line {}: ", e.line).as_bytes());
    }
    if let Some(n) = name {
        out.extend_from_slice(b"element ");
        out.extend_from_slice(n);
        out.extend_from_slice(b": ");
    }
    out.extend_from_slice(domain_name(domain));
    out.extend_from_slice(match e.level {
        1 => b"warning : ".as_slice(),
        2 | 3 => b"error : ",
        _ => b": ",
    });
    if e.message.is_null() {
        out.extend_from_slice(b"No error message provided\n");
    } else {
        let m = unsafe { cbytes(e.message as *const XChar) };
        out.extend_from_slice(m);
        if m.last() != Some(&b'\n') {
            out.push(b'\n');
        }
    }
    if let Some((line, col)) = context {
        out.extend_from_slice(&line);
        out.push(b'\n');
        let mut marker: Vec<u8> = line[..col.min(line.len())].iter().map(|&c| if c == b'\t' { b'\t' } else { b' ' }).collect();
        marker.extend(std::iter::repeat_n(b' ', col.saturating_sub(line.len())));
        marker.push(b'^');
        out.extend_from_slice(&marker);
        out.push(b'\n');
    }
    emit(channel, data, &out);
}

const ERR_FROM_PARSER: c_int = FROM_PARSER;

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlFormatError(e: *const XmlError, channel: GenericErrorF, data: *mut c_void) {
    if e.is_null() {
        return;
    }
    let Some(c) = channel else { return };
    unsafe { format_error(&*e, c, data) };
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlGetLastError() -> *const XmlError {
    let g = globals();
    if unsafe { (*g).last_error.code } == ERR_OK { null() } else { unsafe { &raw const (*g).last_error } }
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlResetLastError() {
    reset_error(unsafe { &mut (*globals()).last_error });
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlResetError(e: *mut XmlError) {
    if !e.is_null() {
        reset_error(unsafe { &mut *e });
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xmlCopyError(from: *const XmlError, to: *mut XmlError) -> c_int {
    if from.is_null() || to.is_null() {
        return -1;
    }
    copy_error(unsafe { &*from }, unsafe { &mut *to });
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlSetGenericErrorFunc(ctx: *mut c_void, handler: GenericErrorF) {
    let g = globals();
    unsafe {
        (*g).generic_ctx = ctx;
        (*g).generic_error = handler;
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlThrDefSetGenericErrorFunc(ctx: *mut c_void, handler: GenericErrorF) {
    xmlSetGenericErrorFunc(ctx, handler)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn initGenericErrorDefaultFunc(handler: *mut GenericErrorF) {
    let g = globals();
    unsafe { (*g).generic_error = if handler.is_null() { None } else { *handler } };
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlSetStructuredErrorFunc(ctx: *mut c_void, handler: StructuredErrorF) {
    let g = globals();
    unsafe {
        (*g).structured_ctx = ctx;
        (*g).structured = handler;
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlThrDefSetStructuredErrorFunc(ctx: *mut c_void, handler: StructuredErrorF) {
    xmlSetStructuredErrorFunc(ctx, handler)
}

#[unsafe(no_mangle)]
pub extern "C" fn xmlIsCatastrophicError(level: c_int, code: c_int) -> c_int {
    // As libxml2 2.15 has it: a resource limit is not catastrophic.
    (level == LEVEL_FATAL && (matches!(code, ERR_NO_MEMORY | ERR_INTERNAL_ERROR | 115 | 116) || (1500..=1599).contains(&code))) as c_int
}

pub const LEVEL_WARNING: c_int = ERR_WARNING;
pub const LEVEL_ERROR: c_int = ERR_ERROR;
pub const LEVEL_FATAL: c_int = ERR_FATAL;

/// An error message for an error code, as `xmlErrString` gives it.
#[unsafe(no_mangle)]
pub extern "C" fn xmlErrString(code: c_int) -> *const c_char {
    parser::message_for(code).as_ptr()
}

/// The layout of the structs above, for tests/c/libxml2_layout.c: the size
/// of struct `which` and the offsets of its fields, in declaration order.
#[unsafe(no_mangle)]
pub extern "C" fn vxml_libxml2_layout(which: c_int, out: *mut usize, max: c_int) -> c_int {
    let v = layout(which);
    let n = v.len().min(max.max(0) as usize);
    for (i, x) in v.iter().take(n).enumerate() {
        unsafe { *out.add(i) = *x };
    }
    v.len() as c_int
}

macro_rules! offsets {
    ($t:ty; $($f:ident),*) => {
        vec![std::mem::size_of::<$t>(), $(std::mem::offset_of!($t, $f)),*]
    };
}

fn layout(which: c_int) -> Vec<usize> {
    use parser::ParserInput;
    match which {
        0 => offsets!(Ns; next, type_, href, prefix, _private, context),
        1 => offsets!(Node; _private, type_, name, children, last, parent, next, prev, doc, ns, content, properties, nsDef, psvi, line, extra),
        2 => offsets!(Attr; _private, type_, name, children, last, parent, next, prev, doc, ns, atype, psvi, id),
        3 => offsets!(Doc; _private, type_, name, children, last, parent, next, prev, doc, compression, standalone, intSubset, extSubset, oldNs, version, encoding, ids, refs, URL, charset, dict, psvi, parseFlags, properties),
        4 => offsets!(Dtd; _private, type_, name, children, last, parent, next, prev, doc, notations, elements, attributes, entities, ExternalID, SystemID, pentities),
        5 => offsets!(Entity; _private, type_, name, children, last, parent, next, prev, doc, orig, content, length, etype, ExternalID, SystemID, nexte, URI, owner, flags, expandedSize),
        6 => offsets!(ElementDecl; _private, type_, name, children, last, parent, next, prev, doc, etype, content, attributes, prefix, contModel),
        7 => offsets!(AttributeDecl; _private, type_, name, children, last, parent, next, prev, doc, nexth, atype, def, defaultValue, tree, prefix, elem),
        8 => offsets!(ElementContent; type_, ocur, name, c1, c2, parent, prefix),
        9 => offsets!(Enumeration; next, name),
        10 => offsets!(Notation; name, PublicID, SystemID),
        11 => offsets!(Buffer; content, use_, size, alloc, contentIO),
        12 => offsets!(XmlError; domain, code, message, level, file, line, str1, str2, str3, int1, int2, ctxt, node),
        13 => offsets!(SaxHandler; internalSubset, isStandalone, hasInternalSubset, hasExternalSubset, resolveEntity, getEntity, entityDecl, notationDecl, attributeDecl, elementDecl, unparsedEntityDecl, setDocumentLocator, startDocument, endDocument, startElement, endElement, reference, characters, ignorableWhitespace, processingInstruction, comment, warning, error, fatalError, getParameterEntity, cdataBlock, externalSubset, initialized, _private, startElementNs, endElementNs, serror),
        14 => offsets!(ParserInput; buf, filename, directory, base, cur, end, length, line, col, consumed, free, encoding, version, flags, id, parentConsumed, entity),
        15 => parser::ctxt_layout(),
        16 => offsets!(SaxLocator; getPublicId, getSystemId, getLineNumber, getColumnNumber),
        17 => offsets!(Id; next, value, attr, name, lineno, doc),
        _ => vec![],
    }
}
