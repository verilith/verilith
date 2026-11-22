//! C ABI for the mbedTLS drop-in (`mbedtls/vx509_mbedtls.c`).
//!
//! `vx509_parse_crt` runs the verified parser, which decides whether the
//! certificate is accepted. The other functions walk structures inside a
//! certificate it accepted, so they only frame TLVs (through the verified
//! DER readers) and do not check contents again. The adapter is unverified
//! glue that copies these spans into `mbedtls_x509_crt`; see
//! mbedtls/README.md.
#![allow(unsafe_op_in_unsafe_fn)]
use crate::der::*;
use crate::ext::*;
use crate::x509::{Atv, AtvSink};
use crate::mbedtls_err::{diagnose, Stage};
use core::ptr::addr_of_mut;
use core::slice;

#[repr(C)]
#[derive(Clone, Copy)]
pub struct VSpan {
    pub p: *const u8,
    pub len: usize,
}

impl VSpan {
    const EMPTY: VSpan = VSpan { p: core::ptr::null(), len: 0 };
    fn of(s: &[u8]) -> VSpan {
        VSpan { p: s.as_ptr(), len: s.len() }
    }
    unsafe fn get<'a>(&self) -> &'a [u8] {
        if self.p.is_null() { &[] } else { slice::from_raw_parts(self.p, self.len) }
    }
}

#[repr(C)]
pub struct VTime {
    pub year: i32,
    pub mon: i32,
    pub day: i32,
    pub hour: i32,
    pub min: i32,
    pub sec: i32,
}

#[repr(C)]
pub struct VCrt {
    pub raw: VSpan,
    pub tbs: VSpan,
    /// 1, 2 or 3.
    pub version: i32,
    pub serial: VSpan,
    pub sig_oid: VSpan,
    /// 0 when absent.
    pub sig_params_tag: i32,
    pub sig_params: VSpan,
    pub issuer_raw: VSpan,
    pub issuer: VSpan,
    pub subject_raw: VSpan,
    pub subject: VSpan,
    pub valid_from: VTime,
    pub valid_to: VTime,
    pub pk_raw: VSpan,
    /// The SubjectPublicKeyInfo's algorithm OID, its parameters' tag (0
    /// when absent) and contents, and the subjectPublicKey's octets.
    pub pk_oid: VSpan,
    pub pk_params_tag: i32,
    pub pk_params: VSpan,
    pub pk_key: VSpan,
    /// Tag octet, or 0 when absent.
    pub issuer_id_tag: i32,
    /// The BIT STRING contents, unused-bits octet included.
    pub issuer_id: VSpan,
    pub subject_id_tag: i32,
    pub subject_id: VSpan,
    /// The contents of [3] (the SEQUENCE OF Extension TLV), or empty.
    pub v3_ext: VSpan,
    /// The contents of the SEQUENCE OF Extension, or empty.
    pub extensions: VSpan,
    /// The signature BIT STRING's octets after the unused-bits octet.
    pub sig: VSpan,
    /// The issuer's and subject's attributes as the verified check of each
    /// Name read them: `*_n` of them, or more than `NAME_CAP` when only the
    /// first `NAME_CAP` are recorded.
    pub issuer_n: u32,
    pub issuer_atvs: [VAtv; NAME_CAP],
    pub subject_n: u32,
    pub subject_atvs: [VAtv; NAME_CAP],
    /// The extensions as the verified check read and decoded them:
    /// `ext_n` of them, or more than `EXT_CAP` when only the first
    /// `EXT_CAP` are in `exts`.
    pub ext_n: u32,
    pub exts: [VExtOut; EXT_CAP],
    /// The entries of the list-valued extensions in `exts` (see
    /// `VExtOut::item_n`), one extension after another.
    pub items: [VItem; ITEM_CAP],
}

/// One extension and what the verified check decoded from its value
/// (`ext::Decoded`): `kind` is the id-ce arc whose fields are set, or 0.
/// BasicConstraints (19) sets `ca`, `has_len` and `path_len`; KeyUsage (15)
/// sets `a` to the BIT STRING's octets; ExtKeyUsage (37), the alt names (17,
/// 18) and certificatePolicies (32) set `a` to the SEQUENCE's contents, and
/// SubjectKeyIdentifier (14) to its octets; AuthorityKeyIdentifier (35)
/// sets `a`, `b` and `c` to its key identifier, the contents of its
/// GeneralNames and its serial number, each null when absent. Fields that a
/// kind does not set are left unwritten.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct VExtOut {
    pub oid: VSpan,
    pub critical: i32,
    pub value: VSpan,
    pub kind: i32,
    pub ca: i32,
    pub has_len: i32,
    pub path_len: u64,
    pub a: VSpan,
    pub b: VSpan,
    pub c: VSpan,
    /// For ExtKeyUsage, SubjectAltName and certificatePolicies: the list's
    /// entries are `item_n` entries of `VCrt::items` from `item0`, as
    /// `vx509_list_next` would give them, or `NO_ITEMS` when there was no
    /// room.
    pub item0: u32,
    pub item_n: u32,
}

pub const NO_ITEMS: u32 = u32::MAX;

/// How many attributes of each Name, and how many extensions, `VCrt` has
/// room for (`VX509_NAME_CAP` and `VX509_EXT_CAP` in the C adapter).
pub const NAME_CAP: usize = 8;
pub const EXT_CAP: usize = 10;
/// How many list entries `VCrt` has room for (`VX509_ITEM_CAP`).
pub const ITEM_CAP: usize = 24;

/// Writes each attribute the verified check hands over straight into
/// `VCrt`'s array: the first `NAME_CAP` of them, and counts them all.
struct AtvsOut {
    out: *mut VAtv,
    n: usize,
}

impl<'a> AtvSink<'a> for AtvsOut {
    #[inline(always)]
    fn push(&mut self, a: Atv<'a>, merged: bool) {
        if self.n < NAME_CAP {
            // SAFETY: `out` has room for NAME_CAP entries (vx509_parse_crt).
            unsafe {
                self.out.add(self.n).write(VAtv {
                    oid: VSpan::of(a.oid),
                    val_tag: a.value.tag.first().map_or(0, |&t| t as i32),
                    val: VSpan::of(a.value.content),
                    merged: merged as i32,
                });
            }
        }
        self.n += 1;
    }
}

fn opt_span(o: Option<&[u8]>) -> VSpan {
    o.map(VSpan::of).unwrap_or(VSpan::EMPTY)
}

/// The same for extensions: every span is a slice the verified check
/// returned, so it lies inside the certificate.
struct ExtsOut {
    out: *mut VExtOut,
    n: usize,
    items: *mut VItem,
    item_n: usize,
}

impl ExtsOut {
    /// Frames the entries of `list`, the contents of a list the verified
    /// check accepted, into `items`: where they start and how many, or
    /// `NO_ITEMS` when they do not all fit.
    #[inline(always)]
    fn list(&mut self, list: &[u8], kind: i32) -> (u32, u32) {
        let mut r = list;
        let mut k = self.item_n;
        while !r.is_empty() {
            let Some((tag, item, next)) = list_step(r, kind) else { return (0, NO_ITEMS) };
            if k == ITEM_CAP {
                return (0, NO_ITEMS);
            }
            // SAFETY: `items` has room for ITEM_CAP entries (vx509_parse_crt).
            unsafe { self.items.add(k).write(VItem { tag, item: VSpan::of(item) }) };
            k += 1;
            r = next;
        }
        let start = self.item_n;
        self.item_n = k;
        (start as u32, (k - start) as u32)
    }
}

impl<'a> ExtSink<'a> for ExtsOut {
    #[inline(always)]
    fn push(&mut self, e: Extension<'a>, d: Decoded<'a>) {
        if self.n < EXT_CAP {
            // Only the fields the adapter reads for this kind (see VExtOut).
            // SAFETY: `out` has room for EXT_CAP entries (vx509_parse_crt).
            unsafe {
                let o = self.out.add(self.n);
                addr_of_mut!((*o).oid).write(VSpan::of(e.oid));
                addr_of_mut!((*o).critical).write(e.critical as i32);
                addr_of_mut!((*o).value).write(VSpan::of(e.value));
                addr_of_mut!((*o).kind).write(d.kind as i32);
                match d.kind {
                    0 => {}
                    19 => {
                        addr_of_mut!((*o).ca).write(d.ca as i32);
                        addr_of_mut!((*o).has_len).write(d.path_len.is_some() as i32);
                        addr_of_mut!((*o).path_len).write(d.path_len.unwrap_or(0));
                    }
                    35 => {
                        addr_of_mut!((*o).a).write(if d.a_some { VSpan::of(d.a) } else { VSpan::EMPTY });
                        addr_of_mut!((*o).b).write(opt_span(d.b));
                        addr_of_mut!((*o).c).write(opt_span(d.c));
                    }
                    k => {
                        addr_of_mut!((*o).a).write(VSpan::of(d.a));
                        let (item0, item_n) = match k {
                            37 => self.list(d.a, 0),
                            17 => self.list(d.a, 1),
                            32 => self.list(d.a, 2),
                            _ => (0, NO_ITEMS),
                        };
                        addr_of_mut!((*o).item0).write(item0);
                        addr_of_mut!((*o).item_n).write(item_n);
                    }
                }
            }
        }
        self.n += 1;
    }
}

/// What the adapter must do after a rejection: run mbedTLS's own
/// signature-algorithm mapping (stage >= 1) and key parser (stage >= 2) on
/// these spans first, in mbedTLS's order, then report `code`.
#[repr(C)]
pub struct VErr {
    pub code: i32,
    pub stage: i32,
    pub sig_oid: VSpan,
    pub sig_params_tag: i32,
    pub sig_params: VSpan,
    pub spki: VSpan,
}

fn time(t: crate::time::Time) -> VTime {
    VTime { year: t.year as i32, mon: t.month as i32, day: t.day as i32, hour: t.hour as i32, min: t.minute as i32, sec: t.second as i32 }
}

/// Offset of `inner` within `outer` (both from the same input).
fn off(outer: &[u8], inner: &[u8]) -> usize {
    inner.as_ptr() as usize - outer.as_ptr() as usize
}

/// Parses the certificate at the start of `buf` (mbedTLS ignores bytes
/// after it). Returns 0 and fills `out`, or fills `err` with mbedTLS's
/// error and returns its code.
///
/// # Safety
/// `buf` must point to `len` readable bytes; `out` and `err` must be valid.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vx509_parse_crt(buf: *const u8, len: usize, out: *mut VCrt, err: *mut VErr) -> i32 {
    let b = if buf.is_null() { &[][..] } else { slice::from_raw_parts(buf, len) };
    let first = match read_tlv(b) {
        Some((_, rest)) => &b[..b.len() - rest.len()],
        None => b,
    };
    // The verified check writes the attributes and extensions into `out`
    // as it reads them; the adapter reads them only after a 0 return.
    let mut iss_l = AtvsOut { out: addr_of_mut!((*out).issuer_atvs).cast(), n: 0 };
    let mut sub_l = AtvsOut { out: addr_of_mut!((*out).subject_atvs).cast(), n: 0 };
    let mut ext_l = ExtsOut { out: addr_of_mut!((*out).exts).cast(), n: 0, items: addr_of_mut!((*out).items).cast(), item_n: 0 };
    let Some(c) = crate::cert::parse_rec(first, &mut iss_l, &mut sub_l, &mut ext_l) else {
        let d = diagnose(first);
        let span = |(s, l): (usize, usize)| if l == 0 && s == 0 { VSpan::EMPTY } else { VSpan::of(&first[s..s + l]) };
        *err = VErr {
            code: d.code,
            stage: match d.stage { Stage::Early => 0, Stage::AfterSigAlg => 1, Stage::AfterKey => 2 },
            sig_oid: span(d.sig_oid),
            sig_params_tag: d.sig_params.0 as i32,
            sig_params: span((d.sig_params.1, d.sig_params.2)),
            spki: span(d.spki),
        };
        return d.code;
    };
    let t = &c.tbs;
    // The verified parser only accepts minimal DER lengths, so a TLV's
    // header length follows from its contents' length.
    let tlv = |contents: &[u8]| {
        let start = off(first, contents) - hdr_len(contents.len());
        VSpan::of(&first[start..off(first, contents) + contents.len()])
    };
    let (iu_tag, iu) = uid(first, t.issuer_uid.map(|u| u.bytes));
    let (su_tag, su) = uid(first, t.subject_uid.map(|u| u.bytes));
    let (v3, exts) = if t.extensions.is_empty() {
        (VSpan::EMPTY, VSpan::EMPTY)
    } else {
        (tlv(t.extensions), VSpan::of(t.extensions))
    };
    // Field by field through raw pointers (the C struct is uninitialized),
    // and only the records in use: the struct is large and the adapter
    // reads no further than the counts.
    addr_of_mut!((*out).raw).write(VSpan::of(first));
    addr_of_mut!((*out).tbs).write(VSpan::of(c.tbs_der));
    addr_of_mut!((*out).version).write(t.version as i32 + 1);
    addr_of_mut!((*out).serial).write(VSpan::of(t.serial));
    addr_of_mut!((*out).sig_oid).write(VSpan::of(t.signature.oid));
    addr_of_mut!((*out).sig_params_tag).write(t.signature.params.map(|p| p.tag[0] as i32).unwrap_or(0));
    addr_of_mut!((*out).sig_params).write(t.signature.params.map(|p| VSpan::of(p.content)).unwrap_or(VSpan::EMPTY));
    addr_of_mut!((*out).issuer_raw).write(tlv(t.issuer.raw));
    addr_of_mut!((*out).issuer).write(VSpan::of(t.issuer.raw));
    addr_of_mut!((*out).subject_raw).write(tlv(t.subject.raw));
    addr_of_mut!((*out).subject).write(VSpan::of(t.subject.raw));
    addr_of_mut!((*out).valid_from).write(time(t.not_before));
    addr_of_mut!((*out).valid_to).write(time(t.not_after));
    addr_of_mut!((*out).pk_raw).write(VSpan::of(t.spki_der));
    addr_of_mut!((*out).pk_oid).write(VSpan::of(t.spki.alg.oid));
    addr_of_mut!((*out).pk_params_tag).write(t.spki.alg.params.map(|p| p.tag[0] as i32).unwrap_or(0));
    addr_of_mut!((*out).pk_params).write(t.spki.alg.params.map(|p| VSpan::of(p.content)).unwrap_or(VSpan::EMPTY));
    addr_of_mut!((*out).pk_key).write(VSpan::of(t.spki.key));
    addr_of_mut!((*out).issuer_id_tag).write(iu_tag);
    addr_of_mut!((*out).issuer_id).write(iu);
    addr_of_mut!((*out).subject_id_tag).write(su_tag);
    addr_of_mut!((*out).subject_id).write(su);
    addr_of_mut!((*out).v3_ext).write(v3);
    addr_of_mut!((*out).extensions).write(exts);
    addr_of_mut!((*out).sig).write(VSpan::of(c.signature));
    addr_of_mut!((*out).issuer_n).write(iss_l.n.min(NAME_CAP + 1) as u32);
    addr_of_mut!((*out).subject_n).write(sub_l.n.min(NAME_CAP + 1) as u32);
    addr_of_mut!((*out).ext_n).write(ext_l.n.min(EXT_CAP + 1) as u32);
    0
}

/// Identifier plus length octets of a DER TLV with `n` contents octets.
fn hdr_len(n: usize) -> usize {
    match n {
        0..=0x7F => 2,
        0x80..=0xFF => 3,
        0x100..=0xFFFF => 4,
        0x1_0000..=0xFF_FFFF => 5,
        _ => 6,
    }
}

/// A unique identifier: its tag and its whole contents (the unused-bits
/// octet just before the verified bit string's bytes).
fn uid(all: &[u8], bytes: Option<&[u8]>) -> (i32, VSpan) {
    match bytes {
        None => (0, VSpan::EMPTY),
        Some(b) => {
            let start = off(all, b) - 1;
            let n = b.len() + 1;
            (all[start - hdr_len(n)] as i32, VSpan::of(&all[start..start + n]))
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct VAtv {
    pub oid: VSpan,
    pub val_tag: i32,
    pub val: VSpan,
    /// 1 when the next attribute is in the same RDN.
    pub merged: i32,
}

/// Next attribute of a Name. `rdns` starts as the Name's contents and `set`
/// as empty; both advance. Returns 1 with `out` filled, or 0 at the end.
///
/// # Safety
/// The spans must come from `vx509_parse_crt` or earlier calls.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vx509_name_next(rdns: *mut VSpan, set: *mut VSpan, out: *mut VAtv) -> i32 {
    let mut s = (*set).get();
    if s.is_empty() {
        let r = (*rdns).get();
        let Some((c, rest)) = read_expect(r, 0x31) else { return 0 };
        *rdns = VSpan::of(rest);
        s = c;
    }
    let Some((c, rest)) = read_expect(s, 0x30) else { return 0 };
    let Some((oid, v)) = read_expect(c, 0x06) else { return 0 };
    let Some(val) = read_only_tlv(v) else { return 0 };
    *set = VSpan::of(rest);
    *out = VAtv { oid: VSpan::of(oid), val_tag: val.tag[0] as i32, val: VSpan::of(val.content), merged: !rest.is_empty() as i32 };
    1
}

/// Every attribute of a Name at once: fills up to `cap` entries of `out`
/// and returns how many there are (more than `cap` means the caller must
/// use `vx509_name_next`).
///
/// # Safety
/// `rdns` must come from `vx509_parse_crt`; `out` must hold `cap` entries.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vx509_name_atvs(rdns: VSpan, out: *mut VAtv, cap: usize) -> usize {
    let mut r = rdns.get();
    let mut n = 0;
    while let Some((set, rest)) = read_expect(r, 0x31) {
        let mut s = set;
        while let Some((c, next)) = read_expect(s, 0x30) {
            let Some((oid, v)) = read_expect(c, 0x06) else { return n };
            let Some(val) = read_only_tlv(v) else { return n };
            if n < cap {
                *out.add(n) = VAtv { oid: VSpan::of(oid), val_tag: val.tag[0] as i32, val: VSpan::of(val.content), merged: !next.is_empty() as i32 };
            }
            n += 1;
            s = next;
        }
        r = rest;
    }
    n
}

#[repr(C)]
pub struct VExt {
    pub oid: VSpan,
    pub critical: i32,
    pub value: VSpan,
}

/// Next extension of a verified extensions list; 1 or 0 at the end.
///
/// # Safety
/// `rest` must come from `vx509_parse_crt` or earlier calls.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vx509_ext_next(rest: *mut VSpan, out: *mut VExt) -> i32 {
    let Some((c, r)) = read_expect((*rest).get(), 0x30) else { return 0 };
    let Some((oid, x)) = read_expect(c, 0x06) else { return 0 };
    let (critical, x) = match read_expect(x, 0x01) {
        Some((b, x)) => (b.first().is_some_and(|&b| b != 0), x),
        None => (false, x),
    };
    let Some(value) = read_only(x, 0x04) else { return 0 };
    *rest = VSpan::of(r);
    *out = VExt { oid: VSpan::of(oid), critical: critical as i32, value: VSpan::of(value) };
    1
}

/// Every extension at once: fills up to `cap` entries of `out` and
/// returns how many there are (more than `cap` means the caller must use
/// `vx509_ext_next`).
///
/// # Safety
/// `list` must come from `vx509_parse_crt`; `out` must hold `cap` entries.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vx509_ext_all(list: VSpan, out: *mut VExt, cap: usize) -> usize {
    let mut rest = list;
    let mut n = 0;
    let mut e = VExt { oid: VSpan::EMPTY, critical: 0, value: VSpan::EMPTY };
    while vx509_ext_next(&mut rest, &mut e) == 1 {
        if n < cap {
            *out.add(n) = VExt { ..e };
        }
        n += 1;
    }
    n
}

/// BasicConstraints: `ca`, and the path length if present (`has_len`).
///
/// # Safety
/// Pointers must be valid.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vx509_basic_constraints(v: VSpan, ca: *mut i32, has_len: *mut i32, path_len: *mut u64) -> i32 {
    let Some(b) = read_basic_constraints(v.get()) else { return -1 };
    *ca = b.ca as i32;
    *has_len = b.path_len.is_some() as i32;
    *path_len = b.path_len.unwrap_or(0);
    0
}

/// A BIT STRING extension (KeyUsage, nsCertType): its octets.
///
/// # Safety
/// Pointers must be valid.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vx509_bit_string(v: VSpan, bits: *mut VSpan) -> i32 {
    let Some(c) = read_only(v.get(), 0x03) else { return -1 };
    let Some(b) = read_bit_string(c) else { return -1 };
    *bits = VSpan::of(b.bytes);
    0
}

/// The list inside a list-valued extension: `kind` 0 is ExtendedKeyUsage,
/// 1 is SubjectAltName, 2 is certificatePolicies.
///
/// # Safety
/// Pointers must be valid.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vx509_ext_list(v: VSpan, kind: i32, list: *mut VSpan) -> i32 {
    let _ = kind;
    match read_only(v.get(), 0x30) {
        Some(l) => {
            *list = VSpan::of(l);
            0
        }
        None => -1,
    }
}

/// The first entry of a non-empty list (see `vx509_list_next`) and the
/// rest of the list: the entry's tag and contents.
#[inline(always)]
fn list_step(r: &[u8], kind: i32) -> Option<(i32, &[u8], &[u8])> {
    match kind {
        0 => read_expect(r, 0x06).map(|(c, n)| (0x06, c, n)),
        1 => read_tlv(r).map(|(x, n)| (x.tag[0] as i32, x.content, n)),
        _ => read_expect(r, 0x30).and_then(|(c, n)| read_expect(c, 0x06).map(|(o, _)| (0x06, o, n))),
    }
}

/// Next entry of a list from `vx509_ext_list` or `vx509_aki`: an OID
/// (kind 0), a GeneralName as tag and contents (kind 1), or a policy OID
/// (kind 2). Returns 1, or 0 at the end.
///
/// # Safety
/// Pointers must be valid.
#[unsafe(no_mangle)]
#[inline]
pub unsafe extern "C" fn vx509_list_next(rest: *mut VSpan, kind: i32, tag: *mut i32, out: *mut VSpan) -> i32 {
    let r = (*rest).get();
    if r.is_empty() {
        return 0;
    }
    let Some((t, item, next)) = list_step(r, kind) else { return 0 };
    *rest = VSpan::of(next);
    *tag = t;
    *out = VSpan::of(item);
    1
}

#[repr(C)]
pub struct VItem {
    pub tag: i32,
    pub item: VSpan,
}

/// Every entry of a list at once (see `vx509_list_next`): fills up to `cap`
/// entries of `out` and returns how many there are (more than `cap` means
/// the caller must use `vx509_list_next`).
///
/// # Safety
/// `list` must come from `vx509_parse_crt`; `out` must hold `cap` entries.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vx509_list_all(list: VSpan, kind: i32, out: *mut VItem, cap: usize) -> usize {
    let mut rest = list;
    let mut n = 0;
    let mut tag = 0;
    let mut item = VSpan::EMPTY;
    while vx509_list_next(&mut rest, kind, &mut tag, &mut item) == 1 {
        if n < cap {
            out.add(n).write(VItem { tag, item });
        }
        n += 1;
    }
    n
}

/// SubjectKeyIdentifier's octets.
///
/// # Safety
/// Pointers must be valid.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vx509_subject_key_id(v: VSpan, out: *mut VSpan) -> i32 {
    match read_only(v.get(), 0x04) {
        Some(k) => {
            *out = VSpan::of(k);
            0
        }
        None => -1,
    }
}

/// AuthorityKeyIdentifier's parts; each span is null when absent, and
/// `issuer` is the contents of the GeneralNames.
///
/// # Safety
/// Pointers must be valid.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vx509_authority_key_id(v: VSpan, key_id: *mut VSpan, issuer: *mut VSpan, serial: *mut VSpan) -> i32 {
    let Some(a) = read_authority_key_id(v.get()) else { return -1 };
    *key_id = a.key_id.map(VSpan::of).unwrap_or(VSpan::EMPTY);
    *issuer = a.issuer.map(VSpan::of).unwrap_or(VSpan::EMPTY);
    *serial = a.serial.map(VSpan::of).unwrap_or(VSpan::EMPTY);
    0
}
