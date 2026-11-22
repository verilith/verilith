//! The native C API (`include/vx509.h`), behind the `capi` feature.
//!
//! The Rust API with C types: `vx509_cert_parse` fills a caller-provided
//! struct of spans into the input, and the other functions step through
//! names, extensions and lists inside it. Nothing is copied and nothing is
//! allocated, which is what the mbedTLS drop-in (`mbedtls.rs`, which must
//! build mbedTLS's linked structures) cannot avoid.
//!
//! This layer is NOT verified. It is kept mechanical: each function turns
//! its arguments into slices, calls the verified function of the same name,
//! and writes the result out as spans. Every decision about a certificate
//! is made by the verified parser.
#![allow(non_camel_case_types)]
#![allow(clippy::missing_safety_doc)]
#![allow(unsafe_op_in_unsafe_fn)]

use crate::api::OidDisplay;
use crate::cert::{Certificate, Tbs};
use crate::der::Tlv;
use crate::error::ErrorKind;
use crate::iter::*;
use crate::time::Time;
use crate::x509::{AlgId, GeneralName, Name, Spki};
use core::ffi::{c_char, c_int};
use core::fmt::Write;

/// Bytes of the certificate. `p` is null when the field is absent.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct vx509_span {
    pub p: *const u8,
    pub len: usize,
}

const ABSENT: vx509_span = vx509_span { p: core::ptr::null(), len: 0 };

fn span(s: &[u8]) -> vx509_span {
    vx509_span { p: s.as_ptr(), len: s.len() }
}

fn opt(s: Option<&[u8]>) -> vx509_span {
    s.map_or(ABSENT, span)
}

/// # Safety
/// `s` is absent, or `len` readable bytes.
unsafe fn bytes<'a>(s: vx509_span) -> &'a [u8] {
    if s.p.is_null() || s.len == 0 {
        &[]
    } else {
        core::slice::from_raw_parts(s.p, s.len)
    }
}

/// A DER element: its identifier octets and its contents octets.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct vx509_tlv {
    pub tag: vx509_span,
    pub content: vx509_span,
}

fn tlv(t: Tlv) -> vx509_tlv {
    vx509_tlv { tag: span(t.tag), content: span(t.content) }
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct vx509_alg {
    pub oid: vx509_span,
    /// Absent (`tag.p` null) when the AlgorithmIdentifier has no parameters.
    pub params: vx509_tlv,
}

fn alg(a: AlgId) -> vx509_alg {
    vx509_alg { oid: span(a.oid), params: a.params.map_or(vx509_tlv { tag: ABSENT, content: ABSENT }, tlv) }
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct vx509_time {
    pub year: u16,
    pub month: u8,
    pub day: u8,
    pub hour: u8,
    pub minute: u8,
    pub second: u8,
}

fn time(t: Time) -> vx509_time {
    vx509_time { year: t.year, month: t.month, day: t.day, hour: t.hour, minute: t.minute, second: t.second }
}

#[repr(C)]
pub struct vx509_cert {
    pub tbs: vx509_span,
    pub serial: vx509_span,
    pub signature_alg: vx509_alg,
    pub issuer: vx509_span,
    pub subject: vx509_span,
    pub not_before: vx509_time,
    pub not_after: vx509_time,
    pub spki: vx509_span,
    pub public_key_alg: vx509_alg,
    pub public_key: vx509_span,
    pub issuer_uid: vx509_span,
    pub subject_uid: vx509_span,
    pub extensions: vx509_span,
    pub signature: vx509_span,
    /// 1, 2 or 3.
    pub version: u8,
    pub issuer_uid_unused_bits: u8,
    pub subject_uid_unused_bits: u8,
}

fn kind_code(k: ErrorKind) -> c_int {
    match k {
        ErrorKind::Outer => 1,
        ErrorKind::TbsCertificate => 2,
        ErrorKind::Version => 3,
        ErrorKind::Serial => 4,
        ErrorKind::SignatureAlgorithm => 5,
        ErrorKind::Issuer => 6,
        ErrorKind::Validity => 7,
        ErrorKind::Subject => 8,
        ErrorKind::SubjectPublicKeyInfo => 9,
        ErrorKind::UniqueId => 10,
        ErrorKind::Extensions => 11,
        ErrorKind::ExtensionContents(_) => 12,
        ErrorKind::DuplicateExtension => 13,
        ErrorKind::AlgorithmMismatch => 14,
        ErrorKind::SignatureValue => 15,
    }
}

/// Parses one DER certificate. Returns 0 and fills `*out`, or a
/// `VX509_E_*` code, with the offset of the element at fault in
/// `*err_offset`.
///
/// # Safety
/// `der` points to `len` readable bytes; `out` and `err_offset` are null
/// or valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vx509_cert_parse(
    der: *const u8,
    len: usize,
    out: *mut vx509_cert,
    err_offset: *mut usize,
) -> c_int {
    if der.is_null() && len != 0 {
        return -1;
    }
    let b = bytes(vx509_span { p: der, len });
    match crate::cert::parse(b) {
        Some(c) => {
            if !out.is_null() {
                let t = &c.tbs;
                out.write(vx509_cert {
                    tbs: span(c.tbs_der),
                    serial: span(t.serial),
                    signature_alg: alg(t.signature),
                    issuer: span(t.issuer.raw),
                    subject: span(t.subject.raw),
                    not_before: time(t.not_before),
                    not_after: time(t.not_after),
                    spki: span(t.spki_der),
                    public_key_alg: alg(t.spki.alg),
                    public_key: span(t.spki.key),
                    issuer_uid: opt(t.issuer_uid.map(|u| u.bytes)),
                    subject_uid: opt(t.subject_uid.map(|u| u.bytes)),
                    extensions: span(t.extensions),
                    signature: span(c.signature),
                    version: t.version + 1,
                    issuer_uid_unused_bits: t.issuer_uid.map_or(0, |u| u.unused),
                    subject_uid_unused_bits: t.subject_uid.map_or(0, |u| u.unused),
                });
            }
            0
        }
        None => reject(b, err_offset),
    }
}

/// Why the verified parser rejected `b` (the unverified `error::try_parse`).
#[cold]
unsafe fn reject(b: &[u8], err_offset: *mut usize) -> c_int {
    let (code, offset) = match crate::error::try_parse(b) {
        Err(e) => (kind_code(e.kind), e.offset),
        // Not reachable: `try_parse` rejects exactly what `parse` does.
        Ok(_) => (1, 0),
    };
    if !err_offset.is_null() {
        *err_offset = offset;
    }
    code
}

/// Seconds since 1970-01-01T00:00:00Z.
///
/// # Safety
/// `t` is null or points to a `vx509_time`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vx509_time_unix(t: *const vx509_time) -> i64 {
    if t.is_null() {
        return 0;
    }
    let t = &*t;
    Time { year: t.year, month: t.month, day: t.day, hour: t.hour, minute: t.minute, second: t.second }
        .unix_timestamp()
}

/// Steps a cursor: runs `next` on the list at `*list` and leaves the rest
/// of the list there.
macro_rules! step {
    ($list:expr, $new:expr, $out:expr, $conv:expr) => {{
        if $list.is_null() {
            return false;
        }
        let mut it = $new(bytes(*$list));
        match it.next() {
            Some(x) => {
                *$list = span(it.rest);
                if !$out.is_null() {
                    $out.write($conv(x));
                }
                true
            }
            None => false,
        }
    }};
}

/// # Safety
/// For every function below: a span is one this API wrote (a field of a
/// `vx509_cert` or an out-parameter), unchanged or advanced by this API,
/// from a certificate whose bytes are still alive and unchanged. Out
/// pointers are null or valid for writes.
///
/// The next RelativeDistinguishedName of a Name (`cert.issuer`,
/// `cert.subject`, or a directoryName).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vx509_rdn_next(name: *mut vx509_span, rdn: *mut vx509_span) -> bool {
    step!(name, |raw| RdnIter::new(&Name { raw }), rdn, |r: Rdn| span(r.raw))
}

#[repr(C)]
pub struct vx509_atv {
    pub oid: vx509_span,
    pub value: vx509_tlv,
}

/// The next attribute of an RDN.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vx509_atv_next(rdn: *mut vx509_span, out: *mut vx509_atv) -> bool {
    step!(rdn, |raw| AtvIter::new(&Rdn { raw }), out, |a: crate::x509::Atv| vx509_atv {
        oid: span(a.oid),
        value: tlv(a.value)
    })
}

#[repr(C)]
pub struct vx509_ext {
    pub oid: vx509_span,
    /// The contents of the extnValue OCTET STRING.
    pub value: vx509_span,
    pub critical: bool,
}

fn ext(e: crate::ext::Extension) -> vx509_ext {
    vx509_ext { oid: span(e.oid), value: span(e.value), critical: e.critical }
}

/// The next extension of `cert.extensions`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vx509_ext_next(exts: *mut vx509_span, out: *mut vx509_ext) -> bool {
    step!(exts, ExtensionIter::new, out, ext)
}

#[repr(C)]
pub struct vx509_general_name {
    /// The CHOICE's tag number, `VX509_GN_*`.
    pub kind: c_int,
    /// The name's bytes. For a directoryName, a Name for `vx509_rdn_next`;
    /// for an otherName, the contents of its value.
    pub value: vx509_span,
    /// For an otherName only: its type-id OID, and its value's tag.
    pub other_type_id: vx509_span,
    pub other_value_tag: vx509_span,
}

fn general_name(g: GeneralName) -> vx509_general_name {
    let (kind, value) = match g {
        GeneralName::Other { type_id, value } => {
            return vx509_general_name {
                kind: 0,
                value: span(value.content),
                other_type_id: span(type_id),
                other_value_tag: span(value.tag),
            }
        }
        GeneralName::Rfc822(v) => (1, v),
        GeneralName::Dns(v) => (2, v),
        GeneralName::X400(v) => (3, v),
        GeneralName::Directory(n) => (4, n.raw),
        GeneralName::EdiParty(v) => (5, v),
        GeneralName::Uri(v) => (6, v),
        GeneralName::Ip(v) => (7, v),
        GeneralName::Registered(v) => (8, v),
    };
    vx509_general_name { kind, value: span(value), other_type_id: ABSENT, other_value_tag: ABSENT }
}

/// The next name of a GeneralNames list (from `vx509_get_subject_alt_names`,
/// `vx509_get_issuer_alt_names`, or an authority key identifier's issuer).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vx509_general_name_next(names: *mut vx509_span, out: *mut vx509_general_name) -> bool {
    step!(names, GeneralNameIter::new, out, general_name)
}

/// The next base name of a name constraints subtree list.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vx509_subtree_next(subtrees: *mut vx509_span, out: *mut vx509_general_name) -> bool {
    step!(subtrees, SubtreeIter::new, out, general_name)
}

/// The next OID of an extended key usage list.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vx509_oid_next(oids: *mut vx509_span, oid: *mut vx509_span) -> bool {
    step!(oids, OidIter::new, oid, span)
}

/// The next policy identifier of a certificate policies list.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vx509_policy_next(policies: *mut vx509_span, oid: *mut vx509_span) -> bool {
    step!(policies, PolicyIter::new, oid, span)
}

/// A certificate with these extensions, to call the verified extension
/// accessors of `Certificate`, which read nothing else.
unsafe fn with_exts<'a>(cert: *const vx509_cert) -> Option<Certificate<'a>> {
    if cert.is_null() {
        return None;
    }
    let none = AlgId { oid: &[], params: None };
    let t = Time { year: 0, month: 0, day: 0, hour: 0, minute: 0, second: 0 };
    Some(Certificate {
        tbs_der: &[],
        tbs: Tbs {
            version: 2,
            serial: &[],
            signature: none,
            issuer: Name { raw: &[] },
            not_before: t,
            not_after: t,
            subject: Name { raw: &[] },
            spki_der: &[],
            spki: Spki { alg: none, key: &[] },
            issuer_uid: None,
            subject_uid: None,
            extensions: bytes((*cert).extensions),
        },
        signature: &[],
    })
}

/// Writes `v` to `out` if both are there; returns whether `v` is.
unsafe fn put<T>(v: Option<T>, out: *mut T) -> bool {
    match v {
        Some(x) => {
            if !out.is_null() {
                out.write(x);
            }
            true
        }
        None => false,
    }
}

/// The extension with this OID (contents octets), if present.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vx509_ext_find(
    cert: *const vx509_cert,
    oid: *const u8,
    oid_len: usize,
    out: *mut vx509_ext,
) -> bool {
    if oid.is_null() && oid_len != 0 {
        return false;
    }
    let oid = bytes(vx509_span { p: oid, len: oid_len });
    put(with_exts(cert).and_then(|c| c.extension(oid)).map(ext), out)
}

#[repr(C)]
pub struct vx509_basic_constraints {
    pub path_len: u64,
    pub ca: bool,
    pub has_path_len: bool,
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vx509_get_basic_constraints(cert: *const vx509_cert, out: *mut vx509_basic_constraints) -> bool {
    let b = with_exts(cert).and_then(|c| c.basic_constraints());
    put(
        b.map(|b| vx509_basic_constraints {
            path_len: b.path_len.unwrap_or(0),
            ca: b.ca,
            has_path_len: b.path_len.is_some(),
        }),
        out,
    )
}

/// The key usage bits (`VX509_KU_*`).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vx509_get_key_usage(cert: *const vx509_cert, bits: *mut u16) -> bool {
    put(with_exts(cert).and_then(|c| c.key_usage()), bits)
}

/// The extended key usage OIDs, for `vx509_oid_next`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vx509_get_ext_key_usage(cert: *const vx509_cert, oids: *mut vx509_span) -> bool {
    put(with_exts(cert).and_then(|c| c.ext_key_usage()).map(|i| span(i.rest)), oids)
}

/// The certificate policies, for `vx509_policy_next`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vx509_get_certificate_policies(cert: *const vx509_cert, policies: *mut vx509_span) -> bool {
    put(with_exts(cert).and_then(|c| c.certificate_policies()).map(|i| span(i.rest)), policies)
}

/// The subject alternative names, for `vx509_general_name_next`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vx509_get_subject_alt_names(cert: *const vx509_cert, names: *mut vx509_span) -> bool {
    put(with_exts(cert).and_then(|c| c.subject_alt_names()).map(|i| span(i.rest)), names)
}

/// The issuer alternative names, for `vx509_general_name_next`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vx509_get_issuer_alt_names(cert: *const vx509_cert, names: *mut vx509_span) -> bool {
    put(with_exts(cert).and_then(|c| c.issuer_alt_names()).map(|i| span(i.rest)), names)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vx509_get_subject_key_id(cert: *const vx509_cert, id: *mut vx509_span) -> bool {
    put(with_exts(cert).and_then(|c| c.subject_key_id()).map(span), id)
}

/// Each field is absent (`p` null) when the extension leaves it out.
#[repr(C)]
pub struct vx509_authority_key_id {
    pub key_id: vx509_span,
    /// GeneralNames, for `vx509_general_name_next`.
    pub issuer: vx509_span,
    pub serial: vx509_span,
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vx509_get_authority_key_id(cert: *const vx509_cert, out: *mut vx509_authority_key_id) -> bool {
    let a = with_exts(cert).and_then(|c| c.authority_key_id());
    put(a.map(|a| vx509_authority_key_id { key_id: opt(a.key_id), issuer: opt(a.issuer), serial: opt(a.serial) }), out)
}

/// Subtree lists for `vx509_subtree_next`; absent (`p` null) when the
/// extension leaves one out.
#[repr(C)]
pub struct vx509_name_constraints {
    pub permitted: vx509_span,
    pub excluded: vx509_span,
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn vx509_get_name_constraints(cert: *const vx509_cert, out: *mut vx509_name_constraints) -> bool {
    let n = with_exts(cert).and_then(|c| c.name_constraints());
    put(n.map(|n| vx509_name_constraints { permitted: opt(n.permitted), excluded: opt(n.excluded) }), out)
}

/// `fmt::Write` into a C buffer, counting what did not fit.
struct Buf {
    p: *mut u8,
    cap: usize,
    len: usize,
}

impl Write for Buf {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        for &c in s.as_bytes() {
            if self.len < self.cap {
                // SAFETY: `len < cap`, and `p` has room for `cap` bytes.
                unsafe { self.p.add(self.len).write(c) };
            }
            self.len += 1;
        }
        Ok(())
    }
}

/// Writes an OID's dotted-decimal text (`2.5.4.3`) and a NUL to `buf`, as
/// much as fits in `cap` bytes, and returns the length of the whole text
/// (without the NUL), as `snprintf` does.
///
/// # Safety
/// `oid` points to `oid_len` readable bytes and `buf` to `cap` writable
/// ones.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vx509_oid_text(oid: *const u8, oid_len: usize, buf: *mut c_char, cap: usize) -> usize {
    if oid.is_null() && oid_len != 0 {
        return 0;
    }
    let cap = if buf.is_null() { 0 } else { cap };
    let mut b = Buf { p: buf as *mut u8, cap: cap.saturating_sub(1), len: 0 };
    let _ = write!(b, "{}", OidDisplay(bytes(vx509_span { p: oid, len: oid_len })));
    if cap > 0 {
        *b.p.add(b.len.min(cap - 1)) = 0;
    }
    b.len
}
