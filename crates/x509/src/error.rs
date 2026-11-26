//! [`try_parse`]: the verified parser, plus a reason when it rejects.
//!
//! The verdict is always the verified [`crate::cert::parse`]'s. Only when it
//! rejects does an unverified walker retrace the certificate to say where;
//! the walker reads through the verified DER primitives.
use crate::cert::{parse, Certificate};
use crate::der::*;
use crate::ext::{check_extensions, check_known_extension, read_extension};
use crate::time::read_time;
use crate::x509::{alg_id_eq, check_rdns, read_alg_id, read_spki};
use core::fmt;

/// Why a certificate was rejected, and the offset of the TLV at fault.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Error {
    pub kind: ErrorKind,
    pub offset: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorKind {
    /// Not a single DER SEQUENCE spanning the whole input.
    Outer,
    TbsCertificate,
    /// Explicit v1, or a version other than v2 and v3.
    Version,
    Serial,
    SignatureAlgorithm,
    Issuer,
    Validity,
    Subject,
    SubjectPublicKeyInfo,
    /// A unique identifier in a v1 certificate, or a malformed one.
    UniqueId,
    /// Extensions outside v3, an empty list, or a malformed Extension.
    Extensions,
    /// A decoded extension (by its id-ce arc, 2.5.29.x) whose contents are malformed.
    ExtensionContents(u8),
    DuplicateExtension,
    /// signatureAlgorithm differs from the TBSCertificate's signature field.
    AlgorithmMismatch,
    SignatureValue,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?} at offset {}", self.kind, self.offset)
    }
}

impl core::error::Error for Error {}

/// Parses one DER certificate, or says why it is not one.
pub fn try_parse(b: &[u8]) -> Result<Certificate<'_>, Error> {
    match parse(b) {
        Some(c) => Ok(c),
        None => Err(diagnose(b)),
    }
}

fn diagnose(b: &[u8]) -> Error {
    let off = |s: &[u8]| s.as_ptr() as usize - b.as_ptr() as usize;
    let err = |kind, s: &[u8]| Error { kind, offset: off(s) };
    let Some(c) = read_only(b, 0x30) else { return err(ErrorKind::Outer, b) };
    let Some((t, r1)) = read_expect(c, 0x30) else { return err(ErrorKind::TbsCertificate, c) };
    let (ver, s) = match read_expect(t, 0xA0) {
        Some((vc, r)) => match read_only(vc, 2) {
            Some([1]) => (1, r),
            Some([2]) => (2, r),
            _ => return err(ErrorKind::Version, t),
        },
        None => (0, t),
    };
    let Some((serial, s1)) = read_expect(s, 2) else { return err(ErrorKind::Serial, s) };
    if !check_integer(serial) {
        return err(ErrorKind::Serial, s);
    }
    let Some((sa, s2)) = read_expect(s1, 0x30) else { return err(ErrorKind::SignatureAlgorithm, s1) };
    let Some(tbs_alg) = read_alg_id(sa) else { return err(ErrorKind::SignatureAlgorithm, s1) };
    let Some((iss, s3)) = read_expect(s2, 0x30) else { return err(ErrorKind::Issuer, s2) };
    if !check_rdns(iss) {
        return err(ErrorKind::Issuer, s2);
    }
    let validity_ok = read_expect(s3, 0x30).and_then(|(val, s4)| {
        let (a, r) = read_tlv(val)?;
        read_time(a)?;
        read_time(read_only_tlv(r)?)?;
        Some(s4)
    });
    let Some(s4) = validity_ok else { return err(ErrorKind::Validity, s3) };
    let Some((sub, s5)) = read_expect(s4, 0x30) else { return err(ErrorKind::Subject, s4) };
    if !check_rdns(sub) {
        return err(ErrorKind::Subject, s4);
    }
    let Some((pk, mut s)) = read_expect(s5, 0x30) else { return err(ErrorKind::SubjectPublicKeyInfo, s5) };
    if read_spki(pk).is_none() {
        return err(ErrorKind::SubjectPublicKeyInfo, s5);
    }
    for t in [0x81u8, 0x82] {
        if let Some((u, r)) = read_expect(s, t) {
            if ver == 0 || read_bit_string(u).is_none() {
                return err(ErrorKind::UniqueId, s);
            }
            s = r;
        }
    }
    if !s.is_empty() {
        let list = if ver == 2 { read_only(s, 0xA3).and_then(|e| read_only(e, 0x30)) } else { None };
        let Some(all) = list.filter(|l| !l.is_empty()) else { return err(ErrorKind::Extensions, s) };
        let mut l = all;
        while !l.is_empty() {
            let Some((c, r)) = read_expect(l, 0x30) else { return err(ErrorKind::Extensions, l) };
            let Some(x) = read_extension(c) else { return err(ErrorKind::Extensions, l) };
            if !check_known_extension(&x) {
                return err(ErrorKind::ExtensionContents(x.oid[x.oid.len() - 1]), l);
            }
            l = r;
        }
        // Every extension is well-formed, so the verified check fails only
        // on a repeated OID.
        if !check_extensions(all) {
            return err(ErrorKind::DuplicateExtension, first_duplicate(all));
        }
    }
    let Some((a, r2)) = read_expect(r1, 0x30) else { return err(ErrorKind::SignatureAlgorithm, r1) };
    let Some(alg) = read_alg_id(a) else { return err(ErrorKind::SignatureAlgorithm, r1) };
    if !alg_id_eq(&alg, &tbs_alg) {
        return err(ErrorKind::AlgorithmMismatch, r1);
    }
    err(ErrorKind::SignatureValue, r2)
}

/// The first extension in `all`, a list of well-formed extensions, whose OID
/// an earlier one has: found by sorting the OIDs with their offsets.
#[cfg(feature = "alloc")]
fn first_duplicate(all: &[u8]) -> &[u8] {
    let mut v: alloc::vec::Vec<(&[u8], usize)> = alloc::vec::Vec::new();
    let mut l = all;
    while let Some((c, r)) = read_expect(l, 0x30) {
        if let Some(x) = read_extension(c) {
            v.push((x.oid, all.len() - l.len()));
        }
        l = r;
    }
    v.sort_unstable();
    let mut first = all.len();
    for w in v.windows(2) {
        if w[0].0 == w[1].0 {
            first = first.min(w[1].1);
        }
    }
    &all[first..]
}

/// The same without a heap: each extension against those before it.
#[cfg(not(feature = "alloc"))]
fn first_duplicate(all: &[u8]) -> &[u8] {
    let mut l = all;
    while let Some((c, r)) = read_expect(l, 0x30) {
        if let Some(x) = read_extension(c) {
            if seen_before(&all[..all.len() - l.len()], x.oid) {
                return l;
            }
        }
        l = r;
    }
    l
}

/// Whether an extension in `l`, a list of well-formed extensions, has `oid`.
#[cfg(not(feature = "alloc"))]
fn seen_before(mut l: &[u8], oid: &[u8]) -> bool {
    while let Some((c, r)) = read_expect(l, 0x30) {
        if read_extension(c).is_some_and(|x| x.oid == oid) {
            return true;
        }
        l = r;
    }
    false
}
