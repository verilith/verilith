//! `ares_dns_parse` for c-ares, backed by vdns.
//!
//! A thin adapter, not verified, like `capi`. The message is parsed and every
//! record's RDATA decoded by the verified `parse` and `rdata::read_rdata`;
//! this file only copies the results into c-ares's own `ares_dns_record_t`
//! with c-ares's public setters, so callers see exactly the structure
//! c-ares's parser builds. It also applies the c-ares policies that go beyond
//! the RFCs (one question, printable HINFO/NAPTR/URI strings, non-empty
//! trailing fields, the `ARES_DNS_PARSE_*_RAW` flags, extended RCODEs), so
//! that it accepts and rejects what c-ares does except where vdns is stricter
//! (see the differential tests).
//!
//! Writing (`dns_write`) goes the other way: c-ares's record is read with its
//! public getters into `rdata::Rdata`, laid out by the verified
//! `encode::encode_rdata` (proven to decode back to exactly those fields),
//! and serialized by the verified compressing serializer.
//!
//! With the `ares-abi` feature the entry point is exported as
//! `ares_dns_parse`, to be linked into a c-ares built without its own (see
//! `cares/README.md`). Without it, it is `vdns_ares_dns_parse` and needs a
//! c-ares library to link against.
#![allow(unsafe_op_in_unsafe_fn)]
use alloc::vec::Vec;
use crate::message::Section;
use crate::name::Name;
use crate::rdata::{NameBytes, Rdata};
use alloc::ffi::CString;
use core::ffi::{c_char, c_int, c_uchar, c_uint, c_ushort, c_void};

type Rec = c_void;
type Rr = c_void;

const ARES_SUCCESS: c_int = 0;
const ARES_EFORMERR: c_int = 2;
const ARES_EBADRESP: c_int = 10;

const RAW_RR: c_int = 65536;

unsafe extern "C" {
    fn ares_dns_record_create(rec: *mut *mut Rec, id: c_ushort, flags: c_ushort, opcode: c_int, rcode: c_int)
        -> c_int;
    fn ares_dns_record_destroy(rec: *mut Rec);
    fn ares_dns_record_query_add(rec: *mut Rec, name: *const c_char, qtype: c_int, qclass: c_int) -> c_int;
    fn ares_dns_record_rr_prealloc(rec: *mut Rec, sect: c_int, cnt: usize) -> c_int;
    fn ares_dns_record_rr_add(
        rr: *mut *mut Rr,
        rec: *mut Rec,
        sect: c_int,
        name: *const c_char,
        rtype: c_int,
        rclass: c_int,
        ttl: c_uint,
    ) -> c_int;
    fn ares_dns_rr_set_str(rr: *mut Rr, key: c_int, val: *const c_char) -> c_int;
    fn ares_dns_rr_set_u8(rr: *mut Rr, key: c_int, val: c_uchar) -> c_int;
    fn ares_dns_rr_set_u16(rr: *mut Rr, key: c_int, val: c_ushort) -> c_int;
    fn ares_dns_rr_set_u32(rr: *mut Rr, key: c_int, val: c_uint) -> c_int;
    fn ares_dns_rr_set_addr(rr: *mut Rr, key: c_int, addr: *const c_void) -> c_int;
    fn ares_dns_rr_set_addr6(rr: *mut Rr, key: c_int, addr: *const c_void) -> c_int;
    fn ares_dns_rr_set_bin(rr: *mut Rr, key: c_int, val: *const c_uchar, len: usize) -> c_int;
    fn ares_dns_rr_add_abin(rr: *mut Rr, key: c_int, val: *const c_uchar, len: usize) -> c_int;
    fn ares_dns_rr_set_opt(rr: *mut Rr, key: c_int, opt: c_ushort, val: *const c_uchar, len: usize) -> c_int;
}

/// Whether c-ares has a typed decoder for `t` (`ares_dns_rec_type_isvalid`).
fn cares_knows(t: u16) -> bool {
    matches!(
        t,
        1 | 2 | 5 | 6 | 12 | 13 | 15 | 16 | 24 | 28 | 33 | 35 | 41 | 43 | 44 | 46 | 47 | 48 | 50 | 51 | 52 | 64
            | 65 | 255 | 256 | 257
    )
}

/// RFC 1035 types whose RDATA may be compressed (`ares_dns_rec_allow_name_comp`);
/// they are the "base" types of the `ARES_DNS_PARSE_*_BASE_RAW` flags.
fn base_type(t: u16) -> bool {
    matches!(t, 1 | 2 | 5 | 6 | 12 | 13 | 15 | 16)
}

fn printable(s: &[u8]) -> bool {
    s.iter().all(|&c| (0x20..=0x7e).contains(&c))
}

fn opcode_valid(op: u16) -> bool {
    matches!(op, 0 | 1 | 2 | 4 | 5)
}

fn rcode_valid(rc: u16) -> bool {
    matches!(rc, 0..=11 | 16..=23)
}

/// A name as c-ares prints it: escaped, no trailing dot, root as "".
fn cname(wire: &[u8]) -> CString {
    let mut v = Vec::with_capacity(wire.len() + 8);
    Name::from_wire(wire).write_presentation(&mut v);
    // Escaping turns every NUL octet into `\000`.
    CString::new(v).unwrap()
}

fn ctext(s: &[u8]) -> Option<CString> {
    if printable(s) {
        CString::new(s).ok()
    } else {
        None
    }
}

macro_rules! check {
    ($e:expr) => {{
        let st = $e;
        if st != ARES_SUCCESS {
            return st;
        }
    }};
}

unsafe fn set_bin(rr: *mut Rr, key: c_int, v: &[u8]) -> c_int {
    // An empty field is left unset, as c-ares's parser does.
    if v.is_empty() {
        ARES_SUCCESS
    } else {
        ares_dns_rr_set_bin(rr, key, v.as_ptr(), v.len())
    }
}

unsafe fn set_str(rr: *mut Rr, key: c_int, s: &CString) -> c_int {
    ares_dns_rr_set_str(rr, key, s.as_ptr())
}

unsafe fn set_opts(rr: *mut Rr, key: c_int, v: &[(u16, &[u8])]) -> c_int {
    for &(k, val) in v {
        let p = if val.is_empty() { core::ptr::null() } else { val.as_ptr() };
        check!(ares_dns_rr_set_opt(rr, key, k, p, val.len()));
    }
    ARES_SUCCESS
}

unsafe fn set_sig(rr: *mut Rr, t: c_int, f: (u16, u8, u8, u32, u32, u32, u16, &[u8], &[u8])) -> c_int {
    let (covered, alg, labels, ottl, exp, inc, tag, signer, sig) = f;
    if sig.is_empty() {
        return ARES_EBADRESP;
    }
    check!(ares_dns_rr_set_u16(rr, t * 100 + 1, covered));
    check!(ares_dns_rr_set_u8(rr, t * 100 + 2, alg));
    check!(ares_dns_rr_set_u8(rr, t * 100 + 3, labels));
    check!(ares_dns_rr_set_u32(rr, t * 100 + 4, ottl));
    check!(ares_dns_rr_set_u32(rr, t * 100 + 5, exp));
    check!(ares_dns_rr_set_u32(rr, t * 100 + 6, inc));
    check!(ares_dns_rr_set_u16(rr, t * 100 + 7, tag));
    check!(set_str(rr, t * 100 + 8, &cname(signer)));
    set_bin(rr, t * 100 + 9, sig)
}

/// Fills a typed record from vdns's decoded RDATA.
unsafe fn fill(rr: *mut Rr, t: c_int, d: &Rdata) -> c_int {
    let k = |n: c_int| t * 100 + n;
    match d {
        Rdata::A(a) => ares_dns_rr_set_addr(rr, k(1), a.as_ptr() as *const c_void),
        Rdata::Aaaa(a) => ares_dns_rr_set_addr6(rr, k(1), a.as_ptr() as *const c_void),
        Rdata::Ns(n) | Rdata::Cname(n) | Rdata::Ptr(n) => set_str(rr, k(1), &cname(n)),
        Rdata::Mx { preference, exchange } => {
            check!(ares_dns_rr_set_u16(rr, k(1), *preference));
            set_str(rr, k(2), &cname(exchange))
        }
        Rdata::Txt(v) => {
            for s in v {
                check!(ares_dns_rr_add_abin(rr, k(1), s.as_ptr(), s.len()));
            }
            ARES_SUCCESS
        }
        Rdata::Hinfo { cpu, os } => match (ctext(cpu), ctext(os)) {
            (Some(c), Some(o)) => {
                check!(set_str(rr, k(1), &c));
                set_str(rr, k(2), &o)
            }
            _ => ARES_EBADRESP,
        },
        Rdata::Soa { mname, rname, serial, refresh, retry, expire, minimum } => {
            check!(set_str(rr, k(1), &cname(mname)));
            check!(set_str(rr, k(2), &cname(rname)));
            check!(ares_dns_rr_set_u32(rr, k(3), *serial));
            check!(ares_dns_rr_set_u32(rr, k(4), *refresh));
            check!(ares_dns_rr_set_u32(rr, k(5), *retry));
            check!(ares_dns_rr_set_u32(rr, k(6), *expire));
            ares_dns_rr_set_u32(rr, k(7), *minimum)
        }
        Rdata::Sig { type_covered, algorithm, labels, original_ttl, expiration, inception, key_tag, signer, signature }
        | Rdata::Rrsig {
            type_covered,
            algorithm,
            labels,
            original_ttl,
            expiration,
            inception,
            key_tag,
            signer,
            signature,
        } => set_sig(
            rr,
            t,
            (*type_covered, *algorithm, *labels, *original_ttl, *expiration, *inception, *key_tag, signer, signature),
        ),
        Rdata::Srv { priority, weight, port, target } => {
            check!(ares_dns_rr_set_u16(rr, k(2), *priority));
            check!(ares_dns_rr_set_u16(rr, k(3), *weight));
            check!(ares_dns_rr_set_u16(rr, k(4), *port));
            set_str(rr, k(5), &cname(target))
        }
        Rdata::Naptr { order, preference, flags, services, regexp, replacement } => {
            match (ctext(flags), ctext(services), ctext(regexp)) {
                (Some(f), Some(s), Some(r)) => {
                    check!(ares_dns_rr_set_u16(rr, k(1), *order));
                    check!(ares_dns_rr_set_u16(rr, k(2), *preference));
                    check!(set_str(rr, k(3), &f));
                    check!(set_str(rr, k(4), &s));
                    check!(set_str(rr, k(5), &r));
                    set_str(rr, k(6), &cname(replacement))
                }
                _ => ARES_EBADRESP,
            }
        }
        // The OPT header fields are set by the caller.
        Rdata::Opt(v) => set_opts(rr, k(5), v),
        Rdata::Ds { key_tag, algorithm, digest_type, digest } => {
            if digest.is_empty() {
                return ARES_EBADRESP;
            }
            check!(ares_dns_rr_set_u16(rr, k(1), *key_tag));
            check!(ares_dns_rr_set_u8(rr, k(2), *algorithm));
            check!(ares_dns_rr_set_u8(rr, k(3), *digest_type));
            set_bin(rr, k(4), digest)
        }
        Rdata::Sshfp { algorithm, fp_type, fingerprint } => {
            if fingerprint.is_empty() {
                return ARES_EBADRESP;
            }
            check!(ares_dns_rr_set_u8(rr, k(1), *algorithm));
            check!(ares_dns_rr_set_u8(rr, k(2), *fp_type));
            set_bin(rr, k(3), fingerprint)
        }
        Rdata::Nsec { next, type_bitmaps } => {
            if type_bitmaps.is_empty() {
                return ARES_EBADRESP;
            }
            check!(set_str(rr, k(1), &cname(next)));
            set_bin(rr, k(2), type_bitmaps)
        }
        Rdata::Dnskey { flags, protocol, algorithm, public_key } => {
            if public_key.is_empty() {
                return ARES_EBADRESP;
            }
            check!(ares_dns_rr_set_u16(rr, k(1), *flags));
            check!(ares_dns_rr_set_u8(rr, k(2), *protocol));
            check!(ares_dns_rr_set_u8(rr, k(3), *algorithm));
            set_bin(rr, k(4), public_key)
        }
        Rdata::Nsec3 { hash_algorithm, flags, iterations, salt, next_hashed, type_bitmaps } => {
            if next_hashed.is_empty() {
                return ARES_EBADRESP;
            }
            check!(ares_dns_rr_set_u8(rr, k(1), *hash_algorithm));
            check!(ares_dns_rr_set_u8(rr, k(2), *flags));
            check!(ares_dns_rr_set_u16(rr, k(3), *iterations));
            check!(set_bin(rr, k(4), salt));
            check!(set_bin(rr, k(5), next_hashed));
            set_bin(rr, k(6), type_bitmaps)
        }
        Rdata::Nsec3param { hash_algorithm, flags, iterations, salt } => {
            check!(ares_dns_rr_set_u8(rr, k(1), *hash_algorithm));
            check!(ares_dns_rr_set_u8(rr, k(2), *flags));
            check!(ares_dns_rr_set_u16(rr, k(3), *iterations));
            set_bin(rr, k(4), salt)
        }
        Rdata::Tlsa { usage, selector, matching, data } => {
            if data.is_empty() {
                return ARES_EBADRESP;
            }
            check!(ares_dns_rr_set_u8(rr, k(1), *usage));
            check!(ares_dns_rr_set_u8(rr, k(2), *selector));
            check!(ares_dns_rr_set_u8(rr, k(3), *matching));
            set_bin(rr, k(4), data)
        }
        Rdata::Svcb { priority, target, params } | Rdata::Https { priority, target, params } => {
            check!(ares_dns_rr_set_u16(rr, k(1), *priority));
            check!(set_str(rr, k(2), &cname(target)));
            set_opts(rr, k(3), params)
        }
        Rdata::Uri { priority, weight, target } => match ctext(target) {
            Some(s) => {
                check!(ares_dns_rr_set_u16(rr, k(1), *priority));
                check!(ares_dns_rr_set_u16(rr, k(2), *weight));
                set_str(rr, k(3), &s)
            }
            None => ARES_EBADRESP,
        },
        Rdata::Caa { flags, tag, value } => {
            if value.is_empty() {
                return ARES_EBADRESP;
            }
            check!(ares_dns_rr_set_u8(rr, k(1), *flags));
            // The tag is proven alphanumeric, so it is a valid C string.
            check!(set_str(rr, k(2), &CString::new(*tag).unwrap()));
            set_bin(rr, k(3), value)
        }
        Rdata::Unknown(_) => ARES_EBADRESP,
    }
}

const ARES_EBADNAME: c_int = 8;

fn be16(b: &[u8], p: usize) -> Option<usize> {
    Some(((*b.get(p)? as usize) << 8) | *b.get(p + 1)? as usize)
}

/// The end of the name at `p`, read with the verified decoder; with
/// `compress` false, a name containing a pointer is rejected too.
fn name_end(b: &[u8], p: usize, compress: bool) -> Option<usize> {
    if !compress {
        let mut q = p;
        loop {
            let c = *b.get(q)?;
            if c == 0 {
                break;
            }
            if c >= 64 {
                return None;
            }
            q += 1 + c as usize;
        }
    }
    let mut w = Vec::with_capacity(256);
    crate::parse::read_name_into(b, p, &mut w).map(|(e, _)| e)
}

/// Whether the names inside a record's RDATA (at `p`, of type `t`) decode,
/// as c-ares checks them: compression only in the RFC 1035 types and the
/// RFC 3597 §4 exceptions (SIG, SRV, NAPTR).
fn rdata_names_ok(b: &[u8], t: u16, p: usize) -> bool {
    // A name past the end of the buffer means the fixed fields before it
    // ran out first, which c-ares reports as ARES_EBADRESP.
    let at = |off: usize, compress: bool| {
        if p + off >= b.len() {
            Some(0)
        } else {
            name_end(b, p + off, compress)
        }
    };
    match t {
        2 | 5 | 12 => at(0, true).is_some(),
        15 => at(2, true).is_some(),
        6 => at(0, true).and_then(|e| if e == 0 || e >= b.len() { Some(0) } else { name_end(b, e, true) }).is_some(),
        33 => at(6, true).is_some(),
        24 => at(18, true).is_some(),
        46 => at(18, false).is_some(),
        47 => at(0, false).is_some(),
        64 | 65 => at(2, false).is_some(),
        35 => {
            let mut q = p + 4;
            for _ in 0..3 {
                match b.get(q) {
                    Some(&n) => q += 1 + n as usize,
                    None => return true,
                }
            }
            q >= b.len() || name_end(b, q, true).is_some()
        }
        _ => true,
    }
}

/// Walks the message the way c-ares does, using the verified name decoder:
/// `Ok` with the offset just past the last record, or `Err` with c-ares's
/// error code for the first problem in its parsing order (`ARES_EBADNAME`
/// for a name that does not decode, `ARES_EBADRESP` otherwise). This only
/// picks an error code or a length to try; whether a message is accepted,
/// and what it contains, is always decided by the verified parser.
fn walk(b: &[u8]) -> Result<usize, c_int> {
    let bad = ARES_EBADRESP;
    let qd = be16(b, 4).ok_or(bad)?;
    let total = be16(b, 6).ok_or(bad)? + be16(b, 8).ok_or(bad)? + be16(b, 10).ok_or(bad)?;
    if qd != 1 {
        return Err(bad);
    }
    let mut p = name_end(b, 12, true).ok_or(ARES_EBADNAME)? + 4;
    if p > b.len() || total > (b.len() - p) / 11 {
        return Err(bad);
    }
    for _ in 0..total {
        let q = name_end(b, p, true).ok_or(ARES_EBADNAME)?;
        let t = be16(b, q).ok_or(bad)? as u16;
        let rdlen = be16(b, q + 8).ok_or(bad)?;
        p = q + 10;
        if rdlen > b.len() - p {
            return Err(bad);
        }
        if !rdata_names_ok(b, t, p) {
            return Err(ARES_EBADNAME);
        }
        p += rdlen;
    }
    Ok(p)
}

/// Where each record's RDATA lies in the message `b`, in message order. The
/// `ARES_DNS_PARSE_*_RAW` flags keep RDATA exactly as received, compression
/// pointers included, while vdns stores it with names decompressed. Only
/// called on a message vdns parsed, so every step succeeds.
fn rdata_spans(b: &[u8]) -> Vec<(usize, usize)> {
    let qd = be16(b, 4).unwrap_or(0);
    let total = be16(b, 6).unwrap_or(0) + be16(b, 8).unwrap_or(0) + be16(b, 10).unwrap_or(0);
    let mut p = 12;
    for _ in 0..qd {
        p = name_end(b, p, true).unwrap_or(b.len()) + 4;
    }
    let mut v = Vec::with_capacity(total);
    for _ in 0..total {
        let q = name_end(b, p, true).unwrap_or(b.len());
        let rdlen = be16(b, q + 8).unwrap_or(0);
        p = q + 10;
        v.push((p, rdlen));
        p += rdlen;
    }
    v
}

unsafe fn build(b: &[u8], flags: c_uint, out: *mut *mut Rec) -> c_int {
    // c-ares ignores bytes after the last record (RFC 9267 §6 does not
    // require rejecting them), so a message vdns rejects whole is retried
    // without them.
    let (m, b) = match crate::parse(b) {
        Some(m) => (m, b),
        None => match walk(b) {
            Ok(end) if end < b.len() => match crate::parse(&b[..end]) {
                Some(m) => (m, &b[..end]),
                None => return ARES_EBADRESP,
            },
            Ok(_) => return ARES_EBADRESP,
            Err(code) => return code,
        },
    };
    if m.question_count() != 1 {
        return ARES_EBADRESP;
    }
    let sections = [(Section::Answer, 1), (Section::Authority, 2), (Section::Additional, 3)];
    // RFC 6891 §6.1.1: at most one OPT record in the additional section.
    if m.additionals().filter(|r| r.rtype == 41).count() > 1 {
        return ARES_EBADRESP;
    }

    let hdr = m.flags();
    let mut dflags = 0u16;
    for (bit, f) in [(0x8000, 1), (0x400, 2), (0x200, 4), (0x100, 8), (0x80, 16), (0x20, 32), (0x10, 64)] {
        if hdr & bit != 0 {
            dflags |= f;
        }
    }
    let opcode = (hdr >> 11) & 0xf;
    if !opcode_valid(opcode) {
        return ARES_EFORMERR;
    }
    // The extended RCODE: the OPT TTL's top 8 bits above the header's 4,
    // from each OPT record that is decoded rather than kept raw.
    let mut rcode = hdr & 0xf;
    for (s, sect) in sections {
        let ext_raw = flags & (1 << (sect + 2)) != 0;
        for r in m.records(s).filter(|r| r.rtype == 41 && !ext_raw) {
            rcode |= ((r.ttl >> 20) & 0x0FF0) as u16;
        }
    }
    let rcode = if rcode_valid(rcode) { rcode } else { 2 };

    let mut rec = core::ptr::null_mut();
    check!(ares_dns_record_create(&mut rec, m.id(), dflags, opcode as c_int, rcode as c_int));
    let st = fill_record(&m, b, rec, flags, &sections);
    if st != ARES_SUCCESS {
        ares_dns_record_destroy(rec);
        return st;
    }
    *out = rec;
    ARES_SUCCESS
}

unsafe fn fill_record(m: &crate::Message, b: &[u8], rec: *mut Rec, flags: c_uint, sections: &[(Section, c_int)]) -> c_int {
    // Only needed for raw RDATA and for picking an error code.
    let mut spans = if flags & 0x3F != 0 { rdata_spans(b) } else { Vec::new() };
    let mut k = 0;
    let q = m.questions().next().unwrap();
    check!(ares_dns_record_query_add(rec, cname(q.name).as_ptr(), q.qtype as c_int, q.qclass as c_int));
    for &(s, sect) in sections {
        let n = m.record_count(s);
        if n > 0 {
            check!(ares_dns_record_rr_prealloc(rec, sect, n));
        }
        // ARES_DNS_PARSE_{AN,NS,AR}_BASE_RAW are bits 0..2, *_EXT_RAW 3..5.
        let base_raw = flags & (1 << (sect - 1)) != 0;
        let ext_raw = flags & (1 << (sect + 2)) != 0;
        for r in m.records(s) {
            k += 1;
            // `rdata_spans` walks the message outside the proof. On a
            // message vdns parsed it finds every record, so these lookups
            // succeed; if one did not, the call fails with ARES_EBADRESP
            // instead of panicking across the C ABI.
            let span = |spans: &mut Vec<(usize, usize)>| {
                if spans.is_empty() {
                    *spans = rdata_spans(b);
                }
                spans.get(k - 1).copied()
            };
            let raw = !cares_knows(r.rtype) || if base_type(r.rtype) { base_raw } else { ext_raw };
            let t = if raw { RAW_RR } else { r.rtype as c_int };
            if t == 255 {
                return ARES_EBADRESP;
            }
            let opt = t == 41;
            let mut rr = core::ptr::null_mut();
            check!(ares_dns_record_rr_add(
                &mut rr,
                rec,
                sect,
                cname(r.name).as_ptr(),
                t,
                if opt { 1 } else { r.rclass as c_int },
                if opt { 0 } else { r.ttl },
            ));
            if raw {
                check!(ares_dns_rr_set_u16(rr, RAW_RR * 100 + 1, r.rtype));
                let raw_data = match span(&mut spans) {
                    Some((off, len)) => off.checked_add(len).and_then(|end| b.get(off..end)),
                    None => None,
                };
                match raw_data {
                    Some(d) => check!(set_bin(rr, RAW_RR * 100 + 2, d)),
                    None => return ARES_EBADRESP,
                }
                continue;
            }
            if opt {
                check!(ares_dns_rr_set_u16(rr, 4101, r.rclass));
                check!(ares_dns_rr_set_u8(rr, 4103, (r.ttl >> 16) as u8));
                check!(ares_dns_rr_set_u16(rr, 4104, r.ttl as u16));
            }
            match r.data() {
                Some(d) => check!(fill(rr, t, &d)),
                None if span(&mut spans).is_some_and(|(off, _)| !rdata_names_ok(b, r.rtype, off)) => return ARES_EBADNAME,
                None => return ARES_EBADRESP,
            }
        }
    }
    ARES_SUCCESS
}

/// Drop-in for `ares_dns_parse`. With the `ares-abi` feature it is exported
/// under that exact symbol name.
///
/// # Safety
/// `buf` must point to `buf_len` readable bytes and `dnsrec` must be valid
/// for writes, as with c-ares.
#[cfg_attr(feature = "ares-abi", unsafe(export_name = "ares_dns_parse"))]
#[cfg_attr(not(feature = "ares-abi"), unsafe(no_mangle))]
pub unsafe extern "C" fn vdns_ares_dns_parse(
    buf: *const c_uchar,
    buf_len: usize,
    flags: c_uint,
    dnsrec: *mut *mut c_void,
) -> c_int {
    if buf.is_null() || buf_len == 0 || dnsrec.is_null() {
        return ARES_EFORMERR;
    }
    *dnsrec = core::ptr::null_mut();
    // Maximum DNS packet size is 64k, even over TCP.
    if buf_len > 0xFFFF {
        return ARES_EFORMERR;
    }
    build(core::slice::from_raw_parts(buf, buf_len), flags, dnsrec)
}

// ---------------------------------------------------------------------------
// ares_dns_write

const ARES_EBADQUERY: c_int = 7;

unsafe extern "C" {
    fn ares_dns_record_get_id(rec: *const Rec) -> c_ushort;
    fn ares_dns_record_get_flags(rec: *const Rec) -> c_ushort;
    fn ares_dns_record_get_opcode(rec: *const Rec) -> c_int;
    fn ares_dns_record_get_rcode(rec: *const Rec) -> c_int;
    fn ares_dns_record_query_cnt(rec: *const Rec) -> usize;
    fn ares_dns_record_query_get(
        rec: *const Rec,
        idx: usize,
        name: *mut *const c_char,
        qtype: *mut c_int,
        qclass: *mut c_int,
    ) -> c_int;
    fn ares_dns_record_rr_cnt(rec: *const Rec, sect: c_int) -> usize;
    fn ares_dns_record_rr_get_const(rec: *const Rec, sect: c_int, idx: usize) -> *const Rr;
    fn ares_dns_rr_get_name(rr: *const Rr) -> *const c_char;
    fn ares_dns_rr_get_type(rr: *const Rr) -> c_int;
    fn ares_dns_rr_get_class(rr: *const Rr) -> c_int;
    fn ares_dns_rr_get_ttl(rr: *const Rr) -> c_uint;
    fn ares_dns_rr_get_str(rr: *const Rr, key: c_int) -> *const c_char;
    fn ares_dns_rr_get_u8(rr: *const Rr, key: c_int) -> c_uchar;
    fn ares_dns_rr_get_u16(rr: *const Rr, key: c_int) -> c_ushort;
    fn ares_dns_rr_get_u32(rr: *const Rr, key: c_int) -> c_uint;
    fn ares_dns_rr_get_addr(rr: *const Rr, key: c_int) -> *const [u8; 4];
    fn ares_dns_rr_get_addr6(rr: *const Rr, key: c_int) -> *const [u8; 16];
    fn ares_dns_rr_get_bin(rr: *const Rr, key: c_int, len: *mut usize) -> *const c_uchar;
    fn ares_dns_rr_get_abin_cnt(rr: *const Rr, key: c_int) -> usize;
    fn ares_dns_rr_get_abin(rr: *const Rr, key: c_int, idx: usize, len: *mut usize) -> *const c_uchar;
    fn ares_dns_rr_get_opt_cnt(rr: *const Rr, key: c_int) -> usize;
    fn ares_dns_rr_get_opt(rr: *const Rr, key: c_int, idx: usize, val: *mut *const c_uchar, len: *mut usize)
        -> c_ushort;
}

unsafe fn bytes<'a>(p: *const c_uchar, len: usize) -> &'a [u8] {
    if p.is_null() || len == 0 {
        &[]
    } else {
        core::slice::from_raw_parts(p, len)
    }
}

/// `ares_is_hostnamech`.
fn hostnamech(c: u8) -> bool {
    c.is_ascii_alphanumeric() || matches!(c, b'-' | b'.' | b'_' | b'/' | b'*')
}

/// c-ares's rules for a name it writes (`ares_split_dns_name`) beyond what
/// the verified `text::parse_text` checks: a `\` and a digit must be followed
/// by two more digits, and owner and question names (`hostname`) may only
/// hold the characters of `ares_is_hostnamech`, escaped or not.
fn cares_name_ok(s: &[u8], hostname: bool) -> bool {
    let mut i = 0;
    while i < s.len() {
        let mut c = s[i];
        i += 1;
        if c == b'\\' {
            match s.get(i) {
                None => return false,
                Some(d) if d.is_ascii_digit() => match s.get(i..i + 3) {
                    Some(t) if t.iter().all(u8::is_ascii_digit) => {
                        let v = t.iter().fold(0u32, |a, &d| a * 10 + (d - b'0') as u32);
                        if v > 255 {
                            return false;
                        }
                        c = v as u8;
                        i += 3;
                    }
                    _ => return false,
                },
                Some(&d) => {
                    c = d;
                    i += 1;
                }
            }
        }
        if hostname && !hostnamech(c) {
            return false;
        }
    }
    true
}

/// A name c-ares holds in presentation form, in uncompressed wire form,
/// converted by the verified `text::parse_text`.
unsafe fn wire_name(p: *const c_char, hostname: bool) -> Result<Vec<u8>, c_int> {
    if p.is_null() {
        return Err(ARES_EFORMERR);
    }
    let s = core::ffi::CStr::from_ptr(p).to_bytes();
    if !cares_name_ok(s, hostname) {
        return Err(ARES_EBADNAME);
    }
    crate::text::parse_text(s).map(|(v, _)| v).ok_or(ARES_EBADNAME)
}

/// The fields of one record, read with c-ares's getters. Each getter's key
/// is the record type times 100 plus the field number (`ares_dns_rr_key_t`).
struct Get {
    rr: *const Rr,
    t: c_int,
}

impl Get {
    unsafe fn u8(&self, n: c_int) -> u8 {
        ares_dns_rr_get_u8(self.rr, self.t * 100 + n)
    }
    unsafe fn u16(&self, n: c_int) -> u16 {
        ares_dns_rr_get_u16(self.rr, self.t * 100 + n)
    }
    unsafe fn u32(&self, n: c_int) -> u32 {
        ares_dns_rr_get_u32(self.rr, self.t * 100 + n)
    }
    /// A name in RDATA, in uncompressed wire form: the verified serializer
    /// compresses it where RFC 1035 allows.
    unsafe fn name(&self, n: c_int) -> Result<NameBytes<'static>, c_int> {
        wire_name(ares_dns_rr_get_str(self.rr, self.t * 100 + n), false).map(NameBytes::Owned)
    }
    /// A string field; the encoder checks it fits a <character-string>.
    unsafe fn str(&self, n: c_int) -> Result<&'static [u8], c_int> {
        let p = ares_dns_rr_get_str(self.rr, self.t * 100 + n);
        if p.is_null() {
            return Err(ARES_EFORMERR);
        }
        Ok(core::ffi::CStr::from_ptr(p).to_bytes())
    }
    unsafe fn bin(&self, n: c_int) -> (bool, &'static [u8]) {
        let mut len = 0;
        let p = ares_dns_rr_get_bin(self.rr, self.t * 100 + n, &mut len);
        (!p.is_null(), bytes(p, len))
    }
    /// A binary field that c-ares requires to be non-empty.
    unsafe fn nonempty(&self, n: c_int) -> Result<&'static [u8], c_int> {
        match self.bin(n) {
            (_, []) => Err(ARES_EFORMERR),
            (_, v) => Ok(v),
        }
    }
    unsafe fn opts(&self, n: c_int, sorted: bool) -> Vec<(u16, &'static [u8])> {
        let key = self.t * 100 + n;
        let mut v: Vec<(u16, &[u8])> = (0..ares_dns_rr_get_opt_cnt(self.rr, key))
            .map(|i| {
                let (mut p, mut len) = (core::ptr::null(), 0);
                let k = ares_dns_rr_get_opt(self.rr, key, i, &mut p, &mut len);
                (k, bytes(p, len))
            })
            .collect();
        // RFC 9460 §2.2: SvcParamKeys SHALL appear in increasing order. The
        // encoder checks that they do, and refuses a repeated key.
        if sorted {
            v.sort_by_key(|&(k, _)| k);
        }
        v
    }
}

/// The fields of a typed record, as c-ares holds them. Which getter goes
/// into which field is all this adapter decides: the layout is the verified
/// `encode::encode_rdata`'s.
unsafe fn read_fields(rr: *const Rr, t: c_int) -> Result<Rdata<'static>, c_int> {
    let f = Get { rr, t };
    let sig = |f: &Get| -> Result<_, c_int> {
        Ok((f.u16(1), f.u8(2), f.u8(3), f.u32(4), f.u32(5), f.u32(6), f.u16(7), f.name(8)?, f.nonempty(9)?))
    };
    Ok(match t {
        1 => match ares_dns_rr_get_addr(rr, 101).as_ref() {
            Some(a) => Rdata::A(&a[..]),
            None => return Err(ARES_EFORMERR),
        },
        28 => match ares_dns_rr_get_addr6(rr, 2801).as_ref() {
            Some(a) => Rdata::Aaaa(&a[..]),
            None => return Err(ARES_EFORMERR),
        },
        2 => Rdata::Ns(f.name(1)?),
        5 => Rdata::Cname(f.name(1)?),
        12 => Rdata::Ptr(f.name(1)?),
        6 => Rdata::Soa {
            mname: f.name(1)?,
            rname: f.name(2)?,
            serial: f.u32(3),
            refresh: f.u32(4),
            retry: f.u32(5),
            expire: f.u32(6),
            minimum: f.u32(7),
        },
        13 => Rdata::Hinfo { cpu: f.str(1)?, os: f.str(2)? },
        15 => Rdata::Mx { preference: f.u16(1), exchange: f.name(2)? },
        16 => {
            let n = ares_dns_rr_get_abin_cnt(rr, 1601);
            if n == 0 {
                return Err(ARES_EFORMERR);
            }
            let strs: Vec<&'static [u8]> = (0..n)
                .map(|i| {
                    let mut len = 0;
                    bytes(ares_dns_rr_get_abin(rr, 1601, i, &mut len), len)
                })
                .collect();
            // Longer strings are split into 255-octet pieces (verified).
            Rdata::Txt(crate::encode::split_txt(&strs))
        }
        24 => {
            let (type_covered, algorithm, labels, original_ttl, expiration, inception, key_tag, signer, signature) = sig(&f)?;
            Rdata::Sig { type_covered, algorithm, labels, original_ttl, expiration, inception, key_tag, signer, signature }
        }
        46 => {
            let (type_covered, algorithm, labels, original_ttl, expiration, inception, key_tag, signer, signature) = sig(&f)?;
            Rdata::Rrsig { type_covered, algorithm, labels, original_ttl, expiration, inception, key_tag, signer, signature }
        }
        33 => Rdata::Srv { priority: f.u16(2), weight: f.u16(3), port: f.u16(4), target: f.name(5)? },
        35 => Rdata::Naptr {
            order: f.u16(1),
            preference: f.u16(2),
            flags: f.str(3)?,
            services: f.str(4)?,
            regexp: f.str(5)?,
            replacement: f.name(6)?,
        },
        41 => Rdata::Opt(f.opts(5, false)),
        43 => Rdata::Ds { key_tag: f.u16(1), algorithm: f.u8(2), digest_type: f.u8(3), digest: f.nonempty(4)? },
        44 => Rdata::Sshfp { algorithm: f.u8(1), fp_type: f.u8(2), fingerprint: f.nonempty(3)? },
        47 => Rdata::Nsec { next: f.name(1)?, type_bitmaps: f.nonempty(2)? },
        48 => Rdata::Dnskey { flags: f.u16(1), protocol: f.u8(2), algorithm: f.u8(3), public_key: f.nonempty(4)? },
        50 => Rdata::Nsec3 {
            hash_algorithm: f.u8(1),
            flags: f.u8(2),
            iterations: f.u16(3),
            salt: f.bin(4).1,
            next_hashed: f.nonempty(5)?,
            type_bitmaps: f.bin(6).1,
        },
        51 => Rdata::Nsec3param { hash_algorithm: f.u8(1), flags: f.u8(2), iterations: f.u16(3), salt: f.bin(4).1 },
        52 => Rdata::Tlsa { usage: f.u8(1), selector: f.u8(2), matching: f.u8(3), data: f.nonempty(4)? },
        64 => Rdata::Svcb { priority: f.u16(1), target: f.name(2)?, params: f.opts(3, true) },
        65 => Rdata::Https { priority: f.u16(1), target: f.name(2)?, params: f.opts(3, true) },
        256 => Rdata::Uri { priority: f.u16(1), weight: f.u16(2), target: f.str(3)? },
        257 => Rdata::Caa { flags: f.u8(1), tag: f.str(2)?, value: f.nonempty(3)? },
        _ => return Err(ARES_EFORMERR),
    })
}

/// The RDATA of a record, with names uncompressed, and the type to write it
/// under (RAW_RR records carry their own). Typed records are laid out by
/// the verified `encode::encode_rdata`, proven to decode back to exactly
/// the fields read from c-ares; fields that do not fit their encoding (a
/// string over 255 octets, an option over 65535, a CAA tag that is not 1
/// to 15 letters and digits, a repeated SVCB key) are refused.
unsafe fn write_rdata(rr: *const Rr, t: c_int) -> Result<(u16, Vec<u8>), c_int> {
    if t == RAW_RR {
        let rtype = ares_dns_rr_get_u16(rr, RAW_RR * 100 + 1);
        let v = match (Get { rr, t }).bin(2) {
            (false, _) => return Err(ARES_EFORMERR),
            (true, v) => v,
        };
        // Raw RDATA of a type with names in it, as c-ares's parser keeps
        // it, may hold compression pointers into the message it came from.
        // c-ares copies them into the new message, where they point at
        // whatever is at those offsets; vdns refuses them, and RDATA that
        // does not decode as its type.
        if crate::parse::is_compressible(rtype) {
            let mut c = Vec::new();
            if !crate::rdata::canon_into(v, rtype, 0, v.len(), &mut c) || c[..] != v[..] {
                return Err(ARES_EFORMERR);
            }
        }
        return Ok((rtype, v.to_vec()));
    }
    let d = read_fields(rr, t)?;
    match crate::encode::encode_rdata(&d, t as u16) {
        Some((v, _)) => Ok((t as u16, v)),
        None => Err(ARES_EFORMERR),
    }
}

/// The message c-ares's `ares_dns_write_buf` writes for `rec`, written by the
/// verified compressing serializer (`Message::to_bytes_compressed`, proven
/// to parse back to the message it was given). This adapter reads the
/// record with c-ares's public getters and applies c-ares's rules: header
/// flag bits, an extended RCODE needing an OPT record, hostname characters
/// in owner and question names, the field limits of each type, the TTL
/// decrement of cached answers, and the 64 KiB message limit.
///
/// # Safety
/// `rec` must be a valid `ares_dns_record_t`.
pub unsafe fn dns_write(rec: *const c_void, ttl_decrement: c_uint) -> Result<Vec<u8>, c_int> {
    use crate::message::{BuildError, Message};
    let rcode = ares_dns_record_get_rcode(rec) as u32;
    let has_opt = (0..ares_dns_record_rr_cnt(rec, 3))
        .any(|i| ares_dns_rr_get_type(ares_dns_record_rr_get_const(rec, 3, i)) == 41);
    // Extended RCODEs need an OPT record to carry their upper bits; without
    // one, c-ares writes SERVFAIL.
    let rcode_low = if rcode > 15 && !has_opt { 2 } else { (rcode & 0xF) as u16 };
    // The bit layout is verified (RFC 1035 §4.1.1, RFC 4035 §3.2).
    let hdr = crate::encode::header_flags(
        ares_dns_record_get_flags(rec),
        (ares_dns_record_get_opcode(rec) & 0xF) as u16,
        rcode_low,
    );

    let build = |e: BuildError| match e {
        BuildError::BadName => ARES_EBADNAME,
        BuildError::RdataTooLong => ARES_EBADQUERY,
        BuildError::SectionFull | BuildError::BadRdata => ARES_EFORMERR,
    };
    let mut m = Message::new(ares_dns_record_get_id(rec), hdr);
    for i in 0..ares_dns_record_query_cnt(rec) {
        let (mut name, mut qtype, mut qclass) = (core::ptr::null(), 0, 0);
        check_err(ares_dns_record_query_get(rec, i, &mut name, &mut qtype, &mut qclass))?;
        m.add_question(&wire_name(name, true)?, qtype as u16, qclass as u16).map_err(build)?;
    }
    for (s, sect) in [(Section::Answer, 1), (Section::Authority, 2), (Section::Additional, 3)] {
        for i in 0..ares_dns_record_rr_cnt(rec, sect) {
            let rr = ares_dns_record_rr_get_const(rec, sect, i);
            if rr.is_null() {
                return Err(ARES_EFORMERR);
            }
            let name = wire_name(ares_dns_rr_get_name(rr), true)?;
            let t = ares_dns_rr_get_type(rr);
            let (rtype, rdata) = write_rdata(rr, t)?;
            let (class, ttl) = if t == 41 {
                // OPT: the class is the UDP payload size, the TTL the upper
                // RCODE bits, version and flags (RFC 6891 §6.1.3).
                let ttl = crate::encode::opt_ttl(
                    (rcode >> 4 & 0xFF) as u8,
                    ares_dns_rr_get_u8(rr, 4103),
                    ares_dns_rr_get_u16(rr, 4104),
                );
                (ares_dns_rr_get_u16(rr, 4101), ttl)
            } else {
                (ares_dns_rr_get_class(rr) as u16, ares_dns_rr_get_ttl(rr).saturating_sub(ttl_decrement))
            };
            m.add_record(s, &name, rtype, class, ttl, &rdata).map_err(build)?;
        }
    }
    let out = m.to_bytes_compressed();
    // The largest DNS message, even over TCP.
    if out.len() > 65535 {
        return Err(ARES_EBADQUERY);
    }
    Ok(out)
}

fn check_err(st: c_int) -> Result<(), c_int> {
    if st == ARES_SUCCESS {
        Ok(())
    } else {
        Err(st)
    }
}

#[cfg(feature = "ares-abi")]
unsafe extern "C" {
    fn ares_buf_append(buf: *mut c_void, data: *const c_uchar, len: usize) -> c_int;
}

/// Writes `dnsrec` to `buf` for c-ares's `ares_dns_write_buf` (the patch
/// passes the record's private TTL decrement along).
///
/// # Safety
/// `dnsrec` must be a valid `ares_dns_record_t` and `buf` an `ares_buf_t`.
#[cfg(feature = "ares-abi")]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vdns_ares_dns_write_buf(dnsrec: *const c_void, ttl_decrement: c_uint, buf: *mut c_void) -> c_int {
    if dnsrec.is_null() || buf.is_null() {
        return ARES_EFORMERR;
    }
    match dns_write(dnsrec, ttl_decrement) {
        Ok(v) => ares_buf_append(buf, v.as_ptr(), v.len()),
        Err(e) => e,
    }
}
