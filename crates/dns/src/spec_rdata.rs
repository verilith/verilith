//! Specification of typed RDATA (trusted, like `spec`).
//!
//! RDATA is decoded in the context of the whole message `b`, because names
//! inside RDATA may be compressed with pointers into the rest of the message
//! (RFC 1035 §4.1.4, RFC 3597 §4). `start..end` is the record's RDATA. Every
//! type must consume its RDATA exactly (RFC 9267 §5): a decoder that stops
//! short or runs past `end` rejects the record.
use crate::spec::*;
use vstd::prelude::*;

verus! {

pub spec const TYPE_A: u16 = 1;
pub spec const TYPE_NS: u16 = 2;
pub spec const TYPE_CNAME: u16 = 5;
pub spec const TYPE_SOA: u16 = 6;
pub spec const TYPE_PTR: u16 = 12;
pub spec const TYPE_HINFO: u16 = 13;
pub spec const TYPE_SIG: u16 = 24;
pub spec const TYPE_MX: u16 = 15;
pub spec const TYPE_TXT: u16 = 16;
pub spec const TYPE_AAAA: u16 = 28;
pub spec const TYPE_SRV: u16 = 33;
pub spec const TYPE_NAPTR: u16 = 35;
pub spec const TYPE_OPT: u16 = 41;
pub spec const TYPE_DS: u16 = 43;
pub spec const TYPE_SSHFP: u16 = 44;
pub spec const TYPE_RRSIG: u16 = 46;
pub spec const TYPE_NSEC: u16 = 47;
pub spec const TYPE_DNSKEY: u16 = 48;
pub spec const TYPE_NSEC3: u16 = 50;
pub spec const TYPE_NSEC3PARAM: u16 = 51;
pub spec const TYPE_TLSA: u16 = 52;
pub spec const TYPE_SVCB: u16 = 64;
pub spec const TYPE_HTTPS: u16 = 65;
pub spec const TYPE_URI: u16 = 256;
pub spec const TYPE_CAA: u16 = 257;

pub enum SpecRdata {
    /// RFC 1035 §3.4.1: a 4-octet IPv4 address.
    A(Seq<u8>),
    /// RFC 3596 §2.2: a 16-octet IPv6 address.
    Aaaa(Seq<u8>),
    /// NS, CNAME and PTR (RFC 1035 §3.3.11, §3.3.1, §3.3.12): one name.
    Ns(SpecName),
    Cname(SpecName),
    Ptr(SpecName),
    /// RFC 1035 §3.3.9: preference, exchange.
    Mx { preference: u16, exchange: SpecName },
    /// RFC 1035 §3.3.14: one or more character-strings.
    Txt(Seq<Seq<u8>>),
    /// RFC 1035 §3.3.2: CPU and OS character-strings.
    Hinfo { cpu: Seq<u8>, os: Seq<u8> },
    /// RFC 1035 §3.3.13.
    Soa {
        mname: SpecName,
        rname: SpecName,
        serial: u32,
        refresh: u32,
        retry: u32,
        expire: u32,
        minimum: u32,
    },
    /// RFC 2535 §4.1 / RFC 2931: the fixed fields, the signer's name, and the
    /// signature.
    Sig {
        type_covered: u16,
        algorithm: u8,
        labels: u8,
        original_ttl: u32,
        expiration: u32,
        inception: u32,
        key_tag: u16,
        signer: SpecName,
        signature: Seq<u8>,
    },
    /// RFC 2782: priority, weight, port, target.
    Srv { priority: u16, weight: u16, port: u16, target: SpecName },
    /// RFC 3403 §4.1.
    Naptr {
        order: u16,
        preference: u16,
        flags: Seq<u8>,
        services: Seq<u8>,
        regexp: Seq<u8>,
        replacement: SpecName,
    },
    /// RFC 6891 §6.1.2: a sequence of (option code, option data).
    Opt(Seq<(u16, Seq<u8>)>),
    /// RFC 4034 §5.1.
    Ds { key_tag: u16, algorithm: u8, digest_type: u8, digest: Seq<u8> },
    /// RFC 4255 §3.1.
    Sshfp { algorithm: u8, fp_type: u8, fingerprint: Seq<u8> },
    /// RFC 4034 §3.1, with an uncompressed signer's name (§6.2).
    Rrsig {
        type_covered: u16,
        algorithm: u8,
        labels: u8,
        original_ttl: u32,
        expiration: u32,
        inception: u32,
        key_tag: u16,
        signer: SpecName,
        signature: Seq<u8>,
    },
    /// RFC 4034 §4.1: an uncompressed next domain name and the type bit maps.
    Nsec { next: SpecName, type_bitmaps: Seq<u8> },
    /// RFC 4034 §2.1.
    Dnskey { flags: u16, protocol: u8, algorithm: u8, public_key: Seq<u8> },
    /// RFC 5155 §3.2.
    Nsec3 {
        hash_algorithm: u8,
        flags: u8,
        iterations: u16,
        salt: Seq<u8>,
        next_hashed: Seq<u8>,
        type_bitmaps: Seq<u8>,
    },
    /// RFC 5155 §4.2.
    Nsec3param { hash_algorithm: u8, flags: u8, iterations: u16, salt: Seq<u8> },
    /// RFC 6698 §2.1.
    Tlsa { usage: u8, selector: u8, matching: u8, data: Seq<u8> },
    /// RFC 9460 §2.2 (SVCB and HTTPS share the format): priority, an
    /// uncompressed target name, and parameters with strictly increasing keys.
    Svcb { priority: u16, target: SpecName, params: Seq<(u16, Seq<u8>)> },
    Https { priority: u16, target: SpecName, params: Seq<(u16, Seq<u8>)> },
    /// RFC 7553 §4.5: priority, weight, and a non-empty target.
    Uri { priority: u16, weight: u16, target: Seq<u8> },
    /// RFC 8659 §4.1: flags, a tag of 1 to 15 ASCII letters and digits, value.
    Caa { flags: u8, tag: Seq<u8>, value: Seq<u8> },
    /// Any other type, kept as raw bytes (RFC 3597).
    Unknown(Seq<u8>),
}

/// A u16 field that must lie inside the RDATA.
pub open spec fn parse_u16_in(b: Seq<u8>, p: int, end: int) -> Option<(u16, int)> {
    if p + 2 <= end && end <= b.len() {
        parse_u16(b, p)
    } else {
        None
    }
}

pub open spec fn parse_u32_in(b: Seq<u8>, p: int, end: int) -> Option<(u32, int)> {
    if p + 4 <= end && end <= b.len() {
        parse_u32(b, p)
    } else {
        None
    }
}

pub open spec fn parse_u8_in(b: Seq<u8>, p: int, end: int) -> Option<(u8, int)> {
    if 0 <= p && p + 1 <= end && end <= b.len() {
        Some((b[p], p + 1))
    } else {
        None
    }
}

/// A (possibly compressed) name whose in-place bytes lie inside the RDATA.
pub open spec fn parse_name_in(b: Seq<u8>, p: int, end: int) -> Option<(SpecName, int)> {
    match parse_name(b, p) {
        Some((n, e)) => if e <= end {
            Some((n, e))
        } else {
            None
        },
        None => None,
    }
}

/// The labels of an uncompressed name inside the RDATA.
pub open spec fn parse_plain_labels(b: Seq<u8>, p: int, end: int) -> Option<(SpecName, int)>
    decreases end - p,
{
    if p < 0 || p >= end || end > b.len() {
        None
    } else if b[p] == 0 {
        Some((Seq::empty(), p + 1))
    } else if b[p] >= 64 {
        // Pointers (and the reserved label types) are not allowed.
        None
    } else if p + 1 + b[p] as int > end {
        None
    } else {
        let l = b.subrange(p + 1, p + 1 + b[p] as int);
        match parse_plain_labels(b, p + 1 + b[p] as int, end) {
            Some((rest, e)) => Some((seq![l] + rest, e)),
            None => None,
        }
    }
}

/// An uncompressed name inside the RDATA, at most 255 octets.
pub open spec fn parse_plain_name(b: Seq<u8>, p: int, end: int) -> Option<(SpecName, int)> {
    match parse_plain_labels(b, p, end) {
        Some((n, e)) => if ser_name(n).len() <= MAX_NAME_WIRE_LEN {
            Some((n, e))
        } else {
            None
        },
        None => None,
    }
}

/// RFC 1035 §3.3: a length octet followed by that many octets.
pub open spec fn parse_cstring(b: Seq<u8>, p: int, end: int) -> Option<(Seq<u8>, int)> {
    if 0 <= p && p < end && end <= b.len() && p + 1 + b[p] as int <= end {
        Some((b.subrange(p + 1, p + 1 + b[p] as int), p + 1 + b[p] as int))
    } else {
        None
    }
}

/// Character-strings up to exactly `end`.
pub open spec fn parse_cstrings(b: Seq<u8>, p: int, end: int) -> Option<Seq<Seq<u8>>>
    decreases end - p,
{
    if p == end && end <= b.len() {
        Some(Seq::empty())
    } else {
        match parse_cstring(b, p, end) {
            Some((s, p2)) => match parse_cstrings(b, p2, end) {
                Some(rest) => Some(seq![s] + rest),
                None => None,
            },
            None => None,
        }
    }
}

/// A (u16 key, u16 length, value) item, as in EDNS options and SVCB
/// parameters.
pub open spec fn parse_kv(b: Seq<u8>, p: int, end: int) -> Option<((u16, Seq<u8>), int)> {
    match parse_u16_in(b, p, end) {
        Some((k, p2)) => match parse_u16_in(b, p2, end) {
            Some((len, p3)) => if p3 + len as int <= end {
                Some(((k, b.subrange(p3, p3 + len as int)), p3 + len as int))
            } else {
                None
            },
            None => None,
        },
        None => None,
    }
}

/// Key/value items up to exactly `end`. With `increasing`, each key must be
/// strictly greater than `prev` and the one before it (RFC 9460 §2.2); `prev`
/// is -1 before the first item.
pub open spec fn parse_kvs(b: Seq<u8>, p: int, end: int, increasing: bool, prev: int) -> Option<
    Seq<(u16, Seq<u8>)>,
>
    decreases end - p,
{
    if p == end && end <= b.len() {
        Some(Seq::empty())
    } else {
        match parse_kv(b, p, end) {
            Some((kv, p2)) => if increasing && kv.0 as int <= prev {
                None
            } else {
                match parse_kvs(b, p2, end, increasing, kv.0 as int) {
                    Some(rest) => Some(seq![kv] + rest),
                    None => None,
                }
            },
            None => None,
        }
    }
}

pub open spec fn is_alnum(c: u8) -> bool {
    (48 <= c <= 57) || (65 <= c <= 90) || (97 <= c <= 122)
}

/// A name that must end exactly at `end`.
pub open spec fn parse_name_exact(b: Seq<u8>, p: int, end: int) -> Option<SpecName> {
    match parse_name_in(b, p, end) {
        Some((n, e)) => if e == end {
            Some(n)
        } else {
            None
        },
        None => None,
    }
}

/// SVCB / HTTPS RDATA, as (priority, target, params).
pub open spec fn parse_svcb(b: Seq<u8>, start: int, end: int) -> Option<
    (u16, SpecName, Seq<(u16, Seq<u8>)>),
> {
    match parse_u16_in(b, start, end) {
        Some((prio, p1)) => match parse_plain_name(b, p1, end) {
            Some((target, p2)) => match parse_kvs(b, p2, end, true, -1) {
                Some(params) => Some((prio, target, params)),
                None => None,
            },
            None => None,
        },
        None => None,
    }
}

pub open spec fn parse_mx(b: Seq<u8>, start: int, end: int) -> Option<SpecRdata> {
        match parse_u16_in(b, start, end) {
            Some((preference, p1)) => match parse_name_exact(b, p1, end) {
                Some(exchange) => Some(SpecRdata::Mx { preference, exchange }),
                None => None,
            },
            None => None,
        }
    }

pub open spec fn parse_txt(b: Seq<u8>, start: int, end: int) -> Option<SpecRdata> {
        match parse_cstrings(b, start, end) {
            Some(s) => if s.len() > 0 {
                Some(SpecRdata::Txt(s))
            } else {
                None
            },
            None => None,
        }
    }

pub open spec fn parse_hinfo(b: Seq<u8>, start: int, end: int) -> Option<SpecRdata> {
        match parse_cstring(b, start, end) {
            Some((cpu, p1)) => match parse_cstring(b, p1, end) {
                Some((os, p2)) => if p2 == end {
                    Some(SpecRdata::Hinfo { cpu, os })
                } else {
                    None
                },
                None => None,
            },
            None => None,
        }
    }

pub open spec fn parse_soa(b: Seq<u8>, start: int, end: int) -> Option<SpecRdata> {
        match parse_name_in(b, start, end) {
            Some((mname, p1)) => match parse_name_in(b, p1, end) {
                Some((rname, p2)) => if end - p2 == 20 {
                    Some(
                        SpecRdata::Soa {
                            mname,
                            rname,
                            serial: parse_u32(b, p2).unwrap().0,
                            refresh: parse_u32(b, p2 + 4).unwrap().0,
                            retry: parse_u32(b, p2 + 8).unwrap().0,
                            expire: parse_u32(b, p2 + 12).unwrap().0,
                            minimum: parse_u32(b, p2 + 16).unwrap().0,
                        },
                    )
                } else {
                    None
                },
                None => None,
            },
            None => None,
        }
    }

pub open spec fn parse_srv(b: Seq<u8>, start: int, end: int) -> Option<SpecRdata> {
        if end - start >= 6 {
            match parse_name_exact(b, start + 6, end) {
                Some(target) => Some(
                    SpecRdata::Srv {
                        priority: parse_u16(b, start).unwrap().0,
                        weight: parse_u16(b, start + 2).unwrap().0,
                        port: parse_u16(b, start + 4).unwrap().0,
                        target,
                    },
                ),
                None => None,
            }
        } else {
            None
        }
    }

pub open spec fn parse_naptr(b: Seq<u8>, start: int, end: int) -> Option<SpecRdata> {
        if end - start >= 4 {
            match parse_cstring(b, start + 4, end) {
                Some((flags, p1)) => match parse_cstring(b, p1, end) {
                    Some((services, p2)) => match parse_cstring(b, p2, end) {
                        Some((regexp, p3)) => match parse_name_exact(b, p3, end) {
                            Some(replacement) => Some(
                                SpecRdata::Naptr {
                                    order: parse_u16(b, start).unwrap().0,
                                    preference: parse_u16(b, start + 2).unwrap().0,
                                    flags,
                                    services,
                                    regexp,
                                    replacement,
                                },
                            ),
                            None => None,
                        },
                        None => None,
                    },
                    None => None,
                },
                None => None,
            }
        } else {
            None
        }
    }

pub open spec fn parse_tlsa(b: Seq<u8>, start: int, end: int) -> Option<SpecRdata> {
        if end - start >= 3 {
            Some(
                SpecRdata::Tlsa {
                    usage: b[start],
                    selector: b[start + 1],
                    matching: b[start + 2],
                    data: b.subrange(start + 3, end),
                },
            )
        } else {
            None
        }
    }

pub open spec fn parse_uri(b: Seq<u8>, start: int, end: int) -> Option<SpecRdata> {
        if end - start >= 5 {
            Some(
                SpecRdata::Uri {
                    priority: parse_u16(b, start).unwrap().0,
                    weight: parse_u16(b, start + 2).unwrap().0,
                    target: b.subrange(start + 4, end),
                },
            )
        } else {
            None
        }
    }

pub open spec fn parse_caa(b: Seq<u8>, start: int, end: int) -> Option<SpecRdata> {
        if end - start >= 2 {
            let len = b[start + 1] as int;
            if 1 <= len <= 15 && start + 2 + len <= end && (forall|i: int|
                start + 2 <= i < start + 2 + len ==> is_alnum(#[trigger] b[i])) {
                Some(
                    SpecRdata::Caa {
                        flags: b[start],
                        tag: b.subrange(start + 2, start + 2 + len),
                        value: b.subrange(start + 2 + len, end),
                    },
                )
            } else {
                None
            }
        } else {
            None
        }
    }

pub open spec fn parse_sig(b: Seq<u8>, start: int, end: int) -> Option<SpecRdata> {
    if end - start >= 18 {
        match parse_name_in(b, start + 18, end) {
            Some((signer, p)) => Some(
                SpecRdata::Sig {
                    type_covered: parse_u16(b, start).unwrap().0,
                    algorithm: b[start + 2],
                    labels: b[start + 3],
                    original_ttl: parse_u32(b, start + 4).unwrap().0,
                    expiration: parse_u32(b, start + 8).unwrap().0,
                    inception: parse_u32(b, start + 12).unwrap().0,
                    key_tag: parse_u16(b, start + 16).unwrap().0,
                    signer,
                    signature: b.subrange(p, end),
                },
            ),
            None => None,
        }
    } else {
        None
    }
}

pub open spec fn parse_ds(b: Seq<u8>, start: int, end: int) -> Option<SpecRdata> {
    if end - start >= 4 {
        Some(
            SpecRdata::Ds {
                key_tag: parse_u16(b, start).unwrap().0,
                algorithm: b[start + 2],
                digest_type: b[start + 3],
                digest: b.subrange(start + 4, end),
            },
        )
    } else {
        None
    }
}

pub open spec fn parse_sshfp(b: Seq<u8>, start: int, end: int) -> Option<SpecRdata> {
    if end - start >= 2 {
        Some(
            SpecRdata::Sshfp {
                algorithm: b[start],
                fp_type: b[start + 1],
                fingerprint: b.subrange(start + 2, end),
            },
        )
    } else {
        None
    }
}

pub open spec fn parse_rrsig(b: Seq<u8>, start: int, end: int) -> Option<SpecRdata> {
    if end - start >= 18 {
        match parse_plain_name(b, start + 18, end) {
            Some((signer, p)) => Some(
                SpecRdata::Rrsig {
                    type_covered: parse_u16(b, start).unwrap().0,
                    algorithm: b[start + 2],
                    labels: b[start + 3],
                    original_ttl: parse_u32(b, start + 4).unwrap().0,
                    expiration: parse_u32(b, start + 8).unwrap().0,
                    inception: parse_u32(b, start + 12).unwrap().0,
                    key_tag: parse_u16(b, start + 16).unwrap().0,
                    signer,
                    signature: b.subrange(p, end),
                },
            ),
            None => None,
        }
    } else {
        None
    }
}

pub open spec fn parse_nsec(b: Seq<u8>, start: int, end: int) -> Option<SpecRdata> {
    match parse_plain_name(b, start, end) {
        Some((next, p)) => Some(SpecRdata::Nsec { next, type_bitmaps: b.subrange(p, end) }),
        None => None,
    }
}

pub open spec fn parse_dnskey(b: Seq<u8>, start: int, end: int) -> Option<SpecRdata> {
    if end - start >= 4 {
        Some(
            SpecRdata::Dnskey {
                flags: parse_u16(b, start).unwrap().0,
                protocol: b[start + 2],
                algorithm: b[start + 3],
                public_key: b.subrange(start + 4, end),
            },
        )
    } else {
        None
    }
}

pub open spec fn parse_nsec3(b: Seq<u8>, start: int, end: int) -> Option<SpecRdata> {
    if end - start >= 4 {
        match parse_cstring(b, start + 4, end) {
            Some((salt, p)) => match parse_cstring(b, p, end) {
                Some((next_hashed, q)) => Some(
                    SpecRdata::Nsec3 {
                        hash_algorithm: b[start],
                        flags: b[start + 1],
                        iterations: parse_u16(b, start + 2).unwrap().0,
                        salt,
                        next_hashed,
                        type_bitmaps: b.subrange(q, end),
                    },
                ),
                None => None,
            },
            None => None,
        }
    } else {
        None
    }
}

pub open spec fn parse_nsec3param(b: Seq<u8>, start: int, end: int) -> Option<SpecRdata> {
    if end - start >= 4 {
        match parse_cstring(b, start + 4, end) {
            Some((salt, p)) => if p == end {
                Some(
                    SpecRdata::Nsec3param {
                        hash_algorithm: b[start],
                        flags: b[start + 1],
                        iterations: parse_u16(b, start + 2).unwrap().0,
                        salt,
                    },
                )
            } else {
                None
            },
            None => None,
        }
    } else {
        None
    }
}

/// Typed RDATA of type `rtype` in `b[start..end]`.
pub open spec fn parse_rdata(b: Seq<u8>, rtype: u16, start: int, end: int) -> Option<SpecRdata> {
    if !(0 <= start <= end <= b.len()) {
        None
    } else if rtype == TYPE_A {
        if end - start == 4 {
            Some(SpecRdata::A(b.subrange(start, end)))
        } else {
            None
        }
    } else if rtype == TYPE_AAAA {
        if end - start == 16 {
            Some(SpecRdata::Aaaa(b.subrange(start, end)))
        } else {
            None
        }
    } else if rtype == TYPE_NS {
        match parse_name_exact(b, start, end) {
            Some(n) => Some(SpecRdata::Ns(n)),
            None => None,
        }
    } else if rtype == TYPE_CNAME {
        match parse_name_exact(b, start, end) {
            Some(n) => Some(SpecRdata::Cname(n)),
            None => None,
        }
    } else if rtype == TYPE_PTR {
        match parse_name_exact(b, start, end) {
            Some(n) => Some(SpecRdata::Ptr(n)),
            None => None,
        }
    } else if rtype == TYPE_MX {
        parse_mx(b, start, end)
    } else if rtype == TYPE_TXT {
        parse_txt(b, start, end)
    } else if rtype == TYPE_HINFO {
        parse_hinfo(b, start, end)
    } else if rtype == TYPE_SOA {
        parse_soa(b, start, end)
    } else if rtype == TYPE_SIG {
        parse_sig(b, start, end)
    } else if rtype == TYPE_SRV {
        parse_srv(b, start, end)
    } else if rtype == TYPE_NAPTR {
        parse_naptr(b, start, end)
    } else if rtype == TYPE_OPT {
        match parse_kvs(b, start, end, false, -1) {
            Some(opts) => Some(SpecRdata::Opt(opts)),
            None => None,
        }
    } else if rtype == TYPE_DS {
        parse_ds(b, start, end)
    } else if rtype == TYPE_SSHFP {
        parse_sshfp(b, start, end)
    } else if rtype == TYPE_RRSIG {
        parse_rrsig(b, start, end)
    } else if rtype == TYPE_NSEC {
        parse_nsec(b, start, end)
    } else if rtype == TYPE_DNSKEY {
        parse_dnskey(b, start, end)
    } else if rtype == TYPE_NSEC3 {
        parse_nsec3(b, start, end)
    } else if rtype == TYPE_NSEC3PARAM {
        parse_nsec3param(b, start, end)
    } else if rtype == TYPE_TLSA {
        parse_tlsa(b, start, end)
    } else if rtype == TYPE_SVCB {
        match parse_svcb(b, start, end) {
            Some((priority, target, params)) => Some(SpecRdata::Svcb { priority, target, params }),
            None => None,
        }
    } else if rtype == TYPE_HTTPS {
        match parse_svcb(b, start, end) {
            Some((priority, target, params)) => Some(SpecRdata::Https { priority, target, params }),
            None => None,
        }
    } else if rtype == TYPE_URI {
        parse_uri(b, start, end)
    } else if rtype == TYPE_CAA {
        parse_caa(b, start, end)
    } else {
        Some(SpecRdata::Unknown(b.subrange(start, end)))
    }
}

// ---------------------------------------------------------------------------
// Canonical RDATA
// ---------------------------------------------------------------------------

/// The types whose RDATA may hold compressed names, as `parse_rdata`
/// decodes them: NS, CNAME, SOA, PTR and MX (RFC 1035; RFC 3597 §4), and
/// SIG, SRV and NAPTR, whose names receivers decompress (RFC 3597 §4). In
/// every other type `parse_rdata` reads names only uncompressed.
pub open spec fn compressible(t: u16) -> bool {
    t == TYPE_NS || t == TYPE_CNAME || t == TYPE_SOA || t == TYPE_PTR || t == TYPE_MX || t
        == TYPE_SIG || t == TYPE_SRV || t == TYPE_NAPTR
}

/// The RDATA `b[start..end]` with every name inside it decompressed: the
/// names replaced by their uncompressed wire form and every other byte
/// kept. The result means the same thing wherever it is placed, while the
/// original may point into the rest of its message. Defined exactly when
/// `parse_rdata` accepts a compressible type; other types are kept as they
/// are.
pub open spec fn canon_names(b: Seq<u8>, t: u16, start: int, end: int) -> Option<Seq<u8>> {
    if !(0 <= start <= end <= b.len()) {
        None
    } else if t == TYPE_NS || t == TYPE_CNAME || t == TYPE_PTR {
        match parse_name_exact(b, start, end) {
            Some(n) => Some(ser_name(n)),
            None => None,
        }
    } else if t == TYPE_MX || t == TYPE_SRV {
        let k: int = if t == TYPE_MX { 2 } else { 6 };
        if end - start >= k {
            match parse_name_exact(b, start + k, end) {
                Some(n) => Some(b.subrange(start, start + k) + ser_name(n)),
                None => None,
            }
        } else {
            None
        }
    } else if t == TYPE_SOA {
        match parse_name_in(b, start, end) {
            Some((n1, p1)) => match parse_name_in(b, p1, end) {
                Some((n2, p2)) => if end - p2 == 20 {
                    Some(ser_name(n1) + ser_name(n2) + b.subrange(p2, end))
                } else {
                    None
                },
                None => None,
            },
            None => None,
        }
    } else if t == TYPE_SIG {
        if end - start >= 18 {
            match parse_name_in(b, start + 18, end) {
                Some((n, p)) => Some(b.subrange(start, start + 18) + ser_name(n) + b.subrange(p, end)),
                None => None,
            }
        } else {
            None
        }
    } else if t == TYPE_NAPTR {
        if end - start >= 4 {
            match parse_cstring(b, start + 4, end) {
                Some((_, p1)) => match parse_cstring(b, p1, end) {
                    Some((_, p2)) => match parse_cstring(b, p2, end) {
                        Some((_, p3)) => match parse_name_exact(b, p3, end) {
                            Some(n) => Some(b.subrange(start, p3) + ser_name(n)),
                            None => None,
                        },
                        None => None,
                    },
                    None => None,
                },
                None => None,
            }
        } else {
            None
        }
    } else {
        Some(b.subrange(start, end))
    }
}

/// The canonical RDATA a record holds: `canon_names`, if it still fits the
/// 16-bit RDLENGTH.
pub open spec fn canon_rdata(b: Seq<u8>, t: u16, start: int, end: int) -> Option<Seq<u8>> {
    match canon_names(b, t, start, end) {
        Some(c) => if c.len() <= u16::MAX {
            Some(c)
        } else {
            None
        },
        None => None,
    }
}

} // verus!
