//! Verified typed RDATA decoding: computes exactly `spec_rdata::parse_rdata`.
use alloc::vec::Vec;
#[allow(unused_imports)]
use crate::lemmas::*;
use crate::message::RecordRef;
#[cfg(verus_only)]
use crate::message::{is_prefix, lemma_prefix_append, lemma_prefix_refl, lemma_prefix_trans};
use crate::parse::{append, read_name_into, read_u16, read_u32};
use crate::spec::*;
#[allow(unused_imports)]
use crate::spec_rdata::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// A name in uncompressed wire form. It borrows from the RDATA when it is
/// stored there uncompressed, which is always the case for a parsed
/// record's (canonical) RDATA, and is owned only when it had to be
/// decompressed.
pub enum NameBytes<'a> {
    Borrowed(&'a [u8]),
    Owned(Vec<u8>),
}

impl<'a> View for NameBytes<'a> {
    type V = Seq<u8>;

    open spec fn view(&self) -> Seq<u8> {
        match self {
            NameBytes::Borrowed(s) => s@,
            NameBytes::Owned(v) => v@,
        }
    }
}

/// An uncompressed name is decoded the same way with or without
/// compression allowed.
proof fn lemma_plain_is_name(b: Seq<u8>, p: int, end: int, n: SpecName, e: int)
    requires
        end <= b.len(),
        parse_plain_name(b, p, end) == Some((n, e)),
        p < e <= end,
        b.subrange(p, e) == ser_name(n),
        valid_name(n),
    ensures
        parse_name_in(b, p, end) == Some((n, e)),
{
    let q = p + ser_labels(n).len();
    assert(ser_name(n) == ser_labels(n) + seq![0u8]);
    assert(at(b, p, ser_labels(n) + seq![0u8]));
    lemma_at_split(b, p, ser_labels(n), seq![0u8]);
    crate::compress::lemma_root_end(b, q, p);
    crate::compress::lemma_literal_run(b, p, p, n, Seq::empty(), q + 1);
    assert(n + Seq::<Seq<u8>>::empty() =~= n);
}

/// Decoded RDATA. Names are in uncompressed wire form (see `Name`); other
/// variable-length fields borrow from the message.
pub enum Rdata<'a> {
    A(&'a [u8]),
    Aaaa(&'a [u8]),
    Ns(NameBytes<'a>),
    Cname(NameBytes<'a>),
    Ptr(NameBytes<'a>),
    Mx { preference: u16, exchange: NameBytes<'a> },
    Txt(Vec<&'a [u8]>),
    Hinfo { cpu: &'a [u8], os: &'a [u8] },
    Soa {
        mname: NameBytes<'a>,
        rname: NameBytes<'a>,
        serial: u32,
        refresh: u32,
        retry: u32,
        expire: u32,
        minimum: u32,
    },
    Sig {
        type_covered: u16,
        algorithm: u8,
        labels: u8,
        original_ttl: u32,
        expiration: u32,
        inception: u32,
        key_tag: u16,
        signer: NameBytes<'a>,
        signature: &'a [u8],
    },
    Ds { key_tag: u16, algorithm: u8, digest_type: u8, digest: &'a [u8] },
    Sshfp { algorithm: u8, fp_type: u8, fingerprint: &'a [u8] },
    Rrsig {
        type_covered: u16,
        algorithm: u8,
        labels: u8,
        original_ttl: u32,
        expiration: u32,
        inception: u32,
        key_tag: u16,
        signer: NameBytes<'a>,
        signature: &'a [u8],
    },
    Nsec { next: NameBytes<'a>, type_bitmaps: &'a [u8] },
    Dnskey { flags: u16, protocol: u8, algorithm: u8, public_key: &'a [u8] },
    Nsec3 {
        hash_algorithm: u8,
        flags: u8,
        iterations: u16,
        salt: &'a [u8],
        next_hashed: &'a [u8],
        type_bitmaps: &'a [u8],
    },
    Nsec3param { hash_algorithm: u8, flags: u8, iterations: u16, salt: &'a [u8] },
    Srv { priority: u16, weight: u16, port: u16, target: NameBytes<'a> },
    Naptr {
        order: u16,
        preference: u16,
        flags: &'a [u8],
        services: &'a [u8],
        regexp: &'a [u8],
        replacement: NameBytes<'a>,
    },
    Opt(Vec<(u16, &'a [u8])>),
    Tlsa { usage: u8, selector: u8, matching: u8, data: &'a [u8] },
    Svcb { priority: u16, target: NameBytes<'a>, params: Vec<(u16, &'a [u8])> },
    Https { priority: u16, target: NameBytes<'a>, params: Vec<(u16, &'a [u8])> },
    Uri { priority: u16, weight: u16, target: &'a [u8] },
    Caa { flags: u8, tag: &'a [u8], value: &'a [u8] },
    Unknown(&'a [u8]),
}

pub open spec fn strs_view(v: Seq<&[u8]>) -> Seq<Seq<u8>> {
    v.map_values(|x: &[u8]| x@)
}

pub open spec fn kvs_view(v: Seq<(u16, &[u8])>) -> Seq<(u16, Seq<u8>)> {
    v.map_values(|kv: (u16, &[u8])| (kv.0, kv.1@))
}

/// `r` is the exec form of `s`: names are their uncompressed wire form.
pub open spec fn rdata_is(r: Rdata, s: SpecRdata) -> bool {
    match (r, s) {
        (Rdata::A(x), SpecRdata::A(y)) => x@ == y,
        (Rdata::Aaaa(x), SpecRdata::Aaaa(y)) => x@ == y,
        (Rdata::Ns(x), SpecRdata::Ns(y)) => x@ == ser_name(y),
        (Rdata::Cname(x), SpecRdata::Cname(y)) => x@ == ser_name(y),
        (Rdata::Ptr(x), SpecRdata::Ptr(y)) => x@ == ser_name(y),
        (
            Rdata::Mx { preference: p, exchange: x },
            SpecRdata::Mx { preference: q, exchange: y },
        ) => p == q && x@ == ser_name(y),
        (Rdata::Txt(x), SpecRdata::Txt(y)) => strs_view(x@) == y,
        (Rdata::Hinfo { cpu: c, os: o }, SpecRdata::Hinfo { cpu: c2, os: o2 }) => c@ == c2 && o@
            == o2,
        (
            Rdata::Soa { mname, rname, serial, refresh, retry, expire, minimum },
            SpecRdata::Soa {
                mname: m2,
                rname: r2,
                serial: s2,
                refresh: f2,
                retry: t2,
                expire: e2,
                minimum: n2,
            },
        ) => mname@ == ser_name(m2) && rname@ == ser_name(r2) && serial == s2 && refresh == f2
            && retry == t2 && expire == e2 && minimum == n2,
        (
            Rdata::Sig {
                type_covered,
                algorithm,
                labels,
                original_ttl,
                expiration,
                inception,
                key_tag,
                signer,
                signature,
            },
            SpecRdata::Sig {
                type_covered: a,
                algorithm: b,
                labels: c,
                original_ttl: d,
                expiration: e,
                inception: f,
                key_tag: g,
                signer: h,
                signature: i,
            },
        ) => type_covered == a && algorithm == b && labels == c && original_ttl == d && expiration
            == e && inception == f && key_tag == g && signer@ == ser_name(h) && signature@ == i,
        (
            Rdata::Rrsig {
                type_covered,
                algorithm,
                labels,
                original_ttl,
                expiration,
                inception,
                key_tag,
                signer,
                signature,
            },
            SpecRdata::Rrsig {
                type_covered: a,
                algorithm: b,
                labels: c,
                original_ttl: d,
                expiration: e,
                inception: f,
                key_tag: g,
                signer: h,
                signature: i,
            },
        ) => type_covered == a && algorithm == b && labels == c && original_ttl == d && expiration
            == e && inception == f && key_tag == g && signer@ == ser_name(h) && signature@ == i,
        (
            Rdata::Ds { key_tag, algorithm, digest_type, digest },
            SpecRdata::Ds { key_tag: a, algorithm: b, digest_type: c, digest: d },
        ) => key_tag == a && algorithm == b && digest_type == c && digest@ == d,
        (
            Rdata::Sshfp { algorithm, fp_type, fingerprint },
            SpecRdata::Sshfp { algorithm: a, fp_type: b, fingerprint: c },
        ) => algorithm == a && fp_type == b && fingerprint@ == c,
        (
            Rdata::Nsec { next, type_bitmaps },
            SpecRdata::Nsec { next: a, type_bitmaps: b },
        ) => next@ == ser_name(a) && type_bitmaps@ == b,
        (
            Rdata::Dnskey { flags, protocol, algorithm, public_key },
            SpecRdata::Dnskey { flags: a, protocol: b, algorithm: c, public_key: d },
        ) => flags == a && protocol == b && algorithm == c && public_key@ == d,
        (
            Rdata::Nsec3 { hash_algorithm, flags, iterations, salt, next_hashed, type_bitmaps },
            SpecRdata::Nsec3 {
                hash_algorithm: a,
                flags: b,
                iterations: c,
                salt: d,
                next_hashed: e,
                type_bitmaps: f,
            },
        ) => hash_algorithm == a && flags == b && iterations == c && salt@ == d && next_hashed@ == e
            && type_bitmaps@ == f,
        (
            Rdata::Nsec3param { hash_algorithm, flags, iterations, salt },
            SpecRdata::Nsec3param { hash_algorithm: a, flags: b, iterations: c, salt: d },
        ) => hash_algorithm == a && flags == b && iterations == c && salt@ == d,
        (
            Rdata::Srv { priority, weight, port, target },
            SpecRdata::Srv { priority: p2, weight: w2, port: o2, target: t2 },
        ) => priority == p2 && weight == w2 && port == o2 && target@ == ser_name(t2),
        (
            Rdata::Naptr { order, preference, flags, services, regexp, replacement },
            SpecRdata::Naptr {
                order: o2,
                preference: p2,
                flags: f2,
                services: s2,
                regexp: r2,
                replacement: n2,
            },
        ) => order == o2 && preference == p2 && flags@ == f2 && services@ == s2 && regexp@ == r2
            && replacement@ == ser_name(n2),
        (Rdata::Opt(x), SpecRdata::Opt(y)) => kvs_view(x@) == y,
        (
            Rdata::Tlsa { usage, selector, matching, data },
            SpecRdata::Tlsa { usage: u2, selector: s2, matching: m2, data: d2 },
        ) => usage == u2 && selector == s2 && matching == m2 && data@ == d2,
        (
            Rdata::Svcb { priority, target, params },
            SpecRdata::Svcb { priority: p2, target: t2, params: q2 },
        ) => priority == p2 && target@ == ser_name(t2) && kvs_view(params@) == q2,
        (
            Rdata::Https { priority, target, params },
            SpecRdata::Https { priority: p2, target: t2, params: q2 },
        ) => priority == p2 && target@ == ser_name(t2) && kvs_view(params@) == q2,
        (
            Rdata::Uri { priority, weight, target },
            SpecRdata::Uri { priority: p2, weight: w2, target: t2 },
        ) => priority == p2 && weight == w2 && target@ == t2,
        (
            Rdata::Caa { flags, tag, value },
            SpecRdata::Caa { flags: f2, tag: t2, value: v2 },
        ) => flags == f2 && tag@ == t2 && value@ == v2,
        (Rdata::Unknown(x), SpecRdata::Unknown(y)) => x@ == y,
        _ => false,
    }
}

fn read_u16_in(b: &[u8], p: usize, end: usize) -> (r: Option<(u16, usize)>)
    requires
        end <= b@.len(),
    ensures
        r matches Some((x, q)) ==> parse_u16_in(b@, p as int, end as int) == Some((x, q as int)),
        r is None ==> parse_u16_in(b@, p as int, end as int) is None,
{
    if p > end || end - p < 2 {
        None
    } else {
        read_u16(b, p)
    }
}


/// Decodes a (possibly compressed) name whose in-place bytes end by `end`.
/// An uncompressed name is borrowed, not copied.
fn read_name_in<'a>(b: &'a [u8], p: usize, end: usize) -> (r: Option<(NameBytes<'a>, usize, Ghost<SpecName>)>)
    requires
        end <= b@.len(),
    ensures
        r matches Some((v, e, n)) ==> {
            &&& parse_name_in(b@, p as int, end as int) == Some((n@, e as int))
            &&& v@ == ser_name(n@)
            &&& e <= end
        },
        r is None ==> parse_name_in(b@, p as int, end as int) is None,
{
    if let Some((e, n)) = plain_name_end(b, p, end) {
        proof {
            lemma_plain_is_name(b@, p as int, end as int, n@, e as int);
        }
        return Some((NameBytes::Borrowed(slice_subrange(b, p, e)), e, n));
    }
    let mut v: Vec<u8> = Vec::new();
    match read_name_into(b, p, &mut v) {
        Some((e, n)) => {
            if e > end {
                return None;
            }
            proof {
                assert(v@ =~= ser_name(n@));
            }
            Some((NameBytes::Owned(v), e, n))
        },
        None => None,
    }
}

fn read_name_exact<'a>(b: &'a [u8], p: usize, end: usize) -> (r: Option<(NameBytes<'a>, Ghost<SpecName>)>)
    requires
        end <= b@.len(),
    ensures
        r matches Some((v, n)) ==> {
            &&& parse_name_exact(b@, p as int, end as int) == Some(n@)
            &&& v@ == ser_name(n@)
        },
        r is None ==> parse_name_exact(b@, p as int, end as int) is None,
{
    match read_name_in(b, p, end) {
        Some((v, e, n)) => if e == end {
            Some((v, n))
        } else {
            None
        },
        None => None,
    }
}

/// Decodes an uncompressed name inside `b[p..end]`, borrowing it.
fn read_plain_name<'a>(b: &'a [u8], p: usize, end: usize) -> (r: Option<
    (NameBytes<'a>, usize, Ghost<SpecName>),
>)
    requires
        end <= b@.len(),
    ensures
        r matches Some((v, e, n)) ==> {
            &&& parse_plain_name(b@, p as int, end as int) == Some((n@, e as int))
            &&& v@ == ser_name(n@)
            &&& e <= end
        },
        r is None ==> parse_plain_name(b@, p as int, end as int) is None,
{
    match plain_name_end(b, p, end) {
        Some((e, n)) => Some((NameBytes::Borrowed(slice_subrange(b, p, e)), e, n)),
        None => None,
    }
}

/// Finds the end of the uncompressed name at `b[p..]` (within `end`),
/// without copying it.
pub fn plain_name_end(b: &[u8], p: usize, end: usize) -> (r: Option<(usize, Ghost<SpecName>)>)
    requires
        end <= b@.len(),
    ensures
        r matches Some((e, n)) ==> {
            &&& parse_plain_name(b@, p as int, end as int) == Some((n@, e as int))
            &&& p < e <= end
            &&& b@.subrange(p as int, e as int) == ser_name(n@)
            &&& valid_name(n@)
        },
        r is None ==> parse_plain_name(b@, p as int, end as int) is None,
{
    let ghost mut run: SpecName = Seq::empty();
    let mut q = p;
    if p >= end {
        return None;
    }
    proof {
        assert(ser_labels(run) =~= Seq::<u8>::empty());
        assert(b@.subrange(p as int, p as int) =~= ser_labels(run));
        if let Some((rest, e)) = parse_plain_labels(b@, p as int, end as int) {
            assert(run + rest =~= rest);
        }
    }
    while q < end
        invariant
            p <= q <= end <= b@.len(),
            b@.subrange(p as int, q as int) == ser_labels(run),
            forall|i: int| 0 <= i < run.len() ==> valid_label(#[trigger] run[i]),
            parse_plain_labels(b@, p as int, end as int) == match parse_plain_labels(
                b@,
                q as int,
                end as int,
            ) {
                Some((rest, e)) => Some((run + rest, e)),
                None => None,
            },
        decreases end - q,
    {
        let c = b[q];
        if c == 0 {
            proof {
                assert(run + Seq::<Seq<u8>>::empty() =~= run);
                assert(b@.subrange(p as int, q + 1) =~= b@.subrange(p as int, q as int)
                    + seq![0u8]);
            }
            if q + 1 - p > 255 {
                return None;
            }
            return Some((q + 1, Ghost(run)));
        }
        if c >= 64 {
            return None;
        }
        let len = c as usize;
        if len > end - (q + 1) {
            return None;
        }
        let ghost l = b@.subrange(q + 1, q + 1 + len);
        proof {
            assert(b@.subrange(q as int, q + 1 + len) =~= ser_label(l));
            lemma_ser_labels_push(run, l);
            assert(b@.subrange(p as int, q + 1 + len) =~= b@.subrange(p as int, q as int)
                + b@.subrange(q as int, q + 1 + len));
            if let Some((rest, e)) = parse_plain_labels(b@, (q + 1 + len) as int, end as int) {
                assert(run + (seq![l] + rest) =~= run.push(l) + rest);
            }
            assert(valid_label(l));
            run = run.push(l);
        }
        q = q + 1 + len;
    }
    None
}

fn read_cstring<'a>(b: &'a [u8], p: usize, end: usize) -> (r: Option<(&'a [u8], usize)>)
    requires
        end <= b@.len(),
    ensures
        r matches Some((s, q)) ==> parse_cstring(b@, p as int, end as int) == Some((s@, q as int)),
        r is None ==> parse_cstring(b@, p as int, end as int) is None,
{
    if p >= end {
        return None;
    }
    let len = b[p] as usize;
    if len > end - (p + 1) {
        return None;
    }
    Some((slice_subrange(b, p + 1, p + 1 + len), p + 1 + len))
}

fn read_cstrings<'a>(b: &'a [u8], p: usize, end: usize) -> (r: Option<Vec<&'a [u8]>>)
    requires
        p <= end <= b@.len(),
    ensures
        r matches Some(v) ==> parse_cstrings(b@, p as int, end as int) == Some(strs_view(v@)),
        r is None ==> parse_cstrings(b@, p as int, end as int) is None,
{
    let mut v: Vec<&'a [u8]> = Vec::new();
    let mut q = p;
    proof {
        assert(strs_view(v@) =~= Seq::<Seq<u8>>::empty());
        if let Some(rest) = parse_cstrings(b@, p as int, end as int) {
            assert(strs_view(v@) + rest =~= rest);
        }
    }
    while q < end
        invariant
            p <= q <= end <= b@.len(),
            parse_cstrings(b@, p as int, end as int) == match parse_cstrings(
                b@,
                q as int,
                end as int,
            ) {
                Some(rest) => Some(strs_view(v@) + rest),
                None => None,
            },
        decreases end - q,
    {
        let (s, q2) = match read_cstring(b, q, end) {
            Some(x) => x,
            None => return None,
        };
        let ghost v0 = v@;
        v.push(s);
        proof {
            assert(strs_view(v@) =~= strs_view(v0).push(s@));
            if let Some(rest) = parse_cstrings(b@, q2 as int, end as int) {
                assert(strs_view(v0) + (seq![s@] + rest) =~= strs_view(v@) + rest);
            }
        }
        q = q2;
    }
    proof {
        assert(strs_view(v@) + Seq::<Seq<u8>>::empty() =~= strs_view(v@));
    }
    Some(v)
}

fn read_kvs<'a>(b: &'a [u8], p: usize, end: usize, increasing: bool) -> (r: Option<
    Vec<(u16, &'a [u8])>,
>)
    requires
        p <= end <= b@.len(),
    ensures
        r matches Some(v) ==> parse_kvs(b@, p as int, end as int, increasing, -1) == Some(
            kvs_view(v@),
        ),
        r is None ==> parse_kvs(b@, p as int, end as int, increasing, -1) is None,
{
    let mut v: Vec<(u16, &'a [u8])> = Vec::new();
    let mut q = p;
    let mut prev: i32 = -1;
    proof {
        assert(kvs_view(v@) =~= Seq::<(u16, Seq<u8>)>::empty());
        if let Some(rest) = parse_kvs(b@, p as int, end as int, increasing, -1) {
            assert(kvs_view(v@) + rest =~= rest);
        }
    }
    while q < end
        invariant
            p <= q <= end <= b@.len(),
            -1 <= prev <= 0xffff,
            parse_kvs(b@, p as int, end as int, increasing, -1) == match parse_kvs(
                b@,
                q as int,
                end as int,
                increasing,
                prev as int,
            ) {
                Some(rest) => Some(kvs_view(v@) + rest),
                None => None,
            },
        decreases end - q,
    {
        let (k, q2) = match read_u16_in(b, q, end) {
            Some(x) => x,
            None => return None,
        };
        let (len, q3) = match read_u16_in(b, q2, end) {
            Some(x) => x,
            None => return None,
        };
        if len as usize > end - q3 {
            return None;
        }
        if increasing && (k as i32) <= prev {
            return None;
        }
        let val = slice_subrange(b, q3, q3 + len as usize);
        let ghost v0 = v@;
        v.push((k, val));
        proof {
            assert(kvs_view(v@) =~= kvs_view(v0).push((k, val@)));
            if let Some(rest) = parse_kvs(
                b@,
                (q3 + len as usize) as int,
                end as int,
                increasing,
                k as int,
            ) {
                assert(kvs_view(v0) + (seq![(k, val@)] + rest) =~= kvs_view(v@) + rest);
            }
        }
        prev = k as i32;
        q = q3 + len as usize;
    }
    proof {
        assert(kvs_view(v@) + Seq::<(u16, Seq<u8>)>::empty() =~= kvs_view(v@));
    }
    Some(v)
}

fn read_svcb<'a>(b: &'a [u8], start: usize, end: usize) -> (r: Option<
    (u16, NameBytes<'a>, Vec<(u16, &'a [u8])>, Ghost<SpecName>),
>)
    requires
        start <= end <= b@.len(),
    ensures
        r matches Some((prio, t, params, n)) ==> {
            &&& parse_svcb(b@, start as int, end as int) == Some((prio, n@, kvs_view(params@)))
            &&& t@ == ser_name(n@)
        },
        r is None ==> parse_svcb(b@, start as int, end as int) is None,
{
    let (prio, p1) = match read_u16_in(b, start, end) {
        Some(x) => x,
        None => return None,
    };
    let (t, p2, n) = match read_plain_name(b, p1, end) {
        Some(x) => x,
        None => return None,
    };
    let params = match read_kvs(b, p2, end, true) {
        Some(x) => x,
        None => return None,
    };
    Some((prio, t, params, n))
}

fn read_sig<'a>(b: &'a [u8], start: usize, end: usize) -> (r: Option<Rdata<'a>>)
    requires
        start <= end <= b@.len(),
    ensures
        r matches Some(x) ==> parse_sig(b@, start as int, end as int) matches Some(s) && rdata_is(x, s),
        r is None ==> parse_sig(b@, start as int, end as int) is None,
{
    if end - start < 18 {
        return None;
    }
    match read_name_in(b, start + 18, end) {
        Some((signer, p, n)) => Some(
            Rdata::Sig {
                type_covered: read_u16(b, start).unwrap().0,
                algorithm: b[start + 2],
                labels: b[start + 3],
                original_ttl: read_u32(b, start + 4).unwrap().0,
                expiration: read_u32(b, start + 8).unwrap().0,
                inception: read_u32(b, start + 12).unwrap().0,
                key_tag: read_u16(b, start + 16).unwrap().0,
                signer,
                signature: slice_subrange(b, p, end),
            },
        ),
        None => None,
    }
}

fn read_rrsig<'a>(b: &'a [u8], start: usize, end: usize) -> (r: Option<Rdata<'a>>)
    requires
        start <= end <= b@.len(),
    ensures
        r matches Some(x) ==> parse_rrsig(b@, start as int, end as int) matches Some(s) && rdata_is(x, s),
        r is None ==> parse_rrsig(b@, start as int, end as int) is None,
{
    if end - start < 18 {
        return None;
    }
    match read_plain_name(b, start + 18, end) {
        Some((signer, p, n)) => Some(
            Rdata::Rrsig {
                type_covered: read_u16(b, start).unwrap().0,
                algorithm: b[start + 2],
                labels: b[start + 3],
                original_ttl: read_u32(b, start + 4).unwrap().0,
                expiration: read_u32(b, start + 8).unwrap().0,
                inception: read_u32(b, start + 12).unwrap().0,
                key_tag: read_u16(b, start + 16).unwrap().0,
                signer,
                signature: slice_subrange(b, p, end),
            },
        ),
        None => None,
    }
}

fn read_ds<'a>(b: &'a [u8], start: usize, end: usize) -> (r: Option<Rdata<'a>>)
    requires
        start <= end <= b@.len(),
    ensures
        r matches Some(x) ==> parse_ds(b@, start as int, end as int) matches Some(s) && rdata_is(x, s),
        r is None ==> parse_ds(b@, start as int, end as int) is None,
{
    if end - start < 4 {
        return None;
    }
    Some(
        Rdata::Ds {
            key_tag: read_u16(b, start).unwrap().0,
            algorithm: b[start + 2],
            digest_type: b[start + 3],
            digest: slice_subrange(b, start + 4, end),
        },
    )
}

fn read_sshfp<'a>(b: &'a [u8], start: usize, end: usize) -> (r: Option<Rdata<'a>>)
    requires
        start <= end <= b@.len(),
    ensures
        r matches Some(x) ==> parse_sshfp(b@, start as int, end as int) matches Some(s) && rdata_is(x, s),
        r is None ==> parse_sshfp(b@, start as int, end as int) is None,
{
    if end - start < 2 {
        return None;
    }
    Some(
        Rdata::Sshfp {
            algorithm: b[start],
            fp_type: b[start + 1],
            fingerprint: slice_subrange(b, start + 2, end),
        },
    )
}

fn read_nsec<'a>(b: &'a [u8], start: usize, end: usize) -> (r: Option<Rdata<'a>>)
    requires
        start <= end <= b@.len(),
    ensures
        r matches Some(x) ==> parse_nsec(b@, start as int, end as int) matches Some(s) && rdata_is(x, s),
        r is None ==> parse_nsec(b@, start as int, end as int) is None,
{
    match read_plain_name(b, start, end) {
        Some((next, p, n)) => Some(Rdata::Nsec { next, type_bitmaps: slice_subrange(b, p, end) }),
        None => None,
    }
}

fn read_dnskey<'a>(b: &'a [u8], start: usize, end: usize) -> (r: Option<Rdata<'a>>)
    requires
        start <= end <= b@.len(),
    ensures
        r matches Some(x) ==> parse_dnskey(b@, start as int, end as int) matches Some(s) && rdata_is(x, s),
        r is None ==> parse_dnskey(b@, start as int, end as int) is None,
{
    if end - start < 4 {
        return None;
    }
    Some(
        Rdata::Dnskey {
            flags: read_u16(b, start).unwrap().0,
            protocol: b[start + 2],
            algorithm: b[start + 3],
            public_key: slice_subrange(b, start + 4, end),
        },
    )
}

fn read_nsec3<'a>(b: &'a [u8], start: usize, end: usize) -> (r: Option<Rdata<'a>>)
    requires
        start <= end <= b@.len(),
    ensures
        r matches Some(x) ==> parse_nsec3(b@, start as int, end as int) matches Some(s) && rdata_is(x, s),
        r is None ==> parse_nsec3(b@, start as int, end as int) is None,
{
    if end - start < 4 {
        return None;
    }
    let (salt, p) = match read_cstring(b, start + 4, end) {
        Some(x) => x,
        None => return None,
    };
    let (next_hashed, q) = match read_cstring(b, p, end) {
        Some(x) => x,
        None => return None,
    };
    Some(
        Rdata::Nsec3 {
            hash_algorithm: b[start],
            flags: b[start + 1],
            iterations: read_u16(b, start + 2).unwrap().0,
            salt,
            next_hashed,
            type_bitmaps: slice_subrange(b, q, end),
        },
    )
}

fn read_nsec3param<'a>(b: &'a [u8], start: usize, end: usize) -> (r: Option<Rdata<'a>>)
    requires
        start <= end <= b@.len(),
    ensures
        r matches Some(x) ==> parse_nsec3param(b@, start as int, end as int) matches Some(s) && rdata_is(x, s),
        r is None ==> parse_nsec3param(b@, start as int, end as int) is None,
{
    if end - start < 4 {
        return None;
    }
    let (salt, p) = match read_cstring(b, start + 4, end) {
        Some(x) => x,
        None => return None,
    };
    if p != end {
        return None;
    }
    Some(
        Rdata::Nsec3param {
            hash_algorithm: b[start],
            flags: b[start + 1],
            iterations: read_u16(b, start + 2).unwrap().0,
            salt,
        },
    )
}

fn all_alnum(b: &[u8], from: usize, to: usize) -> (r: bool)
    requires
        from <= to <= b@.len(),
    ensures
        r == forall|j: int| from <= j < to ==> is_alnum(#[trigger] b@[j]),
{
    let mut i = from;
    while i < to
        invariant
            from <= i <= to <= b@.len(),
            forall|j: int| from <= j < i ==> is_alnum(#[trigger] b@[j]),
        decreases to - i,
    {
        let c = b[i];
        if !((48 <= c && c <= 57) || (65 <= c && c <= 90) || (97 <= c && c <= 122)) {
            proof {
                assert(!is_alnum(b@[i as int]));
            }
            return false;
        }
        i = i + 1;
    }
    true
}

fn read_mx<'a>(b: &'a [u8], start: usize, end: usize) -> (r: Option<Rdata<'a>>)
    requires
        start <= end <= b@.len(),
    ensures
        r matches Some(x) ==> parse_mx(b@, start as int, end as int) matches Some(s) && rdata_is(x, s),
        r is None ==> parse_mx(b@, start as int, end as int) is None,
{
    let len = end - start;
        let (preference, p1) = match read_u16_in(b, start, end) {
            Some(x) => x,
            None => return None,
        };
        match read_name_exact(b, p1, end) {
            Some((exchange, n)) => Some(Rdata::Mx { preference, exchange }),
            None => None,
        }
    }

fn read_txt<'a>(b: &'a [u8], start: usize, end: usize) -> (r: Option<Rdata<'a>>)
    requires
        start <= end <= b@.len(),
    ensures
        r matches Some(x) ==> parse_txt(b@, start as int, end as int) matches Some(s) && rdata_is(x, s),
        r is None ==> parse_txt(b@, start as int, end as int) is None,
{
    let len = end - start;
        match read_cstrings(b, start, end) {
            Some(v) => if v.len() > 0 {
                Some(Rdata::Txt(v))
            } else {
                None
            },
            None => None,
        }
    }

fn read_hinfo<'a>(b: &'a [u8], start: usize, end: usize) -> (r: Option<Rdata<'a>>)
    requires
        start <= end <= b@.len(),
    ensures
        r matches Some(x) ==> parse_hinfo(b@, start as int, end as int) matches Some(s) && rdata_is(x, s),
        r is None ==> parse_hinfo(b@, start as int, end as int) is None,
{
    let len = end - start;
        let (cpu, p1) = match read_cstring(b, start, end) {
            Some(x) => x,
            None => return None,
        };
        let (os, p2) = match read_cstring(b, p1, end) {
            Some(x) => x,
            None => return None,
        };
        if p2 == end {
            Some(Rdata::Hinfo { cpu, os })
        } else {
            None
        }
    }

fn read_soa<'a>(b: &'a [u8], start: usize, end: usize) -> (r: Option<Rdata<'a>>)
    requires
        start <= end <= b@.len(),
    ensures
        r matches Some(x) ==> parse_soa(b@, start as int, end as int) matches Some(s) && rdata_is(x, s),
        r is None ==> parse_soa(b@, start as int, end as int) is None,
{
    let len = end - start;
        let (mname, p1, m) = match read_name_in(b, start, end) {
            Some(x) => x,
            None => return None,
        };
        let (rname, p2, n) = match read_name_in(b, p1, end) {
            Some(x) => x,
            None => return None,
        };
        if end - p2 != 20 {
            return None;
        }
        Some(
            Rdata::Soa {
                mname,
                rname,
                serial: read_u32(b, p2).unwrap().0,
                refresh: read_u32(b, p2 + 4).unwrap().0,
                retry: read_u32(b, p2 + 8).unwrap().0,
                expire: read_u32(b, p2 + 12).unwrap().0,
                minimum: read_u32(b, p2 + 16).unwrap().0,
            },
        )
    }

fn read_srv<'a>(b: &'a [u8], start: usize, end: usize) -> (r: Option<Rdata<'a>>)
    requires
        start <= end <= b@.len(),
    ensures
        r matches Some(x) ==> parse_srv(b@, start as int, end as int) matches Some(s) && rdata_is(x, s),
        r is None ==> parse_srv(b@, start as int, end as int) is None,
{
    let len = end - start;
        if len < 6 {
            return None;
        }
        match read_name_exact(b, start + 6, end) {
            Some((target, n)) => Some(
                Rdata::Srv {
                    priority: read_u16(b, start).unwrap().0,
                    weight: read_u16(b, start + 2).unwrap().0,
                    port: read_u16(b, start + 4).unwrap().0,
                    target,
                },
            ),
            None => None,
        }
    }

fn read_naptr<'a>(b: &'a [u8], start: usize, end: usize) -> (r: Option<Rdata<'a>>)
    requires
        start <= end <= b@.len(),
    ensures
        r matches Some(x) ==> parse_naptr(b@, start as int, end as int) matches Some(s) && rdata_is(x, s),
        r is None ==> parse_naptr(b@, start as int, end as int) is None,
{
    let len = end - start;
        if len < 4 {
            return None;
        }
        let (flags, p1) = match read_cstring(b, start + 4, end) {
            Some(x) => x,
            None => return None,
        };
        let (services, p2) = match read_cstring(b, p1, end) {
            Some(x) => x,
            None => return None,
        };
        let (regexp, p3) = match read_cstring(b, p2, end) {
            Some(x) => x,
            None => return None,
        };
        match read_name_exact(b, p3, end) {
            Some((replacement, n)) => Some(
                Rdata::Naptr {
                    order: read_u16(b, start).unwrap().0,
                    preference: read_u16(b, start + 2).unwrap().0,
                    flags,
                    services,
                    regexp,
                    replacement,
                },
            ),
            None => None,
        }
    }

fn read_tlsa<'a>(b: &'a [u8], start: usize, end: usize) -> (r: Option<Rdata<'a>>)
    requires
        start <= end <= b@.len(),
    ensures
        r matches Some(x) ==> parse_tlsa(b@, start as int, end as int) matches Some(s) && rdata_is(x, s),
        r is None ==> parse_tlsa(b@, start as int, end as int) is None,
{
    let len = end - start;
        if len < 3 {
            return None;
        }
        Some(
            Rdata::Tlsa {
                usage: b[start],
                selector: b[start + 1],
                matching: b[start + 2],
                data: slice_subrange(b, start + 3, end),
            },
        )
    }

fn read_uri<'a>(b: &'a [u8], start: usize, end: usize) -> (r: Option<Rdata<'a>>)
    requires
        start <= end <= b@.len(),
    ensures
        r matches Some(x) ==> parse_uri(b@, start as int, end as int) matches Some(s) && rdata_is(x, s),
        r is None ==> parse_uri(b@, start as int, end as int) is None,
{
    let len = end - start;
        if len < 5 {
            return None;
        }
        Some(
            Rdata::Uri {
                priority: read_u16(b, start).unwrap().0,
                weight: read_u16(b, start + 2).unwrap().0,
                target: slice_subrange(b, start + 4, end),
            },
        )
    }

fn read_caa<'a>(b: &'a [u8], start: usize, end: usize) -> (r: Option<Rdata<'a>>)
    requires
        start <= end <= b@.len(),
    ensures
        r matches Some(x) ==> parse_caa(b@, start as int, end as int) matches Some(s) && rdata_is(x, s),
        r is None ==> parse_caa(b@, start as int, end as int) is None,
{
    let len = end - start;
        if len < 2 {
            return None;
        }
        let tlen = b[start + 1] as usize;
        if tlen < 1 || tlen > 15 || tlen > len - 2 {
            return None;
        }
        if !all_alnum(b, start + 2, start + 2 + tlen) {
            return None;
        }
        Some(
            Rdata::Caa {
                flags: b[start],
                tag: slice_subrange(b, start + 2, start + 2 + tlen),
                value: slice_subrange(b, start + 2 + tlen, end),
            },
        )
    }

/// Decodes the RDATA `b[start..end]` of a record of type `rtype`, where `b`
/// is the whole message (names inside RDATA may point into it).
pub fn read_rdata<'a>(b: &'a [u8], rtype: u16, start: usize, end: usize) -> (r: Option<Rdata<'a>>)
    ensures
        r matches Some(x) ==> parse_rdata(b@, rtype, start as int, end as int) matches Some(s)
            && rdata_is(x, s),
        r is None ==> parse_rdata(b@, rtype, start as int, end as int) is None,
{
    if !(start <= end && end <= b.len()) {
        return None;
    }
    let len = end - start;
    if rtype == 1 {
        if len == 4 {
            Some(Rdata::A(slice_subrange(b, start, end)))
        } else {
            None
        }
    } else if rtype == 28 {
        if len == 16 {
            Some(Rdata::Aaaa(slice_subrange(b, start, end)))
        } else {
            None
        }
    } else if rtype == 2 || rtype == 5 || rtype == 12 {
        match read_name_exact(b, start, end) {
            Some((v, n)) => Some(
                if rtype == 2 {
                    Rdata::Ns(v)
                } else if rtype == 5 {
                    Rdata::Cname(v)
                } else {
                    Rdata::Ptr(v)
                },
            ),
            None => None,
        }
    } else if rtype == 15 {
        read_mx(b, start, end)
    } else if rtype == 16 {
        read_txt(b, start, end)
    } else if rtype == 13 {
        read_hinfo(b, start, end)
    } else if rtype == 6 {
        read_soa(b, start, end)
    } else if rtype == 24 {
        read_sig(b, start, end)
    } else if rtype == 43 {
        read_ds(b, start, end)
    } else if rtype == 44 {
        read_sshfp(b, start, end)
    } else if rtype == 46 {
        read_rrsig(b, start, end)
    } else if rtype == 47 {
        read_nsec(b, start, end)
    } else if rtype == 48 {
        read_dnskey(b, start, end)
    } else if rtype == 50 {
        read_nsec3(b, start, end)
    } else if rtype == 51 {
        read_nsec3param(b, start, end)
    } else if rtype == 33 {
        read_srv(b, start, end)
    } else if rtype == 35 {
        read_naptr(b, start, end)
    } else if rtype == 41 {
        match read_kvs(b, start, end, false) {
            Some(v) => Some(Rdata::Opt(v)),
            None => None,
        }
    } else if rtype == 52 {
        read_tlsa(b, start, end)
    } else if rtype == 64 || rtype == 65 {
        match read_svcb(b, start, end) {
            Some((priority, target, params, n)) => Some(
                if rtype == 64 {
                    Rdata::Svcb { priority, target, params }
                } else {
                    Rdata::Https { priority, target, params }
                },
            ),
            None => None,
        }
    } else if rtype == 256 {
        read_uri(b, start, end)
    } else if rtype == 257 {
        read_caa(b, start, end)
    } else {
        Some(Rdata::Unknown(slice_subrange(b, start, end)))
    }
}

/// Appends `s` to `out`.
fn push_bytes(out: &mut Vec<u8>, s: &[u8])
    ensures
        final(out)@ == old(out)@ + s@,
        is_prefix(old(out)@, final(out)@),
{
    append(out, s);
    proof {
        lemma_prefix_append(old(out)@, s@);
    }
}

/// Decodes the name at `p`, whose in-place bytes end by `end`, onto `out`.
fn name_into_in(b: &[u8], p: usize, end: usize, out: &mut Vec<u8>) -> (r: Option<
    (usize, Ghost<SpecName>),
>)
    requires
        end <= b@.len(),
    ensures
        r matches Some((e, n)) ==> {
            &&& parse_name_in(b@, p as int, end as int) == Some((n@, e as int))
            &&& final(out)@ == old(out)@ + ser_name(n@)
        },
        r is None ==> parse_name_in(b@, p as int, end as int) is None,
        is_prefix(old(out)@, final(out)@),
{
    match read_name_into(b, p, out) {
        Some((e, n)) => if e <= end {
            Some((e, n))
        } else {
            None
        },
        None => None,
    }
}

fn canon_one_name(b: &[u8], t: u16, start: usize, end: usize, out: &mut Vec<u8>) -> (ok: bool)
    requires
        start <= end <= b@.len(),
        t == 2 || t == 5 || t == 12,
    ensures
        ok ==> (canon_names(b@, t, start as int, end as int) matches Some(c) && final(out)@ == old(
            out,
        )@ + c),
        !ok ==> canon_names(b@, t, start as int, end as int) is None,
        is_prefix(old(out)@, final(out)@),
{
    let ghost o0 = out@;
    match name_into_in(b, start, end, out) {
        Some((e, n)) => e == end,
        None => false,
    }
}

fn canon_mx_srv(b: &[u8], t: u16, start: usize, end: usize, out: &mut Vec<u8>) -> (ok: bool)
    requires
        start <= end <= b@.len(),
        t == 15 || t == 33,
    ensures
        ok ==> (canon_names(b@, t, start as int, end as int) matches Some(c) && final(out)@ == old(
            out,
        )@ + c),
        !ok ==> canon_names(b@, t, start as int, end as int) is None,
        is_prefix(old(out)@, final(out)@),
{
    let ghost o0 = out@;
    let k: usize = if t == 15 { 2 } else { 6 };
    if end - start < k {
        proof {
            lemma_prefix_refl(o0);
        }
        return false;
    }
    push_bytes(out, slice_subrange(b, start, start + k));
    let ghost o1 = out@;
    let r = name_into_in(b, start + k, end, out);
    proof {
        lemma_prefix_trans(o0, o1, out@);
    }
    match r {
        Some((e, n)) => {
            proof {
                assert(out@ =~= o0 + (b@.subrange(start as int, start + k) + ser_name(n@)));
            }
            e == end
        },
        None => false,
    }
}

fn canon_soa(b: &[u8], t: u16, start: usize, end: usize, out: &mut Vec<u8>) -> (ok: bool)
    requires
        start <= end <= b@.len(),
        t == 6,
    ensures
        ok ==> (canon_names(b@, t, start as int, end as int) matches Some(c) && final(out)@ == old(
            out,
        )@ + c),
        !ok ==> canon_names(b@, t, start as int, end as int) is None,
        is_prefix(old(out)@, final(out)@),
{
    let ghost o0 = out@;
    let (p1, n1) = match name_into_in(b, start, end, out) {
        Some(x) => x,
        None => return false,
    };
    let ghost o1 = out@;
    let r = name_into_in(b, p1, end, out);
    let ghost o2 = out@;
    proof {
        lemma_prefix_trans(o0, o1, o2);
    }
    let (p2, n2) = match r {
        Some(x) => x,
        None => return false,
    };
    if end - p2 != 20 {
        return false;
    }
    push_bytes(out, slice_subrange(b, p2, end));
    proof {
        lemma_prefix_trans(o0, o2, out@);
        assert(out@ =~= o0 + (ser_name(n1@) + ser_name(n2@) + b@.subrange(p2 as int, end as int)));
    }
    true
}

fn canon_sig(b: &[u8], t: u16, start: usize, end: usize, out: &mut Vec<u8>) -> (ok: bool)
    requires
        start <= end <= b@.len(),
        t == 24,
    ensures
        ok ==> (canon_names(b@, t, start as int, end as int) matches Some(c) && final(out)@ == old(
            out,
        )@ + c),
        !ok ==> canon_names(b@, t, start as int, end as int) is None,
        is_prefix(old(out)@, final(out)@),
{
    let ghost o0 = out@;
    if end - start < 18 {
        proof {
            lemma_prefix_refl(o0);
        }
        return false;
    }
    push_bytes(out, slice_subrange(b, start, start + 18));
    let ghost o1 = out@;
    let r = name_into_in(b, start + 18, end, out);
    let ghost o2 = out@;
    proof {
        lemma_prefix_trans(o0, o1, o2);
    }
    let (p, n) = match r {
        Some(x) => x,
        None => return false,
    };
    push_bytes(out, slice_subrange(b, p, end));
    proof {
        lemma_prefix_trans(o0, o2, out@);
        assert(out@ =~= o0 + (b@.subrange(start as int, start + 18) + ser_name(n@)
            + b@.subrange(p as int, end as int)));
    }
    true
}

fn canon_naptr(b: &[u8], t: u16, start: usize, end: usize, out: &mut Vec<u8>) -> (ok: bool)
    requires
        start <= end <= b@.len(),
        t == 35,
    ensures
        ok ==> (canon_names(b@, t, start as int, end as int) matches Some(c) && final(out)@ == old(
            out,
        )@ + c),
        !ok ==> canon_names(b@, t, start as int, end as int) is None,
        is_prefix(old(out)@, final(out)@),
{
    let ghost o0 = out@;
    proof {
        lemma_prefix_refl(o0);
    }
    if end - start < 4 {
        return false;
    }
    let p1 = match read_cstring(b, start + 4, end) {
        Some((_, q)) => q,
        None => return false,
    };
    let p2 = match read_cstring(b, p1, end) {
        Some((_, q)) => q,
        None => return false,
    };
    let p3 = match read_cstring(b, p2, end) {
        Some((_, q)) => q,
        None => return false,
    };
    push_bytes(out, slice_subrange(b, start, p3));
    let ghost o1 = out@;
    let r = name_into_in(b, p3, end, out);
    proof {
        lemma_prefix_trans(o0, o1, out@);
    }
    match r {
        Some((e, n)) => {
            proof {
                assert(out@ =~= o0 + (b@.subrange(start as int, p3 as int) + ser_name(n@)));
            }
            e == end
        },
        None => false,
    }
}

/// Appends the canonical form of the RDATA `b[start..end]` of type `t`
/// (`canon_names`: every name inside it decompressed) to `out`. On failure
/// `out` may have grown.
/// Inlined: out of line it costs `parse` about 20%.
#[inline(always)]
pub fn canon_into(b: &[u8], t: u16, start: usize, end: usize, out: &mut Vec<u8>) -> (ok: bool)
    requires
        start <= end <= b@.len(),
    ensures
        ok ==> (canon_names(b@, t, start as int, end as int) matches Some(c) && final(out)@ == old(
            out,
        )@ + c),
        !ok ==> canon_names(b@, t, start as int, end as int) is None,
        is_prefix(old(out)@, final(out)@),
{
    if t == 2 || t == 5 || t == 12 {
        canon_one_name(b, t, start, end, out)
    } else if t == 15 || t == 33 {
        canon_mx_srv(b, t, start, end, out)
    } else if t == 6 {
        canon_soa(b, t, start, end, out)
    } else if t == 24 {
        canon_sig(b, t, start, end, out)
    } else if t == 35 {
        canon_naptr(b, t, start, end, out)
    } else {
        push_bytes(out, slice_subrange(b, start, end));
        true
    }
}

impl<'a> RecordRef<'a> {
    /// The typed RDATA. Names inside RDATA are stored uncompressed, so it
    /// decodes on its own; for a parsed record this is what the RDATA in
    /// the message decodes to (`lemmas_rdata::theorem_rdata_meaning`).
    pub fn data(&self) -> (r: Option<Rdata<'a>>)
        ensures
            ({
                let s = parse_rdata(self.rdata@, self.rtype, 0, self.rdata@.len() as int);
                &&& r matches Some(x) ==> s matches Some(t) && rdata_is(x, t)
                &&& r is None ==> s is None
            }),
    {
        read_rdata(self.rdata, self.rtype, 0, self.rdata.len())
    }
}

} // verus!

impl core::ops::Deref for NameBytes<'_> {
    type Target = [u8];

    fn deref(&self) -> &[u8] {
        match self {
            NameBytes::Borrowed(s) => s,
            NameBytes::Owned(v) => v,
        }
    }
}

impl core::fmt::Debug for NameBytes<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        (**self).fmt(f)
    }
}

impl PartialEq for NameBytes<'_> {
    fn eq(&self, other: &Self) -> bool {
        **self == **other
    }
}

impl Eq for NameBytes<'_> {}
