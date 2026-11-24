//! Verified typed RDATA encoding: the inverse of `rdata::read_rdata`.
//!
//! `encode_rdata` lays out the fields of a typed record as RFC 1035 and the
//! RDATA RFCs say, and is proven to be undone by the typed decoder: the
//! bytes it writes decode (`spec_rdata::parse_rdata`) to exactly the fields
//! it was given, and are canonical (`canon_names` leaves them unchanged), so
//! a `Message` stores them as written. The c-ares write adapter
//! (`cares::dns_write`) reads c-ares's records into `Rdata` and encodes them
//! here, so what vdns writes for c-ares means what c-ares's record says.
//!
//! Also here: the 255-octet splitting of long TXT strings, and the bit
//! layouts of the header flags (RFC 1035 §4.1.1, RFC 4035 §3.2) and of the
//! OPT record's TTL (RFC 6891 §6.1.3).
use alloc::vec::Vec;
#[allow(unused_imports)]
use crate::lemmas::*;
use crate::parse::append;
use crate::rdata::{plain_name_end, NameBytes, Rdata};
#[cfg(verus_only)]
use crate::rdata::{kvs_view, rdata_is, strs_view};
use crate::spec::*;
#[allow(unused_imports)]
use crate::spec_rdata::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

// ---------------------------------------------------------------------------
// The encoding, as a spec
// ---------------------------------------------------------------------------

/// RFC 1035 §3.3 <character-string>: a length octet, then the octets.
pub open spec fn ser_cstring(s: Seq<u8>) -> Seq<u8> {
    seq![s.len() as u8] + s
}

pub open spec fn ser_cstrings(v: Seq<Seq<u8>>) -> Seq<u8>
    decreases v.len(),
{
    if v.len() == 0 {
        Seq::empty()
    } else {
        ser_cstring(v[0]) + ser_cstrings(v.drop_first())
    }
}

/// An EDNS option or SVCB parameter: key, length, value.
pub open spec fn ser_kv(kv: (u16, Seq<u8>)) -> Seq<u8> {
    ser_u16(kv.0) + ser_u16(kv.1.len() as u16) + kv.1
}

pub open spec fn ser_kvs(v: Seq<(u16, Seq<u8>)>) -> Seq<u8>
    decreases v.len(),
{
    if v.len() == 0 {
        Seq::empty()
    } else {
        ser_kv(v[0]) + ser_kvs(v.drop_first())
    }
}

/// The 18 octets before the signer's name in SIG and RRSIG.
pub open spec fn ser_sig_fixed(
    type_covered: u16,
    algorithm: u8,
    labels: u8,
    original_ttl: u32,
    expiration: u32,
    inception: u32,
    key_tag: u16,
) -> Seq<u8> {
    ser_u16(type_covered) + seq![algorithm] + seq![labels] + ser_u32(original_ttl) + ser_u32(
        expiration,
    ) + ser_u32(inception) + ser_u16(key_tag)
}

/// The RDATA of `s`, names uncompressed.
pub open spec fn ser_rdata(s: SpecRdata) -> Seq<u8> {
    match s {
        SpecRdata::A(x) => x,
        SpecRdata::Aaaa(x) => x,
        SpecRdata::Ns(n) => ser_name(n),
        SpecRdata::Cname(n) => ser_name(n),
        SpecRdata::Ptr(n) => ser_name(n),
        SpecRdata::Mx { preference, exchange } => ser_u16(preference) + ser_name(exchange),
        SpecRdata::Txt(v) => ser_cstrings(v),
        SpecRdata::Hinfo { cpu, os } => ser_cstring(cpu) + ser_cstring(os),
        SpecRdata::Soa { mname, rname, serial, refresh, retry, expire, minimum } => ser_name(mname)
            + ser_name(rname) + ser_u32(serial) + ser_u32(refresh) + ser_u32(retry) + ser_u32(
            expire,
        ) + ser_u32(minimum),
        SpecRdata::Sig {
            type_covered,
            algorithm,
            labels,
            original_ttl,
            expiration,
            inception,
            key_tag,
            signer,
            signature,
        } => ser_sig_fixed(
            type_covered,
            algorithm,
            labels,
            original_ttl,
            expiration,
            inception,
            key_tag,
        ) + ser_name(signer) + signature,
        SpecRdata::Rrsig {
            type_covered,
            algorithm,
            labels,
            original_ttl,
            expiration,
            inception,
            key_tag,
            signer,
            signature,
        } => ser_sig_fixed(
            type_covered,
            algorithm,
            labels,
            original_ttl,
            expiration,
            inception,
            key_tag,
        ) + ser_name(signer) + signature,
        SpecRdata::Srv { priority, weight, port, target } => ser_u16(priority) + ser_u16(weight)
            + ser_u16(port) + ser_name(target),
        SpecRdata::Naptr { order, preference, flags, services, regexp, replacement } => ser_u16(
            order,
        ) + ser_u16(preference) + ser_cstring(flags) + ser_cstring(services) + ser_cstring(regexp)
            + ser_name(replacement),
        SpecRdata::Opt(v) => ser_kvs(v),
        SpecRdata::Ds { key_tag, algorithm, digest_type, digest } => ser_u16(key_tag) + seq![
            algorithm,
        ] + seq![digest_type] + digest,
        SpecRdata::Sshfp { algorithm, fp_type, fingerprint } => seq![algorithm] + seq![fp_type]
            + fingerprint,
        SpecRdata::Nsec { next, type_bitmaps } => ser_name(next) + type_bitmaps,
        SpecRdata::Dnskey { flags, protocol, algorithm, public_key } => ser_u16(flags) + seq![
            protocol,
        ] + seq![algorithm] + public_key,
        SpecRdata::Nsec3 { hash_algorithm, flags, iterations, salt, next_hashed, type_bitmaps } =>
        seq![hash_algorithm] + seq![flags] + ser_u16(iterations) + ser_cstring(salt) + ser_cstring(
            next_hashed,
        ) + type_bitmaps,
        SpecRdata::Nsec3param { hash_algorithm, flags, iterations, salt } => seq![hash_algorithm]
            + seq![flags] + ser_u16(iterations) + ser_cstring(salt),
        SpecRdata::Tlsa { usage, selector, matching, data } => seq![usage] + seq![selector] + seq![
            matching,
        ] + data,
        SpecRdata::Svcb { priority, target, params } => ser_u16(priority) + ser_name(target)
            + ser_kvs(params),
        SpecRdata::Https { priority, target, params } => ser_u16(priority) + ser_name(target)
            + ser_kvs(params),
        SpecRdata::Uri { priority, weight, target } => ser_u16(priority) + ser_u16(weight) + target,
        SpecRdata::Caa { flags, tag, value } => seq![flags] + seq![tag.len() as u8] + tag + value,
        SpecRdata::Unknown(x) => x,
    }
}

/// The types `parse_rdata` decodes; any other is kept as raw bytes.
pub open spec fn typed(t: u16) -> bool {
    t == TYPE_A || t == TYPE_NS || t == TYPE_CNAME || t == TYPE_SOA || t == TYPE_PTR || t
        == TYPE_HINFO || t == TYPE_MX || t == TYPE_TXT || t == TYPE_SIG || t == TYPE_AAAA || t
        == TYPE_SRV || t == TYPE_NAPTR || t == TYPE_OPT || t == TYPE_DS || t == TYPE_SSHFP || t
        == TYPE_RRSIG || t == TYPE_NSEC || t == TYPE_DNSKEY || t == TYPE_NSEC3 || t
        == TYPE_NSEC3PARAM || t == TYPE_TLSA || t == TYPE_SVCB || t == TYPE_HTTPS || t == TYPE_URI
        || t == TYPE_CAA
}

pub open spec fn cstr_ok(s: Seq<u8>) -> bool {
    s.len() <= 255
}

pub open spec fn cstrs_ok(v: Seq<Seq<u8>>) -> bool {
    forall|i: int| 0 <= i < v.len() ==> cstr_ok(#[trigger] v[i])
}

pub open spec fn kvs_ok(v: Seq<(u16, Seq<u8>)>) -> bool {
    forall|i: int| 0 <= i < v.len() ==> (#[trigger] v[i]).1.len() <= u16::MAX
}

/// Each key is greater than the one before it, and the first than `prev`.
pub open spec fn keys_above(v: Seq<(u16, Seq<u8>)>, prev: int) -> bool
    decreases v.len(),
{
    v.len() == 0 || (v[0].0 as int > prev && keys_above(v.drop_first(), v[0].0 as int))
}

/// `s` can be written as RDATA of type `t`: its variant is `t`'s and every
/// field fits its encoding.
pub open spec fn rdata_ok(s: SpecRdata, t: u16) -> bool {
    match s {
        SpecRdata::A(x) => t == TYPE_A && x.len() == 4,
        SpecRdata::Aaaa(x) => t == TYPE_AAAA && x.len() == 16,
        SpecRdata::Ns(n) => t == TYPE_NS && valid_name(n),
        SpecRdata::Cname(n) => t == TYPE_CNAME && valid_name(n),
        SpecRdata::Ptr(n) => t == TYPE_PTR && valid_name(n),
        SpecRdata::Mx { exchange, .. } => t == TYPE_MX && valid_name(exchange),
        SpecRdata::Txt(v) => t == TYPE_TXT && v.len() > 0 && cstrs_ok(v),
        SpecRdata::Hinfo { cpu, os } => t == TYPE_HINFO && cstr_ok(cpu) && cstr_ok(os),
        SpecRdata::Soa { mname, rname, .. } => t == TYPE_SOA && valid_name(mname) && valid_name(
            rname,
        ),
        SpecRdata::Sig { signer, .. } => t == TYPE_SIG && valid_name(signer),
        SpecRdata::Rrsig { signer, .. } => t == TYPE_RRSIG && valid_name(signer),
        SpecRdata::Srv { target, .. } => t == TYPE_SRV && valid_name(target),
        SpecRdata::Naptr { flags, services, regexp, replacement, .. } => t == TYPE_NAPTR && cstr_ok(
            flags,
        ) && cstr_ok(services) && cstr_ok(regexp) && valid_name(replacement),
        SpecRdata::Opt(v) => t == TYPE_OPT && kvs_ok(v),
        SpecRdata::Ds { .. } => t == TYPE_DS,
        SpecRdata::Sshfp { .. } => t == TYPE_SSHFP,
        SpecRdata::Nsec { next, .. } => t == TYPE_NSEC && valid_name(next),
        SpecRdata::Dnskey { .. } => t == TYPE_DNSKEY,
        SpecRdata::Nsec3 { salt, next_hashed, .. } => t == TYPE_NSEC3 && cstr_ok(salt) && cstr_ok(
            next_hashed,
        ),
        SpecRdata::Nsec3param { salt, .. } => t == TYPE_NSEC3PARAM && cstr_ok(salt),
        SpecRdata::Tlsa { .. } => t == TYPE_TLSA,
        SpecRdata::Svcb { target, params, .. } => t == TYPE_SVCB && valid_name(target) && kvs_ok(
            params,
        ) && keys_above(params, -1),
        SpecRdata::Https { target, params, .. } => t == TYPE_HTTPS && valid_name(target) && kvs_ok(
            params,
        ) && keys_above(params, -1),
        SpecRdata::Uri { target, .. } => t == TYPE_URI && target.len() > 0,
        SpecRdata::Caa { tag, .. } => t == TYPE_CAA && 1 <= tag.len() <= 15 && (forall|i: int|
            0 <= i < tag.len() ==> is_alnum(#[trigger] tag[i])),
        SpecRdata::Unknown(_) => !typed(t),
    }
}

// ---------------------------------------------------------------------------
// The encoding is undone by the decoder
// ---------------------------------------------------------------------------

proof fn lemma_byte(b: Seq<u8>, p: int, v: u8)
    requires
        at(b, p, seq![v]),
    ensures
        0 <= p < b.len(),
        b[p] == v,
{
    assert(b[p] == b.subrange(p, p + 1)[0]);
}

proof fn lemma_cstring_rt(b: Seq<u8>, p: int, end: int, s: Seq<u8>)
    requires
        at(b, p, ser_cstring(s)),
        cstr_ok(s),
        p + 1 + s.len() <= end <= b.len(),
    ensures
        parse_cstring(b, p, end) == Some((s, p + 1 + s.len())),
{
    lemma_at_split(b, p, seq![s.len() as u8], s);
    lemma_byte(b, p, s.len() as u8);
}

proof fn lemma_cstrings_rt(b: Seq<u8>, p: int, end: int, v: Seq<Seq<u8>>)
    requires
        at(b, p, ser_cstrings(v)),
        end == p + ser_cstrings(v).len(),
        cstrs_ok(v),
    ensures
        parse_cstrings(b, p, end) == Some(v),
    decreases v.len(),
{
    if v.len() == 0 {
        assert(v =~= Seq::<Seq<u8>>::empty());
    } else {
        let rest = v.drop_first();
        assert(cstr_ok(v[0]));
        lemma_at_split(b, p, ser_cstring(v[0]), ser_cstrings(rest));
        lemma_cstring_rt(b, p, end, v[0]);
        assert(cstrs_ok(rest)) by {
            assert forall|i: int| 0 <= i < rest.len() implies cstr_ok(#[trigger] rest[i]) by {
                assert(rest[i] == v[i + 1]);
            }
        }
        lemma_cstrings_rt(b, p + 1 + v[0].len(), end, rest);
        assert(seq![v[0]] + rest =~= v);
    }
}

proof fn lemma_kv_rt(b: Seq<u8>, p: int, end: int, kv: (u16, Seq<u8>))
    requires
        at(b, p, ser_kv(kv)),
        kv.1.len() <= u16::MAX,
        p + 4 + kv.1.len() <= end <= b.len(),
    ensures
        parse_kv(b, p, end) == Some((kv, p + 4 + kv.1.len())),
{
    let len = kv.1.len() as u16;
    assert(ser_kv(kv) =~= ser_u16(kv.0) + (ser_u16(len) + kv.1));
    lemma_at_split(b, p, ser_u16(kv.0), ser_u16(len) + kv.1);
    lemma_at_split(b, p + 2, ser_u16(len), kv.1);
    lemma_u16_roundtrip(b, p, kv.0);
    lemma_u16_roundtrip(b, p + 2, len);
}

proof fn lemma_kvs_rt(b: Seq<u8>, p: int, end: int, v: Seq<(u16, Seq<u8>)>, inc: bool, prev: int)
    requires
        at(b, p, ser_kvs(v)),
        end == p + ser_kvs(v).len(),
        kvs_ok(v),
        inc ==> keys_above(v, prev),
    ensures
        parse_kvs(b, p, end, inc, prev) == Some(v),
    decreases v.len(),
{
    if v.len() == 0 {
        assert(v =~= Seq::<(u16, Seq<u8>)>::empty());
    } else {
        let rest = v.drop_first();
        assert(v[0].1.len() <= u16::MAX);
        lemma_at_split(b, p, ser_kv(v[0]), ser_kvs(rest));
        lemma_kv_rt(b, p, end, v[0]);
        assert(kvs_ok(rest)) by {
            assert forall|i: int| 0 <= i < rest.len() implies (#[trigger] rest[i]).1.len()
                <= u16::MAX by {
                assert(rest[i] == v[i + 1]);
            }
        }
        lemma_kvs_rt(b, p + 4 + v[0].1.len(), end, rest, inc, v[0].0 as int);
        assert(seq![v[0]] + rest =~= v);
    }
}

proof fn lemma_plain_labels_rt(b: Seq<u8>, p: int, end: int, n: SpecName)
    requires
        forall|i: int| 0 <= i < n.len() ==> valid_label(#[trigger] n[i]),
        at(b, p, ser_name(n)),
        p + ser_name(n).len() <= end <= b.len(),
    ensures
        parse_plain_labels(b, p, end) == Some((n, p + ser_name(n).len())),
    decreases n.len(),
{
    if n.len() == 0 {
        assert(ser_name(n) =~= seq![0u8]);
        lemma_byte(b, p, 0u8);
    } else {
        let l = n[0];
        let rest = n.drop_first();
        assert(valid_label(l));
        assert(ser_name(n) =~= seq![l.len() as u8] + (l + ser_name(rest)));
        lemma_at_split(b, p, seq![l.len() as u8], l + ser_name(rest));
        lemma_at_split(b, p + 1, l, ser_name(rest));
        lemma_byte(b, p, l.len() as u8);
        assert forall|i: int| 0 <= i < rest.len() implies valid_label(#[trigger] rest[i]) by {
            assert(rest[i] == n[i + 1]);
        }
        lemma_plain_labels_rt(b, p + 1 + l.len(), end, rest);
        assert(seq![l] + rest =~= n);
    }
}

proof fn lemma_plain_rt(b: Seq<u8>, p: int, end: int, n: SpecName)
    requires
        valid_name(n),
        at(b, p, ser_name(n)),
        p + ser_name(n).len() <= end <= b.len(),
    ensures
        parse_plain_name(b, p, end) == Some((n, p + ser_name(n).len())),
{
    lemma_plain_labels_rt(b, p, end, n);
}

proof fn lemma_name_in_rt(b: Seq<u8>, p: int, end: int, n: SpecName)
    requires
        valid_name(n),
        at(b, p, ser_name(n)),
        p + ser_name(n).len() <= end,
    ensures
        parse_name_in(b, p, end) == Some((n, p + ser_name(n).len())),
{
    lemma_name_roundtrip(b, p, n);
}

/// `b` is `x` followed by `y`.
proof fn lemma_cat(b: Seq<u8>, x: Seq<u8>, y: Seq<u8>)
    requires
        b == x + y,
    ensures
        at(b, 0, x),
        at(b, x.len() as int, y),
        b.len() == x.len() + y.len(),
{
    lemma_at_whole(b);
    lemma_at_split(b, 0, x, y);
}

/// The fixed SIG/RRSIG fields decode from the first 18 octets of `b`.
proof fn lemma_sig_fixed(
    b: Seq<u8>,
    tc: u16,
    alg: u8,
    lab: u8,
    ottl: u32,
    exp: u32,
    inc: u32,
    kt: u16,
)
    requires
        at(b, 0, ser_sig_fixed(tc, alg, lab, ottl, exp, inc, kt)),
    ensures
        ser_sig_fixed(tc, alg, lab, ottl, exp, inc, kt).len() == 18,
        parse_u16(b, 0) == Some((tc, 2)),
        b[2] == alg,
        b[3] == lab,
        parse_u32(b, 4) == Some((ottl, 8)),
        parse_u32(b, 8) == Some((exp, 12)),
        parse_u32(b, 12) == Some((inc, 16)),
        parse_u16(b, 16) == Some((kt, 18)),
{
    let f = ser_sig_fixed(tc, alg, lab, ottl, exp, inc, kt);
    assert(f =~= ser_u16(tc) + (seq![alg] + (seq![lab] + (ser_u32(ottl) + (ser_u32(exp) + (
    ser_u32(inc) + ser_u16(kt)))))));
    lemma_at_split(b, 0, ser_u16(tc), seq![alg] + (seq![lab] + (ser_u32(ottl) + (ser_u32(exp) + (
    ser_u32(inc) + ser_u16(kt))))));
    lemma_at_split(b, 2, seq![alg], seq![lab] + (ser_u32(ottl) + (ser_u32(exp) + (ser_u32(inc)
        + ser_u16(kt)))));
    lemma_at_split(b, 3, seq![lab], ser_u32(ottl) + (ser_u32(exp) + (ser_u32(inc) + ser_u16(kt))));
    lemma_at_split(b, 4, ser_u32(ottl), ser_u32(exp) + (ser_u32(inc) + ser_u16(kt)));
    lemma_at_split(b, 8, ser_u32(exp), ser_u32(inc) + ser_u16(kt));
    lemma_at_split(b, 12, ser_u32(inc), ser_u16(kt));
    lemma_u16_roundtrip(b, 0, tc);
    lemma_byte(b, 2, alg);
    lemma_byte(b, 3, lab);
    lemma_u32_roundtrip(b, 4, ottl);
    lemma_u32_roundtrip(b, 8, exp);
    lemma_u32_roundtrip(b, 12, inc);
    lemma_u16_roundtrip(b, 16, kt);
}

/// What the decoder makes of encoded RDATA.
pub open spec fn decodes_to(b: Seq<u8>, t: u16, s: SpecRdata) -> bool {
    &&& parse_rdata(b, t, 0, b.len() as int) == Some(s)
    &&& canon_names(b, t, 0, b.len() as int) == Some(b)
}






#[verifier::spinoff_prover]
proof fn lemma_rt_ns(s: SpecRdata, t: u16)
    requires
        rdata_ok(s, t),
        s is Ns,
    ensures
        decodes_to(ser_rdata(s), t, s),
{
    let b = ser_rdata(s);
    let l = b.len() as int;
    match s {
        SpecRdata::Ns(n) => {
            lemma_at_whole(b);
            lemma_name_in_rt(b, 0, l, n);
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_rt_cname(s: SpecRdata, t: u16)
    requires
        rdata_ok(s, t),
        s is Cname,
    ensures
        decodes_to(ser_rdata(s), t, s),
{
    let b = ser_rdata(s);
    let l = b.len() as int;
    match s {
        SpecRdata::Cname(n) => {
            lemma_at_whole(b);
            lemma_name_in_rt(b, 0, l, n);
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_rt_ptr(s: SpecRdata, t: u16)
    requires
        rdata_ok(s, t),
        s is Ptr,
    ensures
        decodes_to(ser_rdata(s), t, s),
{
    let b = ser_rdata(s);
    let l = b.len() as int;
    match s {
        SpecRdata::Ptr(n) => {
            lemma_at_whole(b);
            lemma_name_in_rt(b, 0, l, n);
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_rt_mx(s: SpecRdata, t: u16)
    requires
        rdata_ok(s, t),
        s is Mx,
    ensures
        decodes_to(ser_rdata(s), t, s),
{
    let b = ser_rdata(s);
    let l = b.len() as int;
    match s {
        SpecRdata::Mx { preference, exchange } => {
            lemma_cat(b, ser_u16(preference), ser_name(exchange));
            lemma_u16_roundtrip(b, 0, preference);
            lemma_name_in_rt(b, 2, l, exchange);
            assert(b.subrange(0, 2) + ser_name(exchange) =~= b);
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_rt_srv(s: SpecRdata, t: u16)
    requires
        rdata_ok(s, t),
        s is Srv,
    ensures
        decodes_to(ser_rdata(s), t, s),
{
    let b = ser_rdata(s);
    let l = b.len() as int;
    match s {
        SpecRdata::Srv { priority, weight, port, target } => {
            let n = ser_name(target);
            assert(b =~= ser_u16(priority) + (ser_u16(weight) + (ser_u16(port) + n)));
            lemma_cat(b, ser_u16(priority), ser_u16(weight) + (ser_u16(port) + n));
            lemma_at_split(b, 2, ser_u16(weight), ser_u16(port) + n);
            lemma_at_split(b, 4, ser_u16(port), n);
            lemma_u16_roundtrip(b, 0, priority);
            lemma_u16_roundtrip(b, 2, weight);
            lemma_u16_roundtrip(b, 4, port);
            lemma_name_in_rt(b, 6, l, target);
            assert(b.subrange(0, 6) + ser_name(target) =~= b);
        },
        _ => {},
    }
}

proof fn lemma_soa_tail(b: Seq<u8>, p: int, a: u32, c: u32, d: u32, e: u32, f: u32)
    requires
        at(b, p, ser_u32(a) + (ser_u32(c) + (ser_u32(d) + (ser_u32(e) + ser_u32(f))))),
    ensures
        parse_u32(b, p) == Some((a, p + 4)),
        parse_u32(b, p + 4) == Some((c, p + 8)),
        parse_u32(b, p + 8) == Some((d, p + 12)),
        parse_u32(b, p + 12) == Some((e, p + 16)),
        parse_u32(b, p + 16) == Some((f, p + 20)),
{
    lemma_at_split(b, p, ser_u32(a), ser_u32(c) + (ser_u32(d) + (ser_u32(e) + ser_u32(f))));
    lemma_at_split(b, p + 4, ser_u32(c), ser_u32(d) + (ser_u32(e) + ser_u32(f)));
    lemma_at_split(b, p + 8, ser_u32(d), ser_u32(e) + ser_u32(f));
    lemma_at_split(b, p + 12, ser_u32(e), ser_u32(f));
    lemma_u32_roundtrip(b, p, a);
    lemma_u32_roundtrip(b, p + 4, c);
    lemma_u32_roundtrip(b, p + 8, d);
    lemma_u32_roundtrip(b, p + 12, e);
    lemma_u32_roundtrip(b, p + 16, f);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
proof fn lemma_soa_parse(
    b: Seq<u8>,
    mname: SpecName,
    rname: SpecName,
    serial: u32,
    refresh: u32,
    retry: u32,
    expire: u32,
    minimum: u32,
)
    requires
        valid_name(mname),
        valid_name(rname),
        b == ser_name(mname) + ser_name(rname) + ser_u32(serial) + ser_u32(refresh) + ser_u32(retry)
            + ser_u32(expire) + ser_u32(minimum),
    ensures
        parse_soa(b, 0, b.len() as int) == Some(
            SpecRdata::Soa { mname, rname, serial, refresh, retry, expire, minimum },
        ),
        canon_names(b, TYPE_SOA, 0, b.len() as int) == Some(b),
{
    let l = b.len() as int;
    let n1 = ser_name(mname);
    let n2 = ser_name(rname);
    let tail = ser_u32(serial) + (ser_u32(refresh) + (ser_u32(retry) + (ser_u32(expire) + ser_u32(
        minimum,
    ))));
    let p1: int = n1.len() as int;
    let p2: int = n1.len() + n2.len() as int;
    assert(at(b, 0, n1) && at(b, p1, n2) && at(b, p2, tail) && l == p2 + 20) by {
        assert(b =~= n1 + (n2 + tail));
        lemma_cat(b, n1, n2 + tail);
        lemma_at_split(b, p1, n2, tail);
    }
    assert(parse_name_in(b, 0, l) == Some((mname, p1))) by {
        lemma_name_in_rt(b, 0, l, mname);
    }
    assert(parse_name_in(b, p1, l) == Some((rname, p2))) by {
        lemma_name_in_rt(b, p1, l, rname);
    }
    assert(parse_u32(b, p2).unwrap().0 == serial && parse_u32(b, p2 + 4).unwrap().0 == refresh
        && parse_u32(b, p2 + 8).unwrap().0 == retry && parse_u32(b, p2 + 12).unwrap().0 == expire
        && parse_u32(b, p2 + 16).unwrap().0 == minimum) by {
        lemma_soa_tail(b, p2, serial, refresh, retry, expire, minimum);
    }
    assert(n1 + n2 + b.subrange(p2, l) =~= b) by {
        assert(b.subrange(p2, l) =~= tail);
        assert(b =~= n1 + n2 + tail);
    }
}

#[verifier::spinoff_prover]
proof fn lemma_rt_soa(s: SpecRdata, t: u16)
    requires
        rdata_ok(s, t),
        s is Soa,
    ensures
        decodes_to(ser_rdata(s), t, s),
{
    match s {
        SpecRdata::Soa { mname, rname, serial, refresh, retry, expire, minimum } => {
            lemma_soa_parse(ser_rdata(s), mname, rname, serial, refresh, retry, expire, minimum);
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_rt_sig(s: SpecRdata, t: u16)
    requires
        rdata_ok(s, t),
        s is Sig,
    ensures
        decodes_to(ser_rdata(s), t, s),
{
    let b = ser_rdata(s);
    let l = b.len() as int;
    match s {
        SpecRdata::Sig { type_covered, algorithm, labels, original_ttl, expiration, inception, key_tag, signer, signature } => {
            let f = ser_sig_fixed(type_covered, algorithm, labels, original_ttl, expiration, inception, key_tag);
            assert(b =~= f + (ser_name(signer) + signature));
            lemma_cat(b, f, ser_name(signer) + signature);
            lemma_sig_fixed(b, type_covered, algorithm, labels, original_ttl, expiration, inception, key_tag);
            lemma_at_split(b, 18, ser_name(signer), signature);
            lemma_name_in_rt(b, 18, l, signer);
            let p: int = 18 + ser_name(signer).len() as int;
            assert(b.subrange(p, l) =~= signature);
            assert(b.subrange(0, 18) + ser_name(signer) + b.subrange(p, l) =~= b);
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_rt_rrsig(s: SpecRdata, t: u16)
    requires
        rdata_ok(s, t),
        s is Rrsig,
    ensures
        decodes_to(ser_rdata(s), t, s),
{
    let b = ser_rdata(s);
    let l = b.len() as int;
    match s {
        SpecRdata::Rrsig { type_covered, algorithm, labels, original_ttl, expiration, inception, key_tag, signer, signature } => {
            let f = ser_sig_fixed(type_covered, algorithm, labels, original_ttl, expiration, inception, key_tag);
            assert(b =~= f + (ser_name(signer) + signature));
            lemma_cat(b, f, ser_name(signer) + signature);
            lemma_sig_fixed(b, type_covered, algorithm, labels, original_ttl, expiration, inception, key_tag);
            lemma_at_split(b, 18, ser_name(signer), signature);
            lemma_plain_rt(b, 18, l, signer);
            let p: int = 18 + ser_name(signer).len() as int;
            assert(b.subrange(p, l) =~= signature);
            assert(b.subrange(0, l) =~= b);
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_rt_txt(s: SpecRdata, t: u16)
    requires
        rdata_ok(s, t),
        s is Txt,
    ensures
        decodes_to(ser_rdata(s), t, s),
{
    let b = ser_rdata(s);
    let l = b.len() as int;
    match s {
        SpecRdata::Txt(v) => {
            lemma_at_whole(b);
            lemma_cstrings_rt(b, 0, l, v);
            assert(b.subrange(0, l) =~= b);
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_rt_hinfo(s: SpecRdata, t: u16)
    requires
        rdata_ok(s, t),
        s is Hinfo,
    ensures
        decodes_to(ser_rdata(s), t, s),
{
    let b = ser_rdata(s);
    let l = b.len() as int;
    match s {
        SpecRdata::Hinfo { cpu, os } => {
            lemma_cat(b, ser_cstring(cpu), ser_cstring(os));
            lemma_cstring_rt(b, 0, l, cpu);
            lemma_cstring_rt(b, 1 + cpu.len() as int, l, os);
            assert(b.subrange(0, l) =~= b);
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_rt_naptr(s: SpecRdata, t: u16)
    requires
        rdata_ok(s, t),
        s is Naptr,
    ensures
        decodes_to(ser_rdata(s), t, s),
{
    let b = ser_rdata(s);
    let l = b.len() as int;
    match s {
        SpecRdata::Naptr { order, preference, flags, services, regexp, replacement } => {
            let x = ser_u16(order) + ser_u16(preference);
            let y = ser_cstring(flags) + (ser_cstring(services) + (ser_cstring(regexp) + ser_name(
                replacement,
            )));
            assert(b =~= x + y);
            lemma_cat(b, x, y);
            lemma_cat(x, ser_u16(order), ser_u16(preference));
            assert(b[0] == x[0] && b[1] == x[1] && b[2] == x[2] && b[3] == x[3]);
            lemma_u16_roundtrip(x, 0, order);
            lemma_u16_roundtrip(x, 2, preference);
            let p1: int = 5 + flags.len() as int;
            let p2: int = p1 + 1 + services.len();
            let p3: int = p2 + 1 + regexp.len();
            lemma_at_split(b, 4, ser_cstring(flags), ser_cstring(services) + (ser_cstring(regexp)
                + ser_name(replacement)));
            lemma_at_split(b, p1, ser_cstring(services), ser_cstring(regexp) + ser_name(replacement));
            lemma_at_split(b, p2, ser_cstring(regexp), ser_name(replacement));
            lemma_cstring_rt(b, 4, l, flags);
            lemma_cstring_rt(b, p1, l, services);
            lemma_cstring_rt(b, p2, l, regexp);
            lemma_name_in_rt(b, p3, l, replacement);
            assert(b.subrange(0, p3) + ser_name(replacement) =~= b);
            assert(parse_cstring(b, 4, l) == Some((flags, p1)));
            assert(parse_cstring(b, p1, l) == Some((services, p2)));
            assert(parse_cstring(b, p2, l) == Some((regexp, p3)));
            assert(p3 + ser_name(replacement).len() == l);
            assert(parse_name_exact(b, p3, l) == Some(replacement));
            assert(parse_naptr(b, 0, l) == Some(s));
            assert(parse_rdata(b, t, 0, l) == Some(s));
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_rt_ds(s: SpecRdata, t: u16)
    requires
        rdata_ok(s, t),
        s is Ds,
    ensures
        decodes_to(ser_rdata(s), t, s),
{
    let b = ser_rdata(s);
    let l = b.len() as int;
    lemma_at_whole(b);
    assert(b.subrange(0, l) =~= b);
    match s {
        SpecRdata::Ds { key_tag, algorithm, digest_type, digest } => {
            let x = ser_u16(key_tag) + seq![algorithm] + seq![digest_type];
            lemma_cat(b, x, digest);
            assert(x =~= seq![(key_tag / 256) as u8, (key_tag % 256) as u8, algorithm, digest_type]);
            assert(b[0] == x[0] && b[1] == x[1] && b[2] == x[2] && b[3] == x[3]);
            assert(x =~= ser_u16(key_tag) + (seq![algorithm] + seq![digest_type]));
            lemma_cat(x, ser_u16(key_tag), seq![algorithm] + seq![digest_type]);
            lemma_u16_roundtrip(x, 0, key_tag);
            assert(b.subrange(4, l) =~= digest);
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_rt_sshfp(s: SpecRdata, t: u16)
    requires
        rdata_ok(s, t),
        s is Sshfp,
    ensures
        decodes_to(ser_rdata(s), t, s),
{
    let b = ser_rdata(s);
    let l = b.len() as int;
    lemma_at_whole(b);
    assert(b.subrange(0, l) =~= b);
    match s {
        SpecRdata::Sshfp { algorithm, fp_type, fingerprint } => {
            lemma_cat(b, seq![algorithm] + seq![fp_type], fingerprint);
            assert(b.subrange(2, l) =~= fingerprint);
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_rt_nsec(s: SpecRdata, t: u16)
    requires
        rdata_ok(s, t),
        s is Nsec,
    ensures
        decodes_to(ser_rdata(s), t, s),
{
    let b = ser_rdata(s);
    let l = b.len() as int;
    lemma_at_whole(b);
    assert(b.subrange(0, l) =~= b);
    match s {
        SpecRdata::Nsec { next, type_bitmaps } => {
            lemma_cat(b, ser_name(next), type_bitmaps);
            lemma_plain_rt(b, 0, l, next);
            assert(b.subrange(ser_name(next).len() as int, l) =~= type_bitmaps);
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_rt_dnskey(s: SpecRdata, t: u16)
    requires
        rdata_ok(s, t),
        s is Dnskey,
    ensures
        decodes_to(ser_rdata(s), t, s),
{
    let b = ser_rdata(s);
    let l = b.len() as int;
    lemma_at_whole(b);
    assert(b.subrange(0, l) =~= b);
    match s {
        SpecRdata::Dnskey { flags, protocol, algorithm, public_key } => {
            let x = ser_u16(flags) + seq![protocol] + seq![algorithm];
            lemma_cat(b, x, public_key);
            assert(x =~= ser_u16(flags) + (seq![protocol] + seq![algorithm]));
            lemma_cat(x, ser_u16(flags), seq![protocol] + seq![algorithm]);
            lemma_u16_roundtrip(x, 0, flags);
            assert(b[0] == x[0] && b[1] == x[1] && b[2] == x[2] && b[3] == x[3]);
            assert(b.subrange(4, l) =~= public_key);
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_rt_nsec3(s: SpecRdata, t: u16)
    requires
        rdata_ok(s, t),
        s is Nsec3,
    ensures
        decodes_to(ser_rdata(s), t, s),
{
    let b = ser_rdata(s);
    let l = b.len() as int;
    lemma_at_whole(b);
    assert(b.subrange(0, l) =~= b);
    match s {
        SpecRdata::Nsec3 { hash_algorithm, flags, iterations, salt, next_hashed, type_bitmaps } => {
            let x = seq![hash_algorithm] + seq![flags] + ser_u16(iterations);
            let y = ser_cstring(salt) + (ser_cstring(next_hashed) + type_bitmaps);
            assert(b =~= x + y);
            lemma_cat(b, x, y);
            lemma_cat(x, seq![hash_algorithm] + seq![flags], ser_u16(iterations));
            lemma_u16_roundtrip(x, 2, iterations);
            assert(b[0] == x[0] && b[1] == x[1] && b[2] == x[2] && b[3] == x[3]);
            lemma_at_split(b, 4, ser_cstring(salt), ser_cstring(next_hashed) + type_bitmaps);
            let p: int = 5 + salt.len() as int;
            lemma_at_split(b, p, ser_cstring(next_hashed), type_bitmaps);
            lemma_cstring_rt(b, 4, l, salt);
            lemma_cstring_rt(b, p, l, next_hashed);
            assert(b.subrange(p + 1 + next_hashed.len(), l) =~= type_bitmaps);
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_rt_nsec3param(s: SpecRdata, t: u16)
    requires
        rdata_ok(s, t),
        s is Nsec3param,
    ensures
        decodes_to(ser_rdata(s), t, s),
{
    let b = ser_rdata(s);
    let l = b.len() as int;
    lemma_at_whole(b);
    assert(b.subrange(0, l) =~= b);
    match s {
        SpecRdata::Nsec3param { hash_algorithm, flags, iterations, salt } => {
            let x = seq![hash_algorithm] + seq![flags] + ser_u16(iterations);
            lemma_cat(b, x, ser_cstring(salt));
            lemma_cat(x, seq![hash_algorithm] + seq![flags], ser_u16(iterations));
            lemma_u16_roundtrip(x, 2, iterations);
            assert(b[0] == x[0] && b[1] == x[1] && b[2] == x[2] && b[3] == x[3]);
            lemma_cstring_rt(b, 4, l, salt);
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_rt_tlsa(s: SpecRdata, t: u16)
    requires
        rdata_ok(s, t),
        s is Tlsa,
    ensures
        decodes_to(ser_rdata(s), t, s),
{
    let b = ser_rdata(s);
    let l = b.len() as int;
    lemma_at_whole(b);
    assert(b.subrange(0, l) =~= b);
    match s {
        SpecRdata::Tlsa { usage, selector, matching, data } => {
            lemma_cat(b, seq![usage] + seq![selector] + seq![matching], data);
            assert(b.subrange(3, l) =~= data);
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_rt_opt(s: SpecRdata, t: u16)
    requires
        rdata_ok(s, t),
        s is Opt,
    ensures
        decodes_to(ser_rdata(s), t, s),
{
    let b = ser_rdata(s);
    let l = b.len() as int;
    lemma_at_whole(b);
    assert(b.subrange(0, l) =~= b);
    match s {
        SpecRdata::Opt(v) => {
            lemma_kvs_rt(b, 0, l, v, false, -1);
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_rt_svcb(s: SpecRdata, t: u16)
    requires
        rdata_ok(s, t),
        s is Svcb,
    ensures
        decodes_to(ser_rdata(s), t, s),
{
    let b = ser_rdata(s);
    let l = b.len() as int;
    lemma_at_whole(b);
    assert(b.subrange(0, l) =~= b);
    match s {
        SpecRdata::Svcb { priority, target, params } => {
            assert(b =~= ser_u16(priority) + (ser_name(target) + ser_kvs(params)));
            lemma_cat(b, ser_u16(priority), ser_name(target) + ser_kvs(params));
            lemma_at_split(b, 2, ser_name(target), ser_kvs(params));
            lemma_u16_roundtrip(b, 0, priority);
            lemma_plain_rt(b, 2, l, target);
            lemma_kvs_rt(b, 2 + ser_name(target).len() as int, l, params, true, -1);
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_rt_https(s: SpecRdata, t: u16)
    requires
        rdata_ok(s, t),
        s is Https,
    ensures
        decodes_to(ser_rdata(s), t, s),
{
    let b = ser_rdata(s);
    let l = b.len() as int;
    lemma_at_whole(b);
    assert(b.subrange(0, l) =~= b);
    match s {
        SpecRdata::Https { priority, target, params } => {
            assert(b =~= ser_u16(priority) + (ser_name(target) + ser_kvs(params)));
            lemma_cat(b, ser_u16(priority), ser_name(target) + ser_kvs(params));
            lemma_at_split(b, 2, ser_name(target), ser_kvs(params));
            lemma_u16_roundtrip(b, 0, priority);
            lemma_plain_rt(b, 2, l, target);
            lemma_kvs_rt(b, 2 + ser_name(target).len() as int, l, params, true, -1);
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_rt_uri(s: SpecRdata, t: u16)
    requires
        rdata_ok(s, t),
        s is Uri,
    ensures
        decodes_to(ser_rdata(s), t, s),
{
    let b = ser_rdata(s);
    let l = b.len() as int;
    lemma_at_whole(b);
    assert(b.subrange(0, l) =~= b);
    match s {
        SpecRdata::Uri { priority, weight, target } => {
            let x = ser_u16(priority) + ser_u16(weight);
            lemma_cat(b, x, target);
            lemma_cat(x, ser_u16(priority), ser_u16(weight));
            assert(b[0] == x[0] && b[1] == x[1] && b[2] == x[2] && b[3] == x[3]);
            lemma_u16_roundtrip(x, 0, priority);
            lemma_u16_roundtrip(x, 2, weight);
            assert(b.subrange(4, l) =~= target);
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_rt_caa(s: SpecRdata, t: u16)
    requires
        rdata_ok(s, t),
        s is Caa,
    ensures
        decodes_to(ser_rdata(s), t, s),
{
    let b = ser_rdata(s);
    let l = b.len() as int;
    lemma_at_whole(b);
    assert(b.subrange(0, l) =~= b);
    match s {
        SpecRdata::Caa { flags, tag, value } => {
            let x = seq![flags] + seq![tag.len() as u8];
            assert(b =~= x + (tag + value));
            lemma_cat(b, x, tag + value);
            lemma_at_split(b, 2, tag, value);
            assert(b[0] == flags && b[1] == tag.len() as u8);
            assert forall|i: int| 2 <= i < 2 + tag.len() implies is_alnum(#[trigger] b[i]) by {
                assert(b[i] == b.subrange(2, 2 + tag.len() as int)[i - 2]);
                assert(is_alnum(tag[i - 2]));
            }
            assert(b.subrange(2, 2 + tag.len() as int) =~= tag);
            assert(b.subrange(2 + tag.len() as int, l) =~= value);
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_rt_other(s: SpecRdata, t: u16)
    requires
        rdata_ok(s, t),
        s is A || s is Aaaa || s is Unknown,
    ensures
        decodes_to(ser_rdata(s), t, s),
{
    let b = ser_rdata(s);
    assert(b.subrange(0, b.len() as int) =~= b);
}

/// **Encoding round trip**: RDATA written by `ser_rdata` decodes back to
/// exactly the fields it was written from, and is already canonical.
#[verifier::spinoff_prover]
pub proof fn theorem_rdata_encode(s: SpecRdata, t: u16)
    requires
        rdata_ok(s, t),
    ensures
        decodes_to(ser_rdata(s), t, s),
{
    match s {
        SpecRdata::Ns(..) => lemma_rt_ns(s, t),
        SpecRdata::Cname(..) => lemma_rt_cname(s, t),
        SpecRdata::Ptr(..) => lemma_rt_ptr(s, t),
        SpecRdata::Mx { .. } => lemma_rt_mx(s, t),
        SpecRdata::Srv { .. } => lemma_rt_srv(s, t),
        SpecRdata::Soa { .. } => lemma_rt_soa(s, t),
        SpecRdata::Sig { .. } => lemma_rt_sig(s, t),
        SpecRdata::Rrsig { .. } => lemma_rt_rrsig(s, t),
        SpecRdata::Txt(..) => lemma_rt_txt(s, t),
        SpecRdata::Hinfo { .. } => lemma_rt_hinfo(s, t),
        SpecRdata::Naptr { .. } => lemma_rt_naptr(s, t),
        SpecRdata::Ds { .. } => lemma_rt_ds(s, t),
        SpecRdata::Sshfp { .. } => lemma_rt_sshfp(s, t),
        SpecRdata::Nsec { .. } => lemma_rt_nsec(s, t),
        SpecRdata::Dnskey { .. } => lemma_rt_dnskey(s, t),
        SpecRdata::Nsec3 { .. } => lemma_rt_nsec3(s, t),
        SpecRdata::Nsec3param { .. } => lemma_rt_nsec3param(s, t),
        SpecRdata::Tlsa { .. } => lemma_rt_tlsa(s, t),
        SpecRdata::Opt(..) => lemma_rt_opt(s, t),
        SpecRdata::Svcb { .. } => lemma_rt_svcb(s, t),
        SpecRdata::Https { .. } => lemma_rt_https(s, t),
        SpecRdata::Uri { .. } => lemma_rt_uri(s, t),
        SpecRdata::Caa { .. } => lemma_rt_caa(s, t),
        _ => lemma_rt_other(s, t),
    }
}

// ---------------------------------------------------------------------------
// The encoder
// ---------------------------------------------------------------------------

proof fn lemma_cstrings_push(v: Seq<Seq<u8>>, x: Seq<u8>)
    ensures
        ser_cstrings(v.push(x)) == ser_cstrings(v) + ser_cstring(x),
    decreases v.len(),
{
    let w = v.push(x);
    assert(w[0] == if v.len() == 0 { x } else { v[0] });
    if v.len() == 0 {
        assert(w.drop_first() =~= Seq::<Seq<u8>>::empty());
        assert(ser_cstrings(w.drop_first()) == Seq::<u8>::empty());
        assert(ser_cstrings(v) == Seq::<u8>::empty());
        assert(ser_cstrings(w) =~= ser_cstrings(v) + ser_cstring(x));
    } else {
        assert(w.drop_first() =~= v.drop_first().push(x));
        lemma_cstrings_push(v.drop_first(), x);
        assert(ser_cstrings(w) == ser_cstring(v[0]) + (ser_cstrings(v.drop_first()) + ser_cstring(x)));
        assert(ser_cstrings(w) =~= ser_cstrings(v) + ser_cstring(x));
    }
}

proof fn lemma_kvs_push(v: Seq<(u16, Seq<u8>)>, x: (u16, Seq<u8>))
    ensures
        ser_kvs(v.push(x)) == ser_kvs(v) + ser_kv(x),
    decreases v.len(),
{
    let w = v.push(x);
    assert(w[0] == if v.len() == 0 { x } else { v[0] });
    if v.len() == 0 {
        assert(w.drop_first() =~= Seq::<(u16, Seq<u8>)>::empty());
        assert(ser_kvs(w.drop_first()) == Seq::<u8>::empty());
        assert(ser_kvs(v) == Seq::<u8>::empty());
        assert(ser_kvs(w) =~= ser_kvs(v) + ser_kv(x));
    } else {
        assert(w.drop_first() =~= v.drop_first().push(x));
        lemma_kvs_push(v.drop_first(), x);
        assert(ser_kvs(w) == ser_kv(v[0]) + (ser_kvs(v.drop_first()) + ser_kv(x)));
        assert(ser_kvs(w) =~= ser_kvs(v) + ser_kv(x));
    }
}

/// The last key of `v`, or `prev` if there is none.
pub open spec fn last_key(v: Seq<(u16, Seq<u8>)>, prev: int) -> int {
    if v.len() == 0 {
        prev
    } else {
        v.last().0 as int
    }
}

proof fn lemma_keys_push(v: Seq<(u16, Seq<u8>)>, prev: int, x: (u16, Seq<u8>))
    requires
        keys_above(v, prev),
        x.0 as int > last_key(v, prev),
    ensures
        keys_above(v.push(x), prev),
    decreases v.len(),
{
    let w = v.push(x);
    if v.len() == 0 {
        assert(w.drop_first() =~= Seq::<(u16, Seq<u8>)>::empty());
        assert(keys_above(w.drop_first(), x.0 as int));
        assert(w[0] == x);
    } else {
        assert(w.drop_first() =~= v.drop_first().push(x));
        if v.len() > 1 {
            assert(v.drop_first().last() == v.last());
        }
        lemma_keys_push(v.drop_first(), v[0].0 as int, x);
        assert(w[0] == v[0]);
    }
}

fn put(out: &mut Vec<u8>, x: &[u8])
    ensures
        final(out)@ == old(out)@ + x@,
{
    append(out, x);
}

fn put_u8(out: &mut Vec<u8>, x: u8)
    ensures
        final(out)@ == old(out)@ + seq![x],
{
    out.push(x);
    proof {
        assert(final(out)@ =~= old(out)@ + seq![x]);
    }
}

fn put_u16(out: &mut Vec<u8>, x: u16)
    ensures
        final(out)@ == old(out)@ + ser_u16(x),
{
    out.push((x / 256) as u8);
    out.push((x % 256) as u8);
    proof {
        assert(final(out)@ =~= old(out)@ + ser_u16(x));
    }
}

fn put_u32(out: &mut Vec<u8>, x: u32)
    ensures
        final(out)@ == old(out)@ + ser_u32(x),
{
    out.push((x / 0x100_0000) as u8);
    out.push(((x / 0x1_0000) % 256) as u8);
    out.push(((x / 256) % 256) as u8);
    out.push((x % 256) as u8);
    proof {
        assert(final(out)@ =~= old(out)@ + ser_u32(x));
    }
}

fn name_slice<'b, 'a>(x: &'b NameBytes<'a>) -> (r: &'b [u8])
    ensures
        r@ == x@,
{
    match x {
        NameBytes::Borrowed(s) => *s,
        NameBytes::Owned(v) => v.as_slice(),
    }
}

/// Appends a name after checking that it is a valid uncompressed wire-form
/// name.
fn put_name(out: &mut Vec<u8>, x: &NameBytes) -> (r: Option<Ghost<SpecName>>)
    ensures
        r matches Some(n) ==> valid_name(n@) && x@ == ser_name(n@) && final(out)@ == old(out)@
            + ser_name(n@),
{
    let s = name_slice(x);
    match plain_name_end(s, 0, s.len()) {
        Some((e, n)) => {
            if e != s.len() {
                return None;
            }
            proof {
                assert(s@.subrange(0, s@.len() as int) =~= s@);
            }
            put(out, s);
            Some(n)
        },
        None => None,
    }
}

/// Appends a `<character-string>` if `x` fits one.
fn put_cstring(out: &mut Vec<u8>, x: &[u8]) -> (ok: bool)
    ensures
        ok == cstr_ok(x@),
        ok ==> final(out)@ == old(out)@ + ser_cstring(x@),
{
    if x.len() > 255 {
        return false;
    }
    put_u8(out, x.len() as u8);
    put(out, x);
    proof {
        assert(final(out)@ =~= old(out)@ + ser_cstring(x@));
    }
    true
}

fn put_cstrings(out: &mut Vec<u8>, v: &Vec<&[u8]>) -> (ok: bool)
    ensures
        ok == cstrs_ok(strs_view(v@)),
        ok ==> final(out)@ == old(out)@ + ser_cstrings(strs_view(v@)),
{
    let ghost o = out@;
    let ghost sv = strs_view(v@);
    let mut i: usize = 0;
    proof {
        assert(sv.take(0) =~= Seq::<Seq<u8>>::empty());
        assert(o + ser_cstrings(sv.take(0)) =~= o);
    }
    while i < v.len()
        invariant
            i <= v@.len(),
            sv == strs_view(v@),
            sv.len() == v@.len(),
            cstrs_ok(sv.take(i as int)),
            out@ == o + ser_cstrings(sv.take(i as int)),
        decreases v@.len() - i,
    {
        let ghost before = out@;
        if !put_cstring(out, v[i]) {
            proof {
                assert(!cstr_ok(sv[i as int]));
            }
            return false;
        }
        proof {
            assert(sv[i as int] == v@[i as int]@);
            assert(sv.take(i + 1) =~= sv.take(i as int).push(sv[i as int]));
            lemma_cstrings_push(sv.take(i as int), sv[i as int]);
            assert(cstrs_ok(sv.take(i + 1))) by {
                assert forall|j: int| 0 <= j < i + 1 implies cstr_ok(#[trigger] sv.take(i + 1)[j]) by {
                    if j < i {
                        assert(sv.take(i + 1)[j] == sv.take(i as int)[j]);
                    }
                }
            }
        }
        i += 1;
    }
    proof {
        assert(sv.take(i as int) =~= sv);
    }
    true
}

/// Appends key/value items; with `increasing`, only if each key is above
/// the one before it.
fn put_kvs(out: &mut Vec<u8>, v: &Vec<(u16, &[u8])>, increasing: bool) -> (ok: bool)
    ensures
        ok == (kvs_ok(kvs_view(v@)) && (increasing ==> keys_above(kvs_view(v@), -1))),
        ok ==> final(out)@ == old(out)@ + ser_kvs(kvs_view(v@)),
{
    let ghost o = out@;
    let ghost kv = kvs_view(v@);
    let mut i: usize = 0;
    let mut prev: i32 = -1;
    proof {
        assert(kv.take(0) =~= Seq::<(u16, Seq<u8>)>::empty());
        assert(o + ser_kvs(kv.take(0)) =~= o);
    }
    while i < v.len()
        invariant
            i <= v@.len(),
            kv == kvs_view(v@),
            kv.len() == v@.len(),
            kvs_ok(kv.take(i as int)),
            increasing ==> keys_above(kv.take(i as int), -1),
            prev as int == last_key(kv.take(i as int), -1),
            out@ == o + ser_kvs(kv.take(i as int)),
        decreases v@.len() - i,
    {
        let (k, val) = v[i];
        proof {
            assert(kv[i as int] == (k, val@));
        }
        if val.len() > 65535 {
            proof {
                assert(!kvs_ok(kv)) by {
                    assert(kv[i as int].1.len() > u16::MAX);
                }
            }
            return false;
        }
        if increasing && (k as i32) <= prev {
            proof {
                if keys_above(kv, -1) {
                    lemma_keys_prefix(kv, -1, i as int + 1);
                    lemma_keys_last(kv.take(i + 1), -1, i as int);
                    assert(kv.take(i + 1).take(i as int) =~= kv.take(i as int));
                    assert(kv.take(i + 1)[i as int] == kv[i as int]);
                    assert(false);
                }
            }
            return false;
        }
        put_u16(out, k);
        put_u16(out, val.len() as u16);
        put(out, val);
        proof {
            let x = (k, val@);
            assert(kv.take(i + 1) =~= kv.take(i as int).push(x));
            lemma_kvs_push(kv.take(i as int), x);
            assert(out@ =~= o + ser_kvs(kv.take(i as int)) + ser_kv(x));
            if increasing {
                lemma_keys_push(kv.take(i as int), -1, x);
            }
            assert(kvs_ok(kv.take(i + 1))) by {
                assert forall|j: int| 0 <= j < i + 1 implies (#[trigger] kv.take(i + 1)[j]).1.len()
                    <= u16::MAX by {
                    if j < i {
                        assert(kv.take(i + 1)[j] == kv.take(i as int)[j]);
                    }
                }
            }
        }
        prev = k as i32;
        i += 1;
    }
    proof {
        assert(kv.take(i as int) =~= kv);
    }
    true
}

/// A prefix of keys in increasing order is in increasing order.
proof fn lemma_keys_prefix(v: Seq<(u16, Seq<u8>)>, prev: int, k: int)
    requires
        keys_above(v, prev),
        0 <= k <= v.len(),
    ensures
        keys_above(v.take(k), prev),
    decreases v.len(),
{
    if k > 0 {
        assert(v.take(k).drop_first() =~= v.drop_first().take(k - 1));
        lemma_keys_prefix(v.drop_first(), v[0].0 as int, k - 1);
    }
}

/// In increasing keys, the last is above every earlier one, and the one
/// before it.
proof fn lemma_keys_last(v: Seq<(u16, Seq<u8>)>, prev: int, i: int)
    requires
        keys_above(v, prev),
        0 <= i < v.len(),
    ensures
        v[i].0 as int > last_key(v.take(i), prev),
    decreases v.len(),
{
    if i > 0 {
        lemma_keys_last(v.drop_first(), v[0].0 as int, i - 1);
        if i > 1 {
            assert(v.take(i).last() == v.drop_first().take(i - 1).last());
        }
    }
}

/// The type a typed `Rdata` variant is written under, if `t` is it.
pub open spec fn variant_is(d: Rdata, t: u16) -> bool {
    match d {
        Rdata::A(_) => t == 1,
        Rdata::Aaaa(_) => t == 28,
        Rdata::Ns(_) => t == 2,
        Rdata::Cname(_) => t == 5,
        Rdata::Ptr(_) => t == 12,
        Rdata::Mx { .. } => t == 15,
        Rdata::Txt(_) => t == 16,
        Rdata::Hinfo { .. } => t == 13,
        Rdata::Soa { .. } => t == 6,
        Rdata::Sig { .. } => t == 24,
        Rdata::Rrsig { .. } => t == 46,
        Rdata::Ds { .. } => t == 43,
        Rdata::Sshfp { .. } => t == 44,
        Rdata::Nsec { .. } => t == 47,
        Rdata::Dnskey { .. } => t == 48,
        Rdata::Nsec3 { .. } => t == 50,
        Rdata::Nsec3param { .. } => t == 51,
        Rdata::Srv { .. } => t == 33,
        Rdata::Naptr { .. } => t == 35,
        Rdata::Opt(_) => t == 41,
        Rdata::Tlsa { .. } => t == 52,
        Rdata::Svcb { .. } => t == 64,
        Rdata::Https { .. } => t == 65,
        Rdata::Uri { .. } => t == 256,
        Rdata::Caa { .. } => t == 257,
        Rdata::Unknown(_) => !typed(t),
    }
}

pub fn is_typed(t: u16) -> (r: bool)
    ensures
        r == typed(t),
{
    t == 1 || t == 2 || t == 5 || t == 6 || t == 12 || t == 13 || t == 15 || t == 16 || t == 24
        || t == 28 || t == 33 || t == 35 || t == 41 || t == 43 || t == 44 || t == 46 || t == 47
        || t == 48 || t == 50 || t == 51 || t == 52 || t == 64 || t == 65 || t == 256 || t == 257
}

fn is_alnum_exec(c: u8) -> (r: bool)
    ensures
        r == is_alnum(c),
{
    (48 <= c && c <= 57) || (65 <= c && c <= 90) || (97 <= c && c <= 122)
}

/// Encodes `d` as RDATA of type `t`, names uncompressed (the serializer
/// compresses them where RFC 1035 allows). Refused, with `None`, when `d`
/// is not of type `t` or a field does not fit its encoding: a name that is
/// not a valid wire-form name, a character-string over 255 octets, an
/// option over 65535, SVCB keys out of order, a CAA tag that is not 1 to 15
/// letters and digits, an empty URI target, or no TXT strings.
///
/// Proven: the bytes decode, as RDATA of type `t`, to exactly `d`
/// (`rdata_is`), and are canonical, so a `Message` stores them unchanged.
#[verifier::spinoff_prover]
fn encode_names(d: &Rdata, t: u16) -> (r: Option<(Vec<u8>, Ghost<SpecRdata>)>)
    ensures
        r matches Some((v, s)) ==> {
            &&& rdata_is(*d, s@)
            &&& rdata_ok(s@, t)
            &&& v@ == ser_rdata(s@)
            &&& decodes_to(v@, t, s@)
        },
{
    let mut out: Vec<u8> = Vec::with_capacity(64);
    let ghost e = out@;
    proof {
        assert(e =~= Seq::<u8>::empty());
    }
    let s: Ghost<SpecRdata> = match d {
        Rdata::Ns(x) => {
            if t != 2 {
                return None;
            }
            match put_name(&mut out, x) {
                Some(n) => Ghost(SpecRdata::Ns(n@)),
                None => return None,
            }
        },
        Rdata::Cname(x) => {
            if t != 5 {
                return None;
            }
            match put_name(&mut out, x) {
                Some(n) => Ghost(SpecRdata::Cname(n@)),
                None => return None,
            }
        },
        Rdata::Ptr(x) => {
            if t != 12 {
                return None;
            }
            match put_name(&mut out, x) {
                Some(n) => Ghost(SpecRdata::Ptr(n@)),
                None => return None,
            }
        },
        Rdata::Mx { preference, exchange } => {
            if t != 15 {
                return None;
            }
            put_u16(&mut out, *preference);
            match put_name(&mut out, exchange) {
                Some(n) => Ghost(SpecRdata::Mx { preference: *preference, exchange: n@ }),
                None => return None,
            }
        },
        Rdata::Srv { priority, weight, port, target } => {
            if t != 33 {
                return None;
            }
            put_u16(&mut out, *priority);
            put_u16(&mut out, *weight);
            put_u16(&mut out, *port);
            match put_name(&mut out, target) {
                Some(n) => Ghost(
                    SpecRdata::Srv { priority: *priority, weight: *weight, port: *port, target: n@ },
                ),
                None => return None,
            }
        },
        Rdata::Soa { mname, rname, serial, refresh, retry, expire, minimum } => {
            if t != 6 {
                return None;
            }
            let n1 = match put_name(&mut out, mname) {
                Some(n) => n,
                None => return None,
            };
            let n2 = match put_name(&mut out, rname) {
                Some(n) => n,
                None => return None,
            };
            put_u32(&mut out, *serial);
            put_u32(&mut out, *refresh);
            put_u32(&mut out, *retry);
            put_u32(&mut out, *expire);
            put_u32(&mut out, *minimum);
            Ghost(
                SpecRdata::Soa {
                    mname: n1@,
                    rname: n2@,
                    serial: *serial,
                    refresh: *refresh,
                    retry: *retry,
                    expire: *expire,
                    minimum: *minimum,
                },
            )
        },
        _ => return None,
    };
    proof {
        assert(out@ =~= ser_rdata(s@));
        theorem_rdata_encode(s@, t);
    }
    Some((out, s))
}

#[verifier::spinoff_prover]
fn encode_sigs(d: &Rdata, t: u16) -> (r: Option<(Vec<u8>, Ghost<SpecRdata>)>)
    ensures
        r matches Some((v, s)) ==> {
            &&& rdata_is(*d, s@)
            &&& rdata_ok(s@, t)
            &&& v@ == ser_rdata(s@)
            &&& decodes_to(v@, t, s@)
        },
{
    let mut out: Vec<u8> = Vec::with_capacity(64);
    let ghost e = out@;
    proof {
        assert(e =~= Seq::<u8>::empty());
    }
    let s: Ghost<SpecRdata> = match d {
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
        } => {
            if t != 24 {
                return None;
            }
            put_sig_fixed(&mut out, *type_covered, *algorithm, *labels, *original_ttl, *expiration, *inception, *key_tag);
            let n = match put_name(&mut out, signer) {
                Some(n) => n,
                None => return None,
            };
            put(&mut out, signature);
            Ghost(
                SpecRdata::Sig {
                    type_covered: *type_covered,
                    algorithm: *algorithm,
                    labels: *labels,
                    original_ttl: *original_ttl,
                    expiration: *expiration,
                    inception: *inception,
                    key_tag: *key_tag,
                    signer: n@,
                    signature: signature@,
                },
            )
        },
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
        } => {
            if t != 46 {
                return None;
            }
            put_sig_fixed(&mut out, *type_covered, *algorithm, *labels, *original_ttl, *expiration, *inception, *key_tag);
            let n = match put_name(&mut out, signer) {
                Some(n) => n,
                None => return None,
            };
            put(&mut out, signature);
            Ghost(
                SpecRdata::Rrsig {
                    type_covered: *type_covered,
                    algorithm: *algorithm,
                    labels: *labels,
                    original_ttl: *original_ttl,
                    expiration: *expiration,
                    inception: *inception,
                    key_tag: *key_tag,
                    signer: n@,
                    signature: signature@,
                },
            )
        },
        _ => return None,
    };
    proof {
        assert(out@ =~= ser_rdata(s@));
        theorem_rdata_encode(s@, t);
    }
    Some((out, s))
}

#[verifier::spinoff_prover]
fn encode_strings(d: &Rdata, t: u16) -> (r: Option<(Vec<u8>, Ghost<SpecRdata>)>)
    ensures
        r matches Some((v, s)) ==> {
            &&& rdata_is(*d, s@)
            &&& rdata_ok(s@, t)
            &&& v@ == ser_rdata(s@)
            &&& decodes_to(v@, t, s@)
        },
{
    let mut out: Vec<u8> = Vec::with_capacity(64);
    let ghost e = out@;
    proof {
        assert(e =~= Seq::<u8>::empty());
    }
    let s: Ghost<SpecRdata> = match d {
        Rdata::Txt(v) => {
            if t != 16 || v.len() == 0 {
                return None;
            }
            if !put_cstrings(&mut out, v) {
                return None;
            }
            Ghost(SpecRdata::Txt(strs_view(v@)))
        },
        Rdata::Hinfo { cpu, os } => {
            if t != 13 || !put_cstring(&mut out, cpu) || !put_cstring(&mut out, os) {
                return None;
            }
            Ghost(SpecRdata::Hinfo { cpu: cpu@, os: os@ })
        },
        Rdata::Naptr { order, preference, flags, services, regexp, replacement } => {
            if t != 35 {
                return None;
            }
            put_u16(&mut out, *order);
            put_u16(&mut out, *preference);
            if !put_cstring(&mut out, flags) || !put_cstring(&mut out, services) || !put_cstring(
                &mut out,
                regexp,
            ) {
                return None;
            }
            match put_name(&mut out, replacement) {
                Some(n) => Ghost(
                    SpecRdata::Naptr {
                        order: *order,
                        preference: *preference,
                        flags: flags@,
                        services: services@,
                        regexp: regexp@,
                        replacement: n@,
                    },
                ),
                None => return None,
            }
        },
        Rdata::Opt(v) => {
            if t != 41 || !put_kvs(&mut out, v, false) {
                return None;
            }
            Ghost(SpecRdata::Opt(kvs_view(v@)))
        },
        _ => return None,
    };
    proof {
        assert(out@ =~= ser_rdata(s@));
        theorem_rdata_encode(s@, t);
    }
    Some((out, s))
}

#[verifier::spinoff_prover]
fn encode_dnssec(d: &Rdata, t: u16) -> (r: Option<(Vec<u8>, Ghost<SpecRdata>)>)
    ensures
        r matches Some((v, s)) ==> {
            &&& rdata_is(*d, s@)
            &&& rdata_ok(s@, t)
            &&& v@ == ser_rdata(s@)
            &&& decodes_to(v@, t, s@)
        },
{
    let mut out: Vec<u8> = Vec::with_capacity(64);
    let ghost e = out@;
    proof {
        assert(e =~= Seq::<u8>::empty());
    }
    let s: Ghost<SpecRdata> = match d {
        Rdata::Ds { key_tag, algorithm, digest_type, digest } => {
            if t != 43 {
                return None;
            }
            put_u16(&mut out, *key_tag);
            put_u8(&mut out, *algorithm);
            put_u8(&mut out, *digest_type);
            put(&mut out, digest);
            Ghost(
                SpecRdata::Ds {
                    key_tag: *key_tag,
                    algorithm: *algorithm,
                    digest_type: *digest_type,
                    digest: digest@,
                },
            )
        },
        Rdata::Sshfp { algorithm, fp_type, fingerprint } => {
            if t != 44 {
                return None;
            }
            put_u8(&mut out, *algorithm);
            put_u8(&mut out, *fp_type);
            put(&mut out, fingerprint);
            Ghost(
                SpecRdata::Sshfp {
                    algorithm: *algorithm,
                    fp_type: *fp_type,
                    fingerprint: fingerprint@,
                },
            )
        },
        Rdata::Nsec { next, type_bitmaps } => {
            if t != 47 {
                return None;
            }
            let n = match put_name(&mut out, next) {
                Some(n) => n,
                None => return None,
            };
            put(&mut out, type_bitmaps);
            Ghost(SpecRdata::Nsec { next: n@, type_bitmaps: type_bitmaps@ })
        },
        Rdata::Dnskey { flags, protocol, algorithm, public_key } => {
            if t != 48 {
                return None;
            }
            put_u16(&mut out, *flags);
            put_u8(&mut out, *protocol);
            put_u8(&mut out, *algorithm);
            put(&mut out, public_key);
            Ghost(
                SpecRdata::Dnskey {
                    flags: *flags,
                    protocol: *protocol,
                    algorithm: *algorithm,
                    public_key: public_key@,
                },
            )
        },
        Rdata::Nsec3 { hash_algorithm, flags, iterations, salt, next_hashed, type_bitmaps } => {
            if t != 50 {
                return None;
            }
            put_u8(&mut out, *hash_algorithm);
            put_u8(&mut out, *flags);
            put_u16(&mut out, *iterations);
            if !put_cstring(&mut out, salt) || !put_cstring(&mut out, next_hashed) {
                return None;
            }
            put(&mut out, type_bitmaps);
            Ghost(
                SpecRdata::Nsec3 {
                    hash_algorithm: *hash_algorithm,
                    flags: *flags,
                    iterations: *iterations,
                    salt: salt@,
                    next_hashed: next_hashed@,
                    type_bitmaps: type_bitmaps@,
                },
            )
        },
        Rdata::Nsec3param { hash_algorithm, flags, iterations, salt } => {
            if t != 51 {
                return None;
            }
            put_u8(&mut out, *hash_algorithm);
            put_u8(&mut out, *flags);
            put_u16(&mut out, *iterations);
            if !put_cstring(&mut out, salt) {
                return None;
            }
            Ghost(
                SpecRdata::Nsec3param {
                    hash_algorithm: *hash_algorithm,
                    flags: *flags,
                    iterations: *iterations,
                    salt: salt@,
                },
            )
        },
        Rdata::Tlsa { usage, selector, matching, data } => {
            if t != 52 {
                return None;
            }
            put_u8(&mut out, *usage);
            put_u8(&mut out, *selector);
            put_u8(&mut out, *matching);
            put(&mut out, data);
            Ghost(
                SpecRdata::Tlsa {
                    usage: *usage,
                    selector: *selector,
                    matching: *matching,
                    data: data@,
                },
            )
        },
        _ => return None,
    };
    proof {
        assert(out@ =~= ser_rdata(s@));
        theorem_rdata_encode(s@, t);
    }
    Some((out, s))
}

#[verifier::spinoff_prover]
fn encode_other(d: &Rdata, t: u16) -> (r: Option<(Vec<u8>, Ghost<SpecRdata>)>)
    ensures
        r matches Some((v, s)) ==> {
            &&& rdata_is(*d, s@)
            &&& rdata_ok(s@, t)
            &&& v@ == ser_rdata(s@)
            &&& decodes_to(v@, t, s@)
        },
{
    let mut out: Vec<u8> = Vec::with_capacity(64);
    let ghost e = out@;
    proof {
        assert(e =~= Seq::<u8>::empty());
    }
    let s: Ghost<SpecRdata> = match d {
        Rdata::A(x) => {
            if t != 1 || x.len() != 4 {
                return None;
            }
            put(&mut out, x);
            Ghost(SpecRdata::A(x@))
        },
        Rdata::Aaaa(x) => {
            if t != 28 || x.len() != 16 {
                return None;
            }
            put(&mut out, x);
            Ghost(SpecRdata::Aaaa(x@))
        },
        Rdata::Svcb { priority, target, params } => {
            if t != 64 {
                return None;
            }
            put_u16(&mut out, *priority);
            let n = match put_name(&mut out, target) {
                Some(n) => n,
                None => return None,
            };
            if !put_kvs(&mut out, params, true) {
                return None;
            }
            Ghost(SpecRdata::Svcb { priority: *priority, target: n@, params: kvs_view(params@) })
        },
        Rdata::Https { priority, target, params } => {
            if t != 65 {
                return None;
            }
            put_u16(&mut out, *priority);
            let n = match put_name(&mut out, target) {
                Some(n) => n,
                None => return None,
            };
            if !put_kvs(&mut out, params, true) {
                return None;
            }
            Ghost(SpecRdata::Https { priority: *priority, target: n@, params: kvs_view(params@) })
        },
        Rdata::Uri { priority, weight, target } => {
            if t != 256 || target.len() == 0 {
                return None;
            }
            put_u16(&mut out, *priority);
            put_u16(&mut out, *weight);
            put(&mut out, target);
            Ghost(SpecRdata::Uri { priority: *priority, weight: *weight, target: target@ })
        },
        Rdata::Caa { flags, tag, value } => {
            if t != 257 || tag.len() == 0 || tag.len() > 15 {
                return None;
            }
            let mut i: usize = 0;
            while i < tag.len()
                invariant
                    i <= tag@.len(),
                    forall|j: int| 0 <= j < i ==> is_alnum(#[trigger] tag@[j]),
                decreases tag@.len() - i,
            {
                if !is_alnum_exec(tag[i]) {
                    return None;
                }
                i += 1;
            }
            put_u8(&mut out, *flags);
            put_u8(&mut out, tag.len() as u8);
            put(&mut out, tag);
            put(&mut out, value);
            Ghost(SpecRdata::Caa { flags: *flags, tag: tag@, value: value@ })
        },
        Rdata::Unknown(x) => {
            if is_typed(t) {
                return None;
            }
            put(&mut out, x);
            Ghost(SpecRdata::Unknown(x@))
        },
        _ => return None,
    };
    proof {
        assert(out@ =~= ser_rdata(s@));
        theorem_rdata_encode(s@, t);
    }
    Some((out, s))
}

pub fn encode_rdata(d: &Rdata, t: u16) -> (r: Option<(Vec<u8>, Ghost<SpecRdata>)>)
    ensures
        r matches Some((v, s)) ==> {
            &&& rdata_is(*d, s@)
            &&& rdata_ok(s@, t)
            &&& v@ == ser_rdata(s@)
            &&& decodes_to(v@, t, s@)
        },
{
    match d {
        Rdata::Ns(..) => encode_names(d, t),
        Rdata::Cname(..) => encode_names(d, t),
        Rdata::Ptr(..) => encode_names(d, t),
        Rdata::Mx { .. } => encode_names(d, t),
        Rdata::Srv { .. } => encode_names(d, t),
        Rdata::Soa { .. } => encode_names(d, t),
        Rdata::Sig { .. } => encode_sigs(d, t),
        Rdata::Rrsig { .. } => encode_sigs(d, t),
        Rdata::Txt(..) => encode_strings(d, t),
        Rdata::Hinfo { .. } => encode_strings(d, t),
        Rdata::Naptr { .. } => encode_strings(d, t),
        Rdata::Opt(..) => encode_strings(d, t),
        Rdata::Ds { .. } => encode_dnssec(d, t),
        Rdata::Sshfp { .. } => encode_dnssec(d, t),
        Rdata::Nsec { .. } => encode_dnssec(d, t),
        Rdata::Dnskey { .. } => encode_dnssec(d, t),
        Rdata::Nsec3 { .. } => encode_dnssec(d, t),
        Rdata::Nsec3param { .. } => encode_dnssec(d, t),
        Rdata::Tlsa { .. } => encode_dnssec(d, t),
        Rdata::A(..) => encode_other(d, t),
        Rdata::Aaaa(..) => encode_other(d, t),
        Rdata::Svcb { .. } => encode_other(d, t),
        Rdata::Https { .. } => encode_other(d, t),
        Rdata::Uri { .. } => encode_other(d, t),
        Rdata::Caa { .. } => encode_other(d, t),
        Rdata::Unknown(..) => encode_other(d, t),
    }
}

fn put_sig_fixed(
    out: &mut Vec<u8>,
    tc: u16,
    alg: u8,
    lab: u8,
    ottl: u32,
    exp: u32,
    inc: u32,
    kt: u16,
)
    ensures
        final(out)@ == old(out)@ + ser_sig_fixed(tc, alg, lab, ottl, exp, inc, kt),
{
    put_u16(out, tc);
    put_u8(out, alg);
    put_u8(out, lab);
    put_u32(out, ottl);
    put_u32(out, exp);
    put_u32(out, inc);
    put_u16(out, kt);
    proof {
        assert(final(out)@ =~= old(out)@ + ser_sig_fixed(tc, alg, lab, ottl, exp, inc, kt));
    }
}

// ---------------------------------------------------------------------------
// TXT strings longer than a <character-string>
// ---------------------------------------------------------------------------

/// A string as 255-octet pieces, the last one shorter (and the empty string
/// as one empty piece).
pub open spec fn chunks255(s: Seq<u8>) -> Seq<Seq<u8>>
    decreases s.len(),
{
    if s.len() <= 255 {
        seq![s]
    } else {
        seq![s.take(255)] + chunks255(s.skip(255))
    }
}

/// Every string's pieces, in order.
pub open spec fn txt_split(v: Seq<Seq<u8>>) -> Seq<Seq<u8>>
    decreases v.len(),
{
    if v.len() == 0 {
        Seq::empty()
    } else {
        txt_split(v.drop_last()) + chunks255(v.last())
    }
}

/// Splits each string into `<character-string>`-sized pieces, as c-ares
/// writes TXT strings longer than 255 octets.
pub fn split_txt<'a>(strs: &Vec<&'a [u8]>) -> (r: Vec<&'a [u8]>)
    ensures
        strs_view(r@) == txt_split(strs_view(strs@)),
{
    let ghost sv = strs_view(strs@);
    let mut r: Vec<&'a [u8]> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(sv.take(0) =~= Seq::<Seq<u8>>::empty());
        assert(strs_view(r@) =~= Seq::<Seq<u8>>::empty());
    }
    while i < strs.len()
        invariant
            i <= strs@.len(),
            sv == strs_view(strs@),
            sv.len() == strs@.len(),
            strs_view(r@) == txt_split(sv.take(i as int)),
        decreases strs@.len() - i,
    {
        let s: &'a [u8] = strs[i];
        let ghost base = strs_view(r@);
        let mut j: usize = 0;
        proof {
            assert(s@.skip(0) =~= s@);
            assert(base + chunks255(s@.skip(0)) =~= base + chunks255(s@));
        }
        while s.len() - j > 255
            invariant
                j <= s@.len(),
                strs_view(r@) + chunks255(s@.skip(j as int)) == base + chunks255(s@),
            decreases s@.len() - j,
        {
            let ghost r0 = r@;
            let piece = slice_subrange(s, j, j + 255);
            r.push(piece);
            proof {
                let t = s@.skip(j as int);
                assert(piece@ =~= t.take(255));
                assert(t.skip(255) =~= s@.skip(j + 255));
                assert(strs_view(r@) =~= strs_view(r0).push(piece@));
                assert(strs_view(r@) + chunks255(s@.skip(j + 255)) =~= strs_view(r0) + chunks255(t));
            }
            j += 255;
        }
        let ghost r0 = r@;
        let piece = slice_subrange(s, j, s.len());
        r.push(piece);
        proof {
            assert(piece@ =~= s@.skip(j as int));
            assert(strs_view(r@) =~= strs_view(r0).push(piece@));
            assert(chunks255(s@.skip(j as int)) == seq![piece@]);
            assert(strs_view(r@) =~= strs_view(r0) + chunks255(s@.skip(j as int)));
        }
        proof {
            assert(sv[i as int] == s@);
            assert(sv.take(i + 1).drop_last() =~= sv.take(i as int));
            assert(sv.take(i + 1).last() == sv[i as int]);
        }
        i += 1;
    }
    proof {
        assert(sv.take(i as int) =~= sv);
    }
    r
}

// ---------------------------------------------------------------------------
// Header and OPT bit layouts
// ---------------------------------------------------------------------------

/// RFC 1035 §4.1.1 (with RFC 4035 §3.2's AD and CD in two of the Z bits):
/// QR is bit 15, Opcode bits 11 to 14, AA 10, TC 9, RD 8, RA 7, the
/// remaining Z bit 6, AD 5, CD 4 and RCODE bits 0 to 3.
pub open spec fn header_word(
    qr: bool,
    opcode: u16,
    aa: bool,
    tc: bool,
    rd: bool,
    ra: bool,
    ad: bool,
    cd: bool,
    rcode: u16,
) -> int {
    (if qr { 0x8000int } else { 0 }) + (opcode % 16) as int * 0x800 + (if aa { 0x400int } else { 0 })
        + (if tc { 0x200int } else { 0 }) + (if rd { 0x100int } else { 0 }) + (if ra { 0x80int } else {
        0
    }) + (if ad { 0x20int } else { 0 }) + (if cd { 0x10int } else { 0 }) + (rcode % 16) as int
}

/// c-ares's flag bits (`ares_dns_flags_t`): QR 1, AA 2, TC 4, RD 8, RA 16,
/// AD 32, CD 64.
pub open spec fn has(f: u16, bit: u16) -> bool {
    f & bit != 0
}

/// The header's second 16-bit word for c-ares flags `f`, an opcode and the
/// low four RCODE bits.
pub fn header_flags(f: u16, opcode: u16, rcode: u16) -> (r: u16)
    ensures
        r as int == header_word(
            has(f, 1),
            opcode,
            has(f, 2),
            has(f, 4),
            has(f, 8),
            has(f, 16),
            has(f, 32),
            has(f, 64),
            rcode,
        ),
{
    let qr: u16 = if f & 1 != 0 { 0x8000 } else { 0 };
    let aa: u16 = if f & 2 != 0 { 0x400 } else { 0 };
    let tc: u16 = if f & 4 != 0 { 0x200 } else { 0 };
    let rd: u16 = if f & 8 != 0 { 0x100 } else { 0 };
    let ra: u16 = if f & 16 != 0 { 0x80 } else { 0 };
    let ad: u16 = if f & 32 != 0 { 0x20 } else { 0 };
    let cd: u16 = if f & 64 != 0 { 0x10 } else { 0 };
    qr + (opcode % 16) * 0x800 + aa + tc + rd + ra + ad + cd + rcode % 16
}

/// RFC 6891 §6.1.3: the OPT record's TTL holds the upper eight bits of the
/// extended RCODE, the version, and the 16 flag bits.
pub open spec fn opt_ttl_word(ext_rcode: u8, version: u8, flags: u16) -> int {
    ext_rcode as int * 0x100_0000 + version as int * 0x1_0000 + flags as int
}

pub fn opt_ttl(ext_rcode: u8, version: u8, flags: u16) -> (r: u32)
    ensures
        r as int == opt_ttl_word(ext_rcode, version, flags),
        ser_u32(r) == seq![ext_rcode, version] + ser_u16(flags),
{
    let r = (ext_rcode as u32) * 0x100_0000 + (version as u32) * 0x1_0000 + flags as u32;
    proof {
        let (e, v, f) = (ext_rcode as int, version as int, flags as int);
        let x = r as int;
        assert(x / 0x100_0000 == e) by (nonlinear_arith)
            requires x == e * 0x100_0000 + v * 0x1_0000 + f, 0 <= e < 256, 0 <= v < 256, 0 <= f < 0x1_0000;
        assert((x / 0x1_0000) % 256 == v) by (nonlinear_arith)
            requires x == e * 0x100_0000 + v * 0x1_0000 + f, 0 <= e < 256, 0 <= v < 256, 0 <= f < 0x1_0000;
        assert((x / 256) % 256 == f / 256) by (nonlinear_arith)
            requires x == e * 0x100_0000 + v * 0x1_0000 + f, 0 <= e < 256, 0 <= v < 256, 0 <= f < 0x1_0000;
        assert(x % 256 == f % 256) by (nonlinear_arith)
            requires x == e * 0x100_0000 + v * 0x1_0000 + f, 0 <= e < 256, 0 <= v < 256, 0 <= f < 0x1_0000;
        assert(ser_u32(r) =~= seq![ext_rcode, version] + ser_u16(flags));
    }
    r
}

} // verus!
