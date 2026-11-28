//! The specification of DNSSEC validation (RFC 4033, 4034, 4035, 5155,
//! 6840): when an RRset counts as signed by a key, when a key counts as
//! trusted from the configured trust anchors, and what proves that a name
//! or a type does not exist, or that a zone is not signed. Every verified
//! function of the validator is proven against these definitions; with
//! `spec.rs` this is the file to read to check the claims.
//!
//! Names are uncompressed wire form, as in `spec.rs`. "Lowercase" is
//! ASCII lowercase (`spec::lower`); since label length octets are below
//! `A`, lowercasing a name's wire form lowercases its labels (RFC 4034
//! §6.2).
//!
//! What is trusted beyond this file: `sig_valid`, the signature check
//! (aws-lc, `crypto.rs`), and verilith-sha2's and `sha1.rs`'s
//! specifications of the hashes.
#[cfg(verus_only)]
use crate::sha1::sha1;
use crate::spec::*;
use vstd::prelude::*;

verus! {

pub const TYPE_SOA_: u16 = 6;
pub const TYPE_DNAME: u16 = 39;
pub const TYPE_RRSIG: u16 = 46;
pub const TYPE_NSEC: u16 = 47;
pub const TYPE_DNSKEY: u16 = 48;
pub const TYPE_NSEC3: u16 = 50;

/// The algorithms validated (RFC 8624 §3.1, as updated by RFC 9905: no
/// SHA-1 signatures): RSA/SHA-256, RSA/SHA-512, ECDSA P-256/SHA-256,
/// ECDSA P-384/SHA-384, Ed25519.
pub open spec fn alg_supported(a: u8) -> bool {
    a == 8 || a == 10 || a == 13 || a == 14 || a == 15
}

/// DS digest types (RFC 4034 §5.1.3, RFC 4509, RFC 6605): SHA-1,
/// SHA-256, SHA-384.
pub open spec fn digest_supported(d: u8) -> bool {
    d == 1 || d == 2 || d == 4
}

/// NSEC3 records with more iterations than this are not used (RFC 9276
/// §3.2; Unbound and BIND use the same limit).
pub const MAX_NSEC3_ITERATIONS: u16 = 150;

// ---------------------------------------------------------------------------
// Bytes and names
// ---------------------------------------------------------------------------

pub open spec fn u16_at(b: Seq<u8>, i: int) -> u16 {
    (b[i] as int * 256 + b[i + 1] as int) as u16
}

pub open spec fn u32_at(b: Seq<u8>, i: int) -> u32 {
    (b[i] as int * 0x100_0000 + b[i + 1] as int * 0x1_0000 + b[i + 2] as int * 0x100 + b[i + 3] as int) as u32
}

pub open spec fn be16(x: u16) -> Seq<u8> {
    seq![(x / 256) as u8, (x % 256) as u8]
}

pub open spec fn be32(x: u32) -> Seq<u8> {
    seq![(x / 0x100_0000) as u8, ((x / 0x1_0000) % 256) as u8, ((x / 0x100) % 256) as u8, (x % 256) as u8]
}

/// `s` lowercased.
pub open spec fn lower_seq(s: Seq<u8>) -> Seq<u8> {
    Seq::new(s.len(), |i: int| lower(s[i]))
}

/// The length of the uncompressed wire-form name at `b[off..]`, if one
/// starts there (labels of at most 63 octets, ending in the root label).
pub open spec fn name_len(b: Seq<u8>, off: int) -> Option<int>
    decreases b.len() - off,
{
    if off < 0 || off >= b.len() {
        None
    } else if b[off] == 0 {
        Some(1)
    } else if b[off] > 63 || off + 1 + b[off] >= b.len() {
        None
    } else {
        match name_len(b, off + 1 + b[off]) {
            Some(l) => Some(l + 1 + b[off]),
            None => None,
        }
    }
}

/// `n` is one name in wire form, and nothing more.
pub open spec fn is_name(n: Seq<u8>) -> bool {
    name_len(n, 0) == Some(n.len() as int)
}

/// The number of labels of the name at `n[off..]`, the root not counted.
pub open spec fn labels_from(n: Seq<u8>, off: int) -> nat
    decreases n.len() - off,
{
    if off < 0 || off >= n.len() || n[off] == 0 || off + 1 + n[off] >= n.len() {
        0
    } else {
        1 + labels_from(n, off + 1 + n[off])
    }
}

pub open spec fn label_count(n: Seq<u8>) -> nat {
    labels_from(n, 0)
}

/// The name begins with the wildcard label `*` (RFC 4592).
pub open spec fn is_wild(n: Seq<u8>) -> bool {
    n.len() >= 2 && n[0] == 1 && n[1] == 42
}

/// The labels an RRSIG's Labels field counts: the root and a leading `*`
/// not counted (RFC 4034 §3.1.3).
pub open spec fn sig_label_count(n: Seq<u8>) -> nat {
    if is_wild(n) && label_count(n) > 0 {
        (label_count(n) - 1) as nat
    } else {
        label_count(n)
    }
}

/// The offset in `n` after its first `k` labels, from `off`.
pub open spec fn skip_labels(n: Seq<u8>, off: int, k: nat) -> int
    decreases k,
{
    if k == 0 || off < 0 || off >= n.len() || n[off] == 0 || off + 1 + n[off] >= n.len() {
        off
    } else {
        skip_labels(n, off + 1 + n[off], (k - 1) as nat)
    }
}

/// The ancestor of `n` with `k` labels (`n` itself if it has no more).
pub open spec fn suffix(n: Seq<u8>, k: nat) -> Seq<u8> {
    if label_count(n) <= k {
        n
    } else {
        n.subrange(skip_labels(n, 0, (label_count(n) - k) as nat), n.len() as int)
    }
}

/// `*.` + `n`.
pub open spec fn wild_of(n: Seq<u8>) -> Seq<u8> {
    seq![1u8, 42u8] + n
}

// ---------------------------------------------------------------------------
// Canonical form (RFC 4034 §6.2, RFC 6840 §5.1)
// ---------------------------------------------------------------------------

/// Where the names are in RDATA of type `t`, for the types RFC 4034 §6.2
/// lists (less NSEC, RFC 6840 §5.1): fixed octets first, then
/// character-strings, then names, each count as given.
pub open spec fn layout(t: u16) -> Option<(int, nat, nat)> {
    if t == 2 || t == 3 || t == 4 || t == 5 || t == 7 || t == 8 || t == 9 || t == 12 || t == 30 || t == 39 {
        // NS MD MF CNAME MB MG MR PTR NXT DNAME
        Some((0, 0, 1))
    } else if t == 6 || t == 14 || t == 17 {
        // SOA MINFO RP
        Some((0, 0, 2))
    } else if t == 15 || t == 18 || t == 21 || t == 36 {
        // MX AFSDB RT KX
        Some((2, 0, 1))
    } else if t == 26 {
        // PX
        Some((2, 0, 2))
    } else if t == 33 {
        // SRV
        Some((6, 0, 1))
    } else if t == 35 {
        // NAPTR
        Some((4, 3, 1))
    } else if t == 24 || t == 46 {
        // SIG RRSIG: the signer's name
        Some((18, 0, 1))
    } else {
        None
    }
}

pub open spec fn skip_strings(b: Seq<u8>, off: int, s: nat) -> Option<int>
    decreases s,
{
    if s == 0 {
        Some(off)
    } else if off < 0 || off >= b.len() || off + 1 + b[off] > b.len() {
        None
    } else {
        skip_strings(b, off + 1 + b[off], (s - 1) as nat)
    }
}

pub open spec fn skip_names(b: Seq<u8>, off: int, k: nat) -> Option<int>
    decreases k,
{
    if k == 0 {
        Some(off)
    } else {
        match name_len(b, off) {
            Some(l) => skip_names(b, off + l, (k - 1) as nat),
            None => None,
        }
    }
}

/// The octets of RDATA `rd` of type `t` that are names: `[a, b)`.
pub open spec fn name_region(t: u16, rd: Seq<u8>) -> Option<(int, int)> {
    match layout(t) {
        Some((f, s, k)) => if f > rd.len() {
            None
        } else {
            match skip_strings(rd, f, s) {
                Some(a) => match skip_names(rd, a, k) {
                    Some(b) => Some((a, b)),
                    None => None,
                },
                None => None,
            }
        },
        None => None,
    }
}

/// The canonical form of RDATA (RFC 4034 §6.2 item 3): its names
/// lowercased. RDATA whose names do not parse is left as it is (it then
/// cannot match what a signer signed).
pub open spec fn canon_rdata(t: u16, rd: Seq<u8>) -> Seq<u8> {
    match name_region(t, rd) {
        Some((a, b)) => Seq::new(rd.len(), |i: int| if a <= i < b { lower(rd[i]) } else { rd[i] }),
        None => rd,
    }
}

/// RDATA order (RFC 4034 §6.3): as left-justified unsigned octet
/// sequences, a sequence before any longer one it is a prefix of.
pub open spec fn bytes_lt(a: Seq<u8>, b: Seq<u8>) -> bool {
    exists|k: int|
        0 <= k <= a.len() && k <= b.len() && a.subrange(0, k) == b.subrange(0, k) && ((k == a.len() && k
            < b.len()) || (k < a.len() && k < b.len() && a[k] < b[k]))
}

/// Strictly increasing: sorted with no duplicates (RFC 4034 §6.3).
pub open spec fn sorted_strict(s: Seq<Seq<u8>>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> bytes_lt(#[trigger] s[i], #[trigger] s[j])
}

/// The canonical RDATA of the records of `rs`, as type `t`.
pub open spec fn canons(rs: Seq<RrS>, t: u16) -> Seq<Seq<u8>> {
    Seq::new(rs.len(), |j: int| canon_rdata(t, rs[j].rdata))
}

/// `ords` is the RRset `rs`'s canonical RDATA, as a set.
pub open spec fn rdata_set(ords: Seq<Seq<u8>>, rs: Seq<RrS>, t: u16) -> bool {
    ords.to_set() == canons(rs, t).to_set()
}

/// The owner name as signed (RFC 4034 §3.1.8.1, RFC 4035 §5.3.2):
/// lowercased, and if the RRSIG's Labels field is less than the owner's
/// labels, the RRset was expanded from a wildcard, `*.` + the owner's
/// rightmost `labels` labels.
pub open spec fn signed_owner(owner: Seq<u8>, labels: u8) -> Seq<u8> {
    if (labels as nat) < sig_label_count(owner) {
        wild_of(lower_seq(suffix(owner, labels as nat)))
    } else {
        lower_seq(owner)
    }
}

/// One RR as signed: owner | type | class | original TTL | RDLENGTH |
/// RDATA (RFC 4034 §3.1.8.1).
pub open spec fn rr_wire(owner: Seq<u8>, t: u16, ttl: u32, rd: Seq<u8>) -> Seq<u8> {
    owner + be16(t) + be16(CLASS_IN) + be32(ttl) + be16(rd.len() as u16) + rd
}

pub open spec fn rrs_wire(owner: Seq<u8>, t: u16, ttl: u32, ords: Seq<Seq<u8>>) -> Seq<u8>
    decreases ords.len(),
{
    if ords.len() == 0 {
        Seq::empty()
    } else {
        rrs_wire(owner, t, ttl, ords.drop_last()) + rr_wire(owner, t, ttl, ords.last())
    }
}

// ---------------------------------------------------------------------------
// RRSIG fields (RFC 4034 §3.1)
// ---------------------------------------------------------------------------

pub open spec fn sig_covered(rd: Seq<u8>) -> u16 {
    u16_at(rd, 0)
}

pub open spec fn sig_alg(rd: Seq<u8>) -> u8 {
    rd[2]
}

pub open spec fn sig_labels(rd: Seq<u8>) -> u8 {
    rd[3]
}

pub open spec fn sig_ttl(rd: Seq<u8>) -> u32 {
    u32_at(rd, 4)
}

pub open spec fn sig_expiration(rd: Seq<u8>) -> u32 {
    u32_at(rd, 8)
}

pub open spec fn sig_inception(rd: Seq<u8>) -> u32 {
    u32_at(rd, 12)
}

/// Where the signature starts: after the signer's name.
pub open spec fn sig_end(rd: Seq<u8>) -> int {
    18 + name_len(rd, 18).unwrap()
}

pub open spec fn sig_signer(rd: Seq<u8>) -> Seq<u8> {
    rd.subrange(18, sig_end(rd))
}

pub open spec fn sig_bytes(rd: Seq<u8>) -> Seq<u8> {
    rd.subrange(sig_end(rd), rd.len() as int)
}

pub open spec fn sig_wf(rd: Seq<u8>) -> bool {
    rd.len() >= 19 && name_len(rd, 18) is Some
}

/// What is signed: the RRSIG RDATA without the signature, its signer's
/// name lowercased, then the RRs (RFC 4034 §3.1.8.1).
pub open spec fn signed_data(sig_rd: Seq<u8>, owner: Seq<u8>, t: u16, ords: Seq<Seq<u8>>) -> Seq<u8> {
    canon_rdata(TYPE_RRSIG, sig_rd).subrange(0, sig_end(sig_rd)) + rrs_wire(owner, t, sig_ttl(sig_rd), ords)
}

/// Serial number arithmetic (RFC 1982), as RFC 4034 §3.1.5 asks: `a` is
/// at or before `b`.
pub open spec fn serial_le(a: u32, b: u32) -> bool {
    (b as int - a as int) % 0x1_0000_0000 < 0x8000_0000
}

/// The signature's validity period holds `now` (seconds since 1970,
/// modulo 2^32).
pub open spec fn time_ok(rd: Seq<u8>, now: u32) -> bool {
    serial_le(sig_inception(rd), now) && serial_le(now, sig_expiration(rd))
}

// ---------------------------------------------------------------------------
// Keys (RFC 4034 §2) and the signature check
// ---------------------------------------------------------------------------

/// A DNSKEY's RDATA may sign RRsets: the Zone Key flag set, not revoked
/// (RFC 5011 §3), protocol 3, an algorithm and a key.
pub open spec fn key_ok(k: Seq<u8>) -> bool {
    &&& k.len() > 4
    &&& k[0] % 2 == 1
    &&& k[1] < 128
    &&& k[2] == 3
}

pub open spec fn key_alg(k: Seq<u8>) -> u8 {
    k[3]
}

pub open spec fn key_pub(k: Seq<u8>) -> Seq<u8> {
    k.subrange(4, k.len() as int)
}

/// The signature check of algorithm `alg` (trusted: aws-lc, `crypto.rs`):
/// `sig` is a signature of `data` under public key `key` in its DNSSEC
/// encoding (RFC 3110, RFC 6605, RFC 8080).
pub uninterp spec fn sig_valid(alg: u8, key: Seq<u8>, data: Seq<u8>, sig: Seq<u8>) -> bool;

/// RRset: one or more records of one name (ignoring case), type and
/// class IN.
pub open spec fn rrset_ok(rs: Seq<RrS>) -> bool {
    &&& rs.len() > 0
    &&& forall|i: int| 0 <= i < rs.len() ==> {
        &&& eq_ci((#[trigger] rs[i]).name, rs[0].name)
        &&& rs[i].rtype == rs[0].rtype
        &&& rs[i].rclass == CLASS_IN
    }
}

/// RRSIG `sig` with DNSKEY RDATA `key` of zone `zone` validates the RRset
/// `rs` at time `now` (RFC 4035 §5.3.1 and §5.3.3).
pub open spec fn rrset_signed(rs: Seq<RrS>, sig: RrS, key: Seq<u8>, zone: Seq<u8>, now: u32) -> bool {
    let rd = sig.rdata;
    let t = rs[0].rtype;
    &&& rrset_ok(rs)
    &&& t != TYPE_RRSIG
    &&& sig.rtype == TYPE_RRSIG
    &&& sig.rclass == CLASS_IN
    &&& eq_ci(sig.name, rs[0].name)
    &&& sig_wf(rd)
    &&& sig_covered(rd) == t
    &&& eq_ci(sig_signer(rd), zone)
    &&& is_sub(rs[0].name, zone)
    // A DS RRset is the parent's (RFC 4035 §2.4), a DNSKEY RRset the
    // zone's own (§2.1).
    &&& (t == TYPE_DS ==> !eq_ci(rs[0].name, zone))
    &&& (t == TYPE_DNSKEY ==> eq_ci(rs[0].name, zone))
    &&& (sig_labels(rd) as nat) <= sig_label_count(rs[0].name)
    &&& time_ok(rd, now)
    &&& key_ok(key)
    &&& key_alg(key) == sig_alg(rd)
    &&& alg_supported(sig_alg(rd))
    &&& exists|ords: Seq<Seq<u8>>| {
        &&& sorted_strict(ords)
        &&& rdata_set(ords, rs, t)
        &&& sig_valid(
            sig_alg(rd),
            key_pub(key),
            signed_data(rd, signed_owner(rs[0].name, sig_labels(rd)), t, ords),
            sig_bytes(rd),
        )
    }
}

/// The RRset was expanded from a wildcard: its RRSIG counts fewer labels
/// than its owner has (RFC 4035 §5.3.4).
pub open spec fn expanded(owner: Seq<u8>, sig: RrS) -> bool {
    (sig_labels(sig.rdata) as nat) < sig_label_count(owner)
}

// ---------------------------------------------------------------------------
// DS (RFC 4034 §5, RFC 4509, RFC 6605)
// ---------------------------------------------------------------------------

pub open spec fn ds_digest(dt: u8, data: Seq<u8>) -> Seq<u8> {
    if dt == 1 {
        sha1(data)
    } else if dt == 2 {
        verilith_sha2::spec::sha256(data)
    } else {
        verilith_sha2::spec512::sha384(data)
    }
}

/// DS RDATA `ds` identifies DNSKEY RDATA `key` of zone `owner`: the same
/// algorithm, and the digest of the owner (lowercased) and the key's
/// RDATA. (The key tag is a hint and is not needed for this.)
pub open spec fn ds_matches(ds: Seq<u8>, owner: Seq<u8>, key: Seq<u8>) -> bool {
    &&& ds.len() >= 4
    &&& key.len() >= 4
    &&& ds[2] == key[3]
    &&& digest_supported(ds[3])
    &&& ds.subrange(4, ds.len() as int) == ds_digest(ds[3], lower_seq(owner) + key)
}

// ---------------------------------------------------------------------------
// The chain of trust (RFC 4035 §5)
// ---------------------------------------------------------------------------

/// One zone of a chain: its DNSKEY RRset, validated by a key in it that a
/// validated DS identifies; for a zone below the root, the DS RRset, in
/// the parent zone, validated by one of the parent's trusted keys.
pub struct Link {
    pub zone: Seq<u8>,
    pub keys: Seq<RrS>,
    pub ksk: Seq<u8>,
    pub ksig: RrS,
    pub ds: Seq<RrS>,
    pub dssig: RrS,
    pub dskey: Seq<u8>,
    /// When the DNSKEY RRset's signature was checked, and the DS RRset's.
    pub now: u32,
    pub ds_now: u32,
}

pub open spec fn has_key(keys: Seq<RrS>, k: Seq<u8>) -> bool {
    exists|i: int| 0 <= i < keys.len() && (#[trigger] keys[i]).rdata == k
}

/// The zone's DNSKEY RRset is validated by its key `ksk`.
pub open spec fn keys_selfsigned(l: Link) -> bool {
    &&& l.keys.len() > 0
    &&& l.keys[0].rtype == TYPE_DNSKEY
    &&& eq_ci(l.keys[0].name, l.zone)
    &&& has_key(l.keys, l.ksk)
    &&& rrset_signed(l.keys, l.ksig, l.ksk, l.zone, l.now)
}

/// The trust anchors: DS RDATA for the root zone, as configured (by
/// default IANA's, `trust.rs`). Empty when validation is off.
pub uninterp spec fn anchors() -> Seq<Seq<u8>>;

/// The anchors (DS RDATA for the root, configured) identify the root's
/// key `ksk`.
pub open spec fn anchored(l: Link, anchors: Seq<Seq<u8>>) -> bool {
    exists|i: int| 0 <= i < anchors.len() && ds_matches(#[trigger] anchors[i], root(), l.ksk)
}

/// `l`'s DS RRset is validated by a trusted key of the parent `p`, and
/// identifies `l`'s key.
pub open spec fn delegated(p: Link, l: Link) -> bool {
    &&& is_sub(l.zone, p.zone)
    &&& !eq_ci(l.zone, p.zone)
    &&& l.ds.len() > 0
    &&& l.ds[0].rtype == TYPE_DS
    &&& eq_ci(l.ds[0].name, l.zone)
    &&& has_key(p.keys, l.dskey)
    &&& rrset_signed(l.ds, l.dssig, l.dskey, p.zone, l.ds_now)
    &&& exists|i: int| 0 <= i < l.ds.len() && ds_matches((#[trigger] l.ds[i]).rdata, l.zone, l.ksk)
}

/// A chain of trust from the anchors: the root first, each zone's keys
/// validated through its parent's.
pub open spec fn chain_ok(c: Seq<Link>, anchors: Seq<Seq<u8>>) -> bool {
    &&& c.len() > 0
    &&& c[0].zone == root()
    &&& anchored(c[0], anchors)
    &&& forall|i: int| 0 <= i < c.len() ==> keys_selfsigned(#[trigger] c[i])
    &&& forall|i: int| 0 < i < c.len() ==> delegated(c[i - 1], #[trigger] c[i])
}

/// `keys` is zone `zone`'s DNSKEY RRset and is trusted: chain `c` ends at it.
pub open spec fn trusted(c: Seq<Link>, anchors: Seq<Seq<u8>>, zone: Seq<u8>, keys: Seq<RrS>) -> bool {
    chain_ok(c, anchors) && eq_ci(c.last().zone, zone) && c.last().keys == keys
}

/// A validated RRset: signed by a trusted key of the zone the RRSIG names.
pub struct Signed {
    pub rs: Seq<RrS>,
    pub sig: RrS,
    pub key: Seq<u8>,
    pub chain: Seq<Link>,
    /// When the signature was checked.
    pub now: u32,
}

pub open spec fn signed_ok(s: Signed, anchors: Seq<Seq<u8>>) -> bool {
    &&& chain_ok(s.chain, anchors)
    &&& has_key(s.chain.last().keys, s.key)
    &&& rrset_signed(s.rs, s.sig, s.key, s.chain.last().zone, s.now)
}

impl Signed {
    pub open spec fn zone(self) -> Seq<u8> {
        self.chain.last().zone
    }
}

// ---------------------------------------------------------------------------
// Canonical name order (RFC 4034 §6.1) and NSEC (RFC 4034 §4, RFC 4035 §5.4)
// ---------------------------------------------------------------------------

/// The labels of the name at `n[off..]`, leftmost first, lowercased.
pub open spec fn labels_of(n: Seq<u8>, off: int) -> Seq<Seq<u8>>
    decreases n.len() - off,
{
    if off < 0 || off >= n.len() || n[off] == 0 || off + 1 + n[off] >= n.len() {
        Seq::empty()
    } else {
        seq![lower_seq(n.subrange(off + 1, off + 1 + n[off]))] + labels_of(n, off + 1 + n[off])
    }
}

pub open spec fn rev_labels(n: Seq<u8>) -> Seq<Seq<u8>> {
    labels_of(n, 0).reverse()
}

/// Label sequences in order: label by label, each in RDATA order, a
/// sequence before any longer one it begins.
pub open spec fn lab_lt(x: Seq<Seq<u8>>, y: Seq<Seq<u8>>) -> bool {
    exists|k: int|
        0 <= k <= x.len() && k <= y.len() && x.subrange(0, k) == y.subrange(0, k) && ((k == x.len() && k
            < y.len()) || (k < x.len() && k < y.len() && bytes_lt(x[k], y[k])))
}

/// Canonical order of names: label sequences compared from the rightmost
/// label, each label as lowercased octets, a name before its descendants.
pub open spec fn name_lt(a: Seq<u8>, b: Seq<u8>) -> bool {
    lab_lt(rev_labels(a), rev_labels(b))
}

/// Type bit `t` is set in the type bit maps `bm` from `off` (RFC 4034
/// §4.1.2).
pub open spec fn has_type_from(bm: Seq<u8>, off: int, t: u16) -> bool
    decreases bm.len() - off,
{
    if off < 0 || off + 2 > bm.len() {
        false
    } else {
        let (win, l) = (bm[off], bm[off + 1] as int);
        if l == 0 || l > 32 || off + 2 + l > bm.len() {
            false
        } else if win as int == t as int / 256 {
            (t as int % 256) / 8 < l && (bm[off + 2 + (t as int % 256) / 8] as int / pow2_8(7 - t as int % 8)) % 2
                == 1
        } else {
            has_type_from(bm, off + 2 + l, t)
        }
    }
}

pub open spec fn pow2_8(k: int) -> int {
    if k <= 0 { 1 } else if k == 1 { 2 } else if k == 2 { 4 } else if k == 3 { 8 } else if k == 4 { 16 } else if k == 5 { 32 } else if k == 6 { 64 } else { 128 }
}

/// An NSEC record's next owner name and type bit maps.
pub open spec fn nsec_wf(r: RrS) -> bool {
    r.rtype == TYPE_NSEC && name_len(r.rdata, 0) is Some
}

pub open spec fn nsec_next(r: RrS) -> Seq<u8> {
    r.rdata.subrange(0, name_len(r.rdata, 0).unwrap())
}

pub open spec fn nsec_has(r: RrS, t: u16) -> bool {
    has_type_from(r.rdata, name_len(r.rdata, 0).unwrap(), t)
}

/// NSEC `r` of zone `zone` says no name exists strictly between its owner
/// and its next name (the last NSEC's next name is the apex, so it covers
/// everything after its owner).
pub open spec fn nsec_covers(r: RrS, n: Seq<u8>, zone: Seq<u8>) -> bool {
    &&& nsec_wf(r)
    &&& is_sub(n, zone)
    &&& name_lt(r.name, n)
    &&& (name_lt(n, nsec_next(r)) || !name_lt(r.name, nsec_next(r)))
    // A name below a delegation or a DNAME may exist in another zone
    // (RFC 6840 §4.1).
    &&& is_sub(n, r.name) ==> !nsec_has(r, TYPE_DNAME) && !(nsec_has(r, TYPE_NS) && !nsec_has(r, TYPE_SOA_))
}

/// NSEC `r` is at `n` and `n` has no records of type `t`, and no CNAME;
/// an NSEC at a delegation (NS, no SOA) speaks only for DS, and one at an
/// apex (SOA) not for DS, which is in the parent (RFC 4035 §5.4, RFC 6840
/// §4.1, §4.3).
pub open spec fn nsec_nodata(r: RrS, n: Seq<u8>, t: u16) -> bool {
    &&& nsec_wf(r)
    &&& eq_ci(r.name, n)
    &&& !nsec_has(r, t)
    &&& !nsec_has(r, TYPE_CNAME)
    &&& if t == TYPE_DS {
        !nsec_has(r, TYPE_SOA_)
    } else {
        !(nsec_has(r, TYPE_NS) && !nsec_has(r, TYPE_SOA_))
    }
}

/// The closest encloser NSEC `r` proves for `n`, which it covers: the
/// longer of the common ancestors of `n` with the NSEC's owner and next
/// name (RFC 4035 §5.4). Every ancestor of `n` below it does not exist.
pub open spec fn nsec_ce(r: RrS, n: Seq<u8>) -> Seq<u8> {
    let a = common(n, r.name);
    let b = common(n, nsec_next(r));
    if label_count(a) >= label_count(b) { a } else { b }
}

/// The deepest common ancestor of `a` and `b`, as a suffix of `a`.
pub open spec fn common(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    suffix(a, common_k(rev_labels(a), rev_labels(b), 0))
}

pub open spec fn common_k(x: Seq<Seq<u8>>, y: Seq<Seq<u8>>, k: nat) -> nat
    decreases x.len() - k,
{
    if k < x.len() && k < y.len() && x[k as int] == y[k as int] {
        common_k(x, y, k + 1)
    } else {
        k
    }
}

// ---------------------------------------------------------------------------
// NSEC3 (RFC 5155)
// ---------------------------------------------------------------------------

/// NSEC3 RDATA: hash algorithm 1 (SHA-1), flags, iterations, salt, next
/// hashed owner (20 octets), type bit maps.
pub open spec fn n3_wf(r: RrS) -> bool {
    let d = r.rdata;
    &&& r.rtype == TYPE_NSEC3
    &&& d.len() >= 5
    &&& d[0] == 1
    &&& u16_at(d, 2) <= MAX_NSEC3_ITERATIONS
    &&& 5 + d[4] as int + 1 <= d.len()
    &&& d[5 + d[4] as int] == 20
    &&& 5 + d[4] as int + 21 <= d.len()
}

pub open spec fn n3_optout(r: RrS) -> bool {
    r.rdata[1] % 2 == 1
}

pub open spec fn n3_iter(r: RrS) -> u16 {
    u16_at(r.rdata, 2)
}

pub open spec fn n3_salt(r: RrS) -> Seq<u8> {
    r.rdata.subrange(5, 5 + r.rdata[4] as int)
}

pub open spec fn n3_next(r: RrS) -> Seq<u8> {
    let s = 5 + r.rdata[4] as int + 1;
    r.rdata.subrange(s, s + 20)
}

pub open spec fn n3_has(r: RrS, t: u16) -> bool {
    has_type_from(r.rdata, 5 + r.rdata[4] as int + 21, t)
}

/// IH(salt, x, k) (RFC 5155 §5).
pub open spec fn ih(salt: Seq<u8>, x: Seq<u8>, k: nat) -> Seq<u8>
    decreases k,
{
    if k == 0 {
        sha1(x + salt)
    } else {
        sha1(ih(salt, x, (k - 1) as nat) + salt)
    }
}

/// The hash of name `n` with NSEC3 `r`'s parameters.
pub open spec fn n3_hash(r: RrS, n: Seq<u8>) -> Seq<u8> {
    ih(n3_salt(r), lower_seq(n), n3_iter(r) as nat)
}

/// Base32hex (RFC 4648 §7), lowercase, without padding, of 20 octets: 32
/// characters, each 5 bits, most significant first.
pub open spec fn b32_digit(v: int) -> u8 {
    if v < 10 { (48 + v) as u8 } else { (97 + v - 10) as u8 }
}

pub open spec fn pow32(k: int) -> int
    decreases k,
{
    if k <= 0 { 1 } else { 32 * pow32(k - 1) }
}

/// The 40 bits of octets `5c .. 5c+5` of `h`.
pub open spec fn chunk40(h: Seq<u8>, c: int) -> int {
    h[5 * c] as int * 0x1_0000_0000 + h[5 * c + 1] as int * 0x100_0000 + h[5 * c + 2] as int * 0x1_0000 + h[5 * c
        + 3] as int * 0x100 + h[5 * c + 4] as int
}

pub open spec fn b32hex(h: Seq<u8>) -> Seq<u8> {
    Seq::new(32, |i: int| b32_digit((chunk40(h, i / 8) / pow32(7 - i % 8)) % 32))
}

/// The owner a hash has in zone `zone`: the hash in base32hex as its first
/// label (RFC 5155 §3).
pub open spec fn n3_owner(h: Seq<u8>, zone: Seq<u8>) -> Seq<u8> {
    seq![32u8] + b32hex(h) + zone
}

/// The NSEC3 record's own hash, from its owner's first label: the
/// label, lowercased, if the owner is a 32-character label in `zone`.
pub open spec fn n3_label(r: RrS, zone: Seq<u8>) -> Option<Seq<u8>> {
    if r.name.len() >= 33 && r.name[0] == 32 && eq_ci(r.name.subrange(33, r.name.len() as int), zone) {
        Some(lower_seq(r.name.subrange(1, 33)))
    } else {
        None
    }
}

/// NSEC3 `r` of zone `zone` matches `n`: its owner is `n`'s hash.
pub open spec fn n3_matches(r: RrS, n: Seq<u8>, zone: Seq<u8>) -> bool {
    &&& n3_wf(r)
    &&& is_sub(n, zone)
    &&& n3_label(r, zone) == Some(b32hex(n3_hash(r, n)))
}

/// NSEC3 `r` covers `n`: `n`'s hash is strictly between the record's own
/// hash and its next one, in the order of the hashes (which base32hex
/// keeps: comparing the lowercase base32hex strings compares the hashes),
/// or after its own hash when the next one wraps to the first.
pub open spec fn n3_covers(r: RrS, n: Seq<u8>, zone: Seq<u8>) -> bool {
    let own = n3_label(r, zone).unwrap();
    let h = b32hex(n3_hash(r, n));
    let nx = b32hex(n3_next(r));
    &&& n3_wf(r)
    &&& is_sub(n, zone)
    &&& n3_label(r, zone) is Some
    // Strictly between the owner and the next hash; for the last NSEC3 of
    // the chain (next <= owner), after the owner or before the next.
    &&& if bytes_lt(own, nx) {
        bytes_lt(own, h) && bytes_lt(h, nx)
    } else {
        bytes_lt(own, h) || bytes_lt(h, nx)
    }
}

/// The name one label longer than ancestor `ce` on the way to `n`.
pub open spec fn next_closer(n: Seq<u8>, ce: Seq<u8>) -> Seq<u8> {
    suffix(n, label_count(ce) + 1)
}

/// The closest encloser proof (RFC 5155 §8.3): `ce` is an ancestor of `n`
/// in the zone that exists (an NSEC3 matches it), and the next closer name
/// does not (an NSEC3 covers it).
pub open spec fn n3_ce(ns: Seq<RrS>, n: Seq<u8>, ce: Seq<u8>, zone: Seq<u8>) -> bool {
    &&& is_sub(n, ce)
    &&& is_sub(ce, zone)
    &&& label_count(ce) < label_count(n)
    &&& ce == suffix(n, label_count(ce))
    &&& exists|i: int| 0 <= i < ns.len() && n3_matches(#[trigger] ns[i], ce, zone) && !(n3_has(ns[i], TYPE_DNAME))
        && !(n3_has(ns[i], TYPE_NS) && !n3_has(ns[i], TYPE_SOA_))
    &&& exists|i: int| 0 <= i < ns.len() && n3_covers(#[trigger] ns[i], next_closer(n, ce), zone)
}

// ---------------------------------------------------------------------------
// What a set of validated NSEC and NSEC3 records proves
// ---------------------------------------------------------------------------

/// `n` does not exist in `zone` (RFC 4035 §5.4, RFC 5155 §8.4): an NSEC
/// covers it and another (or the same) covers the wildcard at its closest
/// encloser; or the NSEC3 closest encloser proof and an NSEC3 covering
/// the wildcard there.
pub open spec fn proves_nxdomain(ns: Seq<RrS>, n: Seq<u8>, zone: Seq<u8>) -> bool {
    ||| exists|i: int, j: int|
        0 <= i < ns.len() && 0 <= j < ns.len() && nsec_covers(#[trigger] ns[i], n, zone) && nsec_covers(
            #[trigger] ns[j],
            wild_of(nsec_ce(ns[i], n)),
            zone,
        )
    ||| exists|ce: Seq<u8>| {
        &&& #[trigger] n3_ce(ns, n, ce, zone)
        &&& exists|j: int| 0 <= j < ns.len() && n3_covers(#[trigger] ns[j], wild_of(ce), zone)
    }
}

/// `n` exists in `zone` without records of type `t` (RFC 4035 §5.4,
/// RFC 5155 §8.5, §8.6), or (for DS) is an unsigned delegation of an
/// opt-out span (§8.6), or a wildcard says so (§8.7, RFC 4035 §5.4).
pub open spec fn proves_nodata(ns: Seq<RrS>, n: Seq<u8>, t: u16, zone: Seq<u8>) -> bool {
    ||| exists|i: int| 0 <= i < ns.len() && nsec_nodata(#[trigger] ns[i], n, t)
    ||| exists|i: int| 0 <= i < ns.len() && n3_nodata(#[trigger] ns[i], n, t, zone)
    ||| exists|i: int| 0 <= i < ns.len() && nsec_ent(#[trigger] ns[i], n, zone)
    ||| (t == TYPE_DS && exists|ce: Seq<u8>| #[trigger] n3_ce(ns, n, ce, zone) && optout_covered(ns, n, ce, zone))
    ||| exists|i: int, j: int|
        0 <= i < ns.len() && 0 <= j < ns.len() && nsec_covers(#[trigger] ns[i], n, zone) && nsec_nodata(
            #[trigger] ns[j],
            wild_of(nsec_ce(ns[i], n)),
            t,
        )
    ||| exists|ce: Seq<u8>| {
        &&& #[trigger] n3_ce(ns, n, ce, zone)
        &&& exists|j: int| 0 <= j < ns.len() && n3_nodata(#[trigger] ns[j], wild_of(ce), t, zone)
    }
}

/// `n` is an empty non-terminal (RFC 4035 §3.1.3.2, RFC 4592 §2.2.2):
/// an NSEC covers it (so it owns no records) and its next name is below
/// it (so it exists).
pub open spec fn nsec_ent(r: RrS, n: Seq<u8>, zone: Seq<u8>) -> bool {
    &&& nsec_covers(r, n, zone)
    &&& is_sub(nsec_next(r), n)
    &&& !eq_ci(nsec_next(r), n)
}

pub open spec fn n3_nodata(r: RrS, n: Seq<u8>, t: u16, zone: Seq<u8>) -> bool {
    &&& n3_matches(r, n, zone)
    &&& !n3_has(r, t)
    &&& !n3_has(r, TYPE_CNAME)
    &&& if t == TYPE_DS {
        !n3_has(r, TYPE_SOA_)
    } else {
        !(n3_has(r, TYPE_NS) && !n3_has(r, TYPE_SOA_))
    }
}

pub open spec fn optout_covered(ns: Seq<RrS>, n: Seq<u8>, ce: Seq<u8>, zone: Seq<u8>) -> bool {
    exists|j: int| 0 <= j < ns.len() && n3_covers(#[trigger] ns[j], next_closer(n, ce), zone) && n3_optout(ns[j])
}

/// A wildcard answer for `n` is allowed: `n` itself does not exist, so the
/// wildcard at its closest encloser `ce` applied (RFC 4035 §5.3.4, RFC 5155
/// §8.8): an NSEC covers `n`, or an NSEC3 covers the next closer name.
pub open spec fn proves_expansion(ns: Seq<RrS>, n: Seq<u8>, ce: Seq<u8>, zone: Seq<u8>) -> bool {
    ||| exists|i: int| 0 <= i < ns.len() && nsec_covers(#[trigger] ns[i], n, zone)
    ||| (label_count(ce) < label_count(n) && exists|i: int| 0 <= i < ns.len() && n3_covers(#[trigger] ns[i], next_closer(n, ce), zone))
}

/// Zone `c` is a delegation from its parent with no DS: it is not signed,
/// and nothing at or below it can be validated (RFC 4035 §5.2): NSEC or
/// NSEC3 at `c` with NS and without DS and SOA, or the NSEC3 opt-out proof.
pub open spec fn proves_unsigned(ns: Seq<RrS>, c: Seq<u8>, zone: Seq<u8>) -> bool {
    ||| exists|i: int| 0 <= i < ns.len() && nsec_nodata(#[trigger] ns[i], c, TYPE_DS) && nsec_has(ns[i], TYPE_NS)
    ||| exists|i: int| 0 <= i < ns.len() && n3_nodata(#[trigger] ns[i], c, TYPE_DS, zone) && n3_has(ns[i], TYPE_NS)
    ||| exists|ce: Seq<u8>| #[trigger] n3_ce(ns, c, ce, zone) && optout_covered(ns, c, ce, zone)
}

/// Every record of `ns` is in an RRset of `ev`, validated, of zone `zone`.
pub open spec fn all_validated(ns: Seq<RrS>, ev: Seq<Signed>, anchors: Seq<Seq<u8>>, zone: Seq<u8>) -> bool {
    &&& forall|k: int| 0 <= k < ev.len() ==> signed_ok(#[trigger] ev[k], anchors) && eq_ci(ev[k].zone(), zone)
    &&& forall|i: int| 0 <= i < ns.len() ==> in_validated(ev, #[trigger] ns[i])
}

/// `r` is a record of one of the validated RRsets `ev`.
pub open spec fn in_validated(ev: Seq<Signed>, r: RrS) -> bool {
    exists|k: int, j: int| 0 <= k < ev.len() && 0 <= j < ev[k].rs.len() && r == #[trigger] ev[k].rs[j]
}

/// Zone `c` is proven unsigned: validated NSEC/NSEC3 records of its parent
/// `p`, which is trusted, say so.
pub struct Unsigned {
    pub cut: Seq<u8>,
    pub parent: Seq<u8>,
    pub ns: Seq<RrS>,
    pub ev: Seq<Signed>,
}

/// Either validated NSEC or NSEC3 records of the parent say the cut has
/// no DS; or its DS RRset is validated and names no algorithm and digest
/// both supported, so it is treated as unsigned (RFC 4035 §5.2, RFC 6840
/// §5.2). `u.ev[0]` is that DS RRset.
pub open spec fn unsigned_ok(u: Unsigned, anchors: Seq<Seq<u8>>) -> bool {
    &&& is_sub(u.cut, u.parent)
    &&& !eq_ci(u.cut, u.parent)
    &&& all_validated(u.ns, u.ev, anchors, u.parent)
    &&& u.ev.len() > 0
    &&& {
        ||| proves_unsigned(u.ns, u.cut, u.parent)
        ||| {
            let d = u.ev[0].rs;
            &&& d[0].rtype == TYPE_DS
            &&& eq_ci(d[0].name, u.cut)
            &&& forall|i: int| 0 <= i < d.len() ==> !ds_usable(#[trigger] d[i].rdata)
        }
    }
}

/// A DS record whose algorithm and digest type are both supported.
pub open spec fn ds_usable(ds: Seq<u8>) -> bool {
    ds.len() >= 4 && alg_supported(ds[2]) && digest_supported(ds[3])
}

/// Name `n` is in an unsigned zone: at or below a proven unsigned cut.
/// (Names are compared lowercased throughout what follows, so that a
/// statement about a name is one about every spelling of it.)
pub open spec fn insecure(u: Unsigned, anchors: Seq<Seq<u8>>, n: Seq<u8>) -> bool {
    unsigned_ok(u, anchors) && is_sub(lower_seq(n), u.cut)
}

// ---------------------------------------------------------------------------
// What an answer's validation rests on
// ---------------------------------------------------------------------------

/// Validated NSEC and NSEC3 records of one zone.
pub struct Denial {
    pub zone: Seq<u8>,
    pub ns: Seq<RrS>,
    pub ev: Seq<Signed>,
}

pub open spec fn denial_ok(d: Denial) -> bool {
    all_validated(d.ns, d.ev, anchors(), d.zone)
}

/// The evidence an answer carries (ghost: it costs nothing at run time):
/// validated RRsets, validated denial records, proven unsigned zones.
pub struct Ev {
    pub signed: Seq<Signed>,
    pub denials: Seq<Denial>,
    pub unsigned: Seq<Unsigned>,
}

pub open spec fn ev_ok(e: Ev) -> bool {
    &&& forall|k: int| 0 <= k < e.signed.len() ==> signed_ok(#[trigger] e.signed[k], anchors())
    &&& forall|k: int| 0 <= k < e.denials.len() ==> denial_ok(#[trigger] e.denials[k])
    &&& forall|k: int| 0 <= k < e.unsigned.len() ==> unsigned_ok(#[trigger] e.unsigned[k], anchors())
}

pub open spec fn ev_empty() -> Ev {
    Ev { signed: Seq::empty(), denials: Seq::empty(), unsigned: Seq::empty() }
}

pub open spec fn ev_join(a: Ev, b: Ev) -> Ev {
    Ev { signed: a.signed + b.signed, denials: a.denials + b.denials, unsigned: a.unsigned + b.unsigned }
}

/// The same record, whatever its TTL (the cache lowers TTLs).
pub open spec fn same_rr(a: RrS, b: RrS) -> bool {
    a.name == b.name && a.rtype == b.rtype && a.rclass == b.rclass && a.rdata == b.rdata
}

/// Record `r` is in an RRset `e` validated; if that RRset was expanded
/// from a wildcard, validated denial records of its zone prove the
/// expansion was allowed.
pub open spec fn rec_secure(r: RrS, e: Ev) -> bool {
    exists|k: int, j: int|
        0 <= k < e.signed.len() && 0 <= j < e.signed[k].rs.len() && same_rr(#[trigger] e.signed[k].rs[j], r) && wild_ok(
            e.signed[k],
            e,
        )
}

pub open spec fn wild_ok(s: Signed, e: Ev) -> bool {
    expanded(s.rs[0].name, s.sig) ==> exists|d: int|
        0 <= d < e.denials.len() && eq_ci((#[trigger] e.denials[d]).zone, s.zone()) && proves_expansion(
            e.denials[d].ns,
            lower_seq(s.rs[0].name),
            lower_seq(suffix(s.rs[0].name, sig_labels(s.sig.rdata) as nat)),
            e.denials[d].zone,
        )
}

/// Record `r` is owned by a name in a proven unsigned zone.
pub open spec fn rec_insecure(r: RrS, e: Ev) -> bool {
    name_insecure(r.name, e)
}

pub open spec fn name_insecure(n: Seq<u8>, e: Ev) -> bool {
    exists|u: int| 0 <= u < e.unsigned.len() && insecure(#[trigger] e.unsigned[u], anchors(), n)
}

pub open spec fn nx_proven(n: Seq<u8>, e: Ev) -> bool {
    exists|d: int| 0 <= d < e.denials.len() && proves_nxdomain((#[trigger] e.denials[d]).ns, lower_seq(n), e.denials[d].zone)
}

pub open spec fn nodata_proven(n: Seq<u8>, t: u16, e: Ev) -> bool {
    exists|d: int| 0 <= d < e.denials.len() && proves_nodata((#[trigger] e.denials[d]).ns, lower_seq(n), t, e.denials[d].zone)
}

/// Validation is on: trust anchors are configured.
pub open spec fn validating() -> bool {
    anchors().len() > 0
}

/// The security status of data (RFC 4035 §4.3): not checked (validation
/// off, or the client set CD), secure, or proven insecure. Bogus data is
/// never kept or served: the resolver says SERVFAIL.
pub const UNCHECKED: u8 = 0;
pub const SECURE: u8 = 1;
pub const INSECURE: u8 = 2;

/// Records `rs` with status `sec` and evidence `e`: every record is
/// validated, or (`INSECURE` only) in a proven unsigned zone.
pub open spec fn recs_ok(rs: Seq<RrS>, sec: u8, e: Ev) -> bool {
    forall|i: int| 0 <= i < rs.len() ==> rec_secure(#[trigger] rs[i], e) || (sec == INSECURE && rec_insecure(rs[i], e))
}

/// What validation establishes about an answer for `qname`/`qtype` with
/// RCODE `code`, answer records `rs` and authority records `soa`.
pub open spec fn sec_ok(sec: u8, e: Ev, qname: Seq<u8>, qtype: u16, code: u16, rs: Seq<RrS>, soa: Seq<RrS>) -> bool {
    let end = chain_end(qname, qtype, rs);
    sec == UNCHECKED || {
        &&& sec == SECURE || sec == INSECURE
        &&& validating()
        &&& ev_ok(e)
        &&& recs_ok(rs, sec, e)
        &&& recs_ok(soa, sec, e)
        &&& code == RCODE_NXDOMAIN ==> nx_proven(end, e) || (sec == INSECURE && name_insecure(end, e))
        &&& (code == RCODE_NOERROR && links_only(qname, qtype, rs)) ==> nodata_proven(end, qtype, e) || (sec
            == INSECURE && name_insecure(end, e))
    }
}

} // verus!
