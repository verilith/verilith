//! The trusted specification: DER (X.690 §8, §10) and the X.509 v3
//! certificate profile (RFC 5280 §4) as total functions over `Seq<u8>`.
//!
//! Every exec function in this crate is proven to compute exactly these
//! functions. Read this file to check that it says what X.690 and RFC 5280
//! say; nothing else needs to be trusted about parsing.
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// DER: tag, length, value
// ---------------------------------------------------------------------------

/// One TLV: its identifier octets, kept as bytes, and its contents.
pub struct SpecTlv {
    pub tag: Seq<u8>,
    pub content: Seq<u8>,
}

/// Most subsequent octets a high-tag-number identifier may have (28-bit tag
/// numbers, far beyond anything X.509 uses).
pub spec const MAX_TAG_CONT: nat = 4;

/// Where a high-tag-number identifier that continues at `i` ends: octets with
/// bit 8 set continue it, the first one without ends it (X.690 §8.1.2.4).
pub open spec fn high_tag_end(s: Seq<u8>, i: int, k: nat) -> Option<int>
    decreases k,
{
    if k == 0 || i < 0 || i >= s.len() {
        None
    } else if s[i] < 128 {
        Some(i + 1)
    } else {
        high_tag_end(s, i + 1, (k - 1) as nat)
    }
}

/// The number of identifier octets at the start of `s`. DER requires the
/// shortest form, so the high-tag-number form is only for numbers 31 and up
/// and its first subsequent octet is never 0x80 (X.690 §8.1.2.4.2).
pub open spec fn tag_len(s: Seq<u8>) -> Option<int> {
    if s.len() == 0 {
        None
    } else if s[0] % 32 != 31 {
        Some(1)
    } else if s.len() < 2 || s[1] == 0x80 || s[1] < 31 {
        None
    } else {
        high_tag_end(s, 1, MAX_TAG_CONT)
    }
}

/// The length octets at `i`: `Some((length, offset of the contents))`.
/// DER allows only the definite form, in the fewest octets (X.690 §10.1):
/// lengths below 128 use the short form, and a long form never starts with a
/// zero octet. Long forms of more than four octets (lengths of 4 GiB and up)
/// are refused.
pub open spec fn parse_len(s: Seq<u8>, i: int) -> Option<(int, int)> {
    if i < 0 || i >= s.len() {
        None
    } else if s[i] < 128 {
        Some((s[i] as int, i + 1))
    } else if s[i] == 0x81 {
        if i + 2 > s.len() || s[i + 1] < 128 {
            None
        } else {
            Some((s[i + 1] as int, i + 2))
        }
    } else if s[i] == 0x82 {
        if i + 3 > s.len() || s[i + 1] == 0 {
            None
        } else {
            Some((s[i + 1] as int * 0x100 + s[i + 2] as int, i + 3))
        }
    } else if s[i] == 0x83 {
        if i + 4 > s.len() || s[i + 1] == 0 {
            None
        } else {
            Some(
                (s[i + 1] as int * 0x1_0000 + s[i + 2] as int * 0x100 + s[i + 3] as int, i + 4),
            )
        }
    } else if s[i] == 0x84 {
        if i + 5 > s.len() || s[i + 1] == 0 {
            None
        } else {
            Some(
                (
                    s[i + 1] as int * 0x100_0000 + s[i + 2] as int * 0x1_0000 + s[i + 3] as int
                        * 0x100 + s[i + 4] as int,
                    i + 5,
                ),
            )
        }
    } else {
        None
    }
}

/// The TLV at the start of `s`, and the bytes after it.
pub open spec fn parse_tlv(s: Seq<u8>) -> Option<(SpecTlv, Seq<u8>)> {
    match tag_len(s) {
        None => None,
        Some(h) => match parse_len(s, h) {
            None => None,
            Some((len, c)) => if c + len > s.len() {
                None
            } else {
                Some(
                    (
                        SpecTlv { tag: s.subrange(0, h), content: s.subrange(c, c + len) },
                        s.subrange(c + len, s.len() as int),
                    ),
                )
            },
        },
    }
}

/// The TLV at the start of `s` if its identifier is the single octet `t`:
/// `Some((contents, rest))`.
pub open spec fn parse_expect(s: Seq<u8>, t: u8) -> Option<(Seq<u8>, Seq<u8>)> {
    match parse_tlv(s) {
        Some((x, r)) => if x.tag == seq![t] {
            Some((x.content, r))
        } else {
            None
        },
        None => None,
    }
}

/// `s` is exactly one TLV with identifier `t`: its contents.
pub open spec fn parse_only(s: Seq<u8>, t: u8) -> Option<Seq<u8>> {
    match parse_expect(s, t) {
        Some((c, r)) => if r.len() == 0 {
            Some(c)
        } else {
            None
        },
        None => None,
    }
}

/// `s` is exactly one TLV, of any tag.
pub open spec fn parse_only_tlv(s: Seq<u8>) -> Option<SpecTlv> {
    match parse_tlv(s) {
        Some((x, r)) => if r.len() == 0 {
            Some(x)
        } else {
            None
        },
        None => None,
    }
}

// Universal and context-specific identifier octets used below.
pub spec const T_BOOLEAN: u8 = 0x01;
pub spec const T_INTEGER: u8 = 0x02;
pub spec const T_BIT_STRING: u8 = 0x03;
pub spec const T_OCTET_STRING: u8 = 0x04;
pub spec const T_OID: u8 = 0x06;
pub spec const T_UTC_TIME: u8 = 0x17;
pub spec const T_GENERALIZED_TIME: u8 = 0x18;
pub spec const T_SEQUENCE: u8 = 0x30;
pub spec const T_SET: u8 = 0x31;

// ---------------------------------------------------------------------------
// Primitive types
// ---------------------------------------------------------------------------

/// BOOLEAN contents read as BER (X.690 §8.2): one octet, non-zero is TRUE.
/// DER requires 0xFF for TRUE and omits a FALSE that is the DEFAULT, but
/// certificates from widely deployed tools (including mbedTLS's own test
/// CAs and RFC 8410's example) use 0x01 or an explicit FALSE, and mbedTLS,
/// OpenSSL and NSS accept both; so does this crate (see DEPARTURES.md).
pub open spec fn parse_ber_bool(c: Seq<u8>) -> Option<bool> {
    if c.len() == 1 {
        Some(c[0] != 0)
    } else {
        None
    }
}

/// DER INTEGER contents: at least one octet, and in the fewest octets, so the
/// first nine bits are never all zero or all one (X.690 §8.3.2).
pub open spec fn valid_integer(c: Seq<u8>) -> bool {
    &&& c.len() >= 1
    &&& c.len() >= 2 ==> !(c[0] == 0 && c[1] < 128)
    &&& c.len() >= 2 ==> !(c[0] == 0xFF && c[1] >= 128)
}

/// The unsigned value of the big-endian octets `c[0..n]`.
pub open spec fn be_value(c: Seq<u8>, n: int) -> nat
    decreases n,
{
    if n <= 0 {
        0
    } else {
        be_value(c, n - 1) * 256 + c[n - 1] as nat
    }
}

/// A non-negative DER INTEGER that fits in a `u64`.
pub open spec fn parse_u64(c: Seq<u8>) -> Option<u64> {
    if !valid_integer(c) || c[0] >= 128 {
        None
    } else if c.len() <= 8 || (c.len() == 9 && c[0] == 0) {
        Some(be_value(c, c.len() as int) as u64)
    } else {
        None
    }
}

/// OBJECT IDENTIFIER contents: one or more subidentifiers, each in base 128
/// with bit 8 set on every octet but its last, and in the fewest octets, so
/// none starts with 0x80 (X.690 §8.19.2). Arcs may be any size; they are kept
/// as bytes and never converted.
pub open spec fn valid_oid(c: Seq<u8>) -> bool {
    &&& c.len() >= 1
    &&& c[c.len() - 1] < 128
    &&& forall|i: int|
        0 <= i < c.len() && (i == 0 || c[i - 1] < 128) ==> #[trigger] c[i] != 0x80
}

/// A BIT STRING: the number of unused bits in the last octet, and the octets.
pub struct SpecBitString {
    pub unused: u8,
    pub bytes: Seq<u8>,
}

pub open spec fn pow2_8(u: u8) -> nat {
    if u == 0 {
        1
    } else if u == 1 {
        2
    } else if u == 2 {
        4
    } else if u == 3 {
        8
    } else if u == 4 {
        16
    } else if u == 5 {
        32
    } else if u == 6 {
        64
    } else {
        128
    }
}

/// DER BIT STRING contents (X.690 §8.6.2, §11.2.1): the initial octet counts
/// the unused bits (0 to 7, and 0 when there are no octets), and the unused
/// bits are zero.
pub open spec fn parse_bit_string(c: Seq<u8>) -> Option<SpecBitString> {
    if c.len() == 0 || c[0] > 7 {
        None
    } else if c.len() == 1 && c[0] != 0 {
        None
    } else if c.len() > 1 && (c[c.len() - 1] as nat) % pow2_8(c[0]) != 0 {
        None
    } else {
        Some(SpecBitString { unused: c[0], bytes: c.subrange(1, c.len() as int) })
    }
}

/// A BIT STRING holding whole octets (signatures and public keys).
pub open spec fn parse_octet_aligned_bits(c: Seq<u8>) -> Option<Seq<u8>> {
    if c.len() >= 1 && c[0] == 0 {
        Some(c.subrange(1, c.len() as int))
    } else {
        None
    }
}

/// IA5String contents used for names (dNSName, rfc822Name, URI): 7-bit, and
/// with no NUL octet, so a C consumer can never see a shorter string than the
/// one that was signed (the "null prefix" attack, CVE-2009-2408).
pub open spec fn valid_ia5_name(c: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < c.len() ==> 0 < #[trigger] c[i] < 128
}

// ---------------------------------------------------------------------------
// Time (RFC 5280 §4.1.2.5)
// ---------------------------------------------------------------------------

pub struct SpecTime {
    pub year: u16,
    pub month: u8,
    pub day: u8,
    pub hour: u8,
    pub minute: u8,
    pub second: u8,
}

pub open spec fn is_digit(b: u8) -> bool {
    0x30 <= b <= 0x39
}

pub open spec fn all_digits(c: Seq<u8>, n: int) -> bool {
    forall|i: int| 0 <= i < n ==> is_digit(#[trigger] c[i])
}

/// The two-digit decimal number at `c[i..i + 2]`.
pub open spec fn dd(c: Seq<u8>, i: int) -> int {
    (c[i] - 0x30) * 10 + (c[i + 1] - 0x30)
}

pub open spec fn is_leap(y: int) -> bool {
    y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)
}

pub open spec fn days_in_month(y: int, m: int) -> int {
    if m == 2 {
        if is_leap(y) {
            29
        } else {
            28
        }
    } else if m == 4 || m == 6 || m == 9 || m == 11 {
        30
    } else {
        31
    }
}

/// Month, day, hour, minute and second at `c[i..i + 10]`, then `Z`, and
/// nothing after it: seconds are required, fractions and offsets are not
/// allowed (RFC 5280 §4.1.2.5.1 and §4.1.2.5.2).
pub open spec fn parse_time_tail(c: Seq<u8>, i: int, year: int) -> Option<SpecTime> {
    let mo = dd(c, i);
    let d = dd(c, i + 2);
    let h = dd(c, i + 4);
    let mi = dd(c, i + 6);
    let se = dd(c, i + 8);
    if c[i + 10] != 0x5A {
        None
    } else if mo < 1 || mo > 12 || d < 1 || d > days_in_month(year, mo) || h > 23 || mi > 59
        || se > 59 {
        None
    } else {
        Some(
            SpecTime {
                year: year as u16,
                month: mo as u8,
                day: d as u8,
                hour: h as u8,
                minute: mi as u8,
                second: se as u8,
            },
        )
    }
}

/// UTCTime `YYMMDDHHMMSSZ`; YY below 50 is 20YY, otherwise 19YY.
pub open spec fn parse_utc_time(c: Seq<u8>) -> Option<SpecTime> {
    if c.len() != 13 || !all_digits(c, 12) {
        None
    } else {
        let yy = dd(c, 0);
        parse_time_tail(
            c,
            2,
            if yy < 50 {
                2000 + yy
            } else {
                1900 + yy
            },
        )
    }
}

/// GeneralizedTime `YYYYMMDDHHMMSSZ`.
pub open spec fn parse_generalized_time(c: Seq<u8>) -> Option<SpecTime> {
    if c.len() != 15 || !all_digits(c, 14) {
        None
    } else {
        parse_time_tail(c, 4, dd(c, 0) * 100 + dd(c, 2))
    }
}

/// Time ::= CHOICE { utcTime UTCTime, generalTime GeneralizedTime }
pub open spec fn parse_time(x: SpecTlv) -> Option<SpecTime> {
    if x.tag == seq![T_UTC_TIME] {
        parse_utc_time(x.content)
    } else if x.tag == seq![T_GENERALIZED_TIME] {
        parse_generalized_time(x.content)
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// AlgorithmIdentifier, SubjectPublicKeyInfo
// ---------------------------------------------------------------------------

/// AlgorithmIdentifier ::= SEQUENCE { algorithm OID, parameters ANY OPTIONAL }
pub struct SpecAlgId {
    pub oid: Seq<u8>,
    pub params: Option<SpecTlv>,
}

/// The contents of an AlgorithmIdentifier SEQUENCE.
pub open spec fn parse_alg_id(c: Seq<u8>) -> Option<SpecAlgId> {
    match parse_expect(c, T_OID) {
        None => None,
        Some((oid, r)) => if !valid_oid(oid) {
            None
        } else if r.len() == 0 {
            Some(SpecAlgId { oid, params: None })
        } else {
            match parse_only_tlv(r) {
                None => None,
                Some(p) => Some(SpecAlgId { oid, params: Some(p) }),
            }
        },
    }
}

/// SubjectPublicKeyInfo ::= SEQUENCE { algorithm AlgorithmIdentifier,
///     subjectPublicKey BIT STRING }. The key must be whole octets.
pub struct SpecSpki {
    pub alg: SpecAlgId,
    pub key: Seq<u8>,
}

pub open spec fn parse_spki(c: Seq<u8>) -> Option<SpecSpki> {
    match parse_expect(c, T_SEQUENCE) {
        None => None,
        Some((a, r)) => match parse_alg_id(a) {
            None => None,
            Some(alg) => match parse_only(r, T_BIT_STRING) {
                None => None,
                Some(k) => match parse_octet_aligned_bits(k) {
                    None => None,
                    Some(key) => Some(SpecSpki { alg, key }),
                },
            },
        },
    }
}

// ---------------------------------------------------------------------------
// Name (RFC 5280 §4.1.2.4)
// ---------------------------------------------------------------------------

/// AttributeTypeAndValue ::= SEQUENCE { type OID, value ANY }
pub struct SpecAtv {
    pub oid: Seq<u8>,
    pub value: SpecTlv,
}

pub type SpecRdn = Seq<SpecAtv>;

pub type SpecName = Seq<SpecRdn>;

pub open spec fn parse_atv(c: Seq<u8>) -> Option<SpecAtv> {
    match parse_expect(c, T_OID) {
        None => None,
        Some((oid, r)) => if !valid_oid(oid) {
            None
        } else {
            match parse_only_tlv(r) {
                None => None,
                Some(v) => Some(SpecAtv { oid, value: v }),
            }
        },
    }
}

/// The contents of a SET OF AttributeTypeAndValue.
pub open spec fn parse_atvs(s: Seq<u8>) -> Option<Seq<SpecAtv>>
    decreases s.len(),
{
    if s.len() == 0 {
        Some(Seq::empty())
    } else {
        match parse_expect(s, T_SEQUENCE) {
            None => None,
            Some((c, r)) => if r.len() >= s.len() {
                None
            } else {
                match parse_atv(c) {
                    None => None,
                    Some(a) => match parse_atvs(r) {
                        None => None,
                        Some(rest) => Some(seq![a] + rest),
                    },
                }
            },
        }
    }
}

/// RelativeDistinguishedName ::= SET SIZE (1..MAX) OF AttributeTypeAndValue
pub open spec fn parse_rdn(c: Seq<u8>) -> Option<SpecRdn> {
    match parse_atvs(c) {
        Some(a) => if a.len() == 0 {
            None
        } else {
            Some(a)
        },
        None => None,
    }
}

/// The contents of a Name: SEQUENCE OF RelativeDistinguishedName.
pub open spec fn parse_rdns(s: Seq<u8>) -> Option<SpecName>
    decreases s.len(),
{
    if s.len() == 0 {
        Some(Seq::empty())
    } else {
        match parse_expect(s, T_SET) {
            None => None,
            Some((c, r)) => if r.len() >= s.len() {
                None
            } else {
                match parse_rdn(c) {
                    None => None,
                    Some(a) => match parse_rdns(r) {
                        None => None,
                        Some(rest) => Some(seq![a] + rest),
                    },
                }
            },
        }
    }
}

// ---------------------------------------------------------------------------
// GeneralName (RFC 5280 §4.2.1.6)
// ---------------------------------------------------------------------------

/// GeneralName. Each alternative is its own variant, so one can never be
/// read as another (the type confusions of CVE-2023-0286 and CVE-2020-1971).
pub enum SpecGeneralName {
    /// [0] otherName: type-id OID and the [0] EXPLICIT value.
    Other { type_id: Seq<u8>, value: SpecTlv },
    /// [1] rfc822Name IA5String
    Rfc822(Seq<u8>),
    /// [2] dNSName IA5String
    Dns(Seq<u8>),
    /// [3] x400Address ORAddress, kept as its contents.
    X400(Seq<u8>),
    /// [4] directoryName Name
    Directory(SpecName),
    /// [5] ediPartyName, kept as its contents.
    EdiParty(Seq<u8>),
    /// [6] uniformResourceIdentifier IA5String
    Uri(Seq<u8>),
    /// [7] iPAddress OCTET STRING
    Ip(Seq<u8>),
    /// [8] registeredID OBJECT IDENTIFIER
    Registered(Seq<u8>),
}

/// otherName ::= SEQUENCE { type-id OID, value [0] EXPLICIT ANY }, IMPLICIT [0].
pub open spec fn parse_other_name(c: Seq<u8>) -> Option<SpecGeneralName> {
    match parse_expect(c, T_OID) {
        None => None,
        Some((oid, r)) => if !valid_oid(oid) {
            None
        } else {
            match parse_only(r, 0xA0) {
                None => None,
                Some(v) => match parse_only_tlv(v) {
                    None => None,
                    Some(val) => Some(SpecGeneralName::Other { type_id: oid, value: val }),
                },
            }
        },
    }
}

/// One GeneralName TLV. `subtree` selects the iPAddress form of name
/// constraints (address and mask: 8 or 32 octets) instead of 4 or 16.
pub open spec fn parse_general_name(x: SpecTlv, subtree: bool) -> Option<SpecGeneralName> {
    let c = x.content;
    if x.tag == seq![0xA0u8] {
        parse_other_name(c)
    } else if x.tag == seq![0x81u8] {
        if valid_ia5_name(c) {
            Some(SpecGeneralName::Rfc822(c))
        } else {
            None
        }
    } else if x.tag == seq![0x82u8] {
        if valid_ia5_name(c) {
            Some(SpecGeneralName::Dns(c))
        } else {
            None
        }
    } else if x.tag == seq![0xA3u8] {
        Some(SpecGeneralName::X400(c))
    } else if x.tag == seq![0xA4u8] {
        match parse_only(c, T_SEQUENCE) {
            None => None,
            Some(n) => match parse_rdns(n) {
                None => None,
                Some(name) => Some(SpecGeneralName::Directory(name)),
            },
        }
    } else if x.tag == seq![0xA5u8] {
        Some(SpecGeneralName::EdiParty(c))
    } else if x.tag == seq![0x86u8] {
        if valid_ia5_name(c) {
            Some(SpecGeneralName::Uri(c))
        } else {
            None
        }
    } else if x.tag == seq![0x87u8] {
        if (!subtree && (c.len() == 4 || c.len() == 16)) || (subtree && (c.len() == 8 || c.len()
            == 32)) {
            Some(SpecGeneralName::Ip(c))
        } else {
            None
        }
    } else if x.tag == seq![0x88u8] {
        if valid_oid(c) {
            Some(SpecGeneralName::Registered(c))
        } else {
            None
        }
    } else {
        None
    }
}

/// The contents of GeneralNames: SEQUENCE OF GeneralName.
pub open spec fn parse_general_names(s: Seq<u8>) -> Option<Seq<SpecGeneralName>>
    decreases s.len(),
{
    if s.len() == 0 {
        Some(Seq::empty())
    } else {
        match parse_tlv(s) {
            None => None,
            Some((x, r)) => if r.len() >= s.len() {
                None
            } else {
                match parse_general_name(x, false) {
                    None => None,
                    Some(g) => match parse_general_names(r) {
                        None => None,
                        Some(rest) => Some(seq![g] + rest),
                    },
                }
            },
        }
    }
}

/// GeneralNames ::= SEQUENCE SIZE (1..MAX) OF GeneralName, as contents.
pub open spec fn parse_general_names_nonempty(s: Seq<u8>) -> Option<Seq<SpecGeneralName>> {
    match parse_general_names(s) {
        Some(g) => if g.len() == 0 {
            None
        } else {
            Some(g)
        },
        None => None,
    }
}

// ---------------------------------------------------------------------------
// Extensions (RFC 5280 §4.2)
// ---------------------------------------------------------------------------

/// Extension ::= SEQUENCE { extnID OID, critical BOOLEAN DEFAULT FALSE,
///     extnValue OCTET STRING }
pub struct SpecExtension {
    pub oid: Seq<u8>,
    pub critical: bool,
    pub value: Seq<u8>,
}

pub open spec fn parse_extension(c: Seq<u8>) -> Option<SpecExtension> {
    match parse_expect(c, T_OID) {
        None => None,
        Some((oid, r)) => if !valid_oid(oid) {
            None
        } else {
            match parse_expect(r, T_BOOLEAN) {
                Some((b, r2)) => match parse_ber_bool(b) {
                    Some(crit) => match parse_only(r2, T_OCTET_STRING) {
                        None => None,
                        Some(v) => Some(SpecExtension { oid, critical: crit, value: v }),
                    },
                    None => None,
                },
                None => match parse_only(r, T_OCTET_STRING) {
                    None => None,
                    Some(v) => Some(SpecExtension { oid, critical: false, value: v }),
                },
            }
        },
    }
}

/// The contents of SEQUENCE OF Extension.
pub open spec fn parse_extensions(s: Seq<u8>) -> Option<Seq<SpecExtension>>
    decreases s.len(),
{
    if s.len() == 0 {
        Some(Seq::empty())
    } else {
        match parse_expect(s, T_SEQUENCE) {
            None => None,
            Some((c, r)) => if r.len() >= s.len() {
                None
            } else {
                match parse_extension(c) {
                    None => None,
                    Some(e) => match parse_extensions(r) {
                        None => None,
                        Some(rest) => Some(seq![e] + rest),
                    },
                }
            },
        }
    }
}

// id-ce arcs (2.5.29.x), as OID contents.
pub open spec fn oid_ce(x: u8) -> Seq<u8> {
    seq![0x55u8, 0x1Du8, x]
}

pub spec const CE_SUBJECT_KEY_ID: u8 = 14;
pub spec const CE_KEY_USAGE: u8 = 15;
pub spec const CE_SUBJECT_ALT_NAME: u8 = 17;
pub spec const CE_ISSUER_ALT_NAME: u8 = 18;
pub spec const CE_BASIC_CONSTRAINTS: u8 = 19;
pub spec const CE_NAME_CONSTRAINTS: u8 = 30;
pub spec const CE_AUTHORITY_KEY_ID: u8 = 35;
pub spec const CE_EXT_KEY_USAGE: u8 = 37;
pub spec const CE_CERTIFICATE_POLICIES: u8 = 32;

/// BasicConstraints ::= SEQUENCE { cA BOOLEAN DEFAULT FALSE,
///     pathLenConstraint INTEGER (0..MAX) OPTIONAL }
pub struct SpecBasicConstraints {
    pub ca: bool,
    pub path_len: Option<u64>,
}

pub open spec fn parse_bc_path_len(r: Seq<u8>, ca: bool) -> Option<SpecBasicConstraints> {
    if r.len() == 0 {
        Some(SpecBasicConstraints { ca, path_len: None })
    } else {
        match parse_only(r, T_INTEGER) {
            None => None,
            Some(i) => match parse_u64(i) {
                None => None,
                Some(n) => Some(SpecBasicConstraints { ca, path_len: Some(n) }),
            },
        }
    }
}

pub open spec fn parse_basic_constraints(v: Seq<u8>) -> Option<SpecBasicConstraints> {
    match parse_only(v, T_SEQUENCE) {
        None => None,
        Some(c) => match parse_expect(c, T_BOOLEAN) {
            Some((b, r)) => match parse_ber_bool(b) {
                Some(ca) => parse_bc_path_len(r, ca),
                None => None,
            },
            None => parse_bc_path_len(c, false),
        },
    }
}

/// KeyUsage ::= BIT STRING, as a 9-bit mask: bit `i` of the result is
/// KeyUsage bit `i` (digitalSignature is 0, decipherOnly is 8). Octets past
/// the second must be zero (some CAs pad the BIT STRING with them).
pub open spec fn parse_key_usage(v: Seq<u8>) -> Option<u16> {
    match parse_only(v, T_BIT_STRING) {
        None => None,
        Some(c) => match parse_bit_string(c) {
            None => None,
            Some(bs) => if !zero_from(bs.bytes, 2) {
                None
            } else {
                Some(key_usage_mask(bs.bytes))
            },
        },
    }
}

pub open spec fn zero_from(b: Seq<u8>, k: int) -> bool {
    forall|i: int| k <= i < b.len() ==> #[trigger] b[i] == 0
}

/// Reverses the bit order of an octet, so that bit 0 of the BIT STRING
/// (the most significant bit of its first octet) becomes bit 0 of the mask.
pub open spec fn rev8(b: u8) -> u16 {
    ((b / 128) % 2 + ((b / 64) % 2) * 2 + ((b / 32) % 2) * 4 + ((b / 16) % 2) * 8 + ((b / 8) % 2)
        * 16 + ((b / 4) % 2) * 32 + ((b / 2) % 2) * 64 + (b % 2) * 128) as u16
}

pub open spec fn key_usage_mask(bytes: Seq<u8>) -> u16 {
    if bytes.len() == 0 {
        0
    } else if bytes.len() == 1 {
        rev8(bytes[0])
    } else {
        (rev8(bytes[0]) + (bytes[1] / 128) as u16 * 256) as u16
    }
}

/// The contents of SEQUENCE OF KeyPurposeId (OIDs).
pub open spec fn parse_oids(s: Seq<u8>) -> Option<Seq<Seq<u8>>>
    decreases s.len(),
{
    if s.len() == 0 {
        Some(Seq::empty())
    } else {
        match parse_expect(s, T_OID) {
            None => None,
            Some((c, r)) => if r.len() >= s.len() || !valid_oid(c) {
                None
            } else {
                match parse_oids(r) {
                    None => None,
                    Some(rest) => Some(seq![c] + rest),
                }
            },
        }
    }
}

/// ExtKeyUsageSyntax ::= SEQUENCE SIZE (1..MAX) OF KeyPurposeId
pub open spec fn parse_ext_key_usage(v: Seq<u8>) -> Option<Seq<Seq<u8>>> {
    match parse_only(v, T_SEQUENCE) {
        None => None,
        Some(c) => match parse_oids(c) {
            Some(o) => if o.len() == 0 {
                None
            } else {
                Some(o)
            },
            None => None,
        },
    }
}

/// SubjectAltName and IssuerAltName ::= GeneralNames
pub open spec fn parse_alt_name(v: Seq<u8>) -> Option<Seq<SpecGeneralName>> {
    match parse_only(v, T_SEQUENCE) {
        None => None,
        Some(c) => parse_general_names_nonempty(c),
    }
}

/// SubjectKeyIdentifier ::= OCTET STRING
pub open spec fn parse_subject_key_id(v: Seq<u8>) -> Option<Seq<u8>> {
    parse_only(v, T_OCTET_STRING)
}

/// AuthorityKeyIdentifier ::= SEQUENCE {
///     keyIdentifier             [0] IMPLICIT OCTET STRING OPTIONAL,
///     authorityCertIssuer       [1] IMPLICIT GeneralNames OPTIONAL,
///     authorityCertSerialNumber [2] IMPLICIT INTEGER OPTIONAL }
pub struct SpecAuthorityKeyId {
    pub key_id: Option<Seq<u8>>,
    pub issuer: Option<Seq<SpecGeneralName>>,
    pub serial: Option<Seq<u8>>,
}

pub open spec fn parse_aki_serial(s: Seq<u8>) -> Option<Option<Seq<u8>>> {
    if s.len() == 0 {
        Some(None)
    } else {
        match parse_only(s, 0x82) {
            Some(i) => if valid_integer(i) {
                Some(Some(i))
            } else {
                None
            },
            None => None,
        }
    }
}

pub open spec fn parse_aki_issuer(s: Seq<u8>) -> Option<
    (Option<Seq<SpecGeneralName>>, Option<Seq<u8>>),
> {
    match parse_expect(s, 0xA1) {
        Some((c, r)) => match parse_general_names_nonempty(c) {
            None => None,
            Some(g) => match parse_aki_serial(r) {
                None => None,
                Some(sn) => Some((Some(g), sn)),
            },
        },
        None => match parse_aki_serial(s) {
            None => None,
            Some(sn) => Some((None, sn)),
        },
    }
}

pub open spec fn parse_authority_key_id(v: Seq<u8>) -> Option<SpecAuthorityKeyId> {
    match parse_only(v, T_SEQUENCE) {
        None => None,
        Some(c) => match parse_expect(c, 0x80) {
            Some((k, r)) => match parse_aki_issuer(r) {
                None => None,
                Some((g, sn)) => Some(SpecAuthorityKeyId { key_id: Some(k), issuer: g, serial: sn }),
            },
            None => match parse_aki_issuer(c) {
                None => None,
                Some((g, sn)) => Some(SpecAuthorityKeyId { key_id: None, issuer: g, serial: sn }),
            },
        },
    }
}

/// The contents of GeneralSubtrees: SEQUENCE OF GeneralSubtree, where
/// GeneralSubtree ::= SEQUENCE { base GeneralName, minimum [0] DEFAULT 0,
/// maximum [1] OPTIONAL }. RFC 5280 §4.2.1.10 requires minimum to be 0 and
/// maximum absent, and DER omits a default, so a subtree is its base alone.
pub open spec fn parse_subtrees(s: Seq<u8>) -> Option<Seq<SpecGeneralName>>
    decreases s.len(),
{
    if s.len() == 0 {
        Some(Seq::empty())
    } else {
        match parse_expect(s, T_SEQUENCE) {
            None => None,
            Some((c, r)) => if r.len() >= s.len() {
                None
            } else {
                match parse_only_tlv(c) {
                    None => None,
                    Some(x) => match parse_general_name(x, true) {
                        None => None,
                        Some(g) => match parse_subtrees(r) {
                            None => None,
                            Some(rest) => Some(seq![g] + rest),
                        },
                    },
                }
            },
        }
    }
}

pub open spec fn parse_subtrees_nonempty(s: Seq<u8>) -> Option<Seq<SpecGeneralName>> {
    match parse_subtrees(s) {
        Some(g) => if g.len() == 0 {
            None
        } else {
            Some(g)
        },
        None => None,
    }
}

/// NameConstraints ::= SEQUENCE { permittedSubtrees [0] GeneralSubtrees
/// OPTIONAL, excludedSubtrees [1] GeneralSubtrees OPTIONAL }; at least one
/// is present (RFC 5280 §4.2.1.10).
pub struct SpecNameConstraints {
    pub permitted: Option<Seq<SpecGeneralName>>,
    pub excluded: Option<Seq<SpecGeneralName>>,
}

pub open spec fn parse_nc_excluded(s: Seq<u8>) -> Option<Option<Seq<SpecGeneralName>>> {
    if s.len() == 0 {
        Some(None)
    } else {
        match parse_only(s, 0xA1) {
            None => None,
            Some(c) => match parse_subtrees_nonempty(c) {
                None => None,
                Some(g) => Some(Some(g)),
            },
        }
    }
}

pub open spec fn parse_name_constraints(v: Seq<u8>) -> Option<SpecNameConstraints> {
    match parse_only(v, T_SEQUENCE) {
        None => None,
        Some(c) => if c.len() == 0 {
            None
        } else {
            match parse_expect(c, 0xA0) {
                Some((p, r)) => match parse_subtrees_nonempty(p) {
                    None => None,
                    Some(g) => match parse_nc_excluded(r) {
                        None => None,
                        Some(e) => Some(SpecNameConstraints { permitted: Some(g), excluded: e }),
                    },
                },
                None => match parse_nc_excluded(c) {
                    None => None,
                    Some(e) => Some(SpecNameConstraints { permitted: None, excluded: e }),
                },
            }
        },
    }
}

/// Whether `s` is the contents of SEQUENCE OF PolicyQualifierInfo, where
/// PolicyQualifierInfo ::= SEQUENCE { policyQualifierId OID, qualifier ANY }.
pub open spec fn parse_qualifiers(s: Seq<u8>) -> bool
    decreases s.len(),
{
    if s.len() == 0 {
        true
    } else {
        match parse_expect(s, T_SEQUENCE) {
            None => false,
            Some((c, r)) => if r.len() >= s.len() {
                false
            } else {
                match parse_expect(c, T_OID) {
                    None => false,
                    Some((oid, q)) => valid_oid(oid) && parse_only_tlv(q) is Some
                        && parse_qualifiers(r),
                }
            },
        }
    }
}

/// PolicyInformation ::= SEQUENCE { policyIdentifier OID,
///     policyQualifiers SEQUENCE SIZE (1..MAX) OF PolicyQualifierInfo OPTIONAL }:
/// the policy OID.
pub open spec fn parse_policy_info(c: Seq<u8>) -> Option<Seq<u8>> {
    match parse_expect(c, T_OID) {
        None => None,
        Some((oid, r)) => if !valid_oid(oid) {
            None
        } else if r.len() == 0 {
            Some(oid)
        } else {
            match parse_only(r, T_SEQUENCE) {
                None => None,
                Some(q) => if q.len() > 0 && parse_qualifiers(q) {
                    Some(oid)
                } else {
                    None
                },
            }
        },
    }
}

/// The contents of SEQUENCE OF PolicyInformation: the policy OIDs.
pub open spec fn parse_policies(s: Seq<u8>) -> Option<Seq<Seq<u8>>>
    decreases s.len(),
{
    if s.len() == 0 {
        Some(Seq::empty())
    } else {
        match parse_expect(s, T_SEQUENCE) {
            None => None,
            Some((c, r)) => if r.len() >= s.len() {
                None
            } else {
                match parse_policy_info(c) {
                    None => None,
                    Some(o) => match parse_policies(r) {
                        None => None,
                        Some(rest) => Some(seq![o] + rest),
                    },
                }
            },
        }
    }
}

/// certificatePolicies ::= SEQUENCE SIZE (1..MAX) OF PolicyInformation
pub open spec fn parse_certificate_policies(v: Seq<u8>) -> Option<Seq<Seq<u8>>> {
    match parse_only(v, T_SEQUENCE) {
        None => None,
        Some(c) => match parse_policies(c) {
            Some(p) => if p.len() == 0 {
                None
            } else {
                Some(p)
            },
            None => None,
        },
    }
}

/// The contents of every extension this crate decodes are well-formed;
/// other extensions are kept as bytes, whether critical or not (deciding what
/// to do with an unknown critical extension is path validation's job).
pub open spec fn known_extension_ok(e: SpecExtension) -> bool {
    if e.oid == oid_ce(CE_BASIC_CONSTRAINTS) {
        parse_basic_constraints(e.value) is Some
    } else if e.oid == oid_ce(CE_KEY_USAGE) {
        parse_key_usage(e.value) is Some
    } else if e.oid == oid_ce(CE_EXT_KEY_USAGE) {
        parse_ext_key_usage(e.value) is Some
    } else if e.oid == oid_ce(CE_SUBJECT_ALT_NAME) || e.oid == oid_ce(CE_ISSUER_ALT_NAME) {
        parse_alt_name(e.value) is Some
    } else if e.oid == oid_ce(CE_SUBJECT_KEY_ID) {
        parse_subject_key_id(e.value) is Some
    } else if e.oid == oid_ce(CE_AUTHORITY_KEY_ID) {
        parse_authority_key_id(e.value) is Some
    } else if e.oid == oid_ce(CE_NAME_CONSTRAINTS) {
        parse_name_constraints(e.value) is Some
    } else if e.oid == oid_ce(CE_CERTIFICATE_POLICIES) {
        parse_certificate_policies(e.value) is Some
    } else {
        true
    }
}

/// RFC 5280 §4.2: a certificate MUST NOT include more than one instance of a
/// particular extension.
pub open spec fn distinct_oids(e: Seq<SpecExtension>) -> bool {
    forall|i: int, j: int| 0 <= i < j < e.len() ==> #[trigger] e[i].oid != #[trigger] e[j].oid
}

pub open spec fn valid_extensions(e: Seq<SpecExtension>) -> bool {
    &&& distinct_oids(e)
    &&& forall|i: int| 0 <= i < e.len() ==> known_extension_ok(#[trigger] e[i])
}

/// The extension with this OID, if any (there is at most one).
pub open spec fn find_extension(e: Seq<SpecExtension>, oid: Seq<u8>) -> Option<SpecExtension>
    decreases e.len(),
{
    if e.len() == 0 {
        None
    } else if e[0].oid == oid {
        Some(e[0])
    } else {
        find_extension(e.drop_first(), oid)
    }
}

// ---------------------------------------------------------------------------
// Certificate (RFC 5280 §4.1)
// ---------------------------------------------------------------------------

/// TBSCertificate. `version` is 0 for v1, 1 for v2, 2 for v3.
pub struct SpecTbs {
    pub version: u8,
    /// The INTEGER contents (two's complement, minimal).
    pub serial: Seq<u8>,
    pub signature: SpecAlgId,
    pub issuer: SpecName,
    pub not_before: SpecTime,
    pub not_after: SpecTime,
    pub subject: SpecName,
    pub spki: SpecSpki,
    pub issuer_uid: Option<SpecBitString>,
    pub subject_uid: Option<SpecBitString>,
    pub extensions: Seq<SpecExtension>,
}

pub struct SpecCertificate {
    /// The DER bytes of the TBSCertificate, which the signature covers.
    pub tbs_der: Seq<u8>,
    pub tbs: SpecTbs,
    pub signature_alg: SpecAlgId,
    pub signature: Seq<u8>,
}

/// version [0] EXPLICIT Version DEFAULT v1. DER omits the default, so an
/// encoded version is v2 or v3: `Some((version, rest))`.
pub open spec fn parse_version(s: Seq<u8>) -> Option<(u8, Seq<u8>)> {
    match parse_expect(s, 0xA0) {
        Some((c, r)) => match parse_only(c, T_INTEGER) {
            Some(v) => if v == seq![1u8] {
                Some((1u8, r))
            } else if v == seq![2u8] {
                Some((2u8, r))
            } else {
                None
            },
            None => None,
        },
        None => Some((0u8, s)),
    }
}

/// Validity ::= SEQUENCE { notBefore Time, notAfter Time }
pub open spec fn parse_validity(c: Seq<u8>) -> Option<(SpecTime, SpecTime)> {
    match parse_tlv(c) {
        None => None,
        Some((a, r)) => match parse_time(a) {
            None => None,
            Some(nb) => match parse_only_tlv(r) {
                None => None,
                Some(b) => match parse_time(b) {
                    None => None,
                    Some(na) => Some((nb, na)),
                },
            },
        },
    }
}

/// An optional `[n] IMPLICIT BIT STRING` unique identifier, only allowed in
/// v2 and v3 certificates (RFC 5280 §4.1.2.8).
pub open spec fn parse_uid(s: Seq<u8>, t: u8, version: u8) -> Option<
    (Option<SpecBitString>, Seq<u8>),
> {
    match parse_expect(s, t) {
        Some((c, r)) => if version == 0 {
            None
        } else {
            match parse_bit_string(c) {
                None => None,
                Some(b) => Some((Some(b), r)),
            }
        },
        None => Some((None, s)),
    }
}

/// extensions [3] EXPLICIT SEQUENCE SIZE (1..MAX) OF Extension, only in v3.
/// `s` is everything after subjectUniqueID and must be the extensions or
/// nothing.
pub open spec fn parse_tbs_extensions(s: Seq<u8>, version: u8) -> Option<Seq<SpecExtension>> {
    if s.len() == 0 {
        Some(Seq::empty())
    } else if version != 2 {
        None
    } else {
        match parse_only(s, 0xA3) {
            None => None,
            Some(c) => match parse_only(c, T_SEQUENCE) {
                None => None,
                Some(l) => match parse_extensions(l) {
                    None => None,
                    Some(e) => if e.len() == 0 || !valid_extensions(e) {
                        None
                    } else {
                        Some(e)
                    },
                },
            },
        }
    }
}

/// The contents of TBSCertificate, after the version.
pub open spec fn parse_tbs_body(version: u8, s: Seq<u8>) -> Option<SpecTbs> {
    match parse_expect(s, T_INTEGER) {
        None => None,
        Some((serial, s1)) => if !valid_integer(serial) {
            None
        } else {
            match parse_expect(s1, T_SEQUENCE) {
                None => None,
                Some((sa, s2)) => match parse_alg_id(sa) {
                    None => None,
                    Some(signature) => match parse_expect(s2, T_SEQUENCE) {
                        None => None,
                        Some((iss, s3)) => match parse_rdns(iss) {
                            None => None,
                            Some(issuer) => match parse_expect(s3, T_SEQUENCE) {
                                None => None,
                                Some((val, s4)) => match parse_validity(val) {
                                    None => None,
                                    Some((nb, na)) => match parse_expect(s4, T_SEQUENCE) {
                                        None => None,
                                        Some((sub, s5)) => match parse_rdns(sub) {
                                            None => None,
                                            Some(subject) => match parse_expect(s5, T_SEQUENCE) {
                                                None => None,
                                                Some((pk, s6)) => match parse_spki_seq(pk) {
                                                    None => None,
                                                    Some(spki) => parse_tbs_tail(
                                                        version,
                                                        serial,
                                                        signature,
                                                        issuer,
                                                        nb,
                                                        na,
                                                        subject,
                                                        spki,
                                                        s6,
                                                    ),
                                                },
                                            },
                                        },
                                    },
                                },
                            },
                        },
                    },
                },
            }
        },
    }
}

/// The contents of the SubjectPublicKeyInfo SEQUENCE.
pub open spec fn parse_spki_seq(c: Seq<u8>) -> Option<SpecSpki> {
    parse_spki(c)
}

pub open spec fn parse_tbs_tail(
    version: u8,
    serial: Seq<u8>,
    signature: SpecAlgId,
    issuer: SpecName,
    nb: SpecTime,
    na: SpecTime,
    subject: SpecName,
    spki: SpecSpki,
    s6: Seq<u8>,
) -> Option<SpecTbs> {
    match parse_uid(s6, 0x81, version) {
        None => None,
        Some((iu, s7)) => match parse_uid(s7, 0x82, version) {
            None => None,
            Some((su, s8)) => match parse_tbs_extensions(s8, version) {
                None => None,
                Some(extensions) => Some(
                    SpecTbs {
                        version,
                        serial,
                        signature,
                        issuer,
                        not_before: nb,
                        not_after: na,
                        subject,
                        spki,
                        issuer_uid: iu,
                        subject_uid: su,
                        extensions,
                    },
                ),
            },
        },
    }
}

/// The contents of the TBSCertificate SEQUENCE.
pub open spec fn parse_tbs(c: Seq<u8>) -> Option<SpecTbs> {
    match parse_version(c) {
        None => None,
        Some((v, r)) => parse_tbs_body(v, r),
    }
}

/// The DER length of the TLV at the start of `s` (header and contents).
pub open spec fn tlv_len(s: Seq<u8>) -> int {
    match parse_tlv(s) {
        Some((_, r)) => s.len() - r.len(),
        None => 0,
    }
}

/// Certificate ::= SEQUENCE { tbsCertificate TBSCertificate,
///     signatureAlgorithm AlgorithmIdentifier, signatureValue BIT STRING }
///
/// `b` must be exactly one certificate. The signatureAlgorithm must be
/// identical to the signature field inside the TBSCertificate (RFC 5280
/// §4.1.1.2), and the signature must be whole octets.
pub open spec fn parse_certificate(b: Seq<u8>) -> Option<SpecCertificate> {
    match parse_only(b, T_SEQUENCE) {
        None => None,
        Some(c) => match parse_expect(c, T_SEQUENCE) {
            None => None,
            Some((t, r1)) => match parse_tbs(t) {
                None => None,
                Some(tbs) => match parse_expect(r1, T_SEQUENCE) {
                    None => None,
                    Some((a, r2)) => match parse_alg_id(a) {
                        None => None,
                        Some(alg) => if alg != tbs.signature {
                            None
                        } else {
                            match parse_only(r2, T_BIT_STRING) {
                                None => None,
                                Some(sig) => match parse_octet_aligned_bits(sig) {
                                    None => None,
                                    Some(signature) => Some(
                                        SpecCertificate {
                                            tbs_der: c.subrange(0, c.len() - r1.len()),
                                            tbs,
                                            signature_alg: alg,
                                            signature,
                                        },
                                    ),
                                },
                            }
                        },
                    },
                },
            },
        },
    }
}

} // verus!
