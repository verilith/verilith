//! Verified decoding of certificate extensions (RFC 5280 §4.2).
use crate::der::*;
use crate::spec::*;
use crate::x509::*;
use vstd::prelude::*;

verus! {

/// One extension, borrowed.
#[derive(Clone, Copy)]
pub struct Extension<'a> {
    pub oid: &'a [u8],
    pub critical: bool,
    /// The extnValue OCTET STRING's contents.
    pub value: &'a [u8],
}

impl<'a> View for Extension<'a> {
    type V = SpecExtension;

    open spec fn view(&self) -> SpecExtension {
        SpecExtension { oid: self.oid@, critical: self.critical, value: self.value@ }
    }
}

#[inline(always)]
pub fn read_extension<'a>(c: &'a [u8]) -> (r: Option<Extension<'a>>)
    ensures
        r matches Some(e) ==> parse_extension(c@) == Some(e@),
        r is None ==> parse_extension(c@) is None,
{
    read_extension_m(c).0
}

/// `read_extension`, with its steps (at most two for each octet of the OID).
#[inline(always)]
pub fn read_extension_m<'a>(c: &'a [u8]) -> (r: (Option<Extension<'a>>, Ghost<nat>))
    ensures
        r.0 matches Some(e) ==> parse_extension(c@) == Some(e@),
        r.0 matches Some(e) ==> e.oid@.len() + e.value@.len() + 4 <= c@.len() && r.1@ <= 2
            * e.oid@.len(),
        r.0 is None ==> parse_extension(c@) is None,
        r.1@ <= 2 * c@.len(),
{
    let (oid, r) = match read_expect(c, 0x06) {
        Some(x) => x,
        None => return (None, Ghost(0)),
    };
    let (ok, st) = check_oid_m(oid);
    if !ok {
        return (None, st);
    }
    match read_expect(r, 0x01) {
        Some((b, r2)) => {
            if b.len() != 1 {
                return (None, st);
            }
            match read_only(r2, 0x04) {
                Some(v) => (Some(Extension { oid, critical: b[0] != 0, value: v }), st),
                None => (None, st),
            }
        },
        None => match read_only(r, 0x04) {
            Some(v) => (Some(Extension { oid, critical: false, value: v }), st),
            None => (None, st),
        },
    }
}

/// Whether `oid` is id-ce `x` (2.5.29.x).
#[inline(always)]
pub fn oid_is_ce(oid: &[u8], x: u8) -> (r: bool)
    ensures
        r == (oid@ == oid_ce(x)),
{
    let r = oid.len() == 3 && oid[0] == 0x55 && oid[1] == 0x1D && oid[2] == x;
    proof {
        if r {
            assert(oid@ =~= oid_ce(x));
        }
        if oid@ == oid_ce(x) {
            assert(oid@[0] == oid_ce(x)[0] && oid@[1] == oid_ce(x)[1] && oid@[2] == oid_ce(x)[2]);
        }
    }
    r
}

// ---------------------------------------------------------------------------
// Typed extensions
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct BasicConstraints {
    pub ca: bool,
    pub path_len: Option<u64>,
}

impl View for BasicConstraints {
    type V = SpecBasicConstraints;

    open spec fn view(&self) -> SpecBasicConstraints {
        SpecBasicConstraints { ca: self.ca, path_len: self.path_len }
    }
}

fn read_bc_path_len(r: &[u8], ca: bool) -> (out: Option<BasicConstraints>)
    ensures
        out matches Some(b) ==> parse_bc_path_len(r@, ca) == Some(b@),
        out is None ==> parse_bc_path_len(r@, ca) is None,
{
    if r.len() == 0 {
        return Some(BasicConstraints { ca, path_len: None });
    }
    match read_only(r, 0x02) {
        None => None,
        Some(i) => match read_u64(i) {
            None => None,
            Some(n) => Some(BasicConstraints { ca, path_len: Some(n) }),
        },
    }
}

pub fn read_basic_constraints(v: &[u8]) -> (out: Option<BasicConstraints>)
    ensures
        out matches Some(b) ==> parse_basic_constraints(v@) == Some(b@),
        out is None ==> parse_basic_constraints(v@) is None,
{
    let c = match read_only(v, 0x30) {
        Some(c) => c,
        None => return None,
    };
    match read_expect(c, 0x01) {
        Some((b, r)) => if b.len() == 1 {
            read_bc_path_len(r, b[0] != 0)
        } else {
            None
        },
        None => read_bc_path_len(c, false),
    }
}

#[inline(always)]
fn rev8_exec(b: u8) -> (r: u16)
    ensures
        r == rev8(b),
{
    ((b / 128) % 2 + ((b / 64) % 2) * 2 + ((b / 32) % 2) * 4 + ((b / 16) % 2) * 8 + ((b / 8) % 2)
        * 16 + ((b / 4) % 2) * 32 + ((b / 2) % 2) * 64 + (b % 2) * 128) as u16
}

/// KeyUsage as a 9-bit mask (bit 0 is digitalSignature).
pub fn read_key_usage(v: &[u8]) -> (out: Option<u16>)
    ensures
        out == parse_key_usage(v@),
{
    match read_key_usage_bits(v).0 {
        Some((k, _)) => Some(k),
        None => None,
    }
}

/// `read_key_usage`, with the BIT STRING's octets.
#[inline]
pub fn read_key_usage_bits<'a>(v: &'a [u8]) -> (out: (Option<(u16, &'a [u8])>, Ghost<nat>))
    ensures
        out.1@ <= v@.len(),
        out.0 matches Some((k, b)) ==> parse_key_usage(v@) == Some(k) && (match parse_only(v@, T_BIT_STRING) {
            Some(c) => match parse_bit_string(c) {
                Some(bs) => bs.bytes == b@,
                None => false,
            },
            None => false,
        }),
        out.0 is None ==> parse_key_usage(v@) is None,
{
    let c = match read_only(v, 0x03) {
        Some(c) => c,
        None => return (None, Ghost(0)),
    };
    let bs = match read_bit_string(c) {
        Some(b) => b,
        None => return (None, Ghost(0)),
    };
    let n = bs.bytes.len();
    let mut i: usize = 2;
    while i < n
        invariant
            parse_only(v@, T_BIT_STRING) == Some(c@),
            parse_bit_string(c@) == Some(bs@),
            n == bs.bytes@.len(),
            n < v@.len(),
            2 <= i,
            n >= 2 ==> i <= n,
            forall|j: int| 2 <= j < i && j < n ==> #[trigger] bs.bytes@[j] == 0,
        decreases n - i,
    {
        if bs.bytes[i] != 0 {
            proof {
                assert(!zero_from(bs.bytes@, 2));
            }
            return (None, Ghost(i as nat));
        }
        i = i + 1;
    }
    let ghost st: nat = i as nat;
    if n == 0 {
        (Some((0, bs.bytes)), Ghost(0))
    } else if n == 1 {
        (Some((rev8_exec(bs.bytes[0]), bs.bytes)), Ghost(0))
    } else {
        (Some((rev8_exec(bs.bytes[0]) + (bs.bytes[1] / 128) as u16 * 256, bs.bytes)), Ghost(st))
    }
}

/// ExtKeyUsage: the contents of its SEQUENCE OF OID.
pub fn read_ext_key_usage<'a>(v: &'a [u8]) -> (out: Option<&'a [u8]>)
    ensures
        out matches Some(l) ==> parse_only(v@, T_SEQUENCE) == Some(l@),
        out matches Some(l) ==> parse_ext_key_usage(v@) == Some(parse_oids(l@).unwrap()) && parse_oids(l@) is Some,
        out is None ==> parse_ext_key_usage(v@) is None,
{
    read_ext_key_usage_m(v).0
}

/// `read_ext_key_usage`, with its steps.
pub fn read_ext_key_usage_m<'a>(v: &'a [u8]) -> (out: (Option<&'a [u8]>, Ghost<nat>))
    ensures
        out.0 matches Some(l) ==> parse_only(v@, T_SEQUENCE) == Some(l@),
        out.0 matches Some(l) ==> parse_ext_key_usage(v@) == Some(parse_oids(l@).unwrap()) && parse_oids(l@) is Some,
        out.0 is None ==> parse_ext_key_usage(v@) is None,
        out.1@ <= 2 * v@.len(),
{
    match read_only(v, 0x30) {
        Some(c) => {
            if c.len() == 0 {
                return (None, Ghost(0));
            }
            let (ok, st) = check_oids(c);
            if ok {
                (Some(c), st)
            } else {
                (None, st)
            }
        },
        None => (None, Ghost(0)),
    }
}

/// SubjectAltName / IssuerAltName: the contents of its GeneralNames.
pub fn read_alt_name<'a>(v: &'a [u8]) -> (out: Option<&'a [u8]>)
    ensures
        out matches Some(l) ==> parse_only(v@, T_SEQUENCE) == Some(l@),
        out matches Some(l) ==> parse_alt_name(v@) == Some(parse_general_names(l@).unwrap()) && parse_general_names(l@) is Some,
        out is None ==> parse_alt_name(v@) is None,
{
    read_alt_name_m(v).0
}

/// `read_alt_name`, with its steps.
pub fn read_alt_name_m<'a>(v: &'a [u8]) -> (out: (Option<&'a [u8]>, Ghost<nat>))
    ensures
        out.0 matches Some(l) ==> parse_only(v@, T_SEQUENCE) == Some(l@),
        out.0 matches Some(l) ==> parse_alt_name(v@) == Some(parse_general_names(l@).unwrap()) && parse_general_names(l@) is Some,
        out.0 is None ==> parse_alt_name(v@) is None,
        out.1@ <= 2 * v@.len(),
{
    match read_only(v, 0x30) {
        Some(c) => {
            let (ok, st) = check_general_names_nonempty(c);
            if ok {
                (Some(c), st)
            } else {
                (None, st)
            }
        },
        None => (None, Ghost(0)),
    }
}

/// AuthorityKeyIdentifier, borrowed. `issuer` is the contents of the
/// GeneralNames.
#[derive(Clone, Copy)]
pub struct AuthorityKeyId<'a> {
    pub key_id: Option<&'a [u8]>,
    pub issuer: Option<&'a [u8]>,
    pub serial: Option<&'a [u8]>,
}

pub open spec fn opt_bytes_view(o: Option<&[u8]>) -> Option<Seq<u8>> {
    match o {
        Some(s) => Some(s@),
        None => None,
    }
}

pub open spec fn opt_general_names_view(o: Option<&[u8]>) -> Option<Seq<SpecGeneralName>> {
    match o {
        Some(s) => Some(parse_general_names(s@).unwrap()),
        None => None,
    }
}

impl<'a> View for AuthorityKeyId<'a> {
    type V = SpecAuthorityKeyId;

    open spec fn view(&self) -> SpecAuthorityKeyId {
        SpecAuthorityKeyId {
            key_id: opt_bytes_view(self.key_id),
            issuer: opt_general_names_view(self.issuer),
            serial: opt_bytes_view(self.serial),
        }
    }
}

fn read_aki_serial<'a>(s: &'a [u8]) -> (out: Option<Option<&'a [u8]>>)
    ensures
        out matches Some(o) ==> parse_aki_serial(s@) == Some(opt_bytes_view(o)),
        out is None ==> parse_aki_serial(s@) is None,
{
    if s.len() == 0 {
        return Some(None);
    }
    match read_only(s, 0x82) {
        Some(i) => if check_integer(i) {
            Some(Some(i))
        } else {
            None
        },
        None => None,
    }
}

fn read_aki_issuer<'a>(s: &'a [u8]) -> (out: (Option<(Option<&'a [u8]>, Option<&'a [u8]>)>, Ghost<nat>))
    ensures
        out.0 matches Some((g, sn)) ==> parse_aki_issuer(s@) == Some(
            (opt_general_names_view(g), opt_bytes_view(sn)),
        ) && (g matches Some(l) ==> parse_general_names(l@) is Some),
        out.0 is None ==> parse_aki_issuer(s@) is None,
        out.1@ <= 2 * s@.len(),
{
    match read_expect(s, 0xA1) {
        Some((c, r)) => {
            let (ok, st) = check_general_names_nonempty(c);
            if !ok {
                return (None, st);
            }
            match read_aki_serial(r) {
                None => (None, st),
                Some(sn) => (Some((Some(c), sn)), st),
            }
        },
        None => match read_aki_serial(s) {
            None => (None, Ghost(0)),
            Some(sn) => (Some((None, sn)), Ghost(0)),
        },
    }
}

pub fn read_authority_key_id<'a>(v: &'a [u8]) -> (out: Option<AuthorityKeyId<'a>>)
    ensures
        out matches Some(a) ==> parse_authority_key_id(v@) == Some(a@) && (a.issuer matches Some(
            l,
        ) ==> parse_general_names(l@) is Some),
        out is None ==> parse_authority_key_id(v@) is None,
{
    read_authority_key_id_m(v).0
}

/// `read_authority_key_id`, with its steps.
pub fn read_authority_key_id_m<'a>(v: &'a [u8]) -> (out: (Option<AuthorityKeyId<'a>>, Ghost<nat>))
    ensures
        out.0 matches Some(a) ==> parse_authority_key_id(v@) == Some(a@) && (a.issuer matches Some(
            l,
        ) ==> parse_general_names(l@) is Some),
        out.0 is None ==> parse_authority_key_id(v@) is None,
        out.1@ <= 2 * v@.len(),
{
    let c = match read_only(v, 0x30) {
        Some(c) => c,
        None => return (None, Ghost(0)),
    };
    match read_expect(c, 0x80) {
        Some((k, r)) => {
            let (i, st) = read_aki_issuer(r);
            match i {
                None => (None, st),
                Some((g, sn)) => (Some(AuthorityKeyId { key_id: Some(k), issuer: g, serial: sn }), st),
            }
        },
        None => {
            let (i, st) = read_aki_issuer(c);
            match i {
                None => (None, st),
                Some((g, sn)) => (Some(AuthorityKeyId { key_id: None, issuer: g, serial: sn }), st),
            }
        },
    }
}

/// NameConstraints, borrowed: the contents of each GeneralSubtrees.
#[derive(Clone, Copy)]
pub struct NameConstraints<'a> {
    pub permitted: Option<&'a [u8]>,
    pub excluded: Option<&'a [u8]>,
}

pub open spec fn opt_subtrees_view(o: Option<&[u8]>) -> Option<Seq<SpecGeneralName>> {
    match o {
        Some(s) => Some(parse_subtrees(s@).unwrap()),
        None => None,
    }
}

/// Both lists, when present, are GeneralSubtrees that parse (so a
/// `SubtreeIter` can walk them).
pub open spec fn nc_lists_wf(n: NameConstraints) -> bool {
    &&& n.permitted matches Some(l) ==> parse_subtrees(l@) is Some
    &&& n.excluded matches Some(l) ==> parse_subtrees(l@) is Some
}

impl<'a> View for NameConstraints<'a> {
    type V = SpecNameConstraints;

    open spec fn view(&self) -> SpecNameConstraints {
        SpecNameConstraints {
            permitted: opt_subtrees_view(self.permitted),
            excluded: opt_subtrees_view(self.excluded),
        }
    }
}

fn read_nc_excluded<'a>(s: &'a [u8]) -> (out: (Option<Option<&'a [u8]>>, Ghost<nat>))
    ensures
        out.0 matches Some(o) ==> parse_nc_excluded(s@) == Some(opt_subtrees_view(o)) && (o matches Some(
            l,
        ) ==> parse_subtrees(l@) is Some),
        out.0 is None ==> parse_nc_excluded(s@) is None,
        out.1@ <= 2 * s@.len(),
{
    if s.len() == 0 {
        return (Some(None), Ghost(0));
    }
    match read_only(s, 0xA1) {
        None => (None, Ghost(0)),
        Some(c) => {
            let (ok, st) = check_subtrees_nonempty(c);
            if ok {
                (Some(Some(c)), st)
            } else {
                (None, st)
            }
        },
    }
}

pub fn read_name_constraints<'a>(v: &'a [u8]) -> (out: Option<NameConstraints<'a>>)
    ensures
        out matches Some(n) ==> parse_name_constraints(v@) == Some(n@) && nc_lists_wf(n),
        out is None ==> parse_name_constraints(v@) is None,
{
    read_name_constraints_m(v).0
}

/// `read_name_constraints`, with its steps.
pub fn read_name_constraints_m<'a>(v: &'a [u8]) -> (out: (Option<NameConstraints<'a>>, Ghost<nat>))
    ensures
        out.0 matches Some(n) ==> parse_name_constraints(v@) == Some(n@) && nc_lists_wf(n),
        out.0 is None ==> parse_name_constraints(v@) is None,
        out.1@ <= 2 * v@.len(),
{
    let c = match read_only(v, 0x30) {
        Some(c) => c,
        None => return (None, Ghost(0)),
    };
    if c.len() == 0 {
        return (None, Ghost(0));
    }
    match read_expect(c, 0xA0) {
        Some((p, r)) => {
            let (ok, s1) = check_subtrees_nonempty(p);
            if !ok {
                return (None, s1);
            }
            let (e, s2) = read_nc_excluded(r);
            match e {
                None => (None, Ghost(s1@ + s2@)),
                Some(e) => (Some(NameConstraints { permitted: Some(p), excluded: e }), Ghost(s1@ + s2@)),
            }
        },
        None => {
            let (e, st) = read_nc_excluded(c);
            match e {
                None => (None, st),
                Some(e) => (Some(NameConstraints { permitted: None, excluded: e }), st),
            }
        },
    }
}

fn check_qualifiers(s: &[u8]) -> (r: (bool, Ghost<nat>))
    ensures
        r.0 == parse_qualifiers(s@),
        r.1@ <= 2 * s@.len(),
{
    let mut cur = s;
    let ghost mut st: nat = 0;
    while cur.len() > 0
        invariant
            parse_qualifiers(s@) == parse_qualifiers(cur@),
            cur@.len() <= s@.len(),
            st <= 2 * (s@.len() - cur@.len()),
        decreases cur@.len(),
    {
        let (c, r) = match read_expect(cur, 0x30) {
            Some(x) => x,
            None => return (false, Ghost(st)),
        };
        proof {
            lemma_tlv_shrinks(cur@);
        }
        let (oid, q) = match read_expect(c, 0x06) {
            Some(x) => x,
            None => return (false, Ghost(st)),
        };
        let (ok, s1) = check_oid_m(oid);
        proof {
            st = st + 1 + s1@;
        }
        if !ok || read_only_tlv(q).is_none() {
            return (false, Ghost(st));
        }
        cur = r;
    }
    (true, Ghost(st))
}

pub fn read_policy_info<'a>(c: &'a [u8]) -> (r: Option<&'a [u8]>)
    ensures
        r matches Some(o) ==> parse_policy_info(c@) == Some(o@),
        r is None ==> parse_policy_info(c@) is None,
{
    read_policy_info_m(c).0
}

/// `read_policy_info`, with its steps.
pub fn read_policy_info_m<'a>(c: &'a [u8]) -> (r: (Option<&'a [u8]>, Ghost<nat>))
    ensures
        r.0 matches Some(o) ==> parse_policy_info(c@) == Some(o@),
        r.0 is None ==> parse_policy_info(c@) is None,
        r.1@ <= 2 * c@.len(),
{
    let (oid, r) = match read_expect(c, 0x06) {
        Some(x) => x,
        None => return (None, Ghost(0)),
    };
    let (ok, s1) = check_oid_m(oid);
    if !ok {
        return (None, s1);
    }
    if r.len() == 0 {
        return (Some(oid), s1);
    }
    let q = match read_only(r, 0x30) {
        Some(q) => q,
        None => return (None, s1),
    };
    if q.len() == 0 {
        return (None, s1);
    }
    let (ok2, s2) = check_qualifiers(q);
    if ok2 {
        (Some(oid), Ghost(s1@ + s2@))
    } else {
        (None, Ghost(s1@ + s2@))
    }
}

pub fn check_policies(s: &[u8]) -> (r: (bool, Ghost<nat>))
    ensures
        r.0 == parse_policies(s@) is Some,
        r.1@ <= 2 * s@.len(),
{
    let mut cur = s;
    let ghost mut st: nat = 0;
    while cur.len() > 0
        invariant
            (parse_policies(s@) is Some) == (parse_policies(cur@) is Some),
            cur@.len() <= s@.len(),
            st <= 2 * (s@.len() - cur@.len()),
        decreases cur@.len(),
    {
        let (c, r) = match read_expect(cur, 0x30) {
            Some(x) => x,
            None => return (false, Ghost(st)),
        };
        proof {
            lemma_tlv_shrinks(cur@);
        }
        let (p, s1) = read_policy_info_m(c);
        proof {
            st = st + 1 + s1@;
        }
        if p.is_none() {
            return (false, Ghost(st));
        }
        cur = r;
    }
    (true, Ghost(st))
}

/// certificatePolicies: the contents of its SEQUENCE OF PolicyInformation.
pub fn read_certificate_policies<'a>(v: &'a [u8]) -> (out: Option<&'a [u8]>)
    ensures
        out matches Some(l) ==> parse_only(v@, T_SEQUENCE) == Some(l@),
        out matches Some(l) ==> parse_certificate_policies(v@) == Some(parse_policies(l@).unwrap()) && parse_policies(l@) is Some,
        out is None ==> parse_certificate_policies(v@) is None,
{
    read_certificate_policies_m(v).0
}

/// `read_certificate_policies`, with its steps.
pub fn read_certificate_policies_m<'a>(v: &'a [u8]) -> (out: (Option<&'a [u8]>, Ghost<nat>))
    ensures
        out.0 matches Some(l) ==> parse_only(v@, T_SEQUENCE) == Some(l@),
        out.0 matches Some(l) ==> parse_certificate_policies(v@) == Some(parse_policies(l@).unwrap()) && parse_policies(l@) is Some,
        out.0 is None ==> parse_certificate_policies(v@) is None,
        out.1@ <= 2 * v@.len(),
{
    match read_only(v, 0x30) {
        Some(c) => {
            if c.len() == 0 {
                return (None, Ghost(0));
            }
            let (ok, st) = check_policies(c);
            if ok {
                (Some(c), st)
            } else {
                (None, st)
            }
        },
        None => (None, Ghost(0)),
    }
}

/// What `decode_known_extension` decoded from an extension's value, for the
/// mbedTLS adapter: `kind` is the id-ce arc (2.5.29.x) whose fields are
/// set, or 0 when the value was not decoded here. BasicConstraints (19) sets
/// `ca` and `path_len`. KeyUsage (15) sets `a` to the BIT STRING's octets.
/// ExtKeyUsage (37), SubjectAltName (17), IssuerAltName (18) and
/// certificatePolicies (32) set `a` to the SEQUENCE's contents, and
/// SubjectKeyIdentifier (14) to its octets. AuthorityKeyIdentifier (35)
/// sets `a` (when `a_some`) to its key identifier, `b` to the contents of
/// its GeneralNames and `c` to its serial number.
#[derive(Clone, Copy)]
pub struct Decoded<'a> {
    pub kind: u8,
    pub ca: bool,
    pub a_some: bool,
    pub path_len: Option<u64>,
    pub a: &'a [u8],
    pub b: Option<&'a [u8]>,
    pub c: Option<&'a [u8]>,
}

pub fn no_decoded<'a>() -> (d: Decoded<'a>)
    ensures
        d.kind == 0 && !d.a_some,
{
    Decoded { kind: 0, ca: false, a_some: false, path_len: None, a: &[], b: None, c: None }
}

/// `d` holds what the spec says `e`'s value is, for the fields its kind
/// sets.
pub open spec fn decoded_ok(e: SpecExtension, d: Decoded) -> bool {
    &&& (d.kind != 0 ==> e.oid == oid_ce(d.kind))
    &&& (d.kind == 19 ==> parse_basic_constraints(e.value) == Some(SpecBasicConstraints { ca: d.ca, path_len: d.path_len }))
    &&& (d.kind == 15 ==> parse_key_usage(e.value) is Some && (match parse_only(e.value, T_BIT_STRING) {
        Some(c) => match parse_bit_string(c) {
            Some(bs) => bs.bytes == d.a@,
            None => false,
        },
        None => false,
    }))
    &&& (d.kind == 37 ==> parse_ext_key_usage(e.value) is Some && parse_only(e.value, T_SEQUENCE) == Some(d.a@))
    &&& ((d.kind == 17 || d.kind == 18) ==> parse_alt_name(e.value) is Some && parse_only(e.value, T_SEQUENCE) == Some(d.a@))
    &&& (d.kind == 32 ==> parse_certificate_policies(e.value) is Some && parse_only(e.value, T_SEQUENCE) == Some(d.a@))
    &&& (d.kind == 14 ==> parse_subject_key_id(e.value) == Some(d.a@))
    &&& (d.kind == 35 ==> parse_authority_key_id(e.value) == Some(SpecAuthorityKeyId {
        key_id: if d.a_some { Some(d.a@) } else { None },
        issuer: opt_general_names_view(d.b),
        serial: opt_bytes_view(d.c),
    }))
}

fn dec_bc<'a>(v: &'a [u8]) -> (r: Option<Decoded<'a>>)
    ensures
        r is Some == parse_basic_constraints(v@) is Some,
        r matches Some(d) ==> d.kind == 19 && parse_basic_constraints(v@) == Some(
            SpecBasicConstraints { ca: d.ca, path_len: d.path_len },
        ),
{
    let mut d = no_decoded();
    match read_basic_constraints(v) {
        Some(b) => {
            d.kind = 19;
            d.ca = b.ca;
            d.path_len = b.path_len;
            Some(d)
        },
        None => None,
    }
}

fn dec_ku<'a>(v: &'a [u8]) -> (r: (Option<Decoded<'a>>, Ghost<nat>))
    ensures
        r.1@ <= v@.len(),
        r.0 is Some == parse_key_usage(v@) is Some,
        r.0 matches Some(d) ==> d.kind == 15 && (match parse_only(v@, T_BIT_STRING) {
            Some(c) => match parse_bit_string(c) {
                Some(bs) => bs.bytes == d.a@,
                None => false,
            },
            None => false,
        }),
{
    let mut d = no_decoded();
    let (k, st) = read_key_usage_bits(v);
    match k {
        Some((_, b)) => {
            d.kind = 15;
            d.a = b;
            (Some(d), st)
        },
        None => (None, st),
    }
}

fn dec_aki<'a>(v: &'a [u8]) -> (r: (Option<Decoded<'a>>, Ghost<nat>))
    ensures
        r.1@ <= 2 * v@.len(),
        r.0 is Some == parse_authority_key_id(v@) is Some,
        r.0 matches Some(d) ==> d.kind == 35 && parse_authority_key_id(v@) == Some(SpecAuthorityKeyId {
            key_id: if d.a_some { Some(d.a@) } else { None },
            issuer: opt_general_names_view(d.b),
            serial: opt_bytes_view(d.c),
        }),
{
    let mut d = no_decoded();
    let (a, st) = read_authority_key_id_m(v);
    match a {
        Some(a) => {
            d.kind = 35;
            match a.key_id {
                Some(k) => {
                    d.a_some = true;
                    d.a = k;
                },
                None => {},
            }
            d.b = a.issuer;
            d.c = a.serial;
            assert(opt_bytes_view(a.key_id) == (if d.a_some { Some(d.a@) } else { None }));
            assert(a@ == SpecAuthorityKeyId {
                key_id: if d.a_some { Some(d.a@) } else { None },
                issuer: opt_general_names_view(d.b),
                serial: opt_bytes_view(d.c),
            });
            (Some(d), st)
        },
        None => (None, st),
    }
}

/// `check_known_extension`, keeping what it decoded.
#[verifier::spinoff_prover]
#[inline(always)]
pub fn decode_known_extension<'a>(e: &Extension<'a>) -> (r: (Option<Decoded<'a>>, Ghost<nat>))
    ensures
        r.0 is Some == known_extension_ok(e@),
        r.0 matches Some(d) ==> decoded_ok(e@, d),
        r.1@ <= 2 * e.value@.len(),
{
    let oid = e.oid;
    let v = e.value;
    proof {
        lemma_ce(oid@, 19);
        lemma_ce(oid@, 15);
        lemma_ce(oid@, 37);
        lemma_ce(oid@, 17);
        lemma_ce(oid@, 18);
        lemma_ce(oid@, 14);
        lemma_ce(oid@, 35);
        lemma_ce(oid@, 30);
        lemma_ce(oid@, 32);
    }
    let mut d = no_decoded();
    if !(oid.len() == 3 && oid[0] == 0x55 && oid[1] == 0x1D) {
        return (Some(d), Ghost(0));
    }
    let x = oid[2];
    if x == 19 {
        (dec_bc(v), Ghost(0))
    } else if x == 15 {
        dec_ku(v)
    } else if x == 35 {
        dec_aki(v)
    } else if x == 37 || x == 17 || x == 18 || x == 32 {
        let (l, st) = if x == 37 {
            read_ext_key_usage_m(v)
        } else if x == 32 {
            read_certificate_policies_m(v)
        } else {
            read_alt_name_m(v)
        };
        match l {
            Some(l) => {
                d.kind = x;
                d.a = l;
                (Some(d), st)
            },
            None => (None, st),
        }
    } else if x == 14 {
        match read_only(v, 0x04) {
            Some(k) => {
                d.kind = 14;
                d.a = k;
                (Some(d), Ghost(0))
            },
            None => (None, Ghost(0)),
        }
    } else if x == 30 {
        let (n, st) = read_name_constraints_m(v);
        if n.is_some() {
            (Some(d), st)
        } else {
            (None, st)
        }
    } else {
        (Some(d), Ghost(0))
    }
}

/// Checks the contents of every extension this crate decodes.
proof fn lemma_ce(oid: Seq<u8>, c: u8)
    ensures
        (oid == oid_ce(c)) == (oid.len() == 3 && oid[0] == 0x55 && oid[1] == 0x1D && oid[2] == c),
{
    if oid.len() == 3 && oid[0] == 0x55 && oid[1] == 0x1D && oid[2] == c {
        assert(oid =~= oid_ce(c));
    }
}

pub fn check_known_extension(e: &Extension) -> (r: bool)
    ensures
        r == known_extension_ok(e@),
{
    let oid = e.oid;
    let v = e.value;
    proof {
        lemma_ce(oid@, 19);
        lemma_ce(oid@, 15);
        lemma_ce(oid@, 37);
        lemma_ce(oid@, 17);
        lemma_ce(oid@, 18);
        lemma_ce(oid@, 14);
        lemma_ce(oid@, 35);
        lemma_ce(oid@, 30);
        lemma_ce(oid@, 32);
    }
    // Every extension decoded here is id-ce (2.5.29.x).
    if !(oid.len() == 3 && oid[0] == 0x55 && oid[1] == 0x1D) {
        return true;
    }
    let x = oid[2];
    if x == 19 {
        read_basic_constraints(v).is_some()
    } else if x == 15 {
        read_key_usage(v).is_some()
    } else if x == 37 {
        read_ext_key_usage(v).is_some()
    } else if x == 17 || x == 18 {
        read_alt_name(v).is_some()
    } else if x == 14 {
        read_only(v, 0x04).is_some()
    } else if x == 35 {
        read_authority_key_id(v).is_some()
    } else if x == 30 {
        read_name_constraints(v).is_some()
    } else if x == 32 {
        read_certificate_policies(v).is_some()
    } else {
        true
    }
}

/// `Some(acc + xs)` if `o` is `Some(xs)`.
pub open spec fn prepend<T>(acc: Seq<T>, o: Option<Seq<T>>) -> Option<Seq<T>> {
    match o {
        Some(xs) => Some(acc + xs),
        None => None,
    }
}

/// One step through a well-formed extensions list.
pub proof fn lemma_ext_list_unfold(s: Seq<u8>, c: Seq<u8>, r: Seq<u8>)
    requires
        s.len() > 0,
        parse_extensions(s) is Some,
        parse_expect(s, T_SEQUENCE) == Some((c, r)),
    ensures
        parse_extension(c) is Some,
        parse_extensions(r) is Some,
        parse_extensions(s).unwrap() == seq![parse_extension(c).unwrap()] + parse_extensions(
            r,
        ).unwrap(),
{
}

/// The same, also giving the extension's OID.
pub proof fn lemma_ext_list_step(s: Seq<u8>, c: Seq<u8>, r: Seq<u8>, oid: Seq<u8>, x: Seq<u8>)
    requires
        s.len() > 0,
        parse_extensions(s) is Some,
        parse_expect(s, T_SEQUENCE) == Some((c, r)),
        parse_expect(c, T_OID) == Some((oid, x)),
    ensures
        parse_extension(c) is Some,
        parse_extension(c).unwrap().oid == oid,
        parse_extensions(r) is Some,
        parse_extensions(s).unwrap() == seq![parse_extension(c).unwrap()] + parse_extensions(
            r,
        ).unwrap(),
{
    lemma_ext_list_unfold(s, c, r);
}

/// Whether no extension in `b`, which is `all.skip(j)`, has OID `oid`.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
fn oid_absent(bs: &[u8], oid: &[u8], Ghost(all): Ghost<Seq<SpecExtension>>, Ghost(i): Ghost<int>, Ghost(j): Ghost<int>) -> (r: (bool, Ghost<nat>))
    requires
        0 <= i < j <= all.len(),
        oid@ == all[i].oid,
        parse_extensions(bs@) == Some(all.skip(j)),
    ensures
        r.0 == forall|q: int| j <= q < all.len() ==> all[i].oid != #[trigger] all[q].oid,
        r.1@ <= bs@.len(),
{
    let ghost b0 = bs@;
    let mut b = bs;
    let ghost mut k: int = j;
    let ghost mut st: nat = 0;
    while b.len() > 0
        invariant
            0 <= i < j <= k <= all.len(),
            oid@ == all[i].oid,
            parse_extensions(b@) == Some(all.skip(k)),
            forall|q: int| j <= q < k ==> all[i].oid != #[trigger] all[q].oid,
            b0 == bs@,
            b@.len() <= b0.len(),
            st <= b0.len() - b@.len(),
        decreases b@.len(),
    {
        let (c2, r2) = match read_expect(b, 0x30) {
            Some(x) => x,
            None => {
                proof {
                    assert(false);
                }
                return (false, Ghost(st));
            },
        };
        proof {
            lemma_tlv_shrinks(b@);
        }
        let (oid2, _x2) = match read_expect(c2, 0x06) {
            Some(x) => x,
            None => {
                proof {
                    lemma_ext_list_unfold(b@, c2@, r2@);
                    assert(false);
                }
                return (false, Ghost(st));
            },
        };
        proof {
            lemma_ext_list_step(b@, c2@, r2@, oid2@, _x2@);
            let e2 = parse_extension(c2@).unwrap();
            lemma_skip_step(all, k, e2, parse_extensions(r2@).unwrap());
        }
        let (eq, s1) = bytes_eq_m(oid, oid2);
        proof {
            st = st + 1 + s1@;
            assert(st <= b0.len() - r2@.len());
        }
        if eq {
            return (false, Ghost(st));
        }
        b = r2;
        proof {
            k = k + 1;
        }
    }
    proof {
        assert(all.skip(k).len() == 0);
    }
    (true, Ghost(st))
}

/// Whether two OIDs differ; looks at the last octets first, where OIDs of
/// the same arc (id-ce, id-pe) differ.
#[inline(always)]
fn oid_ne(a: &[u8], b: &[u8]) -> (r: (bool, Ghost<nat>))
    ensures
        r.0 == (a@ != b@),
        r.1@ <= b@.len(),
{
    if a.len() != b.len() {
        return (true, Ghost(0));
    }
    if a.len() > 0 && a[a.len() - 1] != b[b.len() - 1] {
        proof {
            assert(a@[a@.len() - 1] != b@[b@.len() - 1]);
        }
        return (true, Ghost(0));
    }
    let (eq, st) = bytes_eq_m(a, b);
    (!eq, st)
}

/// How many OIDs outside the low id-ce arcs `check_extensions` keeps to find
/// duplicates in one pass; lists with more take the slower second pass.
pub const MAX_OTHER_EXTENSIONS: usize = 8;

/// An id-ce OID (2.5.29.x) with x below 64: `check_extensions` remembers
/// these as bits of one word.
pub open spec fn small_ce(oid: Seq<u8>) -> bool {
    oid.len() == 3 && oid[0] == 0x55 && oid[1] == 0x1D && oid[2] < 64
}

pub open spec fn bit(m: u64, x: u64) -> bool {
    (m >> x) & 1 == 1
}

pub open spec fn has_ce(acc: Seq<SpecExtension>, x: u64) -> bool {
    exists|k: int| 0 <= k < acc.len() && small_ce(#[trigger] acc[k].oid) && acc[k].oid[2] as u64 == x
}

pub open spec fn has_oid(acc: Seq<SpecExtension>, o: Seq<u8>) -> bool {
    exists|k: int| 0 <= k < acc.len() && #[trigger] acc[k].oid == o
}

pub open spec fn kept(others: Seq<&[u8]>, m: int, o: Seq<u8>) -> bool {
    exists|j: int| 0 <= j < m && (#[trigger] others[j])@ == o
}

proof fn lemma_bit_zero(x: u64)
    requires
        x < 64,
    ensures
        !bit(0, x),
{
    assert((0u64 >> x) & 1 != 1) by (bit_vector)
        requires
            x < 64,
    ;
}

proof fn lemma_bit_set(m: u64, x: u64, y: u64)
    requires
        x < 64,
        y < 64,
    ensures
        bit(m | (1u64 << x), y) == (y == x || bit(m, y)),
{
    assert((((m | (1u64 << x)) >> y) & 1 == 1) == (y == x || (m >> y) & 1 == 1)) by (bit_vector)
        requires
            x < 64,
            y < 64,
    ;
}

proof fn lemma_has_ce_push(acc: Seq<SpecExtension>, e: SpecExtension, x: u64)
    ensures
        has_ce(acc.push(e), x) == (has_ce(acc, x) || (small_ce(e.oid) && e.oid[2] as u64 == x)),
{
    let acc2 = acc.push(e);
    if has_ce(acc, x) {
        let k = choose|k: int| 0 <= k < acc.len() && small_ce(#[trigger] acc[k].oid) && acc[k].oid[2] as u64 == x;
        assert(acc2[k] == acc[k]);
    }
    if small_ce(e.oid) && e.oid[2] as u64 == x {
        assert(acc2[acc.len() as int] == e);
    }
    if has_ce(acc2, x) {
        let k = choose|k: int| 0 <= k < acc2.len() && small_ce(#[trigger] acc2[k].oid) && acc2[k].oid[2] as u64 == x;
        if k < acc.len() {
            assert(acc2[k] == acc[k]);
        }
    }
}

proof fn lemma_has_oid_push(acc: Seq<SpecExtension>, e: SpecExtension, o: Seq<u8>)
    ensures
        has_oid(acc.push(e), o) == (has_oid(acc, o) || e.oid == o),
{
    let acc2 = acc.push(e);
    if has_oid(acc, o) {
        let k = choose|k: int| 0 <= k < acc.len() && #[trigger] acc[k].oid == o;
        assert(acc2[k] == acc[k]);
    }
    if e.oid == o {
        assert(acc2[acc.len() as int] == e);
    }
    if has_oid(acc2, o) {
        let k = choose|k: int| 0 <= k < acc2.len() && #[trigger] acc2[k].oid == o;
        if k < acc.len() {
            assert(acc2[k] == acc[k]);
        }
    }
}

/// `acc` with `e`, whose OID none of `acc` has, still has distinct OIDs.
proof fn lemma_distinct_push(acc: Seq<SpecExtension>, e: SpecExtension)
    requires
        distinct_oids(acc),
        !has_oid(acc, e.oid),
    ensures
        distinct_oids(acc.push(e)),
{
    let acc2 = acc.push(e);
    assert forall|p: int, q: int| 0 <= p < q < acc2.len() implies #[trigger] acc2[p].oid != #[trigger] acc2[q].oid by {
        if q < acc.len() {
            assert(acc2[p] == acc[p] && acc2[q] == acc[q]);
        } else {
            assert(acc2[p] == acc[p] && acc2[q] == e);
        }
    }
}

/// `acc`, then `e` with the OID of one of `acc`, then `rest`: not distinct.
proof fn lemma_dup(acc: Seq<SpecExtension>, e: SpecExtension, rest: Seq<SpecExtension>)
    requires
        has_oid(acc, e.oid),
    ensures
        !distinct_oids(acc + (seq![e] + rest)),
{
    let all = acc + (seq![e] + rest);
    let k = choose|k: int| 0 <= k < acc.len() && #[trigger] acc[k].oid == e.oid;
    assert(all[k] == acc[k]);
    assert(all[acc.len() as int] == e);
}

/// Whether `oid` is one of the first `m` OIDs kept.
fn oid_kept(others: &[&[u8]; MAX_OTHER_EXTENSIONS], m: usize, oid: &[u8]) -> (r: (bool, Ghost<nat>))
    requires
        m <= MAX_OTHER_EXTENSIONS,
    ensures
        r.0 == kept(others@, m as int, oid@),
        r.1@ <= 8 * oid@.len(),
{
    let mut j: usize = 0;
    let ghost mut st: nat = 0;
    while j < m
        invariant
            j <= m,
            m <= MAX_OTHER_EXTENSIONS,
            forall|k: int| 0 <= k < j ==> (#[trigger] others@[k])@ != oid@,
            st <= j * oid@.len(),
        decreases m - j,
    {
        let (ne, s1) = oid_ne(others[j], oid);
        proof {
            assert(st + s1@ <= (j + 1) * oid@.len()) by (nonlinear_arith)
                requires
                    st <= j * oid@.len(),
                    s1@ <= oid@.len(),
            ;
            st = st + s1@;
        }
        if !ne {
            proof {
                assert((j + 1) * oid@.len() <= 8 * oid@.len()) by (nonlinear_arith)
                    requires
                        j < 8,
                ;
            }
            return (true, Ghost(st));
        }
        j = j + 1;
    }
    proof {
        assert(j * oid@.len() <= 8 * oid@.len()) by (nonlinear_arith)
            requires
                j <= 8,
        ;
    }
    (false, Ghost(st))
}

/// What `check_extensions` remembers of the OIDs of `acc`, which are
/// distinct: the low id-ce arcs as the bits of `seen`, the others as the
/// first `m` of `others`.
pub open spec fn tracked(seen: u64, others: Seq<&[u8]>, m: usize, acc: Seq<SpecExtension>) -> bool {
    &&& m <= MAX_OTHER_EXTENSIONS
    &&& forall|x: u64| x < 64 ==> (#[trigger] bit(seen, x) <==> has_ce(acc, x))
    &&& forall|j: int| 0 <= j < m ==> has_oid(acc, (#[trigger] others[j])@)
    &&& forall|k: int|
        0 <= k < acc.len() && !small_ce(#[trigger] acc[k].oid) ==> kept(others, m as int, acc[k].oid)
    &&& distinct_oids(acc)
}

/// Looks up the OID of `e`, the extension after `acc`: 0 if one of `acc`
/// has it, 1 if not and it is now remembered too, 2 if not and there is no
/// room to remember it.
#[inline(always)]
fn note_oid<'a>(
    seen: &mut u64,
    others: &mut [&'a [u8]; MAX_OTHER_EXTENSIONS],
    m: &mut usize,
    oid: &'a [u8],
    Ghost(acc): Ghost<Seq<SpecExtension>>,
    Ghost(e): Ghost<SpecExtension>,
) -> (r: (u8, Ghost<nat>))
    requires
        tracked(*old(seen), old(others)@, *old(m), acc),
        e.oid == oid@,
    ensures
        r.0 <= 2,
        r.0 == 0 ==> has_oid(acc, e.oid),
        r.0 == 1 ==> tracked(*final(seen), final(others)@, *final(m), acc.push(e)),
        r.1@ <= 8 * oid@.len(),
{
    let ghost acc2 = acc.push(e);
    if oid.len() == 3 && oid[0] == 0x55 && oid[1] == 0x1D && oid[2] < 64 {
        let x = oid[2] as u64;
        assert(small_ce(e.oid));
        if (*seen >> x) & 1 == 1 {
            proof {
                assert(bit(*seen, x));
                assert(has_ce(acc, x));
                let k = choose|k: int| 0 <= k < acc.len() && small_ce(#[trigger] acc[k].oid) && acc[k].oid[2] as u64 == x;
                assert(acc[k].oid =~= e.oid);
            }
            return (0, Ghost(0));
        }
        let ghost seen0 = *seen;
        *seen = *seen | (1u64 << x);
        proof {
            assert(!bit(seen0, x));
            if has_oid(acc, e.oid) {
                let k = choose|k: int| 0 <= k < acc.len() && #[trigger] acc[k].oid == e.oid;
                assert(has_ce(acc, x));
            }
            lemma_distinct_push(acc, e);
            assert forall|y: u64| y < 64 implies (#[trigger] bit(*seen, y) <==> has_ce(acc2, y)) by {
                lemma_bit_set(seen0, x, y);
                lemma_has_ce_push(acc, e, y);
            }
            assert forall|j: int| 0 <= j < *m implies has_oid(acc2, (#[trigger] others@[j])@) by {
                lemma_has_oid_push(acc, e, others@[j]@);
            }
            assert forall|k: int| 0 <= k < acc2.len() && !small_ce(#[trigger] acc2[k].oid) implies kept(
                others@,
                *m as int,
                acc2[k].oid,
            ) by {
                assert(acc2[k] == acc[k]);
            }
        }
        (1, Ghost(0))
    } else {
        assert(!small_ce(e.oid));
        let (kp, st) = oid_kept(others, *m, oid);
        if kp {
            proof {
                let j = choose|j: int| 0 <= j < *m && (#[trigger] others@[j])@ == oid@;
                assert(has_oid(acc, others@[j]@));
            }
            return (0, st);
        }
        if *m == MAX_OTHER_EXTENSIONS {
            return (2, st);
        }
        let ghost others0 = others@;
        let ghost m0 = *m as int;
        others[*m] = oid;
        proof {
            if has_oid(acc, e.oid) {
                let k = choose|k: int| 0 <= k < acc.len() && #[trigger] acc[k].oid == e.oid;
                assert(kept(others0, m0, acc[k].oid));
            }
            lemma_distinct_push(acc, e);
            assert forall|y: u64| y < 64 implies (#[trigger] bit(*seen, y) <==> has_ce(acc2, y)) by {
                lemma_has_ce_push(acc, e, y);
            }
            assert forall|j: int| 0 <= j < m0 + 1 implies has_oid(acc2, (#[trigger] others@[j])@) by {
                lemma_has_oid_push(acc, e, others@[j]@);
                if j < m0 {
                    assert(others@[j] == others0[j]);
                }
            }
            assert forall|k: int| 0 <= k < acc2.len() && !small_ce(#[trigger] acc2[k].oid) implies kept(
                others@,
                m0 + 1,
                acc2[k].oid,
            ) by {
                if k < acc.len() {
                    assert(acc2[k] == acc[k]);
                    let j = choose|j: int| 0 <= j < m0 && (#[trigger] others0[j])@ == acc[k].oid;
                    assert(others@[j] == others0[j]);
                } else {
                    assert(others@[m0]@ == acc2[k].oid);
                }
            }
        }
        *m = *m + 1;
        (1, st)
    }
}

/// One extension as `check_extensions_rec` read it, and what it decoded
/// from the value, for the mbedTLS adapter.
#[derive(Clone, Copy)]
pub struct ExtOut<'a> {
    pub ext: Extension<'a>,
    pub dec: Decoded<'a>,
}

/// Receives each extension, in order, as `check_extensions_rec` reads it,
/// with what it decoded from the value (the mbedTLS adapter takes them from
/// here instead of walking the list again). `log` is what it has been given
/// so far.
pub trait ExtSink<'a> {
    spec fn log(&self) -> Seq<ExtOut<'a>>;

    fn push(&mut self, e: Extension<'a>, d: Decoded<'a>)
        ensures
            final(self).log() == old(self).log().push(ExtOut { ext: e, dec: d }),
    ;
}

/// The sink that keeps nothing.
pub struct NoExts<'a> {
    pub seen: Ghost<Seq<ExtOut<'a>>>,
}

impl<'a> ExtSink<'a> for NoExts<'a> {
    open spec fn log(&self) -> Seq<ExtOut<'a>> {
        self.seen@
    }

    #[inline(always)]
    fn push(&mut self, e: Extension<'a>, d: Decoded<'a>) {
        proof {
            self.seen@ = self.seen@.push(ExtOut { ext: e, dec: d });
        }
    }
}

pub fn no_exts<'a>() -> (o: NoExts<'a>) {
    NoExts { seen: Ghost(Seq::empty()) }
}

/// `now` is `before` followed by one record for each of `exts`, in order,
/// each with what the spec says its value decodes to.
pub open spec fn ext_log_ok(before: Seq<ExtOut>, now: Seq<ExtOut>, exts: Seq<SpecExtension>) -> bool {
    &&& now.len() == before.len() + exts.len()
    &&& forall|k: int| 0 <= k < before.len() ==> #[trigger] now[k] == before[k]
    &&& forall|k: int|
        0 <= k < exts.len() ==> now[before.len() + k].ext@ == #[trigger] exts[k] && decoded_ok(
            exts[k],
            now[before.len() + k].dec,
        )
}

/// Whether `l`, the contents of the extensions SEQUENCE, is a non-empty
/// list of well-formed extensions with distinct OIDs.
pub fn check_extensions(l: &[u8]) -> (r: bool)
    ensures
        r == (parse_extensions(l@) matches Some(e) && e.len() > 0 && valid_extensions(e)),
{
    let mut x = no_exts();
    check_extensions_rec(l, &mut x).0
}

/// Steps `check_extensions_rec` takes for each octet of the list, besides
/// the duplicate check of `pass2`.
pub spec const EXT_STEPS: nat = 10;

/// `check_extensions`, giving the extensions and their decoded values to
/// `list`.
pub fn check_extensions_rec<'a, S: ExtSink<'a>>(l: &'a [u8], list: &mut S) -> (r: (bool, Ghost<nat>))
    ensures
        r.0 == (parse_extensions(l@) matches Some(e) && e.len() > 0 && valid_extensions(e)),
        r.0 ==> ext_log_ok(old(list).log(), final(list).log(), parse_extensions(l@).unwrap()),
        r.1@ <= EXT_STEPS * l@.len() + dup_cost(l@.len() as nat),
{
    let ghost prev = list.log();
    if l.len() == 0 {
        return (false, Ghost(0));
    }
    let ghost mut st: nat = 0;
    // Every extension is well-formed and its OID differs from the ones
    // before it: the low id-ce arcs seen so far are the bits of `seen`,
    // and up to MAX_OTHER_EXTENSIONS other OIDs are kept in `others`.
    let mut cur = l;
    let ghost mut acc: Seq<SpecExtension> = Seq::empty();
    let mut seen: u64 = 0;
    let mut others: [&[u8]; MAX_OTHER_EXTENSIONS] = [l; MAX_OTHER_EXTENSIONS];
    let mut m: usize = 0;
    let mut many = false;
    proof {
        assert(acc + parse_extensions(cur@).unwrap() =~= parse_extensions(cur@).unwrap());
        assert forall|x: u64| x < 64 implies (#[trigger] bit(seen, x) <==> has_ce(acc, x)) by {
            lemma_bit_zero(x);
        }
        assert(tracked(seen, others@, m, acc));
    }
    while cur.len() > 0
        invariant
            parse_extensions(l@) == prepend(acc, parse_extensions(cur@)),
            forall|k: int| 0 <= k < acc.len() ==> known_extension_ok(#[trigger] acc[k]),
            l@.len() > 0 ==> (cur@.len() < l@.len() <==> acc.len() > 0),
            cur@.len() <= l@.len(),
            !many ==> tracked(seen, others@, m, acc),
            ext_log_ok(prev, list.log(), acc),
            st <= EXT_STEPS * (l@.len() - cur@.len()),
        decreases cur@.len(),
    {
        let ghost st0 = st;
        let (c, r) = match read_expect(cur, 0x30) {
            Some(x) => x,
            None => return (false, Ghost(st)),
        };
        proof {
            lemma_tlv_shrinks(cur@);
        }
        let (e, s1) = read_extension_m(c);
        let e = match e {
            Some(e) => e,
            None => return (false, Ghost(st + 1 + s1@)),
        };
        let (dec, s2) = decode_known_extension(&e);
        proof {
            st = st + 1 + s1@ + s2@;
        }
        let dec = match dec {
            Some(d) => d,
            None => {
            proof {
                if let Some(rest) = parse_extensions(r@) {
                    let all = acc + (seq![e@] + rest);
                    assert(all[acc.len() as int] == e@);
                }
            }
                return (false, Ghost(st));
            },
        };
        list.push(e, dec);
        proof {
            let acc2 = acc.push(e@);
            assert forall|k: int| 0 <= k < acc2.len() implies list.log()[prev.len() + k].ext@ == #[trigger] acc2[k]
                && decoded_ok(acc2[k], list.log()[prev.len() + k].dec) by {
                if k < acc.len() {
                    assert(acc2[k] == acc[k]);
                }
            }
        }

        if !many {
            let (t, s3) = note_oid(&mut seen, &mut others, &mut m, e.oid, Ghost(acc), Ghost(e@));
            proof {
                st = st + s3@;
            }
            if t == 0 {
                proof {
                    if let Some(rest) = parse_extensions(r@) {
                        lemma_dup(acc, e@, rest);
                    }
                    lemma_dup_cost_nonneg(l@.len() as nat);
                }
                return (false, Ghost(st));
            }
            if t == 2 {
                many = true;
            }
        }
        proof {
            assert(st <= st0 + EXT_STEPS * (cur@.len() - r@.len()));
        }
        proof {
            if let Some(rest) = parse_extensions(r@) {
                lemma_concat_step(acc, e@, rest);
            }
            acc = acc.push(e@);
        }
        cur = r;
    }
    let ghost all = acc;
    proof {
        assert(acc + Seq::<SpecExtension>::empty() =~= acc);
        assert(all.len() > 0);
        lemma_dup_cost_nonneg(l@.len() as nat);
    }
    if !many {
        return (true, Ghost(st));
    }
    let (ok, s4) = pass2(l, Ghost(all));
    (ok, Ghost(st + s4@))
}

/// Steps the duplicate check of `pass2` may take for an `n`-octet list:
/// with `alloc`, `n` for each halving of a merge sort; without it, `n`
/// for each extension.
#[cfg(feature = "alloc")]
pub open spec fn dup_cost(n: nat) -> nat {
    n * (crate::dedup::depth(n) + 2)
}

#[cfg(not(feature = "alloc"))]
pub open spec fn dup_cost(n: nat) -> nat {
    n * n
}

pub proof fn lemma_dup_cost_nonneg(n: nat)
    ensures
        dup_cost(n) >= 0,
{
}

#[cfg(feature = "alloc")]
pub proof fn lemma_dup_cost_mono(a: nat, b: nat)
    requires
        a <= b,
    ensures
        dup_cost(a) <= dup_cost(b),
{
    crate::dedup::lemma_depth_mono(a, b);
    let da = crate::dedup::depth(a) + 2;
    let db = crate::dedup::depth(b) + 2;
    assert(a * da <= b * db) by (nonlinear_arith)
        requires
            a <= b,
            da <= db,
    ;
}

#[cfg(not(feature = "alloc"))]
pub proof fn lemma_dup_cost_mono(a: nat, b: nat)
    requires
        a <= b,
    ensures
        dup_cost(a) <= dup_cost(b),
{
    assert(a * a <= b * b) by (nonlinear_arith)
        requires
            a <= b,
    ;
}

/// Pass 2 of `check_extensions`, which runs only when the list has more
/// than `MAX_OTHER_EXTENSIONS` OIDs outside the low id-ce arcs: whether the
/// OIDs of `all`, which `l` parses to, are distinct. With `alloc` it sorts
/// them (`dedup`); without, it compares each with every later one.
#[cfg(feature = "alloc")]
#[cold]
#[inline(never)]
fn pass2(l: &[u8], Ghost(all): Ghost<Seq<SpecExtension>>) -> (r: (bool, Ghost<nat>))
    requires
        parse_extensions(l@) == Some(all),
    ensures
        r.0 == distinct_oids(all),
        r.1@ <= dup_cost(l@.len() as nat),
{
    crate::dedup::distinct_sorted(l, Ghost(all))
}

#[cfg(not(feature = "alloc"))]
#[cold]
#[inline(never)]
fn pass2(l: &[u8], Ghost(all): Ghost<Seq<SpecExtension>>) -> (r: (bool, Ghost<nat>))
    requires
        parse_extensions(l@) == Some(all),
    ensures
        r.0 == distinct_oids(all),
        r.1@ <= dup_cost(l@.len() as nat),
{
    distinct_extension_oids(l, Ghost(all))
}

proof fn lemma_quad_step(st: nat, s1: nat, x: nat, d: nat, n: nat)
    requires
        st <= x * n,
        1 + s1 <= n,
        d >= 1,
        x + d <= n,
    ensures
        st + 1 + s1 <= (x + d) * n,
        (x + d) * n <= n * n,
{
    assert((x + d) * n <= n * n) by (nonlinear_arith)
        requires
            x + d <= n,
    ;
    assert(st + 1 + s1 <= (x + d) * n) by (nonlinear_arith)
        requires
            st <= x * n,
            1 + s1 <= n,
            d >= 1,
    ;
}

/// Pass 2 of `check_extensions`: whether the OIDs of `all`, which `l`
/// parses to, are distinct.
#[cfg_attr(feature = "alloc", allow(dead_code))]
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
fn distinct_extension_oids(l: &[u8], Ghost(all): Ghost<Seq<SpecExtension>>) -> (r: (bool, Ghost<nat>))
    requires
        parse_extensions(l@) == Some(all),
    ensures
        r.0 == distinct_oids(all),
        r.1@ <= l@.len() * l@.len(),
{
    let mut a = l;
    let ghost mut i: int = 0;
    let ghost mut st: nat = 0;
    let ghost n = l@.len();
    proof {
        assert(all.skip(0) =~= all);
    }
    while a.len() > 0
        invariant
            parse_extensions(l@) == Some(all),
            0 <= i <= all.len(),
            parse_extensions(a@) == Some(all.skip(i)),
            forall|p: int, q: int|
                0 <= p < i && p < q < all.len() ==> #[trigger] all[p].oid != #[trigger] all[q].oid,
            n == l@.len(),
            a@.len() <= n,
            st <= (n - a@.len()) * n,
        decreases a@.len(),
    {
        let (c, r) = match read_expect(a, 0x30) {
            Some(x) => x,
            None => {
                proof {
                    assert(false);
                }
                return (false, Ghost(st));
            },
        };
        proof {
            lemma_tlv_shrinks(a@);
        }
        let (oid, _x) = match read_expect(c, 0x06) {
            Some(x) => x,
            None => {
                proof {
                    lemma_ext_list_unfold(a@, c@, r@);
                    assert(false);
                }
                return (false, Ghost(st));
            },
        };
        proof {
            lemma_ext_list_step(a@, c@, r@, oid@, _x@);
            let e = parse_extension(c@).unwrap();
            lemma_skip_step(all, i, e, parse_extensions(r@).unwrap());
        }
        let (absent, s1) = oid_absent(r, oid, Ghost(all), Ghost(i), Ghost(i + 1));
        proof {
            lemma_quad_step(st, s1@, (n - a@.len()) as nat, (a@.len() - r@.len()) as nat, n);
            st = st + 1 + s1@;
        }
        if !absent {
            proof {
                let q = choose|q: int| i + 1 <= q < all.len() && all[i].oid == #[trigger] all[q].oid;
                assert(!distinct_oids(all));
            }
            return (false, Ghost(st));
        }
        proof {
            assert forall|p: int, q: int| 0 <= p < i + 1 && p < q < all.len() implies #[trigger] all[p].oid
                != #[trigger] all[q].oid by {
                if p == i {
                    assert(i + 1 <= q < all.len());
                }
            }
        }
        a = r;
        proof {
            i = i + 1;
        }
    }
    proof {
        assert(all.skip(i).len() == 0);
    }
    (true, Ghost(st))
}

/// The extension with OID `oid` in a well-formed extensions list.
pub fn find_extension_in<'a>(l: &'a [u8], oid: &[u8]) -> (r: Option<Extension<'a>>)
    requires
        parse_extensions(l@) is Some,
    ensures
        r matches Some(e) ==> find_extension(parse_extensions(l@).unwrap(), oid@) == Some(e@),
        r is None ==> find_extension(parse_extensions(l@).unwrap(), oid@) is None,
{
    let ghost all = parse_extensions(l@).unwrap();
    let mut a = l;
    let ghost mut i: int = 0;
    proof {
        assert(all.skip(0) =~= all);
    }
    while a.len() > 0
        invariant
            all == parse_extensions(l@).unwrap(),
            0 <= i <= all.len(),
            parse_extensions(a@) == Some(all.skip(i)),
            find_extension(all, oid@) == find_extension(all.skip(i), oid@),
        decreases a@.len(),
    {
        let (c, r) = match read_expect(a, 0x30) {
            Some(x) => x,
            None => {
                proof {
                    assert(false);
                }
                return None;
            },
        };
        proof {
            lemma_tlv_shrinks(a@);
        }
        let e = match read_extension(c) {
            Some(e) => e,
            None => {
                proof {
                    assert(false);
                }
                return None;
            },
        };
        proof {
            lemma_ext_list_unfold(a@, c@, r@);
            lemma_skip_step(all, i, e@, parse_extensions(r@).unwrap());
            assert(all.skip(i).drop_first() =~= all.skip(i + 1));
        }
        if bytes_eq(e.oid, oid) {
            proof {
                assert(all.skip(i)[0] == all[i]);
            }
            return Some(e);
        }
        a = r;
        proof {
            i = i + 1;
        }
    }
    None
}

} // verus!
