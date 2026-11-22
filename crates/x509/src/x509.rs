//! Verified decoding of the X.509 building blocks: AlgorithmIdentifier,
//! SubjectPublicKeyInfo, Name and GeneralName.
use crate::der::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

pub open spec fn opt_tlv_view(p: Option<Tlv>) -> Option<SpecTlv> {
    match p {
        Some(t) => Some(t@),
        None => None,
    }
}

/// `acc + (seq![e] + rest) == acc.push(e) + rest`
pub proof fn lemma_concat_step<T>(acc: Seq<T>, e: T, rest: Seq<T>)
    ensures
        acc + (seq![e] + rest) == acc.push(e) + rest,
{
    assert(acc + (seq![e] + rest) =~= acc.push(e) + rest);
}

/// After parsing `seq![e] + rest == all.skip(i)`, `e` is `all[i]` and
/// `rest` is `all.skip(i + 1)`.
pub proof fn lemma_skip_step<T>(all: Seq<T>, i: int, e: T, rest: Seq<T>)
    requires
        0 <= i <= all.len(),
        seq![e] + rest == all.skip(i),
    ensures
        i < all.len(),
        all[i] == e,
        rest == all.skip(i + 1),
{
    assert((seq![e] + rest)[0] == e);
    assert(all.skip(i).len() == all.len() - i);
    assert forall|k: int| 0 <= k < rest.len() implies rest[k] == all.skip(i + 1)[k] by {
        assert(rest[k] == (seq![e] + rest)[k + 1]);
    }
    assert(rest =~= all.skip(i + 1));
}

/// AlgorithmIdentifier, borrowed.
#[derive(Clone, Copy)]
pub struct AlgId<'a> {
    /// The algorithm OID's contents octets.
    pub oid: &'a [u8],
    pub params: Option<Tlv<'a>>,
}

impl<'a> View for AlgId<'a> {
    type V = SpecAlgId;

    open spec fn view(&self) -> SpecAlgId {
        SpecAlgId { oid: self.oid@, params: opt_tlv_view(self.params) }
    }
}

pub fn read_alg_id<'a>(c: &'a [u8]) -> (r: Option<AlgId<'a>>)
    ensures
        r matches Some(a) ==> parse_alg_id(c@) == Some(a@),
        r is None ==> parse_alg_id(c@) is None,
{
    let (oid, r) = match read_expect(c, 0x06) {
        Some(x) => x,
        None => return None,
    };
    if !check_oid(oid) {
        return None;
    }
    if r.len() == 0 {
        return Some(AlgId { oid, params: None });
    }
    match read_only_tlv(r) {
        Some(p) => Some(AlgId { oid, params: Some(p) }),
        None => None,
    }
}

/// Whether two AlgorithmIdentifiers are the same.
pub fn alg_id_eq(a: &AlgId, b: &AlgId) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if !bytes_eq(a.oid, b.oid) {
        return false;
    }
    match (a.params, b.params) {
        (None, None) => true,
        (Some(x), Some(y)) => {
            let r = bytes_eq(x.tag, y.tag) && bytes_eq(x.content, y.content);
            proof {
                if !r {
                    assert(opt_tlv_view(a.params) != opt_tlv_view(b.params));
                }
            }
            r
        },
        _ => false,
    }
}

/// SubjectPublicKeyInfo, borrowed.
#[derive(Clone, Copy)]
pub struct Spki<'a> {
    pub alg: AlgId<'a>,
    /// The subjectPublicKey BIT STRING's octets.
    pub key: &'a [u8],
}

impl<'a> View for Spki<'a> {
    type V = SpecSpki;

    open spec fn view(&self) -> SpecSpki {
        SpecSpki { alg: self.alg@, key: self.key@ }
    }
}

pub fn read_spki<'a>(c: &'a [u8]) -> (r: Option<Spki<'a>>)
    ensures
        r matches Some(a) ==> parse_spki(c@) == Some(a@),
        r is None ==> parse_spki(c@) is None,
{
    let (a, r) = match read_expect(c, 0x30) {
        Some(x) => x,
        None => return None,
    };
    let alg = match read_alg_id(a) {
        Some(x) => x,
        None => return None,
    };
    let k = match read_only(r, 0x03) {
        Some(x) => x,
        None => return None,
    };
    match read_octet_aligned_bits(k) {
        Some(key) => Some(Spki { alg, key }),
        None => None,
    }
}

// ---------------------------------------------------------------------------
// Name
// ---------------------------------------------------------------------------

/// Identifier plus length octets of a minimal DER TLV with `n` contents
/// octets and a one-octet tag.
#[inline(always)]
pub fn hdr_len(n: usize) -> usize {
    if n < 0x80 {
        2
    } else if n < 0x100 {
        3
    } else if n < 0x10000 {
        4
    } else if n < 0x1000000 {
        5
    } else {
        6
    }
}

/// A Name, borrowed: the contents of its SEQUENCE, proven well-formed.
#[derive(Clone, Copy)]
pub struct Name<'a> {
    pub raw: &'a [u8],
}

impl<'a> View for Name<'a> {
    type V = SpecName;

    open spec fn view(&self) -> SpecName {
        parse_rdns(self.raw@).unwrap()
    }
}

impl<'a> Name<'a> {
    pub open spec fn wf(&self) -> bool {
        parse_rdns(self.raw@) is Some
    }

    /// The contents octets of the Name's SEQUENCE.
    pub fn raw(&self) -> (r: &'a [u8])
        ensures
            r@ == self.raw@,
    {
        self.raw
    }
}

/// AttributeTypeAndValue, borrowed.
#[derive(Clone, Copy)]
pub struct Atv<'a> {
    pub oid: &'a [u8],
    pub value: Tlv<'a>,
}

impl<'a> View for Atv<'a> {
    type V = SpecAtv;

    open spec fn view(&self) -> SpecAtv {
        SpecAtv { oid: self.oid@, value: self.value@ }
    }
}

/// Receives the attributes of a Name, in order, as the verified check
/// reads them (the mbedTLS adapter takes them from here instead of walking
/// the Name again). `log` is what it has been given so far; `merged` says
/// that the next attribute is in the same RDN.
pub trait AtvSink<'a> {
    spec fn log(&self) -> Seq<(SpecAtv, bool)>;

    fn push(&mut self, a: Atv<'a>, merged: bool)
        ensures
            final(self).log() == old(self).log().push((a@, merged)),
    ;
}

/// The sink that keeps nothing.
pub struct NoAtvs {
    pub seen: Ghost<Seq<(SpecAtv, bool)>>,
}

impl<'a> AtvSink<'a> for NoAtvs {
    open spec fn log(&self) -> Seq<(SpecAtv, bool)> {
        self.seen@
    }

    #[inline(always)]
    fn push(&mut self, a: Atv<'a>, merged: bool) {
        proof {
            self.seen@ = self.seen@.push((a@, merged));
        }
    }
}

pub fn no_atvs() -> (o: NoAtvs) {
    NoAtvs { seen: Ghost(Seq::empty()) }
}

/// An RDN's attributes, each with whether another follows it in the RDN.
pub open spec fn rdn_atvs(r: SpecRdn) -> Seq<(SpecAtv, bool)> {
    Seq::new(r.len(), |i: int| (r[i], i + 1 < r.len()))
}

/// A Name's attributes in order, as `rdn_atvs` marks them.
pub open spec fn name_atvs(n: SpecName) -> Seq<(SpecAtv, bool)>
    decreases n.len(),
{
    if n.len() == 0 {
        Seq::empty()
    } else {
        name_atvs(n.drop_last()) + rdn_atvs(n.last())
    }
}

#[inline]
pub fn read_atv<'a>(c: &'a [u8]) -> (r: Option<Atv<'a>>)
    ensures
        r matches Some(a) ==> parse_atv(c@) == Some(a@),
        r is None ==> parse_atv(c@) is None,
{
    let (oid, r) = match read_expect(c, 0x06) {
        Some(x) => x,
        None => return None,
    };
    if !check_oid(oid) {
        return None;
    }
    match read_only_tlv(r) {
        Some(v) => Some(Atv { oid, value: v }),
        None => None,
    }
}

pub fn check_atvs(s: &[u8]) -> (r: bool)
    ensures
        r == parse_atvs(s@) is Some,
{
    let mut cur = s;
    while cur.len() > 0
        invariant
            (parse_atvs(s@) is Some) == (parse_atvs(cur@) is Some),
        decreases cur@.len(),
    {
        let (c, r) = match read_expect(cur, 0x30) {
            Some(x) => x,
            None => return false,
        };
        proof {
            lemma_tlv_shrinks(cur@);
        }
        if read_atv(c).is_none() {
            return false;
        }
        cur = r;
    }
    true
}

pub fn check_rdn(c: &[u8]) -> (r: bool)
    ensures
        r == parse_rdn(c@) is Some,
{
    c.len() > 0 && check_atvs(c)
}

/// One step of `check_atvs_rec`: the attribute after `acc` in `f`.
proof fn lemma_atvs_step(prev: Seq<(SpecAtv, bool)>, f: Seq<SpecAtv>, acc: Seq<SpecAtv>, a: SpecAtv, rest: Seq<SpecAtv>)
    requires
        f == acc + (seq![a] + rest),
    ensures
        f == acc.push(a) + rest,
        prev + rdn_atvs(f).take(acc.len() + 1 as int) == (prev + rdn_atvs(f).take(acc.len() as int)).push(
            (a, rest.len() > 0),
        ),
{
    assert(acc + (seq![a] + rest) =~= acc.push(a) + rest);
    let i = acc.len() as int;
    assert(f[i] == a);
    assert(rdn_atvs(f).take(i + 1) =~= rdn_atvs(f).take(i).push((a, rest.len() > 0)));
    assert(prev + rdn_atvs(f).take(i + 1) =~= (prev + rdn_atvs(f).take(i)).push((a, rest.len() > 0)));
}

/// `check_atvs`, giving each attribute to `list`.
#[verifier::spinoff_prover]
pub fn check_atvs_rec<'a, S: AtvSink<'a>>(s: &'a [u8], list: &mut S) -> (r: bool)
    ensures
        r == parse_atvs(s@) is Some,
        r ==> final(list).log() == old(list).log() + rdn_atvs(parse_atvs(s@).unwrap()),
{
    let mut cur = s;
    let ghost prev = list.log();
    let ghost f = parse_atvs(s@).unwrap();
    let ghost mut acc: Seq<SpecAtv> = Seq::empty();
    proof {
        if parse_atvs(s@) is Some {
            assert(acc + f =~= f);
        }
        assert(prev + rdn_atvs(f).take(0) =~= prev);
    }
    while cur.len() > 0
        invariant
            (parse_atvs(s@) is Some) == (parse_atvs(cur@) is Some),
            f == parse_atvs(s@).unwrap(),
            parse_atvs(s@) is Some ==> f == acc + parse_atvs(cur@).unwrap(),
            parse_atvs(s@) is Some ==> list.log() == prev + rdn_atvs(f).take(acc.len() as int),
            cur@.len() <= s@.len(),
        decreases cur@.len(),
    {
        let (c, r) = match read_expect(cur, 0x30) {
            Some(x) => x,
            None => return false,
        };
        proof {
            lemma_tlv_shrinks(cur@);
        }
        let a = match read_atv(c) {
            Some(a) => a,
            None => return false,
        };
        proof {
            if parse_atvs(s@) is Some {
                let rest = parse_atvs(r@).unwrap();
                assert(parse_atvs(cur@) == Some(seq![a@] + rest));
                if r@.len() > 0 {
                    assert(rest.len() > 0);
                }
                assert((r@.len() > 0) == (rest.len() > 0));
                lemma_atvs_step(prev, f, acc, a@, rest);
            }
        }
        list.push(a, r.len() > 0);
        proof {
            acc = acc.push(a@);
        }
        cur = r;
    }
    proof {
        if parse_atvs(s@) is Some {
            assert(acc + Seq::<SpecAtv>::empty() =~= acc);
            assert(rdn_atvs(f).take(acc.len() as int) =~= rdn_atvs(f));
        }
    }
    true
}

/// `check_rdns`, giving every attribute to `list`.
#[verifier::spinoff_prover]
pub fn check_rdns_rec<'a, S: AtvSink<'a>>(s: &'a [u8], list: &mut S) -> (r: bool)
    ensures
        r == parse_rdns(s@) is Some,
        r ==> final(list).log() == old(list).log() + name_atvs(parse_rdns(s@).unwrap()),
{
    let mut cur = s;
    let ghost prev = list.log();
    let ghost mut acc: SpecName = Seq::empty();
    proof {
        if let Some(t) = parse_rdns(s@) {
            assert(acc + t =~= t);
        }
        assert(prev + name_atvs(acc) =~= prev);
    }
    while cur.len() > 0
        invariant
            (parse_rdns(s@) is Some) == (parse_rdns(cur@) is Some),
            parse_rdns(cur@) is Some ==> parse_rdns(s@) == Some(acc + parse_rdns(cur@).unwrap()),
            list.log() == prev + name_atvs(acc),
            cur@.len() <= s@.len(),
        decreases cur@.len(),
    {
        let (c, r) = match read_expect(cur, 0x31) {
            Some(x) => x,
            None => return false,
        };
        proof {
            lemma_tlv_shrinks(cur@);
        }
        if !(c.len() > 0 && check_atvs_rec(c, list)) {
            return false;
        }
        proof {
            let rdn = parse_atvs(c@).unwrap();
            let acc2 = acc.push(rdn);
            assert(acc2.drop_last() =~= acc);
            assert(name_atvs(acc2) == name_atvs(acc) + rdn_atvs(rdn));
            assert(prev + name_atvs(acc) + rdn_atvs(rdn) =~= prev + name_atvs(acc2));
            if let Some(rest) = parse_rdns(r@) {
                assert(parse_rdns(cur@) == Some(seq![rdn] + rest));
                assert(acc + (seq![rdn] + rest) =~= acc2 + rest);
            }
            acc = acc2;
        }
        cur = r;
    }
    proof {
        assert(acc + Seq::<SpecRdn>::empty() =~= acc);
    }
    true
}

/// `read_name`, giving the Name's attributes to `list`.
pub fn read_name_rec<'a, S: AtvSink<'a>>(c: &'a [u8], list: &mut S) -> (r: Option<Name<'a>>)
    ensures
        r matches Some(n) ==> parse_rdns(c@) == Some(n@) && n.raw@ == c@,
        r matches Some(n) ==> final(list).log() == old(list).log() + name_atvs(n@),
        r is None ==> parse_rdns(c@) is None,
{
    if check_rdns_rec(c, list) {
        Some(Name { raw: c })
    } else {
        None
    }
}

pub fn check_rdns(s: &[u8]) -> (r: bool)
    ensures
        r == parse_rdns(s@) is Some,
{
    let mut cur = s;
    while cur.len() > 0
        invariant
            (parse_rdns(s@) is Some) == (parse_rdns(cur@) is Some),
        decreases cur@.len(),
    {
        let (c, r) = match read_expect(cur, 0x31) {
            Some(x) => x,
            None => return false,
        };
        proof {
            lemma_tlv_shrinks(cur@);
        }
        if !check_rdn(c) {
            return false;
        }
        cur = r;
    }
    true
}

pub fn read_name<'a>(c: &'a [u8]) -> (r: Option<Name<'a>>)
    ensures
        r matches Some(n) ==> parse_rdns(c@) == Some(n@) && n.raw@ == c@,
        r is None ==> parse_rdns(c@) is None,
{
    if check_rdns(c) {
        Some(Name { raw: c })
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// GeneralName
// ---------------------------------------------------------------------------

/// GeneralName, borrowed. Each alternative is its own variant.
#[derive(Clone, Copy)]
pub enum GeneralName<'a> {
    Other { type_id: &'a [u8], value: Tlv<'a> },
    Rfc822(&'a [u8]),
    Dns(&'a [u8]),
    X400(&'a [u8]),
    Directory(Name<'a>),
    EdiParty(&'a [u8]),
    Uri(&'a [u8]),
    Ip(&'a [u8]),
    Registered(&'a [u8]),
}

impl<'a> View for GeneralName<'a> {
    type V = SpecGeneralName;

    open spec fn view(&self) -> SpecGeneralName {
        match self {
            GeneralName::Other { type_id, value } => SpecGeneralName::Other {
                type_id: type_id@,
                value: value@,
            },
            GeneralName::Rfc822(s) => SpecGeneralName::Rfc822(s@),
            GeneralName::Dns(s) => SpecGeneralName::Dns(s@),
            GeneralName::X400(s) => SpecGeneralName::X400(s@),
            GeneralName::Directory(n) => SpecGeneralName::Directory(n@),
            GeneralName::EdiParty(s) => SpecGeneralName::EdiParty(s@),
            GeneralName::Uri(s) => SpecGeneralName::Uri(s@),
            GeneralName::Ip(s) => SpecGeneralName::Ip(s@),
            GeneralName::Registered(s) => SpecGeneralName::Registered(s@),
        }
    }
}

fn read_other_name<'a>(c: &'a [u8]) -> (r: Option<GeneralName<'a>>)
    ensures
        r matches Some(g) ==> parse_other_name(c@) == Some(g@),
        r is None ==> parse_other_name(c@) is None,
{
    let (oid, r) = match read_expect(c, 0x06) {
        Some(x) => x,
        None => return None,
    };
    if !check_oid(oid) {
        return None;
    }
    let v = match read_only(r, 0xA0) {
        Some(x) => x,
        None => return None,
    };
    match read_only_tlv(v) {
        Some(val) => Some(GeneralName::Other { type_id: oid, value: val }),
        None => None,
    }
}

/// One GeneralName; `subtree` selects the name-constraints iPAddress form.
pub fn read_general_name<'a>(x: Tlv<'a>, subtree: bool) -> (r: Option<GeneralName<'a>>)
    ensures
        r matches Some(g) ==> parse_general_name(x@, subtree) == Some(g@),
        r is None ==> parse_general_name(x@, subtree) is None,
{
    let c = x.content;
    let t = x.tag;
    if tag_is(t, 0xA0) {
        read_other_name(c)
    } else if tag_is(t, 0x81) {
        if check_ia5_name(c) {
            Some(GeneralName::Rfc822(c))
        } else {
            None
        }
    } else if tag_is(t, 0x82) {
        if check_ia5_name(c) {
            Some(GeneralName::Dns(c))
        } else {
            None
        }
    } else if tag_is(t, 0xA3) {
        Some(GeneralName::X400(c))
    } else if tag_is(t, 0xA4) {
        match read_only(c, 0x30) {
            None => None,
            Some(n) => match read_name(n) {
                None => None,
                Some(name) => Some(GeneralName::Directory(name)),
            },
        }
    } else if tag_is(t, 0xA5) {
        Some(GeneralName::EdiParty(c))
    } else if tag_is(t, 0x86) {
        if check_ia5_name(c) {
            Some(GeneralName::Uri(c))
        } else {
            None
        }
    } else if tag_is(t, 0x87) {
        let n = c.len();
        if (!subtree && (n == 4 || n == 16)) || (subtree && (n == 8 || n == 32)) {
            Some(GeneralName::Ip(c))
        } else {
            None
        }
    } else if tag_is(t, 0x88) {
        if check_oid(c) {
            Some(GeneralName::Registered(c))
        } else {
            None
        }
    } else {
        None
    }
}

pub fn check_general_names(s: &[u8]) -> (r: bool)
    ensures
        r == parse_general_names(s@) is Some,
{
    let mut cur = s;
    while cur.len() > 0
        invariant
            (parse_general_names(s@) is Some) == (parse_general_names(cur@) is Some),
        decreases cur@.len(),
    {
        let (x, r) = match read_tlv(cur) {
            Some(x) => x,
            None => return false,
        };
        proof {
            lemma_tlv_shrinks(cur@);
        }
        if read_general_name(x, false).is_none() {
            return false;
        }
        cur = r;
    }
    true
}

pub fn check_general_names_nonempty(s: &[u8]) -> (r: bool)
    ensures
        r == parse_general_names_nonempty(s@) is Some,
{
    s.len() > 0 && check_general_names(s)
}

pub fn check_subtrees(s: &[u8]) -> (r: bool)
    ensures
        r == parse_subtrees(s@) is Some,
{
    let mut cur = s;
    while cur.len() > 0
        invariant
            (parse_subtrees(s@) is Some) == (parse_subtrees(cur@) is Some),
        decreases cur@.len(),
    {
        let (c, r) = match read_expect(cur, 0x30) {
            Some(x) => x,
            None => return false,
        };
        proof {
            lemma_tlv_shrinks(cur@);
        }
        let x = match read_only_tlv(c) {
            Some(x) => x,
            None => return false,
        };
        if read_general_name(x, true).is_none() {
            return false;
        }
        cur = r;
    }
    true
}

pub fn check_subtrees_nonempty(s: &[u8]) -> (r: bool)
    ensures
        r == parse_subtrees_nonempty(s@) is Some,
{
    s.len() > 0 && check_subtrees(s)
}

pub fn check_oids(s: &[u8]) -> (r: bool)
    ensures
        r == parse_oids(s@) is Some,
{
    let mut cur = s;
    while cur.len() > 0
        invariant
            (parse_oids(s@) is Some) == (parse_oids(cur@) is Some),
        decreases cur@.len(),
    {
        let (c, r) = match read_expect(cur, 0x06) {
            Some(x) => x,
            None => return false,
        };
        proof {
            lemma_tlv_shrinks(cur@);
        }
        if !check_oid(c) {
            return false;
        }
        cur = r;
    }
    true
}

} // verus!
