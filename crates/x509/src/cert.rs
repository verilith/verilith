//! The verified certificate parser: `parse` computes exactly
//! `spec::parse_certificate`.
use crate::der::*;
use crate::ext::*;
use crate::iter::*;
use crate::spec::*;
use crate::time::*;
use crate::x509::*;
use vstd::prelude::*;

verus! {

pub open spec fn opt_bits_view(o: Option<BitString>) -> Option<SpecBitString> {
    match o {
        Some(b) => Some(b@),
        None => None,
    }
}

/// TBSCertificate, borrowed from the input.
#[derive(Clone, Copy)]
pub struct Tbs<'a> {
    pub version: u8,
    pub serial: &'a [u8],
    pub signature: AlgId<'a>,
    pub issuer: Name<'a>,
    pub not_before: Time,
    pub not_after: Time,
    pub subject: Name<'a>,
    /// The whole SubjectPublicKeyInfo TLV, for hashing and pinning.
    pub spki_der: &'a [u8],
    pub spki: Spki<'a>,
    pub issuer_uid: Option<BitString<'a>>,
    pub subject_uid: Option<BitString<'a>>,
    /// The contents of the extensions SEQUENCE (empty when absent).
    pub extensions: &'a [u8],
}

impl<'a> View for Tbs<'a> {
    type V = SpecTbs;

    open spec fn view(&self) -> SpecTbs {
        SpecTbs {
            version: self.version,
            serial: self.serial@,
            signature: self.signature@,
            issuer: self.issuer@,
            not_before: self.not_before@,
            not_after: self.not_after@,
            subject: self.subject@,
            spki: self.spki@,
            issuer_uid: opt_bits_view(self.issuer_uid),
            subject_uid: opt_bits_view(self.subject_uid),
            extensions: parse_extensions(self.extensions@).unwrap(),
        }
    }
}

impl<'a> Tbs<'a> {
    /// What `parse` guarantees beyond the view.
    pub open spec fn wf(&self) -> bool {
        &&& self.issuer.wf()
        &&& self.subject.wf()
        &&& parse_extensions(self.extensions@) is Some
    }
}

/// A parsed certificate, borrowed from the input.
#[derive(Clone, Copy)]
pub struct Certificate<'a> {
    /// The DER bytes of the TBSCertificate, which the signature covers.
    pub tbs_der: &'a [u8],
    pub tbs: Tbs<'a>,
    /// The signature, whole octets. Its algorithm is `tbs.signature`.
    pub signature: &'a [u8],
}

impl<'a> View for Certificate<'a> {
    type V = SpecCertificate;

    open spec fn view(&self) -> SpecCertificate {
        SpecCertificate {
            tbs_der: self.tbs_der@,
            tbs: self.tbs@,
            signature_alg: self.tbs@.signature,
            signature: self.signature@,
        }
    }
}

fn read_version<'a>(s: &'a [u8]) -> (r: Option<(u8, &'a [u8])>)
    ensures
        r matches Some((v, rest)) ==> parse_version(s@) == Some((v, rest@)) && rest@.len() <= s@.len(),
        r is None ==> parse_version(s@) is None,
{
    match read_expect(s, 0xA0) {
        Some((c, r)) => match read_only(c, 0x02) {
            Some(v) => if tag_is(v, 1) {
                Some((1u8, r))
            } else if tag_is(v, 2) {
                Some((2u8, r))
            } else {
                None
            },
            None => None,
        },
        None => Some((0u8, s)),
    }
}

fn read_validity(c: &[u8]) -> (r: Option<(Time, Time)>)
    ensures
        r matches Some((a, b)) ==> parse_validity(c@) == Some((a@, b@)),
        r is None ==> parse_validity(c@) is None,
{
    let (a, r) = match read_tlv(c) {
        Some(x) => x,
        None => return None,
    };
    let nb = match read_time(a) {
        Some(t) => t,
        None => return None,
    };
    let b = match read_only_tlv(r) {
        Some(x) => x,
        None => return None,
    };
    match read_time(b) {
        Some(na) => Some((nb, na)),
        None => None,
    }
}

fn read_uid<'a>(s: &'a [u8], t: u8, version: u8) -> (r: Option<(Option<BitString<'a>>, &'a [u8])>)
    requires
        t == 0x81 || t == 0x82,
    ensures
        r matches Some((u, rest)) ==> parse_uid(s@, t, version) == Some((opt_bits_view(u), rest@)) && rest@.len() <= s@.len(),
        r is None ==> parse_uid(s@, t, version) is None,
{
    match read_expect(s, t) {
        Some((c, r)) => {
            if version == 0 {
                return None;
            }
            match read_bit_string(c) {
                Some(b) => Some((Some(b), r)),
                None => None,
            }
        },
        None => Some((None, s)),
    }
}

/// Steps `parse_metered` may take for an `n`-octet certificate.
pub open spec fn parse_cost(n: nat) -> nat {
    EXT_STEPS * n + dup_cost(n)
}

fn read_tbs_extensions<'a, E: ExtSink<'a>>(s: &'a [u8], version: u8, ext_l: &mut E) -> (r: (Option<&'a [u8]>, Ghost<nat>))
    ensures
        r.0 matches Some(l) ==> parse_extensions(l@) is Some && parse_tbs_extensions(s@, version)
            == Some(parse_extensions(l@).unwrap()),
        r.0 is None ==> parse_tbs_extensions(s@, version) is None,
        r.0 matches Some(l) ==> (l.len() > 0 ==> ext_log_ok(old(ext_l).log(), final(ext_l).log(), parse_extensions(l@).unwrap())),
        r.1@ <= parse_cost(s@.len() as nat),
{
    if s.len() == 0 {
        return (Some(s), Ghost(0));
    }
    if version != 2 {
        return (None, Ghost(0));
    }
    let c = match read_only(s, 0xA3) {
        Some(c) => c,
        None => return (None, Ghost(0)),
    };
    let l = match read_only(c, 0x30) {
        Some(l) => l,
        None => return (None, Ghost(0)),
    };
    let (ok, st) = check_extensions_rec(l, ext_l);
    proof {
        lemma_dup_cost_mono(l@.len() as nat, s@.len() as nat);
    }
    if ok {
        (Some(l), st)
    } else {
        (None, st)
    }
}

fn read_tbs_tail<'a, E: ExtSink<'a>>(
    version: u8,
    serial: &'a [u8],
    signature: AlgId<'a>,
    issuer: Name<'a>,
    nb: Time,
    na: Time,
    subject: Name<'a>,
    spki_der: &'a [u8],
    spki: Spki<'a>,
    s6: &'a [u8],
    ext_l: &mut E,
) -> (r: (Option<Tbs<'a>>, Ghost<nat>))
    requires
        issuer.wf(),
        subject.wf(),
    ensures
        r.1@ <= parse_cost(s6@.len() as nat),
        r.0 matches Some(t) ==> t.wf() && parse_tbs_tail(
            version,
            serial@,
            signature@,
            issuer@,
            nb@,
            na@,
            subject@,
            spki@,
            s6@,
        ) == Some(t@) && t.spki_der == spki_der,
        r.0 is None ==> parse_tbs_tail(
            version,
            serial@,
            signature@,
            issuer@,
            nb@,
            na@,
            subject@,
            spki@,
            s6@,
        ) is None,
        r.0 matches Some(t) ==> (t.extensions.len() > 0 ==> ext_log_ok(old(ext_l).log(), final(ext_l).log(), parse_extensions(t.extensions@).unwrap())),
        r.0 matches Some(t) ==> t.issuer@ == issuer@ && t.subject@ == subject@,
{
    let (iu, s7) = match read_uid(s6, 0x81, version) {
        Some(x) => x,
        None => return (None, Ghost(0)),
    };
    let (su, s8) = match read_uid(s7, 0x82, version) {
        Some(x) => x,
        None => return (None, Ghost(0)),
    };
    let (extensions, st) = read_tbs_extensions(s8, version, ext_l);
    proof {
        lemma_dup_cost_mono(s8@.len() as nat, s6@.len() as nat);
    }
    let extensions = match extensions {
        Some(l) => l,
        None => return (None, st),
    };
    (Some(
        Tbs {
            version,
            serial,
            signature,
            issuer,
            not_before: nb,
            not_after: na,
            subject,
            spki_der,
            spki,
            issuer_uid: iu,
            subject_uid: su,
            extensions,
        },
    ), st)
}

#[verifier::spinoff_prover]
fn read_tbs_body<'a, A: AtvSink<'a>, B: AtvSink<'a>, E: ExtSink<'a>>(version: u8, s: &'a [u8], iss_l: &mut A, sub_l: &mut B, ext_l: &mut E) -> (r: (Option<Tbs<'a>>, Ghost<nat>))
    ensures
        r.0 matches Some(t) ==> t.wf() && parse_tbs_body(version, s@) == Some(t@),
        r.0 is None ==> parse_tbs_body(version, s@) is None,
        r.0 matches Some(t) ==> (t.extensions.len() > 0 ==> ext_log_ok(old(ext_l).log(), final(ext_l).log(), parse_extensions(t.extensions@).unwrap())),
        r.0 matches Some(t) ==> final(iss_l).log() == old(iss_l).log() + name_atvs(t.issuer@) && final(sub_l).log() == old(sub_l).log() + name_atvs(t.subject@),
        r.1@ <= parse_cost(s@.len() as nat),
{
    let ghost n = s@.len() as nat;
    proof {
        lemma_dup_cost_nonneg(n);
    }
    let (serial, s1) = match read_expect(s, 0x02) {
        Some(x) => x,
        None => return (None, Ghost(0)),
    };
    if !check_integer(serial) {
        return (None, Ghost(0));
    }
    let (sa, s2) = match read_expect(s1, 0x30) {
        Some(x) => x,
        None => return (None, Ghost(0)),
    };
    let (signature, c1) = read_alg_id_m(sa);
    let signature = match signature {
        Some(x) => x,
        None => return (None, c1),
    };
    let (iss, s3) = match read_expect(s2, 0x30) {
        Some(x) => x,
        None => return (None, c1),
    };
    let (issuer, c2) = read_name_rec(iss, iss_l);
    let issuer = match issuer {
        Some(x) => x,
        None => return (None, Ghost(c1@ + c2@)),
    };
    let (val, s4) = match read_expect(s3, 0x30) {
        Some(x) => x,
        None => return (None, Ghost(c1@ + c2@)),
    };
    let (nb, na) = match read_validity(val) {
        Some(x) => x,
        None => return (None, Ghost(c1@ + c2@)),
    };
    let (sub, s5) = match read_expect(s4, 0x30) {
        Some(x) => x,
        None => return (None, Ghost(c1@ + c2@)),
    };
    let (subject, c3) = read_name_rec(sub, sub_l);
    let subject = match subject {
        Some(x) => x,
        None => return (None, Ghost(c1@ + c2@ + c3@)),
    };
    let (pk, s6) = match read_expect(s5, 0x30) {
        Some(x) => x,
        None => return (None, Ghost(c1@ + c2@ + c3@)),
    };
    proof {
        lemma_tlv_shrinks(s5@);
    }
    let spki_der = subslice(s5, 0, s5.len() - s6.len());
    let (spki, c4) = read_spki_m(pk);
    let spki = match spki {
        Some(x) => x,
        None => return (None, Ghost(c1@ + c2@ + c3@ + c4@)),
    };
    let (t, c5) = read_tbs_tail(version, serial, signature, issuer, nb, na, subject, spki_der, spki, s6, ext_l);
    proof {
        lemma_dup_cost_mono(s6@.len() as nat, n);
    }
    (t, Ghost(c1@ + c2@ + c3@ + c4@ + c5@))
}

fn read_tbs<'a, A: AtvSink<'a>, B: AtvSink<'a>, E: ExtSink<'a>>(c: &'a [u8], iss_l: &mut A, sub_l: &mut B, ext_l: &mut E) -> (r: (Option<Tbs<'a>>, Ghost<nat>))
    ensures
        r.0 matches Some(t) ==> t.wf() && parse_tbs(c@) == Some(t@),
        r.0 is None ==> parse_tbs(c@) is None,
        r.0 matches Some(t) ==> (t.extensions.len() > 0 ==> ext_log_ok(old(ext_l).log(), final(ext_l).log(), parse_extensions(t.extensions@).unwrap())),
        r.0 matches Some(t) ==> final(iss_l).log() == old(iss_l).log() + name_atvs(t.issuer@) && final(sub_l).log() == old(sub_l).log() + name_atvs(t.subject@),
        r.1@ <= parse_cost(c@.len() as nat),
{
    match read_version(c) {
        None => (None, Ghost(0)),
        Some((v, r)) => {
            let (t, st) = read_tbs_body(v, r, iss_l, sub_l, ext_l);
            proof {
                lemma_dup_cost_mono(r@.len() as nat, c@.len() as nat);
            }
            (t, st)
        },
    }
}

/// Parses one DER certificate; `b` must hold exactly the certificate.
///
/// Returns `Some` exactly when `spec::parse_certificate` does, with the same
/// certificate.
pub fn parse<'a>(b: &'a [u8]) -> (r: Option<Certificate<'a>>)
    ensures
        r matches Some(c) ==> c.tbs.wf() && parse_certificate(b@) == Some(c@),
        r is None ==> parse_certificate(b@) is None,
{
    let mut i = no_atvs();
    let mut s = no_atvs();
    let mut e = no_exts();
    parse_rec(b, &mut i, &mut s, &mut e)
}

/// `parse`, with the number of steps it took: at most `parse_cost(n)` for
/// an `n`-octet input, whatever the outcome (see the README for what a step
/// is).
pub fn parse_metered<'a>(b: &'a [u8]) -> (r: (Option<Certificate<'a>>, Ghost<nat>))
    ensures
        r.0 matches Some(c) ==> c.tbs.wf() && parse_certificate(b@) == Some(c@),
        r.0 is None ==> parse_certificate(b@) is None,
        r.1@ <= parse_cost(b@.len() as nat),
{
    let mut i = no_atvs();
    let mut s = no_atvs();
    let mut e = no_exts();
    parse_rec_m(b, &mut i, &mut s, &mut e)
}

/// `parse`, giving the issuer's and subject's attributes to `iss_l` and
/// `sub_l` (see `AtvSink`) and the extensions to `ext_l` (see `ExtSink`),
/// in order, as it checks them.
pub fn parse_rec<'a, A: AtvSink<'a>, B: AtvSink<'a>, E: ExtSink<'a>>(b: &'a [u8], iss_l: &mut A, sub_l: &mut B, ext_l: &mut E) -> (r: Option<Certificate<'a>>)
    ensures
        r matches Some(c) ==> c.tbs.wf() && parse_certificate(b@) == Some(c@),
        r is None ==> parse_certificate(b@) is None,
        r matches Some(c) ==> (c.tbs.extensions.len() > 0 ==> ext_log_ok(old(ext_l).log(), final(ext_l).log(), parse_extensions(c.tbs.extensions@).unwrap())),
        r matches Some(c) ==> final(iss_l).log() == old(iss_l).log() + name_atvs(c.tbs.issuer@) && final(sub_l).log() == old(sub_l).log() + name_atvs(c.tbs.subject@),
{
    parse_rec_m(b, iss_l, sub_l, ext_l).0
}

/// `parse_rec`, with its steps.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub fn parse_rec_m<'a, A: AtvSink<'a>, B: AtvSink<'a>, E: ExtSink<'a>>(b: &'a [u8], iss_l: &mut A, sub_l: &mut B, ext_l: &mut E) -> (r: (Option<Certificate<'a>>, Ghost<nat>))
    ensures
        r.0 matches Some(c) ==> c.tbs.wf() && parse_certificate(b@) == Some(c@),
        r.0 is None ==> parse_certificate(b@) is None,
        r.0 matches Some(c) ==> (c.tbs.extensions.len() > 0 ==> ext_log_ok(old(ext_l).log(), final(ext_l).log(), parse_extensions(c.tbs.extensions@).unwrap())),
        r.0 matches Some(c) ==> final(iss_l).log() == old(iss_l).log() + name_atvs(c.tbs.issuer@) && final(sub_l).log() == old(sub_l).log() + name_atvs(c.tbs.subject@),
        r.1@ <= parse_cost(b@.len() as nat),
{
    let ghost n = b@.len() as nat;
    proof {
        lemma_dup_cost_nonneg(n);
    }
    let c = match read_only(b, 0x30) {
        Some(c) => c,
        None => return (None, Ghost(0)),
    };
    let (t, r1) = match read_expect(c, 0x30) {
        Some(x) => x,
        None => return (None, Ghost(0)),
    };
    proof {
        lemma_tlv_shrinks(c@);
    }
    let (tbs, c1) = read_tbs(t, iss_l, sub_l, ext_l);
    proof {
        lemma_dup_cost_mono(t@.len() as nat, n);
    }
    let tbs = match tbs {
        Some(x) => x,
        None => return (None, c1),
    };
    let (a, r2) = match read_expect(r1, 0x30) {
        Some(x) => x,
        None => return (None, c1),
    };
    let (alg, c2) = read_alg_id_m(a);
    let alg = match alg {
        Some(x) => x,
        None => return (None, Ghost(c1@ + c2@)),
    };
    let (eq, c3) = alg_id_eq_m(&alg, &tbs.signature);
    if !eq {
        return (None, Ghost(c1@ + c2@ + c3@));
    }
    let sig = match read_only(r2, 0x03) {
        Some(x) => x,
        None => return (None, Ghost(c1@ + c2@ + c3@)),
    };
    let signature = match read_octet_aligned_bits(sig) {
        Some(x) => x,
        None => return (None, Ghost(c1@ + c2@ + c3@)),
    };
    let tbs_der = subslice(c, 0, c.len() - r1.len());
    (Some(Certificate { tbs_der, tbs, signature }), Ghost(c1@ + c2@ + c3@))
}

/// The decoded contents of the extension with id-ce arc `x`, if present.
pub open spec fn ext_value(c: SpecCertificate, x: u8) -> Option<Seq<u8>> {
    match find_extension(c.tbs.extensions, oid_ce(x)) {
        Some(e) => Some(e.value),
        None => None,
    }
}

pub open spec fn spec_basic_constraints(c: SpecCertificate) -> Option<SpecBasicConstraints> {
    match ext_value(c, CE_BASIC_CONSTRAINTS) {
        Some(v) => parse_basic_constraints(v),
        None => None,
    }
}

pub open spec fn spec_key_usage(c: SpecCertificate) -> Option<u16> {
    match ext_value(c, CE_KEY_USAGE) {
        Some(v) => parse_key_usage(v),
        None => None,
    }
}

pub open spec fn spec_ext_key_usage(c: SpecCertificate) -> Option<Seq<Seq<u8>>> {
    match ext_value(c, CE_EXT_KEY_USAGE) {
        Some(v) => parse_ext_key_usage(v),
        None => None,
    }
}

pub open spec fn spec_certificate_policies(c: SpecCertificate) -> Option<Seq<Seq<u8>>> {
    match ext_value(c, CE_CERTIFICATE_POLICIES) {
        Some(v) => parse_certificate_policies(v),
        None => None,
    }
}

pub open spec fn spec_alt_names(c: SpecCertificate, x: u8) -> Option<Seq<SpecGeneralName>> {
    match ext_value(c, x) {
        Some(v) => parse_alt_name(v),
        None => None,
    }
}

pub open spec fn spec_subject_key_id(c: SpecCertificate) -> Option<Seq<u8>> {
    match ext_value(c, CE_SUBJECT_KEY_ID) {
        Some(v) => parse_subject_key_id(v),
        None => None,
    }
}

pub open spec fn spec_authority_key_id(c: SpecCertificate) -> Option<SpecAuthorityKeyId> {
    match ext_value(c, CE_AUTHORITY_KEY_ID) {
        Some(v) => parse_authority_key_id(v),
        None => None,
    }
}

pub open spec fn spec_name_constraints(c: SpecCertificate) -> Option<SpecNameConstraints> {
    match ext_value(c, CE_NAME_CONSTRAINTS) {
        Some(v) => parse_name_constraints(v),
        None => None,
    }
}

impl<'a> Certificate<'a> {
    /// The extension with this OID (contents octets), if present.
    pub fn extension(&self, oid: &[u8]) -> (r: Option<Extension<'a>>)
        requires
            self.tbs.wf(),
        ensures
            r matches Some(e) ==> find_extension(self@.tbs.extensions, oid@) == Some(e@),
            r is None ==> find_extension(self@.tbs.extensions, oid@) is None,
    {
        find_extension_in(self.tbs.extensions, oid)
    }

    fn ce(&self, x: u8) -> (r: Option<&'a [u8]>)
        requires
            self.tbs.wf(),
        ensures
            r matches Some(v) ==> ext_value(self@, x) == Some(v@),
            r is None ==> ext_value(self@, x) is None,
    {
        let oid: [u8; 3] = [0x55, 0x1D, x];
        proof {
            assert(oid@ =~= oid_ce(x));
        }
        match find_extension_in(self.tbs.extensions, oid.as_slice()) {
            Some(e) => Some(e.value),
            None => None,
        }
    }

    pub fn extensions(&self) -> (r: ExtensionIter<'a>)
        requires
            self.tbs.wf(),
        ensures
            r.inv(),
            r.remaining@ == self@.tbs.extensions,
    {
        ExtensionIter::new(self.tbs.extensions)
    }

    pub fn issuer_rdns(&self) -> (r: RdnIter<'a>)
        requires
            self.tbs.wf(),
        ensures
            r.inv(),
            r.remaining@ == self@.tbs.issuer,
    {
        RdnIter::new(&self.tbs.issuer)
    }

    pub fn subject_rdns(&self) -> (r: RdnIter<'a>)
        requires
            self.tbs.wf(),
        ensures
            r.inv(),
            r.remaining@ == self@.tbs.subject,
    {
        RdnIter::new(&self.tbs.subject)
    }

    pub fn basic_constraints(&self) -> (r: Option<BasicConstraints>)
        requires
            self.tbs.wf(),
        ensures
            r matches Some(b) ==> spec_basic_constraints(self@) == Some(b@),
            r is None ==> spec_basic_constraints(self@) is None,
    {
        match self.ce(19) {
            Some(v) => read_basic_constraints(v),
            None => None,
        }
    }

    /// KeyUsage as a mask: bit 0 is digitalSignature, bit 8 decipherOnly.
    pub fn key_usage(&self) -> (r: Option<u16>)
        requires
            self.tbs.wf(),
        ensures
            r == spec_key_usage(self@),
    {
        match self.ce(15) {
            Some(v) => read_key_usage(v),
            None => None,
        }
    }

    pub fn ext_key_usage(&self) -> (r: Option<OidIter<'a>>)
        requires
            self.tbs.wf(),
        ensures
            r matches Some(i) ==> i.inv() && spec_ext_key_usage(self@) == Some(i.remaining@),
            r is None ==> spec_ext_key_usage(self@) is None,
    {
        match self.ce(37) {
            Some(v) => match read_ext_key_usage(v) {
                Some(l) => Some(OidIter::new(l)),
                None => None,
            },
            None => None,
        }
    }

    /// The policy identifiers of certificatePolicies, in order.
    pub fn certificate_policies(&self) -> (r: Option<PolicyIter<'a>>)
        requires
            self.tbs.wf(),
        ensures
            r matches Some(i) ==> i.inv() && spec_certificate_policies(self@) == Some(i.remaining@),
            r is None ==> spec_certificate_policies(self@) is None,
    {
        match self.ce(32) {
            Some(v) => match read_certificate_policies(v) {
                Some(l) => Some(PolicyIter::new(l)),
                None => None,
            },
            None => None,
        }
    }

    fn alt_names(&self, x: u8) -> (r: Option<GeneralNameIter<'a>>)
        requires
            self.tbs.wf(),
        ensures
            r matches Some(i) ==> i.inv() && spec_alt_names(self@, x) == Some(i.remaining@),
            r is None ==> spec_alt_names(self@, x) is None,
    {
        match self.ce(x) {
            Some(v) => match read_alt_name(v) {
                Some(l) => Some(GeneralNameIter::new(l)),
                None => None,
            },
            None => None,
        }
    }

    pub fn subject_alt_names(&self) -> (r: Option<GeneralNameIter<'a>>)
        requires
            self.tbs.wf(),
        ensures
            r matches Some(i) ==> i.inv() && spec_alt_names(self@, CE_SUBJECT_ALT_NAME) == Some(
                i.remaining@,
            ),
            r is None ==> spec_alt_names(self@, CE_SUBJECT_ALT_NAME) is None,
    {
        self.alt_names(17)
    }

    pub fn issuer_alt_names(&self) -> (r: Option<GeneralNameIter<'a>>)
        requires
            self.tbs.wf(),
        ensures
            r matches Some(i) ==> i.inv() && spec_alt_names(self@, CE_ISSUER_ALT_NAME) == Some(
                i.remaining@,
            ),
            r is None ==> spec_alt_names(self@, CE_ISSUER_ALT_NAME) is None,
    {
        self.alt_names(18)
    }

    pub fn subject_key_id(&self) -> (r: Option<&'a [u8]>)
        requires
            self.tbs.wf(),
        ensures
            r matches Some(k) ==> spec_subject_key_id(self@) == Some(k@),
            r is None ==> spec_subject_key_id(self@) is None,
    {
        match self.ce(14) {
            Some(v) => read_only(v, 0x04),
            None => None,
        }
    }

    pub fn authority_key_id(&self) -> (r: Option<AuthorityKeyId<'a>>)
        requires
            self.tbs.wf(),
        ensures
            r matches Some(a) ==> spec_authority_key_id(self@) == Some(a@) && (a.issuer matches Some(
                l,
            ) ==> parse_general_names(l@) is Some),
            r is None ==> spec_authority_key_id(self@) is None,
    {
        match self.ce(35) {
            Some(v) => read_authority_key_id(v),
            None => None,
        }
    }

    pub fn name_constraints(&self) -> (r: Option<NameConstraints<'a>>)
        requires
            self.tbs.wf(),
        ensures
            r matches Some(n) ==> spec_name_constraints(self@) == Some(n@) && nc_lists_wf(n),
            r is None ==> spec_name_constraints(self@) is None,
    {
        match self.ce(30) {
            Some(v) => read_name_constraints(v),
            None => None,
        }
    }
}

} // verus!
