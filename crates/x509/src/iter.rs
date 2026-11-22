//! Verified iterators over the lists inside a parsed certificate. Each
//! iterator holds the bytes still to read and, as ghost state, the spec
//! values they parse to; `next` is proven to return exactly the next spec
//! value. On bytes that `parse` accepted, `next` never fails.
use crate::der::*;
use crate::ext::*;
use crate::spec::*;
use crate::x509::*;
use vstd::prelude::*;

verus! {

proof fn lemma_first<T>(all: Seq<T>, x: T, tail: Seq<T>)
    requires
        all == seq![x] + tail,
    ensures
        all.len() > 0,
        all[0] == x,
        all.drop_first() == tail,
{
    assert(all[0] == x);
    assert(all.drop_first() =~= tail);
}

/// A RelativeDistinguishedName, borrowed: the contents of its SET.
#[derive(Clone, Copy)]
pub struct Rdn<'a> {
    pub raw: &'a [u8],
}

impl<'a> View for Rdn<'a> {
    type V = SpecRdn;

    open spec fn view(&self) -> SpecRdn {
        parse_rdn(self.raw@).unwrap()
    }
}

/// The RDNs of a Name, in order.
pub struct RdnIter<'a> {
    pub rest: &'a [u8],
    pub remaining: Ghost<Seq<SpecRdn>>,
}

impl<'a> RdnIter<'a> {
    pub open spec fn inv(&self) -> bool {
        parse_rdns(self.rest@) == Some(self.remaining@)
    }

    pub fn new(n: &Name<'a>) -> (r: Self)
        requires
            n.wf(),
        ensures
            r.inv(),
            r.remaining@ == n@,
    {
        RdnIter { rest: n.raw, remaining: Ghost(n@) }
    }

    pub fn next(&mut self) -> (r: Option<Rdn<'a>>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            old(self).remaining@.len() == 0 ==> r is None,
            old(self).remaining@.len() > 0 ==> (r matches Some(x) && x@ == old(
                self,
            ).remaining@[0] && parse_rdn(x.raw@) is Some && final(self).remaining@ == old(
                self,
            ).remaining@.drop_first()),
    {
        if self.rest.len() == 0 {
            return None;
        }
        let (c, r) = match read_expect(self.rest, 0x31) {
            Some(x) => x,
            None => {
                proof {
                    assert(false);
                }
                return None;
            },
        };
        proof {
            lemma_tlv_shrinks(self.rest@);
            lemma_first(self.remaining@, parse_rdn(c@).unwrap(), parse_rdns(r@).unwrap());
        }
        self.rest = r;
        self.remaining = Ghost(self.remaining@.drop_first());
        Some(Rdn { raw: c })
    }
}

/// The attributes of an RDN, in order.
pub struct AtvIter<'a> {
    pub rest: &'a [u8],
    pub remaining: Ghost<Seq<SpecAtv>>,
}

impl<'a> AtvIter<'a> {
    pub open spec fn inv(&self) -> bool {
        parse_atvs(self.rest@) == Some(self.remaining@)
    }

    pub fn new(n: &Rdn<'a>) -> (r: Self)
        requires
            parse_rdn(n.raw@) is Some,
        ensures
            r.inv(),
            r.remaining@ == n@,
    {
        AtvIter { rest: n.raw, remaining: Ghost(n@) }
    }

    pub fn next(&mut self) -> (r: Option<Atv<'a>>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            old(self).remaining@.len() == 0 ==> r is None,
            old(self).remaining@.len() > 0 ==> (r matches Some(x) && x@ == old(
                self,
            ).remaining@[0] && final(self).remaining@ == old(self).remaining@.drop_first()),
    {
        if self.rest.len() == 0 {
            return None;
        }
        let (c, r) = match read_expect(self.rest, 0x30) {
            Some(x) => x,
            None => {
                proof {
                    assert(false);
                }
                return None;
            },
        };
        let a = match read_atv(c) {
            Some(a) => a,
            None => {
                proof {
                    assert(false);
                }
                return None;
            },
        };
        proof {
            lemma_tlv_shrinks(self.rest@);
            lemma_first(self.remaining@, a@, parse_atvs(r@).unwrap());
        }
        self.rest = r;
        self.remaining = Ghost(self.remaining@.drop_first());
        Some(a)
    }
}

/// The entries of GeneralNames, in order.
pub struct GeneralNameIter<'a> {
    pub rest: &'a [u8],
    pub remaining: Ghost<Seq<SpecGeneralName>>,
}

impl<'a> GeneralNameIter<'a> {
    pub open spec fn inv(&self) -> bool {
        parse_general_names(self.rest@) == Some(self.remaining@)
    }

    /// Over the contents of a GeneralNames SEQUENCE.
    pub fn new(l: &'a [u8]) -> (r: Self)
        requires
            parse_general_names(l@) is Some,
        ensures
            r.inv(),
            r.remaining@ == parse_general_names(l@).unwrap(),
    {
        GeneralNameIter { rest: l, remaining: Ghost(parse_general_names(l@).unwrap()) }
    }

    pub fn next(&mut self) -> (r: Option<GeneralName<'a>>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            old(self).remaining@.len() == 0 ==> r is None,
            old(self).remaining@.len() > 0 ==> (r matches Some(x) && x@ == old(
                self,
            ).remaining@[0] && final(self).remaining@ == old(self).remaining@.drop_first()),
    {
        if self.rest.len() == 0 {
            return None;
        }
        let (x, r) = match read_tlv(self.rest) {
            Some(x) => x,
            None => {
                proof {
                    assert(false);
                }
                return None;
            },
        };
        let g = match read_general_name(x, false) {
            Some(g) => g,
            None => {
                proof {
                    assert(false);
                }
                return None;
            },
        };
        proof {
            lemma_tlv_shrinks(self.rest@);
            lemma_first(self.remaining@, g@, parse_general_names(r@).unwrap());
        }
        self.rest = r;
        self.remaining = Ghost(self.remaining@.drop_first());
        Some(g)
    }
}

/// The bases of GeneralSubtrees (name constraints), in order.
pub struct SubtreeIter<'a> {
    pub rest: &'a [u8],
    pub remaining: Ghost<Seq<SpecGeneralName>>,
}

impl<'a> SubtreeIter<'a> {
    pub open spec fn inv(&self) -> bool {
        parse_subtrees(self.rest@) == Some(self.remaining@)
    }

    pub fn new(l: &'a [u8]) -> (r: Self)
        requires
            parse_subtrees(l@) is Some,
        ensures
            r.inv(),
            r.remaining@ == parse_subtrees(l@).unwrap(),
    {
        SubtreeIter { rest: l, remaining: Ghost(parse_subtrees(l@).unwrap()) }
    }

    pub fn next(&mut self) -> (r: Option<GeneralName<'a>>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            old(self).remaining@.len() == 0 ==> r is None,
            old(self).remaining@.len() > 0 ==> (r matches Some(x) && x@ == old(
                self,
            ).remaining@[0] && final(self).remaining@ == old(self).remaining@.drop_first()),
    {
        if self.rest.len() == 0 {
            return None;
        }
        let (c, r) = match read_expect(self.rest, 0x30) {
            Some(x) => x,
            None => {
                proof {
                    assert(false);
                }
                return None;
            },
        };
        let x = match read_only_tlv(c) {
            Some(x) => x,
            None => {
                proof {
                    assert(false);
                }
                return None;
            },
        };
        let g = match read_general_name(x, true) {
            Some(g) => g,
            None => {
                proof {
                    assert(false);
                }
                return None;
            },
        };
        proof {
            lemma_tlv_shrinks(self.rest@);
            lemma_first(self.remaining@, g@, parse_subtrees(r@).unwrap());
        }
        self.rest = r;
        self.remaining = Ghost(self.remaining@.drop_first());
        Some(g)
    }
}

/// A list of OIDs (ExtendedKeyUsage), in order.
pub struct OidIter<'a> {
    pub rest: &'a [u8],
    pub remaining: Ghost<Seq<Seq<u8>>>,
}

impl<'a> OidIter<'a> {
    pub open spec fn inv(&self) -> bool {
        parse_oids(self.rest@) == Some(self.remaining@)
    }

    pub fn new(l: &'a [u8]) -> (r: Self)
        requires
            parse_oids(l@) is Some,
        ensures
            r.inv(),
            r.remaining@ == parse_oids(l@).unwrap(),
    {
        OidIter { rest: l, remaining: Ghost(parse_oids(l@).unwrap()) }
    }

    pub fn next(&mut self) -> (r: Option<&'a [u8]>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            old(self).remaining@.len() == 0 ==> r is None,
            old(self).remaining@.len() > 0 ==> (r matches Some(x) && x@ == old(
                self,
            ).remaining@[0] && final(self).remaining@ == old(self).remaining@.drop_first()),
    {
        if self.rest.len() == 0 {
            return None;
        }
        let (c, r) = match read_expect(self.rest, 0x06) {
            Some(x) => x,
            None => {
                proof {
                    assert(false);
                }
                return None;
            },
        };
        proof {
            lemma_tlv_shrinks(self.rest@);
            lemma_first(self.remaining@, c@, parse_oids(r@).unwrap());
        }
        self.rest = r;
        self.remaining = Ghost(self.remaining@.drop_first());
        Some(c)
    }
}

/// The extensions of a certificate, in order.
pub struct ExtensionIter<'a> {
    pub rest: &'a [u8],
    pub remaining: Ghost<Seq<SpecExtension>>,
}

impl<'a> ExtensionIter<'a> {
    pub open spec fn inv(&self) -> bool {
        parse_extensions(self.rest@) == Some(self.remaining@)
    }

    pub fn new(l: &'a [u8]) -> (r: Self)
        requires
            parse_extensions(l@) is Some,
        ensures
            r.inv(),
            r.remaining@ == parse_extensions(l@).unwrap(),
    {
        ExtensionIter { rest: l, remaining: Ghost(parse_extensions(l@).unwrap()) }
    }

    pub fn next(&mut self) -> (r: Option<Extension<'a>>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            old(self).remaining@.len() == 0 ==> r is None,
            old(self).remaining@.len() > 0 ==> (r matches Some(x) && x@ == old(
                self,
            ).remaining@[0] && final(self).remaining@ == old(self).remaining@.drop_first()),
    {
        if self.rest.len() == 0 {
            return None;
        }
        let (c, r) = match read_expect(self.rest, 0x30) {
            Some(x) => x,
            None => {
                proof {
                    assert(false);
                }
                return None;
            },
        };
        let e = match read_extension(c) {
            Some(e) => e,
            None => {
                proof {
                    lemma_ext_list_unfold(self.rest@, c@, r@);
                    assert(false);
                }
                return None;
            },
        };
        proof {
            lemma_tlv_shrinks(self.rest@);
            lemma_ext_list_unfold(self.rest@, c@, r@);
            lemma_first(self.remaining@, e@, parse_extensions(r@).unwrap());
        }
        self.rest = r;
        self.remaining = Ghost(self.remaining@.drop_first());
        Some(e)
    }
}

/// The policy OIDs of certificatePolicies, in order.
pub struct PolicyIter<'a> {
    pub rest: &'a [u8],
    pub remaining: Ghost<Seq<Seq<u8>>>,
}

impl<'a> PolicyIter<'a> {
    pub open spec fn inv(&self) -> bool {
        parse_policies(self.rest@) == Some(self.remaining@)
    }

    pub fn new(l: &'a [u8]) -> (r: Self)
        requires
            parse_policies(l@) is Some,
        ensures
            r.inv(),
            r.remaining@ == parse_policies(l@).unwrap(),
    {
        PolicyIter { rest: l, remaining: Ghost(parse_policies(l@).unwrap()) }
    }

    pub fn next(&mut self) -> (r: Option<&'a [u8]>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            old(self).remaining@.len() == 0 ==> r is None,
            old(self).remaining@.len() > 0 ==> (r matches Some(x) && x@ == old(
                self,
            ).remaining@[0] && final(self).remaining@ == old(self).remaining@.drop_first()),
    {
        if self.rest.len() == 0 {
            return None;
        }
        let (c, r) = match read_expect(self.rest, 0x30) {
            Some(x) => x,
            None => {
                proof {
                    assert(false);
                }
                return None;
            },
        };
        let o = match read_policy_info(c) {
            Some(o) => o,
            None => {
                proof {
                    assert(false);
                }
                return None;
            },
        };
        proof {
            lemma_tlv_shrinks(self.rest@);
            lemma_first(self.remaining@, o@, parse_policies(r@).unwrap());
        }
        self.rest = r;
        self.remaining = Ghost(self.remaining@.drop_first());
        Some(o)
    }
}

} // verus!
