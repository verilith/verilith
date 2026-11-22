//! An index of the general entities by name, so that a reference finds
//! its entity in time independent of how many there are (`find_ent`
//! by a linear search would make a document with many entities and many
//! references quadratic). It is a table of chains, seeded at random like
//! `uniq.rs`'s, that holds only the first entity of each name: the one
//! that is binding (§4.2), which is what `find_ent` returns.
#[cfg(verus_keep_ghost)]
use crate::lex::{ent_view, ents_view};
use crate::lex::{ex_bytes_eq, XEnt};
use crate::spec::*;
use crate::uniq::*;
use vstd::prelude::*;

verus! {

/// The entity names, as spans into the document.
pub open spec fn spans(es: Seq<XEnt>) -> Seq<(usize, usize)> {
    es.map_values(|e: XEnt| (e.a, e.b))
}

/// No earlier name is the same.
pub open spec fn first_occ(s: Seq<u8>, ns: Seq<(usize, usize)>, j: int) -> bool {
    forall|k: int| 0 <= k < j ==> nm(s, #[trigger] ns[k]) != nm(s, ns[j])
}

/// The chains hold exactly the first occurrences among the first `k`
/// names, each in its bucket's.
#[verifier::opaque]
pub open spec fn index_ok(
    s: Seq<u8>,
    ns: Seq<(usize, usize)>,
    sd: u64,
    mul: u64,
    m: int,
    k: int,
    chains: Seq<Seq<int>>,
    head: Seq<usize>,
    next: Seq<usize>,
) -> bool {
    &&& m > 0 && chains.len() == m && head.len() == m && next.len() == ns.len() && 0 <= k <= ns.len()
    &&& forall|b: int| 0 <= b < m ==> chain_links(k, #[trigger] chains[b], head[b], next)
    &&& forall|b: int, p: int|
        0 <= b < m && 0 <= p < chains[b].len() ==> bkt(sd, mul, m, nm(s, ns[#[trigger] chains[b][p]])) == b
            && first_occ(s, ns, chains[b][p])
    &&& forall|j: int|
        0 <= j < k && first_occ(s, ns, j) ==> #[trigger] chains[bkt(sd, mul, m, nm(s, ns[j]))].contains(j)
}

/// The index of the entities of a document.
pub struct NameIndex {
    pub head: Vec<usize>,
    pub next: Vec<usize>,
    pub sd: u64,
    pub mul: u64,
    pub chains: Ghost<Seq<Seq<int>>>,
}

/// The index is the index of the names of `es` in `s`.
pub open spec fn indexes(x: &NameIndex, s: Seq<u8>, es: Seq<XEnt>) -> bool {
    index_ok(s, spans(es), x.sd, x.mul, x.head@.len() as int, es.len() as int, x.chains@, x.head@, x.next@)
        && es.len() <= isize::MAX
}

/// `find_ent` is the first entity of the name.
pub proof fn lemma_find_first(ents: Seq<Ent>, name: Seq<u8>)
    ensures
        match find_ent(ents, name) {
            Some(j) => 0 <= j < ents.len() && ents[j].name == name && forall|k: int| 0 <= k < j ==> #[trigger] ents[k].name
                != name,
            None => forall|k: int| 0 <= k < ents.len() ==> #[trigger] ents[k].name != name,
        },
    decreases ents.len(),
{
    if ents.len() > 0 {
        let d = ents.drop_last();
        lemma_find_first(d, name);
        match find_ent(d, name) {
            Some(j) => {
                assert forall|k: int| 0 <= k < j implies #[trigger] ents[k].name != name by {
                    assert(ents[k] == d[k]);
                }
                assert(ents[j] == d[j]);
            },
            None => {
                assert forall|k: int| 0 <= k < ents.len() - 1 implies #[trigger] ents[k].name != name by {
                    assert(ents[k] == d[k]);
                }
            },
        }
    }
}

proof fn lemma_names(s: Seq<u8>, es: Seq<XEnt>, j: int)
    requires
        0 <= j < es.len(),
    ensures
        ents_view(s, es)[j].name == nm(s, spans(es)[j]),
{
    assert(ents_view(s, es)[j] == ent_view(s, es[j]));
    assert(spans(es)[j] == (es[j].a, es[j].b));
}

/// A name equal to one in the table, which holds only first occurrences,
/// is that one's first occurrence.
proof fn lemma_found(s: Seq<u8>, es: Seq<XEnt>, j: int, q: Seq<u8>, lim: int)
    requires
        0 <= j < es.len(),
        0 <= lim <= es.len(),
        first_occ(s, spans(es), j),
        nm(s, spans(es)[j]) == q,
    ensures
        find_ent(ents_view(s, es).subrange(0, lim), q) == if j < lim {
            Some(j)
        } else {
            None::<int>
        },
{
    let ev = ents_view(s, es).subrange(0, lim);
    lemma_find_first(ev, q);
    lemma_names(s, es, j);
    assert forall|k: int| 0 <= k < j && k < lim implies #[trigger] ev[k].name != q by {
        lemma_names(s, es, k);
        assert(nm(s, spans(es)[k]) != nm(s, spans(es)[j]));
    }
    if j < lim {
        assert(ev[j].name == q);
    } else {
        match find_ent(ev, q) {
            Some(i) => {
                lemma_names(s, es, i);
                assert(nm(s, spans(es)[i]) != nm(s, spans(es)[j]));
            },
            None => {},
        }
    }
}

/// No entity has the name `q` if its first occurrence is not where the
/// table says it would be.
proof fn lemma_absent(
    s: Seq<u8>,
    es: Seq<XEnt>,
    sd: u64,
    mul: u64,
    m: int,
    chains: Seq<Seq<int>>,
    head: Seq<usize>,
    next: Seq<usize>,
    q: Seq<u8>,
    lim: int,
)
    requires
        index_ok(s, spans(es), sd, mul, m, es.len() as int, chains, head, next),
        0 <= lim <= es.len(),
        forall|p: int|
            0 <= p < chains[bkt(sd, mul, m, q)].len() ==> nm(s, spans(es)[#[trigger] chains[bkt(sd, mul, m, q)][p]]) != q,
    ensures
        find_ent(ents_view(s, es).subrange(0, lim), q) is None,
{
    reveal(index_ok);
    let ns = spans(es);
    let ev = ents_view(s, es).subrange(0, lim);
    lemma_find_first(ev, q);
    match find_ent(ev, q) {
        Some(i) => {
            lemma_names(s, es, i);
            // The first entity named q is in the table, in q's chain.
            lemma_first_exists(s, ns, i);
            let f = choose|f: int| 0 <= f <= i && nm(s, ns[f]) == nm(s, ns[i]) && first_occ(s, ns, f);
            let b = bkt(sd, mul, m, q);
            assert(chains[b].contains(f));
            let p = choose|p: int| 0 <= p < chains[b].len() && chains[b][p] == f;
            assert(nm(s, ns[chains[b][p]]) != q);
        },
        None => {},
    }
}

/// Every name has a first occurrence at or before it.
proof fn lemma_first_exists(s: Seq<u8>, ns: Seq<(usize, usize)>, i: int)
    requires
        0 <= i < ns.len(),
    ensures
        exists|f: int| 0 <= f <= i && nm(s, ns[f]) == nm(s, ns[i]) && first_occ(s, ns, f),
    decreases i,
{
    if !first_occ(s, ns, i) {
        let k = choose|k: int| 0 <= k < i && nm(s, #[trigger] ns[k]) == nm(s, ns[i]);
        lemma_first_exists(s, ns, k);
    }
}

/// The chain `ch` from `h` holds a name like `q[a..b]`: where.
fn ex_chain_find(
    s: &[u8],
    ns: &[XEnt],
    q: &[u8],
    a: usize,
    b: usize,
    h: usize,
    next: &Vec<usize>,
    Ghost(k): Ghost<int>,
    Ghost(ch): Ghost<Seq<int>>,
) -> (r: Option<usize>)
    requires
        a <= b <= q@.len(),
        next@.len() == ns@.len(),
        0 <= k <= ns@.len(),
        forall|p: int| 0 <= p < ns@.len() ==> (#[trigger] ns@[p]).a <= ns@[p].b <= s@.len(),
        chain_links(k, ch, h, next@),
    ensures
        match r {
            Some(j) => j < k && nm(s@, spans(ns@)[j as int]) == q@.subrange(a as int, b as int) && ch.contains(
                j as int,
            ),
            None => forall|p: int| 0 <= p < ch.len() ==> nm(s@, spans(ns@)[#[trigger] ch[p]]) != q@.subrange(a as int, b as int),
        },
{
    let mut cur = h;
    let ghost mut p: int = 0;
    while cur != 0
        invariant
            0 <= p <= ch.len(),
            a <= b <= q@.len(),
            next@.len() == ns@.len(),
            0 <= k <= ns@.len(),
            forall|p2: int| 0 <= p2 < ns@.len() ==> (#[trigger] ns@[p2]).a <= ns@[p2].b <= s@.len(),
            chain_links(k, ch, h, next@),
            cur as int == if p < ch.len() {
                ch[p] + 1
            } else {
                0
            },
            forall|p2: int| 0 <= p2 < p ==> nm(s@, spans(ns@)[#[trigger] ch[p2]]) != q@.subrange(a as int, b as int),
        decreases ch.len() - p,
    {
        let j = (cur - 1) as usize;
        proof {
            assert(p < ch.len());
            assert(j == ch[p]);
            assert(0 <= ch[p] < k);
        }
        let e = ns[j];
        proof {
            assert(ns@[j as int] == e);
            assert(spans(ns@)[j as int] == (e.a, e.b));
        }
        if ex_bytes_eq(s, e.a as usize, e.b as usize, q, a, b) {
            proof {
                assert(ch[p] == j);
            }
            return Some(j);
        }
        let nx = next[j];
        proof {
            assert(next@[ch[p]] as int == if p + 1 < ch.len() {
                ch[p + 1] + 1
            } else {
                0
            });
            p = p + 1;
        }
        cur = nx;
    }
    None
}

impl NameIndex {
    /// The index of the names of `ns`.
    pub fn build(s: &[u8], ns: &[XEnt]) -> (r: NameIndex)
        requires
            ns@.len() <= isize::MAX,
            forall|p: int| 0 <= p < ns@.len() ==> (#[trigger] ns@[p]).a <= ns@[p].b <= s@.len(),
        ensures
            indexes(&r, s@, ns@),
    {
        let n = ns.len();
        let m: usize = n + 1;
        let (sd, mul) = seed();
        let mut head: Vec<usize> = Vec::new();
        while head.len() < m
            invariant
                head@.len() <= m,
                forall|b: int| 0 <= b < head@.len() ==> head@[b] == 0,
            decreases m - head@.len(),
        {
            head.push(0);
        }
        let mut next: Vec<usize> = Vec::new();
        while next.len() < n
            invariant
                next@.len() <= n,
            decreases n - next@.len(),
        {
            next.push(0);
        }
        let ghost sp = spans(ns@);
        let ghost mut chains: Seq<Seq<int>> = Seq::new(m as nat, |b: int| Seq::<int>::empty());
        proof {
            reveal(index_ok);
        }
        let mut k: usize = 0;
        while k < n
            invariant
                k <= n,
                n == ns@.len() <= isize::MAX,
                m == n + 1,
                sp == spans(ns@),
                head@.len() == m,
                next@.len() == n,
                forall|p: int| 0 <= p < ns@.len() ==> (#[trigger] ns@[p]).a <= ns@[p].b <= s@.len(),
                index_ok(s@, sp, sd, mul, m as int, k as int, chains, head@, next@),
            decreases n - k,
        {
            let e = ns[k];
            proof {
                assert(ns@[k as int] == e);
                assert(sp[k as int] == (e.a, e.b));
            }
            let h = ex_hash(s, e.a as usize, e.b as usize, sd, mul);
            let b = ((h >> 32u64) % (m as u64)) as usize;
            proof {
                assert(nm(s@, sp[k as int]) == s@.subrange(e.a as int, e.b as int));
                assert(bkt(sd, mul, m as int, nm(s@, sp[k as int])) == b);
                reveal(index_ok);
            }
            let found = ex_chain_find(s, ns, s, e.a as usize, e.b as usize, head[b], &next, Ghost(k as int), Ghost(chains[b as int]));
            if found.is_none() {
                proof {
                    // `k` is the first of its name: an earlier one would
                    // have its first occurrence in this chain.
                    assert forall|j: int| 0 <= j < k implies nm(s@, #[trigger] sp[j]) != nm(s@, sp[k as int]) by {
                        if nm(s@, sp[j]) == nm(s@, sp[k as int]) {
                            lemma_first_exists(s@, sp, j);
                            let f = choose|f: int| 0 <= f <= j && nm(s@, sp[f]) == nm(s@, sp[j]) && first_occ(s@, sp, f);
                            assert(chains[b as int].contains(f));
                            let q = choose|q: int| 0 <= q < chains[b as int].len() && chains[b as int][q] == f;
                            assert(nm(s@, sp[chains[b as int][q]]) != nm(s@, sp[k as int]));
                        }
                    }
                    lemma_index_insert(s@, sp, sd, mul, m as int, k as int, chains, head@, next@, b as int);
                }
                let old_head = head[b];
                next.set(k, old_head);
                head.set(b, (k + 1) as usize);
                proof {
                    chains = chains.update(b as int, seq![k as int] + chains[b as int]);
                }
            } else {
                proof {
                    // Not the first of its name: nothing to record.
                    let j = found.unwrap() as int;
                    assert(!first_occ(s@, sp, k as int)) by {
                        assert(nm(s@, sp[j]) == nm(s@, sp[k as int]));
                    }
                    lemma_index_skip(s@, sp, sd, mul, m as int, k as int, chains, head@, next@);
                }
            }
            k = k + 1;
        }
        NameIndex { head, next, sd, mul, chains: Ghost(chains) }
    }

    /// `find_ent` of the name `q[a..b]` among the first `lim` entities.
    pub fn find(&self, s: &[u8], ns: &[XEnt], lim: usize, q: &[u8], a: usize, b: usize) -> (r: Option<usize>)
        requires
            indexes(self, s@, ns@),
            lim <= ns@.len(),
            a <= b <= q@.len(),
            forall|p: int| 0 <= p < ns@.len() ==> (#[trigger] ns@[p]).a <= ns@[p].b <= s@.len(),
        ensures
            match find_ent(ents_view(s@, ns@).subrange(0, lim as int), q@.subrange(a as int, b as int)) {
                Some(j) => r == Some(j as usize),
                None => r is None,
            },
    {
        let m = self.head.len();
        proof {
            reveal(index_ok);
        }
        let h = ex_hash(q, a, b, self.sd, self.mul);
        let bk = ((h >> 32u64) % (m as u64)) as usize;
        let ghost qn = q@.subrange(a as int, b as int);
        let ghost sp = spans(ns@);
        proof {
            reveal(index_ok);
            assert(bkt(self.sd, self.mul, m as int, qn) == bk);
        }
        let ghost ch = self.chains@[bk as int];
        match ex_chain_find(s, ns, q, a, b, self.head[bk], &self.next, Ghost(ns@.len() as int), Ghost(ch)) {
            Some(j) => {
                proof {
                    let p = choose|p: int| 0 <= p < ch.len() && ch[p] == j as int;
                    assert(first_occ(s@, sp, ch[p]));
                    lemma_found(s@, ns@, j as int, qn, lim as int);
                }
                if j < lim {
                    Some(j)
                } else {
                    None
                }
            },
            None => {
                proof {
                    lemma_absent(s@, ns@, self.sd, self.mul, m as int, self.chains@, self.head@, self.next@, qn, lim as int);
                }
                None
            },
        }
    }
}

/// A name that is not the first of its name changes nothing.
proof fn lemma_index_skip(
    s: Seq<u8>,
    ns: Seq<(usize, usize)>,
    sd: u64,
    mul: u64,
    m: int,
    k: int,
    chains: Seq<Seq<int>>,
    head: Seq<usize>,
    next: Seq<usize>,
)
    requires
        index_ok(s, ns, sd, mul, m, k, chains, head, next),
        0 <= k < ns.len(),
        !first_occ(s, ns, k),
    ensures
        index_ok(s, ns, sd, mul, m, k + 1, chains, head, next),
{
    reveal(index_ok);
    assert forall|b: int| 0 <= b < m implies chain_links(k + 1, #[trigger] chains[b], head[b], next) by {
        assert(chain_links(k, chains[b], head[b], next));
    }
}

/// Inserting the first occurrence `k` at the head of its bucket's chain.
proof fn lemma_index_insert(
    s: Seq<u8>,
    ns: Seq<(usize, usize)>,
    sd: u64,
    mul: u64,
    m: int,
    k: int,
    chains: Seq<Seq<int>>,
    head: Seq<usize>,
    next: Seq<usize>,
    b: int,
)
    requires
        index_ok(s, ns, sd, mul, m, k, chains, head, next),
        0 <= k < ns.len() <= isize::MAX,
        first_occ(s, ns, k),
        b == bkt(sd, mul, m, nm(s, ns[k])),
        0 <= b < m,
    ensures
        index_ok(
            s,
            ns,
            sd,
            mul,
            m,
            k + 1,
            chains.update(b, seq![k] + chains[b]),
            head.update(b, (k + 1) as usize),
            next.update(k, head[b]),
        ),
{
    reveal(index_ok);
    let c2 = chains.update(b, seq![k] + chains[b]);
    let h2 = head.update(b, (k + 1) as usize);
    let n2 = next.update(k, head[b]);
    assert forall|b2: int| 0 <= b2 < m implies chain_links(k + 1, #[trigger] c2[b2], h2[b2], n2) by {
        let ch = chains[b2];
        assert(chain_links(k, ch, head[b2], next));
        if b2 == b {
            let c = c2[b2];
            assert forall|p: int| 0 <= p < c.len() implies 0 <= #[trigger] c[p] < k + 1 by {
                if p > 0 {
                    assert(c[p] == ch[p - 1]);
                }
            }
            assert forall|p: int| 0 <= p < c.len() implies #[trigger] n2[c[p]] as int == if p + 1 < c.len() {
                c[p + 1] + 1
            } else {
                0
            } by {
                if p > 0 {
                    assert(c[p] == ch[p - 1]);
                    assert(ch[p - 1] < k);
                    assert(next[ch[p - 1]] as int == if p < ch.len() {
                        ch[p] + 1
                    } else {
                        0
                    });
                } else if ch.len() > 0 {
                    assert(c[1] == ch[0]);
                }
            }
        } else {
            assert(c2[b2] == ch);
            assert forall|p: int| 0 <= p < ch.len() implies 0 <= #[trigger] ch[p] < k + 1 by {
            }
            assert forall|p: int| 0 <= p < ch.len() implies #[trigger] n2[ch[p]] as int == if p + 1 < ch.len() {
                ch[p + 1] + 1
            } else {
                0
            } by {
                assert(ch[p] < k);
                assert(next[ch[p]] as int == if p + 1 < ch.len() {
                    ch[p + 1] + 1
                } else {
                    0
                });
            }
        }
    }
    assert forall|b2: int, p: int|
        0 <= b2 < m && 0 <= p < c2[b2].len() implies bkt(sd, mul, m, nm(s, ns[#[trigger] c2[b2][p]])) == b2
        && first_occ(s, ns, c2[b2][p]) by {
        if b2 == b && p > 0 {
            assert(c2[b2][p] == chains[b2][p - 1]);
        } else if b2 != b {
            assert(c2[b2][p] == chains[b2][p]);
        }
    }
    assert forall|j: int| 0 <= j < k + 1 && first_occ(s, ns, j) implies #[trigger] c2[bkt(sd, mul, m, nm(s, ns[j]))].contains(
        j,
    ) by {
        let bj = bkt(sd, mul, m, nm(s, ns[j]));
        if j == k {
            assert(c2[b][0] == j);
        } else {
            assert(chains[bj].contains(j));
            let q = choose|q: int| 0 <= q < chains[bj].len() && chains[bj][q] == j;
            if bj == b {
                assert(c2[bj][q + 1] == j);
            } else {
                assert(c2[bj][q] == j);
            }
        }
    }
}

} // verus!
