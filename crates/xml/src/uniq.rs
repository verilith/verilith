//! WFC: Unique Att Spec for start tags with many attributes, in time
//! linear in their number: each name is hashed into a table of chains, and
//! compared only with the names already in its chain. Equal names hash
//! alike, so a name equal to an earlier one meets it in its chain; the
//! proof keeps, for each bucket, the list of names its chain holds.
//!
//! The hash is seeded at random for each tag, so that no input can be
//! made to put many names in one chain (hash flooding, as in expat's
//! CVE-2012-0876, fixed there the same way). The seed's value plays no
//! part in the result; only its source, `seed`, is trusted to terminate.
use crate::lex::{ex_bytes_eq, get};
use crate::spec::*;
use crate::tape::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Names, apart from the tape
// ---------------------------------------------------------------------------

/// The name a span stands for.
pub open spec fn nm(s: Seq<u8>, x: (u32, u32)) -> Seq<u8> {
    s.subrange(x.0 as int, x.1 as int)
}

/// The spans are inside `s`.
pub open spec fn spans_ok(s: Seq<u8>, ns: Seq<(u32, u32)>) -> bool {
    forall|p: int| 0 <= p < ns.len() ==> (#[trigger] ns[p]).0 <= ns[p].1 <= s.len()
}

/// No two spans name the same.
pub open spec fn distinct(s: Seq<u8>, ns: Seq<(u32, u32)>) -> bool {
    forall|p: int, q: int| 0 <= p < q < ns.len() ==> nm(s, #[trigger] ns[p]) != nm(s, #[trigger] ns[q])
}

/// `ns` lists the spans of the `Attr` tokens of `t[first..k]`, in order;
/// `ix` is where each is.
pub open spec fn listed(t: Seq<XTok>, first: int, k: int, ix: Seq<int>, ns: Seq<(u32, u32)>) -> bool {
    &&& ix.len() == ns.len()
    &&& forall|p: int|
        0 <= p < ix.len() ==> first <= #[trigger] ix[p] < k && t[ix[p]] is Attr && t[ix[p]]->Attr_start == ns[p].0 as int
            && t[ix[p]]->Attr_end == ns[p].1 as int
    &&& forall|p: int, q: int| 0 <= p < q < ix.len() ==> #[trigger] ix[p] < #[trigger] ix[q]
    &&& forall|j: int| first <= j < k && #[trigger] t[j] is Attr ==> ix.contains(j)
}

/// The spans of the attributes from `first` on.
fn ex_list(tape: &Tape, first: usize) -> (r: (Vec<(u32, u32)>, Ghost<Seq<int>>))
    requires
        first <= tape@.len(),
    ensures
        listed(tape@, first as int, tape@.len() as int, r.1@, r.0@),
{
    let ghost t = tape@;
    let mut ns: Vec<(u32, u32)> = Vec::new();
    let ghost mut ix: Seq<int> = Seq::empty();
    let n = tape.len();
    let mut k = first;
    while k < n
        invariant
            first <= k <= n,
            n == t.len(),
            t == tape@,
            listed(t, first as int, k as int, ix, ns@),
        decreases n - k,
    {
        let tk = tape.toks[k];
        proof {
            assert(t[k as int] == tk@);
        }
        if is_attr(tk.kind) {
            ns.push((tk.a, tk.b));
            proof {
                let ix0 = ix;
                ix = ix.push(k as int);
                assert forall|j: int| first <= j < k + 1 && #[trigger] t[j] is Attr implies ix.contains(j) by {
                    if j < k {
                        let p = choose|p: int| 0 <= p < ix0.len() && ix0[p] == j;
                        assert(ix[p] == j);
                    } else {
                        assert(ix[ix.len() - 1] == j);
                    }
                }
            }
        } else {
            proof {
                assert forall|j: int| first <= j < k + 1 && #[trigger] t[j] is Attr implies ix.contains(j) by {
                    if j == k as int {
                        assert(!(t[j] is Attr));
                    }
                }
            }
        }
        k = k + 1;
    }
    (ns, Ghost(ix))
}

/// The tape's attributes are distinct exactly when the listed names are.
proof fn lemma_listed_distinct(s: Seq<u8>, t: Seq<XTok>, first: int, ix: Seq<int>, ns: Seq<(u32, u32)>)
    requires
        listed(t, first, t.len() as int, ix, ns),
    ensures
        attrs_distinct(s, t, first) == distinct(s, ns),
{
    if distinct(s, ns) {
        assert forall|j: int, k: int|
            first <= j < k < t.len() && #[trigger] t[j] is Attr && #[trigger] t[k] is Attr implies s.subrange(
            t[j]->Attr_start,
            t[j]->Attr_end,
        ) != s.subrange(t[k]->Attr_start, t[k]->Attr_end) by {
            let p = choose|p: int| 0 <= p < ix.len() && ix[p] == j;
            let q = choose|q: int| 0 <= q < ix.len() && ix[q] == k;
            if q < p {
                assert(ix[q] < ix[p]);
            }
            assert(p != q);
            assert(p < q);
            assert(nm(s, ns[p]) != nm(s, ns[q]));
        }
    }
    if attrs_distinct(s, t, first) {
        assert forall|p: int, q: int| 0 <= p < q < ns.len() implies nm(s, #[trigger] ns[p]) != nm(s, #[trigger] ns[q]) by {
            assert(ix[p] < ix[q]);
            assert(t[ix[p]] is Attr && t[ix[q]] is Attr);
        }
    }
}

// ---------------------------------------------------------------------------
// The hash table
// ---------------------------------------------------------------------------

/// The hash of the bytes `b`.
pub open spec fn hash(seed: u64, mul: u64, b: Seq<u8>) -> u64
    decreases b.len(),
{
    if b.len() == 0 {
        seed
    } else {
        let x = hash(seed, mul, b.drop_last()) ^ (b.last() as u64);
        ((x as int * mul as int) % 0x1_0000_0000_0000_0000int) as u64
    }
}

/// The bucket of a name, among `m`.
pub open spec fn bkt(seed: u64, mul: u64, m: int, b: Seq<u8>) -> int {
    ((hash(seed, mul, b) >> 32u64) as int) % m
}

/// Random words for the hash: the trusted part (any values are correct).
#[verifier::external_body]
pub fn seed() -> (r: (u64, u64)) {
    use std::hash::BuildHasher;
    let st = std::collections::hash_map::RandomState::new();
    (st.hash_one(0x5EEDu64), st.hash_one(0x1u64) | 1)
}

/// `hash(seed, mul, s[a..b])`.
pub fn ex_hash(s: &[u8], a: usize, b: usize, seed: u64, mul: u64) -> (h: u64)
    requires
        a <= b <= s@.len(),
    ensures
        h == hash(seed, mul, s@.subrange(a as int, b as int)),
{
    let mut h = seed;
    let mut k = a;
    proof {
        assert(s@.subrange(a as int, a as int) =~= Seq::<u8>::empty());
    }
    while k < b
        invariant
            a <= k <= b <= s@.len(),
            h == hash(seed, mul, s@.subrange(a as int, k as int)),
        decreases b - k,
    {
        let c = get(s, k);
        proof {
            assert(s@.subrange(a as int, k + 1).drop_last() =~= s@.subrange(a as int, k as int));
        }
        let x = h ^ (c as u64);
        proof {
            vstd::arithmetic::mul::lemma_mul_upper_bound(x as int, u64::MAX as int, mul as int, u64::MAX as int);
        }
        h = ((x as u128 * mul as u128) % 0x1_0000_0000_0000_0000u128) as u64;
        k = k + 1;
    }
    h
}

/// One chain, linked from `h` through `next` (each entry one more than a
/// name's index, 0 for the end), of names before `k`.
pub open spec fn chain_links(k: int, ch: Seq<int>, h: u32, next: Seq<u32>) -> bool {
    &&& h as int == if ch.len() == 0 {
        0
    } else {
        ch[0] + 1
    }
    &&& forall|p: int| 0 <= p < ch.len() ==> 0 <= #[trigger] ch[p] < k
    &&& forall|p: int|
        0 <= p < ch.len() ==> #[trigger] next[ch[p]] as int == if p + 1 < ch.len() {
            ch[p + 1] + 1
        } else {
            0
        }
}

/// The chains hold exactly the names before `k`, each in its bucket's,
/// linked by `head` and `next`.
#[verifier::opaque]
pub open spec fn chains_ok(
    s: Seq<u8>,
    ns: Seq<(u32, u32)>,
    sd: u64,
    mul: u64,
    m: int,
    k: int,
    chains: Seq<Seq<int>>,
    head: Seq<u32>,
    next: Seq<u32>,
) -> bool {
    &&& chains.len() == m && head.len() == m && next.len() == ns.len()
    &&& forall|b: int| 0 <= b < m ==> chain_links(k, #[trigger] chains[b], head[b], next)
    &&& forall|b: int, p: int|
        0 <= b < m && 0 <= p < chains[b].len() ==> bkt(sd, mul, m, nm(s, ns[#[trigger] chains[b][p]])) == b
    &&& forall|j: int| 0 <= j < k ==> #[trigger] chains[bkt(sd, mul, m, nm(s, ns[j]))].contains(j)
}

proof fn lemma_chains_init(s: Seq<u8>, ns: Seq<(u32, u32)>, sd: u64, mul: u64, m: int, head: Seq<u32>, next: Seq<u32>)
    requires
        m > 0,
        head.len() == m,
        next.len() == ns.len(),
        forall|b: int| 0 <= b < m ==> head[b] == 0,
    ensures
        chains_ok(s, ns, sd, mul, m, 0, Seq::new(m as nat, |b: int| Seq::<int>::empty()), head, next),
{
    reveal(chains_ok);
}

/// The chain of bucket `b`, and that it holds every earlier name of its
/// bucket.
proof fn lemma_chain_of(
    s: Seq<u8>,
    ns: Seq<(u32, u32)>,
    sd: u64,
    mul: u64,
    m: int,
    k: int,
    chains: Seq<Seq<int>>,
    head: Seq<u32>,
    next: Seq<u32>,
    b: int,
)
    requires
        chains_ok(s, ns, sd, mul, m, k, chains, head, next),
        0 <= b < m,
    ensures
        chain_links(k, chains[b], head[b], next),
        forall|j: int| 0 <= j < k && bkt(sd, mul, m, nm(s, ns[j])) == b ==> #[trigger] chains[b].contains(j),
{
    reveal(chains_ok);
}

/// Inserting name `k` at the head of its bucket's chain.
proof fn lemma_chains_insert(
    s: Seq<u8>,
    ns: Seq<(u32, u32)>,
    sd: u64,
    mul: u64,
    m: int,
    k: int,
    chains: Seq<Seq<int>>,
    head: Seq<u32>,
    next: Seq<u32>,
    b: int,
)
    requires
        chains_ok(s, ns, sd, mul, m, k, chains, head, next),
        0 <= k < ns.len() < u32::MAX,
        b == bkt(sd, mul, m, nm(s, ns[k])),
        0 <= b < m,
    ensures
        chains_ok(
            s,
            ns,
            sd,
            mul,
            m,
            k + 1,
            chains.update(b, seq![k] + chains[b]),
            head.update(b, (k + 1) as u32),
            next.update(k, head[b]),
        ),
{
    reveal(chains_ok);
    let c2 = chains.update(b, seq![k] + chains[b]);
    let h2 = head.update(b, (k + 1) as u32);
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
        0 <= b2 < m && 0 <= p < c2[b2].len() implies bkt(sd, mul, m, nm(s, ns[#[trigger] c2[b2][p]])) == b2 by {
        if b2 == b && p > 0 {
            assert(c2[b2][p] == chains[b2][p - 1]);
        } else if b2 != b {
            assert(c2[b2][p] == chains[b2][p]);
        }
    }
    assert forall|j: int| 0 <= j < k + 1 implies #[trigger] c2[bkt(sd, mul, m, nm(s, ns[j]))].contains(j) by {
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

/// Whether the chain `ch` from `h` holds a name like the `k`th.
fn chain_has(s: &[u8], ns: &Vec<(u32, u32)>, k: usize, h: u32, next: &Vec<u32>, Ghost(ch): Ghost<Seq<int>>) -> (r: bool)
    requires
        k < ns@.len() < u32::MAX,
        next@.len() == ns@.len(),
        spans_ok(s@, ns@),
        chain_links(k as int, ch, h, next@),
    ensures
        r == exists|q: int| 0 <= q < ch.len() && nm(s@, ns@[#[trigger] ch[q]]) == nm(s@, ns@[k as int]),
{
    let (ka, kb) = ns[k];
    let mut cur = h;
    let ghost mut p: int = 0;
    while cur != 0
        invariant
            0 <= p <= ch.len(),
            k < ns@.len() < u32::MAX,
            next@.len() == ns@.len(),
            spans_ok(s@, ns@),
            chain_links(k as int, ch, h, next@),
            (ka, kb) == ns@[k as int],
            cur as int == if p < ch.len() {
                ch[p] + 1
            } else {
                0
            },
            forall|q: int| 0 <= q < p ==> nm(s@, ns@[#[trigger] ch[q]]) != nm(s@, ns@[k as int]),
        decreases ch.len() - p,
    {
        let j = (cur - 1) as usize;
        proof {
            assert(p < ch.len());
            assert(j == ch[p]);
            assert(0 <= ch[p] < k);
        }
        let (ja, jb) = ns[j];
        proof {
            assert(ns@[j as int] == (ja, jb));
            assert(ja <= jb <= s@.len() && ka <= kb <= s@.len());
        }
        let same = ex_bytes_eq(s, ja as usize, jb as usize, s, ka as usize, kb as usize);
        proof {
            assert(nm(s@, ns@[ch[p]]) == s@.subrange(ja as int, jb as int));
            assert(nm(s@, ns@[k as int]) == s@.subrange(ka as int, kb as int));
            assert(same == (nm(s@, ns@[ch[p]]) == nm(s@, ns@[k as int])));
        }
        if same {
            return true;
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
    false
}

/// `distinct(s, ns)`, with a hash table.
fn ex_distinct_names(s: &[u8], ns: &Vec<(u32, u32)>) -> (r: bool)
    requires
        ns@.len() < u32::MAX,
        spans_ok(s@, ns@),
    ensures
        r == distinct(s@, ns@),
{
    let n = ns.len();
    let m: usize = n + 1;
    let (sd, mul) = seed();
    let mut head: Vec<u32> = Vec::new();
    while head.len() < m
        invariant
            head@.len() <= m,
            forall|b: int| 0 <= b < head@.len() ==> head@[b] == 0,
        decreases m - head@.len(),
    {
        head.push(0);
    }
    let mut next: Vec<u32> = Vec::new();
    while next.len() < n
        invariant
            next@.len() <= n,
        decreases n - next@.len(),
    {
        next.push(0);
    }
    let ghost mut chains: Seq<Seq<int>> = Seq::new(m as nat, |b: int| Seq::<int>::empty());
    proof {
        lemma_chains_init(s@, ns@, sd, mul, m as int, head@, next@);
    }
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            n == ns@.len() < u32::MAX,
            m == n + 1,
            head@.len() == m,
            next@.len() == n,
            spans_ok(s@, ns@),
            chains_ok(s@, ns@, sd, mul, m as int, k as int, chains, head@, next@),
            forall|p: int, q: int| 0 <= p < q < k ==> nm(s@, #[trigger] ns@[p]) != nm(s@, #[trigger] ns@[q]),
        decreases n - k,
    {
        let (a, b0) = ns[k];
        proof {
            assert(ns@[k as int].0 <= ns@[k as int].1 <= s@.len());
        }
        let h = ex_hash(s, a as usize, b0 as usize, sd, mul);
        let b = ((h >> 32u64) % (m as u64)) as usize;
        proof {
            assert(nm(s@, ns@[k as int]) == s@.subrange(a as int, b0 as int));
            assert(bkt(sd, mul, m as int, nm(s@, ns@[k as int])) == b);
            lemma_chain_of(s@, ns@, sd, mul, m as int, k as int, chains, head@, next@, b as int);
        }
        if chain_has(s, ns, k, head[b], &next, Ghost(chains[b as int])) {
            proof {
                let ch = chains[b as int];
                let q = choose|q: int| 0 <= q < ch.len() && nm(s@, ns@[#[trigger] ch[q]]) == nm(s@, ns@[k as int]);
                assert(0 <= ch[q] < k);
                assert(nm(s@, ns@[ch[q]]) == nm(s@, ns@[k as int]));
            }
            return false;
        }
        proof {
            // An earlier equal name would hash alike, so be in this chain.
            assert forall|p: int, q: int| 0 <= p < q < k + 1 implies nm(s@, #[trigger] ns@[p]) != nm(
                s@,
                #[trigger] ns@[q],
            ) by {
                if q == k as int && nm(s@, ns@[p]) == nm(s@, ns@[k as int]) {
                    let ch = chains[b as int];
                    assert(bkt(sd, mul, m as int, nm(s@, ns@[p])) == b);
                    assert(ch.contains(p));
                    let r = choose|r: int| 0 <= r < ch.len() && ch[r] == p;
                    assert(nm(s@, ns@[ch[r]]) != nm(s@, ns@[k as int]));
                }
            }
            lemma_chains_insert(s@, ns@, sd, mul, m as int, k as int, chains, head@, next@, b as int);
        }
        let old_head = head[b];
        next.set(k, old_head);
        head.set(b, (k + 1) as u32);
        proof {
            chains = chains.update(b as int, seq![k as int] + chains[b as int]);
        }
        k = k + 1;
    }
    true
}

/// A strictly increasing sequence of numbers in `[lo, hi)` has at most
/// `hi - lo` of them.
proof fn lemma_increasing_len(ix: Seq<int>, lo: int, hi: int)
    requires
        lo <= hi,
        forall|p: int| 0 <= p < ix.len() ==> lo <= #[trigger] ix[p] < hi,
        forall|p: int, q: int| 0 <= p < q < ix.len() ==> #[trigger] ix[p] < #[trigger] ix[q],
    ensures
        ix.len() <= hi - lo,
    decreases ix.len(),
{
    if ix.len() > 0 {
        let rest = ix.drop_last();
        assert forall|p: int| 0 <= p < rest.len() implies lo <= #[trigger] rest[p] < ix.last() by {
            assert(rest[p] == ix[p]);
            assert(ix[p] < ix[ix.len() - 1]);
        }
        assert forall|p: int, q: int| 0 <= p < q < rest.len() implies #[trigger] rest[p] < #[trigger] rest[q] by {
            assert(rest[p] == ix[p] && rest[q] == ix[q]);
        }
        assert(lo <= ix[ix.len() - 1] < hi);
        lemma_increasing_len(rest, lo, ix.last());
        assert(rest.len() + 1 == ix.len());
    }
}

/// The attribute names in `t[first..]` are all different, decided with a
/// hash table: `attrs_distinct`.
pub fn ex_distinct_hashed(s: &[u8], tape: &Tape, first: usize) -> (r: bool)
    requires
        first <= tape@.len() < u32::MAX,
        forall|m: int|
            #![trigger tape@[m]]
            first <= m < tape@.len() && tape@[m] is Attr ==> 0 <= tape@[m]->Attr_start <= tape@[m]->Attr_end <= s@.len(),
    ensures
        r == attrs_distinct(s@, tape@, first as int),
{
    let (ns, Ghost(ix)) = ex_list(tape, first);
    proof {
        lemma_listed_distinct(s@, tape@, first as int, ix, ns@);
        assert forall|p: int| 0 <= p < ns@.len() implies (#[trigger] ns@[p]).0 <= ns@[p].1 <= s@.len() by {
            assert(tape@[ix[p]] is Attr);
        }
        lemma_increasing_len(ix, first as int, tape@.len() as int);
    }
    ex_distinct_names(s, &ns)
}

} // verus!
