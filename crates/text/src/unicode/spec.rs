//! Unicode normalization forms (UAX #15, Unicode 3.11) over code points:
//! full decomposition, the canonical ordering algorithm as a stable
//! insertion fold, and the canonical composition algorithm (D117) as a
//! fold. Then the theorem that lets an implementation normalize segment by
//! segment: `nf(x + y) == nf(x) + nf(y)` when `y` starts at a boundary.
use super::data::*;
#[cfg(verus_only)]
use verilith_core::utf8::utf8_encode;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Definitions
// ---------------------------------------------------------------------------

/// The full decompositions of `cs`, concatenated.
pub open spec fn decomp_all(cs: Seq<u32>, compat: bool) -> Seq<u32>
    decreases cs.len(),
{
    if cs.len() == 0 {
        seq![]
    } else {
        decomp_all(cs.drop_last(), compat) + decomp(cs.last(), compat)
    }
}

/// Where a nonstarter of class `k` goes in `o[..p]`: after the last
/// character whose class is not above `k`.
pub open spec fn insert_pos(o: Seq<u32>, k: u8, p: int) -> int
    decreases p,
{
    if p > 0 && ccc(o[p - 1]) > k {
        insert_pos(o, k, p - 1)
    } else {
        p
    }
}

/// One step of canonical ordering: a starter goes at the end, a
/// nonstarter after the characters it may not pass.
pub open spec fn insert(o: Seq<u32>, c: u32) -> Seq<u32> {
    if ccc(c) == 0 {
        o.push(c)
    } else {
        o.insert(insert_pos(o, ccc(c), o.len() as int), c)
    }
}

pub open spec fn reorder_from(o: Seq<u32>, d: Seq<u32>) -> Seq<u32>
    decreases d.len(),
{
    if d.len() == 0 {
        o
    } else {
        insert(reorder_from(o, d.drop_last()), d.last())
    }
}

/// Index of the last starter in `o[..p]`, or -1.
pub open spec fn last_starter(o: Seq<u32>, p: int) -> int
    decreases p,
{
    if p <= 0 {
        -1
    } else if ccc(o[p - 1]) == 0 {
        p - 1
    } else {
        last_starter(o, p - 1)
    }
}

/// D115: `c`, appended to `o`, is blocked from `o[l]`.
pub open spec fn blocked(o: Seq<u32>, l: int, c: u32) -> bool {
    exists|k: int| l < k < o.len() && (ccc(#[trigger] o[k]) == 0 || ccc(o[k]) >= ccc(c))
}

/// One step of D117: `c` either combines with the last starter or is
/// appended.
pub open spec fn compose_step(o: Seq<u32>, c: u32) -> Seq<u32> {
    let l = last_starter(o, o.len() as int);
    if l >= 0 && !blocked(o, l, c) && comp(o[l], c) is Some {
        o.update(l, comp(o[l], c)->0)
    } else {
        o.push(c)
    }
}

pub open spec fn compose_from(o: Seq<u32>, d: Seq<u32>) -> Seq<u32>
    decreases d.len(),
{
    if d.len() == 0 {
        o
    } else {
        compose_step(compose_from(o, d.drop_last()), d.last())
    }
}

/// NFD, NFKD, NFC or NFKC of `cs`.
pub open spec fn nf(cs: Seq<u32>, compose: bool, compat: bool) -> Seq<u32> {
    let r = reorder_from(seq![], decomp_all(cs, compat));
    if compose {
        compose_from(seq![], r)
    } else {
        r
    }
}

/// `c` starts a segment: normalizing never moves or merges anything across
/// the boundary before it.
pub open spec fn boundary(c: u32, compose: bool, compat: bool) -> bool {
    &&& ccc(decomp(c, compat)[0]) == 0
    &&& compose ==> !second(decomp(c, compat)[0])
}

/// `c` is a boundary and its own normal form.
pub open spec fn stable(c: u32, compose: bool, compat: bool) -> bool {
    boundary(c, compose, compat) && nf(seq![c], compose, compat) == seq![c]
}

/// A fast character is stable. Checked for every code point by
/// tests/unicode_data.rs, against the verified segment normalizer.
pub axiom fn axiom_fast(c: u32, compose: bool, compat: bool)
    requires
        is_scalar(c),
        has_flag(c, fast_flag(compose, compat)),
    ensures
        stable(c, compose, compat),
        ccc(c) == 0;

/// Full decompositions are in canonical order. Checked for every code
/// point by tests/unicode_data.rs.
pub axiom fn axiom_decomp_ordered(c: u32, compat: bool)
    requires
        is_scalar(c),
    ensures
        reorder_from(seq![], decomp(c, compat)) == decomp(c, compat);

/// UTF-8 encoding of a sequence of scalars.
pub open spec fn enc(cs: Seq<u32>) -> Seq<u8>
    decreases cs.len(),
{
    if cs.len() == 0 {
        seq![]
    } else {
        enc(cs.drop_last()) + utf8_encode(cs.last())
    }
}

// ---------------------------------------------------------------------------
// Folds over concatenations
// ---------------------------------------------------------------------------

pub proof fn lemma_decomp_all_append(a: Seq<u32>, b: Seq<u32>, compat: bool)
    ensures
        decomp_all(a + b, compat) == decomp_all(a, compat) + decomp_all(b, compat),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
        assert(decomp_all(a, compat) + seq![] =~= decomp_all(a, compat));
    } else {
        assert((a + b).drop_last() =~= a + b.drop_last());
        lemma_decomp_all_append(a, b.drop_last(), compat);
        assert(decomp_all(a, compat) + decomp_all(b.drop_last(), compat) + decomp(b.last(), compat) =~= decomp_all(a, compat) + (
        decomp_all(b.drop_last(), compat) + decomp(b.last(), compat)));
    }
}

pub proof fn lemma_decomp_all_one(c: u32, compat: bool)
    ensures
        decomp_all(seq![c], compat) == decomp(c, compat),
{
    reveal_with_fuel(decomp_all, 2);
    assert(seq![c].drop_last() =~= Seq::<u32>::empty());
    assert(Seq::<u32>::empty() + decomp(c, compat) =~= decomp(c, compat));
}

pub proof fn lemma_enc_append(a: Seq<u32>, b: Seq<u32>)
    ensures
        enc(a + b) == enc(a) + enc(b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
        assert(enc(a) + seq![] =~= enc(a));
    } else {
        assert((a + b).drop_last() =~= a + b.drop_last());
        lemma_enc_append(a, b.drop_last());
        assert(enc(a) + enc(b.drop_last()) + utf8_encode(b.last()) =~= enc(a) + (enc(b.drop_last()) + utf8_encode(
            b.last())));
    }
}

pub proof fn lemma_enc_one(c: u32)
    ensures
        enc(seq![c]) == utf8_encode(c),
{
    reveal_with_fuel(enc, 2);
    assert(seq![c].drop_last() =~= Seq::<u32>::empty());
    assert(Seq::<u8>::empty() + utf8_encode(c) =~= utf8_encode(c));
}

pub proof fn lemma_reorder_append(o: Seq<u32>, a: Seq<u32>, b: Seq<u32>)
    ensures
        reorder_from(o, a + b) == reorder_from(reorder_from(o, a), b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        assert((a + b).drop_last() =~= a + b.drop_last());
        lemma_reorder_append(o, a, b.drop_last());
    }
}

pub proof fn lemma_compose_append(o: Seq<u32>, a: Seq<u32>, b: Seq<u32>)
    ensures
        compose_from(o, a + b) == compose_from(compose_from(o, a), b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        assert((a + b).drop_last() =~= a + b.drop_last());
        lemma_compose_append(o, a, b.drop_last());
    }
}

pub proof fn lemma_reorder_one(o: Seq<u32>, c: u32)
    ensures
        reorder_from(o, seq![c]) == insert(o, c),
{
    reveal_with_fuel(reorder_from, 2);
    assert(seq![c].drop_last() =~= Seq::<u32>::empty());
}

pub proof fn lemma_compose_one(o: Seq<u32>, c: u32)
    ensures
        compose_from(o, seq![c]) == compose_step(o, c),
{
    reveal_with_fuel(compose_from, 2);
    assert(seq![c].drop_last() =~= Seq::<u32>::empty());
}

/// Folding `d` is folding its first element, then the rest.
pub proof fn lemma_reorder_first(o: Seq<u32>, d: Seq<u32>)
    requires
        d.len() > 0,
    ensures
        reorder_from(o, d) == reorder_from(insert(o, d[0]), d.drop_first()),
{
    assert(d =~= seq![d[0]] + d.drop_first());
    lemma_reorder_append(o, seq![d[0]], d.drop_first());
    lemma_reorder_one(o, d[0]);
}

pub proof fn lemma_compose_first(o: Seq<u32>, d: Seq<u32>)
    requires
        d.len() > 0,
    ensures
        compose_from(o, d) == compose_from(compose_step(o, d[0]), d.drop_first()),
{
    assert(d =~= seq![d[0]] + d.drop_first());
    lemma_compose_append(o, seq![d[0]], d.drop_first());
    lemma_compose_one(o, d[0]);
}

// ---------------------------------------------------------------------------
// Nothing crosses a starter
// ---------------------------------------------------------------------------

/// `q` begins with a starter.
pub open spec fn led(q: Seq<u32>) -> bool {
    q.len() > 0 && ccc(q[0]) == 0
}

proof fn lemma_insert_pos_shift(o: Seq<u32>, q: Seq<u32>, k: u8, p: int)
    requires
        led(q),
        1 <= p <= q.len(),
    ensures
        insert_pos(o + q, k, o.len() + p) == o.len() + insert_pos(q, k, p),
        1 <= insert_pos(q, k, p) <= p,
    decreases p,
{
    assert((o + q)[o.len() + p - 1] == q[p - 1]);
    if p > 1 && ccc(q[p - 1]) > k {
        lemma_insert_pos_shift(o, q, k, p - 1);
    }
}

proof fn lemma_insert_shift(o: Seq<u32>, q: Seq<u32>, c: u32)
    requires
        led(q),
    ensures
        insert(o + q, c) == o + insert(q, c),
        led(insert(q, c)),
        insert(q, c)[0] == q[0],
{
    if ccc(c) == 0 {
        assert((o + q).push(c) =~= o + q.push(c));
    } else {
        let k = ccc(c);
        lemma_insert_pos_shift(o, q, k, q.len() as int);
        let p = insert_pos(q, k, q.len() as int);
        assert((o + q).len() == o.len() + q.len());
        assert((o + q).insert(o.len() + p, c) =~= o + q.insert(p, c));
    }
}

proof fn lemma_reorder_shift(o: Seq<u32>, q: Seq<u32>, d: Seq<u32>)
    requires
        led(q),
    ensures
        reorder_from(o + q, d) == o + reorder_from(q, d),
        led(reorder_from(q, d)),
        reorder_from(q, d)[0] == q[0],
    decreases d.len(),
{
    if d.len() > 0 {
        lemma_reorder_shift(o, q, d.drop_last());
        lemma_insert_shift(o, reorder_from(q, d.drop_last()), d.last());
    }
}

/// Canonical ordering of `d`, which begins with a starter, does not touch
/// what is already ordered.
pub proof fn lemma_reorder_split(o: Seq<u32>, d: Seq<u32>)
    requires
        led(d),
    ensures
        reorder_from(o, d) == o + reorder_from(seq![], d),
        led(reorder_from(seq![], d)),
        reorder_from(seq![], d)[0] == d[0],
{
    let q = seq![d[0]];
    lemma_reorder_first(o, d);
    lemma_reorder_first(seq![], d);
    assert(insert(o, d[0]) == o + q);
    assert(insert(Seq::<u32>::empty(), d[0]) =~= q);
    lemma_reorder_shift(o, q, d.drop_first());
    lemma_reorder_shift(seq![], q, d.drop_first());
    assert(Seq::<u32>::empty() + q =~= q);
    assert(Seq::<u32>::empty() + reorder_from(q, d.drop_first()) =~= reorder_from(q, d.drop_first()));
}

proof fn lemma_last_starter_shift(o: Seq<u32>, q: Seq<u32>, p: int)
    requires
        led(q),
        1 <= p <= q.len(),
    ensures
        last_starter(o + q, o.len() + p) == o.len() + last_starter(q, p),
        0 <= last_starter(q, p) < p,
    decreases p,
{
    assert((o + q)[o.len() + p - 1] == q[p - 1]);
    if ccc(q[p - 1]) != 0 {
        lemma_last_starter_shift(o, q, p - 1);
    }
}

proof fn lemma_compose_step_shift(o: Seq<u32>, q: Seq<u32>, c: u32)
    requires
        led(q),
    ensures
        compose_step(o + q, c) == o + compose_step(q, c),
        led(compose_step(q, c)),
{
    let oq = o + q;
    lemma_last_starter_shift(o, q, q.len() as int);
    let l = last_starter(q, q.len() as int);
    assert(oq.len() == o.len() + q.len());
    assert(last_starter(oq, oq.len() as int) == o.len() + l);
    assert(oq[o.len() + l] == q[l]);
    assert(blocked(oq, o.len() + l, c) == blocked(q, l, c)) by {
        if blocked(q, l, c) {
            let k = choose|k: int| l < k < q.len() && (ccc(#[trigger] q[k]) == 0 || ccc(q[k]) >= ccc(c));
            assert(oq[o.len() + k] == q[k]);
        }
        if blocked(oq, o.len() + l, c) {
            let k = choose|k: int| o.len() + l < k < oq.len() && (ccc(#[trigger] oq[k]) == 0 || ccc(oq[k]) >= ccc(c));
            assert(q[k - o.len()] == oq[k]);
        }
    }
    if !blocked(q, l, c) && comp(q[l], c) is Some {
        let p = comp(q[l], c)->0;
        axiom_comp(q[l], c);
        assert(oq.update(o.len() + l, p) =~= o + q.update(l, p));
    } else {
        assert(oq.push(c) =~= o + q.push(c));
    }
}

proof fn lemma_compose_shift(o: Seq<u32>, q: Seq<u32>, d: Seq<u32>)
    requires
        led(q),
    ensures
        compose_from(o + q, d) == o + compose_from(q, d),
        led(compose_from(q, d)),
    decreases d.len(),
{
    if d.len() > 0 {
        lemma_compose_shift(o, q, d.drop_last());
        lemma_compose_step_shift(o, compose_from(q, d.drop_last()), d.last());
    }
}

/// Composition of `d`, which begins with a starter that is never the second
/// of a pair, does not touch what is already composed.
pub proof fn lemma_compose_split(o: Seq<u32>, d: Seq<u32>)
    requires
        led(d),
        !second(d[0]),
    ensures
        compose_from(o, d) == o + compose_from(seq![], d),
{
    let q = seq![d[0]];
    lemma_compose_first(o, d);
    lemma_compose_first(seq![], d);
    if comp(o[last_starter(o, o.len() as int)], d[0]) is Some {
        axiom_comp(o[last_starter(o, o.len() as int)], d[0]);
    }
    assert(compose_step(o, d[0]) == o + q);
    assert(compose_step(Seq::<u32>::empty(), d[0]) =~= q);
    lemma_compose_shift(o, q, d.drop_first());
    lemma_compose_shift(seq![], q, d.drop_first());
    assert(Seq::<u32>::empty() + q =~= q);
    assert(Seq::<u32>::empty() + compose_from(q, d.drop_first()) =~= compose_from(q, d.drop_first()));
}

/// Segmentation: normalizing `x + y`, with `y` starting at a boundary, is
/// normalizing `x` and `y` apart.
pub proof fn lemma_nf_split(x: Seq<u32>, y: Seq<u32>, compose: bool, compat: bool)
    requires
        y.len() > 0,
        boundary(y[0], compose, compat),
    ensures
        nf(x + y, compose, compat) == nf(x, compose, compat) + nf(y, compose, compat),
{
    let dx = decomp_all(x, compat);
    let dy = decomp_all(y, compat);
    lemma_decomp_all_append(x, y, compat);
    assert(y =~= seq![y[0]] + y.drop_first());
    lemma_decomp_all_append(seq![y[0]], y.drop_first(), compat);
    lemma_decomp_all_one(y[0], compat);
    lemma_decomp_nonempty(y[0], compat);
    assert(dy[0] == decomp(y[0], compat)[0]);
    lemma_reorder_append(seq![], dx, dy);
    let rx = reorder_from(seq![], dx);
    let ry = reorder_from(seq![], dy);
    lemma_reorder_split(rx, dy);
    if compose {
        lemma_compose_append(seq![], rx, ry);
        lemma_compose_split(compose_from(seq![], rx), ry);
    }
}

/// Appending a stable character appends it to the normal form.
pub proof fn lemma_nf_stable(x: Seq<u32>, c: u32, compose: bool, compat: bool)
    requires
        stable(c, compose, compat),
    ensures
        nf(x.push(c), compose, compat) == nf(x, compose, compat).push(c),
{
    assert(x.push(c) =~= x + seq![c]);
    lemma_nf_split(x, seq![c], compose, compat);
}

/// Appending a run of stable characters appends the run.
pub proof fn lemma_nf_stable_run(x: Seq<u32>, r: Seq<u32>, compose: bool, compat: bool)
    requires
        forall|i: int| 0 <= i < r.len() ==> stable(#[trigger] r[i], compose, compat),
    ensures
        nf(x + r, compose, compat) == nf(x, compose, compat) + r,
    decreases r.len(),
{
    if r.len() == 0 {
        assert(x + r =~= x);
        assert(nf(x, compose, compat) + r =~= nf(x, compose, compat));
    } else {
        let r0 = r.drop_last();
        lemma_nf_stable_run(x, r0, compose, compat);
        assert(stable(r[r.len() - 1], compose, compat));
        lemma_nf_stable(x + r0, r.last(), compose, compat);
        assert((x + r0).push(r.last()) =~= x + r);
        assert((nf(x, compose, compat) + r0).push(r.last()) =~= nf(x, compose, compat) + r);
    }
}

/// When decomposing, character `k` can be copied through after the
/// characters `kd..k` were: it is stable, or it does not decompose and does
/// not sort before the character just before it.
pub open spec fn passable(cs: Seq<u32>, kd: int, k: int, compose: bool, compat: bool) -> bool {
    ||| stable(cs[k], compose, compat)
    ||| !compose && k > kd && decomp(cs[k], compat) == seq![cs[k]] && ccc(cs[k - 1]) <= ccc(cs[k])
}

proof fn lemma_nf_pass(x: Seq<u32>, c: u32, compat: bool)
    requires
        decomp(c, compat) == seq![c],
        nf(x, false, compat).len() > 0,
        ccc(nf(x, false, compat).last()) <= ccc(c),
    ensures
        nf(x.push(c), false, compat) == nf(x, false, compat).push(c),
{
    let r = nf(x, false, compat);
    assert(x.push(c).drop_last() =~= x);
    lemma_reorder_append(seq![], decomp_all(x, compat), seq![c]);
    lemma_reorder_one(r, c);
    if ccc(c) != 0 {
        assert(insert_pos(r, ccc(c), r.len() as int) == r.len());
        assert(r.insert(r.len() as int, c) =~= r.push(c));
    }
}

/// Copying through a run of passable characters appends the run.
pub proof fn lemma_nf_pass_run(cs: Seq<u32>, kd: int, b: int, compose: bool, compat: bool)
    requires
        0 <= kd <= b <= cs.len(),
        forall|k: int| kd <= k < b ==> passable(cs, kd, k, compose, compat),
    ensures
        nf(cs.take(b), compose, compat) == nf(cs.take(kd), compose, compat) + cs.subrange(kd, b),
    decreases b - kd,
{
    if b == kd {
        assert(nf(cs.take(kd), compose, compat) + cs.subrange(kd, b) =~= nf(cs.take(kd), compose, compat));
    } else {
        lemma_nf_pass_run(cs, kd, b - 1, compose, compat);
        let c = cs[b - 1];
        let r = nf(cs.take(kd), compose, compat) + cs.subrange(kd, b - 1);
        assert(cs.take(b) =~= cs.take(b - 1).push(c));
        assert(passable(cs, kd, b - 1, compose, compat));
        if stable(c, compose, compat) {
            lemma_nf_stable(cs.take(b - 1), c, compose, compat);
        } else {
            assert(r.last() == cs[b - 2]);
            lemma_nf_pass(cs.take(b - 1), c, compat);
        }
        assert(r.push(c) =~= nf(cs.take(kd), compose, compat) + cs.subrange(kd, b));
    }
}

} // verus!
