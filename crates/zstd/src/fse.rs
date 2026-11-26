//! FSE table descriptions and decoding tables (RFC 8878 §4.1).
#[allow(unused_imports)]
use crate::spec::*;
use crate::bits::*;
use crate::work::Meter;
#[cfg(verus_only)]
use verilith_core::bits::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::mul::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
#[cfg(verus_only)]
use vstd::bits::*;
#[cfg(verus_only)]
use vstd::set_lib::*;
use vstd::prelude::*;

verus! {

/// A distribution as the spec sees it.
pub open spec fn iseq(v: Seq<i16>) -> Seq<int> {
    Seq::new(v.len(), |i: int| v[i] as int)
}

/// Probabilities from -1 up to `2^log`, as every distribution the decoder
/// builds a table from has.
pub open spec fn norm_ok(v: Seq<i16>, log: nat) -> bool {
    forall|i: int| 0 <= i < v.len() ==> -1 <= #[trigger] v[i] <= pow2(log)
}

/// Reads the zero repeat flags (`nc_zeros`).
fn nc_zeros_exec(b: &[u8], q0: usize, Tracked(m): Tracked<&mut Meter>) -> (r: Option<(usize, usize)>)
    requires
        q0 <= 8 * b@.len(),
        b@.len() < BITS_MAX,
    ensures
        r is Some ==> r.unwrap().0 >= q0 + 2 && 2 * (final(m).n - old(m).n) <= r.unwrap().0 - q0,
        final(m).n <= old(m).n + 8 * b@.len() - q0 + 1,
        match nc_zeros(b@, q0 as int, 0) {
            None => r is None,
            Some((q, z)) => r is Some && r.unwrap().0 as int == q && r.unwrap().1 as nat == z && q
                <= 8 * b@.len(),
        },
        r is Some ==> r.unwrap().1 <= 2 * r.unwrap().0,
{
    let mut q = q0;
    let mut z: usize = 0;
    loop
        invariant
            q <= 8 * b@.len(),
            b@.len() < BITS_MAX,
            z <= 2 * q,
            nc_zeros(b@, q as int, z as nat) == nc_zeros(b@, q0 as int, 0),
            q >= q0,
            2 * (m.n - old(m).n) == q - q0,
        decreases 8 * b@.len() - q,
    {
        proof {
            m.n = m.n + 1;
        }
        if q + 2 > 8 * b.len() {
            return None;
        }
        let f = bits_at(b, q, 2) as usize;
        proof {
            lemma2_to64();
        }
        if f == 3 {
            q = q + 2;
            z = z + 3;
        } else {
            return Some((q + 2, z + f));
        }
    }
}

/// Reads one probability field (`nc_value`).
fn nc_value_exec(b: &[u8], q: usize, rem: u32) -> (r: Option<(u32, usize)>)
    requires
        q <= 8 * b@.len(),
        b@.len() < BITS_MAX,
        2 <= rem <= 1025,
    ensures
        match nc_value(b@, q as int, rem as int) {
            None => r is None,
            Some((v, q2)) => r is Some && r.unwrap().0 as int == v && r.unwrap().1 as int == q2 && q2
                <= 8 * b@.len() && 0 <= v <= rem,
        },
{
    let hb = highbit_u32(rem);
    proof {
        lemma_highbit(rem as nat);
        assert(pow2(11) == 2048) by {
            lemma2_to64();
        }
        if hb >= 11 {
            lemma_pow2_le(11, hb as nat);
        }
        lemma_u32_pow2_no_overflow(hb as nat);
        lemma_u32_shl_is_mul(1, hb);
        lemma_pow2_unfold(hb as nat + 1);
    }
    let t: u32 = 1u32 << hb;
    let nb: u32 = hb + 1;
    let max: u32 = 2 * t - 1 - rem;
    if q + nb as usize - 1 > 8 * b.len() {
        return None;
    }
    let low = bits_at(b, q, nb - 1) as u32;
    if low < max {
        return Some((low, q + nb as usize - 1));
    }
    if q + nb as usize > 8 * b.len() {
        return None;
    }
    let v = bits_at(b, q, nb) as u32;
    proof {
        lemma_pow2_unfold(nb as nat);
    }
    if v >= t {
        Some((v - max, q + nb as usize))
    } else {
        Some((v, q + nb as usize))
    }
}

/// Reads an FSE table description at the start of `b` (`fse_desc`).
pub fn read_ncount(b: &[u8], maxsv: u32, maxlog: u32, Tracked(m): Tracked<&mut Meter>) -> (r: Option<(u32, Vec<i16>, usize)>)
    requires
        maxsv <= 255,
        maxlog <= 9,
        b@.len() < BITS_MAX,
    ensures
        final(m).n <= old(m).n + 3 * maxsv + 8 * b@.len() + 6,
        match fse_desc(b@, maxsv as nat, maxlog as nat) {
            None => r is None,
            Some((log, norm, used)) => {
                &&& r is Some
                &&& r.unwrap().0 as nat == log
                &&& iseq(r.unwrap().1@) == norm
                &&& r.unwrap().2 as int == used
                &&& 5 <= log <= maxlog
                &&& 1 <= norm.len() <= maxsv + 1
                &&& norm_ok(r.unwrap().1@, log)
                &&& used <= b@.len()
                &&& psum(norm, norm.len() as int) == pow2(log)
            },
        },
{
    if b.len() == 0 {
        return None;
    }
    let l4 = bits_at(b, 0, 4);
    proof {
        lemma2_to64();
    }
    let log = l4 as u32 + 5;
    if log > maxlog {
        return None;
    }
    proof {
        lemma_u32_pow2_no_overflow(log as nat);
        lemma_u32_shl_is_mul(1, log);
        lemma_pow2_le(log as nat, 9);
        assert(pow2(9) == 512) by {
            lemma2_to64();
        }
    }
    let maxsv1: usize = maxsv as usize + 1;
    let mut q: usize = 4;
    let mut norm: Vec<i16> = Vec::new();
    let mut rem: u32 = (1u32 << log) + 1;
    let mut prev0 = false;
    let ghost full = nc_run(b@, 4, Seq::empty(), pow2(log as nat) + 1int, false, maxsv1 as nat);
    proof {
        assert(fse_desc(b@, maxsv as nat, maxlog as nat) == match full {
            None => None,
            Some((nr, qq)) => Some((log as nat, nr, (qq + 7) / 8)),
        });
        if full is Some {
            lemma_nc_run_psum(b@, 4, Seq::empty(), pow2(log as nat) + 1int, false, maxsv1 as nat);
        }
    }
    proof {
        assert(iseq(norm@) =~= Seq::<int>::empty());
    }
    loop
        invariant
            q <= 8 * b@.len(),
            b@.len() < BITS_MAX,
            maxsv1 == maxsv + 1,
            maxsv <= 255,
            5 <= log <= 9,
            pow2(log as nat) <= 512,
            1 <= rem <= pow2(log as nat) + 1,
            norm@.len() <= maxsv1,
            norm_ok(norm@, log as nat),
            prev0 ==> norm@.len() >= 1,
            nc_run(b@, q as int, iseq(norm@), rem as int, prev0, maxsv1 as nat) == full,
            full == nc_run(b@, 4, Seq::empty(), pow2(log as nat) + 1int, false, maxsv1 as nat),
            fse_desc(b@, maxsv as nat, maxlog as nat) == match full {
                None => None,
                Some((nr, qq)) => Some((log as nat, nr, (qq + 7) / 8)),
            },
            log <= maxlog,
            full is Some ==> psum(full.unwrap().0, full.unwrap().0.len() as int) == pow2(log as nat),
            q >= 4,
            m.n <= old(m).n + 3 * norm@.len() + q - 4,
        decreases maxsv1 - norm@.len(), if prev0 {
            1int
        } else {
            0int
        },
    {
        let ghost cur = nc_run(b@, q as int, iseq(norm@), rem as int, prev0, maxsv1 as nat);
        proof {
            m.n = m.n + 1;
        }
        if norm.len() > maxsv1 || rem < 2 {
            proof {
                assert(cur is None);
            }
            return None;
        }
        if prev0 {
            match nc_zeros_exec(b, q, Tracked(m)) {
                None => {
                    return None;
                },
                Some((q2, z)) => {
                    if norm.len() + z >= maxsv1 {
                        proof {
                            assert(iseq(norm@).len() + z >= maxsv1);
                        }
                        return None;
                    }
                    let ghost n0 = norm@;
                    let ghost m1 = m.n;
                    let mut k: usize = 0;
                    while k < z
                        invariant
                            k <= z,
                            norm@.len() == n0.len() + k,
                            norm@ == n0 + Seq::new(k as nat, |i: int| 0i16),
                            m.n == m1 + k,
                        decreases z - k,
                    {
                        proof {
                            m.n = m.n + 1;
                        }
                        norm.push(0);
                        k = k + 1;
                        proof {
                            assert(norm@ =~= n0 + Seq::new(k as nat, |i: int| 0i16));
                        }
                    }
                    proof {
                        assert(iseq(norm@) =~= iseq(n0) + Seq::new(z as nat, |i: int| 0int));
                        assert forall|i: int| 0 <= i < norm@.len() implies -1 <= #[trigger] norm@[i]
                            <= pow2(log as nat) by {
                            if i >= n0.len() {
                                assert(norm@[i] == 0);
                            } else {
                                assert(norm@[i] == n0[i]);
                            }
                        }
                    }
                    q = q2;
                    prev0 = false;
                },
            }
        } else if norm.len() >= maxsv1 {
            return None;
        } else {
            match nc_value_exec(b, q, rem) {
                None => {
                    return None;
                },
                Some((v, q2)) => {
                    let count: i32 = v as i32 - 1;
                    let rem2: u32 = if count >= 0 {
                        rem - count as u32
                    } else {
                        rem - 1
                    };
                    let ghost n0 = norm@;
                    norm.push(count as i16);
                    proof {
                        assert(iseq(norm@) =~= iseq(n0).push(count as int));
                        assert forall|i: int| 0 <= i < norm@.len() implies -1 <= #[trigger] norm@[i]
                            <= pow2(log as nat) by {
                            if i < n0.len() {
                                assert(norm@[i] == n0[i]);
                            }
                        }
                    }
                    if rem2 <= 1 {
                        if rem2 == 1 {
                            return Some((log, norm, (q2 + 7) / 8));
                        } else {
                            proof {
                                assert(cur is None);
                            }
                            return None;
                        }
                    }
                    if norm.len() >= maxsv1 {
                        proof {
                            assert(cur is None);
                        }
                        return None;
                    }
                    q = q2;
                    rem = rem2;
                    prev0 = count == 0;
                },
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Decoding tables
// ---------------------------------------------------------------------------

/// A table row: symbol, bits to read, base of the next state.
#[derive(Clone, Copy)]
pub struct FseRow {
    pub sym: u8,
    pub nb: u8,
    pub base: u16,
}

pub struct FseTab {
    pub log: u32,
    pub rows: Vec<FseRow>,
}

/// `t` is the spec's table `s`.
pub open spec fn tab_is(t: &FseTab, s: FseTable) -> bool {
    &&& t.log as nat == s.log
    &&& t.rows@.len() == s.rows.len()
    &&& forall|u: int|
        #![trigger t.rows@[u]]
        0 <= u < s.rows.len() ==> {
            &&& t.rows@[u].sym as nat == s.rows[u].sym
            &&& t.rows@[u].nb as nat == s.rows[u].nb
            &&& t.rows@[u].base as nat == s.rows[u].base
        }
}

/// Well-formed: `2^log` rows, each row's next states inside the table, and
/// symbols below `nsym`.
pub open spec fn tab_wf(t: &FseTab, nsym: nat) -> bool {
    &&& t.log <= 9
    &&& t.rows@.len() == pow2(t.log as nat)
    &&& forall|u: int|
        #![trigger t.rows@[u]]
        0 <= u < t.rows@.len() ==> {
            &&& t.rows@[u].base as nat + pow2(t.rows@[u].nb as nat) <= pow2(t.log as nat)
            &&& t.rows@[u].nb <= t.log
            &&& (t.rows@[u].sym as nat) < nsym
        }
}

impl FseTab {
    pub fn clone_tab(&self, Tracked(m): Tracked<&mut Meter>) -> (r: FseTab)
        ensures
            r.log == self.log,
            r.rows@ == self.rows@,
            final(m).n == old(m).n + self.rows@.len(),
    {
        proof {
            m.n = m.n + self.rows@.len();
        }
        FseTab { log: self.log, rows: self.rows.clone() }
    }
}

/// `occ` counts at most `u` rows.
proof fn lemma_occ_le(tab: Seq<nat>, s: nat, u: int)
    requires
        u >= 0,
    ensures
        occ(tab, s, u) <= u,
    decreases u,
{
    if u > 0 {
        lemma_occ_le(tab, s, u - 1);
    }
}

/// `occ` one row further.
proof fn lemma_occ_step(tab: Seq<nat>, s: nat, u: int)
    requires
        u >= 0,
    ensures
        occ(tab, s, u + 1) == occ(tab, s, u) + if tab[u] == s {
            1nat
        } else {
            0nat
        },
{
}

/// `lowprob_count` one symbol further.
proof fn lemma_lowprob_step(norm: Seq<int>, s: int)
    requires
        s >= 0,
    ensures
        lowprob_count(norm, s + 1) == lowprob_count(norm, s) + if norm[s] == -1 {
            1nat
        } else {
            0nat
        },
{
}

proof fn lemma_lowprob_le(norm: Seq<int>, s: int)
    requires
        s >= 0,
    ensures
        lowprob_count(norm, s) <= s,
    decreases s,
{
    if s > 0 {
        lemma_lowprob_le(norm, s - 1);
    }
}

// ---------------------------------------------------------------------------
// Work: a distribution fills the table exactly, and the spread visits each
// row at most once
// ---------------------------------------------------------------------------

/// The points one probability takes: its value, and 1 for "less than 1".
pub open spec fn pw(x: int) -> int {
    if x >= 0 {
        x
    } else {
        1
    }
}

/// The points the first `s` probabilities take.
pub open spec fn psum(v: Seq<int>, s: int) -> int
    decreases s,
{
    if s <= 0 {
        0
    } else {
        psum(v, s - 1) + pw(v[s - 1])
    }
}

/// The rows the first `s` probabilities of at least one take.
pub open spec fn spos(v: Seq<int>, s: int) -> int
    decreases s,
{
    if s <= 0 {
        0
    } else {
        spos(v, s - 1) + if v[s - 1] >= 1 {
            v[s - 1]
        } else {
            0
        }
    }
}

proof fn lemma_psum_ext(v: Seq<int>, w: Seq<int>, j: int)
    requires
        j <= v.len(),
        j <= w.len(),
        forall|i: int| 0 <= i < j ==> v[i] == w[i],
    ensures
        psum(v, j) == psum(w, j),
    decreases j,
{
    if j > 0 {
        lemma_psum_ext(v, w, j - 1);
    }
}

proof fn lemma_psum_push(v: Seq<int>, x: int)
    ensures
        psum(v.push(x), v.len() + 1int) == psum(v, v.len() as int) + pw(x),
{
    lemma_psum_ext(v, v.push(x), v.len() as int);
}

proof fn lemma_psum_zeros(v: Seq<int>, z: nat, t: nat)
    requires
        t <= z,
    ensures
        psum(v + Seq::new(z, |i: int| 0int), (v.len() + t) as int) == psum(v, v.len() as int),
    decreases t,
{
    let w = v + Seq::new(z, |i: int| 0int);
    if t == 0 {
        lemma_psum_ext(v, w, v.len() as int);
    } else {
        lemma_psum_zeros(v, z, (t - 1) as nat);
        assert(w[v.len() + t - 1] == 0);
    }
}

/// A distribution read takes exactly the points it was given.
proof fn lemma_nc_run_psum(b: Seq<u8>, q: int, norm: Seq<int>, rem: int, prev0: bool, maxsv1: nat)
    requires
        nc_run(b, q, norm, rem, prev0, maxsv1) is Some,
    ensures
        ({
            let r = nc_run(b, q, norm, rem, prev0, maxsv1).unwrap().0;
            psum(r, r.len() as int) == psum(norm, norm.len() as int) + rem - 1
        }),
    decreases maxsv1 - norm.len(), if prev0 {
        1int
    } else {
        0int
    },
{
    if norm.len() > maxsv1 || rem < 2 {
    } else if prev0 {
        let (q2, z) = nc_zeros(b, q, 0).unwrap();
        let norm2 = norm + Seq::new(z, |i: int| 0int);
        lemma_psum_zeros(norm, z, z);
        lemma_nc_run_psum(b, q2, norm2, rem, false, maxsv1);
    } else {
        let (v, q2) = nc_value(b, q, rem).unwrap();
        let count = v - 1;
        let rem2 = if count >= 0 {
            rem - count
        } else {
            rem - 1
        };
        let norm2 = norm.push(count);
        lemma_psum_push(norm, count);
        if rem2 > 1 {
            lemma_nc_run_psum(b, q2, norm2, rem2, count == 0, maxsv1);
        }
    }
}

/// With probabilities from -1 up, the points are the rows of probabilities
/// of at least one and one per "less than 1".
proof fn lemma_psum_split(v: Seq<int>, s: int)
    requires
        0 <= s <= v.len(),
        forall|i: int| 0 <= i < s ==> -1 <= #[trigger] v[i],
    ensures
        psum(v, s) == spos(v, s) + lowprob_count(v, s),
        spos(v, s) >= 0,
    decreases s,
{
    if s > 0 {
        lemma_psum_split(v, s - 1);
    }
}

proof fn lemma_spos_mono(v: Seq<int>, s: int, t: int)
    requires
        0 <= s <= t <= v.len(),
    ensures
        spos(v, s) <= spos(v, t),
    decreases t - s,
{
    if s < t {
        lemma_spos_mono(v, s, t - 1);
    }
}

/// Position `k` of the spread walk: `k` steps on from row 0.
pub open spec fn walk(size: nat, k: int) -> int {
    (k * fse_step(size)) % (size as int)
}

/// How many of the positions `1..=k` of the walk are rows at most `high`.
pub open spec fn nfree(size: nat, high: int, k: int) -> nat
    decreases k,
{
    if k <= 0 {
        0
    } else {
        nfree(size, high, k - 1) + if walk(size, k) <= high {
            1nat
        } else {
            0nat
        }
    }
}

/// The rows above `high` that the positions `1..=k` of the walk land on.
pub open spec fn skipped(size: nat, high: int, k: int) -> Set<int>
    decreases k,
{
    if k <= 0 {
        Set::empty()
    } else {
        let s = skipped(size, high, k - 1);
        if walk(size, k) > high {
            s.insert(walk(size, k))
        } else {
            s
        }
    }
}

/// The step is odd and below the size.
proof fn lemma_step(log: nat)
    requires
        5 <= log <= 9,
    ensures
        fse_step(pow2(log)) % 2 == 1,
        fse_step(pow2(log)) < pow2(log),
{
    let size = pow2(log);
    lemma_pow2_adds(4, (log - 4) as nat);
    let q = pow2((log - 4) as nat);
    assert(pow2(4) == 16) by {
        lemma2_to64();
    }
    assert(size == 16 * q);
    lemma_pow2_le(1, (log - 4) as nat);
    assert(pow2(1) == 2) by {
        lemma2_to64();
    }
    assert(size / 2 == 8 * q) by {
        lemma_div_multiples_vanish(8 * q as int, 2);
    }
    assert(size / 8 == 2 * q) by {
        lemma_div_multiples_vanish(2 * q as int, 8);
    }
    assert((10 * q + 3) % 2 == 1) by {
        lemma_fundamental_div_mod_converse((10 * q + 3) as int, 2, (5 * q + 1) as int, 1);
    }
}

proof fn lemma_walk_next(log: nat, k: int)
    requires
        5 <= log <= 9,
        k >= 0,
    ensures
        walk(pow2(log), k + 1) == (walk(pow2(log), k) + fse_step(pow2(log))) % (pow2(log) as int),
        0 <= walk(pow2(log), k) < pow2(log),
{
    let size = pow2(log) as int;
    let st = fse_step(pow2(log)) as int;
    lemma_step(log);
    lemma_pow2_pos(log);
    lemma_small_mod(st as nat, size as nat);
    lemma_add_mod_noop(k * st, st, size);
    lemma_mul_is_distributive_add_other_way(st, k, 1);
    lemma_mod_pos_bound(k * st, size);
    lemma_mul_nonnegative(k, st);
}

/// An odd number times `d` is a multiple of `2^l` only if `d` is.
proof fn lemma_odd_mul_pow2(d: int, st: int, l: nat)
    requires
        0 < d < pow2(l),
        st % 2 == 1,
        st > 0,
    ensures
        (d * st) % (pow2(l) as int) != 0,
    decreases l,
{
    if l == 0 {
        assert(pow2(0) == 1) by {
            lemma2_to64();
        }
    } else {
        lemma_pow2_unfold(l);
        let h = pow2((l - 1) as nat) as int;
        lemma_pow2_pos((l - 1) as nat);
        if d % 2 == 1 {
            lemma_mul_mod_noop(d, st, 2);
            assert((d * st) % 2 == 1) by {
                assert((1int * 1int) % 2 == 1);
            }
            lemma_mod_mod(d * st, 2, h);
            if (d * st) % (2 * h) == 0 {
                assert(0int % 2 == 0);
            }
        } else {
            let d2 = d / 2;
            lemma_fundamental_div_mod(d, 2);
            assert(d == 2 * d2);
            assert(0 < d2 < h);
            lemma_odd_mul_pow2(d2, st, (l - 1) as nat);
            let x = d2 * st;
            lemma_fundamental_div_mod(x, h);
            let r = x % h;
            lemma_mod_pos_bound(x, h);
            let qq = x / h;
            assert(d * st == 2 * x) by {
                lemma_mul_is_associative(2, d2, st);
            }
            assert(2 * x == qq * (2 * h) + 2 * r) by {
                lemma_mul_is_associative(qq, 2, h);
                lemma_mul_is_commutative(qq, 2);
                lemma_mul_is_associative(2, qq, h);
            }
            lemma_fundamental_div_mod_converse(2 * x, 2 * h, qq, 2 * r);
        }
    }
}

/// The walk does not come back to a row within `size` steps.
proof fn lemma_walk_inj(log: nat, a: int, b: int)
    requires
        5 <= log <= 9,
        0 <= a < b,
        b - a < pow2(log),
    ensures
        walk(pow2(log), a) != walk(pow2(log), b),
{
    let size = pow2(log) as int;
    let st = fse_step(pow2(log)) as int;
    lemma_step(log);
    lemma_pow2_pos(log);
    lemma_sub_mod_noop(b * st, a * st, size);
    lemma_mul_is_distributive_sub_other_way(st, b, a);
    lemma_odd_mul_pow2(b - a, st, log);
    if walk(pow2(log), a) == walk(pow2(log), b) {
        assert(0int % size == 0);
    }
}

/// Every `size` steps the walk is back at row 0.
proof fn lemma_walk_zero(log: nat, q: int)
    requires
        5 <= log <= 9,
        q >= 0,
    ensures
        walk(pow2(log), q * pow2(log)) == 0,
{
    let size = pow2(log) as int;
    let st = fse_step(pow2(log)) as int;
    lemma_pow2_pos(log);
    lemma_mul_is_associative(q, size, st);
    lemma_mul_is_commutative(size, st);
    lemma_mul_is_associative(q, st, size);
    lemma_mod_multiples_basic(q * st, size);
}

proof fn lemma_skipped_not(size: nat, high: int, k: int, y: int)
    requires
        forall|j: int| 1 <= j <= k ==> walk(size, j) != y,
    ensures
        !skipped(size, high, k).contains(y),
    decreases k,
{
    if k > 0 {
        lemma_skipped_not(size, high, k - 1, y);
    }
}

/// Within the first `size` steps the walk skips each row above `high` at
/// most once.
proof fn lemma_skipped_len(log: nat, high: int, k: int)
    requires
        5 <= log <= 9,
        0 <= k < pow2(log),
    ensures
        skipped(pow2(log), high, k).len() + nfree(pow2(log), high, k) == k,
        forall|x: int| #[trigger] skipped(pow2(log), high, k).contains(x) ==> high < x < pow2(log),
    decreases k,
{
    let size = pow2(log);
    if k > 0 {
        lemma_skipped_len(log, high, k - 1);
        lemma_walk_next(log, k);
        if walk(size, k) > high {
            assert forall|j: int| 1 <= j <= k - 1 implies walk(size, j) != walk(size, k) by {
                lemma_walk_inj(log, j, k);
            }
            lemma_skipped_not(size, high, k - 1, walk(size, k));
        }
    }
}

proof fn lemma_nfree_mono(size: nat, high: int, a: int, b: int)
    requires
        a <= b,
    ensures
        nfree(size, high, a) <= nfree(size, high, b),
    decreases b - a,
{
    if a < b {
        lemma_nfree_mono(size, high, a, b - 1);
    }
}

/// After `size` steps the walk has passed every row at most `high`.
proof fn lemma_nfree_full(log: nat, high: int, k: int)
    requires
        5 <= log <= 9,
        0 <= high < pow2(log),
        k >= pow2(log),
    ensures
        nfree(pow2(log), high, k) >= high + 1,
{
    let size = pow2(log);
    lemma_pow2_pos(log);
    lemma_skipped_len(log, high, size - 1);
    let sk = skipped(size, high, size - 1);
    lemma_int_range(high + 1, size as int);
    assert(sk.subset_of(set_int_range(high + 1, size as int)));
    lemma_len_subset(sk, set_int_range(high + 1, size as int));
    lemma_walk_zero(log, 1);
    assert(1 * size == size);
    assert(nfree(size, high, size as int) == nfree(size, high, size - 1) + 1);
    lemma_nfree_mono(size, high, size as int, k);
}

/// A run of skipped rows and then one at most `high` adds one row.
proof fn lemma_nfree_run(size: nat, high: int, k: int, t: int)
    requires
        k >= 0,
        t >= 1,
        walk(size, k + t) <= high,
        forall|j: int| k < j < k + t ==> walk(size, j) > high,
    ensures
        nfree(size, high, k + t) == nfree(size, high, k) + 1,
{
    lemma_nfree_skip(size, high, k, t - 1);
}

proof fn lemma_nfree_skip(size: nat, high: int, k: int, t: int)
    requires
        k >= 0,
        t >= 0,
        forall|j: int| k < j <= k + t ==> walk(size, j) > high,
    ensures
        nfree(size, high, k + t) == nfree(size, high, k),
    decreases t,
{
    if t > 0 {
        lemma_nfree_skip(size, high, k, t - 1);
    }
}

/// The next position in the spread order (`next_pos`).
#[inline(always)]
fn next_pos_exec(
    pos: u32,
    size: u32,
    mask: u32,
    step: u32,
    high: i32,
    Ghost(lg): Ghost<nat>,
    Ghost(k): Ghost<int>,
    Tracked(m): Tracked<&mut Meter>,
) -> (r: (u32, Ghost<int>))
    requires
        pos < size <= 512,
        5 <= lg <= 9,
        size as nat == pow2(lg),
        mask as nat == low_bits_mask(lg),
        step == fse_step(size as nat),
        k >= 0,
        pos == walk(size as nat, k),
        0 <= high,
    ensures
        r.0 as nat == next_pos(pos as nat, size as nat, high as int, size as nat),
        r.0 < size,
        // The walk moves on `t` positions, all but the last above `high`.
        r.1@ >= 1,
        r.0 == walk(size as nat, k + r.1@),
        r.0 <= high,
        forall|j: int| k < j < k + r.1@ ==> walk(size as nat, j) > high,
        final(m).n == old(m).n + r.1@,
{
    let mut cur = pos;
    let mut fuel = size;
    let ghost mut kk: int = k;
    let ghost top: int = (k / (size as int) + 1) * (size as int);
    proof {
        lemma_fundamental_div_mod(k, size as int);
        lemma_mod_pos_bound(k, size as int);
        lemma_mul_is_distributive_add_other_way(size as int, k / (size as int), 1);
        lemma_mul_is_commutative(size as int, k / (size as int));
        lemma_div_pos_is_pos(k, size as int);
        lemma_walk_zero(lg, k / (size as int) + 1);
    }
    loop
        invariant
            cur < size <= 512,
            step == fse_step(size as nat),
            5 <= lg <= 9,
            size as nat == pow2(lg),
            mask as nat == low_bits_mask(lg),
            fuel <= size,
            next_pos(cur as nat, size as nat, high as int, fuel as nat) == next_pos(
                pos as nat,
                size as nat,
                high as int,
                size as nat,
            ),
            0 <= high,
            k >= 0,
            k <= kk < top,
            top <= k + size,
            walk(size as nat, top) == 0,
            cur == walk(size as nat, kk),
            fuel == size - (kk - k),
            forall|j: int| k < j <= kk ==> walk(size as nat, j) > high,
            m.n == old(m).n + (kk - k),
        decreases fuel,
    {
        proof {
            lemma_u32_low_bits_mask_is_mod((cur + step) as u32, lg);
            lemma_walk_next(lg, kk);
            m.n = m.n + 1;
        }
        let p = (cur + step) & mask;
        if (p as i32) > high && fuel > 0 {
            cur = p;
            fuel = fuel - 1;
            proof {
                kk = kk + 1;
            }
        } else {
            return (p, Ghost(kk + 1 - k));
        }
    }
}

/// Builds the decoding table of a distribution (`fse_table`).
pub fn build_table(norm: &[i16], log: u32, Tracked(m): Tracked<&mut Meter>) -> (r: FseTab)
    requires
        5 <= log <= 9,
        1 <= norm@.len() <= 256,
        norm_ok(norm@, log as nat),
        psum(iseq(norm@), norm@.len() as int) == pow2(log as nat),
    ensures
        tab_is(&r, fse_table(iseq(norm@), log as nat)),
        tab_wf(&r, norm@.len()),
        final(m).n <= old(m).n + 3 * norm@.len() + 3 * pow2(log as nat),
{
    let ghost nm = iseq(norm@);
    proof {
        lemma_u32_pow2_no_overflow(log as nat);
        lemma_u32_shl_is_mul(1, log);
        lemma_pow2_le(log as nat, 9);
        lemma_pow2_le(5, log as nat);
        assert(pow2(9) == 512 && pow2(5) == 32) by {
            lemma2_to64();
        }
    }
    let size: u32 = 1u32 << log;
    let n = norm.len();
    let ghost gsize = size as nat;
    // Symbols with probability "less than 1" take the last rows.
    let tab: Vec<u8> = vec![0u8; size as usize];
    let mut tab = tab;
    proof {
        assert forall|i: int| 0 <= i < size implies tab@[i] == 0 by {
            assert(cloned::<u8>(0u8, tab@[i]));
        }
    }
    let ghost tab0 = Seq::new(gsize, |i: int| 0nat);
    let ghost low_full = place_lowprob(nm, gsize, 0, tab0);
    proof {
        assert(tab@.map_values(|x: u8| x as nat) =~= tab0);
    }
    let mut nlow: u32 = 0;
    let mut s: usize = 0;
    while s < n
        invariant
            s <= n,
            n == norm@.len(),
            n <= 256,
            nm == iseq(norm@),
            gsize == size,
            size <= 512,
            tab@.len() == size,
            nlow as nat == lowprob_count(nm, s as int),
            nlow <= s,
            forall|i: int| 0 <= i < size ==> (#[trigger] tab@[i] as nat) < n,
            place_lowprob(nm, gsize, s as int, tab@.map_values(|x: u8| x as nat)) == low_full,
            low_full == place_lowprob(nm, gsize, 0, tab0),
            m.n == old(m).n + s,
        decreases n - s,
    {
        proof {
            lemma_lowprob_step(nm, s as int);
            m.n = m.n + 1;
        }
        if norm[s] == -1 {
            if nlow < size {
                let ghost before = tab@.map_values(|x: u8| x as nat);
                tab.set((size - 1 - nlow) as usize, s as u8);
                proof {
                    assert(tab@.map_values(|x: u8| x as nat) =~= before.update(
                        gsize - 1 - lowprob_count(nm, s as int),
                        s as nat,
                    ));
                }
            } else {
                // Not reachable: the "less than 1" rows count against the
                // table's size. The spec's update is out of range there,
                // which leaves the table as it is.
                proof {
                    let before = tab@.map_values(|x: u8| x as nat);
                    assert(before.update(gsize - 1 - lowprob_count(nm, s as int), s as nat) =~= before);
                }
            }
            nlow = nlow + 1;
        }
        s = s + 1;
    }
    // Spread the other symbols. The walk visits each row at most once
    // (`lemma_nfree_full`), so its steps are at most the table's size.
    let step: u32 = size / 2 + size / 8 + 3;
    let high: i32 = size as i32 - 1 - nlow as i32;
    let ghost spread_full = spread(nm, gsize, high as int, 0, 0, 0, low_full);
    let ghost mut k: int = 0;
    let ghost mut pl: int = 0;
    let ghost m0 = m.n;
    proof {
        assert forall|i: int| 0 <= i < n implies -1 <= #[trigger] nm[i] by {
            assert(nm[i] == norm@[i] as int);
        }
        lemma_psum_split(nm, n as int);
        assert(spos(nm, n as int) == high + 1);
        assert(0 * (fse_step(gsize) as int) == 0);
        lemma_small_mod(0, gsize);
        assert(walk(gsize, 0) == 0);
    }
    let mut pos: u32 = 0;
    let mut s: usize = 0;
    while s < n
        invariant
            s <= n,
            n == norm@.len(),
            n <= 256,
            nm == iseq(norm@),
            gsize == size,
            5 <= log <= 9,
            size == pow2(log as nat),
            size <= 512,
            step == fse_step(size as nat),
            pos < size,
            tab@.len() == size,
            nlow == 0 ==> high == size - 1,
            norm_ok(norm@, log as nat),
            forall|i: int| 0 <= i < size ==> (#[trigger] tab@[i] as nat) < n,
            spread(nm, gsize, high as int, s as int, 0, pos as nat, tab@.map_values(|x: u8| x as nat))
                == spread_full,
            spos(nm, n as int) == high + 1,
            k >= 0,
            pos == walk(gsize, k),
            k == 0 || walk(gsize, k) <= high,
            nfree(gsize, high as int, k) == pl,
            pl == spos(nm, s as int),
            m.n <= m0 + s + pl + k,
        decreases n - s,
    {
        let c = norm[s];
        proof {
            m.n = m.n + 1;
            lemma_spos_mono(nm, s as int + 1, n as int);
            assert(nm[s as int] == c as int);
        }
        let mut i: i16 = 0;
        while i < c
            invariant
                s < n,
                n == norm@.len(),
                n <= 256,
                nm == iseq(norm@),
                gsize == size,
                c == norm@[s as int],
                c <= 512,
                0 <= i,
                5 <= log <= 9,
                size == pow2(log as nat),
                step == fse_step(size as nat),
                pos < size,
                size <= 512,
                tab@.len() == size,
                nlow == 0 ==> high == size - 1,
                forall|i: int| 0 <= i < size ==> (#[trigger] tab@[i] as nat) < n,
                spread(nm, gsize, high as int, s as int, i as int, pos as nat, tab@.map_values(|x: u8| x as nat))
                    == spread_full,
                spos(nm, n as int) == high + 1,
                spos(nm, s as int + 1) <= high + 1,
                spos(nm, s as int + 1) == spos(nm, s as int) + if c >= 1 { c as int } else { 0 },
                k >= 0,
                pos == walk(gsize, k),
                k == 0 || walk(gsize, k) <= high,
                nfree(gsize, high as int, k) == pl,
                pl == spos(nm, s as int) + i,
                c >= 0 ==> i <= c,
                c < 0 ==> i == 0,
                m.n <= m0 + s + 1 + pl + k,
            decreases c - i,
        {
            proof {
                m.n = m.n + 1;
                pl = pl + 1;
            }
            let ghost before = tab@.map_values(|x: u8| x as nat);
            tab.set(pos as usize, s as u8);
            proof {
                assert(tab@.map_values(|x: u8| x as nat) =~= before.update(pos as int, s as nat));
            }
            proof {
                assert(low_bits_mask(log as nat) == size - 1);
            }
            if nlow == 0 {
                // No rows are reserved, so no position is skipped.
                proof {
                    lemma_u32_low_bits_mask_is_mod((pos + step) as u32, log as nat);
                    let p = ((pos + step) as nat) % (size as nat);
                    assert(p < size) by {
                        lemma_mod_bound((pos + step) as int, size as int);
                    }
                    assert(next_pos(pos as nat, size as nat, high as int, size as nat) == p);
                    lemma_walk_next(log as nat, k);
                    m.n = m.n + 1;
                }
                pos = (pos + step) & (size - 1);
                proof {
                    k = k + 1;
                    assert(walk(gsize, k) <= high);
                }
            } else {
                let (p2, Ghost(t)) = next_pos_exec(pos, size, size - 1, step, high, Ghost(log as nat), Ghost(k), Tracked(m));
                pos = p2;
                proof {
                    lemma_nfree_run(gsize, high as int, k, t);
                    k = k + t;
                }
            }
            i = i + 1;
        }
        s = s + 1;
    }
    proof {
        // The walk ends within the first `size` steps.
        if k > gsize {
            lemma_walk_next(log as nat, k);
            lemma_nfree_full(log as nat, high as int, k - 1);
        }
        assert(k <= gsize);
    }
    let ghost syms = tab@.map_values(|x: u8| x as nat);
    proof {
        assert(syms == fse_symbols(nm, log as nat));
    }
    // Rows: number each symbol's rows from its count up.
    let mut next: [u32; 256] = [0u32; 256];
    let mut s: usize = 0;
    while s < n
        invariant
            s <= n,
            n == norm@.len(),
            n <= 256,
            nm == iseq(norm@),
            forall|j: int|
                0 <= j < s ==> #[trigger] next@[j] as nat == (if nm[j] >= 1 {
                    nm[j] as nat
                } else {
                    1nat
                }),
            m.n <= m0 + n + 2 * gsize + s,
        decreases n - s,
    {
        proof {
            m.n = m.n + 1;
        }
        let c = norm[s];
        next[s] = if c >= 1 { c as u32 } else { 1 };
        s = s + 1;
    }
    let mut rows: Vec<FseRow> = Vec::with_capacity(size as usize);
    let mut u: u32 = 0;
    let ghost full = fse_table(nm, log as nat);
    while u < size
        invariant
            u <= size,
            n == norm@.len(),
            1 <= n <= 256,
            nm == iseq(norm@),
            gsize == size,
            5 <= log <= 9,
            size == pow2(log as nat),
            size <= 512,
            tab@.len() == size,
            syms == tab@.map_values(|x: u8| x as nat),
            syms == fse_symbols(nm, log as nat),
            full == fse_table(nm, log as nat),
            norm_ok(norm@, log as nat),
            forall|i: int| 0 <= i < size ==> (#[trigger] tab@[i] as nat) < n,
            forall|j: int|
                0 <= j < n ==> #[trigger] next@[j] as nat == (if nm[j] >= 1 {
                    nm[j] as nat
                } else {
                    1nat
                }) + occ(syms, j as nat, u as int),
            rows@.len() == u,
            forall|v: int|
                #![trigger rows@[v]]
                0 <= v < u ==> {
                    &&& rows@[v].sym as nat == full.rows[v].sym
                    &&& rows@[v].nb as nat == full.rows[v].nb
                    &&& rows@[v].base as nat == full.rows[v].base
                    &&& rows@[v].base as nat + pow2(rows@[v].nb as nat) <= pow2(log as nat)
                    &&& rows@[v].nb <= log
                    &&& (rows@[v].sym as nat) < n
                },
            m.n <= m0 + 2 * n + 2 * gsize + u,
        decreases size - u,
    {
        proof {
            m.n = m.n + 1;
        }
        let sym = tab[u as usize];
        let x = next[sym as usize];
        proof {
            let j = sym as int;
            assert(syms[u as int] == sym as nat);
            lemma_occ_le(syms, sym as nat, u as int);
            assert(-1 <= norm@[j] <= pow2(log as nat));
            assert(nm[j] == norm@[j] as int);
            // x = c + occ <= size + (size - 1)
            assert(x as nat <= 2 * size - 1);
            assert(x >= 1);
        }
        let hb0 = highbit_u32(x);
        let hb = if hb0 <= log { hb0 } else { log };
        let nb = log - hb;
        proof {
            lemma_highbit(x as nat);
            lemma_pow2_unfold(log as nat + 1);
            if hb0 > log {
                lemma_pow2_le(log as nat + 1, hb0 as nat);
            }
            assert(hb0 <= log);
            assert(hb == hb0);
            lemma_pow2_adds(hb as nat, nb as nat);
            assert(hb + nb == log);
            lemma_mul_inequality(pow2(hb as nat) as int, x as int, pow2(nb as nat) as int);
            lemma_mul_inequality(x as int + 1, pow2(hb as nat + 1) as int, pow2(nb as nat) as int);
            lemma_pow2_adds(hb as nat + 1, nb as nat);
            lemma_pow2_unfold(hb as nat + 1);
            assert(x * pow2(nb as nat) >= pow2(log as nat));
            assert((x + 1) * pow2(nb as nat) <= 2 * pow2(log as nat)) by {
                lemma_mul_is_distributive_add_other_way(pow2(nb as nat) as int, x as int, 1);
                assert(pow2(hb as nat + 1) * pow2(nb as nat) == pow2(log as nat + 1));
            }
            lemma_mul_is_distributive_add_other_way(pow2(nb as nat) as int, x as int, 1);
            lemma_u32_pow2_no_overflow(nb as nat);
            lemma_u32_shl_is_mul(x, nb);
        }
        let base = (x << nb) - size;
        proof {
            let row = fse_row(nm, log as nat, syms, u as int);
            assert(full.rows[u as int] == row);
            assert(row.sym == sym as nat);
            assert(highbit(x as nat) == hb as nat);
            assert(row.nb == nb as nat);
            assert(row.base == base as nat);
        }
        rows.push(FseRow { sym: sym, nb: nb as u8, base: base as u16 });
        let ghost nx = next@;
        next[sym as usize] = x + 1;
        proof {
            assert forall|j: int| 0 <= j < n implies #[trigger] next@[j] as nat == (if nm[j] >= 1 {
                nm[j] as nat
            } else {
                1nat
            }) + occ(syms, j as nat, u + 1) by {
                lemma_occ_step(syms, j as nat, u as int);
            }
        }
        u = u + 1;
    }
    FseTab { log: log, rows: rows }
}

/// The table of RLE mode.
pub fn rle_tab(sym: u8) -> (r: FseTab)
    ensures
        tab_is(&r, rle_table(sym as nat)),
        tab_wf(&r, sym as nat + 1),
{
    let mut rows = Vec::new();
    rows.push(FseRow { sym: sym, nb: 0, base: 0 });
    proof {
        lemma2_to64();
    }
    FseTab { log: 0, rows: rows }
}

} // verus!
