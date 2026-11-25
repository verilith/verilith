//! FSE table descriptions and decoding tables (RFC 8878 §4.1).
#[allow(unused_imports)]
use crate::spec::*;
use crate::bits::*;
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
fn nc_zeros_exec(b: &[u8], q0: usize) -> (r: Option<(usize, usize)>)
    requires
        q0 <= 8 * b@.len(),
        b@.len() < BITS_MAX,
    ensures
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
        decreases 8 * b@.len() - q,
    {
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
pub fn read_ncount(b: &[u8], maxsv: u32, maxlog: u32) -> (r: Option<(u32, Vec<i16>, usize)>)
    requires
        maxsv <= 255,
        maxlog <= 9,
        b@.len() < BITS_MAX,
    ensures
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
        decreases maxsv1 - norm@.len(), if prev0 {
            1int
        } else {
            0int
        },
    {
        let ghost cur = nc_run(b@, q as int, iseq(norm@), rem as int, prev0, maxsv1 as nat);
        if norm.len() > maxsv1 || rem < 2 {
            proof {
                assert(cur is None);
            }
            return None;
        }
        if prev0 {
            match nc_zeros_exec(b, q) {
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
                    let mut k: usize = 0;
                    while k < z
                        invariant
                            k <= z,
                            norm@.len() == n0.len() + k,
                            norm@ == n0 + Seq::new(k as nat, |i: int| 0i16),
                        decreases z - k,
                    {
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
    pub fn clone_tab(&self) -> (r: FseTab)
        ensures
            r.log == self.log,
            r.rows@ == self.rows@,
    {
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

/// The next position in the spread order (`next_pos`).
#[inline(always)]
fn next_pos_exec(pos: u32, size: u32, mask: u32, step: u32, high: i32, Ghost(lg): Ghost<nat>) -> (r: u32)
    requires
        pos < size <= 512,
        lg < 32,
        size as nat == pow2(lg),
        mask as nat == low_bits_mask(lg),
        step == fse_step(size as nat),
    ensures
        r as nat == next_pos(pos as nat, size as nat, high as int, size as nat),
        r < size,
{
    let mut cur = pos;
    let mut fuel = size;
    loop
        invariant
            cur < size <= 512,
            step == fse_step(size as nat),
            lg < 32,
            size as nat == pow2(lg),
            mask as nat == low_bits_mask(lg),
            fuel <= size,
            next_pos(cur as nat, size as nat, high as int, fuel as nat) == next_pos(
                pos as nat,
                size as nat,
                high as int,
                size as nat,
            ),
        decreases fuel,
    {
        proof {
            lemma_u32_low_bits_mask_is_mod((cur + step) as u32, lg);
        }
        let p = (cur + step) & mask;
        if (p as i32) > high && fuel > 0 {
            cur = p;
            fuel = fuel - 1;
        } else {
            return p;
        }
    }
}

/// Builds the decoding table of a distribution (`fse_table`).
pub fn build_table(norm: &[i16], log: u32) -> (r: FseTab)
    requires
        5 <= log <= 9,
        1 <= norm@.len() <= 256,
        norm_ok(norm@, log as nat),
    ensures
        tab_is(&r, fse_table(iseq(norm@), log as nat)),
        tab_wf(&r, norm@.len()),
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
        decreases n - s,
    {
        proof {
            lemma_lowprob_step(nm, s as int);
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
    // Spread the other symbols.
    let step: u32 = size / 2 + size / 8 + 3;
    let high: i32 = size as i32 - 1 - nlow as i32;
    let ghost spread_full = spread(nm, gsize, high as int, 0, 0, 0, low_full);
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
        decreases n - s,
    {
        let c = norm[s];
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
            decreases c - i,
        {
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
                }
                pos = (pos + step) & (size - 1);
            } else {
                pos = next_pos_exec(pos, size, size - 1, step, high, Ghost(log as nat));
            }
            i = i + 1;
        }
        s = s + 1;
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
        decreases n - s,
    {
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
        decreases size - u,
    {
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
