//! PackBits (§9), proven to compute `spec::packbits`.
use crate::spec::*;
use crate::work::Meter;
use verilith_core::prims::{copy_in, get, set};
use vstd::prelude::*;

verus! {

/// Writes `n` copies of `v` at `out[pos..]`.
fn fill(out: &mut [u8], pos: usize, n: usize, v: u8, Tracked(m): Tracked<&mut Meter>)
    requires
        pos + n <= old(out)@.len(),
    ensures
        final(m).n == old(m).n + n,
        final(out)@ == old(out)@.subrange(0, pos as int) + Seq::new(n as nat, |k: int| v) + old(
            out,
        )@.subrange(pos + n, old(out)@.len() as int),
{
    let ghost o = out@;
    let ln = out.len();
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            ln == out@.len(),
            pos + n <= o.len(),
            out@.len() == o.len(),
            forall|j: int| 0 <= j < pos ==> #[trigger] out@[j] == o[j],
            forall|j: int| pos <= j < pos + k ==> #[trigger] out@[j] == v,
            forall|j: int| pos + n <= j < o.len() ==> #[trigger] out@[j] == o[j],
            m.n == old(m).n + k,
        decreases n - k,
    {
        proof {
            m.n = m.n + 1;
        }
        set(out, pos + k, v);
        k = k + 1;
    }
    assert(out@ =~= o.subrange(0, pos as int) + Seq::new(n as nat, |k: int| v) + o.subrange(pos + n, o.len() as int));
}

/// Decodes the PackBits data `d`, in rows of `rb` bytes, into
/// `out[..need]`. Returns whether `spec::packbits` accepts it. Counts a
/// step for each byte of `d` read and each byte written: at most
/// `d.len() + need`.
pub fn packbits_exec(d: &[u8], out: &mut [u8], need: usize, rb: usize, Tracked(m): Tracked<&mut Meter>) -> (r: bool)
    requires
        need <= old(out)@.len(),
        rb >= 1,
        need % rb == 0,
    ensures
        final(m).n <= old(m).n + d@.len() + need,
        final(out)@.len() == old(out)@.len(),
        r == packbits(d@, 0, Seq::empty(), need as nat, rb as nat) is Some,
        r ==> packbits(d@, 0, Seq::empty(), need as nat, rb as nat) == Some(final(out)@.subrange(0, need as int)),
{
    let ghost want = packbits(d@, 0, Seq::empty(), need as nat, rb as nat);
    let mut i: usize = 0;
    let mut pos: usize = 0;
    proof {
        assert(out@.subrange(0, 0) =~= Seq::<u8>::empty());
    }
    while pos < need
        invariant
            i <= d@.len(),
            pos <= need <= out@.len(),
            rb >= 1,
            need % rb == 0,
            out@.len() == old(out)@.len(),
            want == packbits(d@, 0, Seq::empty(), need as nat, rb as nat),
            want == packbits(d@, i as int, out@.subrange(0, pos as int), need as nat, rb as nat),
            m.n <= old(m).n + i + pos,
        decreases d@.len() - i,
    {
        if i >= d.len() || rb == 0 {
            assert(packbits(d@, i as int, out@.subrange(0, pos as int), need as nat, rb as nat) is None);
            return false;
        }
        let h = get(d, i);
        let ghost o = out@;
        proof {
            m.n = m.n + 1;
        }
        let room = rb - pos % rb;
        proof {
            // The end of this row is at most `need`.
            let g = pos - pos % rb;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(pos as int, rb as int);
            vstd::arithmetic::div_mod::lemma_mod_multiples_basic((pos / rb) as int, rb as int);
            vstd::arithmetic::mul::lemma_mul_is_commutative((pos / rb) as int, rb as int);
            crate::chunk::lemma_multiples(g as int, need as int, rb as int);
            assert(pos + room <= need);
        }
        if h == 128 {
            i = i + 1;
        } else if h > 128 {
            let r = (257 - h as usize) as usize;
            if r > room || d.len() - i <= 1 {
                assert(packbits(d@, i as int, out@.subrange(0, pos as int), need as nat, rb as nat) is None);
                return false;
            }
            let v = get(d, i + 1);
            fill(out, pos, r, v, Tracked(m));
            proof {
                assert(out@.subrange(0, pos + r) =~= o.subrange(0, pos as int) + Seq::new(r as nat, |k: int| d@[i + 1]));
            }
            i = i + 2;
            pos = pos + r;
        } else {
            let l = h as usize + 1;
            if l > room || d.len() - i - 1 < l {
                assert(packbits(d@, i as int, out@.subrange(0, pos as int), need as nat, rb as nat) is None);
                return false;
            }
            copy_in(out, pos, d, i + 1, l);
            proof {
                m.n = (m.n + l) as nat;
            }
            proof {
                assert(out@.subrange(0, pos + l) =~= o.subrange(0, pos as int) + d@.subrange(i + 1, i + 1 + l));
            }
            i = i + 1 + l;
            pos = pos + l;
        }
    }
    true
}

} // verus!
