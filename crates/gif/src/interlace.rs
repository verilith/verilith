//! Interlaced images (Appendix E), proven against `spec::deinterlace`.
use crate::prims::alloc_zeroed;
use crate::spec::*;
use verilith_core::prims::copy_in;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

/// `(8a + k) / 8 == a + k / 8`.
proof fn lemma_div8(a: int, k: int)
    requires
        0 <= a,
        0 <= k < 16,
    ensures
        (8 * a + k) / 8 == a + k / 8,
        (8 * a + k) % 8 == k % 8,
{
    lemma_fundamental_div_mod_converse(8 * a + k, 8, a + k / 8, k % 8);
}

/// The four passes hold `h` rows between them.
pub proof fn lemma_pass_rows(h: nat)
    ensures
        (h + 7) / 8 + (h + 3) / 8 + (h + 1) / 4 + h / 2 == h,
{
    let a = (h / 8) as int;
    let b = (h % 8) as int;
    lemma_fundamental_div_mod(h as int, 8);
    assert(h == 8 * a + b);
    lemma_div8(a, b + 7);
    lemma_div8(a, b + 3);
    assert(h + 1 == 4 * (2 * a) + (b + 1));
    lemma_fundamental_div_mod_converse(h + 1int, 4, 2 * a + (b + 1) / 4, (b + 1) % 4);
    assert(h == 2 * (4 * a) + b);
    lemma_fundamental_div_mod_converse(h as int, 2, 4 * a + b / 2, b % 2);
}

/// Where row `y` comes in the data (`spec::interlaced_row`); always a row
/// of the image.
pub fn interlaced_row_exec(h: usize, y: usize) -> (r: usize)
    requires
        y < h <= 65535,
    ensures
        r == interlaced_row(h as nat, y as nat),
        r < h,
{
    proof {
        lemma_pass_rows(h as nat);
        let k = (y / 8) as int;
        lemma_fundamental_div_mod(y as int, 8);
        lemma_fundamental_div_mod(y as int, 4);
        lemma_fundamental_div_mod(y as int, 2);
        lemma_div8(k, 0);
        lemma_div8(k, 8);
        lemma_div8(k, 9);
        lemma_div8(k, 11);
        lemma_div8(k, 12);
        lemma_div8(k, 13);
        lemma_div8(k, 14);
        lemma_div8(k, 15);
    }
    let n1 = (h + 7) / 8;
    let n2 = (h + 3) / 8;
    let n3 = (h + 1) / 4;
    if y % 8 == 0 {
        y / 8
    } else if y % 8 == 4 {
        n1 + y / 8
    } else if y % 4 == 2 {
        n1 + n2 + y / 4
    } else {
        n1 + n2 + n3 + y / 2
    }
}

/// The rows of `px`, an interlaced image, in order, or `None` if the
/// allocation fails.
pub fn deinterlace_exec(px: &[u8], w: usize, h: usize) -> (r: Option<Vec<u8>>)
    requires
        1 <= w <= 65535,
        1 <= h <= 65535,
        px@.len() == w * h,
    ensures
        r matches Some(v) ==> v@ == deinterlace(px@, w as nat, h as nat),
{
    proof {
        lemma_mul_inequality(w as int, 65535, h as int);
        lemma_mul_inequality(h as int, 65535, 65535);
        lemma_mul_is_commutative(w as int, h as int);
    }
    let n = w * h;
    let mut out = match alloc_zeroed(n) {
        Some(v) => v,
        None => return None,
    };
    let ghost want = deinterlace(px@, w as nat, h as nat);
    let mut y: usize = 0;
    while y < h
        invariant
            1 <= w <= 65535,
            y <= h <= 65535,
            n == w * h,
            px@.len() == n,
            out@.len() == n,
            want == deinterlace(px@, w as nat, h as nat),
            forall|i: int| 0 <= i < y * w ==> #[trigger] out@[i] == want[i],
        decreases h - y,
    {
        let s = interlaced_row_exec(h, y);
        proof {
            lemma_mul_inequality(y as int + 1, h as int, w as int);
            lemma_mul_inequality(s as int + 1, h as int, w as int);
            lemma_mul_is_distributive_add_other_way(w as int, y as int, 1);
            lemma_mul_is_distributive_add_other_way(w as int, s as int, 1);
            lemma_mul_is_commutative(w as int, h as int);
        }
        let ghost o = out@;
        copy_in(out.as_mut_slice(), y * w, px, s * w, w);
        proof {
            assert forall|i: int| 0 <= i < (y + 1) * w implies #[trigger] out@[i] == want[i] by {
                if i >= y * w {
                    lemma_fundamental_div_mod_converse(i, w as int, y as int, i - y * w);
                    assert(out@[i] == px@[s * w + (i - y * w)]);
                } else {
                    assert(out@[i] == o[i]);
                }
            }
        }
        y = y + 1;
    }
    proof {
        lemma_mul_is_commutative(w as int, h as int);
        assert(out@ =~= want);
    }
    Some(out)
}

} // verus!
