//! One strip or tile: its data decompressed (`spec::decompress`), made
//! little-endian (`spec::to_le`), and with the predictor undone
//! (`spec::unpredict`).
use crate::lzw::{lzw_exec, SLACK};
#[cfg(verus_only)]
use crate::lzw::STORED;
use crate::packbits::packbits_exec;
use crate::prims::alloc_zeroed;
use crate::spec::*;
use verilith_core::prims::{get, set};
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::mul::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;
use vstd::slice::slice_to_vec;
use verilith_zlib::wrap::{Decompressor, Format as ZFormat};
#[cfg(verus_only)]
use verilith_zlib::spec as z;

verus! {

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
/// Why a file could not be decoded.
pub enum Error {
    /// The file is not a TIFF file that the specification accepts.
    Invalid,
    /// The file uses a feature this decoder does not read (BigTIFF, a
    /// compression scheme other than none, PackBits, LZW and Deflate, the
    /// floating-point predictor, FillOrder 2). The specification rejects
    /// these files too.
    Unsupported,
    /// The image needs more memory than the caller's limit allows.
    TooLarge,
    /// An allocation failed.
    OutOfMemory,
}

/// Decompresses a zlib stream, which must be valid to its end and give
/// exactly `need` bytes.
fn deflate_exec(d: &[u8], need: usize) -> (r: Result<Vec<u8>, Error>)
    ensures
        match r {
            Ok(v) => decompress(DEFLATE, d@, need as nat, 1) == Some(v@),
            Err(Error::Invalid) => decompress(DEFLATE, d@, need as nat, 1) is None,
            Err(Error::Unsupported) => false,
            Err(_) => true,
        },
{
    if need >= usize::MAX {
        return Err(Error::TooLarge);
    }
    // One byte more than the strip: a stream that fills it is too long.
    let mut raw = match alloc_zeroed(need + 1) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    let mut dz = Decompressor::new();
    let res = dz.decompress_into(ZFormat::Zlib, d, raw.as_mut_slice());
    proof {
        reveal(verilith_zlib::wrap::spec_decompress);
    }
    match res {
        Ok((_, m)) => {
            if m != need {
                return Err(Error::Invalid);
            }
            raw.truncate(need);
            proof {
                assert(raw@ =~= raw@.subrange(0, need as int));
            }
            Ok(raw)
        },
        // Longer than the strip.
        Err(_) => Err(Error::Invalid),
    }
}

/// The `need` bytes, in rows of `rb`, the data `d` decompresses to with
/// scheme `comp` (`spec::decompress`). `off` and `len` are scratch space
/// for LZW.
pub fn decompress_exec(comp: u32, d: &[u8], need: usize, rb: usize, off: &mut [u32], len: &mut [u32]) -> (r: Result<Vec<u8>, Error>)
    requires
        compression_ok(comp as nat),
        rb >= 1,
        need % rb == 0,
        old(off)@.len() == STORED,
        old(len)@.len() == STORED,
    ensures
        final(off)@.len() == STORED,
        final(len)@.len() == STORED,
        match r {
            Ok(v) => decompress(comp as nat, d@, need as nat, rb as nat) == Some(v@) && v@.len() == need,
            Err(Error::Invalid) => decompress(comp as nat, d@, need as nat, rb as nat) is None,
            Err(Error::Unsupported) => false,
            Err(_) => true,
        },
{
    if comp == 1 {
        if d.len() != need {
            return Err(Error::Invalid);
        }
        Ok(slice_to_vec(d))
    } else if comp == 32773 {
        let mut out = match alloc_zeroed(need) {
            Some(v) => v,
            None => return Err(Error::OutOfMemory),
        };
        if !packbits_exec(d, out.as_mut_slice(), need, rb) {
            return Err(Error::Invalid);
        }
        proof {
            assert(out@ =~= out@.subrange(0, need as int));
        }
        Ok(out)
    } else if comp == 5 {
        if need > u32::MAX as usize - SLACK {
            return Err(Error::TooLarge);
        }
        let mut out = match alloc_zeroed(need + SLACK) {
            Some(v) => v,
            None => return Err(Error::OutOfMemory),
        };
        if !lzw_exec(d, need, out.as_mut_slice(), off, len) {
            return Err(Error::Invalid);
        }
        out.truncate(need);
        Ok(out)
    } else {
        match deflate_exec(d, need) {
            Ok(v) => Ok(v),
            Err(e) => Err(e),
        }
    }
}

/// Multiples of `k` below `n`, which is one too, are at least `k` below it.
pub proof fn lemma_multiples(g: int, n: int, k: int)
    requires
        k > 0,
        0 <= g < n,
        g % k == 0,
        n % k == 0,
    ensures
        g + k <= n,
{
    lemma_fundamental_div_mod(g, k);
    lemma_fundamental_div_mod(n, k);
    lemma_mul_is_commutative(k, g / k);
    lemma_mul_is_commutative(k, n / k);
    lemma_mul_strict_inequality_converse(g / k, n / k, k);
    lemma_mul_is_distributive_add_other_way(k, g / k, 1);
    lemma_mul_inequality(g / k + 1, n / k, k);
    lemma_mul_is_commutative(k, g / k + 1);
    lemma_mul_is_commutative(k, n / k);
}

/// Reverses the bytes of each `k`-byte sample (`spec::to_le` for a
/// big-endian file).
pub fn swap_exec(v: &mut [u8], k: usize)
    requires
        2 <= k <= 4,
        old(v)@.len() % (k as nat) == 0,
    ensures
        final(v)@ == Seq::new(old(v)@.len(), |i: int| old(v)@[i - i % k as int + (k as int - 1 - i % k as int)]),
{
    let ghost o = v@;
    let ghost want = Seq::new(o.len(), |i: int| o[i - i % k as int + (k as int - 1 - i % k as int)]);
    let n = v.len();
    let mut g: usize = 0;
    while g < n
        invariant
            2 <= k <= 4,
            n == v@.len(),
            n == o.len(),
            n % k == 0,
            g % k == 0,
            g <= n,
            want == Seq::new(o.len(), |i: int| o[i - i % k as int + (k as int - 1 - i % k as int)]),
            forall|i: int| 0 <= i < g ==> #[trigger] v@[i] == want[i],
            forall|i: int| g <= i < n ==> #[trigger] v@[i] == o[i],
        decreases n - g,
    {
        proof {
            lemma_multiples(g as int, n as int, k as int);
        }
        let a = get(v, g);
        let z = get(v, g + k - 1);
        set(v, g, z);
        set(v, g + k - 1, a);
        if k == 4 {
            let b1 = get(v, g + 1);
            let b2 = get(v, g + 2);
            set(v, g + 1, b2);
            set(v, g + 2, b1);
        }
        proof {
            assert forall|i: int| 0 <= i < g + k implies #[trigger] v@[i] == want[i] by {
                if i >= g {
                    lemma_fundamental_div_mod(g as int, k as int);
                    lemma_fundamental_div_mod_converse(i, k as int, g as int / k as int, i - g);
                    assert(i % k as int == i - g);
                }
            }
            lemma_mod_add_multiples_vanish(g as int, k as int);
        }
        g = g + k;
    }
    proof {
        assert(v@ =~= want);
    }
}

} // verus!
