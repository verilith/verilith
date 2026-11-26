//! One strip or tile: its data decompressed (`spec::decompress`), made
//! little-endian (`spec::to_le`), and with the predictor undone
//! (`spec::unpredict`).
use crate::lzw::{lzw_exec, SLACK};
#[cfg(verus_only)]
use crate::lzw::STORED;
use crate::packbits::packbits_exec;
use verilith_core::prims::alloc_u8;
use crate::spec::*;
use crate::work::Meter;
#[cfg(verus_only)]
use crate::lzw::lzw_work;
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

/// What setting up a Deflate decoder costs: more than the entries of the
/// fixed-size tables `Decompressor::new` zeroes (about 3,800).
pub open spec fn znew_cost() -> nat {
    4096
}

/// verilith-zlib's `decompress_into` for a zlib stream, with a new
/// decoder, and the steps it counts.
fn zlib_into(d: &[u8], out: &mut [u8]) -> (r: (Result<(usize, usize), verilith_zlib::wrap::Error>, Ghost<nat>))
    ensures
        final(out)@.len() == old(out)@.len(),
        match r.0 {
            Ok((used, n)) => n <= final(out)@.len() && verilith_zlib::wrap::spec_decompress(ZFormat::Zlib, d@) == Some(
                (final(out)@.subrange(0, n as int), used as int),
            ),
            Err(e) => e != verilith_zlib::wrap::Error::InsufficientSpace ==> verilith_zlib::wrap::spec_decompress(ZFormat::Zlib, d@) is None,
        },
        r.0 == Err::<(usize, usize), verilith_zlib::wrap::Error>(verilith_zlib::wrap::Error::InsufficientSpace) ==> (verilith_zlib::wrap::spec_decompress(ZFormat::Zlib, d@) matches Some((o, _)) ==> o.len() >= old(out)@.len()),
        r.1@ <= verilith_zlib::wrap::work_bound(d@.len(), old(out)@.len() as nat),
{
    let mut dz = Decompressor::new();
    let ghost z0 = dz.inf.work@;
    let ghost ol = out@.len();
    let res = dz.decompress_into(ZFormat::Zlib, d, out);
    let ghost z1 = dz.inf.work@;
    assert(z1 <= z0 + verilith_zlib::wrap::work_bound(d@.len(), ol as nat));
    (res, Ghost(if z1 >= z0 { (z1 - z0) as nat } else { 0 }))
}

/// Decompresses a zlib stream, which must be valid to its end and give
/// exactly `need` bytes. Counts the bytes zeroed, the decoder's setup and
/// verilith-zlib's own count of its steps (`wrap::work_bound`).
fn deflate_exec(d: &[u8], need: usize, Tracked(m): Tracked<&mut Meter>) -> (r: Result<Vec<u8>, Error>)
    ensures
        match r {
            Ok(v) => decompress(DEFLATE, d@, need as nat, 1) == Some(v@),
            Err(Error::Invalid) => decompress(DEFLATE, d@, need as nat, 1) is None,
            Err(Error::Unsupported) => false,
            Err(_) => true,
        },
        final(m).n <= old(m).n + need + 1 + znew_cost() + verilith_zlib::wrap::work_bound(d@.len(), need as nat + 1),
{
    if need >= usize::MAX {
        return Err(Error::TooLarge);
    }
    // One byte more than the strip: a stream that fills it is too long.
    let mut raw = match alloc_u8(need + 1) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    proof {
        m.n = (m.n + need + 1) as nat;
    }
    let (res, Ghost(zw)) = zlib_into(d, raw.as_mut_slice());
    proof {
        m.n = (m.n + znew_cost() + zw) as nat;
    }
    proof {
        reveal(verilith_zlib::wrap::spec_decompress);
    }
    match res {
        Ok((_, got)) => {
            if got != need {
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
///
/// Counts its steps: at most `chunk_work(d.len(), need)`.
pub fn decompress_exec(comp: u32, d: &[u8], need: usize, rb: usize, off: &mut [u32], len: &mut [u32], Tracked(m): Tracked<&mut Meter>) -> (r: Result<Vec<u8>, Error>)
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
        final(m).n <= old(m).n + chunk_work(d@.len(), need as nat),
{
    proof {
        lemma_chunk_work(d@.len(), need as nat);
    }
    if comp == 1 {
        if d.len() != need {
            return Err(Error::Invalid);
        }
        proof {
            m.n = (m.n + need) as nat;
        }
        Ok(slice_to_vec(d))
    } else if comp == 32773 {
        let mut out = match alloc_u8(need) {
            Some(v) => v,
            None => return Err(Error::OutOfMemory),
        };
        proof {
            m.n = (m.n + need) as nat;
        }
        if !packbits_exec(d, out.as_mut_slice(), need, rb, Tracked(m)) {
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
        let mut out = match alloc_u8(need + SLACK) {
            Some(v) => v,
            None => return Err(Error::OutOfMemory),
        };
        proof {
            m.n = (m.n + need + SLACK) as nat;
        }
        if !lzw_exec(d, need, out.as_mut_slice(), off, len, Tracked(m)) {
            return Err(Error::Invalid);
        }
        out.truncate(need);
        Ok(out)
    } else {
        match deflate_exec(d, need, Tracked(m)) {
            Ok(v) => Ok(v),
            Err(e) => Err(e),
        }
    }
}

/// The bound on the work of decompressing one strip or tile of `c` bytes
/// that decodes to `s`: Deflate's, the largest.
pub open spec fn chunk_work(c: nat, s: nat) -> nat {
    s + 1 + znew_cost() + verilith_zlib::wrap::work_bound(c, s + 1)
}

/// `chunk_work`, as a number: `9600c + 132s + 36529`.
pub proof fn lemma_chunk_work(c: nat, s: nat)
    ensures
        chunk_work(c, s) == 9600 * c + 132 * s + 36529,
{
    assert(verilith_zlib::inflate::fixed_cost() == 10834);
    assert(verilith_zlib::inflate::bit_cost() == 1200);
    assert(verilith_zlib::inflate::header_cost() == 21207);
    assert(verilith_zlib::inflate::body_cost() == 130);
    assert(verilith_zlib::wrap::work_bound(c, s + 1) == 10834 + 1200 * 8 * c + 131 * (s + 1) + 21207 + 2 * 130);
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
/// big-endian file). Counts a step a sample.
pub fn swap_exec(v: &mut [u8], k: usize, Tracked(m): Tracked<&mut Meter>)
    requires
        2 <= k <= 4,
        old(v)@.len() % (k as nat) == 0,
    ensures
        final(m).n <= old(m).n + old(v)@.len(),
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
            m.n <= old(m).n + g,
        decreases n - g,
    {
        proof {
            lemma_multiples(g as int, n as int, k as int);
            m.n = m.n + 1;
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
