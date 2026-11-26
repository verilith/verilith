//! String literals (RFC 9204 §4.1.2): framing (`end`) and decoding
//! (`read`), verified against `spec::str_end` and `spec::str_dec`.
use crate::integer::{self, IntE, P2, lemma_pows};
use crate::spec::*;
use verilith_hpack::huffman;
use vstd::prelude::*;

verus! {

pub enum EndE {
    Short,
    Bad,
    Ok(usize),
}

pub open spec fn end_matches(r: EndE, s: EndR) -> bool {
    match (r, s) {
        (EndE::Short, EndR::Short) => true,
        (EndE::Bad, EndR::Bad) => true,
        (EndE::Ok(e), EndR::Ok(se)) => e as int == se,
        _ => false,
    }
}

pub enum StrE {
    Short,
    Bad,
    Ok(usize),
}

/// The H bit.
#[inline(always)]
pub fn hbit_of(c: u8, n: u8) -> (r: bool)
    requires
        2 <= n <= 8,
    ensures
        r == hbit(c, n as nat),
{
    proof {
        lemma_pows();
        assert(P2@[n as int] as nat == p2(n as nat));
        assert(P2@[n - 1] as nat == p2((n - 1) as nat));
    }
    (c as u64) % P2[n as usize] >= P2[(n - 1) as usize]
}

/// Where the `n`-bit prefix string literal at `b[pos]` ends.
#[inline(always)]
pub fn end(b: &[u8], pos: usize, n: u8, limit: u64) -> (r: EndE)
    requires
        2 <= n <= 8,
    ensures
        end_matches(r, str_end(b@, pos as int, n as nat, limit as nat)),
        r matches EndE::Ok(e) ==> pos < e <= b@.len() && e <= pos + 10 + limit,
{
    match integer::decode(b, pos, n - 1) {
        IntE::Short => EndE::Short,
        IntE::Bad => EndE::Bad,
        IntE::Ok(len, e) => {
            if len > limit {
                EndE::Bad
            } else if len > (b.len() - e) as u64 {
                EndE::Short
            } else {
                EndE::Ok(e + len as usize)
            }
        },
    }
}

/// Decodes the `n`-bit prefix string literal at `b[pos]` into `out`
/// (replacing what it held). The second result is the work: the Huffman
/// decoder's or the bytes copied, at most `4 * (end - pos) + 4`.
pub fn read(b: &[u8], pos: usize, n: u8, limit: u64, out: &mut Vec<u8>, t: &[u32]) -> (r: (StrE, Ghost<nat>))
    requires
        2 <= n <= 8,
        huffman::layout_ok(),
        huffman::dtab_ok(t@),
        b@.len() <= 0x1000_0000,
    ensures
        match (r.0, str_dec(b@, pos as int, n as nat, limit as nat)) {
            (StrE::Short, StrR::Short) => true,
            (StrE::Bad, StrR::Bad) => true,
            (StrE::Ok(e), StrR::Ok(s, se)) => e as int == se && final(out)@ == s && pos < e <= b@.len(),
            _ => false,
        },
        r.0 matches StrE::Ok(e) ==> r.1@ <= 4 * (e - pos) + 4 && final(out)@.len() <= 2 * b@.len() + 2,
        r.1@ <= 4 * b@.len() + 4,
{
    match integer::decode(b, pos, n - 1) {
        IntE::Short => (StrE::Short, Ghost(0)),
        IntE::Bad => (StrE::Bad, Ghost(0)),
        IntE::Ok(len, e) => {
            if len > limit {
                return (StrE::Bad, Ghost(0));
            }
            if len > (b.len() - e) as u64 {
                return (StrE::Short, Ghost(0));
            }
            let end = e + len as usize;
            let raw = vstd::slice::slice_subrange(b, e, end);
            proof {
                assert(raw@ == b@.subrange(e as int, end as int));
            }
            if hbit_of(b[pos], n) {
                let (ok, g) = huffman::decode_metered(raw, out, t);
                if ok {
                    (StrE::Ok(end), g)
                } else {
                    (StrE::Bad, g)
                }
            } else {
                out.clear();
                verilith_core::prims::extend(out, raw);
                proof {
                    assert(out@ =~= raw@);
                }
                (StrE::Ok(end), Ghost(len as nat))
            }
        },
    }
}

} // verus!
