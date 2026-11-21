//! Verified DER primitives: reading a TLV, and checking INTEGER, OID,
//! BOOLEAN and BIT STRING contents. Each function is proven to compute
//! exactly its counterpart in `spec`.
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// `s[i]` without rustc's bounds check: Verus proves `i < s.len()` at every
/// call, which is the check rustc would repeat. Verified against vstd's
/// spec of `get_unchecked`.
#[inline(always)]
pub fn at(s: &[u8], i: usize) -> (b: u8)
    requires
        i < s@.len(),
    ensures
        b == s@[i as int],
{
    unsafe { *s.get_unchecked(i) }
}

/// `&s[i..j]` without rustc's bounds check, proven in range as `at`.
#[inline(always)]
pub fn subslice<'a>(s: &'a [u8], i: usize, j: usize) -> (out: &'a [u8])
    requires
        i <= j <= s@.len(),
    ensures
        out@ == s@.subrange(i as int, j as int),
{
    unsafe { s.get_unchecked(i..j) }
}


/// One TLV, borrowed from the input.
#[derive(Clone, Copy)]
pub struct Tlv<'a> {
    /// The identifier octets.
    pub tag: &'a [u8],
    /// The contents octets.
    pub content: &'a [u8],
}

impl<'a> View for Tlv<'a> {
    type V = SpecTlv;

    open spec fn view(&self) -> SpecTlv {
        SpecTlv { tag: self.tag@, content: self.content@ }
    }
}

pub proof fn lemma_high_tag_end_bounds(s: Seq<u8>, i: int, k: nat)
    ensures
        high_tag_end(s, i, k) matches Some(e) ==> i < e <= s.len(),
    decreases k,
{
    if k > 0 && 0 <= i < s.len() && s[i] >= 128 {
        lemma_high_tag_end_bounds(s, i + 1, (k - 1) as nat);
    }
}

pub proof fn lemma_tag_len_bounds(s: Seq<u8>)
    ensures
        tag_len(s) matches Some(h) ==> 1 <= h <= s.len() && (h == 1 <==> s[0] % 32 != 31),
{
    if s.len() >= 2 && s[0] % 32 == 31 {
        lemma_high_tag_end_bounds(s, 1, MAX_TAG_CONT);
    }
}

/// A TLV's header is at least two octets, so the rest is strictly shorter.
pub proof fn lemma_tlv_shrinks(s: Seq<u8>)
    ensures
        parse_tlv(s) matches Some((x, r)) ==> r.len() + 2 <= s.len() && x.content.len() + 2
            <= s.len() - r.len(),
{
    lemma_tag_len_bounds(s);
}

/// The number of identifier octets at the start of `s`.
#[inline(always)]
pub fn read_tag_len(s: &[u8]) -> (r: Option<usize>)
    ensures
        r matches Some(h) ==> tag_len(s@) == Some(h as int),
        r is None ==> tag_len(s@) is None,
{
    if s.len() == 0 {
        return None;
    }
    if at(s, 0) % 32 != 31 {
        return Some(1);
    }
    if s.len() < 2 || at(s, 1) == 0x80 || at(s, 1) < 31 {
        return None;
    }
    let mut i: usize = 1;
    let mut k: usize = 4;
    assert(tag_len(s@) == high_tag_end(s@, 1, MAX_TAG_CONT));
    while k > 0
        invariant
            1 <= i <= s@.len(),
            k <= 4,
            i + k == 5,
            tag_len(s@) == high_tag_end(s@, i as int, k as nat),
        decreases k,
    {
        proof {
            assert(high_tag_end(s@, i as int, k as nat) == if i >= s@.len() {
                None
            } else if s@[i as int] < 128 {
                Some(i + 1)
            } else {
                high_tag_end(s@, i + 1, (k - 1) as nat)
            });
        }
        if i >= s.len() {
            return None;
        }
        if at(s, i) < 128 {
            return Some(i + 1);
        }
        i = i + 1;
        k = k - 1;
    }
    None
}

/// The length octets at `i`: `(length, offset of the contents)`.
#[inline(always)]
pub fn read_len(s: &[u8], i: usize) -> (r: Option<(usize, usize)>)
    ensures
        r matches Some((len, c)) ==> parse_len(s@, i as int) == Some((len as int, c as int)),
        r is None ==> parse_len(s@, i as int) is None,
{
    if i >= s.len() {
        return None;
    }
    let b = at(s, i);
    if b < 128 {
        Some((b as usize, i + 1))
    } else if b == 0x81 {
        if s.len() - i < 2 || at(s, i + 1) < 128 {
            None
        } else {
            Some((at(s, i + 1) as usize, i + 2))
        }
    } else if b == 0x82 {
        if s.len() - i < 3 || at(s, i + 1) == 0 {
            None
        } else {
            Some(((at(s, i + 1) as usize) * 0x100 + at(s, i + 2) as usize, i + 3))
        }
    } else if b == 0x83 {
        if s.len() - i < 4 || at(s, i + 1) == 0 {
            None
        } else {
            Some(
                (
                    (at(s, i + 1) as usize) * 0x1_0000 + (at(s, i + 2) as usize) * 0x100 + at(s, i + 3) as usize,
                    i + 4,
                ),
            )
        }
    } else if b == 0x84 {
        if s.len() - i < 5 || at(s, i + 1) == 0 {
            None
        } else {
            let v: u32 = (at(s, i + 1) as u32) * 0x100_0000 + (at(s, i + 2) as u32) * 0x1_0000 + (at(s, i
                + 2 + 1) as u32) * 0x100 + at(s, i + 4) as u32;
            Some((v as usize, i + 5))
        }
    } else {
        None
    }
}

/// The TLV at the start of `s`, and the bytes after it.
#[inline(always)]
pub fn read_tlv<'a>(s: &'a [u8]) -> (r: Option<(Tlv<'a>, &'a [u8])>)
    ensures
        r matches Some((x, rest)) ==> parse_tlv(s@) == Some((x@, rest@)),
        r is None ==> parse_tlv(s@) is None,
{
    proof {
        lemma_tag_len_bounds(s@);
    }
    // One identifier octet and a short-form length: most TLVs.
    if s.len() >= 2 && at(s, 0) % 32 != 31 && at(s, 1) < 128 {
        let len = at(s, 1) as usize;
        if len > s.len() - 2 {
            return None;
        }
        let x = Tlv { tag: subslice(s, 0, 1), content: subslice(s, 2, 2 + len) };
        let rest = subslice(s, 2 + len, s.len());
        return Some((x, rest));
    }
    read_tlv_long(s)
}

/// `read_tlv` for any TLV: the identifier and length octets in full.
#[inline(never)]
pub fn read_tlv_long<'a>(s: &'a [u8]) -> (r: Option<(Tlv<'a>, &'a [u8])>)
    ensures
        r matches Some((x, rest)) ==> parse_tlv(s@) == Some((x@, rest@)),
        r is None ==> parse_tlv(s@) is None,
{
    proof {
        lemma_tag_len_bounds(s@);
    }
    let h = match read_tag_len(s) {
        Some(h) => h,
        None => return None,
    };
    let (len, c) = match read_len(s, h) {
        Some(x) => x,
        None => return None,
    };
    if len > s.len() - c {
        return None;
    }
    let x = Tlv { tag: subslice(s, 0, h), content: subslice(s, c, c + len) };
    let rest = subslice(s, c + len, s.len());
    Some((x, rest))
}

/// The TLV at the start of `s` if its identifier is the single octet `t`:
/// `(contents, rest)`.
#[inline(always)]
pub fn read_expect<'a>(s: &'a [u8], t: u8) -> (r: Option<(&'a [u8], &'a [u8])>)
    requires
        t % 32 != 31,
    ensures
        r matches Some((c, rest)) ==> parse_expect(s@, t) == Some((c@, rest@)),
        r is None ==> parse_expect(s@, t) is None,
{
    proof {
        lemma_tag_len_bounds(s@);
    }
    // The expected tag and a short-form length: most TLVs in a certificate.
    if s.len() >= 2 && at(s, 0) == t && at(s, 1) < 128 {
        proof {
            assert(s@.subrange(0, 1) =~= seq![t]);
        }
        let len = at(s, 1) as usize;
        if len > s.len() - 2 {
            return None;
        }
        let c = subslice(s, 2, 2 + len);
        let r = subslice(s, 2 + len, s.len());
        proof {
            assert(c@ =~= s@.subrange(2, 2 + len as int));
            assert(r@ =~= s@.subrange(2 + len as int, s@.len() as int));
        }
        return Some((c, r));
    }
    if s.len() == 0 {
        return None;
    }
    if at(s, 0) != t {
        proof {
            if let Some(h) = tag_len(s@) {
                if h == 1 {
                    assert(s@.subrange(0, 1)[0] != seq![t][0]);
                } else {
                    assert(s@.subrange(0, h).len() != seq![t].len());
                }
            }
        }
        return None;
    }
    proof {
        assert(s@.subrange(0, 1) =~= seq![t]);
    }
    let (len, c) = match read_len(s, 1) {
        Some(x) => x,
        None => return None,
    };
    if len > s.len() - c {
        return None;
    }
    Some((subslice(s, c, c + len), subslice(s, c + len, s.len())))
}

/// `s` is exactly one TLV with identifier `t`: its contents.
#[inline(always)]
pub fn read_only<'a>(s: &'a [u8], t: u8) -> (r: Option<&'a [u8]>)
    requires
        t % 32 != 31,
    ensures
        r matches Some(c) ==> parse_only(s@, t) == Some(c@),
        r is None ==> parse_only(s@, t) is None,
{
    match read_expect(s, t) {
        Some((c, rest)) => if rest.len() == 0 {
            Some(c)
        } else {
            None
        },
        None => None,
    }
}

/// `s` is exactly one TLV.
#[inline(always)]
pub fn read_only_tlv<'a>(s: &'a [u8]) -> (r: Option<Tlv<'a>>)
    ensures
        r matches Some(x) ==> parse_only_tlv(s@) == Some(x@),
        r is None ==> parse_only_tlv(s@) is None,
{
    match read_tlv(s) {
        Some((x, rest)) => if rest.len() == 0 {
            Some(x)
        } else {
            None
        },
        None => None,
    }
}

/// Whether the identifier octets are exactly `t`.
#[inline(always)]
pub fn tag_is(tag: &[u8], t: u8) -> (r: bool)
    ensures
        r == (tag@ == seq![t]),
{
    let r = tag.len() == 1 && at(tag, 0) == t;
    proof {
        if tag@.len() == 1 && tag@[0] == t {
            assert(tag@ =~= seq![t]);
        }
        if tag@ == seq![t] {
            assert(tag@[0] == seq![t][0]);
        }
    }
    r
}

/// Byte-for-byte equality.
#[inline(always)]
pub fn bytes_eq(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a@.len(),
            a@.len() == b@.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases a@.len() - i,
    {
        if at(a, i) != at(b, i) {
            proof {
                assert(a@[i as int] != b@[i as int]);
            }
            return false;
        }
        i = i + 1;
    }
    proof {
        assert(a@ =~= b@);
    }
    true
}

pub fn check_integer(c: &[u8]) -> (r: bool)
    ensures
        r == valid_integer(c@),
{
    if c.len() == 0 {
        return false;
    }
    if c.len() >= 2 {
        if at(c, 0) == 0 && at(c, 1) < 128 {
            return false;
        }
        if at(c, 0) == 0xFF && at(c, 1) >= 128 {
            return false;
        }
    }
    true
}

#[inline]
pub fn check_oid(c: &[u8]) -> (r: bool)
    ensures
        r == valid_oid(c@),
{
    let n = c.len();
    if n == 0 || at(c, n - 1) >= 128 {
        return false;
    }
    // Almost every OID has no 0x80 octet at all, and then none begins a
    // subidentifier. Three octets (id-ce, id-at) are the most common.
    if n == 3 {
        if at(c, 0) != 0x80 && at(c, 1) != 0x80 {
            return true;
        }
    } else {
        let mut any = false;
        let mut k: usize = 0;
        while k < n
            invariant
                n == c@.len(),
                k <= n,
                !any ==> forall|j: int| 0 <= j < k ==> #[trigger] c@[j] != 0x80,
            decreases n - k,
        {
            any = any | (at(c, k) == 0x80);
            k = k + 1;
        }
        if !any {
            return true;
        }
    }
    if at(c, 0) == 0x80 {
        return false;
    }
    // A 0x80 octet that begins a subidentifier is padding.
    let mut i: usize = 1;
    while i < n
        invariant
            n == c@.len(),
            1 <= i <= n,
            c@[0] != 0x80,
            forall|j: int|
                0 <= j < i && (j == 0 || c@[j - 1] < 128) ==> #[trigger] c@[j] != 0x80,
        decreases n - i,
    {
        if at(c, i) == 0x80 && at(c, i - 1) < 128 {
            return false;
        }
        i = i + 1;
    }
    true
}

/// A BIT STRING, borrowed.
#[derive(Clone, Copy)]
pub struct BitString<'a> {
    pub unused: u8,
    pub bytes: &'a [u8],
}

impl<'a> View for BitString<'a> {
    type V = SpecBitString;

    open spec fn view(&self) -> SpecBitString {
        SpecBitString { unused: self.unused, bytes: self.bytes@ }
    }
}

#[inline(always)]
pub fn pow2_u8(u: u8) -> (r: u8)
    requires
        u <= 7,
    ensures
        r as nat == pow2_8(u),
        r >= 1,
{
    if u == 0 {
        1
    } else if u == 1 {
        2
    } else if u == 2 {
        4
    } else if u == 3 {
        8
    } else if u == 4 {
        16
    } else if u == 5 {
        32
    } else if u == 6 {
        64
    } else {
        128
    }
}

pub fn read_bit_string<'a>(c: &'a [u8]) -> (r: Option<BitString<'a>>)
    ensures
        r matches Some(b) ==> parse_bit_string(c@) == Some(b@),
        r is None ==> parse_bit_string(c@) is None,
{
    let n = c.len();
    if n == 0 || at(c, 0) > 7 {
        return None;
    }
    if n == 1 && at(c, 0) != 0 {
        return None;
    }
    if n > 1 && at(c, n - 1) % pow2_u8(at(c, 0)) != 0 {
        return None;
    }
    Some(BitString { unused: at(c, 0), bytes: subslice(c, 1, n) })
}

pub fn read_octet_aligned_bits<'a>(c: &'a [u8]) -> (r: Option<&'a [u8]>)
    ensures
        r matches Some(b) ==> parse_octet_aligned_bits(c@) == Some(b@),
        r is None ==> parse_octet_aligned_bits(c@) is None,
{
    if c.len() >= 1 && at(c, 0) == 0 {
        Some(subslice(c, 1, c.len()))
    } else {
        None
    }
}

/// A non-negative INTEGER that fits in a `u64`.
pub fn read_u64(c: &[u8]) -> (r: Option<u64>)
    ensures
        r == parse_u64(c@),
{
    if !check_integer(c) || at(c, 0) >= 128 {
        return None;
    }
    let n = c.len();
    if !(n <= 8 || (n == 9 && at(c, 0) == 0)) {
        return None;
    }
    // A ninth octet is a leading zero: skip it.
    let off: usize = if n == 9 {
        1
    } else {
        0
    };
    let mut v: u64 = 0;
    let mut i: usize = off;
    proof {
        reveal_with_fuel(be_value, 2);
    }
    while i < n
        invariant
            n == c@.len(),
            off <= i <= n,
            n <= 8 + off,
            v as nat == be_value(c@, i as int),
            be_value(c@, i as int) < pow256(i - off),
        decreases n - i,
    {
        proof {
            let k = i - off;
            lemma_pow256_le8(k);
            let bv = be_value(c@, i as int);
            let p = pow256(k);
            let x = c@[i as int] as nat;
            assert(bv * 256 + x < 256 * p) by (nonlinear_arith)
                requires
                    bv < p,
                    x < 256,
            ;
            assert(pow256(k + 1) == 256 * p);
        }
        v = v * 256 + at(c, i) as u64;
        i = i + 1;
    }
    Some(v)
}

pub open spec fn pow256(n: int) -> nat
    decreases n,
{
    if n <= 0 {
        1
    } else {
        256 * pow256(n - 1)
    }
}

pub proof fn lemma_pow256_step(n: int)
    requires
        n >= 0,
    ensures
        pow256(n + 1) == 256 * pow256(n),
{
}

pub proof fn lemma_pow256_le8(n: int)
    requires
        0 <= n <= 8,
    ensures
        pow256(n) <= 0x1_0000_0000_0000_0000,
        n <= 7 ==> 256 * pow256(n) <= 0x1_0000_0000_0000_0000,
    decreases n,
{
    reveal_with_fuel(pow256, 9);
}

/// IA5String name contents: 7-bit with no NUL.
pub fn check_ia5_name(c: &[u8]) -> (r: bool)
    ensures
        r == valid_ia5_name(c@),
{
    // No early exit, so that the compiler can check many octets at a time.
    let mut i: usize = 0;
    let mut ok = true;
    while i < c.len()
        invariant
            i <= c@.len(),
            ok == forall|j: int| 0 <= j < i ==> 0 < #[trigger] c@[j] < 128,
        decreases c@.len() - i,
    {
        let b = at(c, i);
        let ghost ok0 = ok;
        ok = ok & (b != 0) & (b < 128);
        proof {
            if ok0 && !ok {
                assert(!(0 < c@[i as int] < 128));
            }
        }
        i = i + 1;
    }
    ok
}

} // verus!
