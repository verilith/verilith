//! LZW decoding (Appendix F), proven to compute `spec::lzw`.
//!
//! The table holds, for each code the decoder has added, where its string
//! is in the output and how long it is: an entry is always the previous
//! code's output followed by one more byte that was output right after it,
//! so it is a run of the output already written. Decoding a code is then
//! one LZ77 match copy (`verilith_core::lz::copy_match`), with the code the
//! decoder is about to add (`KwKwK`) being the one copy that overlaps
//! itself.
//!
//! The output buffer has `SLACK` bytes past the `need` the caller wants, so
//! that the last string, which may run past `need`, is written whole and no
//! copy has to be cut short.
use crate::spec::*;
use verilith_core::lz::copy_match;
#[cfg(verus_only)]
use verilith_core::lz::matched;
use verilith_core::prims::{get, get32, set, set32};
#[cfg(verus_only)]
use verilith_core::bits::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

/// Bytes the output buffer needs past what the caller wants: one string.
pub const SLACK: usize = 4096;

/// The table entries the decoder added are runs of `out` before `pos`, at
/// `off` and `len`; the roots are what `spec::init_dict` says.
pub open spec fn table_ok(s: Lzw, m: nat, out: Seq<u8>, pos: int, off: Seq<u32>, len: Seq<u32>) -> bool {
    &&& off.len() == MAX_CODES
    &&& len.len() == MAX_CODES
    &&& clear_code(m) + 2 <= s.dict.len() <= MAX_CODES
    &&& forall|j: int| 0 <= j < clear_code(m) ==> #[trigger] s.dict[j] == seq![j as u8]
    &&& forall|j: int|
        #![trigger s.dict[j]]
        #![trigger len[j]]
        clear_code(m) + 2 <= j < s.dict.len() ==> {
            &&& 1 <= len[j] <= j + 1
            &&& off[j] + len[j] <= pos
            &&& s.dict[j] == out.subrange(off[j] as int, off[j] + len[j])
        }
}

/// Bytes before `pos` that do not change keep the table right, and so does
/// a larger `pos`.
pub proof fn lemma_table_keep(s: Lzw, m: nat, a: Seq<u8>, b: Seq<u8>, pos: int, pos2: int, off: Seq<u32>, len: Seq<u32>)
    requires
        table_ok(s, m, a, pos, off, len),
        pos <= pos2,
        pos <= a.len(),
        pos <= b.len(),
        forall|j: int| 0 <= j < pos ==> #[trigger] b[j] == a[j],
    ensures
        table_ok(s, m, b, pos2, off, len),
{
    assert forall|j: int|
        #![trigger s.dict[j]]
        #![trigger len[j]]
        clear_code(m) + 2 <= j < s.dict.len() implies {
            &&& 1 <= len[j] <= j + 1
            &&& off[j] + len[j] <= pos2
            &&& s.dict[j] == b.subrange(off[j] as int, off[j] + len[j])
        } by {
        assert(b.subrange(off[j] as int, off[j] + len[j]) =~= a.subrange(off[j] as int, off[j] + len[j]));
    }
}

/// Adding an entry that is the run of `l` bytes at `o`.
pub proof fn lemma_table_push(s: Lzw, m: nat, out: Seq<u8>, pos: int, off: Seq<u32>, len: Seq<u32>, o: u32, l: u32, x: Seq<u8>)
    requires
        table_ok(s, m, out, pos, off, len),
        s.dict.len() < MAX_CODES,
        1 <= l <= s.dict.len() + 1,
        o + l <= pos,
        x == out.subrange(o as int, o + l),
    ensures
        table_ok(
            Lzw { dict: s.dict.push(x), ..s },
            m,
            out,
            pos,
            off.update(s.dict.len() as int, o),
            len.update(s.dict.len() as int, l),
        ),
{
    let n = s.dict.len() as int;
    let d2 = s.dict.push(x);
    let off2 = off.update(n, o);
    let len2 = len.update(n, l);
    assert forall|j: int| 0 <= j < clear_code(m) implies #[trigger] d2[j] == seq![j as u8] by {
        assert(d2[j] == s.dict[j]);
    }
    assert forall|j: int|
        #![trigger d2[j]]
        #![trigger len2[j]]
        clear_code(m) + 2 <= j < d2.len() implies {
            &&& 1 <= len2[j] <= j + 1
            &&& off2[j] + len2[j] <= pos
            &&& d2[j] == out.subrange(off2[j] as int, off2[j] + len2[j])
        } by {
        if j < n {
            assert(d2[j] == s.dict[j]);
            assert(len2[j] == len[j]);
        }
    }
}

/// A match copied from a run that ends before `pos` is that run.
pub proof fn lemma_copy_old(a: Seq<u8>, b: Seq<u8>, pos: int, o: int, l: int)
    requires
        matched(a, b, pos, pos - o, l),
        0 <= o,
        o + l <= pos,
        1 <= l,
        pos + l <= a.len(),
    ensures
        b.subrange(pos, pos + l) == a.subrange(o, o + l),
        forall|j: int| 0 <= j < pos ==> #[trigger] b[j] == a[j],
{
    assert forall|k: int| 0 <= k < l implies #[trigger] b.subrange(pos, pos + l)[k] == a.subrange(o, o + l)[k] by {
        assert(b[pos + k] == b[pos + k - (pos - o)]);
        assert(pos + k - (pos - o) == o + k);
    }
    assert(b.subrange(pos, pos + l) =~= a.subrange(o, o + l));
}

/// The match for the code about to be added: the previous string, at
/// `last..pos`, and its first byte again.
pub proof fn lemma_copy_new(a: Seq<u8>, b: Seq<u8>, pos: int, last: int)
    requires
        matched(a, b, pos, pos - last, pos - last + 1),
        0 <= last < pos,
        pos + (pos - last + 1) <= a.len(),
    ensures
        b.subrange(pos, 2 * pos - last + 1) == a.subrange(last, pos) + seq![a[last]],
        forall|j: int| 0 <= j < pos ==> #[trigger] b[j] == a[j],
{
    let l = pos - last + 1;
    let r = a.subrange(last, pos) + seq![a[last]];
    assert forall|k: int| 0 <= k < l implies #[trigger] b.subrange(pos, pos + l)[k] == r[k] by {
        assert(b[pos + k] == b[pos + k - (pos - last)]);
        if k < l - 1 {
            assert(pos + k - (pos - last) == last + k);
        } else {
            assert(pos + k - (pos - last) == pos);
            assert(b[pos] == b[pos - (pos - last)]);
        }
    }
    assert(b.subrange(pos, pos + l) =~= r);
}

/// The decoder's state between codes, and the specification's state
/// (`s`) it stands for.
pub struct St {
    /// Entries in the table: `s.dict.len()`.
    pub n: usize,
    /// The code width.
    pub w: u64,
    /// Whether there is a previous code (not the first code after a clear code).
    pub has_prev: bool,
    /// The previous code, if `has_prev`.
    pub prev: usize,
    /// Where the previous code's string starts in the output.
    pub last: usize,
    /// Bytes output so far.
    pub pos: usize,
    /// The specification's state.
    pub s: Ghost<Lzw>,
}

impl St {
    pub open spec fn ok(self, m: nat, need: nat, out: Seq<u8>, off: Seq<u32>, len: Seq<u32>) -> bool {
        let s = self.s@;
        &&& m <= 8
        &&& need + SLACK <= out.len() <= u32::MAX
        &&& self.pos < need + SLACK
        &&& s.out == out.subrange(0, self.pos as int)
        &&& self.n == s.dict.len()
        &&& self.w == s.width
        &&& m + 1 <= self.w <= 12
        &&& table_ok(s, m, out, self.pos as int, off, len)
        &&& self.has_prev == (s.prev is Some)
        &&& self.has_prev ==> {
            &&& s.prev == Some(self.prev as nat)
            &&& self.prev < self.n
            &&& (self.prev < clear_code(m) || self.prev >= clear_code(m) + 2)
            &&& self.last < self.pos
            &&& self.pos - self.last <= self.prev + 1
            &&& s.dict[self.prev as int] == out.subrange(self.last as int, self.pos as int)
        }
    }
}

/// The state after a clear code.
pub fn st_reset(m: u8, clear: usize, pos: usize, Ghost(out): Ghost<Seq<u8>>) -> (st: St)
    requires
        m <= 8,
        clear == clear_code(m as nat),
    ensures
        st.pos == pos,
        st.s@ == reset(m as nat, out),
        st.n == clear + 2,
        st.w == m + 1,
        !st.has_prev,
{
    proof {
        lemma2_to64();
        if m < 8 {
            lemma_pow2_strictly_increases(m as nat, 8);
        }
    }
    St { n: clear + 2, w: m as u64 + 1, has_prev: false, prev: 0, last: 0, pos, s: Ghost(reset(m as nat, out)) }
}

/// The width after a code (`spec::next_width`).
#[inline(always)]
fn grow(n: usize, w: u64) -> (r: u64)
    requires
        1 <= w <= 12,
    ensures
        r == next_width(n as nat, w as nat),
        1 <= r <= 12,
{
    proof {
        lemma_mask(w);
    }
    if n as u64 >= (1u64 << w) && w < 12 {
        w + 1
    } else {
        w
    }
}

/// The first code after a clear code (or of the data): a root.
#[inline(always)]
pub fn code_first(st: &mut St, m: u8, clear: usize, need: usize, out: &mut [u8], off: &[u32], len: &[u32], c: usize) -> (ok: bool)
    requires
        old(st).ok(m as nat, need as nat, old(out)@, off@, len@),
        !old(st).has_prev,
        old(st).pos < need,
        clear == clear_code(m as nat),
        c != clear,
        c != clear + 1,
    ensures
        final(out)@.len() == old(out)@.len(),
        ok == lzw_code(m as nat, old(st).s@, c as nat) is Some,
        ok ==> final(st).ok(m as nat, need as nat, final(out)@, off@, len@)
            && final(st).s@ == lzw_code(m as nat, old(st).s@, c as nat)->Some_0,
{
    let ghost mm = m as nat;
    let ghost s = st.s@;
    if c >= clear {
        return false;
    }
    let ghost o = out@;
    let pos = st.pos;
    set(out, pos, c as u8);
    proof {
        let s2 = lzw_code(mm, s, c as nat)->Some_0;
        lemma_table_keep(s, mm, o, out@, pos as int, pos + 1, off@, len@);
        assert(s2.out =~= out@.subrange(0, pos + 1));
        assert(s2.dict[c as int] =~= out@.subrange(pos as int, pos + 1));
    }
    st.last = pos;
    st.pos = pos + 1;
    st.prev = c;
    st.has_prev = true;
    st.w = grow(st.n, st.w);
    st.s = Ghost(lzw_code(mm, s, c as nat)->Some_0);
    true
}

/// The string of code `c`, written at `pos`; `None` if it is not in the
/// table.
#[inline(always)]
fn put_string(st: &St, m: u8, clear: usize, need: usize, out: &mut [u8], off: &[u32], len: &[u32], c: usize) -> (r: Option<(usize, Ghost<Seq<u8>>)>)
    requires
        st.ok(m as nat, need as nat, old(out)@, off@, len@),
        st.has_prev,
        st.pos < need,
        clear == clear_code(m as nat),
        c != clear,
        c != clear + 1,
    ensures
        final(out)@.len() == old(out)@.len(),
        r is Some == (c < st.n || (c == st.n && st.n < MAX_CODES)),
        r matches Some((l, str)) ==> {
            &&& str@ == (if c < st.n { st.s@.dict[c as int] } else {
                st.s@.dict[st.prev as int] + seq![st.s@.dict[st.prev as int][0]]
            })
            &&& l == str@.len()
            &&& 1 <= l <= c + 1
            &&& final(out)@.subrange(st.pos as int, st.pos + l) == str@
            &&& forall|j: int| 0 <= j < st.pos ==> #[trigger] final(out)@[j] == old(out)@[j]
        },
{
    let ghost s = st.s@;
    let ghost o = out@;
    let pos = st.pos;
    if c < clear {
        set(out, pos, c as u8);
        proof {
            assert(out@.subrange(pos as int, pos + 1) =~= s.dict[c as int]);
        }
        Some((1, Ghost(s.dict[c as int])))
    } else if c < st.n {
        let co = get32(off, c) as usize;
        let cl = get32(len, c) as usize;
        proof {
            assert(1 <= len@[c as int] <= c + 1);
        }
        copy_match(out, pos, pos - co, cl);
        proof {
            lemma_copy_old(o, out@, pos as int, co as int, cl as int);
        }
        Some((cl, Ghost(s.dict[c as int])))
    } else if c == st.n && st.n < 4096 {
        let last = st.last;
        let cl = pos - last + 1;
        copy_match(out, pos, pos - last, cl);
        proof {
            lemma_copy_new(o, out@, pos as int, last as int);
            assert(o.subrange(last as int, pos as int)[0] == o[last as int]);
            assert(2 * pos - last + 1 == pos + cl);
        }
        Some((cl, Ghost(s.dict[st.prev as int] + seq![s.dict[st.prev as int][0]])))
    } else {
        None
    }
}

/// A code after the first: its string, and a new table entry.
#[inline(always)]
pub fn code_next(st: &mut St, m: u8, clear: usize, need: usize, out: &mut [u8], off: &mut [u32], len: &mut [u32], c: usize) -> (ok: bool)
    requires
        old(st).ok(m as nat, need as nat, old(out)@, old(off)@, old(len)@),
        old(st).has_prev,
        old(st).pos < need,
        clear == clear_code(m as nat),
        c != clear,
        c != clear + 1,
    ensures
        final(out)@.len() == old(out)@.len(),
        final(off)@.len() == old(off)@.len(),
        final(len)@.len() == old(len)@.len(),
        ok == lzw_code(m as nat, old(st).s@, c as nat) is Some,
        ok ==> final(st).ok(m as nat, need as nat, final(out)@, final(off)@, final(len)@)
            && final(st).s@ == lzw_code(m as nat, old(st).s@, c as nat)->Some_0,
{
    let ghost mm = m as nat;
    let ghost s = st.s@;
    let ghost o = out@;
    let start = st.pos;
    let last = st.last;
    let (l, Ghost(str)) = match put_string(st, m, clear, need, out, off, len, c) {
        Some(x) => x,
        None => return false,
    };
    let pos = start + l;
    proof {
        lemma_table_keep(s, mm, o, out@, start as int, pos as int, off@, len@);
        assert(out@.subrange(last as int, start as int) =~= o.subrange(last as int, start as int));
        assert(out@[start as int] == str[0]);
    }
    let ghost s1 = s;
    if st.n < 4096 {
        let n = st.n;
        let el = (start - last + 1) as u32;
        proof {
            let x = out@.subrange(last as int, start + 1);
            assert(x =~= s.dict[st.prev as int] + seq![str[0]]);
            lemma_table_push(s, mm, out@, pos as int, off@, len@, last as u32, el, x);
            s1 = Lzw { dict: s.dict.push(x), ..s };
        }
        set32(off, n, last as u32);
        set32(len, n, el);
        st.n = n + 1;
    }
    proof {
        let s2 = lzw_code(mm, s, c as nat)->Some_0;
        assert(s2.dict == s1.dict);
        assert(s2.out =~= out@.subrange(0, pos as int));
        assert(s2.dict[c as int] == str);
    }
    st.last = start;
    st.pos = pos;
    st.prev = c;
    st.w = grow(st.n, st.w);
    st.s = Ghost(lzw_code(mm, s, c as nat)->Some_0);
    true
}

/// Decodes the first `need` bytes of the LZW data `data`, with minimum code
/// size `m`, into `out[..need]`. Returns whether `spec::lzw` accepts the
/// data; `out` from `need` on is scratch space. `off` and `len` are the
/// table, scratch space too.
#[verifier::loop_isolation(false)]
pub fn lzw_exec(data: &[u8], m: u8, need: usize, out: &mut [u8], off: &mut [u32], len: &mut [u32]) -> (r: bool)
    requires
        m <= 8,
        1 <= need,
        need + SLACK <= old(out)@.len() <= u32::MAX,
        old(off)@.len() == MAX_CODES,
        old(len)@.len() == MAX_CODES,
    ensures
        final(out)@.len() == old(out)@.len(),
        final(off)@.len() == MAX_CODES,
        final(len)@.len() == MAX_CODES,
        r == lzw(data@, m as nat, need as nat) is Some,
        r ==> lzw(data@, m as nat, need as nat) == Some(final(out)@.subrange(0, need as int)),
{
    let ghost dd = data@;
    let ghost mm = m as nat;
    let ghost olen = out@.len();
    proof {
        lemma_mask(m as u64);
        lemma_pow2_strictly_increases(m as nat, 9);
        lemma2_to64();
    }
    let clear: usize = (1u64 << (m as u64)) as usize;
    let mut st = st_reset(m, clear, 0, Ghost(Seq::empty()));
    let mut buf: u64 = 0;
    let mut cnt: u64 = 0;
    let mut ip: usize = 0;
    proof {
        let s = st.s@;
        assert(s.out =~= out@.subrange(0, 0));
        assert forall|j: int| 0 <= j < clear_code(mm) implies #[trigger] s.dict[j] == seq![j as u8] by {}
    }
    while st.pos < need
        invariant
            out@.len() == olen,
            off@.len() == MAX_CODES,
            len@.len() == MAX_CODES,
            st.ok(mm, need as nat, out@, off@, len@),
            ip <= data@.len(),
            cnt <= 8 * ip,
            cnt < 20,
            buf as nat == bits(dd, 8 * ip - cnt, cnt as nat),
            lzw(dd, mm, need as nat) == lzw_run(dd, mm, need as nat, st.s@, 8 * ip - cnt),
        decreases 8 * data@.len() - (8 * ip - cnt),
    {
        let ghost q = 8 * ip - cnt;
        let w = st.w;
        // Enough bits for a code.
        while cnt < w
            invariant
                ip <= data@.len(),
                cnt <= 8 * ip,
                cnt < 20,
                8 * ip - cnt == q,
                buf as nat == bits(dd, q, cnt as nat),
            decreases data@.len() - ip,
        {
            if ip >= data.len() {
                return false;
            }
            let byte = get(data, ip) as u64;
            proof {
                lemma_bits_bound(dd, q, cnt as nat);
                lemma_or_byte(buf, byte, cnt);
                lemma_bits_split(dd, q, cnt as nat, 8);
                lemma_bits_byte(dd, ip as int);
                assert(q + cnt == 8 * ip);
            }
            buf = buf | (byte << cnt);
            cnt = cnt + 8;
            ip = ip + 1;
        }
        proof {
            lemma_mask(w);
            lemma_shr_bits(dd, q, cnt as nat, buf, w);
            lemma_bits_bound(dd, q, w as nat);
            lemma_pow2_strictly_increases(w as nat, 13);
        }
        let c = (buf & ((1u64 << w) - 1)) as usize;
        buf = buf >> w;
        cnt = cnt - w;
        assert(c == bits(dd, q, w as nat));
        if c == clear {
            proof {
                let s = reset(mm, st.s@.out);
                assert forall|j: int| 0 <= j < clear_code(mm) implies #[trigger] s.dict[j] == seq![j as u8] by {}
            }
            st = st_reset(m, clear, st.pos, Ghost(st.s@.out));
        } else if c == clear + 1 {
            return false;
        } else if !st.has_prev {
            if !code_first(&mut st, m, clear, need, out, off, len, c) {
                return false;
            }
        } else {
            if !code_next(&mut st, m, clear, need, out, off, len, c) {
                return false;
            }
        }
    }
    proof {
        assert(out@.subrange(0, st.pos as int).subrange(0, need as int) =~= out@.subrange(0, need as int));
    }
    true
}

} // verus!
