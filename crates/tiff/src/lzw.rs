//! TIFF LZW decoding (§13), proven to compute `spec::lzw`.
//!
//! The same design as verilith-gif's decoder: each table entry the decoder
//! adds is the previous code's output and the byte after it, so it is a
//! run of output already written, and decoding a code is one LZ77 match
//! copy. TIFF's codes are packed most significant bit first, widen one
//! entry early, and the data must start with a clear code and end with the
//! end code. The table holds at most 4096 entries.
use crate::spec::*;
use verilith_core::lz::copy_match;
#[cfg(verus_only)]
use verilith_core::lz::matched;
use verilith_core::prims::{get, get32, set, set32};
#[cfg(verus_only)]
use verilith_core::bits::{lowmask, lemma_mask, lemma_and_mask};
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

/// Bytes the output buffer needs past what the caller wants: one string.
pub const SLACK: usize = 4096;

/// Entries the exec table stores: those a 12-bit code can name.
pub spec const STORED: nat = 4096;

// ---------------------------------------------------------------------------
// Bits, most significant first
// ---------------------------------------------------------------------------

pub proof fn lemma_mbits_bound(d: Seq<u8>, q: int, n: nat)
    ensures
        mbits(d, q, n) < pow2(n),
    decreases n,
{
    if n == 0 {
        lemma2_to64();
    } else {
        lemma_mbits_bound(d, q, (n - 1) as nat);
        lemma_pow2_unfold(n);
        assert(mbit(d, q + n - 1) <= 1);
    }
}

/// The first `m` bits, then the next `n`.
pub proof fn lemma_mbits_split(d: Seq<u8>, q: int, m: nat, n: nat)
    ensures
        mbits(d, q, m + n) == mbits(d, q, m) * pow2(n) + mbits(d, q + m, n),
    decreases n,
{
    if n == 0 {
        lemma2_to64();
        assert(m + n == m);
    } else {
        lemma_mbits_split(d, q, m, (n - 1) as nat);
        assert((m + n - 1) as nat == m + (n - 1) as nat);
        assert(q + (m + n) - 1 == q + m + n - 1);
        lemma_pow2_unfold(n);
        let a = mbits(d, q, m);
        let x = mbits(d, q + m, (n - 1) as nat);
        let p = pow2((n - 1) as nat);
        assert(mbits(d, q, m + n) == 2 * (a * p + x) + mbit(d, q + m + n - 1));
        assert(mbits(d, q + m, n) == 2 * x + mbit(d, q + m + n - 1));
        assert(2 * (a * p + x) == a * (2 * p) + 2 * x) by (nonlinear_arith);
    }
}

/// The first `k` bits of byte `i` are its top `k` bits.
proof fn lemma_mbits_top(d: Seq<u8>, i: int, k: nat)
    requires
        0 <= i < d.len(),
        k <= 8,
    ensures
        mbits(d, 8 * i, k) == d[i] as nat / pow2((8 - k) as nat),
    decreases k,
{
    let x = d[i] as nat;
    lemma2_to64();
    if k == 0 {
        assert(x / 256 == 0);
    } else {
        lemma_mbits_top(d, i, (k - 1) as nat);
        let j = (k - 1) as int;
        let kk = 8 * i + j;
        assert(kk / 8 == i && kk % 8 == j) by {
            lemma_fundamental_div_mod_converse(kk, 8, i, j);
        }
        // mbit = (x / 2^(8-k)) % 2, and x / 2^(9-k) == (x / 2^(8-k)) / 2.
        let y = x / pow2((8 - k) as nat);
        lemma_pow2_pos((8 - k) as nat);
        assert(pow2((9 - k) as nat) == pow2((8 - k) as nat) * 2) by {
            lemma_pow2_unfold((9 - k) as nat);
            assert((9 - k) as nat - 1 == (8 - k) as nat);
        }
        lemma_div_denominator(x as int, pow2((8 - k) as nat) as int, 2);
        assert(y == 2 * (y / 2) + y % 2) by {
            lemma_fundamental_div_mod(y as int, 2);
        }
        assert(8 * i + k - 1 == kk);
    }
}

pub proof fn lemma_mbits_byte(d: Seq<u8>, i: int)
    requires
        0 <= i < d.len(),
    ensures
        mbits(d, 8 * i, 8) == d[i] as nat,
{
    lemma_mbits_top(d, i, 8);
    lemma2_to64();
}

// ---------------------------------------------------------------------------
// The table
// ---------------------------------------------------------------------------

/// The stored table entries are runs of `out` before `pos`, at `off` and
/// `len`; the roots are the 256 bytes.
pub open spec fn table_ok(s: Lzw, out: Seq<u8>, pos: int, off: Seq<u32>, len: Seq<u32>) -> bool {
    &&& off.len() == STORED
    &&& len.len() == STORED
    &&& 258 <= s.dict.len() <= TABLE_MAX
    &&& forall|j: int| 0 <= j < 256 ==> #[trigger] s.dict[j] == seq![j as u8]
    &&& forall|j: int|
        #![trigger s.dict[j]]
        #![trigger len[j]]
        258 <= j < s.dict.len() && j < STORED ==> {
            &&& 1 <= len[j] <= j + 1
            &&& off[j] + len[j] <= pos
            &&& s.dict[j] == out.subrange(off[j] as int, off[j] + len[j])
        }
}

pub proof fn lemma_table_keep(s: Lzw, a: Seq<u8>, b: Seq<u8>, pos: int, pos2: int, off: Seq<u32>, len: Seq<u32>)
    requires
        table_ok(s, a, pos, off, len),
        pos <= pos2,
        pos <= a.len(),
        pos <= b.len(),
        forall|j: int| 0 <= j < pos ==> #[trigger] b[j] == a[j],
    ensures
        table_ok(s, b, pos2, off, len),
{
    assert forall|j: int|
        #![trigger s.dict[j]]
        #![trigger len[j]]
        258 <= j < s.dict.len() && j < STORED implies {
            &&& 1 <= len[j] <= j + 1
            &&& off[j] + len[j] <= pos2
            &&& s.dict[j] == b.subrange(off[j] as int, off[j] + len[j])
        } by {
        assert(b.subrange(off[j] as int, off[j] + len[j]) =~= a.subrange(off[j] as int, off[j] + len[j]));
    }
}

/// Adding an entry that is the run of `l` bytes at `o`, stored if the
/// table has room for it.
pub proof fn lemma_table_push(s: Lzw, out: Seq<u8>, pos: int, off: Seq<u32>, len: Seq<u32>, o: u32, l: u32, x: Seq<u8>)
    requires
        table_ok(s, out, pos, off, len),
        s.dict.len() < TABLE_MAX,
        s.dict.len() < STORED ==> 1 <= l <= s.dict.len() + 1 && o + l <= pos && x == out.subrange(o as int, o + l),
    ensures
        s.dict.len() < STORED ==> table_ok(
            Lzw { dict: s.dict.push(x), ..s },
            out,
            pos,
            off.update(s.dict.len() as int, o),
            len.update(s.dict.len() as int, l),
        ),
        s.dict.len() >= STORED ==> table_ok(Lzw { dict: s.dict.push(x), ..s }, out, pos, off, len),
{
    let n = s.dict.len() as int;
    let d2 = s.dict.push(x);
    assert forall|j: int| 0 <= j < 256 implies #[trigger] d2[j] == seq![j as u8] by {
        assert(d2[j] == s.dict[j]);
    }
    if n < STORED {
        let off2 = off.update(n, o);
        let len2 = len.update(n, l);
        assert forall|j: int|
            #![trigger d2[j]]
            #![trigger len2[j]]
            258 <= j < d2.len() && j < STORED implies {
                &&& 1 <= len2[j] <= j + 1
                &&& off2[j] + len2[j] <= pos
                &&& d2[j] == out.subrange(off2[j] as int, off2[j] + len2[j])
            } by {
            if j < n {
                assert(d2[j] == s.dict[j]);
                assert(len2[j] == len[j]);
            }
        }
    } else {
        assert forall|j: int|
            #![trigger d2[j]]
            #![trigger len[j]]
            258 <= j < d2.len() && j < STORED implies {
                &&& 1 <= len[j] <= j + 1
                &&& off[j] + len[j] <= pos
                &&& d2[j] == out.subrange(off[j] as int, off[j] + len[j])
            } by {
            assert(d2[j] == s.dict[j]);
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

// ---------------------------------------------------------------------------
// The decoder's state
// ---------------------------------------------------------------------------

/// The decoder's state between codes, and the specification's state (`s`) it stands for.
pub struct St {
    /// Entries in the table: `s.dict.len()`, up to 4096.
    pub n: usize,
    /// The code width, 9 to 12.
    pub w: u64,
    /// Whether a clear code has been seen.
    pub started: bool,
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
    pub open spec fn ok(self, need: nat, out: Seq<u8>, off: Seq<u32>, len: Seq<u32>) -> bool {
        let s = self.s@;
        &&& need + SLACK <= out.len() <= u32::MAX
        &&& self.pos <= need
        &&& s.out == out.subrange(0, self.pos as int)
        &&& self.n == s.dict.len()
        &&& self.w == s.width
        &&& 9 <= self.w <= 12
        &&& self.started == s.started
        &&& table_ok(s, out, self.pos as int, off, len)
        &&& self.has_prev == (s.prev is Some)
        &&& self.has_prev ==> {
            &&& s.prev == Some(self.prev as nat)
            &&& self.prev < self.n
            &&& self.prev < STORED
            &&& (self.prev < 256 || self.prev >= 258)
            &&& self.last < self.pos
            &&& self.pos - self.last <= self.prev + 1
            &&& s.dict[self.prev as int] == out.subrange(self.last as int, self.pos as int)
        }
    }
}

pub open spec fn cleared(out: Seq<u8>) -> Lzw {
    Lzw { dict: init_dict(), width: 9, prev: None, started: true, out }
}

fn st_new(started: bool, pos: usize, Ghost(out): Ghost<Seq<u8>>) -> (st: St)
    ensures
        st.pos == pos,
        st.s@ == (if started { cleared(out) } else { Lzw { out, ..lzw_start() } }),
        st.n == 258,
        st.w == 9,
        st.started == started,
        !st.has_prev,
{
    let ghost s = if started { cleared(out) } else { Lzw { out, ..lzw_start() } };
    St { n: 258, w: 9, started, has_prev: false, prev: 0, last: 0, pos, s: Ghost(s) }
}

/// The width once the table has `n` entries (`spec::next_width`).
#[inline(always)]
fn grow(n: usize, w: u64) -> (r: u64)
    requires
        9 <= w <= 12,
        n <= TABLE_MAX,
    ensures
        r == next_width(n as nat, w as nat),
        9 <= r <= 12,
{
    proof {
        lemma_mask(w);
    }
    if n as u64 + 1 >= (1u64 << w) && w < 12 {
        w + 1
    } else {
        w
    }
}

/// The first code after a clear code: a root.
#[inline(always)]
fn code_first(st: &mut St, need: usize, out: &mut [u8], off: &[u32], len: &[u32], c: usize) -> (ok: bool)
    requires
        old(st).ok(need as nat, old(out)@, off@, len@),
        old(st).started,
        !old(st).has_prev,
        old(st).pos < need,
        c != 256,
        c != 257,
    ensures
        final(out)@.len() == old(out)@.len(),
        ok == lzw_code(old(st).s@, c as nat, need as nat) is Some,
        ok ==> final(st).ok(need as nat, final(out)@, off@, len@)
            && final(st).s@ == lzw_code(old(st).s@, c as nat, need as nat)->Some_0,
{
    let ghost s = st.s@;
    if c >= 256 {
        return false;
    }
    let ghost o = out@;
    let pos = st.pos;
    set(out, pos, c as u8);
    proof {
        let s2 = lzw_code(s, c as nat, need as nat)->Some_0;
        lemma_table_keep(s, o, out@, pos as int, pos + 1, off@, len@);
        assert(s2.out =~= out@.subrange(0, pos + 1));
        assert(s2.dict[c as int] =~= out@.subrange(pos as int, pos + 1));
    }
    st.last = pos;
    st.pos = pos + 1;
    st.prev = c;
    st.has_prev = true;
    st.s = Ghost(lzw_code(s, c as nat, need as nat)->Some_0);
    true
}

/// The string of code `c`, written at `pos`; `None` if it is not in the
/// table.
#[inline(always)]
fn put_string(st: &St, need: usize, out: &mut [u8], off: &[u32], len: &[u32], c: usize) -> (r: Option<(usize, Ghost<Seq<u8>>)>)
    requires
        st.ok(need as nat, old(out)@, off@, len@),
        st.has_prev,
        st.pos <= need,
        c < STORED,
        c != 256,
        c != 257,
    ensures
        final(out)@.len() == old(out)@.len(),
        r is Some == (c < st.n || c == st.n),
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
    if c < 256 {
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
    } else if c == st.n {
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
fn code_next(st: &mut St, need: usize, out: &mut [u8], off: &mut [u32], len: &mut [u32], c: usize) -> (ok: bool)
    requires
        old(st).ok(need as nat, old(out)@, old(off)@, old(len)@),
        old(st).started,
        old(st).has_prev,
        old(st).pos <= need,
        c < STORED,
        c != 256,
        c != 257,
    ensures
        final(out)@.len() == old(out)@.len(),
        final(off)@.len() == old(off)@.len(),
        final(len)@.len() == old(len)@.len(),
        ok == lzw_code(old(st).s@, c as nat, need as nat) is Some,
        ok ==> final(st).ok(need as nat, final(out)@, final(off)@, final(len)@)
            && final(st).s@ == lzw_code(old(st).s@, c as nat, need as nat)->Some_0,
{
    let ghost s = st.s@;
    let ghost o = out@;
    if st.n >= 4096 {
        return false;
    }
    let start = st.pos;
    let last = st.last;
    let (l, Ghost(str)) = match put_string(st, need, out, off, len, c) {
        Some(x) => x,
        None => return false,
    };
    if l > need - start {
        // The string would go past the end of the strip.
        return false;
    }
    let pos = start + l;
    proof {
        lemma_table_keep(s, o, out@, start as int, pos as int, off@, len@);
        assert(out@.subrange(last as int, start as int) =~= o.subrange(last as int, start as int));
        assert(out@[start as int] == str[0]);
    }
    let n = st.n;
    let el = (start - last + 1) as u32;
    let ghost x = out@.subrange(last as int, start + 1);
    proof {
        assert(x =~= s.dict[st.prev as int] + seq![str[0]]);
        lemma_table_push(s, out@, pos as int, off@, len@, last as u32, el, x);
    }
    if n < 4096 {
        set32(off, n, last as u32);
        set32(len, n, el);
    }
    st.n = n + 1;
    proof {
        let s2 = lzw_code(s, c as nat, need as nat)->Some_0;
        assert(s2.dict == s.dict.push(x));
        assert(s2.out =~= out@.subrange(0, pos as int));
        assert(s2.dict[c as int] == str);
    }
    st.last = start;
    st.pos = pos;
    st.prev = c;
    st.w = grow(st.n, st.w);
    st.s = Ghost(lzw_code(s, c as nat, need as nat)->Some_0);
    true
}

/// Decodes the LZW data `data`, to its end code, into `out[..need]`.
/// Returns whether `spec::lzw` accepts the data; `out` from `need` on is
/// scratch space, and so are `off` and `len`.
#[verifier::loop_isolation(false)]
pub fn lzw_exec(data: &[u8], need: usize, out: &mut [u8], off: &mut [u32], len: &mut [u32]) -> (r: bool)
    requires
        need + SLACK <= old(out)@.len() <= u32::MAX,
        old(off)@.len() == STORED,
        old(len)@.len() == STORED,
    ensures
        final(out)@.len() == old(out)@.len(),
        final(off)@.len() == STORED,
        final(len)@.len() == STORED,
        r == lzw(data@, need as nat) is Some,
        r ==> lzw(data@, need as nat) == Some(final(out)@.subrange(0, need as int)),
{
    let ghost dd = data@;
    let ghost olen = out@.len();
    let mut st = st_new(false, 0, Ghost(Seq::empty()));
    let mut buf: u64 = 0;
    let mut cnt: u64 = 0;
    let mut ip: usize = 0;
    proof {
        lemma2_to64();
        let s = st.s@;
        assert(s.out =~= out@.subrange(0, 0));
        assert(s =~= lzw_start());
        assert forall|j: int| 0 <= j < 256 implies #[trigger] s.dict[j] == seq![j as u8] by {}
    }
    loop
        invariant
            out@.len() == olen,
            off@.len() == STORED,
            len@.len() == STORED,
            st.ok(need as nat, out@, off@, len@),
            ip <= data@.len(),
            cnt <= 8 * ip,
            cnt < 20,
            buf as nat == mbits(dd, 8 * ip - cnt, cnt as nat),
            lzw(dd, need as nat) == lzw_run(dd, need as nat, st.s@, 8 * ip - cnt),
        decreases 8 * data@.len() - (8 * ip - cnt),
    {
        let ghost q = 8 * ip - cnt;
        let w = st.w;
        while cnt < w
            invariant
                ip <= data@.len(),
                cnt <= 8 * ip,
                cnt < 20,
                8 * ip - cnt == q,
                buf as nat == mbits(dd, q, cnt as nat),
            decreases data@.len() - ip,
        {
            if ip >= data.len() {
                return false;
            }
            let byte = get(data, ip) as u64;
            proof {
                lemma_mbits_bound(dd, q, cnt as nat);
                lemma_mbits_split(dd, q, cnt as nat, 8);
                lemma_mbits_byte(dd, ip as int);
                assert(q + cnt == 8 * ip);
                lemma_pow2_strictly_increases(cnt as nat, 20);
                assert(pow2(20) == 0x100000) by { lemma2_to64(); }
                assert(buf < 0x100000);
                assert((buf << 8u64) | byte == buf * 256 + byte) by (bit_vector)
                    requires buf < 0x100000, byte < 256;
            }
            buf = (buf << 8u64) | byte;
            cnt = cnt + 8;
            ip = ip + 1;
        }
        let sh = cnt - w;
        proof {
            lemma_mbits_split(dd, q, w as nat, sh as nat);
            assert(w + sh == cnt);
            lemma_mbits_bound(dd, q + w, sh as nat);
            lemma_mbits_bound(dd, q, w as nat);
            lemma_pow2_pos(sh as nat);
            lemma_u64_shr_is_div(buf, sh);
            lemma_and_mask(buf, sh);
            lemma_mask(sh);
            lemma_fundamental_div_mod_converse(
                buf as int,
                pow2(sh as nat) as int,
                mbits(dd, q, w as nat) as int,
                mbits(dd, q + w, sh as nat) as int,
            );
            lemma_pow2_strictly_increases(w as nat, 13);
            assert(pow2(12) == 4096);
        }
        let c = (buf >> sh) as usize;
        buf = buf & ((1u64 << sh) - 1);
        cnt = sh;
        assert(c == mbits(dd, q, w as nat));
        assert(c < STORED) by {
            if w < 12 { lemma_pow2_strictly_increases(w as nat, 12); }
        }
        if c == 256 {
            proof {
                let s = cleared(st.s@.out);
                assert forall|j: int| 0 <= j < 256 implies #[trigger] s.dict[j] == seq![j as u8] by {}
            }
            st = st_new(true, st.pos, Ghost(st.s@.out));
        } else if c == 257 {
            // The end code: the strip must be complete.
            if st.started && st.pos == need {
                proof {
                    assert(out@.subrange(0, st.pos as int) =~= out@.subrange(0, need as int));
                }
                return true;
            }
            return false;
        } else if !st.started {
            return false;
        } else if !st.has_prev {
            if st.pos >= need {
                return false;
            }
            if !code_first(&mut st, need, out, off, len, c) {
                return false;
            }
        } else {
            if !code_next(&mut st, need, out, off, len, c) {
                return false;
            }
        }
    }
}

} // verus!
