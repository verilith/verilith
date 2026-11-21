//! Verified string escaping for the writer.
//!
//! `escape` says how the writer spells a string's bytes inside quotes.
//! `lemma_escape_parses` is the round trip: wherever the escaped bytes
//! appear in a text, followed by a quote, the parser's `string_body` reads
//! exactly them and `decode` gives back the original bytes. So a string the
//! writer emits can neither end early nor change, whatever bytes it holds.
#[allow(unused_imports)]
use crate::simd::*;
#[allow(unused_imports)]
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// Lowercase hex digit for `n < 16`.
pub open spec fn hexd(n: u8) -> u8 {
    if n < 10 { (0x30 + n) as u8 } else { (0x61 + n - 10) as u8 }
}

/// How one byte is written inside a string: `"` and `\` and control
/// characters are escaped (with the short forms where JSON has them), and
/// everything else is written as is.
pub open spec fn esc(b: u8) -> Seq<u8> {
    if b == 0x22 {
        seq![0x5Cu8, 0x22]
    } else if b == 0x5C {
        seq![0x5Cu8, 0x5C]
    } else if b == 0x08 {
        seq![0x5Cu8, 0x62]
    } else if b == 0x0C {
        seq![0x5Cu8, 0x66]
    } else if b == 0x0A {
        seq![0x5Cu8, 0x6E]
    } else if b == 0x0D {
        seq![0x5Cu8, 0x72]
    } else if b == 0x09 {
        seq![0x5Cu8, 0x74]
    } else if b < 0x20 {
        seq![0x5Cu8, 0x75, 0x30, 0x30, hexd(b / 16), hexd(b % 16)]
    } else {
        seq![b]
    }
}

/// How a string's bytes are written between the quotes.
pub open spec fn escape(b: Seq<u8>) -> Seq<u8>
    decreases b.len(),
{
    if b.len() == 0 {
        Seq::empty()
    } else {
        esc(b[0]) + escape(b.drop_first())
    }
}

pub proof fn lemma_escape_append(x: Seq<u8>, y: Seq<u8>)
    ensures
        escape(x + y) == escape(x) + escape(y),
    decreases x.len(),
{
    if x.len() == 0 {
        assert(x + y =~= y);
        assert(escape(x) + escape(y) =~= escape(y));
    } else {
        assert((x + y).drop_first() =~= x.drop_first() + y);
        lemma_escape_append(x.drop_first(), y);
        assert(escape(x + y) =~= esc(x[0]) + (escape(x.drop_first()) + escape(y)));
    }
}

pub proof fn lemma_escape_one(c: u8)
    ensures
        escape(seq![c]) == esc(c),
{
    let x = seq![c];
    assert(x.drop_first() =~= Seq::<u8>::empty());
    assert(escape(x.drop_first()) == Seq::<u8>::empty());
    assert(escape(x) == esc(x[0]) + escape(x.drop_first()));
    assert(esc(c) + Seq::<u8>::empty() =~= esc(c));
}

/// Bytes that need no escape are written as they are.
pub proof fn lemma_escape_plain(x: Seq<u8>)
    requires
        forall|k: int| 0 <= k < x.len() ==> plain(#[trigger] x[k]),
    ensures
        escape(x) == x,
    decreases x.len(),
{
    if x.len() > 0 {
        assert(plain(x[0]));
        assert forall|k: int| 0 <= k < x.drop_first().len() implies plain(#[trigger] x.drop_first()[k]) by {
            assert(x.drop_first()[k] == x[k + 1]);
        }
        lemma_escape_plain(x.drop_first());
        assert(esc(x[0]) == seq![x[0]]);
        assert(escape(x) =~= x);
    }
}

proof fn lemma_hexd(n: u8)
    requires
        n < 16,
    ensures
        is_hex(hexd(n)),
        hex_val(hexd(n)) == n as u32,
{
}

/// The parser reads one escaped byte back.
proof fn lemma_esc_char(t: Seq<u8>, p: int, c: u8)
    requires
        0 <= p,
        p + esc(c).len() <= t.len(),
        t.subrange(p, p + esc(c).len()) == esc(c),
    ensures
        string_char(t, p) == Some((seq![c], p + esc(c).len())),
        t[p] != 0x22,
        (t[p] == 0x5C) == !plain(c),
{
    let e = esc(c);
    assert forall|k: int| 0 <= k < e.len() implies t[p + k] == #[trigger] e[k] by {
        assert(t.subrange(p, p + e.len())[k] == t[p + k]);
    }
    if c == 0x22 || c == 0x5C || c == 0x08 || c == 0x0C || c == 0x0A || c == 0x0D || c == 0x09 {
        assert(t[p] == 0x5C && t[p + 1] == e[1]);
    } else if c < 0x20 {
        let hi = c / 16;
        let lo = c % 16;
        lemma_hexd(hi);
        lemma_hexd(lo);
        assert(t[p + 1] == 0x75);
        assert(t[p + 2] == 0x30 && t[p + 3] == 0x30 && t[p + 4] == hexd(hi) && t[p + 5] == hexd(lo));
        assert(hex4(t, p + 2) == Some(c as u32)) by {
            assert(hex_val(0x30) == 0);
            assert((((0u32 * 16 + 0) * 16 + hi as u32) * 16 + lo as u32) == c as u32);
        }
        assert(utf8_encode(c as u32) =~= seq![c]);
    } else {
        assert(e == seq![c]);
        assert(e[0] == c);
        assert(t[p] == c);
    }
}

/// The round trip. Escaped bytes followed by a quote are read back as one
/// string body that ends at that quote and decodes to the original bytes.
pub proof fn lemma_escape_parses(t: Seq<u8>, p: int, b: Seq<u8>, e: bool)
    requires
        0 <= p,
        p + escape(b).len() < t.len(),
        t.subrange(p, p + escape(b).len()) == escape(b),
        t[p + escape(b).len()] == 0x22,
    ensures
        string_body(t, p, e) matches Some((n, _)) && n == p + escape(b).len() + 1,
        decode(t, p, p + escape(b).len()) == b,
    decreases b.len(),
{
    let end = p + escape(b).len();
    if b.len() == 0 {
        assert(decode(t, p, end) == Seq::<u8>::empty());
        assert(b =~= Seq::<u8>::empty());
    } else {
        let c = b[0];
        let r = b.drop_first();
        let l = esc(c).len() as int;
        assert(escape(b) == esc(c) + escape(r));
        assert(t.subrange(p, p + l) =~= esc(c)) by {
            assert(t.subrange(p, p + l) =~= t.subrange(p, end).subrange(0, l));
        }
        assert(t.subrange(p + l, p + l + escape(r).len()) =~= escape(r)) by {
            assert(t.subrange(p + l, p + l + escape(r).len()) =~= t.subrange(p, end).subrange(l, escape(b).len() as int));
        }
        lemma_esc_char(t, p, c);
        lemma_escape_parses(t, p + l, r, e || t[p] == 0x5C);
        assert(decode(t, p, end) == seq![c] + decode(t, p + l, end));
        assert(b =~= seq![c] + r);
    }
}

/// The parser reads the quoted, escaped bytes as one string.
pub proof fn lemma_quoted_parses(t: Seq<u8>, p: int, b: Seq<u8>)
    requires
        0 <= p,
        p + escape(b).len() + 2 <= t.len(),
        t.subrange(p, p + escape(b).len() + 2) == seq![0x22u8] + escape(b) + seq![0x22u8],
    ensures
        string(t, p) matches Some((n, _)) && n == p + escape(b).len() + 2,
        decode(t, p + 1, p + 1 + escape(b).len()) == b,
{
    let q = seq![0x22u8] + escape(b) + seq![0x22u8];
    let l = escape(b).len() as int;
    assert(t[p] == q[0]);
    assert(t[p + 1 + l] == q[1 + l]);
    assert(t.subrange(p + 1, p + 1 + l) =~= t.subrange(p, p + l + 2).subrange(1, 1 + l));
    assert(q.subrange(1, 1 + l) =~= escape(b));
    lemma_escape_parses(t, p + 1, b, false);
}

// ---------------------------------------------------------------------------
// Code
// ---------------------------------------------------------------------------

#[inline(always)]
fn ex_hexd(n: u8) -> (r: u8)
    requires
        n < 16,
    ensures
        r == hexd(n),
{
    if n < 10 { 0x30 + n } else { 0x61 + n - 10 }
}

/// Writes `esc(c)`.
#[inline(always)]
fn push_esc(out: &mut Vec<u8>, c: u8)
    ensures
        final(out)@ == old(out)@ + esc(c),
{
    let ghost o = out@;
    if c == 0x22 || c == 0x5C {
        out.push(0x5C);
        out.push(c);
    } else if c == 0x08 {
        out.push(0x5C);
        out.push(0x62);
    } else if c == 0x0C {
        out.push(0x5C);
        out.push(0x66);
    } else if c == 0x0A {
        out.push(0x5C);
        out.push(0x6E);
    } else if c == 0x0D {
        out.push(0x5C);
        out.push(0x72);
    } else if c == 0x09 {
        out.push(0x5C);
        out.push(0x74);
    } else if c < 0x20 {
        out.push(0x5C);
        out.push(0x75);
        out.push(0x30);
        out.push(0x30);
        out.push(ex_hexd(c / 16));
        out.push(ex_hexd(c % 16));
    } else {
        out.push(c);
    }
    assert(out@ =~= o + esc(c));
}

/// Appends `escape(b)`: runs of bytes that need no escape are copied 16 at
/// a time where possible.
pub fn write_escaped(out: &mut Vec<u8>, b: &[u8])
    ensures
        final(out)@ == old(out)@ + escape(b@),
{
    let n = b.len();
    let mut i = 0;
    while i < n
        invariant
            n == b@.len(),
            i <= n,
            out@ == old(out)@ + escape(b@.subrange(0, i as int)),
        decreases n - i,
    {
        let mut k = i;
        while n - k >= 16
            invariant
                n == b@.len(),
                i <= k <= n,
                forall|m: int| i <= m < k ==> plain(#[trigger] b@[m]),
            decreases n - k,
        {
            let p = plain_run16(b, k);
            k = k + p;
            if p < 16 {
                break;
            }
        }
        while k < n && b[k] != 0x22 && b[k] != 0x5C && b[k] >= 0x20
            invariant
                n == b@.len(),
                i <= k <= n,
                forall|m: int| i <= m < k ==> plain(#[trigger] b@[m]),
            decreases n - k,
        {
            k = k + 1;
        }
        let ghost before = out@;
        out.extend_from_slice(vstd::slice::slice_subrange(b, i, k));
        proof {
            let run = b@.subrange(i as int, k as int);
            assert(out@ =~= before + run);
            assert forall|m: int| 0 <= m < run.len() implies plain(#[trigger] run[m]) by {
                assert(run[m] == b@[i + m]);
            }
            lemma_escape_plain(run);
            lemma_escape_append(b@.subrange(0, i as int), run);
            assert(b@.subrange(0, i as int) + run =~= b@.subrange(0, k as int));
        }
        if k < n {
            let ghost before2 = out@;
            push_esc(out, b[k]);
            proof {
                lemma_escape_append(b@.subrange(0, k as int), seq![b@[k as int]]);
                assert(b@.subrange(0, k as int) + seq![b@[k as int]] =~= b@.subrange(0, k + 1));
                lemma_escape_one(b@[k as int]);
            }
            i = k + 1;
        } else {
            i = k;
        }
    }
    proof {
        assert(b@.subrange(0, n as int) =~= b@);
    }
}

/// Appends `b` as a quoted JSON string.
pub fn write_string(out: &mut Vec<u8>, b: &[u8])
    ensures
        final(out)@ == old(out)@ + (seq![0x22u8] + escape(b@) + seq![0x22u8]),
{
    let ghost o = out@;
    out.push(0x22);
    write_escaped(out, b);
    out.push(0x22);
    assert(out@ =~= o + (seq![0x22u8] + escape(b@) + seq![0x22u8]));
}

} // verus!

verus! {

/// `lex` followed by zero bytes.
pub open spec fn padded(lex: Seq<u8>, pad: Seq<u8>) -> bool {
    &&& lex.len() < pad.len()
    &&& pad.subrange(0, lex.len() as int) == lex
    &&& forall|k: int| lex.len() <= k < pad.len() ==> #[trigger] pad[k] == 0
}

proof fn lemma_digits_end_padded(lex: Seq<u8>, pad: Seq<u8>, p: int)
    requires
        padded(lex, pad),
        0 <= p <= lex.len(),
    ensures
        digits_end(pad, p) == digits_end(lex, p),
    decreases lex.len() - p,
{
    if p < lex.len() {
        assert(pad[p] == pad.subrange(0, lex.len() as int)[p]);
        if is_digit(lex[p]) {
            lemma_digits_end_padded(lex, pad, p + 1);
        }
    } else {
        assert(pad[p] == 0);
    }
}

proof fn lemma_digits_end_le(s: Seq<u8>, p: int)
    requires
        0 <= p,
    ensures
        p <= digits_end(s, p),
        p <= s.len() ==> digits_end(s, p) <= s.len(),
    decreases s.len() - p,
{
    if 0 <= p < s.len() && is_digit(s[p]) {
        lemma_digits_end_le(s, p + 1);
    }
}

/// A number lexeme reads the same with zero bytes after it.
proof fn lemma_number_end_padded(lex: Seq<u8>, pad: Seq<u8>)
    requires
        padded(lex, pad),
    ensures
        (number_end(pad, 0) == Some(lex.len() as int)) == (number_end(lex, 0) == Some(lex.len() as int)),
{
    let n = lex.len() as int;
    assert forall|k: int| 0 <= k < n implies #[trigger] pad[k] == lex[k] by {
        assert(pad[k] == pad.subrange(0, n)[k]);
    }
    assert forall|k: int| n <= k < pad.len() implies #[trigger] pad[k] == 0 by {}
    let j = if 0 < lex.len() && lex[0] == 0x2D { 1int } else { 0 };
    if !(0 <= j < lex.len() && is_digit(lex[j])) {
        return;
    }
    lemma_digits_end_padded(lex, pad, j);
    lemma_digits_end_le(lex, j);
    let k = if lex[j] == 0x30 { j + 1 } else { digits_end(lex, j) };
    assert(k <= n);
    if k < n && lex[k] == 0x2E {
        lemma_digits_end_padded(lex, pad, k + 1);
        lemma_digits_end_le(lex, k + 1);
    }
    let frac = if 0 <= k < lex.len() && lex[k] == 0x2E {
        let d = digits_end(lex, k + 1);
        if d == k + 1 { None } else { Some(d) }
    } else {
        Some(k)
    };
    if let Some(k2) = frac {
        assert(k2 <= n);
        if k2 + 2 <= n {
            lemma_digits_end_padded(lex, pad, k2 + 2);
        }
        if k2 + 1 <= n {
            lemma_digits_end_padded(lex, pad, k2 + 1);
        }
    }
}

/// Whether `lex` is exactly one JSON number lexeme. Numbers the writer
/// formats are short, so they are copied into a zero-padded buffer, where
/// the digit runs are found 16 bytes at a time.
#[inline]
pub fn is_number(lex: &[u8]) -> (r: bool)
    ensures
        r == (number_end(lex@, 0) == Some(lex@.len() as int)),
{
    let n = lex.len();
    if n >= 48 {
        return match crate::parser::ex_number_end(lex, 0) {
            Some(e) => e == n,
            None => false,
        };
    }
    let mut buf = [0u8; 64];
    buf[..n].copy_from_slice(lex);
    let pad = buf.as_slice();
    proof {
        assert(pad@.subrange(0, n as int) =~= lex@);
        lemma_number_end_padded(lex@, pad@);
    }
    match crate::parser::ex_number_end(pad, 0) {
        Some(e) => e == n,
        None => false,
    }
}

/// Appends `lex` if it is a JSON number lexeme, and says whether it was.
pub fn write_number(out: &mut Vec<u8>, lex: &[u8]) -> (r: bool)
    ensures
        r == (number_end(lex@, 0) == Some(lex@.len() as int)),
        final(out)@ == if r { old(out)@ + lex@ } else { old(out)@ },
{
    match crate::parser::ex_number_end(lex, 0) {
        Some(e) if e == lex.len() => {
            out.extend_from_slice(lex);
            assert(out@ =~= old(out)@ + lex@) by {
                assert forall|k: int| 0 <= k < lex@.len() implies out@[old(out)@.len() + k] == lex@[k] by {
                    assert(cloned::<u8>(lex@[k], out@[old(out)@.len() + k]));
                }
            }
            true
        },
        _ => false,
    }
}

} // verus!
