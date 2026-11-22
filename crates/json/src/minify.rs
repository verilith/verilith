//! `cJSON_Minify`: removes whitespace and `//` and `/* */` comments from a
//! NUL-terminated buffer, in place, as cJSON 1.7.19 does. Strings are
//! copied as they are, with cJSON's rule that a backslash followed by a
//! quote does not end one.
//!
//! `spec_minify` is the out-of-place definition; `minify_in_place` is
//! proven to leave exactly that in the front of the buffer, followed by a
//! NUL, without reading or writing past the buffer.
use vstd::prelude::*;

verus! {

pub open spec fn is_ws(c: u8) -> bool {
    c == 0x20 || c == 0x09 || c == 0x0d || c == 0x0a
}

/// The byte at `i`, or 0 past the end.
pub open spec fn at(s: Seq<u8>, i: int) -> u8 {
    if 0 <= i < s.len() {
        s[i]
    } else {
        0
    }
}

/// After `//`: where the comment ends (past its newline, or at the NUL).
pub open spec fn skip_line(s: Seq<u8>, i: int) -> int
    decreases s.len() - i,
{
    if i < 0 || i >= s.len() || s[i] == 0 {
        i
    } else if s[i] == 0x0a {
        i + 1
    } else {
        skip_line(s, i + 1)
    }
}

/// After `/*`: where the comment ends (past its `*/`, or at the NUL).
pub open spec fn skip_block(s: Seq<u8>, i: int) -> int
    decreases s.len() - i,
{
    if i < 0 || i >= s.len() || s[i] == 0 {
        i
    } else if s[i] == 0x2a && at(s, i + 1) == 0x2f {
        i + 2
    } else {
        skip_block(s, i + 1)
    }
}

/// After an opening quote: the string's bytes up to and including its
/// closing quote (or up to the NUL), and where they end.
pub open spec fn str_body(s: Seq<u8>, i: int) -> (int, Seq<u8>)
    decreases s.len() - i,
{
    if i < 0 || i >= s.len() || s[i] == 0 {
        (i, Seq::empty())
    } else if s[i] == 0x22 {
        (i + 1, seq![0x22u8])
    } else if s[i] == 0x5c && at(s, i + 1) == 0x22 {
        let r = str_body(s, i + 2);
        (r.0, seq![0x5cu8, 0x22u8] + r.1)
    } else {
        let r = str_body(s, i + 1);
        (r.0, seq![s[i]] + r.1)
    }
}

/// The minified text from `i` to the NUL.
pub open spec fn spec_minify(s: Seq<u8>, i: int) -> Seq<u8>
    decreases s.len() - i,
{
    if i < 0 || i >= s.len() || s[i] == 0 {
        Seq::empty()
    } else if is_ws(s[i]) {
        spec_minify(s, i + 1)
    } else if s[i] == 0x2f && at(s, i + 1) == 0x2f {
        if i < skip_line(s, i + 2) <= s.len() { spec_minify(s, skip_line(s, i + 2)) } else { Seq::empty() }
    } else if s[i] == 0x2f && at(s, i + 1) == 0x2a {
        if i < skip_block(s, i + 2) <= s.len() { spec_minify(s, skip_block(s, i + 2)) } else { Seq::empty() }
    } else if s[i] == 0x2f {
        spec_minify(s, i + 1)
    } else if s[i] == 0x22 {
        let r = str_body(s, i + 1);
        if i < r.0 <= s.len() { seq![0x22u8] + r.1 + spec_minify(s, r.0) } else { Seq::empty() }
    } else {
        seq![s[i]] + spec_minify(s, i + 1)
    }
}

proof fn lemma_skip_line(s: Seq<u8>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        i <= skip_line(s, i) <= s.len(),
    decreases s.len() - i,
{
    if i < s.len() && s[i] != 0 && s[i] != 0x0a {
        lemma_skip_line(s, i + 1);
    }
}

proof fn lemma_skip_block(s: Seq<u8>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        i <= skip_block(s, i) <= s.len(),
    decreases s.len() - i,
{
    if i < s.len() && s[i] != 0 && !(s[i] == 0x2a && at(s, i + 1) == 0x2f) {
        lemma_skip_block(s, i + 1);
    }
}

proof fn lemma_str_body(s: Seq<u8>, i: int)
    requires
        0 <= i <= s.len(),
        s.len() > 0,
        s.last() == 0,
    ensures
        i <= str_body(s, i).0 <= s.len(),
        str_body(s, i).1.len() <= str_body(s, i).0 - i,
    decreases s.len() - i,
{
    if i < s.len() && s[i] != 0 && s[i] != 0x22 {
        if s[i] == 0x5c && at(s, i + 1) == 0x22 {
            lemma_str_body(s, i + 2);
        } else {
            lemma_str_body(s, i + 1);
        }
    }
}

/// Minifies the NUL-terminated text in `buf` in place; returns the length
/// of the result, which is followed by a NUL.
pub fn minify_in_place(buf: &mut [u8]) -> (n: usize)
    requires
        old(buf)@.len() > 0,
        old(buf)@.last() == 0,
    ensures
        final(buf)@.len() == old(buf)@.len(),
        n < final(buf)@.len(),
        final(buf)@.subrange(0, n as int) == spec_minify(old(buf)@, 0),
        final(buf)@[n as int] == 0,
{
    let ghost s = buf@;
    let len = buf.len();
    let mut i: usize = 0;
    let mut o: usize = 0;
    assert(buf@.subrange(0, 0) + spec_minify(s, 0) =~= spec_minify(s, 0));
    // Bytes from `i` on are still the input's (the output never passes
    // the input); the output so far, then the rest minified, is the whole
    // result.
    while buf[i] != 0
        invariant
            buf@.len() == len == s.len(),
            s.last() == 0,
            o <= i < len,
            forall|k: int| i <= k < len ==> #[trigger] buf@[k] == s[k],
            buf@.subrange(0, o as int) + spec_minify(s, i as int) == spec_minify(s, 0),
        decreases len - i,
    {
        let ghost i0 = i as int;
        let ghost out0 = buf@.subrange(0, o as int);
        let c = buf[i];
        // Not the NUL, so not the last byte.
        assert(i + 1 < len);
        let d = buf[i + 1];
        assert(d == at(s, i + 1));
        if c == 0x20 || c == 0x09 || c == 0x0d || c == 0x0a {
            i += 1;
        } else if c == 0x2f && d == 0x2f {
            let ghost j0 = i0 + 2;
            let ghost b0 = buf@;
            i += 2;
            while buf[i] != 0
                invariant_except_break
                    skip_line(s, i as int) == skip_line(s, j0),
                invariant
                    buf@ == b0,
                    buf@.len() == len == s.len(),
                    s.last() == 0,
                    o <= j0 <= i < len,
                    forall|k: int| j0 <= k < len ==> #[trigger] buf@[k] == s[k],
                ensures
                    buf@ == b0,
                    j0 <= i < len,
                    i == skip_line(s, j0),
                decreases len - i,
            {
                let e = buf[i];
                i += 1;
                if e == 0x0a {
                    break;
                }
            }
        } else if c == 0x2f && d == 0x2a {
            let ghost j0 = i0 + 2;
            let ghost b0 = buf@;
            i += 2;
            while buf[i] != 0
                invariant_except_break
                    skip_block(s, i as int) == skip_block(s, j0),
                invariant
                    buf@ == b0,
                    buf@.len() == len == s.len(),
                    s.last() == 0,
                    o <= j0 <= i < len,
                    forall|k: int| j0 <= k < len ==> #[trigger] buf@[k] == s[k],
                ensures
                    buf@ == b0,
                    j0 <= i < len,
                    i == skip_block(s, j0),
                decreases len - i,
            {
                assert(i + 1 < len);
                assert(buf@[i + 1] == at(s, i + 1));
                if buf[i] == 0x2a && buf[i + 1] == 0x2f {
                    i += 2;
                    break;
                }
                i += 1;
            }
        } else if c == 0x2f {
            i += 1;
        } else if c == 0x22 {
            let ghost j0 = i0 + 1;
            buf[o] = 0x22;
            i += 1;
            o += 1;
            let ghost mut done: Seq<u8> = Seq::empty();
            proof {
                assert(buf@.subrange(0, o as int) =~= out0 + seq![0x22u8] + done);
                assert(done + str_body(s, j0).1 =~= str_body(s, j0).1);
            }
            // `done`: the string's bytes copied so far.
            while buf[i] != 0
                invariant_except_break
                    buf@.subrange(0, o as int) == out0 + seq![0x22u8] + done,
                    done + str_body(s, i as int).1 == str_body(s, j0).1,
                    str_body(s, i as int).0 == str_body(s, j0).0,
                invariant
                    buf@.len() == len == s.len(),
                    s.last() == 0,
                    o <= i < len,
                    j0 <= i,
                    forall|k: int| i <= k < len ==> #[trigger] buf@[k] == s[k],
                ensures
                    buf@.len() == len,
                    o <= i < len,
                    forall|k: int| i <= k < len ==> #[trigger] buf@[k] == s[k],
                    buf@.subrange(0, o as int) == out0 + seq![0x22u8] + str_body(s, j0).1,
                    i == str_body(s, j0).0,
                decreases len - i,
            {
                let e = buf[i];
                assert(i + 1 < len);
                let f = buf[i + 1];
                assert(f == at(s, i + 1));
                let ghost before = buf@;
                buf[o] = e;
                if e == 0x22 {
                    proof {
                        assert(buf@.subrange(0, o + 1) =~= before.subrange(0, o as int) + seq![0x22u8]);
                        assert(done + seq![0x22u8] =~= str_body(s, j0).1);
                        done = done + seq![0x22u8];
                    }
                    i += 1;
                    o += 1;
                    break;
                }
                if e == 0x5c && f == 0x22 {
                    buf[o + 1] = 0x22;
                    proof {
                        assert(buf@.subrange(0, o + 2) =~= before.subrange(0, o as int) + seq![0x5cu8, 0x22u8]);
                        assert((done + seq![0x5cu8, 0x22u8]) + str_body(s, i + 2).1 =~= done + str_body(s, i as int).1);
                        done = done + seq![0x5cu8, 0x22u8];
                    }
                    i += 2;
                    o += 2;
                } else {
                    proof {
                        assert(buf@.subrange(0, o + 1) =~= before.subrange(0, o as int) + seq![e]);
                        assert((done + seq![e]) + str_body(s, i + 1).1 =~= done + str_body(s, i as int).1);
                        done = done + seq![e];
                    }
                    i += 1;
                    o += 1;
                }
            }
            proof {
                lemma_str_body(s, j0);
                let r = str_body(s, j0);
                assert(spec_minify(s, i0) == seq![0x22u8] + r.1 + spec_minify(s, r.0));
                assert(out0 + seq![0x22u8] + r.1 + spec_minify(s, i as int) =~= out0 + (seq![0x22u8] + r.1 + spec_minify(s, r.0)));
            }
        } else {
            buf[o] = c;
            proof {
                assert(buf@.subrange(0, o + 1) =~= out0 + seq![c]);
                assert(out0 + seq![c] + spec_minify(s, i0 + 1) =~= out0 + (seq![c] + spec_minify(s, i0 + 1)));
            }
            i += 1;
            o += 1;
        }
    }
    let ghost out = buf@.subrange(0, o as int);
    buf[o] = 0;
    proof {
        assert(spec_minify(s, i as int) == Seq::<u8>::empty());
        assert(out + Seq::<u8>::empty() =~= out);
        assert(buf@.subrange(0, o as int) =~= out);
    }
    o
}

} // verus!
