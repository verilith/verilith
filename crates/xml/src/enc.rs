//! Verified code for reading a document in any encoding this processor
//! knows (`spec::parse`): choosing the encoding, decoding UTF-16 and
//! ISO-8859-1 to UTF-8, checking US-ASCII, and then the document.
use crate::chars::*;
use crate::doc::*;
use crate::dtd::*;
use crate::ent::push_utf8;
use crate::lex::*;
use crate::spec::*;
use crate::tape::*;
#[cfg(verus_keep_ghost)]
use verilith_core::utf8::utf8_encode;
use vstd::prelude::*;

verus! {

/// `declared_enc`.
pub fn ex_declared_enc(b: &[u8]) -> (r: Option<(usize, usize)>)
    requires
        b@.len() < u32::MAX,
    ensures
        match declared_enc(b@) {
            Some((x, y)) => r matches Some((p, q)) && p == x && q == y && x <= y <= b@.len(),
            None => r is None,
        },
{
    proof {
        lemma_lits();
    }
    let n = b.len();
    let p0: usize = if n >= 3 && get(b, 0) == 0xEF && get(b, 1) == 0xBB && get(b, 2) == 0xBF {
        proof {
            assert(b@.subrange(0, 3) =~= seq![0xEFu8, 0xBB, 0xBF]);
        }
        3
    } else {
        proof {
            if n >= 3 {
                assert(b@.subrange(0, 3)[0] == b@[0]);
                assert(b@.subrange(0, 3)[1] == b@[1]);
                assert(b@.subrange(0, 3)[2] == b@[2]);
            }
        }
        0
    };
    if !(ex_has_lit(b, p0, &L_XMLDECL) && p0 + 5 < n && ex_is_ws(get(b, p0 + 5))) {
        return None;
    }
    match ex_version_info(b, p0 + 5) {
        None => None,
        Some((v, _, _)) => {
            let j = ex_ws_end(b, v);
            if j > v && ex_has_lit(b, j, &L_ENCODING) {
                match ex_enc_span(b, j) {
                    Some((_, x, y)) => Some((x, y)),
                    None => None,
                }
            } else {
                None
            }
        },
    }
}

/// `input_enc`.
pub fn ex_input_enc(b: &[u8]) -> (r: Enc)
    requires
        b@.len() < u32::MAX,
    ensures
        r == input_enc(b@),
{
    if ex_has2(b, 0, 0xFE, 0xFF) || ex_has2(b, 0, 0xFF, 0xFE) {
        return Enc::Utf16;
    }
    proof {
        lemma_enc_lits();
    }
    match ex_declared_enc(b) {
        Some((x, y)) => if ex_ci_eq(b, x, y, &L_LATIN1) {
            Enc::Latin1
        } else if ex_ci_eq(b, x, y, &L_ASCII) {
            Enc::Ascii
        } else {
            Enc::Utf8
        },
        None => Enc::Utf8,
    }
}

/// `p` followed by the decoding `o`, if there is one.
pub open spec fn cat(p: Seq<u8>, o: Option<Seq<u8>>) -> Option<Seq<u8>> {
    match o {
        Some(r) => Some(p + r),
        None => None,
    }
}

/// `utf16_dec(b, 0, le)`.
pub fn ex_utf16_dec(b: &[u8], le: bool) -> (r: Option<Vec<u8>>)
    ensures
        match utf16_dec(b@, 0, le) {
            Some(u) => r matches Some(v) && v@ == u,
            None => r is None,
        },
{
    let n = b.len();
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    proof {
        match utf16_dec(b@, 0, le) {
            Some(u) => assert(out@ + u =~= u),
            None => {},
        }
    }
    while i < n
        invariant
            i <= n,
            n == b@.len(),
            utf16_dec(b@, 0, le) == cat(out@, utf16_dec(b@, i as int, le)),
        decreases n - i,
    {
        if n - i < 2 {
            return None;
        }
        let x0 = get(b, i) as u32;
        let x1 = get(b, i + 1) as u32;
        let u: u32 = if le { x0 + x1 * 256 } else { x0 * 256 + x1 };
        if 0xD800 <= u && u <= 0xDBFF {
            if n - i < 4 {
                return None;
            }
            let y0 = get(b, i + 2) as u32;
            let y1 = get(b, i + 3) as u32;
            let w: u32 = if le { y0 + y1 * 256 } else { y0 * 256 + y1 };
            if !(0xDC00 <= w && w <= 0xDFFF) {
                return None;
            }
            let c = 0x10000 + (u - 0xD800) * 1024 + (w - 0xDC00);
            proof {
                let rest = utf16_dec(b@, i + 4, le);
                match rest {
                    Some(r) => assert(out@ + (utf8_encode(c) + r) =~= (out@ + utf8_encode(c)) + r),
                    None => {},
                }
            }
            push_utf8(&mut out, c);
            i = i + 4;
        } else if 0xDC00 <= u && u <= 0xDFFF {
            return None;
        } else {
            proof {
                let rest = utf16_dec(b@, i + 2, le);
                match rest {
                    Some(r) => assert(out@ + (utf8_encode(u) + r) =~= (out@ + utf8_encode(u)) + r),
                    None => {},
                }
            }
            push_utf8(&mut out, u);
            i = i + 2;
        }
    }
    proof {
        assert(out@ + Seq::<u8>::empty() =~= out@);
    }
    Some(out)
}

/// A run of ASCII bytes decodes to itself.
proof fn lemma_latin1_ascii(b: Seq<u8>, i: int, k: int)
    requires
        0 <= i,
        0 <= k,
        i + k <= b.len(),
        forall|q: int| i <= q < i + k ==> #[trigger] b[q] < 0x80,
    ensures
        latin1_dec(b, i) == b.subrange(i, i + k) + latin1_dec(b, i + k),
    decreases k,
{
    if k == 0 {
        assert(b.subrange(i, i) + latin1_dec(b, i) =~= latin1_dec(b, i));
    } else {
        lemma_latin1_ascii(b, i + 1, k - 1);
        assert(b[i] < 0x80);
        assert(utf8_encode(b[i] as u32) =~= seq![b[i]]);
        assert(b.subrange(i, i + k) =~= seq![b[i]] + b.subrange(i + 1, i + k));
        assert(seq![b[i]] + (b.subrange(i + 1, i + k) + latin1_dec(b, i + k)) =~= (seq![b[i]] + b.subrange(i + 1, i
            + k)) + latin1_dec(b, i + k));
    }
}

/// `latin1_dec(b, 0)`.
pub fn ex_latin1_dec(b: &[u8]) -> (r: Vec<u8>)
    ensures
        r@ == latin1_dec(b@, 0),
{
    let n = b.len();
    let mut out: Vec<u8> = Vec::with_capacity(n);
    let mut i: usize = 0;
    proof {
        assert(out@ + latin1_dec(b@, 0) =~= latin1_dec(b@, 0));
    }
    while i < n
        invariant
            i <= n,
            n == b@.len(),
            out@ + latin1_dec(b@, i as int) == latin1_dec(b@, 0),
        decreases n - i,
    {
        if n - i >= 16 {
            let k = crate::scan::ascii_run16(b, i);
            if k > 0 {
                proof {
                    lemma_latin1_ascii(b@, i as int, k as int);
                    assert(out@ + (b@.subrange(i as int, i + k) + latin1_dec(b@, i + k)) =~= (out@ + b@.subrange(
                        i as int,
                        i + k,
                    )) + latin1_dec(b@, i + k));
                }
                verilith_core::prims::extend(&mut out, vstd::slice::slice_subrange(b, i, i + k));
                i = i + k;
                continue;
            }
        }
        let c = get(b, i);
        proof {
            let e = utf8_encode(c as u32);
            assert(out@ + (e + latin1_dec(b@, i + 1)) =~= (out@ + e) + latin1_dec(b@, i + 1));
        }
        if c < 0x80 {
            proof {
                assert(utf8_encode(c as u32) =~= seq![c]);
            }
            out.push(c);
        } else {
            push_utf8(&mut out, c as u32);
        }
        i = i + 1;
    }
    proof {
        assert(out@ + Seq::<u8>::empty() =~= out@);
    }
    out
}

/// `decode_input`: `Some(None)` when the input is already the text.
pub fn ex_decode_input(b: &[u8], enc: Enc) -> (r: Option<Option<Vec<u8>>>)
    requires
        b@.len() < u32::MAX,
        enc == input_enc(b@),
    ensures
        match decode_input(b@) {
            Some(u) => r matches Some(x) && match x {
                Some(v) => v@ == u,
                None => u == b@,
            },
            None => r is None,
        },
{
    match enc {
        Enc::Utf16 => {
            let le = get(b, 0) == 0xFF;
            match ex_utf16_dec(b, le) {
                Some(v) => Some(Some(v)),
                None => None,
            }
        },
        Enc::Latin1 => Some(Some(ex_latin1_dec(b))),
        Enc::Ascii => {
            let mut k: usize = 0;
            while k < b.len()
                invariant
                    k <= b@.len(),
                    enc == input_enc(b@),
                    enc == Enc::Ascii,
                    forall|q: int| 0 <= q < k ==> b@[q] < 0x80,
                decreases b@.len() - k,
            {
                if get(b, k) >= 0x80 {
                    proof {
                        assert(b@[k as int] >= 0x80);
                        assert(!(forall|q: int| 0 <= q < b@.len() ==> b@[q] < 0x80));
                    }
                    return None;
                }
                k = k + 1;
            }
            Some(None)
        },
        Enc::Utf8 => Some(None),
    }
}

} // verus!

verus! {

/// `parse`: the tape of the document `b`, the text decoded to UTF-8 if it
/// was not UTF-8 already (`None` when `b` is the text), and what its DTD
/// declares.
pub fn ex_parse(b: &[u8], tape: &mut Tape) -> (r: Option<(Option<Vec<u8>>, DtdOut)>)
    ensures
        match parse(b@) {
            Some((u, t)) => r matches Some((x, d)) && final(tape)@ == t && match x {
                Some(v) => v@ == u,
                None => u == b@,
            },
            None => r is None,
        },
        r matches Some((x, d)) ==> match x {
            Some(v) => out_wf(v@, &d) && final(tape)@.len() <= v@.len(),
            None => out_wf(b@, &d) && final(tape)@.len() <= b@.len(),
        },
{
    if b.len() >= 0xFFFF_FFFF {
        return None;
    }
    let enc = ex_input_enc(b);
    match ex_decode_input(b, enc) {
        None => None,
        Some(None) => match ex_document(b, tape, enc) {
            Some(d) => Some((None, d)),
            None => None,
        },
        Some(Some(v)) => match ex_document(v.as_slice(), tape, enc) {
            Some(d) => Some((Some(v), d)),
            None => None,
        },
    }
}

} // verus!
