//! The trusted specification of well-formed Type 2 charstrings
//! ([`wf_charstrings`]), written from Adobe Technical Note #5177.
//!
//! A charstring is a small stack program. This file says what it means
//! for every glyph's program to run cleanly: every byte decodes, the
//! operand stack never holds more than 48 numbers, every operator finds
//! the operands it takes, every subroutine call names a subroutine that
//! exists, calls nest at most 10 deep, hint masks have the bytes the
//! declared stems need, and the program ends with `endchar`. Running the
//! programs of the whole font takes at most [`MAX_CS_OPS`] operators, so
//! a consumer's work is bounded too.
//!
//! The rules follow what OTS accepts. Like OTS, the specification does not
//! track the values that arithmetic operators compute, so a subroutine
//! number must be written directly before the call, and the operators that
//! index the stack or the transient array by a computed number (`put`,
//! `get`, `index`, `roll`) and `random` are not allowed.
use crate::spec::*;
use crate::spec_cff::*;
use vstd::prelude::*;

verus! {

/// What stands on the stack for a number whose value is not tracked: a
/// 16.16 fixed-point operand, or the result of an arithmetic operator.
pub const UNK: i32 = 0x7FFF_FFFF;

/// The most operators the charstrings of one font may execute in all.
pub const MAX_CS_OPS: u32 = 0x400_0000;

/// One charstring token.
pub enum CsTok {
    /// An operand and where the next token starts.
    Num(i32, int),
    /// An operator (two-byte operators `12 x` are numbered `0xC00 + x`)
    /// and where the next token starts.
    Op(int, int),
    Bad,
}

/// The token at `p` of a charstring that ends at `end` (with `p < end`).
pub open spec fn cs_tok(t: Seq<u8>, p: int, end: int) -> CsTok {
    let b = t[p];
    if b == 12 {
        if p + 2 <= end {
            CsTok::Op(0xC00 + t[p + 1], p + 2)
        } else {
            CsTok::Bad
        }
    } else if b == 28 {
        if p + 3 <= end {
            CsTok::Num(i16_at(t, p + 1) as i32, p + 3)
        } else {
            CsTok::Bad
        }
    } else if b <= 31 {
        CsTok::Op(b as int, p + 1)
    } else if b <= 246 {
        CsTok::Num((b - 139) as i32, p + 1)
    } else if b <= 250 {
        if p + 2 <= end {
            CsTok::Num(((b - 247) * 256 + t[p + 1] + 108) as i32, p + 2)
        } else {
            CsTok::Bad
        }
    } else if b <= 254 {
        if p + 2 <= end {
            CsTok::Num((-(b - 251) * 256 - t[p + 1] - 108) as i32, p + 2)
        } else {
            CsTok::Bad
        }
    } else {
        if p + 5 <= end {
            CsTok::Num(UNK, p + 5)
        } else {
            CsTok::Bad
        }
    }
}

/// The state of a running charstring.
pub struct Cs {
    pub stack: Seq<i32>,
    /// The glyph's optional width operand can no longer appear.
    pub width: bool,
    /// Stem hints declared so far.
    pub stems: int,
    /// How far the hint operators have got: 0 while horizontal stems may
    /// be declared, 1 after a vertical stem, 2 after a counter mask, 3
    /// once drawing or hint masks have begun.
    pub hint: int,
    /// Operators executed so far, over the whole font.
    pub ops: int,
}

pub open spec fn cs_init(ops: int) -> Cs {
    Cs { stack: Seq::empty(), width: false, stems: 0, hint: 0, ops }
}

/// The effect of operator `op`, other than a call, `return` or `endchar`,
/// on `st`: the state after it and the number of mask bytes that follow
/// it. `None` if the operator is not allowed or lacks its operands.
pub open spec fn cs_op(op: int, st: Cs) -> Option<(Cs, int)> {
    let n = st.stack.len() as int;
    let w = st.width;
    let s = st.stack;
    let clr = Cs { stack: Seq::empty(), ..st };
    if op == 1 || op == 18 {
        // hstem, hstemhm
        if n >= 2 && st.hint <= 0 && (n % 2 == 0 || !w) && st.stems + n / 2 <= 96 {
            Some((Cs { stems: st.stems + n / 2, width: true, ..clr }, 0))
        } else {
            None
        }
    } else if op == 3 || op == 23 {
        // vstem, vstemhm
        if n >= 2 && st.hint <= 1 && (n % 2 == 0 || !w) && st.stems + n / 2 <= 96 {
            Some((Cs { stems: st.stems + n / 2, width: true, hint: 1, ..clr }, 0))
        } else {
            None
        }
    } else if op == 21 {
        // rmoveto
        if n == 2 || (!w && n == 3) {
            Some((Cs { width: true, hint: 3, ..clr }, 0))
        } else {
            None
        }
    } else if op == 4 || op == 22 {
        // vmoveto, hmoveto
        if n == 1 || (!w && n == 2) {
            Some((Cs { width: true, hint: 3, ..clr }, 0))
        } else {
            None
        }
    } else if op == 19 || op == 20 {
        // hintmask, cntrmask: operands left on the stack are vertical
        // stems; the mask has one bit for each stem.
        let stems = if n == 0 || (!w && n == 1) {
            st.stems
        } else {
            st.stems + n / 2
        };
        if (n == 0 || !w || n % 2 == 0) && 1 <= stems <= 96 && (op == 19 || st.hint <= 2) {
            Some(
                (
                    Cs {
                        stems,
                        width: true,
                        hint: if op == 19 {
                            3
                        } else {
                            2
                        },
                        ..clr
                    },
                    (stems + 7) / 8,
                ),
            )
        } else {
            None
        }
    } else if op == 5 {
        // rlineto
        if w && n >= 2 && n % 2 == 0 {
            Some((clr, 0))
        } else {
            None
        }
    } else if op == 6 || op == 7 {
        // hlineto, vlineto
        if w && n >= 1 {
            Some((clr, 0))
        } else {
            None
        }
    } else if op == 8 {
        // rrcurveto
        if w && n >= 6 && n % 6 == 0 {
            Some((clr, 0))
        } else {
            None
        }
    } else if op == 24 {
        // rcurveline
        if w && n >= 8 && (n - 2) % 6 == 0 {
            Some((clr, 0))
        } else {
            None
        }
    } else if op == 25 {
        // rlinecurve
        if w && n >= 8 && n % 2 == 0 {
            Some((clr, 0))
        } else {
            None
        }
    } else if op == 26 || op == 27 {
        // vvcurveto, hhcurveto
        if w && n >= 4 && (n % 4 == 0 || n % 4 == 1) {
            Some((clr, 0))
        } else {
            None
        }
    } else if op == 30 || op == 31 {
        // vhcurveto, hvcurveto
        if w && n >= 4 && (n % 8 == 0 || n % 8 == 1 || n % 8 == 4 || n % 8 == 5) {
            Some((clr, 0))
        } else {
            None
        }
    } else if op == 0xC00 {
        // dotsection
        if n == 0 {
            Some((st, 0))
        } else {
            None
        }
    } else if op == 0xC03 || op == 0xC04 || op == 0xC0A || op == 0xC0B || op == 0xC0C || op == 0xC0F
        || op == 0xC18 {
        // and, or, add, sub, div, eq, mul
        if n >= 2 {
            Some((Cs { stack: s.drop_last().drop_last().push(UNK), ..st }, 0))
        } else {
            None
        }
    } else if op == 0xC05 || op == 0xC09 || op == 0xC0E || op == 0xC1A {
        // not, abs, neg, sqrt
        if n >= 1 {
            Some((Cs { stack: s.drop_last().push(UNK), ..st }, 0))
        } else {
            None
        }
    } else if op == 0xC12 {
        // drop
        if n >= 1 {
            Some((Cs { stack: s.drop_last(), ..st }, 0))
        } else {
            None
        }
    } else if op == 0xC16 {
        // ifelse
        if n >= 4 {
            Some(
                (
                    Cs {
                        stack: s.drop_last().drop_last().drop_last().drop_last().push(UNK),
                        ..st
                    },
                    0,
                ),
            )
        } else {
            None
        }
    } else if op == 0xC1B {
        // dup
        if 1 <= n < 48 {
            Some((Cs { stack: s.drop_last().push(UNK).push(UNK), ..st }, 0))
        } else {
            None
        }
    } else if op == 0xC1C {
        // exch
        if n >= 2 {
            Some((Cs { stack: s.drop_last().drop_last().push(UNK).push(UNK), ..st }, 0))
        } else {
            None
        }
    } else if op == 0xC22 {
        // hflex
        if w && n == 7 {
            Some((clr, 0))
        } else {
            None
        }
    } else if op == 0xC23 {
        // flex
        if w && n == 13 {
            Some((clr, 0))
        } else {
            None
        }
    } else if op == 0xC24 {
        // hflex1
        if w && n == 9 {
            Some((clr, 0))
        } else {
            None
        }
    } else if op == 0xC25 {
        // flex1
        if w && n == 11 {
            Some((clr, 0))
        } else {
            None
        }
    } else {
        None
    }
}

/// What is added to a subroutine number to get its place in an INDEX of
/// `count` subroutines.
pub open spec fn subr_bias(count: int) -> int {
    if count < 1240 {
        107
    } else if count < 33900 {
        1131
    } else {
        32768
    }
}

/// The bytes (start, end) of the subroutine that the number `top` names in
/// the subroutine INDEX at `idx` (`idx` is 0 when there is no INDEX).
/// `None` if there is no such subroutine or it is longer than 65535 bytes.
pub open spec fn cs_subr(t: Seq<u8>, idx: int, top: i32) -> Option<(int, int)> {
    let count = if idx == 0 {
        0
    } else {
        index_count(t, idx)
    };
    let k = top + subr_bias(count);
    if top != UNK && 0 <= k < count && index_off(t, idx, k + 1) - index_off(t, idx, k) <= 65535 {
        Some((index_base(t, idx) + index_off(t, idx, k), index_base(t, idx) + index_off(t, idx, k + 1)))
    } else {
        None
    }
}

/// How running a charstring, or a subroutine, ends.
pub enum CsRes {
    Fail,
    /// A subroutine returned, leaving this state.
    Ret(Cs),
    /// The glyph ended with `endchar`.
    End(Cs),
}

/// Runs the charstring bytes `p..end` from state `st`, `depth` calls deep.
/// `g` is the global subroutine INDEX and `l` the local one (0 for none).
/// Running off the end of the bytes is a failure: a charstring ends with
/// `endchar` and a subroutine with `return` or `endchar`.
pub open spec fn cs_run(t: Seq<u8>, g: int, l: int, p: int, end: int, depth: int, st: Cs) -> CsRes
    decreases 10 - depth, end - p,
{
    if depth < 0 || depth > 10 || p < 0 || p >= end {
        CsRes::Fail
    } else {
        match cs_tok(t, p, end) {
            CsTok::Bad => CsRes::Fail,
            CsTok::Num(v, q) => if st.stack.len() < 48 && p < q {
                cs_run(t, g, l, q, end, depth, Cs { stack: st.stack.push(v), ..st })
            } else {
                CsRes::Fail
            },
            CsTok::Op(op, q) => if st.ops >= MAX_CS_OPS || q <= p {
                CsRes::Fail
            } else {
                let st1 = Cs { ops: st.ops + 1, ..st };
                if op == 11 {
                    CsRes::Ret(st1)
                } else if op == 14 {
                    CsRes::End(st1)
                } else if op == 10 || op == 29 {
                    if st.stack.len() == 0 || depth >= 10 {
                        CsRes::Fail
                    } else {
                        match cs_subr(
                            t,
                            if op == 10 {
                                l
                            } else {
                                g
                            },
                            st.stack.last(),
                        ) {
                            None => CsRes::Fail,
                            Some((a, b)) => match cs_run(
                                t,
                                g,
                                l,
                                a,
                                b,
                                depth + 1,
                                Cs { stack: st.stack.drop_last(), ..st1 },
                            ) {
                                CsRes::Ret(st2) => cs_run(t, g, l, q, end, depth, st2),
                                r => r,
                            },
                        }
                    }
                } else {
                    match cs_op(op, st1) {
                        Some((st2, skip)) => if skip >= 0 && q + skip <= end {
                            cs_run(t, g, l, q + skip, end, depth, st2)
                        } else {
                            CsRes::Fail
                        },
                        None => CsRes::Fail,
                    }
                }
            },
        }
    }
}

/// The local subroutine INDEX that the Private DICT at `off` (of `size`
/// bytes) names, or 0 if it names none.
pub open spec fn priv_subrs(t: Seq<u8>, size: int, off: int) -> int {
    match priv_read(t.subrange(off, off + size)) {
        Some(d) => if d.has_subrs {
            off + d.subrs
        } else {
            0
        },
        None => 0,
    }
}

/// The local subroutine INDEX of Font DICT `f` of the FDArray at `fa`.
pub open spec fn fd_subrs(t: Seq<u8>, fa: int, f: int, sm: int) -> int {
    match dict_read(index_obj(t, fa, f), true, sm, t.len() as int) {
        Some(d) => priv_subrs(t, d.priv_size, d.priv_off),
        None => 0,
    }
}

/// The Font DICT that the format 3 FDSelect at `p` gives glyph `i`: that
/// of the last range, at or before range `k`, that starts at or before
/// `i`.
pub open spec fn fds3_fd(t: Seq<u8>, p: int, k: int, i: int) -> int
    decreases k,
{
    if k <= 0 || u16_at(t, p + 3 + 3 * k) <= i {
        t[p + 3 + 3 * k + 2] as int
    } else {
        fds3_fd(t, p, k - 1, i)
    }
}

/// The Font DICT that the FDSelect at `p` gives glyph `i`.
pub open spec fn glyph_fd(t: Seq<u8>, p: int, i: int) -> int {
    if t[p] == 0 {
        t[p + 1 + i] as int
    } else {
        fds3_fd(t, p, u16_at(t, p + 1) - 1, i)
    }
}

/// The local subroutine INDEX that glyph `i` uses (0 for none): the one
/// of its Font DICT in a CID-keyed font, the font's one otherwise.
pub open spec fn glyph_lsubrs(t: Seq<u8>, top: Dict, i: int, sm: int) -> int {
    if top.cid {
        fd_subrs(t, top.fdarray, glyph_fd(t, top.fdselect, i), sm)
    } else {
        priv_subrs(t, top.priv_size, top.priv_off)
    }
}

/// Runs the charstring of glyph `i` after `ops` operators have been spent
/// on the glyphs before it; gives the operators spent after it, or `None`
/// if the charstring is longer than 65535 bytes or does not run cleanly
/// to an `endchar`.
pub open spec fn cs_glyph(t: Seq<u8>, top: Dict, g: int, i: int, ops: int, sm: int) -> Option<int> {
    let cs = top.charstrings;
    let a = index_base(t, cs) + index_off(t, cs, i);
    let b = index_base(t, cs) + index_off(t, cs, i + 1);
    if b - a > 65535 {
        None
    } else {
        match cs_run(t, g, glyph_lsubrs(t, top, i, sm), a, b, 0, cs_init(ops)) {
            CsRes::End(st) => Some(st.ops),
            _ => None,
        }
    }
}

/// Runs the charstrings of glyphs 0 to `n - 1` in turn.
pub open spec fn cs_all(t: Seq<u8>, top: Dict, g: int, n: int, sm: int) -> Option<int>
    decreases n,
{
    if n <= 0 {
        Some(0)
    } else {
        match cs_all(t, top, g, n - 1, sm) {
            Some(ops) => cs_glyph(t, top, g, n - 1, ops, sm),
            None => None,
        }
    }
}

/// Every one of the `ng` charstrings of the font with Top DICT `top` and
/// global subroutine INDEX at `g` runs cleanly. (`sm`, the largest string
/// id, is only needed to read the Font DICTs.)
pub open spec fn wf_charstrings(t: Seq<u8>, top: Dict, g: int, ng: int, sm: int) -> bool {
    cs_all(t, top, g, ng, sm) is Some
}

} // verus!
