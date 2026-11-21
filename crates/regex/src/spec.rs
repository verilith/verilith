//! What a regular expression matches, as mathematics.
//!
//! `ms(r, s, i, c)` is the list of every way `r` can match the text `s`
//! starting at byte `i`, in priority order: the order a backtracking
//! matcher would find them in. Each entry is where the match ends and what
//! the capture slots hold then, starting from `c`. The match the library
//! reports (`search`) is the first entry of the list at the leftmost start
//! that has one: leftmost-first, as in Perl and RE2.
//!
//! The text is bytes. A character class matches one well-formed UTF-8
//! sequence whose code point is in the class; a byte that starts no
//! well-formed sequence matches no class. Positions are byte offsets, and a
//! match may start at any of them.
use verilith_core::utf8::*;
use vstd::prelude::*;
use verilith_text::utf::spec::*;

verus! {

/// An assertion about a position.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Look {
    /// `\A`, and `^` without `(?m)`: the start of the text.
    Start,
    /// `\z`, and `$` without `(?m)`: the end of the text.
    End,
    /// `^` with `(?m)`: the start of the text or just after a `\n`.
    StartLine,
    /// `$` with `(?m)`: the end of the text or just before a `\n`.
    EndLine,
    /// `\b`: an ASCII word character on exactly one side.
    Word,
    /// `\B`: not `\b`.
    NotWord,
}

/// A regular expression. The parser's surface syntax reduces to this:
/// `x*` is `Opt(Plus(x))`, `x{2,3}` is `Cat(x, Cat(x, Opt(Cat(x, Empty))))`.
pub ghost enum Re {
    /// Matches the empty string.
    Empty,
    /// One character whose code point is in the set.
    Char(ISet<u32>),
    Look(Look),
    /// Capture group `k`: slots `2k` and `2k + 1` get its start and end.
    Group(nat, Box<Re>),
    Cat(Box<Re>, Box<Re>),
    /// The left alternative is preferred.
    Alt(Box<Re>, Box<Re>),
    /// `x?` if the flag is set (prefers to match `x`), `x??` if not.
    Opt(Box<Re>, bool),
    /// `x+` if the flag is set (prefers more iterations), `x+?` if not.
    Plus(Box<Re>, bool),
}

/// One way to match: where it ends, and the capture slots (-1: unset).
pub ghost struct M {
    pub end: int,
    pub caps: Seq<int>,
}

/// The character at byte `i` of `s`: its code point and its length, if a
/// well-formed UTF-8 sequence (Unicode Table 3-7) starts there.
pub open spec fn dec(s: Seq<u8>, i: int) -> Option<(u32, int)> {
    if 0 <= i < s.len() {
        match utf8_len(s, i) {
            Some(l) => Some((dec8_at(s, i, l), l)),
            None => None,
        }
    } else {
        None
    }
}

pub open spec fn is_word(b: u8) -> bool {
    (0x61 <= b <= 0x7A) || (0x41 <= b <= 0x5A) || (0x30 <= b <= 0x39) || b == 0x5F
}

/// Whether assertion `k` holds at byte `i` of `s` (`0 <= i <= s.len()`).
pub open spec fn look_holds(k: Look, s: Seq<u8>, i: int) -> bool {
    match k {
        Look::Start => i == 0,
        Look::End => i == s.len(),
        Look::StartLine => i == 0 || s[i - 1] == 0x0A,
        Look::EndLine => i == s.len() || s[i] == 0x0A,
        Look::Word => (i > 0 && is_word(s[i - 1])) != (i < s.len() && is_word(s[i])),
        Look::NotWord => (i > 0 && is_word(s[i - 1])) == (i < s.len() && is_word(s[i])),
    }
}

/// Every match of `r` in `s` from byte `i` with capture slots `c`, best
/// first.
pub open spec fn ms(r: Re, s: Seq<u8>, i: int, c: Seq<int>) -> Seq<M>
    decreases r, 0int, 0int, 0nat,
{
    match r {
        Re::Empty => seq![M { end: i, caps: c }],
        Re::Char(set) => match dec(s, i) {
            Some((cp, l)) => if set.contains(cp) {
                seq![M { end: i + l, caps: c }]
            } else {
                seq![]
            },
            None => seq![],
        },
        Re::Look(k) => if look_holds(k, s, i) {
            seq![M { end: i, caps: c }]
        } else {
            seq![]
        },
        Re::Group(k, x) => close(ms(*x, s, i, c.update(2 * k as int, i)), k),
        Re::Cat(x, y) => ms_then(ms(*x, s, i, c), *y, s),
        Re::Alt(x, y) => ms(*x, s, i, c) + ms(*y, s, i, c),
        Re::Opt(x, greedy) => if greedy {
            ms(*x, s, i, c) + seq![M { end: i, caps: c }]
        } else {
            seq![M { end: i, caps: c }] + ms(*x, s, i, c)
        },
        Re::Plus(x, greedy) => first_it(ms(*x, s, i, c), *x, greedy, s, i),
    }
}

/// Each match in `rs` with group `k` closed at its end.
pub open spec fn close(rs: Seq<M>, k: nat) -> Seq<M>
    decreases rs.len(),
{
    if rs.len() == 0 {
        seq![]
    } else {
        seq![M { end: rs[0].end, caps: rs[0].caps.update(2 * k as int + 1, rs[0].end) }] + close(rs.drop_first(), k)
    }
}

/// Each match in `rs` followed by each match of `y` from where it ends.
pub open spec fn ms_then(rs: Seq<M>, y: Re, s: Seq<u8>) -> Seq<M>
    decreases y, 0int, 1int, rs.len(),
{
    if rs.len() == 0 {
        seq![]
    } else {
        ms(y, s, rs[0].end, rs[0].caps) + ms_then(rs.drop_first(), y, s)
    }
}

/// `x+` after its first iteration, which started at `i` and matched as
/// each of `rs`. If the iteration consumed nothing, the loop ends there.
/// Otherwise more iterations may follow.
pub open spec fn first_it(rs: Seq<M>, x: Re, greedy: bool, s: Seq<u8>, i: int) -> Seq<M>
    decreases x, s.len() - i + 1, 2int, rs.len(),
{
    if rs.len() == 0 {
        seq![]
    } else {
        (if i < rs[0].end <= s.len() {
            more(x, greedy, s, rs[0].end, rs[0].caps)
        } else {
            seq![rs[0]]
        }) + first_it(rs.drop_first(), x, greedy, s, i)
    }
}

/// `x+` at `j`, after an iteration that consumed something: either stop
/// here, or match `x` again, consuming at least one byte, and go on.
pub open spec fn more(x: Re, greedy: bool, s: Seq<u8>, j: int, c: Seq<int>) -> Seq<M>
    decreases x, s.len() - j + 1, 1int, 0nat,
{
    if j > s.len() {
        seq![M { end: j, caps: c }]
    } else if greedy {
        more_it(ms(x, s, j, c), x, greedy, s, j) + seq![M { end: j, caps: c }]
    } else {
        seq![M { end: j, caps: c }] + more_it(ms(x, s, j, c), x, greedy, s, j)
    }
}

/// The iterations `rs` of `x` from `j` that consumed something, each
/// followed by the rest of the loop.
pub open spec fn more_it(rs: Seq<M>, x: Re, greedy: bool, s: Seq<u8>, j: int) -> Seq<M>
    decreases x, s.len() - j + 1, 0int, rs.len(),
{
    if rs.len() == 0 {
        seq![]
    } else {
        (if j < rs[0].end <= s.len() {
            more(x, greedy, s, rs[0].end, rs[0].caps)
        } else {
            seq![]
        }) + more_it(rs.drop_first(), x, greedy, s, j)
    }
}

/// `n` capture slots, all unset.
pub open spec fn unset(n: nat) -> Seq<int> {
    Seq::new(n, |k: int| -1)
}

/// The match of `r` starting at byte `i`, if any: the best one.
pub open spec fn match_at(r: Re, s: Seq<u8>, i: int, nslots: nat) -> Option<M> {
    let l = ms(r, s, i, unset(nslots));
    if l.len() > 0 {
        Some(l[0])
    } else {
        None
    }
}

/// The match a search of `s` from byte `from` reports: the best match at
/// the first position that has one.
pub open spec fn search(r: Re, s: Seq<u8>, from: int, nslots: nat) -> Option<M>
    decreases s.len() - from + 1,
{
    if from < 0 || from > s.len() {
        None
    } else {
        match match_at(r, s, from, nslots) {
            Some(m) => Some(m),
            None => search(r, s, from + 1, nslots),
        }
    }
}

} // verus!
