#![warn(missing_docs)]
#![doc = include_str!("../README.md")]
// A linear-time regular expression engine with RE2's syntax.
// A normal build erases ghost code, so a variable, import, field or value
// used only by proofs looks unused there, and the `verus!` syntax leaves
// some redundant braces and parentheses. These lints are off in that build
// only.
#![cfg_attr(not(verus_keep_ghost), allow(unused_variables, unused_imports, dead_code, unused_braces, non_shorthand_field_patterns))]
#[doc(hidden)]
pub mod ast;
#[doc(hidden)]
pub mod capi;
#[doc(hidden)]
pub mod class;
#[doc(hidden)]
pub mod compile;
#[doc(hidden)]
pub mod cproof;
#[doc(hidden)]
pub mod data;
#[doc(hidden)]
pub mod find;
#[doc(hidden)]
pub mod lanes;
#[doc(hidden)]
pub mod dfa;
#[doc(hidden)]
pub mod lists;
#[doc(hidden)]
pub mod memo;
#[doc(hidden)]
pub mod need;
#[doc(hidden)]
pub mod parse;
#[doc(hidden)]
pub mod pike;
#[doc(hidden)]
pub mod prog;
#[doc(hidden)]
pub mod sem;
#[doc(hidden)]
pub mod skip;
#[doc(hidden)]
pub mod spec;
#[doc(hidden)]
pub mod syntax;
#[doc(hidden)]
pub mod tables;
#[doc(hidden)]
pub mod vmspec;

pub use parse::Error;

use crate::compile::*;
use crate::parse::*;
use crate::pike::*;
use crate::sem::*;
use crate::spec::*;
use crate::syntax::Pat;
use vstd::prelude::*;

// The proofs are checked once for each pointer width the crate supports:
// 64-bit on the host, and 32-bit (wasm32) with `--target
// wasm32-unknown-unknown`. A fixed width keeps the matcher's cost bounds,
// which mention usize::MAX, within the solver's reach.
#[cfg(target_pointer_width = "64")]
verus! {
global size_of usize == 8;
}

#[cfg(target_pointer_width = "32")]
verus! {
global size_of usize == 4;
}

verus! {

/// A compiled pattern.
pub struct Regex {
    /// The compiled program the matchers run.
    pub prog: prog::Prog,
    /// Group names: (name, group number).
    pub names: Vec<(Vec<u8>, usize)>,
    /// The regular expression the pattern stands for.
    pub re: Ghost<Re>,
}

impl Regex {
    /// The program is the compiled form of the regular expression.
    pub open spec fn inv(&self) -> bool {
        &&& self.prog.wf()
        &&& compiled(self.prog.sp(), self.re@)
        &&& self.prog.start == sem::ent_n(self.re@, 0, ln(self.re@) as int)
    }

    /// Compiles `pattern`. The result stands for exactly the regular
    /// expression the syntax gives the pattern; a pattern is refused only
    /// if the syntax refuses it or it is too big.
    pub fn new(pattern: &[u8]) -> (r: Result<Regex, Error>)
        ensures
            match r {
                Ok(x) => x.inv() && x.prog.nslots % 2 == 0 && syntax::parse(pattern@) == Some(
                    Pat { re: x.re@, ngroups: (x.prog.nslots / 2) as nat, names: names_v(x.names@) },
                ),
                Err(e) => e is TooBig || syntax::parse(pattern@) is None,
            },
    {
        Regex::with_limit(pattern, ast::DEFAULT_MAX_PROG)
    }

    /// Compiles `pattern` as [`Regex::new`] does, refusing it with
    /// `TooBig` if its program would be longer than `max_insts`
    /// instructions (at most 2^24 are ever allowed, as in RE2). The
    /// program takes about 32 bytes an instruction.
    pub fn with_limit(pattern: &[u8], max_insts: usize) -> (r: Result<Regex, Error>)
        ensures
            match r {
                Ok(x) => x.inv() && x.prog.nslots % 2 == 0 && x.prog.insts@.len() <= max_insts
                    && syntax::parse(pattern@) == Some(
                    Pat { re: x.re@, ngroups: (x.prog.nslots / 2) as nat, names: names_v(x.names@) },
                ),
                Err(e) => e is TooBig || syntax::parse(pattern@) is None,
            },
    {
        let p = parse::parse(pattern, max_insts)?;
        if p.classes.len() > LIM || p.ngroups > LIM || max_insts < 2 || p.ast.ln > max_insts - 2 {
            return Err(Error::TooBig);
        }
        let ghost re = p.ast.re(p.classes@);
        let prog = compile::compile(&p.ast, p.classes, p.ngroups);
        Ok(Regex { prog: prog, names: p.names, re: Ghost(re) })
    }

    /// Number of groups, counting group 0 (the whole match).
    pub fn groups(&self) -> (r: usize)
        ensures
            r == self.prog.nslots / 2,
    {
        self.prog.nslots / 2
    }

    /// Working memory for searches with this pattern, reusable between
    /// searches.
    pub fn scratch(&self) -> (sc: Scratch)
        requires
            self.inv(),
        ensures
            sc.wf(&self.prog),
    {
        Scratch::new(&self.prog)
    }

    /// Capture slots for searches with this pattern: two per group.
    pub fn slots(&self) -> (out: Vec<usize>)
        ensures
            out@.len() == self.prog.nslots,
    {
        let n = self.prog.nslots;
        let mut out: Vec<usize> = Vec::new();
        let mut k = 0;
        while k < n
            invariant
                k <= n,
                out@.len() == k,
            decreases n - k,
        {
            out.push(NONE);
            k += 1;
        }
        out
    }

    /// Searches `text` from byte `from`. Reports exactly the match the
    /// semantics gives (the leftmost, and among those the one the
    /// pattern prefers), with the start and end of each group in `out`
    /// (`usize::MAX` for a group that took no part).
    ///
    /// Also gives the number of loop iterations the search took: at most
    /// linear in the text for a fixed pattern. Memory: the thread lists
    /// in `sc` never hold more entries than the program has instructions.
    pub fn search_with(&self, text: &[u8], from: usize, sc: &mut Scratch, out: &mut Vec<usize>) -> (r: (
        bool,
        Ghost<int>,
    ))
        requires
            self.inv(),
            from <= text@.len() < usize::MAX,
            old(sc).wf(&self.prog),
            old(out)@.len() == self.prog.nslots,
        ensures
            final(sc).wf(&self.prog),
            final(out)@.len() == self.prog.nslots,
            match search(self.re@, text@, from as int, self.prog.nslots as nat) {
                Some(m) => r.0 && capv(final(out)@) == m.caps,
                None => !r.0,
            },
            r.1@ <= (text@.len() - from + 2) * step_cost(self.prog.insts@.len() as int, self.prog.nslots as int),
            final(sc).a.pcs@.len() <= self.prog.insts@.len(),
            final(sc).b.pcs@.len() <= self.prog.insts@.len(),
    {
        proof {
            lemma_search(self.prog.sp(), self.re@, text@, from as int, self.prog.nslots as nat);
        }
        let (end, steps) = run(&self.prog, text, from, sc, out);
        (end.is_some(), steps)
    }

    /// `search_with` with fresh working memory.
    pub fn captures_counted(&self, text: &[u8], from: usize) -> (r: (Option<Vec<usize>>, Ghost<int>))
        requires
            self.inv(),
            from <= text@.len() < usize::MAX,
        ensures
            match search(self.re@, text@, from as int, self.prog.nslots as nat) {
                Some(m) => r.0 matches Some(out) && capv(out@) == m.caps,
                None => r.0 is None,
            },
            r.1@ <= (text@.len() - from + 2) * step_cost(self.prog.insts@.len() as int, self.prog.nslots as int),
    {
        let mut sc = self.scratch();
        let mut out = self.slots();
        let (found, steps) = self.search_with(text, from, &mut sc, &mut out);
        if found {
            (Some(out), steps)
        } else {
            (None, steps)
        }
    }
}

} // verus!

impl Regex {
    /// The leftmost match at or after `from`: the start and end of each
    /// group, `usize::MAX` for a group that took no part.
    pub fn captures_at(&self, text: &[u8], from: usize) -> Option<Vec<usize>> {
        if from > text.len() {
            return None;
        }
        self.captures_counted(text, from).0
    }

    /// Whether the pattern matches anywhere in `text`.
    pub fn is_match(&self, text: &[u8]) -> bool {
        self.find(text).is_some()
    }

    /// The start and end of the leftmost match in `text`.
    pub fn find(&self, text: &[u8]) -> Option<(usize, usize)> {
        self.find_at(text, 0)
    }

    /// The start and end of the leftmost match at or after `from`.
    pub fn find_at(&self, text: &[u8], from: usize) -> Option<(usize, usize)> {
        self.captures_at(text, from).map(|m| (m[0], m[1]))
    }
}
