//! The syntax tree the parser builds and the compiler reads.
use crate::class::Class;
use crate::sem::*;
use crate::spec::*;
use vstd::prelude::*;

pub use crate::spec::Look;

verus! {

/// The most instructions any tree may compile to, whatever limit the caller
/// sets: RE2's ceiling too (2^24). `Regex::with_limit` takes a lower one.
pub const MAX_PROG: usize = 0x100_0000;

/// The instruction limit `Regex::new` uses: 2^18, what RE2's default
/// `max_mem` of 8 MiB comes to at 32 bytes an instruction.
pub const DEFAULT_MAX_PROG: usize = 0x4_0000;

pub const MAX_HEIGHT: usize = 4096;

pub const THRU: usize = usize::MAX;

pub enum Node {
    Empty,
    /// One character of class number `.0`.
    Char(usize),
    Look(Look),
    Group(usize, Box<Ast>),
    Cat(Box<Ast>, Box<Ast>),
    Alt(Box<Ast>, Box<Ast>),
    /// `x?`; greedy if the flag is set.
    Opt(Box<Ast>, bool),
    /// `x+`; greedy if the flag is set.
    Plus(Box<Ast>, bool),
}

pub struct Ast {
    pub node: Node,
    /// Instructions in the normal copy.
    pub ln: usize,
    /// Instructions in the no-progress copy.
    pub lz: usize,
    /// Where the normal copy is entered, from its base; `THRU` if at its exit.
    pub en: usize,
    /// The same for the no-progress copy.
    pub ez: usize,
    /// Height of the tree.
    pub h: usize,
    /// The largest product of nested `{n,m}` counts.
    pub rep: usize,
}

/// Where the normal copy of `r` is entered, from its base; `None` if at
/// its exit.
pub open spec fn eno(r: Re) -> Option<int>
    decreases r,
{
    match r {
        Re::Empty => None,
        Re::Cat(x, y) => match eno(*x) {
            Some(k) => Some(k),
            None => match eno(*y) {
                Some(k) => Some(ln(*x) + k),
                None => None,
            },
        },
        Re::Plus(x, _) => match ezo(*x) {
            Some(k) => Some(ln(*x) + 1 + lz(*x) + k),
            None => None,
        },
        _ => Some(0),
    }
}

/// The same for the no-progress copy.
pub open spec fn ezo(r: Re) -> Option<int>
    decreases r,
{
    match r {
        Re::Empty => None,
        Re::Cat(x, y) => match ezo(*x) {
            Some(k) => Some(k),
            None => match ezo(*y) {
                Some(k) => Some(lz(*x) + k),
                None => None,
            },
        },
        Re::Plus(x, _) => ezo(*x),
        _ => Some(0),
    }
}

pub proof fn lemma_ent(r: Re, b: int, e: int)
    ensures
        ent_n(r, b, e) == match eno(r) {
            Some(k) => b + k,
            None => e,
        },
        ent_z(r, b, e) == match ezo(r) {
            Some(k) => b + k,
            None => e,
        },
        eno(r) matches Some(k) ==> 0 <= k < ln(r),
        ezo(r) matches Some(k) ==> 0 <= k < lz(r),
    decreases r,
{
    match r {
        Re::Cat(x, y) => {
            lemma_ent(*y, b + ln(*x), e);
            lemma_ent(*y, b + lz(*x), e);
            lemma_ent(*x, b, ent_n(*y, b + ln(*x), e));
            lemma_ent(*x, b, ent_z(*y, b + lz(*x), e));
        },
        Re::Plus(x, _) => {
            lemma_ent(*x, b + ln(*x) + 1 + lz(*x), e);
            lemma_ent(*x, b, e);
        },
        _ => {},
    }
}

pub open spec fn fo(v: usize) -> Option<int> {
    if v == THRU {
        None
    } else {
        Some(v as int)
    }
}

impl Ast {
    /// The regular expression this tree stands for, given the classes.
    pub open spec fn re(self, cl: Seq<Class>) -> Re
        decreases self,
    {
        match self.node {
            Node::Empty => Re::Empty,
            Node::Char(c) => Re::Char(cl[c as int].set()),
            Node::Look(k) => Re::Look(k),
            Node::Group(k, x) => Re::Group(k as nat, Box::new(x.re(cl))),
            Node::Cat(x, y) => Re::Cat(Box::new(x.re(cl)), Box::new(y.re(cl))),
            Node::Alt(x, y) => Re::Alt(Box::new(x.re(cl)), Box::new(y.re(cl))),
            Node::Opt(x, g) => Re::Opt(Box::new(x.re(cl)), g),
            Node::Plus(x, g) => Re::Plus(Box::new(x.re(cl)), g),
        }
    }

    /// The sizes and entries recorded in the tree are those of its
    /// regular expression (they do not depend on the classes).
    pub open spec fn wf(self) -> bool
        decreases self,
    {
        &&& forall|cl: Seq<Class>|
            {
                let r = #[trigger] self.re(cl);
                self.ln == ln(r) && self.lz == lz(r) && fo(self.en) == eno(r) && fo(self.ez) == ezo(r)
            }
        &&& self.ln <= MAX_PROG
        &&& self.lz <= MAX_PROG
        &&& match self.node {
            Node::Group(k, x) => x.wf(),
            Node::Cat(x, y) => x.wf() && y.wf(),
            Node::Alt(x, y) => x.wf() && y.wf(),
            Node::Opt(x, g) => x.wf(),
            Node::Plus(x, g) => x.wf(),
            _ => true,
        }
    }

    /// Class numbers are below `nc` and group numbers below `ng`.
    pub open spec fn bounded(self, nc: int, ng: int) -> bool
        decreases self,
    {
        match self.node {
            Node::Char(c) => c < nc,
            Node::Group(k, x) => k < ng && x.bounded(nc, ng),
            Node::Cat(x, y) => x.bounded(nc, ng) && y.bounded(nc, ng),
            Node::Alt(x, y) => x.bounded(nc, ng) && y.bounded(nc, ng),
            Node::Opt(x, g) => x.bounded(nc, ng),
            Node::Plus(x, g) => x.bounded(nc, ng),
            _ => true,
        }
    }

    /// What `wf` says about the node itself.
    pub proof fn lemma_wf(self, cl: Seq<Class>)
        requires
            self.wf(),
        ensures
            self.ln == ln(self.re(cl)),
            self.lz == lz(self.re(cl)),
            fo(self.en) == eno(self.re(cl)),
            fo(self.ez) == ezo(self.re(cl)),
            self.ln <= MAX_PROG,
            self.lz <= MAX_PROG,
    {
    }

    /// Classes beyond the ones the tree names do not matter.
    pub proof fn lemma_re_ext(self, c1: Seq<Class>, c2: Seq<Class>, ng: int)
        requires
            self.bounded(c1.len() as int, ng),
            c1.len() <= c2.len(),
            forall|k: int| 0 <= k < c1.len() ==> c2[k] == c1[k],
        ensures
            self.re(c2) == self.re(c1),
        decreases self,
    {
        match self.node {
            Node::Group(k, x) => {
                x.lemma_re_ext(c1, c2, ng);
            },
            Node::Cat(x, y) => {
                x.lemma_re_ext(c1, c2, ng);
                y.lemma_re_ext(c1, c2, ng);
            },
            Node::Alt(x, y) => {
                x.lemma_re_ext(c1, c2, ng);
                y.lemma_re_ext(c1, c2, ng);
            },
            Node::Opt(x, g) => {
                x.lemma_re_ext(c1, c2, ng);
            },
            Node::Plus(x, g) => {
                x.lemma_re_ext(c1, c2, ng);
            },
            _ => {},
        }
    }

    pub proof fn lemma_bounded_mono(self, nc: int, ng: int, nc2: int, ng2: int)
        requires
            self.bounded(nc, ng),
            nc <= nc2,
            ng <= ng2,
        ensures
            self.bounded(nc2, ng2),
        decreases self,
    {
        match self.node {
            Node::Group(k, x) => {
                x.lemma_bounded_mono(nc, ng, nc2, ng2);
            },
            Node::Cat(x, y) => {
                x.lemma_bounded_mono(nc, ng, nc2, ng2);
                y.lemma_bounded_mono(nc, ng, nc2, ng2);
            },
            Node::Alt(x, y) => {
                x.lemma_bounded_mono(nc, ng, nc2, ng2);
                y.lemma_bounded_mono(nc, ng, nc2, ng2);
            },
            Node::Opt(x, g) => {
                x.lemma_bounded_mono(nc, ng, nc2, ng2);
            },
            Node::Plus(x, g) => {
                x.lemma_bounded_mono(nc, ng, nc2, ng2);
            },
            _ => {},
        }
    }

    fn mk(node: Node, ln: usize, lz: usize, en: usize, ez: usize, h: usize, rep: usize) -> (r: Option<Ast>)
        ensures
            r matches Some(a) ==> a.node == node && a.ln == ln && a.lz == lz && a.en == en && a.ez == ez && ln
                <= MAX_PROG && lz <= MAX_PROG && a.rep == rep,
    {
        if ln > MAX_PROG || lz > MAX_PROG || h > MAX_HEIGHT {
            None
        } else {
            Some(Ast { node: node, ln: ln, lz: lz, en: en, ez: ez, h: h, rep: rep })
        }
    }

    pub fn empty() -> (a: Ast)
        ensures
            a.wf(),
            a.rep == 1,
            a.node == Node::Empty,
    {
        Ast { node: Node::Empty, ln: 0, lz: 0, en: THRU, ez: THRU, h: 0, rep: 1 }
    }

    pub fn chr(cls: usize) -> (a: Ast)
        ensures
            a.wf(),
            a.rep == 1,
            a.node == Node::Char(cls),
    {
        Ast { node: Node::Char(cls), ln: 1, lz: 1, en: 0, ez: 0, h: 0, rep: 1 }
    }

    pub fn look(k: Look) -> (a: Ast)
        ensures
            a.wf(),
            a.rep == 1,
            a.node == Node::Look(k),
    {
        Ast { node: Node::Look(k), ln: 1, lz: 1, en: 0, ez: 0, h: 0, rep: 1 }
    }

    pub fn group(k: usize, x: Ast) -> (r: Option<Ast>)
        requires
            x.wf(),
        ensures
            r matches Some(a) ==> a.wf() && a.rep == x.rep && a.node == Node::Group(k, Box::new(x)),
    {
        if x.h >= MAX_HEIGHT {
            return None;
        }
        let (ln, lz, h, x_rep) = (x.ln + 2, x.lz + 2, x.h + 1, x.rep);
        let r = Ast::mk(Node::Group(k, Box::new(x)), ln, lz, 0, 0, h, x_rep);
        proof {
            if r is Some {
                let a = r->0;
                assert forall|cl: Seq<Class>| true implies {
                    let r = #[trigger] a.re(cl);
                    a.ln == crate::sem::ln(r) && a.lz == crate::sem::lz(r) && fo(a.en) == eno(r) && fo(a.ez) == ezo(r)
                } by {
                    let r = a.re(cl);
                    assert(r == Re::Group(k as nat, Box::new(x.re(cl))));
                    assert(x.ln == crate::sem::ln(x.re(cl)) && x.lz == crate::sem::lz(x.re(cl)) && fo(x.en) == eno(x.re(cl)) && fo(x.ez)
                        == ezo(x.re(cl)));
                    lemma_ent(x.re(cl), 0, 0);
                    assert(a.ln == crate::sem::ln(r));
                    assert(a.lz == crate::sem::lz(r));
                    assert(fo(a.en) == eno(r));
                    assert(fo(a.ez) == ezo(r));
                }
                assert(a.wf());
            }
        }
        r
    }

    pub fn cat(x: Ast, y: Ast) -> (r: Option<Ast>)
        requires
            x.wf(),
            y.wf(),
        ensures
            r matches Some(a) ==> a.wf() && a.rep == (if x.rep > y.rep { x.rep } else { y.rep }) && a.node == Node::Cat(Box::new(x), Box::new(y)),
    {
        if x.h >= MAX_HEIGHT || y.h >= MAX_HEIGHT {
            return None;
        }
        let ln = x.ln + y.ln;
        let lz = x.lz + y.lz;
        let h = max(x.h, y.h) + 1;
        let rep = max(x.rep, y.rep);
        proof {
            assert forall|cl: Seq<Class>| true implies {
                let r = Re::Cat(Box::new(#[trigger] x.re(cl)), Box::new(y.re(cl)));
                (eno(x.re(cl)) matches Some(k) ==> k < x.ln) && (eno(y.re(cl)) matches Some(k) ==> k < y.ln) && (ezo(
                    x.re(cl),
                ) matches Some(k) ==> k < x.lz) && (ezo(y.re(cl)) matches Some(k) ==> k < y.lz)
            } by {
                lemma_ent(x.re(cl), 0, 0);
                lemma_ent(y.re(cl), 0, 0);
            }
        }
        let en = if x.en != THRU {
            x.en
        } else if y.en != THRU {
            x.ln + y.en
        } else {
            THRU
        };
        let ez = if x.ez != THRU {
            x.ez
        } else if y.ez != THRU {
            x.lz + y.ez
        } else {
            THRU
        };
        let ghost w = x.re(Seq::empty());
        let ghost w2 = y.re(Seq::empty());
        let r = Ast::mk(Node::Cat(Box::new(x), Box::new(y)), ln, lz, en, ez, h, rep);
        proof {
            if r is Some {
                let a = r->0;
                assert forall|cl: Seq<Class>| true implies {
                    let r = #[trigger] a.re(cl);
                    a.ln == crate::sem::ln(r) && a.lz == crate::sem::lz(r) && fo(a.en) == eno(r) && fo(a.ez) == ezo(r)
                } by {
                    let r = a.re(cl);
                    assert(r == Re::Cat(Box::new(x.re(cl)), Box::new(y.re(cl))));
                    assert(x.ln == crate::sem::ln(x.re(cl)) && x.lz == crate::sem::lz(x.re(cl)) && fo(x.en) == eno(x.re(cl)) && fo(x.ez)
                        == ezo(x.re(cl)));
                    lemma_ent(x.re(cl), 0, 0);
                    assert(y.ln == crate::sem::ln(y.re(cl)) && y.lz == crate::sem::lz(y.re(cl)) && fo(y.en) == eno(y.re(cl)) && fo(y.ez)
                        == ezo(y.re(cl)));
                    lemma_ent(y.re(cl), 0, 0);
                    assert(a.ln == crate::sem::ln(r));
                    assert(a.lz == crate::sem::lz(r));
                    assert(fo(a.en) == eno(r));
                    assert(fo(a.ez) == ezo(r));
                }
                assert(a.wf());
            }
        }
        r
    }

    pub fn alt(x: Ast, y: Ast) -> (r: Option<Ast>)
        requires
            x.wf(),
            y.wf(),
        ensures
            r matches Some(a) ==> a.wf() && a.rep == (if x.rep > y.rep { x.rep } else { y.rep }) && a.node == Node::Alt(Box::new(x), Box::new(y)),
    {
        if x.h >= MAX_HEIGHT || y.h >= MAX_HEIGHT {
            return None;
        }
        let ln = x.ln + y.ln + 1;
        let lz = x.lz + y.lz + 1;
        let h = max(x.h, y.h) + 1;
        let rep = max(x.rep, y.rep);
        let r = Ast::mk(Node::Alt(Box::new(x), Box::new(y)), ln, lz, 0, 0, h, rep);
        proof {
            if r is Some {
                let a = r->0;
                assert forall|cl: Seq<Class>| true implies {
                    let r = #[trigger] a.re(cl);
                    a.ln == crate::sem::ln(r) && a.lz == crate::sem::lz(r) && fo(a.en) == eno(r) && fo(a.ez) == ezo(r)
                } by {
                    let r = a.re(cl);
                    assert(r == Re::Alt(Box::new(x.re(cl)), Box::new(y.re(cl))));
                    assert(x.ln == crate::sem::ln(x.re(cl)) && x.lz == crate::sem::lz(x.re(cl)) && fo(x.en) == eno(x.re(cl)) && fo(x.ez)
                        == ezo(x.re(cl)));
                    lemma_ent(x.re(cl), 0, 0);
                    assert(y.ln == crate::sem::ln(y.re(cl)) && y.lz == crate::sem::lz(y.re(cl)) && fo(y.en) == eno(y.re(cl)) && fo(y.ez)
                        == ezo(y.re(cl)));
                    lemma_ent(y.re(cl), 0, 0);
                    assert(a.ln == crate::sem::ln(r));
                    assert(a.lz == crate::sem::lz(r));
                    assert(fo(a.en) == eno(r));
                    assert(fo(a.ez) == ezo(r));
                }
                assert(a.wf());
            }
        }
        r
    }

    pub fn opt(x: Ast, greedy: bool) -> (r: Option<Ast>)
        requires
            x.wf(),
        ensures
            r matches Some(a) ==> a.wf() && a.rep == x.rep && a.node == Node::Opt(Box::new(x), greedy),
    {
        if x.h >= MAX_HEIGHT {
            return None;
        }
        let (ln, lz, h, x_rep) = (x.ln + 1, x.lz + 1, x.h + 1, x.rep);
        let r = Ast::mk(Node::Opt(Box::new(x), greedy), ln, lz, 0, 0, h, x_rep);
        proof {
            if r is Some {
                let a = r->0;
                assert forall|cl: Seq<Class>| true implies {
                    let r = #[trigger] a.re(cl);
                    a.ln == crate::sem::ln(r) && a.lz == crate::sem::lz(r) && fo(a.en) == eno(r) && fo(a.ez) == ezo(r)
                } by {
                    let r = a.re(cl);
                    assert(r == Re::Opt(Box::new(x.re(cl)), greedy));
                    assert(x.ln == crate::sem::ln(x.re(cl)) && x.lz == crate::sem::lz(x.re(cl)) && fo(x.en) == eno(x.re(cl)) && fo(x.ez)
                        == ezo(x.re(cl)));
                    lemma_ent(x.re(cl), 0, 0);
                    assert(a.ln == crate::sem::ln(r));
                    assert(a.lz == crate::sem::lz(r));
                    assert(fo(a.en) == eno(r));
                    assert(fo(a.ez) == ezo(r));
                }
                assert(a.wf());
            }
        }
        r
    }

    pub fn plus(x: Ast, greedy: bool) -> (r: Option<Ast>)
        requires
            x.wf(),
        ensures
            r matches Some(a) ==> a.wf() && a.rep == x.rep && a.node == Node::Plus(Box::new(x), greedy),
    {
        if x.h >= MAX_HEIGHT {
            return None;
        }
        let ln = x.ln + 1 + 2 * x.lz;
        let (lz, h, x_rep) = (x.lz, x.h + 1, x.rep);
        proof {
            assert forall|cl: Seq<Class>| true implies (ezo(#[trigger] x.re(cl)) matches Some(k) ==> k < x.lz) by {
                lemma_ent(x.re(cl), 0, 0);
            }
        }
        let ghost w = x.re(Seq::empty());
        let en = if x.ez != THRU {
            x.ln + 1 + x.lz + x.ez
        } else {
            THRU
        };
        let ez = x.ez;
        let r = Ast::mk(Node::Plus(Box::new(x), greedy), ln, lz, en, ez, h, x_rep);
        proof {
            if r is Some {
                let a = r->0;
                assert forall|cl: Seq<Class>| true implies {
                    let r = #[trigger] a.re(cl);
                    a.ln == crate::sem::ln(r) && a.lz == crate::sem::lz(r) && fo(a.en) == eno(r) && fo(a.ez) == ezo(r)
                } by {
                    let r = a.re(cl);
                    assert(r == Re::Plus(Box::new(x.re(cl)), greedy));
                    assert(x.ln == crate::sem::ln(x.re(cl)) && x.lz == crate::sem::lz(x.re(cl)) && fo(x.en) == eno(x.re(cl)) && fo(x.ez)
                        == ezo(x.re(cl)));
                    lemma_ent(x.re(cl), 0, 0);
                    assert(a.ln == crate::sem::ln(r));
                    assert(a.lz == crate::sem::lz(r));
                    assert(fo(a.en) == eno(r));
                    assert(fo(a.ez) == ezo(r));
                }
                assert(a.wf());
            }
        }
        r
    }

    /// `x*` is `(x+)?`.
    pub fn star(x: Ast, greedy: bool) -> (r: Option<Ast>)
        requires
            x.wf(),
        ensures
            r matches Some(a) ==> a.wf() && a.rep == x.rep && (a.node matches Node::Opt(p, g) && g == greedy && p.wf()
                && p.node == Node::Plus(Box::new(x), greedy)),
    {
        match Ast::plus(x, greedy) {
            Some(p) => Ast::opt(p, greedy),
            None => None,
        }
    }

    /// The same tree with another repetition count.
    pub fn set_rep(self, rep: usize) -> (r: Ast)
        ensures
            r.node == self.node,
            r.rep == rep,
            self.wf() ==> r.wf(),
            forall|cl: Seq<Class>| #[trigger] r.re(cl) == self.re(cl),
            forall|nc: int, ng: int| #[trigger] r.bounded(nc, ng) == self.bounded(nc, ng),
    {
        let mut a = self;
        a.rep = rep;
        assert forall|cl: Seq<Class>| #[trigger] a.re(cl) == self.re(cl) by {}
        a
    }

    pub fn dup(&self) -> (r: Ast)
        ensures
            r == *self,
        decreases self,
    {
        let node = match &self.node {
            Node::Empty => Node::Empty,
            Node::Char(c) => Node::Char(*c),
            Node::Look(k) => Node::Look(*k),
            Node::Group(k, x) => Node::Group(*k, Box::new(x.dup())),
            Node::Cat(x, y) => Node::Cat(Box::new(x.dup()), Box::new(y.dup())),
            Node::Alt(x, y) => Node::Alt(Box::new(x.dup()), Box::new(y.dup())),
            Node::Opt(x, g) => Node::Opt(Box::new(x.dup()), *g),
            Node::Plus(x, g) => Node::Plus(Box::new(x.dup()), *g),
        };
        Ast { node: node, ln: self.ln, lz: self.lz, en: self.en, ez: self.ez, h: self.h, rep: self.rep }
    }
}

fn max(a: usize, b: usize) -> (r: usize)
    ensures
        r == if a > b {
            a
        } else {
            b
        },
{
    if a > b {
        a
    } else {
        b
    }
}

} // verus!

// Dropping a tree takes its nodes apart one at a time, children first onto
// a list on the heap, so a deep tree costs no call stack (the derived drop
// would recurse once per level). Plain Rust outside the proof: it only
// frees memory.
impl Drop for Ast {
    fn drop(&mut self) {
        let mut todo: Vec<Box<Ast>> = Vec::new();
        take_children(&mut self.node, &mut todo);
        while let Some(mut a) = todo.pop() {
            take_children(&mut a.node, &mut todo);
        }
    }
}

fn take_children(n: &mut Node, todo: &mut Vec<Box<Ast>>) {
    match core::mem::replace(n, Node::Empty) {
        Node::Group(_, x) | Node::Opt(x, _) | Node::Plus(x, _) => todo.push(x),
        Node::Cat(x, y) | Node::Alt(x, y) => {
            todo.push(x);
            todo.push(y);
        },
        _ => {},
    }
}
