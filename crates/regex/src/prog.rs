//! The automaton: a program of instructions.
use crate::class::Class;
use crate::sem::*;
use crate::need::*;
use crate::skip::*;
use crate::spec::Look;
use vstd::prelude::*;

verus! {

#[derive(Clone, Copy)]
pub enum Inst {
    /// Consume one character of class `cls`, go to `next`.
    Char { cls: u32, next: u32 },
    /// Go to `a`, or failing that, `b`.
    Split { a: u32, b: u32 },
    /// Record the position in capture slot `slot`, go to `next`.
    Save { slot: u32, next: u32 },
    /// Go to `next` if the assertion holds here.
    Look { k: Look, next: u32 },
    Match,
    Fail,
}

pub struct Prog {
    pub insts: Vec<Inst>,
    pub classes: Vec<Class>,
    pub start: usize,
    /// Capture slots: two per group, group 0 being the whole match.
    pub nslots: usize,
    /// Empty, or 256 flags: a search with no thread alive may pass over
    /// a byte whose flag is not set (see `skip.rs`).
    pub skip: Vec<bool>,
    /// The instructions the skip table accounts for.
    pub reach: Ghost<Seq<bool>>,
    /// The only byte a match can start with, if there is just one.
    pub lead1: Option<u8>,
    /// Empty, or 256 flags: no match starts at an ASCII byte unless the
    /// byte after it is flagged (see `skip.rs`).
    pub next2: Vec<bool>,
    /// The instructions the second-byte table accounts for.
    pub reach2: Ghost<Seq<bool>>,
    /// `(a, b, c, d)`: every match starts with `a` or `b`, both ASCII,
    /// and goes on with `c` or `d`.
    pub pair: Option<(u8, u8, u8, u8)>,
    /// Three byte ranges that hold every byte a match can start with,
    /// kept when those bytes are few and rare in text: the search for a
    /// start looks for them 16 bytes at a time.
    pub rng: Option<(u8, u8, u8, u8, u8, u8)>,
    /// An ASCII byte every match must contain (see `need.rs`), kept for
    /// programs whose first bytes give no fast scan.
    pub need: Option<u8>,
    /// The sets of instructions that show it.
    pub needg: Ghost<Seq<bool>>,
    pub needw: Ghost<Seq<bool>>,
    /// With `need`, 256 flags: the bytes a match can be made of.
    pub alpha: Vec<bool>,
}

/// The instruction as mathematics.
pub open spec fn iv(i: Inst, classes: Seq<Class>) -> SInst {
    match i {
        Inst::Char { cls, next } => SInst::Char { cls: classes[cls as int].set(), next: next as int },
        Inst::Split { a, b } => SInst::Split { a: a as int, b: b as int },
        Inst::Save { slot, next } => SInst::Save { slot: slot as int, next: next as int },
        Inst::Look { k, next } => SInst::Look { k: k, next: next as int },
        Inst::Match => SInst::Match,
        Inst::Fail => SInst::Fail,
    }
}

impl Prog {
    /// The program as mathematics.
    pub open spec fn sp(&self) -> Seq<SInst> {
        Seq::new(self.insts@.len(), |k: int| iv(self.insts@[k], self.classes@))
    }

    pub open spec fn wf(&self) -> bool {
        &&& fwd(self.sp())
        &&& self.start < self.insts@.len()
        &&& self.insts@.len() <= 0x7fff_ffff
        &&& forall|k: int| 0 <= k < self.classes@.len() ==> (#[trigger] self.classes@[k]).wf()
        &&& forall|pc: int|
            0 <= pc < self.insts@.len() ==> match #[trigger] self.insts@[pc] {
                Inst::Char { cls, next } => cls < self.classes@.len(),
                Inst::Save { slot, next } => slot < self.nslots,
                _ => true,
            }
        &&& (self.skip@.len() == 0 || skip_ok(self.sp(), self.start as int, self.reach@, self.skip@))
        &&& only(self.skip@, self.lead1)
        &&& (self.next2@.len() == 0 || (self.skip@.len() == 256 && pair_ok(
            self.sp(),
            self.reach@,
            self.reach2@,
            self.next2@,
        )))
        &&& (self.pair matches Some(q) ==> self.next2@.len() == 256 && only2(self.skip@, Some((q.0, q.1))) && only2(
            self.next2@,
            Some((q.2, q.3)),
        ) && q.0 < 0x80 && q.1 < 0x80)
        &&& (self.rng matches Some(r) ==> self.skip@.len() == 256 && forall|b: int|
            0 <= b < 256 ==> (#[trigger] self.skip@[b] ==> crate::find::inr(b as u8, r)))
        &&& (self.need matches Some(x) ==> need_ok(self.sp(), self.start as int, x, self.needg@, self.needw@) && al_ok(
            self.sp(),
            self.alpha@,
        ))
    }
}

} // verus!
