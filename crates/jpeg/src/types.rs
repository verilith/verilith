//! The decoder's own data: the tables, frame and scan headers as it holds
//! them, and what each stands for in the specification.
use crate::spec::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;

verus! {

/// What can go wrong.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The file is not a JPEG this decoder takes: it is malformed, or of a
    /// kind that is not supported (see the README).
    Invalid,
    /// An allocation failed, or the image is too large for this machine.
    OutOfMemory,
}

#[derive(Clone, Copy)]
pub struct HuffTab {
    pub counts: [u8; 16],
    pub vals: [u8; 256],
}

impl View for HuffTab {
    type V = HuffTable;

    open spec fn view(&self) -> HuffTable {
        HuffTable { counts: self.counts@, vals: self.vals@ }
    }
}

/// A Huffman table ready for decoding: for each code length `l`, one past
/// the largest code of that length, and what to add to a code of that
/// length to get its symbol's index.
#[derive(Clone, Copy)]
pub struct Derived {
    pub lim: [i32; 17],
    pub off: [i32; 17],
    /// `lim`, with each length's limit moved up to the top of 16 bits: a
    /// 16-bit window of the input starts with a code of length `l` or less
    /// exactly when it is below `ll[l]`.
    pub ll: [u32; 17],
    /// For each value of the next 10 bits: 0 if no code that short starts
    /// them, else the code's length times 256 plus its symbol.
    pub look: [u16; 1024],
}

/// `e` is the right `look` entry for the 10 bits `p`.
pub open spec fn look_ok(e: int, p: int, ll: Seq<u32>, off: Seq<i32>, vals: Seq<u8>) -> bool {
    let l = e / 256;
    if e == 0 {
        true
    } else {
        &&& 1 <= l <= 10
        &&& forall|j: int| 1 <= j < l ==> (#[trigger] ll[j]) <= p * 64
        &&& p * 64 + 64 <= ll[l]
        &&& 0 <= (p * 64) / (pow2((16 - l) as nat) as int) + off[l] < 256
        &&& e % 256 == vals[(p * 64) / (pow2((16 - l) as nat) as int) + off[l]]
    }
}

impl Derived {
    /// The table is `t`'s, and `t` is usable.
    pub open spec fn wf(&self, t: HuffTable) -> bool {
        &&& huff_ok(t)
        &&& forall|l: int|
            1 <= l <= 16 ==> (#[trigger] self.lim[l]) == hfirst(t, l) + hcount(t, l) && self.off[l] == hbase(t, l)
                - hfirst(t, l) && self.ll[l] == self.lim[l] * pow2((16 - l) as nat)
        &&& forall|p: int| 0 <= p < 1024 ==> look_ok(#[trigger] self.look[p] as int, p, self.ll@, self.off@, t.vals)
    }
}

pub struct Tabs {
    pub q: [[u16; 64]; 4],
    pub qdef: [bool; 4],
    pub dc: [HuffTab; 4],
    pub dcdef: [bool; 4],
    pub ac: [HuffTab; 4],
    pub acdef: [bool; 4],
    pub ri: u16,
}

impl View for Tabs {
    type V = Tables;

    open spec fn view(&self) -> Tables {
        Tables {
            q: Seq::new(4, |i: int| self.q@[i]@),
            qdef: self.qdef@,
            dc: Seq::new(4, |i: int| self.dc@[i]@),
            dcdef: self.dcdef@,
            ac: Seq::new(4, |i: int| self.ac@[i]@),
            acdef: self.acdef@,
            ri: self.ri as int,
        }
    }
}

#[derive(Clone, Copy)]
pub struct FrameX {
    pub prog: bool,
    pub w: u16,
    pub h: u16,
    pub nc: u8,
    pub comps: [Comp; 3],
}

impl View for FrameX {
    type V = Frame;

    open spec fn view(&self) -> Frame {
        Frame {
            prog: self.prog,
            w: self.w as int,
            h: self.h as int,
            nc: self.nc as int,
            comps: Seq::new(self.nc as nat, |c: int| self.comps@[c]),
        }
    }
}

#[derive(Clone, Copy)]
pub struct ScanX {
    pub ns: u8,
    pub ci: [u8; 3],
    pub td: [u8; 3],
    pub ta: [u8; 3],
    pub ss: u8,
    pub se: u8,
    pub ah: u8,
    pub al: u8,
}

impl View for ScanX {
    type V = Scan;

    open spec fn view(&self) -> Scan {
        Scan {
            ns: self.ns as int,
            ci: Seq::new(self.ns as nat, |i: int| self.ci@[i] as int),
            td: Seq::new(self.ns as nat, |i: int| self.td@[i] as int),
            ta: Seq::new(self.ns as nat, |i: int| self.ta@[i] as int),
            ss: self.ss as int,
            se: self.se as int,
            ah: self.ah as int,
            al: self.al as int,
        }
    }
}

} // verus!
