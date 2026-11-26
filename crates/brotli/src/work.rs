//! The decoder's work: a ghost step counter, and the credit that pays for
//! the steps no input bit or output byte pays for as it is taken.
use crate::decoder::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;

verus! {

/// Steps taken so far: ghost state, erased at compile time. Each turn of a
/// loop whose length depends on the input adds one; loops of a few turns
/// fixed by the format (refilling the bit window near the end of the
/// input, the 18 code length code lengths, a simple code's 4 symbols, a
/// dictionary word's transform) count as part of the turn that runs them.
pub tracked struct Meter {
    /// The count.
    pub ghost n: nat,
}

/// The work of building a prefix code's table over `alpha` symbols
/// (`verilith_core::htable::build_cost` with the root table at most
/// `MAX_ROOT` bits).
pub open spec fn pcb(alpha: int) -> int {
    18 * alpha + 3 * 1024 + 73
}

/// The work of building the code length code's table.
pub open spec fn clb() -> int {
    493
}

/// The work per input bit: enough for the most a few bits can make the
/// decoder do with no more input or output (the five bits that start a
/// context map of 16,384 entries over 256 codes, read with a one-symbol
/// code and moved to front).
pub open spec fn kbit() -> int {
    1_000_000
}

/// The work per output byte.
pub open spec fn lbyte() -> int {
    8
}

/// The most work an attempt at a step that finds the stream malformed
/// does, beyond what its bits pay for.
pub open spec fn xc() -> int {
    200_000
}

/// The largest ring.
pub open spec fn rmax() -> int {
    0x100_0000
}

/// The work of `mk_flat`, per code.
pub open spec fn flc() -> int {
    2050
}

/// The work of inverse move-to-front of `size` entries below `nt`.
pub open spec fn imtfc(size: int, nt: int) -> int {
    256 + size * nt
}

/// Zero-input steps still to come in the meta-block that are paid for by
/// nothing else: the ends of the context modes, of each context map's
/// symbols and of each group of codes, and the meta-block's end.
pub open spec fn fixed(d: Decoder) -> int {
    match d.ph {
        Ph::WBits | Ph::MetaHeader | Ph::Done => 0,
        Ph::Metadata | Ph::Uncompressed => 2,
        Ph::NBlockTypes(_) | Ph::BTypeCode(_) | Ph::BCountCode(_) | Ph::BCount(_) | Ph::DistParams | Ph::CModes => 7,
        Ph::CMap(w) => (if w == 0 { 6int } else { 5int }) - (if d.cm.stage >= 3 { 1int } else { 0int }),
        Ph::Trees(g) => 4 - g,
        _ => 1,
    }
}

/// Whether the phase reads a prefix code.
pub open spec fn pc_phase(p: Ph) -> bool {
    p is BTypeCode || p is BCountCode || p is CMap || p is Trees
}

/// The prefix code being read: two per code length still to come, its
/// table, and for a literal or distance code its share of `mk_flat`.
pub open spec fn pc_cr(d: Decoder) -> int {
    if d.pc.started && pc_phase(d.ph) {
        let a = alpha_of(d.ph, d.nbt, d.npostfix, d.ndirect, d.cm.view());
        2 * (a - d.pc.n) + pcb(a) + (if d.ph == Ph::Trees(0) || d.ph == Ph::Trees(2) { flc() } else { 0 })
    } else {
        0
    }
}

/// The context map being read: two per entry still to come, and moving
/// them to front.
pub open spec fn cm_cr(d: Decoder) -> int {
    match d.ph {
        Ph::CMap(w) => {
            let size = cmap_size_of(d.nbt, w as int);
            if d.cm.stage == 1 || d.cm.stage == 2 {
                2 * (size - d.cm.map@.len()) + imtfc(size, d.cm.ntrees as int)
            } else if d.cm.stage == 3 {
                imtfc(size, d.cm.ntrees as int)
            } else {
                0
            }
        },
        _ => 0,
    }
}

/// `mk_flat` for the literal and distance codes read so far.
pub open spec fn flat_cr(d: Decoder) -> int {
    if d.ph is Trees {
        flc() * (d.lit@.len() + d.dst@.len())
    } else {
        0
    }
}

/// A command takes a step for its symbol and one for its distance before
/// its first output byte, and a turn that may find no literal: borrowed
/// against that byte.
pub open spec fn cmd_cr(d: Decoder) -> int {
    match d.ph {
        Ph::Insert | Ph::Dist => -2,
        Ph::Copy => -3,
        _ => 0,
    }
}

/// Inside a command, the credit is the borrowed part.
pub proof fn lemma_pot_cmd(o: Decoder, g: Decoder)
    requires
        o.ph == Ph::CmdBegin,
        g.ring@.len() == o.ring@.len(),
        g.ph == Ph::CmdBegin || g.ph == Ph::Insert || g.ph == Ph::Dist || g.ph == Ph::Copy || g.ph == Ph::MetaDone,
    ensures
        pot(g) == pot(o) + cmd_cr(g),
{
}

/// Growing the ring, up to the largest window.
pub open spec fn ring_cr(d: Decoder) -> int {
    4 * (rmax() - d.ring@.len())
}

/// The work paid for in advance.
pub open spec fn pot(d: Decoder) -> int {
    fixed(d) + pc_cr(d) + cm_cr(d) + flat_cr(d) + cmd_cr(d) + ring_cr(d)
}

/// What going from `o` to `n` pays for: the bits read, the bytes output,
/// and the credit used.
pub open spec fn earned(o: Decoder, n: Decoder) -> int {
    kbit() * (n.pos - o.pos) + lbyte() * (n.out@.len() - o.out@.len()) + pot(o) - pot(n)
}

/// The work `w0 .. w1` of an exec step from `o` to `n` returning `r`
/// (`run` counts one more for the turn that calls it).
pub open spec fn wpaid(o: Decoder, n: Decoder, r: Option<Status>, w0: nat, w1: nat) -> bool {
    match r {
        None => w1 + 1 <= w0 + earned(o, n),
        Some(Status::Bad) => w1 <= w0 + xc() + kbit() * (n.pos - o.pos),
        Some(_) => w1 <= w0 + earned(o, n) + 1,
    }
}

/// The credit is never far below zero.
pub proof fn lemma_pot_lb(d: Decoder)
    requires
        d.wf(),
    ensures
        pot(d) >= -3,
        d.ring@.len() <= rmax(),
{
    reveal(ring_ok);
    reveal(reading_ok);
    if d.ring@.len() > 0 {
        lemma_pow2_le(d.wbits as nat, 24);
        vstd::arithmetic::power2::lemma2_to64();
    }
    match d.ph {
        Ph::CMap(w) => {
            let size = cmap_size_of(d.nbt, w as int);
            if d.cm.stage >= 1 {
                assert(size * d.cm.ntrees >= 0) by (nonlinear_arith)
                    requires
                        size >= 0,
                        d.cm.ntrees >= 0,
                ;
            }
        },
        _ => {},
    }
}

} // verus!
