//! CPU-specific code paths (part of the trusted base).
//!
//! Each function here is one of the verified decoding loops
//! (`seq::seq_run_exec`, `huf::huf_4streams_exec`, `huf::huf_stream_exec`),
//! compiled a second time with BMI2 enabled and run when the CPU has it.
//! Its `requires` and `ensures` are copied from the verified function; the
//! body only chooses which compilation of that function to call.
//! `#[target_feature]` only changes code generation. Verus rejects the
//! attribute on verified code (verus-lang/verus#3362), so the BMI2
//! copies live outside `verus!`.
use crate::huf::{huf_4streams_exec, huf_stream_exec, HufTab};
#[cfg(verus_only)]
use crate::huf::{huf_code_of, huf_wf};
use crate::bits::BITS_MAX;
use crate::seq::{seq_run_exec, SeqOut, SeqTabs, MAX_LIMIT};
#[cfg(verus_only)]
use crate::seq::{seqtabs_is, sstate};
#[cfg(verus_only)]
use crate::spec::{huf_4streams, huf_stream, seq_run, Reps};
use crate::spec::SeqTables;
use crate::work::Meter;
use vstd::prelude::*;

verus! {

/// `seq_run_exec`, with BMI2 (a variable shift or mask in one instruction)
/// when the CPU has it.
#[verifier::external_body]
pub fn run_seqs(
    t: &SeqTabs,
    s: &[u8],
    lits: &[u8],
    window: u64,
    n: usize,
    p0: usize,
    sll0: u32,
    sof0: u32,
    sml0: u32,
    r10: u64,
    r20: u64,
    r30: u64,
    out: &mut Vec<u8>,
    fstart: usize,
    olimit: usize,
    Ghost(ts): Ghost<SeqTables>,
    Tracked(m): Tracked<&mut Meter>,
) -> (r: Result<SeqOut, bool>)
    requires
        seqtabs_is(t, ts),
        s@.len() < BITS_MAX,
        lits@.len() <= 131072,
        p0 <= 8 * s@.len(),
        (sll0 as int) < t.ll.rows@.len(),
        (sof0 as int) < t.of.rows@.len(),
        (sml0 as int) < t.ml.rows@.len(),
        fstart <= old(out)@.len() <= olimit,
        olimit <= MAX_LIMIT,
        olimit - old(out)@.len() <= 131072,
    ensures
        final(out)@.len() >= old(out)@.len(),
        final(m).n <= old(m).n + 3 * (final(out)@.len() - old(out)@.len()) + 3,
        final(out)@.len() <= olimit,
        r is Ok ==> final(out)@.len() - old(out)@.len() >= r.unwrap().li,
        ({
            let st0 = sstate(p0, sll0, sof0, sml0, r10, r20, r30, 0, old(out)@, fstart as int);
            match seq_run(ts, s@, lits@, window as nat, n as nat, st0) {
                None => r is Err,
                Some(fin) => match r {
                    Err(lim) => lim && fstart + fin.out.len() > olimit,
                    Ok(o) => {
                        &&& fin.p == o.p as int
                        &&& fin.reps == (Reps { r1: o.r1 as nat, r2: o.r2 as nat, r3: o.r3 as nat })
                        &&& fin.li == o.li as int
                        &&& final(out)@ == old(out)@.subrange(0, fstart as int) + fin.out
                        &&& o.li <= lits@.len()
                        &&& final(out)@.len() <= olimit
                    },
                },
            }
        }),
{
    #[cfg(target_arch = "x86_64")]
    {
        if std::is_x86_feature_detected!("bmi2") {
            // SAFETY: the CPU supports BMI2.
            return unsafe {
                bmi2::seq_run(t, s, lits, window, n, p0, sll0, sof0, sml0, r10, r20, r30, out, fstart, olimit, Ghost(ts), Tracked(m))
            };
        }
    }
    seq_run_exec(t, s, lits, window, n, p0, sll0, sof0, sml0, r10, r20, r30, out, fstart, olimit, Ghost(ts), Tracked(m))
}

/// `huf_4streams_exec`, with BMI2 when the CPU has it.
#[verifier::external_body]
pub fn run_huf4(t: &HufTab, b: &[u8], n: usize, out: &mut Vec<u8>, Tracked(m): Tracked<&mut Meter>) -> (ok: bool)
    requires
        huf_wf(t),
        b@.len() < BITS_MAX,
        n < BITS_MAX,
    ensures
        final(m).n <= old(m).n + 5 * n,
        match huf_4streams(huf_code_of(t), b@, n as nat) {
            None => !ok,
            Some(o) => ok && final(out)@ == o,
        },
{
    #[cfg(target_arch = "x86_64")]
    {
        if std::is_x86_feature_detected!("bmi2") {
            // SAFETY: the CPU supports BMI2.
            return unsafe { bmi2::huf4(t, b, n, out, Tracked(m)) };
        }
    }
    huf_4streams_exec(t, b, n, out, Tracked(m))
}

/// `huf_stream_exec`, with BMI2 when the CPU has it.
#[verifier::external_body]
pub fn run_huf1(t: &HufTab, s: &[u8], n: usize, out: &mut Vec<u8>, Tracked(m): Tracked<&mut Meter>) -> (ok: bool)
    requires
        huf_wf(t),
        s@.len() < BITS_MAX,
    ensures
        final(m).n <= old(m).n + 2 * n,
        match huf_stream(huf_code_of(t), s@, n as nat) {
            None => !ok,
            Some(o) => ok && final(out)@ == old(out)@ + o,
        },
{
    #[cfg(target_arch = "x86_64")]
    {
        if std::is_x86_feature_detected!("bmi2") {
            // SAFETY: the CPU supports BMI2.
            return unsafe { bmi2::huf1(t, s, n, out, Tracked(m)) };
        }
    }
    huf_stream_exec(t, s, n, out, Tracked(m))
}

} // verus!

/// The verified loops compiled with BMI2. Each is one call.
#[cfg(target_arch = "x86_64")]
mod bmi2 {
    use super::*;

    #[target_feature(enable = "bmi2")]
    pub(super) unsafe fn seq_run(
        t: &SeqTabs,
        s: &[u8],
        lits: &[u8],
        window: u64,
        n: usize,
        p0: usize,
        sll0: u32,
        sof0: u32,
        sml0: u32,
        r10: u64,
        r20: u64,
        r30: u64,
        out: &mut Vec<u8>,
        fstart: usize,
        olimit: usize,
        ts: Ghost<SeqTables>,
        m: Tracked<&mut Meter>,
    ) -> Result<SeqOut, bool> {
        seq_run_exec(t, s, lits, window, n, p0, sll0, sof0, sml0, r10, r20, r30, out, fstart, olimit, ts, m)
    }

    #[target_feature(enable = "bmi2")]
    pub(super) unsafe fn huf4(t: &HufTab, b: &[u8], n: usize, out: &mut Vec<u8>, m: Tracked<&mut Meter>) -> bool {
        huf_4streams_exec(t, b, n, out, m)
    }

    #[target_feature(enable = "bmi2")]
    pub(super) unsafe fn huf1(t: &HufTab, s: &[u8], n: usize, out: &mut Vec<u8>, m: Tracked<&mut Meter>) -> bool {
        huf_stream_exec(t, s, n, out, m)
    }
}
