//! Dictionaries (RFC 8878 §5): loading one (`load_dict`, `raw_dict`,
//! against `spec::dict_load` and `spec::raw_dict`), and decompressing with
//! one (`DictDecoder::decompress`, against `spec::decompress_d`).
use crate::frame::*;
use crate::fse::*;
use crate::huf::*;
use crate::seq::*;
use crate::spec::*;
use crate::work::Meter;
#[cfg(verus_only)]
use crate::bits::lemma_pow2_le;
#[cfg(verus_only)]
use crate::stream::{lemma_prefix_append, lemma_prefix_trans, lemma_seq_section_prefix, prefix};
use verilith_xxhash::Xxh64;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// No dictionary is this large or larger (the loaders' inputs, and so the
/// content, are shorter).
#[cfg(target_pointer_width = "64")]
pub const DICT_MAX: usize = 0x1_0000_0000;


/// No dictionary is this large or larger: on 32-bit targets, 128 MiB
/// (`bits::BITS_MAX`; zstd's own dictionaries are a few hundred KiB).
#[cfg(target_pointer_width = "32")]
pub const DICT_MAX: usize = 0x0800_0000;

/// The most a call of `DictDecoder::decompress` may be asked to produce.
pub const DICT_LIMIT: usize = MAX_LIMIT - DICT_MAX;

/// A loaded dictionary (`ZSTD_DDict`): its ID, content, repeat offsets
/// and entropy tables.
pub struct DDict {
    pub id: u32,
    pub content: Vec<u8>,
    pub r1: u64,
    pub r2: u64,
    pub r3: u64,
    pub huf: Option<HufTab>,
    pub seqt: Option<SeqTabs>,
}

impl DDict {
    /// This is the spec's dictionary `g`.
    #[verifier::opaque]
    pub open spec fn is(&self, g: Dict) -> bool {
        &&& g.id == self.id as nat
        &&& g.st.out == self.content@
        &&& self.content@.len() < DICT_MAX
        &&& g.st.reps == (Reps { r1: self.r1 as nat, r2: self.r2 as nat, r3: self.r3 as nat })
        &&& huf_opt_is(self.huf, g.st.huf)
        &&& seqt_opt_is(self.seqt, g.st.seqt)
    }
}

// ---------------------------------------------------------------------------
// Copies of the tables, for each frame to start from
// ---------------------------------------------------------------------------

fn copy_vec<T: Copy>(v: &Vec<T>, Tracked(m): Tracked<&mut Meter>) -> (r: Vec<T>)
    ensures
        r@ == v@,
        final(m).n == old(m).n + v@.len(),
{
    let n = v.len();
    let mut r: Vec<T> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            n == v@.len(),
            i <= n,
            r@ == v@.subrange(0, i as int),
            m.n == old(m).n + i,
        decreases n - i,
    {
        r.push(v[i]);
        proof {
            m.n = m.n + 1;
            assert(r@ =~= v@.subrange(0, i + 1));
        }
        i = i + 1;
    }
    proof {
        assert(v@.subrange(0, n as int) =~= v@);
    }
    r
}

/// The steps copying a dictionary's Huffman table takes.
pub open spec fn huf_size(t: Option<HufTab>) -> nat {
    match t {
        None => 0,
        Some(tt) => tt.w@.len() + tt.x2@.len() + tt.x1@.len(),
    }
}

/// The steps copying a dictionary's sequence tables takes.
pub open spec fn seqt_size(t: Option<SeqTabs>) -> nat {
    match t {
        None => 0,
        Some(tt) => tt.ll.rows@.len() + tt.of.rows@.len() + tt.ml.rows@.len() + tt.dl@.len() + tt.dof@.len()
            + tt.dml@.len(),
    }
}

/// The most steps copying a dictionary's tables takes: 256 weights, two
/// Huffman tables of `2^12` entries, and six FSE tables of `2^9`.
pub spec const TABLE_COPY_WORK: nat = 11520;

proof fn lemma_table_size(d: &DDict, g: Dict)
    requires
        d.is(g),
    ensures
        huf_size(d.huf) + seqt_size(d.seqt) <= TABLE_COPY_WORK,
{
    reveal(DDict::is);
    assert(pow2(12) == 4096 && pow2(9) == 512) by {
        lemma2_to64();
    }
    if let Some(t) = d.huf {
        lemma_pow2_le(t.log as nat, 12);
    }
    if let Some(t) = d.seqt {
        lemma_pow2_le(t.ll.log as nat, 9);
        lemma_pow2_le(t.of.log as nat, 9);
        lemma_pow2_le(t.ml.log as nat, 9);
    }
}

fn copy_huf(t: &HufTab, Tracked(m): Tracked<&mut Meter>) -> (r: HufTab)
    ensures
        huf_code_of(&r) == huf_code_of(t),
        huf_wf(t) ==> huf_wf(&r),
        final(m).n == old(m).n + huf_size(Some(*t)),
{
    let r = HufTab {
        log: t.log,
        w: copy_vec(&t.w, Tracked(m)),
        syms: Ghost(t.syms@),
        lens: Ghost(t.lens@),
        x2: copy_vec(&t.x2, Tracked(m)),
        x1: copy_vec(&t.x1, Tracked(m)),
    };
    proof {
        assert(huf_code_of(&r) =~= huf_code_of(t));
    }
    r
}

fn copy_tab(t: &FseTab, Tracked(m): Tracked<&mut Meter>) -> (r: FseTab)
    ensures
        r.log == t.log,
        r.rows@ == t.rows@,
        final(m).n == old(m).n + t.rows@.len(),
{
    FseTab { log: t.log, rows: copy_vec(&t.rows, Tracked(m)) }
}

fn copy_seqt(t: &SeqTabs, Tracked(m): Tracked<&mut Meter>) -> (r: SeqTabs)
    ensures
        forall|s: SeqTables| seqtabs_is(t, s) ==> seqtabs_is(&r, s),
        final(m).n == old(m).n + seqt_size(Some(*t)),
{
    SeqTabs {
        ll: copy_tab(&t.ll, Tracked(m)),
        of: copy_tab(&t.of, Tracked(m)),
        ml: copy_tab(&t.ml, Tracked(m)),
        dl: copy_vec(&t.dl, Tracked(m)),
        dof: copy_vec(&t.dof, Tracked(m)),
        dml: copy_vec(&t.dml, Tracked(m)),
    }
}

pub fn copy_huf_opt(t: &Option<HufTab>, Tracked(m): Tracked<&mut Meter>) -> (r: Option<HufTab>)
    ensures
        forall|c: Option<HufCode>| huf_opt_is(*t, c) ==> huf_opt_is(r, c),
        final(m).n == old(m).n + huf_size(*t),
{
    match t {
        None => None,
        Some(tt) => Some(copy_huf(tt, Tracked(m))),
    }
}

pub fn copy_seqt_opt(t: &Option<SeqTabs>, Tracked(m): Tracked<&mut Meter>) -> (r: Option<SeqTabs>)
    ensures
        forall|s: Option<SeqTables>| seqt_opt_is(*t, s) ==> seqt_opt_is(r, s),
        final(m).n == old(m).n + seqt_size(*t),
{
    match t {
        None => None,
        Some(tt) => Some(copy_seqt(tt, Tracked(m))),
    }
}

// ---------------------------------------------------------------------------
// Loading
// ---------------------------------------------------------------------------

/// A copy of `d[i..]`.
fn tail_copy(d: &[u8], i: usize, Tracked(m): Tracked<&mut Meter>) -> (r: Vec<u8>)
    requires
        i <= d@.len(),
    ensures
        r@ == d@.subrange(i as int, d@.len() as int),
        final(m).n == old(m).n + (d@.len() - i),
{
    let mut v: Vec<u8> = Vec::new();
    verilith_core::prims::extend(&mut v, slice_subrange(d, i, d.len()));
    proof {
        m.n = (m.n + (d@.len() - i)) as nat;
        assert(v@ =~= d@.subrange(i as int, d@.len() as int));
    }
    v
}

/// The raw-content dictionary `d` (`spec::raw_dict`), as
/// `ZSTD_DCtx_refPrefix` uses it.
pub fn raw_dict_exec(d: &[u8], Tracked(m): Tracked<&mut Meter>) -> (r: DDict)
    requires
        d@.len() < DICT_MAX,
    ensures
        r.is(raw_dict(d@)),
        r.content@.len() == d@.len(),
        final(m).n == old(m).n + d@.len(),
{
    let content = tail_copy(d, 0, Tracked(m));
    proof {
        reveal(DDict::is);
        assert(d@.subrange(0, d@.len() as int) =~= d@);
    }
    DDict { id: 0, content, r1: 1, r2: 4, r3: 8, huf: None, seqt: None }
}

/// The dictionary `d` as `ZSTD_DCtx_loadDictionary` reads it
/// (`spec::dict_load`): formatted, or raw content. `None`: it is
/// corrupted.
/// The most steps loading a dictionary takes besides 25 a byte: its
/// Huffman description, three FSE descriptions and three baked tables.
pub spec const DICT_LOAD_WORK: nat = 19546;

#[verifier::rlimit(40)]
pub fn load_dict(d: &[u8], Tracked(m): Tracked<&mut Meter>) -> (r: Option<DDict>)
    requires
        d@.len() < DICT_MAX,
    ensures
        match dict_load(d@) {
            None => r is None,
            Some(g) => r is Some && r.unwrap().is(g),
        },
        final(m).n <= old(m).n + DICT_LOAD_WORK + 25 * d@.len(),
        r is Some ==> r.unwrap().content@.len() <= d@.len(),
{
    let n = d.len();
    if n < 8 || le_at(d, 0, 4) != 0xEC30A437 {
        return Some(raw_dict_exec(d, Tracked(m)));
    }
    if n == 8 {
        return None;
    }
    let id = le_at(d, 4, 4) as u32;
    let e = slice_subrange(d, 8, n);
    let ghost m0 = m.n;
    let (huf, a0) = match huf_desc_exec(e, Tracked(m)) {
        None => {
            return None;
        },
        Some(x) => x,
    };
    let (of, u1) = match seq_table_exec(slice_subrange(e, a0, e.len()), 1, 2, None, Ghost(None), Tracked(m)) {
        None => {
            return None;
        },
        Some(x) => x,
    };
    proof {
        assert(m.n <= m0 + HUF_DESC_WORK + 8 * (n - 8) + 1870);
    }
    let a1 = a0 + u1;
    let (ml, u2) = match seq_table_exec(slice_subrange(e, a1, e.len()), 2, 2, None, Ghost(None), Tracked(m)) {
        None => {
            return None;
        },
        Some(x) => x,
    };
    proof {
        assert(m.n <= m0 + HUF_DESC_WORK + 16 * (n - 8) + 3740);
    }
    let a2 = a1 + u2;
    let (ll, u3) = match seq_table_exec(slice_subrange(e, a2, e.len()), 0, 2, None, Ghost(None), Tracked(m)) {
        None => {
            return None;
        },
        Some(x) => x,
    };
    proof {
        assert(m.n <= m0 + HUF_DESC_WORK + 24 * (n - 8) + 5610);
    }
    let a = 8 + a2 + u3;
    if a + 12 > n {
        return None;
    }
    let csize = (n - (a + 12)) as u64;
    let r1 = le_at(d, a, 4);
    let r2 = le_at(d, a + 4, 4);
    let r3 = le_at(d, a + 8, 4);
    if r1 == 0 || r1 > csize || r2 == 0 || r2 > csize || r3 == 0 || r3 > csize {
        return None;
    }
    let content = tail_copy(d, a + 12, Tracked(m));
    proof {
        assert(pow2(9) == 512) by {
            lemma2_to64();
        }
        lemma_pow2_le(ll.log as nat, 9);
        lemma_pow2_le(of.log as nat, 9);
        lemma_pow2_le(ml.log as nat, 9);
    }
    let dl = bake(&ll, 0, Tracked(m));
    let dof = bake(&of, 1, Tracked(m));
    let dml = bake(&ml, 2, Tracked(m));
    proof {
        assert(m.n <= m0 + HUF_DESC_WORK + 25 * n + 5610 + 1536);
        reveal(DDict::is);
        assert(e@ =~= d@.subrange(8, n as int));
        assert(id as nat == le(d@, 4, 4));
    }
    Some(
        DDict {
            id,
            content,
            r1,
            r2,
            r3,
            huf: Some(huf),
            seqt: Some(SeqTabs { ll, of, ml, dl, dof, dml }),
        },
    )
}

// ---------------------------------------------------------------------------
// Decompressing
// ---------------------------------------------------------------------------

/// A window above 4 GiB comes only from a single-segment frame, whose
/// window is its content size.
proof fn lemma_big_window(bb: Seq<u8>)
    ensures
        frame_header(bb) matches Some(h) ==> (h.window > 0x1_0000_0000 ==> h.fcs == Some(h.window)),
{
    if let Some(h) = frame_header(bb) {
        let fhd = bb[0];
        let single = (fhd / 32) % 2 == 1;
        if !single {
            let wlog = (bb[1] / 8 + 10) as nat;
            lemma2_to64();
            if wlog < 31 {
                lemma_pow2_strictly_increases(wlog, 31);
            }
            assert(pow2(wlog) <= 0x8000_0000);
            assert(pow2(wlog) / 8 * (bb[1] % 8) as nat <= pow2(wlog)) by (nonlinear_arith)
                requires
                    (bb[1] % 8) < 8,
            ;
        }
    }
}

/// The blocks only append to the output (`stream::lemma_blocks_prefix`,
/// for any reach).
pub proof fn lemma_blocks_r_prefix(b: Seq<u8>, i: int, window: nat, reach: nat, st: FrameState)
    ensures
        blocks_r(b, i, window, reach, st) is Some ==> prefix(st.out, blocks_r(b, i, window, reach, st).unwrap().1.out),
    decreases b.len() - i,
{
    if 0 <= i && i + 3 <= b.len() {
        let bh = le(b, i, 3);
        let size = bh / 8;
        let bmax = min(window as int, BLOCK_MAX as int) as nat;
        let c = i + 3;
        let ty = (bh / 2) % 4;
        let next: Option<(int, FrameState)> = if ty == 0 && c + size <= b.len() {
            lemma_prefix_append(st.out, b.subrange(c, c + size));
            Some((c + size, FrameState { out: st.out + b.subrange(c, c + size), ..st }))
        } else if ty == 1 && c + 1 <= b.len() {
            lemma_prefix_append(st.out, Seq::new(size, |k: int| b[c]));
            Some((c + 1, FrameState { out: st.out + Seq::new(size, |k: int| b[c]), ..st }))
        } else if ty == 2 && c + size <= b.len() {
            let cb = b.subrange(c, c + size);
            match lit_section(cb, bmax, st.huf) {
                None => None,
                Some(l) => {
                    lemma_seq_section_prefix(cb.subrange(l.used, cb.len() as int), l.lits, reach, FrameState { huf: l.huf, ..st });
                    match compressed_block(cb, reach, bmax, st) {
                        None => None,
                        Some(st2) => Some((c + size, st2)),
                    }
                },
            }
        } else {
            None
        };
        if let Some((j, st2)) = next {
            if j <= b.len() {
                lemma_blocks_r_prefix(b, j, window, reach, st2);
                if blocks_r(b, j, window, reach, st2) is Some {
                    lemma_prefix_trans(st.out, st2.out, blocks_r(b, j, window, reach, st2).unwrap().1.out);
                }
            }
        }
    }
}

/// `frames_d` only appends.
proof fn lemma_frames_d_grows(b: Seq<u8>, i: int, out: Seq<u8>, g: Dict)
    ensures
        frames_d(b, i, out, g) is Some ==> frames_d(b, i, out, g).unwrap().len() >= out.len(),
    decreases b.len() - i,
{
    if 0 <= i && i + 5 <= b.len() {
        let m = le(b, i, 4);
        if skippable(m) {
            let size = le(b, i + 4, 4);
            if i + 8 <= b.len() && size + 8 < 0x1_0000_0000 && i + 8 + size <= b.len() {
                lemma_frames_d_grows(b, i + 8 + size, out, g);
            }
        } else if let Some((j, o)) = frame_d(b, i, g) {
            if j > i && j <= b.len() {
                lemma_frames_d_grows(b, j, out + o, g);
            }
        }
    }
}

/// One Zstandard frame at `i` with the dictionary `dict` (`frame_d`).
/// `d.out` holds the dictionary's content, and the frame's is appended
/// to it.
#[verifier::rlimit(40)]
fn frame_d_exec(
    b: &[u8],
    i: usize,
    dict: &DDict,
    d: &mut FrameDec,
    olimit: usize,
    Ghost(g): Ghost<Dict>,
    Tracked(m): Tracked<&mut Meter>,
) -> (r: (Step, usize))
    requires
        b@.len() < MAX_LIMIT,
        i + 4 <= b@.len(),
        dict.is(g),
        old(d).out@ == g.st.out,
        g.st.out.len() <= olimit <= MAX_LIMIT,
    ensures
        // Work: as `frame_exec`, with the tables' copies paid for by the
        // magic number, and one step a byte to hash the frame's content.
        old(d).out@.len() <= final(d).out@.len() <= olimit,
        r.0 is Done ==> i < r.1 <= b@.len(),
        r.0 is Done ==> final(m).n <= old(m).n + (BLOCK_BYTE_WORK + 1) * (r.1 - i) + 11 * (final(d).out@.len()
            - old(d).out@.len()),
        final(m).n <= old(m).n + (BLOCK_BYTE_WORK + 1) * (b@.len() - i) + 11 * (final(d).out@.len() - old(d).out@.len())
            + BLOCK_FAIL_WORK,
        match frame_d(b@, i as int, g) {
            None => !(r.0 is Done),
            Some((j, o)) => match r.0 {
                Step::Done => {
                    &&& r.1 as int == j
                    &&& final(d).out@ == g.st.out + o
                    &&& final(d).out@.len() <= olimit
                },
                Step::Bad => false,
                Step::Limit => g.st.out.len() + o.len() > olimit,
            },
        },
{
    proof {
        reveal(DDict::is);
    }
    let h = match frame_header_exec(slice_subrange(b, i + 4, b.len())) {
        None => {
            return (Step::Bad, 0);
        },
        Some(h) => h,
    };
    if h.dict_id != 0 && h.dict_id != dict.id as u64 {
        return (Step::Bad, 0);
    }
    let dl = dict.content.len();
    // A window above the limit means output above it only when the window
    // is the content size. On 64-bit targets every such window is
    // (`lemma_big_window`); on 32-bit ones that is checked.
    proof {
        lemma_big_window(b@.subrange(i + 4, b@.len() as int));
    }
    #[cfg(target_pointer_width = "64")]
    let big = h.window > MAX_LIMIT as u64;
    #[cfg(target_pointer_width = "32")]
    let big = h.window > MAX_LIMIT as u64 && match h.fcs {
        Some(f) => f == h.window,
        None => false,
    };
    if big {
        proof {
            let sb = b@.subrange(i + 4, b@.len() as int);
            let sh = frame_header(sb).unwrap();
            assert(sh.fcs == Some(sh.window));
            if let Some((j, o)) = frame_d(b@, i as int, g) {
                assert(o.len() == sh.window);
            }
        }
        return (Step::Limit, 0);
    }
    d.fstart = 0;
    d.r1 = dict.r1;
    d.r2 = dict.r2;
    d.r3 = dict.r3;
    d.huf = copy_huf_opt(&dict.huf, Tracked(m));
    d.seqt = copy_seqt_opt(&dict.seqt, Tracked(m));
    proof {
        assert(fout(d.out@, 0) =~= g.st.out);
        lemma_table_size(dict, g);
    }
    let reach = h.window + dl as u64;
    let mut hash = Xxh64::new();
    let (res, j) = blocks_exec(b, i + 4 + h.size, h.window, reach, d, olimit, &mut hash, false, Ghost(g.st), Tracked(m));
    proof {
        let i1 = i + 4 + h.size;
        lemma_work_add(BLOCK_BYTE_WORK + 1int, i1 - i, b@.len() - i1);
        if res is Done {
            lemma_work_add(BLOCK_BYTE_WORK + 1int, i1 - i, j - i1);
            lemma_work_add(BLOCK_BYTE_WORK + 1int, j - i, 4);
        }
        lemma_blocks_grows(b@, i + 4 + h.size, h.window as nat, reach as nat, g.st);
        lemma_blocks_r_prefix(b@, i + 4 + h.size, h.window as nat, reach as nat, g.st);
    }
    match res {
        Step::Done => {},
        _ => {
            return (res, 0);
        },
    }
    let n = d.out.len() - dl;
    let content = slice_subrange(d.out.as_slice(), dl, d.out.len());
    proof {
        assert(fout(d.out@, 0) =~= d.out@);
        assert(d.out@.subrange(0, dl as int) == g.st.out);
        assert(d.out@ =~= g.st.out + content@);
    }
    match h.fcs {
        Some(f) => {
            if f != n as u64 {
                return (Step::Bad, 0);
            }
        },
        None => {},
    }
    if h.checksum {
        if j > b.len() || b.len() - j < 4 {
            return (Step::Bad, 0);
        }
        let mut hh = Xxh64::new();
        hh.update(content, Ghost(Seq::empty()));
        proof {
            m.n = m.n + content@.len();
            assert(Seq::<u8>::empty() + content@ =~= content@);
        }
        let x = hh.digest(Ghost(content@));
        proof {
            m.n = m.n + 32;
        }
        let want = le_at(b, j, 4);
        let lo = x & 0xFFFF_FFFF;
        proof {
            assert(x & 0xFFFF_FFFF == x % 0x1_0000_0000) by (bit_vector);
        }
        if want != lo {
            return (Step::Bad, 0);
        }
        (Step::Done, j + 4)
    } else {
        (Step::Done, j)
    }
}

/// A dictionary, ready to decompress with (`ZSTD_DDict` in a context):
/// the loaded dictionary and a buffer that starts each frame holding its
/// content, so a frame's matches can reach into it. The buffer is kept
/// between calls, so the content is copied once, when the decoder is made.
pub struct DictDecoder {
    dict: DDict,
    work: Vec<u8>,
    #[allow(dead_code)]
    g: Ghost<Dict>,
}

impl DictDecoder {
    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        &&& self.dict.is(self.g@)
        &&& self.work@ == self.g@.st.out
    }

    /// The dictionary, as the spec has it.
    pub closed spec fn view(&self) -> Dict {
        self.g@
    }

    fn new(dict: DDict, Ghost(g): Ghost<Dict>, Tracked(m): Tracked<&mut Meter>) -> (r: DictDecoder)
        requires
            dict.is(g),
        ensures
            r@ == g,
            final(m).n == old(m).n + g.st.out.len(),
    {
        proof {
            reveal(DDict::is);
        }
        let work = copy_vec(&dict.content, Tracked(m));
        proof {
            reveal(DDict::is);
        }
        DictDecoder { dict, work, g: Ghost(g) }
    }

    /// The dictionary `d`, as `ZSTD_DCtx_loadDictionary` reads it
    /// (`dict_load`). `None`: it is corrupted.
    pub fn load(d: &[u8]) -> (r: Option<DictDecoder>)
        requires
            d@.len() < DICT_MAX,
        ensures
            match dict_load(d@) {
                None => r is None,
                Some(g) => r is Some && r.unwrap()@ == g,
            },
    {
        let tracked mut m = Meter { n: 0 };
        DictDecoder::load_metered(d, Tracked(&mut m))
    }

    /// `load`, counting its steps in `m`: linear in the dictionary.
    pub fn load_metered(d: &[u8], Tracked(m): Tracked<&mut Meter>) -> (r: Option<DictDecoder>)
        requires
            d@.len() < DICT_MAX,
        ensures
            match dict_load(d@) {
                None => r is None,
                Some(g) => r is Some && r.unwrap()@ == g,
            },
            final(m).n <= old(m).n + DICT_LOAD_WORK + 26 * d@.len(),
    {
        match load_dict(d, Tracked(m)) {
            None => None,
            Some(dd) => {
                proof {
                    reveal(DDict::is);
                }
                Some(DictDecoder::new(dd, Ghost(dict_load(d@).unwrap()), Tracked(m)))
            },
        }
    }

    /// The raw-content dictionary `d` (`raw_dict`), as
    /// `ZSTD_DCtx_refPrefix` takes it.
    pub fn raw(d: &[u8]) -> (r: DictDecoder)
        requires
            d@.len() < DICT_MAX,
        ensures
            r@ == raw_dict(d@),
    {
        let tracked mut m = Meter { n: 0 };
        DictDecoder::new(raw_dict_exec(d, Tracked(&mut m)), Ghost(raw_dict(d@)), Tracked(&mut m))
    }

    /// Another decoder with the same dictionary, for another context.
    pub fn copy(&self) -> (r: DictDecoder)
        ensures
            r@ == self@,
    {
        proof {
            use_type_invariant(self);
            reveal(DDict::is);
        }
        let tracked mut m = Meter { n: 0 };
        let dd = DDict {
            id: self.dict.id,
            content: copy_vec(&self.dict.content, Tracked(&mut m)),
            r1: self.dict.r1,
            r2: self.dict.r2,
            r3: self.dict.r3,
            huf: copy_huf_opt(&self.dict.huf, Tracked(&mut m)),
            seqt: copy_seqt_opt(&self.dict.seqt, Tracked(&mut m)),
        };
        DictDecoder::new(dd, Ghost(self.g@), Tracked(&mut m))
    }

    /// A copy of the loaded dictionary, for a decoder that keeps its own
    /// buffer (`stream::Stream::set_dict`).
    pub fn ddict(&self) -> (r: DDict)
        ensures
            r.is(self@),
    {
        proof {
            use_type_invariant(self);
            reveal(DDict::is);
        }
        let tracked mut m = Meter { n: 0 };
        DDict {
            id: self.dict.id,
            content: copy_vec(&self.dict.content, Tracked(&mut m)),
            r1: self.dict.r1,
            r2: self.dict.r2,
            r3: self.dict.r3,
            huf: copy_huf_opt(&self.dict.huf, Tracked(&mut m)),
            seqt: copy_seqt_opt(&self.dict.seqt, Tracked(&mut m)),
        }
    }

    /// The size of the dictionary's content.
    pub fn content_len(&self) -> (r: usize)
        ensures
            r as nat == self@.st.out.len(),
    {
        proof {
            use_type_invariant(self);
            reveal(DDict::is);
        }
        self.dict.content.len()
    }

    /// The dictionary's ID (0 for raw content).
    pub fn id(&self) -> (r: u32)
        ensures
            r as nat == self@.id,
    {
        proof {
            use_type_invariant(self);
            reveal(DDict::is);
        }
        self.dict.id
    }

    /// Decompresses all frames of `b` with the dictionary
    /// (`decompress_d`), giving up once the output would pass `limit`
    /// bytes. Gives the decoder back with the result.
    pub fn decompress(self, b: &[u8], limit: usize) -> (r: (DictDecoder, Result<Vec<u8>, Error>))
        requires
            b@.len() < MAX_LIMIT,
            limit <= DICT_LIMIT,
        ensures
            r.0@ == self@,
            match r.1 {
                Ok(v) => decompress_d(b@, self@) == Some(v@) && v@.len() <= limit,
                Err(Error::Corrupt) => decompress_d(b@, self@) is None,
                Err(Error::TooLarge) => decompress_d(b@, self@) is None || decompress_d(b@, self@).unwrap().len()
                    > limit,
            },
    {
        proof {
            use_type_invariant(&self);
        }
        let tracked mut m = Meter { n: 0 };
        self.decompress_metered(b, limit, Tracked(&mut m))
    }

    /// `decompress`, counting its steps in `m`: linear, as
    /// `frame::decompress_metered`, with one step more a byte of output to
    /// move it out of the buffer, and a failure refilling the buffer.
    pub fn decompress_metered(self, b: &[u8], limit: usize, Tracked(m): Tracked<&mut Meter>) -> (r: (
        DictDecoder,
        Result<Vec<u8>, Error>,
    ))
        requires
            b@.len() < MAX_LIMIT,
            limit <= DICT_LIMIT,
        ensures
            r.0@ == self@,
            match r.1 {
                Ok(v) => decompress_d(b@, self@) == Some(v@) && v@.len() <= limit,
                Err(Error::Corrupt) => decompress_d(b@, self@) is None,
                Err(Error::TooLarge) => decompress_d(b@, self@) is None || decompress_d(b@, self@).unwrap().len()
                    > limit,
            },
            match r.1 {
                Ok(v) => final(m).n <= old(m).n + BYTE_WORK * b@.len() + 12 * v@.len() + 1,
                Err(_) => final(m).n <= old(m).n + BYTE_WORK * b@.len() + 12 * limit + BLOCK_FAIL_WORK
                    + self@.st.out.len(),
            },
    {
        proof {
            use_type_invariant(&self);
        }
        let ghost gd = self.g@;
        let dict = self.dict;
        let work = self.work;
        decompress_with(dict, work, b, limit, Ghost(gd), Tracked(m))
    }
}

/// `DictDecoder::decompress`, on the decoder's parts.
fn decompress_with(
    dict: DDict,
    work: Vec<u8>,
    b: &[u8],
    limit: usize,
    Ghost(gd): Ghost<Dict>,
    Tracked(mt): Tracked<&mut Meter>,
) -> (r: (DictDecoder, Result<Vec<u8>, Error>))
    requires
        b@.len() < MAX_LIMIT,
        limit <= DICT_LIMIT,
        dict.is(gd),
        work@ == gd.st.out,
    ensures
        r.0@ == gd,
        match r.1 {
            Ok(v) => decompress_d(b@, gd) == Some(v@) && v@.len() <= limit,
            Err(Error::Corrupt) => decompress_d(b@, gd) is None,
            Err(Error::TooLarge) => decompress_d(b@, gd) is None || decompress_d(b@, gd).unwrap().len() > limit,
        },
        match r.1 {
            Ok(v) => final(mt).n <= old(mt).n + BYTE_WORK * b@.len() + 12 * v@.len() + 1,
            Err(_) => final(mt).n <= old(mt).n + BYTE_WORK * b@.len() + 12 * limit + BLOCK_FAIL_WORK + gd.st.out.len(),
        },
{
    let mut out: Vec<u8> = Vec::new();
    let mut d = FrameDec { out: work, fstart: 0, r1: 1, r2: 4, r3: 8, huf: None, seqt: None, lits: Vec::new() };
    let ghost full = decompress_d(b@, gd);
    let mut i: usize = 0;
    loop
        invariant
            b@.len() < MAX_LIMIT,
            limit <= DICT_LIMIT,
            dict.is(gd),
            d.out@ == gd.st.out,
            i <= b@.len(),
            out@.len() <= limit,
            mt.n <= old(mt).n + BYTE_WORK * i + 12 * out@.len(),
            full == decompress_d(b@, gd),
            frames_d(b@, i as int, out@, gd) == full,
        decreases b@.len() - i,
    {
        proof {
            mt.n = mt.n + 1;
            lemma_work_add(BYTE_WORK as int, i as int, b@.len() - i);
            lemma_work_add(BLOCK_BYTE_WORK + 1int, i as int, b@.len() - i);
            assert(BYTE_WORK == BLOCK_BYTE_WORK + 2);
        }
        if i == b.len() {
            return (DictDecoder { dict, work: d.out, g: Ghost(gd) }, Ok(out));
        }
        let ghost o0 = out@.len();
        match next_frame(b, i, &dict, &mut d, &mut out, limit, Ghost(gd), Tracked(mt)) {
            Ok(j) => {
                proof {
                    lemma_work_add(BYTE_WORK as int, i as int, j - i);
                    lemma_work_add(BLOCK_BYTE_WORK + 1int, i as int, j - i);
                }
                i = j;
            },
            Err(e) => {
                return (DictDecoder { dict, work: d.out, g: Ghost(gd) }, Err(e));
            },
        }
    }
}

/// The frame or skippable frame at `i` (`frames_d`, one step): appends
/// its content to `out`, and gives where the next one starts.
fn next_frame(
    b: &[u8],
    i: usize,
    dict: &DDict,
    d: &mut FrameDec,
    out: &mut Vec<u8>,
    limit: usize,
    Ghost(gd): Ghost<Dict>,
    Tracked(mt): Tracked<&mut Meter>,
) -> (r: Result<usize, Error>)
    requires
        b@.len() < MAX_LIMIT,
        i < b@.len(),
        limit <= DICT_LIMIT,
        dict.is(gd),
        old(d).out@ == gd.st.out,
        old(out)@.len() <= limit,
    ensures
        final(d).out@ == gd.st.out,
        // Work: a frame's, and one step a byte to move its content to
        // `out`; a failure also refills the buffer with the content.
        old(out)@.len() <= final(out)@.len(),
        r is Ok ==> final(mt).n <= old(mt).n + (BLOCK_BYTE_WORK + 1) * (r.unwrap() - i) + 12 * (final(out)@.len()
            - old(out)@.len()),
        r is Err ==> final(mt).n <= old(mt).n + (BLOCK_BYTE_WORK + 1) * (b@.len() - i) + 12 * (limit - old(out)@.len())
            + BLOCK_FAIL_WORK + gd.st.out.len(),
        match r {
            Ok(j) => i < j <= b@.len() && final(out)@.len() <= limit && frames_d(b@, i as int, old(out)@, gd)
                == frames_d(b@, j as int, final(out)@, gd),
            Err(Error::Corrupt) => frames_d(b@, i as int, old(out)@, gd) is None,
            Err(Error::TooLarge) => frames_d(b@, i as int, old(out)@, gd) is None || frames_d(
                b@,
                i as int,
                old(out)@,
                gd,
            ).unwrap().len() > limit,
        },
{
    proof {
        reveal(DDict::is);
    }
    let dlen = dict.content.len();
    if b.len() - i < 5 {
        return Err(Error::Corrupt);
    }
    let m = le_at(b, i, 4);
    if is_skippable(m) {
        if b.len() - i < 8 {
            return Err(Error::Corrupt);
        }
        let size = le_at(b, i + 4, 4);
        if size + 8 >= 0x1_0000_0000 || size as usize > b.len() - i - 8 {
            return Err(Error::Corrupt);
        }
        return Ok(i + 8 + size as usize);
    }
    if m != 0xFD2FB528 {
        return Err(Error::Corrupt);
    }
    let ghost o0 = out@;
    let room = limit - out.len();
    let (step, j) = frame_d_exec(b, i, dict, d, dlen + room, Ghost(gd), Tracked(mt));
    match step {
        Step::Done => {},
        _ => {
            proof {
                if step is Limit {
                    if let Some((j2, o)) = frame_d(b@, i as int, gd) {
                        if j2 > i && j2 <= b@.len() {
                            lemma_frames_d_grows(b@, j2, o0 + o, gd);
                        }
                    }
                }
            }
            // The buffer holds the dictionary's content again.
            d.out.clear();
            verilith_core::prims::extend(&mut d.out, dict.content.as_slice());
            proof {
                mt.n = mt.n + dict.content@.len();
                assert(d.out@ =~= gd.st.out);
            }
            return match step {
                Step::Limit => Err(Error::TooLarge),
                _ => Err(Error::Corrupt),
            };
        },
    }
    let ghost o = d.out@.subrange(dlen as int, d.out@.len() as int);
    crate::prims::extend_from(out, d.out.as_slice(), dlen, d.out.len() - dlen);
    d.out.truncate(dlen);
    proof {
        mt.n = mt.n + o.len();
        let (j2, fo) = frame_d(b@, i as int, gd).unwrap();
        assert(o =~= fo);
        assert(d.out@ =~= gd.st.out);
    }
    if j <= i || j > b.len() {
        return Err(Error::Corrupt);
    }
    Ok(j)
}

} // verus!
