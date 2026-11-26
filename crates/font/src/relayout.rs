//! Laying the input's own tables out again, unchanged: the path that
//! makes every valid font accepted. `canon_tables` picks the input's
//! known tables in order of tag, `assemble` (proven) lays them out, and
//! the lemmas here show the result holds exactly the input's tables and,
//! for a valid font, is well formed.
use crate::build::*;
use crate::prims::*;
use crate::spec::*;
use crate::spec_same::*;
use crate::same::in_get;
use vstd::prelude::*;

verus! {

pub proof fn lemma_kl_vals()
    ensures
        known_list().len() == 21,
        known_list()[0] == T_CFF,
        known_list()[1] == T_GDEF,
        known_list()[2] == T_GPOS,
        known_list()[3] == T_GSUB,
        known_list()[4] == T_OS2,
        known_list()[5] == T_CMAP,
        known_list()[6] == T_CVT,
        known_list()[7] == T_FPGM,
        known_list()[8] == T_GASP,
        known_list()[9] == T_GLYF,
        known_list()[10] == T_HEAD,
        known_list()[11] == T_HHEA,
        known_list()[12] == T_HMTX,
        known_list()[13] == T_KERN,
        known_list()[14] == T_LOCA,
        known_list()[15] == T_MAXP,
        known_list()[16] == T_NAME,
        known_list()[17] == T_POST,
        known_list()[18] == T_PREP,
        known_list()[19] == T_VHEA,
        known_list()[20] == T_VMTX,
{
}

pub proof fn lemma_kl_known(i: int)
    requires
        0 <= i < 21,
    ensures
        known_tag(known_list()[i] as int),
{
    lemma_kl_vals();
    if i == 0 {
        assert(known_list()[0] == T_CFF);
    } else if i == 1 {
        assert(known_list()[1] == T_GDEF);
    } else if i == 2 {
        assert(known_list()[2] == T_GPOS);
    } else if i == 3 {
        assert(known_list()[3] == T_GSUB);
    } else if i == 4 {
        assert(known_list()[4] == T_OS2);
    } else if i == 5 {
        assert(known_list()[5] == T_CMAP);
    } else if i == 6 {
        assert(known_list()[6] == T_CVT);
    } else if i == 7 {
        assert(known_list()[7] == T_FPGM);
    } else if i == 8 {
        assert(known_list()[8] == T_GASP);
    } else if i == 9 {
        assert(known_list()[9] == T_GLYF);
    } else if i == 10 {
        assert(known_list()[10] == T_HEAD);
    } else if i == 11 {
        assert(known_list()[11] == T_HHEA);
    } else if i == 12 {
        assert(known_list()[12] == T_HMTX);
    } else if i == 13 {
        assert(known_list()[13] == T_KERN);
    } else if i == 14 {
        assert(known_list()[14] == T_LOCA);
    } else if i == 15 {
        assert(known_list()[15] == T_MAXP);
    } else if i == 16 {
        assert(known_list()[16] == T_NAME);
    } else if i == 17 {
        assert(known_list()[17] == T_POST);
    } else if i == 18 {
        assert(known_list()[18] == T_PREP);
    } else if i == 19 {
        assert(known_list()[19] == T_VHEA);
    } else if i == 20 {
        assert(known_list()[20] == T_VMTX);
    }
}

pub proof fn lemma_kl_adj(i: int)
    requires
        0 < i < 21,
    ensures
        known_list()[i - 1] < known_list()[i],
{
    lemma_kl_vals();
    if i == 1 {
        assert(known_list()[0] == T_CFF && known_list()[1] == T_GDEF);
    } else if i == 2 {
        assert(known_list()[1] == T_GDEF && known_list()[2] == T_GPOS);
    } else if i == 3 {
        assert(known_list()[2] == T_GPOS && known_list()[3] == T_GSUB);
    } else if i == 4 {
        assert(known_list()[3] == T_GSUB && known_list()[4] == T_OS2);
    } else if i == 5 {
        assert(known_list()[4] == T_OS2 && known_list()[5] == T_CMAP);
    } else if i == 6 {
        assert(known_list()[5] == T_CMAP && known_list()[6] == T_CVT);
    } else if i == 7 {
        assert(known_list()[6] == T_CVT && known_list()[7] == T_FPGM);
    } else if i == 8 {
        assert(known_list()[7] == T_FPGM && known_list()[8] == T_GASP);
    } else if i == 9 {
        assert(known_list()[8] == T_GASP && known_list()[9] == T_GLYF);
    } else if i == 10 {
        assert(known_list()[9] == T_GLYF && known_list()[10] == T_HEAD);
    } else if i == 11 {
        assert(known_list()[10] == T_HEAD && known_list()[11] == T_HHEA);
    } else if i == 12 {
        assert(known_list()[11] == T_HHEA && known_list()[12] == T_HMTX);
    } else if i == 13 {
        assert(known_list()[12] == T_HMTX && known_list()[13] == T_KERN);
    } else if i == 14 {
        assert(known_list()[13] == T_KERN && known_list()[14] == T_LOCA);
    } else if i == 15 {
        assert(known_list()[14] == T_LOCA && known_list()[15] == T_MAXP);
    } else if i == 16 {
        assert(known_list()[15] == T_MAXP && known_list()[16] == T_NAME);
    } else if i == 17 {
        assert(known_list()[16] == T_NAME && known_list()[17] == T_POST);
    } else if i == 18 {
        assert(known_list()[17] == T_POST && known_list()[18] == T_PREP);
    } else if i == 19 {
        assert(known_list()[18] == T_PREP && known_list()[19] == T_VHEA);
    } else if i == 20 {
        assert(known_list()[19] == T_VHEA && known_list()[20] == T_VMTX);
    }
}

pub proof fn lemma_kl_lt(a: int, b: int)
    requires
        0 <= a < b < 21,
    ensures
        known_list()[a] < known_list()[b],
    decreases b - a,
{
    lemma_kl_adj(b);
    if a < b - 1 {
        lemma_kl_lt(a, b - 1);
    }
}

/// Tag `known_list()[i]`.
fn known_at(i: usize) -> (t: u32)
    requires
        i < 21,
    ensures
        t == known_list()[i as int],
{
    proof {
        lemma_kl_vals();
    }
    match i {
        0 => T_CFF,
        1 => T_GDEF,
        2 => T_GPOS,
        3 => T_GSUB,
        4 => T_OS2,
        5 => T_CMAP,
        6 => T_CVT,
        7 => T_FPGM,
        8 => T_GASP,
        9 => T_GLYF,
        10 => T_HEAD,
        11 => T_HHEA,
        12 => T_HMTX,
        13 => T_KERN,
        14 => T_LOCA,
        15 => T_MAXP,
        16 => T_NAME,
        17 => T_POST,
        18 => T_PREP,
        19 => T_VHEA,
        _ => T_VMTX,
    }
}

pub proof fn lemma_find_push(s: Tables, x: (u32, Seq<u8>), t: int, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        find_in(s.push(x), t, i) == if find_in(s, t, i) < s.len() {
            find_in(s, t, i)
        } else if x.0 == t {
            s.len() as int
        } else {
            s.len() + 1int
        },
    decreases s.len() - i,
{
    if i < s.len() {
        assert(s.push(x)[i] == s[i]);
        if s[i].0 != t {
            lemma_find_push(s, x, t, i + 1);
        }
    } else {
        assert(s.push(x)[i] == x);
        if x.0 != t {
            assert(find_in(s.push(x), t, i + 1) == s.len() + 1);
        }
    }
}

/// What `canon_upto` holds: the input's tables among the first `i` known
/// tags, in order, each a known tag.
pub proof fn lemma_canon(tv: Tables, i: int)
    requires
        0 <= i <= 21,
    ensures
        canon_upto(tv, i).len() <= i,
        forall|k: int| 0 <= k < canon_upto(tv, i).len() ==> known_tag(#[trigger] canon_upto(tv, i)[k].0 as int),
        forall|j: int|
            0 <= j < 21 ==> ((find_in(canon_upto(tv, i), #[trigger] known_list()[j] as int, 0) < canon_upto(
                tv,
                i,
            ).len()) == (j < i && in_has(tv, known_list()[j] as int))),
        forall|j: int|
            0 <= j < 21 && find_in(canon_upto(tv, i), #[trigger] known_list()[j] as int, 0) < canon_upto(
                tv,
                i,
            ).len() ==> canon_upto(tv, i)[find_in(canon_upto(tv, i), known_list()[j] as int, 0)].1
                == in_table(tv, known_list()[j] as int),
    decreases i,
{
    lemma_kl_vals();
    if i > 0 {
        lemma_canon(tv, i - 1);
        let p = canon_upto(tv, i - 1);
        let t = known_list()[i - 1];
        if in_has(tv, t as int) {
            let x = (t, in_table(tv, t as int));
            assert(canon_upto(tv, i) == p.push(x));
            lemma_kl_known(i - 1);
            assert forall|k: int| 0 <= k < p.push(x).len() implies known_tag(#[trigger] p.push(x)[k].0 as int) by {
                if k < p.len() {
                    assert(p.push(x)[k] == p[k]);
                }
            }
            assert forall|j: int| 0 <= j < 21 implies ((find_in(p.push(x), #[trigger] known_list()[j] as int, 0)
                < p.push(x).len()) == (j < i && in_has(tv, known_list()[j] as int))) && (find_in(
                p.push(x),
                known_list()[j] as int,
                0,
            ) < p.push(x).len() ==> p.push(x)[find_in(p.push(x), known_list()[j] as int, 0)].1 == in_table(
                tv,
                known_list()[j] as int,
            )) by {
                lemma_find_push(p, x, known_list()[j] as int, 0);
                if j < i - 1 {
                    lemma_kl_lt(j, i - 1);
                } else if j > i - 1 {
                    lemma_kl_lt(i - 1, j);
                }
                let f = find_in(p, known_list()[j] as int, 0);
                if f < p.len() {
                    assert(p.push(x)[f] == p[f]);
                }
            }
        } else {
            assert forall|j: int| 0 <= j < 21 implies ((find_in(p, #[trigger] known_list()[j] as int, 0) < p.len())
                == (j < i && in_has(tv, known_list()[j] as int))) by {
                if j == i - 1 {
                }
            }
        }
    }
}

/// The input's known tables, in increasing order of tag: `canon`.
pub fn canon_tables(ts: &Vec<Table>) -> (c: Vec<Table>)
    ensures
        tview(c@) == canon(tview(ts@)),
        sorted_tags(c@),
        c@.len() <= 21,
{
    let ghost tv = tview(ts@);
    let mut c: Vec<Table> = Vec::new();
    let ghost mut jl: int = 0;
    assert(tview(c@) =~= canon_upto(tv, 0));
    let mut i: usize = 0;
    while i < 21
        invariant
            i <= 21,
            tv == tview(ts@),
            tview(c@) == canon_upto(tv, i as int),
            sorted_tags(c@),
            c@.len() > 0 ==> 0 <= jl < i && c@[c@.len() - 1].tag == known_list()[jl],
        decreases 21 - i,
    {
        let t = known_at(i);
        proof {
            lemma_canon(tv, i as int);
        }
        match in_get(ts, t) {
            Some(x) => {
                let ghost c0 = c@;
                c.push(Table { tag: t, data: to_vec(x) });
                proof {
                    assert(tview(c@) =~= tview(c0).push((t, in_table(tv, t as int))));
                    if c0.len() > 0 {
                        lemma_kl_lt(jl, i as int);
                    }
                    assert forall|k: int| 0 < k < c@.len() implies #[trigger] tag_step(c@, k) by {
                        if k < c0.len() {
                            assert(tag_step(c0, k));
                        }
                    }
                    jl = i as int;
                }
            },
            None => {},
        }
        i += 1;
    }
    proof {
        lemma_canon(tv, 21);
        assert(tview(c@).len() == c@.len());
    }
    c
}

/// `assemble`'s output holds the tables of `c` at the indices of `c`.
pub proof fn lemma_find_eq(out: Seq<u8>, c: Tables, t: int, i: int)
    requires
        0 <= i,
        num_tables(out) == c.len(),
        forall|k: int| 0 <= k < c.len() ==> #[trigger] rec_tag(out, k) == c[k].0,
    ensures
        find_from(out, t, i) == find_in(c, t, i),
    decreases c.len() - i,
{
    if i < c.len() {
        assert(rec_tag(out, i) == c[i].0);
        if c[i].0 != t {
            lemma_find_eq(out, c, t, i + 1);
        }
    }
}

/// What `assemble` returns for the canonical tables.
pub open spec fn relaid(tv: Tables, c: Tables, out: Seq<u8>) -> bool {
    &&& c == canon(tv)
    &&& wf_directory(out)
    &&& num_tables(out) == c.len()
    &&& forall|k: int| 0 <= k < c.len() ==> #[trigger] rec_tag(out, k) == c[k].0
    &&& forall|k: int| 0 <= k < c.len() ==> #[trigger] holds_table(out, c[k], k)
}

proof fn lemma_relaid_one(tv: Tables, c: Tables, out: Seq<u8>, j: int)
    requires
        relaid(tv, c, out),
        0 <= j < 21,
    ensures
        same_one(tv, out, known_list()[j]),
{
    let t = known_list()[j];
    lemma_canon(tv, 21);
    lemma_find_eq(out, c, t as int, 0);
    let f = find_in(c, t as int, 0);
    if f < c.len() {
        lemma_find_in(c, t as int, 0);
        assert(holds_table(out, c[f], f));
    }
}

/// The re-laid-out font holds exactly the input's known tables, and its
/// every table is a known one.
pub proof fn lemma_relaid(tv: Tables, c: Tables, out: Seq<u8>)
    requires
        relaid(tv, c, out),
    ensures
        same_tables(tv, out),
        forall|i: int| 0 <= i < num_tables(out) ==> known_tag(#[trigger] rec_tag(out, i)),
{
    lemma_kl_vals();
    lemma_relaid_one(tv, c, out, 0);
    lemma_relaid_one(tv, c, out, 1);
    lemma_relaid_one(tv, c, out, 2);
    lemma_relaid_one(tv, c, out, 3);
    lemma_relaid_one(tv, c, out, 4);
    lemma_relaid_one(tv, c, out, 5);
    lemma_relaid_one(tv, c, out, 6);
    lemma_relaid_one(tv, c, out, 7);
    lemma_relaid_one(tv, c, out, 8);
    lemma_relaid_one(tv, c, out, 9);
    lemma_relaid_one(tv, c, out, 10);
    lemma_relaid_one(tv, c, out, 11);
    lemma_relaid_one(tv, c, out, 12);
    lemma_relaid_one(tv, c, out, 13);
    lemma_relaid_one(tv, c, out, 14);
    lemma_relaid_one(tv, c, out, 15);
    lemma_relaid_one(tv, c, out, 16);
    lemma_relaid_one(tv, c, out, 17);
    lemma_relaid_one(tv, c, out, 18);
    lemma_relaid_one(tv, c, out, 19);
    lemma_relaid_one(tv, c, out, 20);
    lemma_canon(tv, 21);
    assert forall|i: int| 0 <= i < num_tables(out) implies known_tag(#[trigger] rec_tag(out, i)) by {
        assert(rec_tag(out, i) == c[i].0);
    }
}


/// Fonts with the same known tables agree on table `t`.
pub proof fn lemma_same_tag(tv: Tables, a: Seq<u8>, b: Seq<u8>, t: u32)
    requires
        same_one(tv, a, t),
        same_one(tv, b, t),
        t != T_HEAD,
    ensures
        has_table(a, t as int) == has_table(b, t as int),
        has_table(a, t as int) ==> table(a, t as int) == table(b, t as int),
{
}

/// Fonts with the same known tables have `head`s alike for `wf_head`
/// and `loc_format`.
pub proof fn lemma_same_head(tv: Tables, a: Seq<u8>, b: Seq<u8>)
    requires
        same_one(tv, a, T_HEAD),
        same_one(tv, b, T_HEAD),
    ensures
        has_table(a, T_HEAD as int) == has_table(b, T_HEAD as int),
        has_table(a, T_HEAD as int) ==> wf_head(table(a, T_HEAD as int)) == wf_head(table(b, T_HEAD as int)),
        has_table(a, T_HEAD as int) && table(a, T_HEAD as int).len() >= 52 ==> loc_format(table(a, T_HEAD as int))
            == loc_format(table(b, T_HEAD as int)),
{
    if has_table(a, T_HEAD as int) {
        let ha = table(a, T_HEAD as int);
        let hb = table(b, T_HEAD as int);
        let hi = in_table(tv, T_HEAD as int);
        assert(head_eq(ha, hi) && head_eq(hb, hi));
        assert(ha.len() == hb.len());
        if ha.len() >= 54 {
            assert forall|j: int| 0 <= j < 54 && !(8 <= j < 12) implies ha[j] == hb[j] by {
                assert(ha[j] == hi[j]);
                assert(hb[j] == hi[j]);
            }
            assert(ha[0] == hb[0] && ha[1] == hb[1] && ha[2] == hb[2] && ha[3] == hb[3]);
            assert(ha[12] == hb[12] && ha[13] == hb[13] && ha[14] == hb[14] && ha[15] == hb[15]);
            assert(ha[18] == hb[18] && ha[19] == hb[19]);
            assert(ha[36] == hb[36] && ha[37] == hb[37] && ha[38] == hb[38] && ha[39] == hb[39]);
            assert(ha[40] == hb[40] && ha[41] == hb[41] && ha[42] == hb[42] && ha[43] == hb[43]);
            assert(ha[50] == hb[50] && ha[51] == hb[51] && ha[52] == hb[52] && ha[53] == hb[53]);
        } else if ha.len() >= 52 {
            assert(ha[50] == hi[50] && ha[51] == hi[51]);
            assert(hb[50] == hi[50] && hb[51] == hi[51]);
        }
    }
}

proof fn lemma_same_core(tv: Tables, a: Seq<u8>, b: Seq<u8>)
    requires
        same_tables(tv, a),
        same_tables(tv, b),
    ensures
        has_required(a) == has_required(b),
        has_required(a) ==> wf_core(a) == wf_core(b),
{
    lemma_same_tag(tv, a, b, T_MAXP);
    lemma_same_tag(tv, a, b, T_HHEA);
    lemma_same_tag(tv, a, b, T_HMTX);
    lemma_same_tag(tv, a, b, T_CMAP);
    lemma_same_tag(tv, a, b, T_NAME);
    lemma_same_tag(tv, a, b, T_POST);
    lemma_same_tag(tv, a, b, T_OS2);
    lemma_same_tag(tv, a, b, T_GLYF);
    lemma_same_head(tv, a, b);
}

proof fn lemma_same_outlines(tv: Tables, a: Seq<u8>, b: Seq<u8>)
    requires
        same_tables(tv, a),
        same_tables(tv, b),
        u32_at(a, 0) == u32_at(b, 0),
        has_required(a),
        wf_core(a),
    ensures
        wf_outlines(a) == wf_outlines(b),
{
    lemma_same_tag(tv, a, b, T_MAXP);
    lemma_same_tag(tv, a, b, T_GLYF);
    lemma_same_tag(tv, a, b, T_CFF);
    lemma_same_tag(tv, a, b, T_LOCA);
    lemma_same_head(tv, a, b);
}

proof fn lemma_same_extras(tv: Tables, a: Seq<u8>, b: Seq<u8>)
    requires
        same_tables(tv, a),
        same_tables(tv, b),
        has_required(a),
    ensures
        wf_extras(a) == wf_extras(b),
{
    lemma_same_tag(tv, a, b, T_MAXP);
    lemma_same_tag(tv, a, b, T_GDEF);
    lemma_same_tag(tv, a, b, T_GSUB);
    lemma_same_tag(tv, a, b, T_GPOS);
    lemma_same_tag(tv, a, b, T_CVT);
    lemma_same_tag(tv, a, b, T_GASP);
    lemma_same_tag(tv, a, b, T_KERN);
    lemma_same_tag(tv, a, b, T_VHEA);
    lemma_same_tag(tv, a, b, T_VMTX);
    assert(mark_set_limit(a) == mark_set_limit(b));
}

/// Two fonts with the same known tables (and `head` the same but for
/// checkSumAdjustment) and the same version are well formed alike.
pub proof fn lemma_same_wf(tv: Tables, a: Seq<u8>, b: Seq<u8>)
    requires
        same_tables(tv, a),
        same_tables(tv, b),
        u32_at(a, 0) == u32_at(b, 0),
    ensures
        has_required(a) == has_required(b),
        has_required(a) ==> wf_tables(a) == wf_tables(b),
{
    lemma_same_core(tv, a, b);
    if has_required(a) {
        if wf_core(a) {
            lemma_same_outlines(tv, a, b);
        }
        lemma_same_extras(tv, a, b);
    }
}

/// The re-laid-out tables of a valid font make a well-formed font.
pub proof fn lemma_relaid_wf(tv: Tables, out: Seq<u8>)
    requires
        valid_tables(tv),
        same_tables(tv, out),
        wf_directory(out),
        words_sum(out, 0, out.len() as int / 4) == 0xB1B0_AFBA,
        forall|i: int| 0 <= i < num_tables(out) ==> known_tag(#[trigger] rec_tag(out, i)),
        u32_at(out, 0) == if in_has(tv, T_GLYF as int) {
            TAG_TRUETYPE
        } else {
            TAG_OTTO
        },
    ensures
        wf_font(out),
{
    let s = choose|s: Seq<u8>| wf_font(s) && #[trigger] same_tables(tv, s);
    assert(same_one(tv, s, T_GLYF));
    assert(wf_outlines(s));
    lemma_same_wf(tv, out, s);
}


/// A valid font's canonical tables can be laid out.
pub proof fn lemma_can_assemble(tv: Tables, c: Seq<Table>)
    requires
        valid_tables(tv),
        tview(c) == canon(tv),
        sorted_tags(c),
        c.len() <= 21,
    ensures
        can_assemble(c),
{
    let s = choose|s: Seq<u8>| wf_font(s) && #[trigger] same_tables(tv, s);
    assert(same_one(tv, s, T_HEAD));
    assert(has_required(s));
    assert(wf_core(s));
    let hs = table(s, T_HEAD as int);
    assert(head_eq(hs, in_table(tv, T_HEAD as int)));
    lemma_kl_vals();
    lemma_canon(tv, 21);
    assert(known_list()[10] == T_HEAD);
    let cv = tview(c);
    let f = find_in(cv, T_HEAD as int, 0);
    assert(f < cv.len());
    assert(cv.len() == c.len());
}

} // verus!
