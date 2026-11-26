//! The public entry point: input cleanup and the basic URL parser, proven
//! against `spec::parse_url`.
use crate::encode::*;
use crate::parse::*;
use crate::spec::*;
use crate::tables::*;
use crate::url::*;
use vstd::prelude::*;

verus! {

proof fn lemma_trim(s: Seq<u8>, i: int, j: int)
    requires
        0 <= i <= j <= s.len(),
        forall|k: int| 0 <= k < i ==> is_c0_control_or_space(#[trigger] s[k]),
        forall|k: int| j <= k < s.len() ==> is_c0_control_or_space(#[trigger] s[k]),
        i < j ==> !is_c0_control_or_space(s[i]) && !is_c0_control_or_space(s[j - 1]),
        i == j ==> forall|k: int| 0 <= k < s.len() ==> is_c0_control_or_space(#[trigger] s[k]),
    ensures
        trim_c0_space(s) == s.subrange(i, j),
    decreases s.len(),
{
    if s.len() > 0 && is_c0_control_or_space(s[0]) {
        let t = s.skip(1);
        if i == j {
            lemma_trim(t, 0, 0);
            assert(s.subrange(i, j) =~= t.subrange(0, 0));
        } else {
            assert(i > 0);
            lemma_trim(t, i - 1, j - 1);
            assert(s.subrange(i, j) =~= t.subrange(i - 1, j - 1));
        }
    } else if s.len() > 0 && is_c0_control_or_space(s.last()) {
        let t = s.drop_last();
        if i == j {
            assert(false);
        } else {
            assert(j < s.len());
            lemma_trim(t, i, j);
            assert(s.subrange(i, j) =~= t.subrange(i, j));
        }
    } else {
        if s.len() == 0 {
            assert(s.subrange(i, j) =~= s);
        } else {
            if i == j {
                assert(false);
            }
            assert(i == 0) by {
                if i > 0 {
                    assert(is_c0_control_or_space(s[0]));
                }
            }
            assert(j == s.len()) by {
                if j < s.len() {
                    assert(is_c0_control_or_space(s[s.len() - 1]));
                }
            }
            assert(s.subrange(i, j) =~= s);
        }
    }
}

pub open spec fn not_tab_newline() -> spec_fn(u8) -> bool {
    |c: u8| !is_ascii_tab_or_newline(c)
}

/// Removes ASCII tab or newline from `s[a..b]`.
pub(crate) fn remove_tab_newline_exec(s: &[u8], a: usize, b: usize, Tracked(cost): Tracked<&mut Meter>) -> (r: Vec<u8>)
    requires
        a <= b <= s.len(),
    ensures
        r@ == remove_tab_newline(s@.subrange(a as int, b as int)),
        r.len() <= b - a,
        final(cost).n == old(cost).n + (b - a),
{
    let mut out: Vec<u8> = Vec::with_capacity(b - a);
    let mut i = a;
    proof {
        reveal(Seq::filter);
        assert(s@.subrange(a as int, a as int) =~= Seq::<u8>::empty());
        assert(Seq::<u8>::empty().filter(not_tab_newline()) =~= Seq::<u8>::empty());
    }
    while i < b
        invariant
            a <= i <= b <= s.len(),
            out@ == s@.subrange(a as int, i as int).filter(not_tab_newline()),
            out.len() <= i - a,
            cost.n == old(cost).n + (i - a),
        decreases b - i,
    {
        proof {
            cost.n = cost.n + 1;
        }
        let c = s[i];
        proof {
            assert(s@.subrange(a as int, i + 1) =~= s@.subrange(a as int, i as int).push(c));
            s@.subrange(a as int, i as int).lemma_filter_push(c, not_tab_newline());
        }
        if !(c == 0x09 || c == 0x0A || c == 0x0D) {
            out.push(c);
        }
        i = i + 1;
    }
    proof {
        assert(remove_tab_newline(s@.subrange(a as int, b as int)) == s@.subrange(a as int, b as int).filter(not_tab_newline())) by {
            assert(not_tab_newline() =~= (|c: u8| !is_ascii_tab_or_newline(c)));
        }
    }
    out
}

pub(crate) proof fn lemma_filter_identity(s: Seq<u8>)
    requires
        forall|k: int| 0 <= k < s.len() ==> !is_ascii_tab_or_newline(#[trigger] s[k]),
    ensures
        remove_tab_newline(s) == s,
    decreases s.len(),
{
    reveal(Seq::filter);
    if s.len() > 0 {
        lemma_filter_identity(s.drop_last());
        assert(s.drop_last().push(s.last()) =~= s);
        s.drop_last().lemma_filter_push(s.last(), |c: u8| !is_ascii_tab_or_newline(c));
    } else {
        assert(s.filter(|c: u8| !is_ascii_tab_or_newline(c)) =~= s);
    }
}

/// Whether `t[a..b]` has a tab or newline. No early exit, so the compiler
/// vectorizes it.
#[inline(always)]
fn any_tab_newline_in(t: &[u8], a: usize, b: usize, Tracked(cost): Tracked<&mut Meter>) -> (r: bool)
    requires
        a <= b <= t.len(),
    ensures
        !r ==> forall|q: int| a <= q < b ==> !is_ascii_tab_or_newline(#[trigger] t@[q]),
        final(cost).n == old(cost).n + (b - a),
{
    let mut acc = false;
    let mut k = a;
    while k < b
        invariant
            a <= k <= b <= t.len(),
            !acc ==> forall|q: int| a <= q < k ==> !is_ascii_tab_or_newline(#[trigger] t@[q]),
            cost.n == old(cost).n + (k - a),
        decreases b - k,
    {
        proof {
            cost.n = cost.n + 1;
        }
        let c = t[k];
        acc = acc | (c == 9u8) | (c == 10u8) | (c == 13u8);
        k = k + 1;
    }
    acc
}

/// Whether `t` has a tab or newline: 16-byte blocks with SIMD, the last one
/// overlapping, and a byte loop only below 16 bytes.
#[inline(always)]
pub(crate) fn any_tab_newline(t: &[u8], Tracked(cost): Tracked<&mut Meter>) -> (r: bool)
    ensures
        !r ==> forall|q: int| 0 <= q < t.len() ==> !is_ascii_tab_or_newline(#[trigger] t@[q]),
        final(cost).n <= old(cost).n + t.len() + 32,
{
    let n = t.len();
    if n < 16 {
        return any_tab_newline_in(t, 0, n, Tracked(cost));
    }
    if n >= 64 {
        // Long inputs: the compiler vectorizes the branch-free loop over
        // 32-byte blocks, which beats a test per 16 bytes.
        let main = n - n % 32;
        let a = any_tab_newline_in(t, 0, main, Tracked(cost));
        let w = vstd::slice::slice_subrange(t, n - 32, n);
        let b = any_tab_newline_in(w, 0, 32, Tracked(cost));
        proof {
            if !a && !b {
                assert forall|q: int| 0 <= q < t.len() implies !is_ascii_tab_or_newline(#[trigger] t@[q]) by {
                    if q >= main {
                        assert(t@[q] == w@[q - (n - 32)]);
                    }
                }
            }
        }
        return a | b;
    }
    let mut k: usize = 0;
    while n - k > 16
        invariant
            k <= n,
            16 <= n,
            n == t.len(),
            forall|q: int| 0 <= q < k ==> !is_ascii_tab_or_newline(#[trigger] t@[q]),
            cost.n == old(cost).n + k,
        decreases n - k,
    {
        if crate::simd::tab_nl16(t, k) {
            return true;
        }
        proof {
            cost.n = cost.n + 16;
        }
        k = k + 16;
    }
    let last = crate::simd::tab_nl16(t, n - 16);
    proof {
        cost.n = cost.n + 16;
        if !last {
            assert forall|q: int| 0 <= q < t.len() implies !is_ascii_tab_or_newline(#[trigger] t@[q]) by {
                if q >= k {
                    assert(n - 16 <= q);
                }
            }
        }
    }
    last
}

/// The parser's work bound for an `n`-byte input and an `m`-byte base.
pub open spec fn parse_cost(n: nat, m: nat) -> int {
    3 * n + 32 + crate::parse::simple_cost(n) + machine_cost(n, m)
}

/// Parses `input` against an optional base URL (the WHATWG URL parser).
pub(crate) fn parse(input: &[u8], base: Option<&Url>) -> (r: Option<Url>)
    requires
        base matches Some(b) ==> b.ok(),
    ensures
        r matches Some(u) ==> u.ok() && parse_url(input@, base_rec(base)) == Some(u@),
        r is None ==> parse_url(input@, base_rec(base)) is None,
{
    let tracked mut meter = Meter { n: 0 };
    parse_metered(input, base, Tracked(&mut meter))
}

/// The parser with its step meter: the theorem that parsing takes linear
/// time is this function's bound on the meter, `parse_cost`, which is
/// linear in the lengths of the input and of the base URL's href.
pub(crate) fn parse_metered(input: &[u8], base: Option<&Url>, Tracked(cost): Tracked<&mut Meter>) -> (r: Option<Url>)
    requires
        base matches Some(b) ==> b.ok(),
    ensures
        r matches Some(u) ==> u.ok() && parse_url(input@, base_rec(base)) == Some(u@),
        r is None ==> parse_url(input@, base_rec(base)) is None,
        final(cost).n <= old(cost).n + parse_cost(input.len() as nat, base_len(base_rec(base))),
{
    parse_metered_in(input, base, &mut crate::host::Scratch::new(), Tracked(cost))
}

/// `parse`, with the host parser's scratch storage kept by the caller.
#[inline(always)]
pub(crate) fn parse_sc(input: &[u8], base: Option<&Url>, sc: &mut crate::host::Scratch) -> (r: Option<Url>)
    requires
        base matches Some(b) ==> b.ok(),
    ensures
        r matches Some(u) ==> u.ok() && parse_url(input@, base_rec(base)) == Some(u@),
        r is None ==> parse_url(input@, base_rec(base)) is None,
{
    let tracked mut meter = Meter { n: 0 };
    parse_metered_in(input, base, sc, Tracked(&mut meter))
}

pub(crate) fn parse_metered_in(input: &[u8], base: Option<&Url>, sc: &mut crate::host::Scratch, Tracked(cost): Tracked<&mut Meter>) -> (r: Option<Url>)
    requires
        base matches Some(b) ==> b.ok(),
    ensures
        r matches Some(u) ==> u.ok() && parse_url(input@, base_rec(base)) == Some(u@),
        r is None ==> parse_url(input@, base_rec(base)) is None,
        final(cost).n <= old(cost).n + parse_cost(input.len() as nat, base_len(base_rec(base))),
{
    let n = input.len();
    // Most URLs need neither trimming nor the state machine.
    let ghost c0 = cost.n;
    match crate::parse::parse_simple(input, base, sc, Tracked(cost)) {
        Some(u) => {
            proof {
                crate::why::lemma_run_r(input@, base_rec(base), None, initial_machine(State::SchemeStart, new_url()), 0);
                lemma_trim(input@, 0, n as int);
                assert(input@.subrange(0, n as int) =~= input@);
                lemma_filter_identity(input@);
                crate::ascii::lemma_parse_url_ascii(input@, base_rec(base));
                crate::creds::lemma_parse_url_creds(input@, base_rec(base));
            }
            return Some(u);
        },
        None => {},
    }
    let ghost c1 = cost.n;
    let mut i = 0;
    while i < n && input[i] <= 0x20
        invariant
            i <= n == input.len(),
            forall|k: int| 0 <= k < i ==> is_c0_control_or_space(#[trigger] input@[k]),
            cost.n == c1 + i,
        decreases n - i,
    {
        proof {
            cost.n = cost.n + 1;
        }
        i = i + 1;
    }
    let mut j = n;
    while j > i && input[j - 1] <= 0x20
        invariant
            i <= j <= n == input.len(),
            forall|k: int| j <= k < n ==> is_c0_control_or_space(#[trigger] input@[k]),
            cost.n == c1 + i + (n - j),
        decreases j,
    {
        proof {
            cost.n = cost.n + 1;
        }
        j = j - 1;
    }
    proof {
        if i == j {
            assert forall|k: int| 0 <= k < n implies is_c0_control_or_space(#[trigger] input@[k]) by {
                if k >= i {
                    assert(k >= j);
                }
            }
        }
        lemma_trim(input@, i as int, j as int);
    }
    let t = vstd::slice::slice_subrange(input, i, j);
    let acc = any_tab_newline(t, Tracked(cost));
    proof {
        crate::ascii::lemma_parse_url_ascii(input@, base_rec(base));
        crate::creds::lemma_parse_url_creds(input@, base_rec(base));
    }
    if !acc {
        let s = vstd::slice::slice_subrange(input, i, j);
        proof {
            assert(s@ =~= t@);
            lemma_filter_identity(s@);
        }
        run_machine_in(s, base, sc, Tracked(cost))
    } else {
        let v = remove_tab_newline_exec(input, i, j, Tracked(cost));
        run_machine_in(v.as_slice(), base, sc, Tracked(cost))
    }
}

/// Why the parser rejects `input` against `base`: `None` when it accepts
/// it, else the reason `spec::parse_why` gives.
pub(crate) fn explain(input: &[u8], base: Option<&Url>) -> (r: Option<Why>)
    requires
        base matches Some(b) ==> b.ok(),
    ensures
        r == parse_why(input@, base_rec(base)),
{
    let tracked mut meter = Meter { n: 0 };
    let n = input.len();
    let mut i = 0;
    while i < n && input[i] <= 0x20
        invariant
            i <= n == input.len(),
            forall|k: int| 0 <= k < i ==> is_c0_control_or_space(#[trigger] input@[k]),
        decreases n - i,
    {
        i = i + 1;
    }
    let mut j = n;
    while j > i && input[j - 1] <= 0x20
        invariant
            i <= j <= n == input.len(),
            forall|k: int| j <= k < n ==> is_c0_control_or_space(#[trigger] input@[k]),
        decreases j,
    {
        j = j - 1;
    }
    proof {
        if i == j {
            assert forall|k: int| 0 <= k < n implies is_c0_control_or_space(#[trigger] input@[k]) by {
                if k >= i {
                    assert(k >= j);
                }
            }
        }
        lemma_trim(input@, i as int, j as int);
    }
    let v = remove_tab_newline_exec(input, i, j, Tracked(&mut meter));
    let mut sc = crate::host::Scratch::new();
    match run_machine_f(v.as_slice(), base, &mut sc, Tracked(&mut meter)) {
        Ok(_) => None,
        Err(f) => Some(crate::why::fault_why_exec(v.as_slice(), f)),
    }
}

} // verus!
