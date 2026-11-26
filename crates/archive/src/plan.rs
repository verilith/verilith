//! The extraction planner and its safety theorems.
//!
//! `plan` turns an archive's members into a list of steps (create this
//! directory, write this file, make this link) or refuses the archive.
//! Theorems:
//!
//! - `plan`'s postcondition: a returned plan satisfies `policy::plan_safe`,
//!   and each step is `policy::item_of` its member.
//! - `theorem_contained`: under `plan_safe`, in the model of the operating
//!   system in `policy::resolve`, no step's path and no symbolic link's
//!   target resolves outside the extraction root, whichever of the plan's
//!   links exist at the time.
use crate::order::*;
use crate::policy::*;
use crate::read::{read_entry, MAX_ARCHIVE};
use crate::spec::*;
use crate::tar::find_byte_exec;
use crate::zip::{copy_range, Entry};
#[cfg(verus_only)]
use crate::zip::views;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// The containment theorem.
// ---------------------------------------------------------------------
/// Every link's target, walked from the link's directory, is safe.
pub open spec fn links_ok(links: Map<Path, Path>) -> bool {
    forall|p: Path| #[trigger] links.dom().contains(p) ==> p.len() > 0 && safe_walk(links, p.drop_last(), links[p])
}

/// A safe walk does not escape, in a file system holding any subset `sub`
/// of the links.
pub proof fn lemma_resolve(links: Map<Path, Path>, sub: Map<Path, Path>, cur: Path, rest: Path, fuel: nat)
    requires
        links_ok(links),
        sub.submap_of(links),
        safe_walk(links, cur, rest),
    ensures
        !(resolve(sub, cur, rest, fuel) is Escaped),
    decreases fuel, rest.len(),
{
    if rest.len() > 0 {
        let c = rest[0];
        let r = rest.subrange(1, rest.len() as int);
        if is_dotdot(c) {
            lemma_resolve(links, sub, cur.drop_last(), r, fuel);
        } else {
            let n = cur.push(c);
            if sub.dom().contains(n) {
                assert(links.dom().contains(n));
                if fuel > 0 {
                    assert(sub[n] + r =~= links[n]);
                    assert(n.drop_last() =~= cur);
                    lemma_resolve(links, sub, cur, links[n], (fuel - 1) as nat);
                }
            } else if links.dom().contains(n) {
                assert(r.len() == 0);
            } else {
                lemma_resolve(links, sub, n, r, fuel);
            }
        }
    }
}

proof fn lemma_links_dom(items: Seq<SItem>, n: int, p: Path)
    requires
        0 <= n <= items.len(),
        links_upto(items, n).dom().contains(p),
    ensures
        exists|j: int| 0 <= j < n && (#[trigger] items[j]).kind is Symlink && items[j].path == p,
    decreases n,
{
    if n > 0 {
        if items[n - 1].kind is Symlink && items[n - 1].path == p {
        } else {
            lemma_links_dom(items, n - 1, p);
        }
    }
}

proof fn lemma_links_has(items: Seq<SItem>, n: int, j: int)
    requires
        0 <= j < n <= items.len(),
        items[j].kind is Symlink,
        distinct_paths(items),
    ensures
        links_upto(items, n).dom().contains(items[j].path),
        links_upto(items, n)[items[j].path] == items[j].target,
    decreases n,
{
    if n - 1 > j {
        lemma_links_has(items, n - 1, j);
        assert(items[j].path != items[n - 1].path);
    }
}

proof fn lemma_plan_links_ok(items: Seq<SItem>)
    requires
        plan_safe(items),
    ensures
        links_ok(links_of(items)),
{
    let links = links_of(items);
    assert forall|p: Path| #[trigger] links.dom().contains(p) implies p.len() > 0 && safe_walk(
        links,
        p.drop_last(),
        links[p],
    ) by {
        lemma_links_dom(items, items.len() as int, p);
        let j = choose|j: int| 0 <= j < items.len() && (#[trigger] items[j]).kind is Symlink && items[j].path == p;
        lemma_links_has(items, items.len() as int, j);
        assert(item_safe(items, j));
    }
}

/// **Extraction stays inside the root.** For a plan satisfying the policy,
/// in a file system whose symbolic links under the root are any subset of
/// the plan's (so: at any moment of the extraction into a directory that
/// had no links of its own), following any number of links:
///
/// - the path of every step resolves inside the root, and
/// - the target of every symbolic link the plan creates resolves inside
///   the root.
pub proof fn theorem_contained(items: Seq<SItem>, i: int, sub: Map<Path, Path>, fuel: nat)
    requires
        plan_safe(items),
        0 <= i < items.len(),
        sub.submap_of(links_of(items)),
    ensures
        !(resolve(sub, Seq::empty(), items[i].path, fuel) is Escaped),
        items[i].kind is Symlink ==> !(resolve(sub, items[i].path.drop_last(), items[i].target, fuel) is Escaped),
{
    lemma_plan_links_ok(items);
    assert(item_safe(items, i));
    lemma_resolve(links_of(items), sub, Seq::empty(), items[i].path, fuel);
    if items[i].kind is Symlink {
        lemma_resolve(links_of(items), sub, items[i].path.drop_last(), items[i].target, fuel);
    }
}

// ---------------------------------------------------------------------
// Plan items.
// ---------------------------------------------------------------------
/// One step of an extraction plan.
#[derive(Debug)]
pub struct Item {
    /// Where, relative to the extraction root.
    pub path: Vec<Vec<u8>>,
    pub kind: Kind,
    /// A symbolic link's target, relative to the link's directory; or a
    /// hard link's, relative to the root.
    pub target: Vec<Vec<u8>>,
    /// The archive member this step extracts.
    pub entry: usize,
}

pub open spec fn pv(v: Seq<Vec<u8>>) -> Path {
    Seq::new(v.len(), |i: int| v[i]@)
}

impl Item {
    pub open spec fn sv(&self) -> SItem {
        SItem { path: pv(self.path@), kind: self.kind, target: pv(self.target@) }
    }
}

pub open spec fn sitems(v: Seq<Item>) -> Seq<SItem> {
    Seq::new(v.len(), |i: int| v[i].sv())
}

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum Why {
    /// The name is empty, absolute, has a `..` component, a NUL or a
    /// backslash, or names nothing.
    Path,
    /// Two members have the same path.
    Duplicate,
    /// The path passes through a symbolic link of the same archive.
    ThroughSymlink,
    /// A symbolic link's target is absolute, unreadable, leaves the root or
    /// passes through another symbolic link.
    SymlinkTarget,
    /// A hard link's target is not an earlier regular file of the archive.
    HardlinkTarget,
    /// The sorting routine misbehaved. Never seen; see TRUST.md.
    Internal,
}

/// Why an archive was refused, and for which member.
#[derive(Debug)]
pub struct Rejected {
    pub entry: usize,
    pub why: Why,
}

fn is_symlink(k: Kind) -> (r: bool)
    ensures
        r == (k is Symlink),
{
    match k {
        Kind::Symlink => true,
        _ => false,
    }
}

fn is_hardlink(k: Kind) -> (r: bool)
    ensures
        r == (k is Hardlink),
{
    match k {
        Kind::Hardlink => true,
        _ => false,
    }
}

fn is_file(k: Kind) -> (r: bool)
    ensures
        r == (k is File),
{
    match k {
        Kind::File => true,
        _ => false,
    }
}

fn is_other(k: Kind) -> (r: bool)
    ensures
        r == (k is Other),
{
    match k {
        Kind::Other => true,
        _ => false,
    }
}

fn dup(v: &Vec<u8>) -> (r: Vec<u8>)
    ensures
        r@ == v@,
{
    let r = copy_range(v.as_slice(), 0, v.len());
    proof {
        assert(r@ =~= v@);
    }
    r
}

fn comps_exec(s: &[u8]) -> (r: Vec<Vec<u8>>)
    ensures
        pv(r@) == comps_from(s@, 0),
{
    let n = s.len();
    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(pv(out@) + comps_from(s@, 0) =~= comps_from(s@, 0));
    }
    while i < n
        invariant
            i <= n,
            n == s@.len(),
            comps_from(s@, 0) == pv(out@) + comps_from(s@, i as int),
        decreases n - i,
    {
        let k = find_byte_exec(s, i, n, 0x2f);
        let dot = k - i == 1 && s[i] == 0x2e;
        proof {
            assert(is_dot(s@.subrange(i as int, k as int)) == dot);
            assert(comps_from(s@, n as int) =~= Seq::<Seq<u8>>::empty());
            assert(comps_from(s@, n + 1) =~= Seq::<Seq<u8>>::empty());
        }
        if k > i && !dot {
            let c = copy_range(s, i, k - i);
            proof {
                assert(pv(out@.push(c)) + comps_from(s@, k + 1) =~= pv(out@) + (seq![c@] + comps_from(s@, k + 1)));
            }
            out.push(c);
        }
        i = if k == n {
            n
        } else {
            k + 1
        };
    }
    proof {
        assert(pv(out@) + Seq::<Seq<u8>>::empty() =~= pv(out@));
    }
    out
}

fn clean_exec(s: &[u8]) -> (r: bool)
    ensures
        r == clean_bytes(s@),
{
    let n = s.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == s@.len(),
            forall|k: int| 0 <= k < i ==> s@[k] != 0 && s@[k] != 0x5c,
        decreases n - i,
    {
        if s[i] == 0 || s[i] == 0x5c {
            return false;
        }
        i += 1;
    }
    true
}

fn is_dotdot_exec(c: &Vec<u8>) -> (r: bool)
    ensures
        r == is_dotdot(c@),
{
    c.len() == 2 && c[0] == 0x2e && c[1] == 0x2e
}

fn no_dotdot_exec(p: &Vec<Vec<u8>>) -> (r: bool)
    ensures
        r == no_dotdot(pv(p@)),
{
    let n = p.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == p@.len(),
            forall|k: int| 0 <= k < i ==> !is_dotdot(#[trigger] pv(p@)[k]),
        decreases n - i,
    {
        if is_dotdot_exec(&p[i]) {
            proof {
                assert(is_dotdot(pv(p@)[i as int]));
            }
            return false;
        }
        i += 1;
    }
    true
}

fn name_ok_exec(s: &[u8]) -> (r: Option<Vec<Vec<u8>>>)
    ensures
        match r {
            Some(p) => name_ok(s@) && pv(p@) == comps_from(s@, 0),
            None => !name_ok(s@),
        },
{
    if s.len() == 0 || s[0] == 0x2f || !clean_exec(s) {
        return None;
    }
    let p = comps_exec(s);
    if p.len() == 0 || !no_dotdot_exec(&p) {
        return None;
    }
    Some(p)
}

fn target_ok_exec(s: &[u8]) -> (r: bool)
    ensures
        r == target_ok(s@),
{
    s.len() > 0 && s[0] != 0x2f && clean_exec(s) && s.len() <= MAX_LINK
}

fn eq_bytes(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    let n = a.len();
    if b.len() != n {
        return false;
    }
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == a@.len(),
            n == b@.len(),
            forall|k: int| 0 <= k < i ==> a@[k] == b@[k],
        decreases n - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    proof {
        assert(a@ =~= b@);
    }
    true
}

fn cmp_bytes(a: &[u8], b: &[u8]) -> (r: i8)
    ensures
        r < 0 ==> blt(a@, b@),
        r == 0 ==> a@ == b@,
        r > 0 ==> blt(b@, a@),
{
    let na = a.len();
    let nb = b.len();
    let mut i: usize = 0;
    loop
        invariant
            i <= na,
            i <= nb,
            na == a@.len(),
            nb == b@.len(),
            forall|k: int| 0 <= k < i ==> a@[k] == b@[k],
            blt(a@, b@) == blt_from(a@, b@, i as int),
            blt(b@, a@) == blt_from(b@, a@, i as int),
        decreases na - i,
    {
        if i >= na {
            if i >= nb {
                proof {
                    assert(a@ =~= b@);
                }
                return 0;
            }
            return -1;
        }
        if i >= nb {
            return 1;
        }
        if a[i] < b[i] {
            return -1;
        }
        if a[i] > b[i] {
            return 1;
        }
        i += 1;
    }
}

fn cmp_path(a: &Vec<Vec<u8>>, b: &Vec<Vec<u8>>) -> (r: i8)
    ensures
        r < 0 ==> plt(pv(a@), pv(b@)),
        r == 0 ==> pv(a@) == pv(b@),
        r > 0 ==> plt(pv(b@), pv(a@)),
{
    let na = a.len();
    let nb = b.len();
    let ghost p = pv(a@);
    let ghost q = pv(b@);
    let mut i: usize = 0;
    loop
        invariant
            i <= na,
            i <= nb,
            na == a@.len(),
            nb == b@.len(),
            p == pv(a@),
            q == pv(b@),
            forall|k: int| 0 <= k < i ==> p[k] == q[k],
            plt(p, q) == plt_from(p, q, i as int),
            plt(q, p) == plt_from(q, p, i as int),
        decreases na - i,
    {
        if i >= na {
            if i >= nb {
                proof {
                    assert(p =~= q);
                }
                return 0;
            }
            return -1;
        }
        if i >= nb {
            return 1;
        }
        let c = cmp_bytes(a[i].as_slice(), b[i].as_slice());
        proof {
            assert(p[i as int] == a@[i as int]@);
            assert(q[i as int] == b@[i as int]@);
            lemma_blt_irrefl(p[i as int], 0);
            lemma_blt_asym(p[i as int], q[i as int]);
        }
        if c < 0 {
            return -1;
        }
        if c > 0 {
            return 1;
        }
        i += 1;
    }
}

fn is_prefix_exec(a: &Vec<Vec<u8>>, b: &Vec<Vec<u8>>) -> (r: bool)
    ensures
        r == is_prefix(pv(a@), pv(b@)),
{
    let n = a.len();
    if b.len() < n {
        return false;
    }
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == a@.len(),
            n <= b@.len(),
            forall|k: int| 0 <= k < i ==> pv(a@)[k] == pv(b@)[k],
        decreases n - i,
    {
        if !eq_bytes(a[i].as_slice(), b[i].as_slice()) {
            proof {
                assert(pv(a@)[i as int] != pv(b@)[i as int]);
            }
            return false;
        }
        i += 1;
    }
    true
}

// ---------------------------------------------------------------------
// Members to items.
// ---------------------------------------------------------------------
/// Each item is what the policy makes of its member, and items are in
/// member order.
pub open spec fn items_match(b: Seq<u8>, es: Seq<SEntry>, items: Seq<Item>) -> bool {
    &&& forall|k: int|
        0 <= k < items.len() ==> (#[trigger] items[k]).entry < es.len() && item_of(
            b,
            es[items[k].entry as int],
            items[k].sv(),
        )
    &&& forall|k: int, m: int| 0 <= k < m < items.len() ==> (#[trigger] items[k]).entry < (#[trigger] items[m]).entry
}

/// Member `j` has no item: the policy refuses its name or its target.
pub open spec fn refused(b: Seq<u8>, es: Seq<SEntry>, j: int) -> bool {
    &&& 0 <= j < es.len()
    &&& !(es[j].kind is Other)
    &&& forall|it: SItem| !#[trigger] item_of(b, es[j], it)
}

proof fn lemma_kept_has(es: Seq<SEntry>, j: int)
    requires
        0 <= j < es.len(),
        !(es[j].kind is Other),
    ensures
        exists|k: int| 0 <= k < kept(es).len() && kept(es)[k] == es[j],
    decreases es.len(),
{
    let d = es.drop_last();
    if j == es.len() - 1 {
        assert(kept(es) == kept(d).push(es[j]));
        assert(kept(es)[kept(d).len() as int] == es[j]);
    } else {
        assert(d[j] == es[j]);
        lemma_kept_has(d, j);
        let k = choose|k: int| 0 <= k < kept(d).len() && kept(d)[k] == d[j];
        if es.last().kind is Other {
            assert(kept(es) == kept(d));
        } else {
            assert(kept(es) == kept(d).push(es.last()));
            assert(kept(es)[k] == kept(d)[k]);
        }
    }
}

/// An archive with a refused member has no plan.
proof fn lemma_refused_no_plan(b: Seq<u8>, es: Seq<SEntry>, j: int, p: Seq<SItem>)
    requires
        refused(b, es, j),
    ensures
        !plan_of(b, es, p),
{
    lemma_kept_has(es, j);
    let k = choose|k: int| 0 <= k < kept(es).len() && kept(es)[k] == es[j];
    if plan_of(b, es, p) {
        assert(item_of(b, kept(es)[k], p[k]));
    }
}

/// `item_of` determines the item, so an archive has at most one plan.
proof fn lemma_plan_unique(b: Seq<u8>, es: Seq<SEntry>, p: Seq<SItem>, q: Seq<SItem>)
    requires
        plan_of(b, es, p),
        plan_of(b, es, q),
    ensures
        p == q,
{
    assert forall|k: int| 0 <= k < p.len() implies p[k] == q[k] by {
        assert(item_of(b, kept(es)[k], p[k]));
        assert(item_of(b, kept(es)[k], q[k]));
        let e = kept(es)[k];
        if !(e.kind is Symlink) && !(e.kind is Hardlink) {
            assert(p[k].target =~= q[k].target);
        }
    }
    assert(p =~= q);
}

fn build_items(b: &[u8], es: &Vec<Entry>) -> (r: Result<Vec<Item>, Rejected>)
    requires
        in_bounds(views(es@), b@.len() as int),
        b@.len() < MAX_ARCHIVE,
    ensures
        r matches Ok(items) ==> items_match(b@, views(es@), items@) && plan_of(b@, views(es@), sitems(items@)),
        r matches Err(e) ==> refused(b@, views(es@), e.entry as int) && !(e.why is Internal),
{
    let n = es.len();
    let mut items: Vec<Item> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(views(es@).subrange(0, 0) =~= Seq::<SEntry>::empty());
        assert(sitems(items@) =~= Seq::<SItem>::empty());
    }
    while i < n
        invariant
            i <= n,
            n == es@.len(),
            in_bounds(views(es@), b@.len() as int),
            b@.len() < MAX_ARCHIVE,
            items_match(b@, views(es@), items@),
            forall|k: int| 0 <= k < items@.len() ==> (#[trigger] items@[k]).entry < i,
            plan_of(b@, views(es@).subrange(0, i as int), sitems(items@)),
        decreases n - i,
    {
        let e = &es[i];
        let ghost es1 = views(es@).subrange(0, i + 1);
        proof {
            assert(views(es@)[i as int] == e.sv());
            assert(views(es@)[i as int].end() <= b@.len());
            assert(es1.drop_last() =~= views(es@).subrange(0, i as int));
            assert(es1.last() == e.sv());
        }
        if !is_other(e.kind) {
            let path = match name_ok_exec(e.name.as_slice()) {
                Some(p) => p,
                None => return Err(Rejected { entry: i, why: Why::Path }),
            };
            let target = if is_symlink(e.kind) {
                let text = if e.link.len() > 0 {
                    dup(&e.link)
                } else {
                    match read_entry(b, e, MAX_LINK) {
                        Ok(v) => v,
                        Err(_) => return Err(Rejected { entry: i, why: Why::SymlinkTarget }),
                    }
                };
                if !target_ok_exec(text.as_slice()) {
                    return Err(Rejected { entry: i, why: Why::SymlinkTarget });
                }
                comps_exec(text.as_slice())
            } else if is_hardlink(e.kind) {
                match name_ok_exec(e.link.as_slice()) {
                    Some(p) => p,
                    None => return Err(Rejected { entry: i, why: Why::HardlinkTarget }),
                }
            } else {
                Vec::new()
            };
            let it = Item { path, kind: e.kind, target, entry: i };
            let ghost old_items = items@;
            proof {
                assert(item_of(b@, e.sv(), it.sv()));
            }
            items.push(it);
            proof {
                assert(kept(es1) == kept(views(es@).subrange(0, i as int)).push(e.sv()));
                assert(sitems(items@) =~= sitems(old_items).push(it.sv()));
                assert forall|k: int| 0 <= k < sitems(items@).len() implies #[trigger] item_of(
                    b@,
                    kept(es1)[k],
                    sitems(items@)[k],
                ) by {
                    if k < old_items.len() {
                        assert(item_of(b@, kept(views(es@).subrange(0, i as int))[k], sitems(old_items)[k]));
                    }
                }
            }
        } else {
            proof {
                assert(kept(es1) == kept(views(es@).subrange(0, i as int)));
            }
        }
        i += 1;
    }
    proof {
        assert(views(es@).subrange(0, n as int) =~= views(es@));
    }
    Ok(items)
}

// ---------------------------------------------------------------------
// Sorting, checked.
// ---------------------------------------------------------------------
/// The items' positions in an order hoped to be sorted by path. Plain Rust
/// that Verus does not look inside; nothing is assumed about the result,
/// which `check_sorted` validates.
#[verifier::external_body]
fn order_by_path(items: &Vec<Item>) -> (r: Vec<usize>) {
    let mut v: Vec<usize> = (0..items.len()).collect();
    v.sort_unstable_by(|&i, &j| items[i].path.cmp(&items[j].path));
    v
}

/// The paths in the order `ord`.
pub open spec fn pp(items: Seq<Item>, ord: Seq<usize>) -> Seq<Path> {
    Seq::new(ord.len(), |k: int| pv(items[ord[k] as int].path@))
}

/// `ord` lists every item once, strictly ascending by path; `inv` is its
/// inverse.
pub open spec fn sorted_perm(items: Seq<Item>, ord: Seq<usize>, inv: Seq<usize>) -> bool {
    let n = items.len();
    &&& ord.len() == n
    &&& inv.len() == n
    &&& forall|k: int| #![auto] 0 <= k < n ==> ord[k] < n && inv[ord[k] as int] == k
    &&& forall|i: int| #![auto] 0 <= i < n ==> inv[i] < n && ord[inv[i] as int] == i
    &&& forall|k: int| 0 <= k < n - 1 ==> plt(#[trigger] pp(items, ord)[k], pp(items, ord)[k + 1])
}

enum Sorted {
    Yes(Vec<usize>),
    /// Two items have this path; the second is this member.
    Dup(usize),
    No,
}

fn check_sorted(items: &Vec<Item>, ord: &Vec<usize>) -> (r: Sorted)
    ensures
        r matches Sorted::Yes(inv) ==> sorted_perm(items@, ord@, inv@),
        r matches Sorted::Dup(_) ==> !distinct_paths(sitems(items@)),
{
    let n = items.len();
    if ord.len() != n {
        return Sorted::No;
    }
    let mut inv: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            inv@.len() == i,
            forall|k: int| 0 <= k < i ==> inv@[k] == n,
        decreases n - i,
    {
        inv.push(n);
        i += 1;
    }
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            n == items@.len(),
            ord@.len() == n,
            inv@.len() == n,
            forall|m: int| #![auto] 0 <= m < k ==> ord@[m] < n && inv@[ord@[m] as int] == m,
            forall|i: int| #![auto] 0 <= i < n ==> inv@[i] == n || (inv@[i] < k && ord@[inv@[i] as int] == i),
        decreases n - k,
    {
        let i = ord[k];
        if i >= n || inv[i] != n {
            return Sorted::No;
        }
        inv.set(i, k);
        k += 1;
    }
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            inv@.len() == n,
            forall|j: int| 0 <= j < i ==> inv@[j] < n,
        decreases n - i,
    {
        if inv[i] >= n {
            return Sorted::No;
        }
        i += 1;
    }
    let mut k: usize = 1;
    while k < n
        invariant
            1 <= k,
            n == items@.len(),
            ord@.len() == n,
            inv@.len() == n,
            forall|m: int| #![auto] 0 <= m < n ==> ord@[m] < n && inv@[ord@[m] as int] == m,
            forall|m: int| 0 <= m < k - 1 ==> plt(#[trigger] pp(items@, ord@)[m], pp(items@, ord@)[m + 1]),
        decreases n - k,
    {
        let c = cmp_path(&items[ord[k - 1]].path, &items[ord[k]].path);
        if c == 0 {
            proof {
                let x = ord@[k - 1] as int;
                let y = ord@[k as int] as int;
                assert(inv@[x] != inv@[y]);
                let si = sitems(items@);
                assert(si[x].path == si[y].path);
                if x < y {
                    assert(!distinct_paths(si));
                } else {
                    assert(!distinct_paths(si));
                }
            }
            return Sorted::Dup(items[ord[k]].entry);
        }
        if c > 0 {
            return Sorted::No;
        }
        proof {
            assert(plt(pp(items@, ord@)[k - 1], pp(items@, ord@)[k as int]));
        }
        k += 1;
    }
    Sorted::Yes(inv)
}

proof fn lemma_distinct(items: Seq<Item>, ord: Seq<usize>, inv: Seq<usize>, i: int, j: int)
    requires
        sorted_perm(items, ord, inv),
        0 <= i < items.len(),
        0 <= j < items.len(),
        i != j,
    ensures
        pv(items[i].path@) != pv(items[j].path@),
{
    let ps = pp(items, ord);
    let a = inv[i] as int;
    let c = inv[j] as int;
    assert(ord[a] == i && ord[c] == j);
    assert(ps[a] == pv(items[i].path@));
    assert(ps[c] == pv(items[j].path@));
    if a < c {
        lemma_sorted(ps, a, c);
        lemma_plt_irrefl(ps[a], 0);
    } else {
        lemma_sorted(ps, c, a);
        lemma_plt_irrefl(ps[c], 0);
    }
}

proof fn lemma_sitems_distinct(items: Seq<Item>, ord: Seq<usize>, inv: Seq<usize>)
    requires
        sorted_perm(items, ord, inv),
    ensures
        distinct_paths(sitems(items)),
{
    assert forall|i: int, k: int| 0 <= i < k < sitems(items).len() implies (#[trigger] sitems(items)[i]).path != (
    #[trigger] sitems(items)[k]).path by {
        lemma_distinct(items, ord, inv, i, k);
    }
}

/// Whether `key` is an item's path, by binary search.
fn find(items: &Vec<Item>, ord: &Vec<usize>, key: &Vec<Vec<u8>>, Ghost(inv): Ghost<Seq<usize>>) -> (r: Option<usize>)
    requires
        sorted_perm(items@, ord@, inv),
    ensures
        match r {
            Some(j) => j < items@.len() && pv(items@[j as int].path@) == pv(key@),
            None => forall|j: int| 0 <= j < items@.len() ==> pv(#[trigger] items@[j].path@) != pv(key@),
        },
{
    let n = items.len();
    let ghost ps = pp(items@, ord@);
    let ghost kp = pv(key@);
    let mut lo: usize = 0;
    let mut hi: usize = n;
    while lo < hi
        invariant
            lo <= hi <= n,
            n == items@.len(),
            sorted_perm(items@, ord@, inv),
            ps == pp(items@, ord@),
            kp == pv(key@),
            forall|k: int| 0 <= k < lo ==> plt(#[trigger] ps[k], kp),
            forall|k: int| hi <= k < n ==> plt(kp, #[trigger] ps[k]),
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        let j = ord[mid];
        let c = cmp_path(&items[j].path, key);
        proof {
            assert(ps[mid as int] == pv(items@[j as int].path@));
        }
        if c == 0 {
            return Some(j);
        }
        if c < 0 {
            proof {
                assert forall|k: int| 0 <= k < mid + 1 implies plt(#[trigger] ps[k], kp) by {
                    if k < mid {
                        lemma_sorted(ps, k, mid as int);
                        lemma_plt_trans(ps[k], ps[mid as int], kp, 0);
                    }
                }
            }
            lo = mid + 1;
        } else {
            proof {
                assert forall|k: int| mid <= k < n implies plt(kp, #[trigger] ps[k]) by {
                    if k > mid {
                        lemma_sorted(ps, mid as int, k);
                        lemma_plt_trans(kp, ps[mid as int], ps[k], 0);
                    }
                }
            }
            hi = mid;
        }
    }
    proof {
        assert forall|j: int| 0 <= j < items@.len() implies pv(#[trigger] items@[j].path@) != kp by {
            let k = inv[j] as int;
            assert(ord@[k] == j);
            assert(ps[k] == pv(items@[j].path@));
            lemma_plt_irrefl(kp, 0);
            if k < lo {
                assert(plt(ps[k], kp));
            } else {
                assert(plt(kp, ps[k]));
            }
        }
    }
    None
}

// ---------------------------------------------------------------------
// No path passes through a symbolic link.
// ---------------------------------------------------------------------
/// No symbolic link is followed, in path order, by one of its extensions.
pub open spec fn adj_ok(items: Seq<Item>, ord: Seq<usize>) -> bool {
    forall|k: int|
        0 <= k < items.len() - 1 ==> !(items[ord[k] as int].kind is Symlink && is_prefix(
            #[trigger] pp(items, ord)[k],
            pp(items, ord)[k + 1],
        ))
}

proof fn lemma_no_link_prefix(items: Seq<Item>, ord: Seq<usize>, inv: Seq<usize>, i: int, m: int)
    requires
        sorted_perm(items, ord, inv),
        adj_ok(items, ord),
        0 <= i < items.len(),
        0 < m < items[i].path@.len(),
    ensures
        !links_of(sitems(items)).dom().contains(pv(items[i].path@).subrange(0, m)),
{
    let si = sitems(items);
    let p = pv(items[i].path@);
    let q = p.subrange(0, m);
    if links_of(si).dom().contains(q) {
        lemma_links_dom(si, si.len() as int, q);
        let j = choose|j: int| 0 <= j < si.len() && (#[trigger] si[j]).kind is Symlink && si[j].path == q;
        let ps = pp(items, ord);
        let a = inv[j] as int;
        let c = inv[i] as int;
        assert(ord[a] == j && ord[c] == i);
        assert(ps[a] == q);
        assert(ps[c] == p);
        assert(is_prefix(q, p));
        lemma_prefix_lt(q, p, 0);
        lemma_plt_irrefl(q, 0);
        if a == c {
            assert(false);
        } else if a > c {
            lemma_sorted(ps, c, a);
            lemma_plt_trans(q, p, q, 0);
            assert(false);
        } else {
            let r = ps[a + 1];
            assert(plt(ps[a], ps[a + 1]));
            if a + 1 < c {
                lemma_sorted(ps, a + 1, c);
            }
            lemma_between(q, r, p, 0);
            assert(items[ord[a] as int].kind is Symlink);
            assert(false);
        }
    }
}

proof fn lemma_walk_item(links: Map<Path, Path>, p: Path, a: int)
    requires
        no_dotdot(p),
        forall|m: int| 0 < m < p.len() ==> !links.dom().contains(#[trigger] p.subrange(0, m)),
        0 <= a <= p.len(),
    ensures
        safe_walk(links, p.subrange(0, a), p.subrange(a, p.len() as int)),
    decreases p.len() - a,
{
    if a < p.len() {
        let rest = p.subrange(a, p.len() as int);
        let n = p.subrange(0, a).push(rest[0]);
        assert(rest[0] == p[a]);
        assert(n =~= p.subrange(0, a + 1));
        assert(rest.subrange(1, rest.len() as int) =~= p.subrange(a + 1, p.len() as int));
        lemma_walk_item(links, p, a + 1);
    }
}

proof fn lemma_path_safe(items: Seq<Item>, ord: Seq<usize>, inv: Seq<usize>, k: int)
    requires
        sorted_perm(items, ord, inv),
        adj_ok(items, ord),
        0 <= k < items.len(),
        no_dotdot(pv(items[k].path@)),
    ensures
        safe_walk(links_of(sitems(items)), Seq::empty(), pv(items[k].path@)),
{
    let links = links_of(sitems(items));
    let p = pv(items[k].path@);
    assert forall|m: int| 0 < m < p.len() implies !links.dom().contains(#[trigger] p.subrange(0, m)) by {
        lemma_no_link_prefix(items, ord, inv, k, m);
    }
    lemma_walk_item(links, p, 0);
    assert(p.subrange(0, 0) =~= Seq::<Seq<u8>>::empty());
    assert(p.subrange(0, p.len() as int) =~= p);
}

proof fn lemma_walk_blocked(links: Map<Path, Path>, p: Path, a: int, m: int)
    requires
        no_dotdot(p),
        0 <= a < m < p.len(),
        links.dom().contains(p.subrange(0, m)),
    ensures
        !safe_walk(links, p.subrange(0, a), p.subrange(a, p.len() as int)),
    decreases m - a,
{
    let rest = p.subrange(a, p.len() as int);
    let n = p.subrange(0, a).push(rest[0]);
    assert(rest[0] == p[a]);
    assert(n =~= p.subrange(0, a + 1));
    assert(rest.subrange(1, rest.len() as int) =~= p.subrange(a + 1, p.len() as int));
    if a + 1 < m {
        lemma_walk_blocked(links, p, a + 1, m);
    }
}

fn check_adjacent(items: &Vec<Item>, ord: &Vec<usize>, Ghost(inv): Ghost<Seq<usize>>) -> (r: Option<usize>)
    requires
        sorted_perm(items@, ord@, inv),
    ensures
        r is None ==> adj_ok(items@, ord@),
        r is Some ==> !plan_safe(sitems(items@)),
{
    let n = items.len();
    let mut k: usize = 1;
    while k < n
        invariant
            1 <= k,
            n == items@.len(),
            sorted_perm(items@, ord@, inv),
            forall|m: int|
                0 <= m < k - 1 ==> !(items@[ord@[m] as int].kind is Symlink && is_prefix(
                    #[trigger] pp(items@, ord@)[m],
                    pp(items@, ord@)[m + 1],
                )),
        decreases n - k,
    {
        let a = &items[ord[k - 1]];
        let c = &items[ord[k]];
        if is_symlink(a.kind) && is_prefix_exec(&a.path, &c.path) {
            proof {
                let x = ord@[k - 1] as int;
                let y = ord@[k as int] as int;
                let si = sitems(items@);
                let ps = pp(items@, ord@);
                assert(ps[k - 1] == pv(a.path@) && ps[k as int] == pv(c.path@));
                assert(plt(ps[k - 1], ps[k as int]));
                let p = pv(c.path@);
                let q = pv(a.path@);
                if q.len() == p.len() {
                    assert(q =~= p);
                    lemma_plt_irrefl(q, 0);
                }
                lemma_sitems_distinct(items@, ord@, inv);
                lemma_links_has(si, si.len() as int, x);
                assert(si[x].path == q);
                assert(si[y].path == p);
                assert(p.subrange(0, q.len() as int) =~= q);
                if q.len() == 0 {
                    assert(!item_safe(si, x));
                } else if no_dotdot(p) {
                    lemma_walk_blocked(links_of(si), p, 0, q.len() as int);
                    assert(p.subrange(0, 0) =~= Seq::<Seq<u8>>::empty());
                    assert(p.subrange(0, p.len() as int) =~= p);
                    assert(!item_safe(si, y));
                } else {
                    assert(!item_safe(si, y));
                }
            }
            return Some(c.entry);
        }
        proof {
            assert(pp(items@, ord@)[k - 1] == pv(a.path@));
            assert(pp(items@, ord@)[k as int] == pv(c.path@));
        }
        k += 1;
    }
    None
}

// ---------------------------------------------------------------------
// Symbolic link targets.
// ---------------------------------------------------------------------
fn check_target(items: &Vec<Item>, ord: &Vec<usize>, Ghost(inv): Ghost<Seq<usize>>, i: usize) -> (r: bool)
    requires
        sorted_perm(items@, ord@, inv),
        i < items@.len(),
        items@[i as int].path@.len() > 0,
    ensures
        r == safe_walk(
            links_of(sitems(items@)),
            pv(items@[i as int].path@).drop_last(),
            pv(items@[i as int].target@),
        ),
{
    let it = &items[i];
    let ghost si = sitems(items@);
    let ghost links = links_of(si);
    let ghost parent = pv(it.path@).drop_last();
    let ghost target = pv(it.target@);
    proof {
        lemma_sitems_distinct(items@, ord@, inv);
    }
    let pl = it.path.len();
    let mut cur: Vec<Vec<u8>> = Vec::new();
    let mut k: usize = 0;
    while k < pl - 1
        invariant
            k <= pl - 1,
            pl == it.path@.len(),
            pv(cur@) == pv(it.path@).subrange(0, k as int),
        decreases pl - k,
    {
        let c = dup(&it.path[k]);
        proof {
            assert(pv(cur@.push(c)) =~= pv(cur@).push(c@));
            assert(pv(it.path@).subrange(0, k + 1) =~= pv(it.path@).subrange(0, k as int).push(pv(it.path@)[k as int]));
        }
        cur.push(c);
        k += 1;
    }
    proof {
        assert(pv(cur@) =~= parent);
        assert(target.subrange(0, target.len() as int) =~= target);
    }
    let tl = it.target.len();
    let mut t: usize = 0;
    while t < tl
        invariant
            t <= tl,
            tl == it.target@.len(),
            *it == items@[i as int],
            parent == pv(it.path@).drop_last(),
            target == pv(it.target@),
            si == sitems(items@),
            links == links_of(si),
            sorted_perm(items@, ord@, inv),
            distinct_paths(si),
            safe_walk(links, pv(cur@), target.subrange(t as int, tl as int)) == safe_walk(links, parent, target),
        decreases tl - t,
    {
        let c = &it.target[t];
        let ghost rest = target.subrange(t as int, tl as int);
        let ghost cur0 = pv(cur@);
        proof {
            assert(rest[0] == c@);
            assert(rest.subrange(1, rest.len() as int) =~= target.subrange(t + 1, tl as int));
        }
        if is_dotdot_exec(c) {
            if cur.len() == 0 {
                return false;
            }
            cur.pop();
            proof {
                assert(pv(cur@) =~= cur0.drop_last());
            }
        } else {
            cur.push(dup(c));
            proof {
                assert(pv(cur@) =~= cur0.push(c@));
            }
            let ghost np = pv(cur@);
            match find(items, ord, &cur, Ghost(inv)) {
                Some(j) => {
                    if is_symlink(items[j].kind) {
                        proof {
                            assert(si[j as int].kind is Symlink && si[j as int].path == np);
                            lemma_links_has(si, si.len() as int, j as int);
                            assert(links.dom().contains(np));
                            assert(np == cur0.push(rest[0]));
                            assert(safe_walk(links, cur0, rest) == (t + 1 == tl));
                        }
                        return t + 1 == tl;
                    }
                    proof {
                        if links.dom().contains(np) {
                            lemma_links_dom(si, si.len() as int, np);
                            let j2 = choose|j2: int|
                                0 <= j2 < si.len() && (#[trigger] si[j2]).kind is Symlink && si[j2].path == np;
                            assert(si[j as int].path == np);
                            assert(j2 != j);
                            assert(false);
                        }
                    }
                },
                None => {
                    proof {
                        if links.dom().contains(np) {
                            lemma_links_dom(si, si.len() as int, np);
                            let j2 = choose|j2: int|
                                0 <= j2 < si.len() && (#[trigger] si[j2]).kind is Symlink && si[j2].path == np;
                            assert(pv(items@[j2].path@) == np);
                            assert(false);
                        }
                    }
                },
            }
        }
        t += 1;
    }
    proof {
        assert(target.subrange(tl as int, tl as int) =~= Seq::<Seq<u8>>::empty());
    }
    true
}

// ---------------------------------------------------------------------
// The planner.
// ---------------------------------------------------------------------
/// The policy's conditions on item `k` as a link.
pub open spec fn link_safe(items: Seq<SItem>, k: int) -> bool {
    let it = items[k];
    &&& it.kind is Symlink ==> safe_walk(links_of(items), it.path.drop_last(), it.target)
    &&& it.kind is Hardlink ==> exists|j: int| 0 <= j < k && (#[trigger] items[j]).kind is File && items[j].path == it.target
}

proof fn lemma_only_plan(b: Seq<u8>, es: Seq<SEntry>, si: Seq<SItem>)
    requires
        plan_of(b, es, si),
        !plan_safe(si),
    ensures
        forall|p: Seq<SItem>| #[trigger] plan_of(b, es, p) ==> !plan_safe(p),
{
    assert forall|p: Seq<SItem>| #[trigger] plan_of(b, es, p) implies !plan_safe(p) by {
        lemma_plan_unique(b, es, p, si);
    }
}

/// **Plans the extraction of an archive.** `es` are the members of the
/// archive `b` (from `parse_zip` or `parse_tar`).
///
/// A returned plan is the archive's plan (`plan_of`: its steps are the
/// archive's members, in order, without those of kind `Other`) and
/// satisfies the extraction policy `plan_safe`, so `theorem_contained`
/// applies to it. A refusal means the archive has no plan that satisfies
/// the policy, unless it is `Why::Internal` (the unverified sort misbehaved,
/// see TRUST.md). So the planner accepts every archive whose plan is safe.
pub fn plan(b: &[u8], es: &Vec<Entry>) -> (r: Result<Vec<Item>, Rejected>)
    requires
        in_bounds(views(es@), b@.len() as int),
        b@.len() < MAX_ARCHIVE,
    ensures
        r matches Ok(items) ==> plan_safe(sitems(items@)) && plan_of(b@, views(es@), sitems(items@)) && items_match(
            b@,
            views(es@),
            items@,
        ),
        r matches Err(e) ==> e.why is Internal || forall|p: Seq<SItem>|
            #[trigger] plan_of(b@, views(es@), p) ==> !plan_safe(p),
{
    let items = match build_items(b, es) {
        Ok(items) => items,
        Err(e) => {
            proof {
                assert forall|p: Seq<SItem>| #[trigger] plan_of(b@, views(es@), p) implies !plan_safe(p) by {
                    lemma_refused_no_plan(b@, views(es@), e.entry as int, p);
                }
            }
            return Err(e);
        },
    };
    let ghost si = sitems(items@);
    let ghost bv = b@;
    let ghost ev = views(es@);
    let ord = order_by_path(&items);
    let inv = match check_sorted(&items, &ord) {
        Sorted::Yes(inv) => inv,
        Sorted::Dup(e) => {
            proof {
                lemma_only_plan(bv, ev, si);
            }
            return Err(Rejected { entry: e, why: Why::Duplicate });
        },
        Sorted::No => return Err(Rejected { entry: 0, why: Why::Internal }),
    };
    let ghost inv = inv@;
    match check_adjacent(&items, &ord, Ghost(inv)) {
        Some(e) => {
            proof {
                lemma_only_plan(bv, ev, si);
            }
            return Err(Rejected { entry: e, why: Why::ThroughSymlink });
        },
        None => {},
    }
    let ghost links = links_of(si);
    proof {
        lemma_sitems_distinct(items@, ord@, inv);
    }
    let n = items.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == items@.len(),
            si == sitems(items@),
            links == links_of(si),
            sorted_perm(items@, ord@, inv),
            items_match(b@, views(es@), items@),
            plan_of(bv, ev, si),
            bv == b@,
            ev == views(es@),
            distinct_paths(si),
            forall|k: int| 0 <= k < i ==> #[trigger] link_safe(si, k),
        decreases n - i,
    {
        let it = &items[i];
        proof {
            assert(item_of(b@, views(es@)[it.entry as int], it.sv()));
            assert(si[i as int] == it.sv());
        }
        if is_symlink(it.kind) {
            if !check_target(&items, &ord, Ghost(inv), i) {
                proof {
                    assert(!item_safe(si, i as int));
                    lemma_only_plan(bv, ev, si);
                }
                return Err(Rejected { entry: it.entry, why: Why::SymlinkTarget });
            }
            proof {
                assert(link_safe(si, i as int));
            }
        } else if is_hardlink(it.kind) {
            match find(&items, &ord, &it.target, Ghost(inv)) {
                Some(j) => {
                    if j >= i || !is_file(items[j].kind) {
                        proof {
                            assert(si[j as int].path == si[i as int].target);
                            assert forall|j2: int| 0 <= j2 < i && (#[trigger] si[j2]).kind is File implies si[j2].path
                                != si[i as int].target by {
                                if j2 < j {
                                    assert(si[j2].path != si[j as int].path);
                                } else if j2 > j {
                                    assert(si[j as int].path != si[j2].path);
                                }
                            }
                            assert(!item_safe(si, i as int));
                            lemma_only_plan(bv, ev, si);
                        }
                        return Err(Rejected { entry: it.entry, why: Why::HardlinkTarget });
                    }
                    proof {
                        assert(si[j as int].kind is File && si[j as int].path == si[i as int].target);
                        assert(link_safe(si, i as int));
                    }
                },
                None => {
                    proof {
                        assert forall|j2: int| 0 <= j2 < i && (#[trigger] si[j2]).kind is File implies si[j2].path
                            != si[i as int].target by {
                            assert(si[j2].path == pv(items@[j2].path@));
                        }
                        assert(!item_safe(si, i as int));
                        lemma_only_plan(bv, ev, si);
                    }
                    return Err(Rejected { entry: it.entry, why: Why::HardlinkTarget });
                },
            }
        }
        i += 1;
    }
    proof {
        assert forall|k: int| 0 <= k < si.len() implies #[trigger] item_safe(si, k) by {
            assert(item_of(b@, views(es@)[items@[k].entry as int], items@[k].sv()));
            lemma_path_safe(items@, ord@, inv, k);
            assert(link_safe(si, k));
        }
    }
    Ok(items)
}

} // verus!

impl core::fmt::Display for Why {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Why::Path => "the path is empty, absolute, has a `..` component, a NUL or a backslash",
            Why::Duplicate => "two members have the same path",
            Why::ThroughSymlink => "the path passes through a symbolic link of the archive",
            Why::SymlinkTarget => "the symbolic link points outside the root or through another link",
            Why::HardlinkTarget => "the hard link does not point to an earlier regular file",
            Why::Internal => "internal error",
        })
    }
}

impl std::error::Error for Why {}

impl core::fmt::Display for Rejected {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "member {} refused: {}", self.entry, self.why)
    }
}

impl std::error::Error for Rejected {}
