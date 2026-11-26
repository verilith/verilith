//! The trusted specification, part 2: what it means to extract safely.
//!
//! Three things are defined here, and they are what a reader of the safety
//! theorems has to believe:
//!
//! 1. `comps_from`: how a member name becomes a path (split at `/`, drop
//!    empty and `.` components).
//! 2. `resolve`: a model of how the operating system walks a path, following
//!    symbolic links, relative to the extraction root. It answers `Escaped`
//!    when the walk leaves the root.
//! 3. `plan_safe`: the conditions the planner checks.
//!
//! The theorems in `plan.rs` say: a plan the planner returns satisfies
//! `plan_safe`, and under `plan_safe` no path the extractor uses, and no
//! symbolic link it creates, resolves to `Escaped`, whatever subset of the
//! plan's links exists at the time.
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// A path: its components, outermost first.
pub type Path = Seq<Seq<u8>>;

pub open spec fn is_dot(c: Seq<u8>) -> bool {
    c.len() == 1 && c[0] == 0x2e
}

pub open spec fn is_dotdot(c: Seq<u8>) -> bool {
    c.len() == 2 && c[0] == 0x2e && c[1] == 0x2e
}

/// The components of the `/`-separated string `s` from byte `i` on. Empty
/// components (`a//b`, a trailing `/`) and `.` are dropped, as the
/// operating system ignores them; `..` is kept.
pub open spec fn comps_from(s: Seq<u8>, i: int) -> Path
    decreases s.len() - i + 1,
{
    if i < 0 || i >= s.len() {
        Seq::empty()
    } else {
        let k = find_byte(s, i, s.len() as int, 0x2f);
        let c = s.subrange(i, k);
        if k < i || k > s.len() {
            Seq::empty()
        } else if c.len() == 0 || is_dot(c) {
            comps_from(s, k + 1)
        } else {
            seq![c] + comps_from(s, k + 1)
        }
    }
}

/// No NUL (which would end the name early in a C API) and no backslash
/// (a separator on Windows).
pub open spec fn clean_bytes(s: Seq<u8>) -> bool {
    forall|k: int| 0 <= k < s.len() ==> s[k] != 0 && s[k] != 0x5c
}

pub open spec fn no_dotdot(p: Path) -> bool {
    forall|k: int| 0 <= k < p.len() ==> !is_dotdot(#[trigger] p[k])
}

/// A member name the planner accepts: relative, clean, naming something,
/// and with no `..` component.
pub open spec fn name_ok(s: Seq<u8>) -> bool {
    s.len() > 0 && s[0] != 0x2f && clean_bytes(s) && comps_from(s, 0).len() > 0 && no_dotdot(comps_from(s, 0))
}

/// The longest symbolic link target accepted, in bytes: Linux's and
/// macOS's `PATH_MAX`, past which `symlink` fails anyway.
pub const MAX_LINK: usize = 4096;

/// A symbolic link target the planner accepts: relative, clean and at most
/// `MAX_LINK` bytes. It may contain `..`; where it leads is checked by
/// `safe_walk`.
pub open spec fn target_ok(s: Seq<u8>) -> bool {
    s.len() > 0 && s[0] != 0x2f && clean_bytes(s) && s.len() <= MAX_LINK
}

/// One step of an extraction plan. `path` is relative to the extraction
/// root. `target` is a symbolic link's target, relative to the link's
/// directory, or a hard link's target, relative to the root.
pub ghost struct SItem {
    pub path: Path,
    pub kind: Kind,
    pub target: Path,
}

/// The symbolic links that the first `n` items create: where each is, and
/// its target.
pub open spec fn links_upto(items: Seq<SItem>, n: int) -> Map<Path, Path>
    decreases n,
{
    if n <= 0 {
        Map::empty()
    } else {
        let m = links_upto(items, n - 1);
        if items[n - 1].kind is Symlink {
            m.insert(items[n - 1].path, items[n - 1].target)
        } else {
            m
        }
    }
}

pub open spec fn links_of(items: Seq<SItem>) -> Map<Path, Path> {
    links_upto(items, items.len() as int)
}

// ---------------------------------------------------------------------
// The model of the operating system.
// ---------------------------------------------------------------------
pub ghost enum Res {
    /// The walk ended at this path, relative to the extraction root.
    At(Path),
    /// The walk left the extraction root.
    Escaped,
    /// Too many symbolic links were followed (the system's ELOOP).
    Loop,
}

/// **How the system resolves a path.** The walk stands in directory `cur`
/// (relative to the extraction root) with the components `rest` still to
/// go. `links` are the symbolic links that exist under the root. A `..`
/// goes to the parent, and leaves the root if `cur` is the root. A
/// component that is a symbolic link is replaced by the link's target,
/// *including when it is the last component* (as `open` without
/// `O_NOFOLLOW` does). `fuel` bounds the number of links followed.
///
/// Every link in `links` has a relative target: the planner refuses
/// absolute ones, and the theorems are about file systems whose links
/// under the root are ones the plan created.
pub open spec fn resolve(links: Map<Path, Path>, cur: Path, rest: Path, fuel: nat) -> Res
    decreases fuel, rest.len(),
{
    if rest.len() == 0 {
        Res::At(cur)
    } else {
        let c = rest[0];
        let r = rest.subrange(1, rest.len() as int);
        if is_dotdot(c) {
            if cur.len() == 0 {
                Res::Escaped
            } else {
                resolve(links, cur.drop_last(), r, fuel)
            }
        } else {
            let n = cur.push(c);
            if links.dom().contains(n) {
                if fuel == 0 {
                    Res::Loop
                } else {
                    resolve(links, cur, links[n] + r, (fuel - 1) as nat)
                }
            } else {
                resolve(links, n, r, fuel)
            }
        }
    }
}

// ---------------------------------------------------------------------
// What the planner checks.
// ---------------------------------------------------------------------
/// Walking `rest` from `cur` never climbs out of the root, and passes
/// *through* no symbolic link: only its last component may be one.
pub open spec fn safe_walk(links: Map<Path, Path>, cur: Path, rest: Path) -> bool
    decreases rest.len(),
{
    if rest.len() == 0 {
        true
    } else {
        let c = rest[0];
        let r = rest.subrange(1, rest.len() as int);
        if is_dotdot(c) {
            cur.len() > 0 && safe_walk(links, cur.drop_last(), r)
        } else {
            let n = cur.push(c);
            if links.dom().contains(n) {
                r.len() == 0
            } else {
                safe_walk(links, n, r)
            }
        }
    }
}

/// **The extraction policy.**
///
/// - No two items have the same path.
/// - Every path is non-empty, has no `..`, and passes through no symbolic
///   link of the plan.
/// - Every symbolic link's target, walked from the link's directory, stays
///   under the root and passes through no symbolic link of the plan.
/// - Every hard link's target is the path of a regular file that an
///   earlier item of the same plan creates.
pub open spec fn plan_safe(items: Seq<SItem>) -> bool {
    &&& distinct_paths(items)
    &&& forall|i: int| 0 <= i < items.len() ==> #[trigger] item_safe(items, i)
}

pub open spec fn distinct_paths(items: Seq<SItem>) -> bool {
    forall|i: int, j: int| 0 <= i < j < items.len() ==> (#[trigger] items[i]).path != (#[trigger] items[j]).path
}

/// The policy's conditions on item `i`.
pub open spec fn item_safe(items: Seq<SItem>, i: int) -> bool {
    let links = links_of(items);
    let it = items[i];
    &&& it.path.len() > 0
    &&& no_dotdot(it.path)
    &&& safe_walk(links, Seq::empty(), it.path)
    &&& it.kind is Symlink ==> safe_walk(links, it.path.drop_last(), it.target)
    &&& it.kind is Hardlink ==> exists|j: int| 0 <= j < i && (#[trigger] items[j]).kind is File && items[j].path == it.target
}

/// The text of a symbolic link's target: tar keeps it in the header, zip in
/// the member's data.
pub open spec fn link_text(b: Seq<u8>, e: SEntry) -> Option<Seq<u8>> {
    if e.link.len() > 0 {
        Some(e.link)
    } else {
        entry_data(b, e)
    }
}

/// The plan item `it` is what the policy makes of the archive member `e`.
pub open spec fn item_of(b: Seq<u8>, e: SEntry, it: SItem) -> bool {
    &&& name_ok(e.name)
    &&& it.path == comps_from(e.name, 0)
    &&& it.kind == e.kind
    &&& e.kind is Symlink ==> match link_text(b, e) {
        Some(t) => target_ok(t) && it.target == comps_from(t, 0),
        None => false,
    }
    &&& e.kind is Hardlink ==> name_ok(e.link) && it.target == comps_from(e.link, 0)
    &&& !(e.kind is Symlink) && !(e.kind is Hardlink) ==> it.target.len() == 0
}

/// The members a plan extracts: all but those of kind `Other`, in order.
pub open spec fn kept(es: Seq<SEntry>) -> Seq<SEntry>
    decreases es.len(),
{
    if es.len() == 0 {
        Seq::empty()
    } else if es.last().kind is Other {
        kept(es.drop_last())
    } else {
        kept(es.drop_last()).push(es.last())
    }
}

/// **The plan of an archive.** `items` has one step for each member that
/// is not of kind `Other`, in member order, and each is what the policy
/// makes of its member. An archive has at most one plan (`item_of`
/// determines the item), and none if a member's name or target is refused.
///
/// The planner is proven to return the plan when there is one and it
/// satisfies `plan_safe`, and to refuse the archive otherwise.
pub open spec fn plan_of(b: Seq<u8>, es: Seq<SEntry>, items: Seq<SItem>) -> bool {
    &&& items.len() == kept(es).len()
    &&& forall|k: int| 0 <= k < items.len() ==> #[trigger] item_of(b, kept(es)[k], items[k])
}

} // verus!
