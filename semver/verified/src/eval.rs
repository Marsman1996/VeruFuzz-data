//! Mirror of `code/src/eval.rs`.
//!
//! Machine-level transcription of the VersionReq/Comparator matching evaluator:
//! - Prerelease Ord comparisons such as `ver.pre > cmp.pre` -> `impls::pre_gt/pre_ge/
//!   pre_eq/pre_lt` (contract anchored on pre_cmp_spec_top);
//! - matches_req's pre gate ("in order for *any* VersionReq to match a
//!   pre-release version, the VersionReq must contain at least one Comparator
//!   that has an explicit major, minor, and patch version identical to the
//!   pre-release being matched, and that has a nonempty pre-release
//!   component" -- the lib.rs VersionReq::STAR doc) enters the contract verbatim;
//! - the spec side is a branch-locking mirror (flat field parameters, so
//!   no struct value is passed in a spec); UT/doc-level semantics are carried
//!   by the harness example theorems (the Op doc equivalence chains).

use vstd::prelude::*;
use vstd::seq::Seq;

use super::impls::{pre_cmp_spec_top, pre_gt, Ord2};
use super::{Comparator, Op, Version, VersionReq};

verus! {

/* ======================================================================
 * spec mirror (branch-locking layer, flat parameters)
 * ====================================================================== */

pub open spec fn pre_is_compatible_spec(
    c_major: u64,
    c_minor: Option<u64>,
    c_patch: Option<u64>,
    c_pre: Seq<u8>,
    vmaj: u64,
    vmin: u64,
    vpat: u64,
) -> bool {
    c_major == vmaj && c_minor == Option::Some(vmin) && c_patch == Option::Some(vpat)
        && c_pre.len() > 0
}

/// eval.rs:42-60 matches_exact (the conjunctive mirror of the early-return chain).
pub open spec fn matches_exact_spec(
    c_major: u64,
    c_minor: Option<u64>,
    c_patch: Option<u64>,
    c_pre: Seq<u8>,
    vmaj: u64,
    vmin: u64,
    vpat: u64,
    vpre: Seq<u8>,
) -> bool {
    vmaj == c_major
        && (c_minor.is_Some() ==> vmin == c_minor.unwrap())
        && (c_patch.is_Some() ==> vpat == c_patch.unwrap())
        && pre_cmp_spec_top(vpre, c_pre) == Ord2::Equal
}

/// eval.rs:62-86 matches_greater.
pub open spec fn matches_greater_spec(
    c_major: u64,
    c_minor: Option<u64>,
    c_patch: Option<u64>,
    c_pre: Seq<u8>,
    vmaj: u64,
    vmin: u64,
    vpat: u64,
    vpre: Seq<u8>,
) -> bool {
    if vmaj != c_major {
        vmaj > c_major
    } else if c_minor.is_None() {
        false
    } else if vmin != c_minor.unwrap() {
        vmin > c_minor.unwrap()
    } else if c_patch.is_None() {
        false
    } else if vpat != c_patch.unwrap() {
        vpat > c_patch.unwrap()
    } else {
        pre_cmp_spec_top(vpre, c_pre) == Ord2::Greater
    }
}

/// eval.rs:88-112 matches_less.
pub open spec fn matches_less_spec(
    c_major: u64,
    c_minor: Option<u64>,
    c_patch: Option<u64>,
    c_pre: Seq<u8>,
    vmaj: u64,
    vmin: u64,
    vpat: u64,
    vpre: Seq<u8>,
) -> bool {
    if vmaj != c_major {
        vmaj < c_major
    } else if c_minor.is_None() {
        false
    } else if vmin != c_minor.unwrap() {
        vmin < c_minor.unwrap()
    } else if c_patch.is_None() {
        false
    } else if vpat != c_patch.unwrap() {
        vpat < c_patch.unwrap()
    } else {
        pre_cmp_spec_top(vpre, c_pre) == Ord2::Less
    }
}

/// eval.rs:114-132 matches_tilde.
pub open spec fn matches_tilde_spec(
    c_major: u64,
    c_minor: Option<u64>,
    c_patch: Option<u64>,
    c_pre: Seq<u8>,
    vmaj: u64,
    vmin: u64,
    vpat: u64,
    vpre: Seq<u8>,
) -> bool {
    vmaj == c_major
        && (c_minor.is_Some() ==> vmin == c_minor.unwrap())
        && (if c_patch.is_Some() && vpat != c_patch.unwrap() {
            vpat > c_patch.unwrap()
        } else {
            pre_cmp_spec_top(vpre, c_pre) != Ord2::Less
        })
}

/// eval.rs:134-168 matches_caret (the code face of the doc Op::Caret equivalence chains).
pub open spec fn matches_caret_spec(
    c_major: u64,
    c_minor: Option<u64>,
    c_patch: Option<u64>,
    c_pre: Seq<u8>,
    vmaj: u64,
    vmin: u64,
    vpat: u64,
    vpre: Seq<u8>,
) -> bool {
    if vmaj != c_major {
        false
    } else if c_minor.is_None() {
        true
    } else if c_patch.is_None() {
        if c_major > 0 {
            vmin >= c_minor.unwrap()
        } else {
            vmin == c_minor.unwrap()
        }
    } else if c_major > 0 {
        if vmin != c_minor.unwrap() {
            vmin > c_minor.unwrap()
        } else if vpat != c_patch.unwrap() {
            vpat > c_patch.unwrap()
        } else {
            pre_cmp_spec_top(vpre, c_pre) != Ord2::Less
        }
    } else if c_minor.unwrap() > 0 {
        if vmin != c_minor.unwrap() {
            false
        } else if vpat != c_patch.unwrap() {
            vpat > c_patch.unwrap()
        } else {
            pre_cmp_spec_top(vpre, c_pre) != Ord2::Less
        }
    } else if vmin != c_minor.unwrap() || vpat != c_patch.unwrap() {
        false
    } else {
        pre_cmp_spec_top(vpre, c_pre) != Ord2::Less
    }
}

/// eval.rs:30-40 matches_impl (Op dispatch; Wildcard same as Exact -- the upstream match).
pub open spec fn matches_impl_spec(
    op: Op,
    c_major: u64,
    c_minor: Option<u64>,
    c_patch: Option<u64>,
    c_pre: Seq<u8>,
    vmaj: u64,
    vmin: u64,
    vpat: u64,
    vpre: Seq<u8>,
) -> bool {
    if op == Op::Exact || op == Op::Wildcard {
        matches_exact_spec(c_major, c_minor, c_patch, c_pre, vmaj, vmin, vpat, vpre)
    } else if op == Op::Greater {
        matches_greater_spec(c_major, c_minor, c_patch, c_pre, vmaj, vmin, vpat, vpre)
    } else if op == Op::GreaterEq {
        matches_exact_spec(c_major, c_minor, c_patch, c_pre, vmaj, vmin, vpat, vpre)
            || matches_greater_spec(c_major, c_minor, c_patch, c_pre, vmaj, vmin, vpat, vpre)
    } else if op == Op::Less {
        matches_less_spec(c_major, c_minor, c_patch, c_pre, vmaj, vmin, vpat, vpre)
    } else if op == Op::LessEq {
        matches_exact_spec(c_major, c_minor, c_patch, c_pre, vmaj, vmin, vpat, vpre)
            || matches_less_spec(c_major, c_minor, c_patch, c_pre, vmaj, vmin, vpat, vpre)
    } else if op == Op::Tilde {
        matches_tilde_spec(c_major, c_minor, c_patch, c_pre, vmaj, vmin, vpat, vpre)
    } else {
        matches_caret_spec(c_major, c_minor, c_patch, c_pre, vmaj, vmin, vpat, vpre)
    }
}

/// eval.rs:3-24 matches_req (including the pre gate of the VersionReq::STAR doc).
/// matches_req's conjunction over all comparators (carried by its own trigger).
pub open spec fn matches_all_spec(
    comps: Seq<Comparator>,
    vmaj: u64,
    vmin: u64,
    vpat: u64,
    vpre: Seq<u8>,
) -> bool {
    forall|i: int|
        0 <= i < comps.len() ==>
            #[trigger]
        matches_impl_spec(
            comps[i].op,
            comps[i].major,
            comps[i].minor,
            comps[i].patch,
            comps[i].pre.bytes@,
            vmaj,
            vmin,
            vpat,
            vpre,
        )
}

/// eval.rs:3-24 matches_req (including the pre gate of the VersionReq::STAR doc).
pub open spec fn matches_req_spec(
    comps: Seq<Comparator>,
    vmaj: u64,
    vmin: u64,
    vpat: u64,
    vpre: Seq<u8>,
) -> bool {
    matches_all_spec(comps, vmaj, vmin, vpat, vpre)
        && (vpre.len() == 0
            || exists|i: int|
                0 <= i < comps.len()
                    && pre_is_compatible_spec(
                        comps[i].major,
                        comps[i].minor,
                        comps[i].patch,
                        comps[i].pre.bytes@,
                        vmaj,
                        vmin,
                        vpat,
                    ))
}

/// eval.rs:26-28 matches_comparator.
pub open spec fn matches_comparator_spec(
    op: Op,
    c_major: u64,
    c_minor: Option<u64>,
    c_patch: Option<u64>,
    c_pre: Seq<u8>,
    vmaj: u64,
    vmin: u64,
    vpat: u64,
    vpre: Seq<u8>,
) -> bool {
    matches_impl_spec(op, c_major, c_minor, c_patch, c_pre, vmaj, vmin, vpat, vpre)
        && (vpre.len() == 0
            || pre_is_compatible_spec(c_major, c_minor, c_patch, c_pre, vmaj, vmin, vpat))
}

/* ======================================================================
 * exec machine-level transcription
 * ====================================================================== */

/// Origin Rust: pub(crate) fn matches_req(req: &VersionReq, ver: &Version) -> bool
pub(crate) fn matches_req(req: &VersionReq, ver: &Version) -> (r: bool)
    ensures
        r == matches_req_spec(req.comparators@, ver.major, ver.minor, ver.patch, ver.pre.bytes@),
{
    let vmaj = ver.major;
    let vmin = ver.minor;
    let vpat = ver.patch;
    let comps = &req.comparators;
    let mut i: usize = 0;
    while i < comps.len()
        invariant
            i <= comps.len(),
            forall|k: int|
                0 <= k < i as int
                    ==> matches_impl_spec(
                        comps@[k].op,
                        comps@[k].major,
                        comps@[k].minor,
                        comps@[k].patch,
                        comps@[k].pre.bytes@,
                        vmaj,
                        vmin,
                        vpat,
                        ver.pre.bytes@,
                    ),
        decreases
            comps.len() - i,
    {
        if !matches_impl(&comps[i], ver) {
            proof {
                let c = comps@[i as int];
                assert(!matches_impl_spec(
                    c.op,
                    c.major,
                    c.minor,
                    c.patch,
                    c.pre.bytes@,
                    vmaj,
                    vmin,
                    vpat,
                    ver.pre.bytes@,
                ));
                assert(!matches_all_spec(comps@, vmaj, vmin, vpat, ver.pre.bytes@));
                assert(matches_req_spec(comps@, vmaj, vmin, vpat, ver.pre.bytes@) == false);
            }
            return false;
        }
        i += 1;
    }

    /* Origin Rust: if ver.pre.is_empty() { return true; } */
    if ver.pre.bytes.len() == 0 {
        proof {
            assert(matches_all_spec(comps@, vmaj, vmin, vpat, ver.pre.bytes@));
            assert(matches_req_spec(comps@, vmaj, vmin, vpat, ver.pre.bytes@));
        }
        return true;
    }

    /* Origin Rust: for cmp in &req.comparators { if pre_is_compatible(cmp, ver) { return true; } } */
    let mut j: usize = 0;
    while j < comps.len()
        invariant
            j <= comps.len(),
            forall|k: int|
                0 <= k < j as int
                    ==> !pre_is_compatible_spec(
                        comps@[k].major,
                        comps@[k].minor,
                        comps@[k].patch,
                        comps@[k].pre.bytes@,
                        vmaj,
                        vmin,
                        vpat,
                    ),
        decreases
            comps.len() - j,
    {
        if pre_is_compatible(&comps[j], ver) {
            proof {
                let c = comps@[j as int];
                assert(pre_is_compatible_spec(
                    c.major,
                    c.minor,
                    c.patch,
                    c.pre.bytes@,
                    vmaj,
                    vmin,
                    vpat,
                ));
                assert(matches_req_spec(comps@, vmaj, vmin, vpat, ver.pre.bytes@));
            }
            return true;
        }
        proof {
            let c = comps@[j as int];
            assert(!pre_is_compatible_spec(
                c.major,
                c.minor,
                c.patch,
                c.pre.bytes@,
                vmaj,
                vmin,
                vpat,
            ));
        }
        j += 1;
    }
    proof {
        assert(matches_req_spec(comps@, vmaj, vmin, vpat, ver.pre.bytes@) == false);
    }
    false
}

/// Origin Rust: pub(crate) fn matches_comparator(cmp: &Comparator, ver: &Version)
pub(crate) fn matches_comparator(c: &Comparator, ver: &Version) -> (r: bool)
    ensures
        r == matches_comparator_spec(
            c.op,
            c.major,
            c.minor,
            c.patch,
            c.pre.bytes@,
            ver.major,
            ver.minor,
            ver.patch,
            ver.pre.bytes@,
        ),
{
    matches_impl(c, ver) && (ver.pre.bytes.len() == 0 || pre_is_compatible(c, ver))
}

/// Origin Rust: fn matches_impl(cmp: &Comparator, ver: &Version) -> bool (eval.rs:30-40)
fn matches_impl(c: &Comparator, ver: &Version) -> (r: bool)
    ensures
        r == matches_impl_spec(
            c.op,
            c.major,
            c.minor,
            c.patch,
            c.pre.bytes@,
            ver.major,
            ver.minor,
            ver.patch,
            ver.pre.bytes@,
        ),
{
    /* Origin Rust: match cmp.op { Op::Exact | Op::Wildcard => matches_exact(cmp, ver), ... }
     * the exec side disambiguates the enum with a match (verus's enum == does
     * not symbolically align in exec). */
    match c.op {
        Op::Exact | Op::Wildcard => matches_exact(c, ver),
        Op::Greater => matches_greater(c, ver),
        Op::GreaterEq => matches_exact(c, ver) || matches_greater(c, ver),
        Op::Less => matches_less(c, ver),
        Op::LessEq => matches_exact(c, ver) || matches_less(c, ver),
        Op::Tilde => matches_tilde(c, ver),
        Op::Caret => matches_caret(c, ver),
    }
}

/// Origin Rust: fn pre_is_compatible(cmp: &Comparator, ver: &Version) (eval.rs:170-175)
fn pre_is_compatible(c: &Comparator, ver: &Version) -> (r: bool)
    ensures
        r == pre_is_compatible_spec(
            c.major,
            c.minor,
            c.patch,
            c.pre.bytes@,
            ver.major,
            ver.minor,
            ver.patch,
        ),
{
    c.major == ver.major
        && c.minor == Option::Some(ver.minor)
        && c.patch == Option::Some(ver.patch)
        && c.pre.bytes.len() > 0
}

/// Origin Rust: fn matches_exact(cmp: &Comparator, ver: &Version) (eval.rs:42-60)
fn matches_exact(c: &Comparator, ver: &Version) -> (r: bool)
    ensures
        r == matches_exact_spec(
            c.major,
            c.minor,
            c.patch,
            c.pre.bytes@,
            ver.major,
            ver.minor,
            ver.patch,
            ver.pre.bytes@,
        ),
{
    if ver.major != c.major {
        return false;
    }
    if let Some(minor) = c.minor {
        if ver.minor != minor {
            return false;
        }
    }
    if let Some(patch) = c.patch {
        if ver.patch != patch {
            return false;
        }
    }
    super::impls::pre_eq(&ver.pre, &c.pre)
}

/// Origin Rust: fn matches_greater(cmp, ver) (eval.rs:62-86)
fn matches_greater(c: &Comparator, ver: &Version) -> (r: bool)
    ensures
        r == matches_greater_spec(
            c.major,
            c.minor,
            c.patch,
            c.pre.bytes@,
            ver.major,
            ver.minor,
            ver.patch,
            ver.pre.bytes@,
        ),
{
    if ver.major != c.major {
        return ver.major > c.major;
    }

    let minor = match c.minor {
        Some(m) => m,
        None => return false,
    };
    if ver.minor != minor {
        return ver.minor > minor;
    }

    let patch = match c.patch {
        Some(p) => p,
        None => return false,
    };
    if ver.patch != patch {
        return ver.patch > patch;
    }

    pre_gt(&ver.pre, &c.pre)
}

/// Origin Rust: fn matches_less(cmp, ver) (eval.rs:88-112)
fn matches_less(c: &Comparator, ver: &Version) -> (r: bool)
    ensures
        r == matches_less_spec(
            c.major,
            c.minor,
            c.patch,
            c.pre.bytes@,
            ver.major,
            ver.minor,
            ver.patch,
            ver.pre.bytes@,
        ),
{
    if ver.major != c.major {
        return ver.major < c.major;
    }

    let minor = match c.minor {
        Some(m) => m,
        None => return false,
    };
    if ver.minor != minor {
        return ver.minor < minor;
    }

    let patch = match c.patch {
        Some(p) => p,
        None => return false,
    };
    if ver.patch != patch {
        return ver.patch < patch;
    }

    super::impls::pre_lt(&ver.pre, &c.pre)
}

/// Origin Rust: fn matches_tilde(cmp, ver) (eval.rs:114-132)
fn matches_tilde(c: &Comparator, ver: &Version) -> (r: bool)
    ensures
        r == matches_tilde_spec(
            c.major,
            c.minor,
            c.patch,
            c.pre.bytes@,
            ver.major,
            ver.minor,
            ver.patch,
            ver.pre.bytes@,
        ),
{
    if ver.major != c.major {
        return false;
    }

    if let Some(minor) = c.minor {
        if ver.minor != minor {
            return false;
        }
    }

    if let Some(patch) = c.patch {
        if ver.patch != patch {
            return ver.patch > patch;
        }
    }

    super::impls::pre_ge(&ver.pre, &c.pre)
}

/// Origin Rust: fn matches_caret(cmp, ver) (eval.rs:134-168)
fn matches_caret(c: &Comparator, ver: &Version) -> (r: bool)
    ensures
        r == matches_caret_spec(
            c.major,
            c.minor,
            c.patch,
            c.pre.bytes@,
            ver.major,
            ver.minor,
            ver.patch,
            ver.pre.bytes@,
        ),
{
    if ver.major != c.major {
        return false;
    }

    let minor = match c.minor {
        Some(m) => m,
        None => return true,
    };

    let patch = match c.patch {
        Some(p) => p,
        None => {
            if c.major > 0 {
                return ver.minor >= minor;
            } else {
                return ver.minor == minor;
            }
        }
    };

    if c.major > 0 {
        if ver.minor != minor {
            return ver.minor > minor;
        } else if ver.patch != patch {
            return ver.patch > patch;
        }
    } else if minor > 0 {
        if ver.minor != minor {
            return false;
        } else if ver.patch != patch {
            return ver.patch > patch;
        }
    } else if ver.minor != minor || ver.patch != patch {
        return false;
    }

    super::impls::pre_ge(&ver.pre, &c.pre)
}

} // verus!
