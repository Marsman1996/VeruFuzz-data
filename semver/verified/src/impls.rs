//! Mirror of `code/src/impls.rs`.
//!
//! Carries the machine-level transcription of `Ord for Prerelease`
//! (the semver precedence algorithm of impls.rs:50-105).
//!
//! **Algorithm-shape transcription ledger (exec-code-preservation grade)**:
//! upstream compares materialized segments (iterate `split('.')` calling
//! `seg_cmp` per segment; the side with more segments is greater). Verus
//! spec-function termination does not accept unknown-index slices of the
//! form `s[first_dot(s)+1..]`,
//! so the algorithm is transcribed as an **equivalent dual-track byte-state
//! recursion**: cursors (ai, sa)/(bi, bs) = current byte position / current
//! segment start, every advance is the constant +1, and segment completion
//! (segment length, all-digit classification) is expressed with
//! non-recursive quantifier look-ahead. Case-by-case mapping onto the
//! upstream rules (the four match arms + tie-break of impls.rs:77-92):
//!
//! | this mirror's case | upstream rule source (impls.rs) |
//! |---|---|
//! | `seg_digits_all` true on both sides: segment length then bytes | :78-84 `(true,true)`: `Ord::cmp(len)` then `string_cmp` |
//! | `seg_digits_all` true on one side | :85-88 `(true,false)=>Less / (false,true)=>Greater` |
//! | both non-digit segments decided by bytes | :90-92 `(false,false) => string_cmp()` (byte-lex, short prefix smaller) |
//! | one segment ends first (res_a_ended) | digit < non-digit / shorter digit segment smaller / shorter non-digit prefix smaller |
//! | ai at the end AND bi not at the end | :68-73 lhs exhausted, `rhs.next()` has a remaining segment => Less |
//! | '..' double-dot advance | :64-67 the `rhs.next()` segment-advance semantics |
//! | top-level empty gate (empty pre = release) | :52-62 the `is_empty` gate (pre_cmp_spec_top) |
//!
//! - The `ptr_eq` fast path (:52) is implied by Equal-transitivity under the
//!   equal-value model, dropped (relax ledger 2).
//! - `core::cmp::Ordering` -> the mirror `Ord2` (relax ledger 4).
//! - `Ord for BuildMetadata` (:107-150, the trim-'0' tie-break chain) and the
//!   antisymmetry/transitivity universals of `sort_version` are blocked this
//!   round (solver shape: nested exists + the spec-recursion unknown-slice
//!   forbidden zone); the semantic surface is locked by
//!   harness examples; the blocking record is in out/bug-finder-summary.md.
//!
//! Consumption: this file has no fn main; the harness references it via
//! lib.rs -- do not duplicate its specs.

use vstd::prelude::*;
use vstd::seq::Seq;

use super::parse::digits_only;
use super::{is_digit, Prerelease, Version};

verus! {

broadcast use vstd::seq::group_seq_lemmas;

/* ======================================================================
 * Ord2 (relax ledger 4: the mirror of core::cmp::Ordering)
 * ====================================================================== */

#[derive(PartialEq, Eq, Copy, Clone)]
pub enum Ord2 {
    Less,
    Equal,
    Greater,
}

/* ======================================================================
 * Segment-level components (the machine-level face of the upstream four match arms; recursion-free)
 * ====================================================================== */

/// Mirror of Rust's `Ord for &[u8]` (byte lexicographic; the short prefix is smaller).
pub open spec fn lex_cmp(a: Seq<u8>, b: Seq<u8>) -> Ord2
    decreases
        a.len() + b.len(),
{
    if a.len() == 0 || b.len() == 0 {
        if a.len() == b.len() {
            Ord2::Equal
        } else if a.len() == 0 {
            Ord2::Less
        } else {
            Ord2::Greater
        }
    } else if a[0] != b[0] {
        if a[0] < b[0] {
            Ord2::Less
        } else {
            Ord2::Greater
        }
    } else {
        lex_cmp(a[1..], b[1..])
    }
}

/// doc (the lib.rs Prerelease Total ordering): "Identifiers consisting of only
/// digits are compared numerically." (an equal-length digit segment = lexicographic
/// = numeric order); "Any numeric identifier is always less than any
/// non-numeric identifier."
/// "Otherwise, ASCII sort order."
pub open spec fn seg_cmp_spec(sa: Seq<u8>, sb: Seq<u8>) -> Ord2 {
    let da = digits_only(sa);
    let db = digits_only(sb);
    if da && db {
        if sa.len() != sb.len() {
            if sa.len() < sb.len() {
                Ord2::Less
            } else {
                Ord2::Greater
            }
        } else {
            lex_cmp(sa, sb)
        }
    } else if da {
        Ord2::Less
    } else if db {
        Ord2::Greater
    } else {
        lex_cmp(sa, sb)
    }
}

/// The segment's right end e (the first '.' or the end; no '.' inside [from..e))
/// -- the shell of the quantifier look-ahead.
pub open spec fn seg_end_at(s: Seq<u8>, from: int, e: int) -> bool {
    (e == s.len() || (e < s.len() && s[e] == 0x2e))
        && from <= e
        && forall|j: int| from <= j < e ==> #[trigger] s[j] != 0x2e
}

/// Whether the current segment (starting at from) is all digits (the whole-
/// segment look-ahead of upstream `bytes().all(is_ascii_digit)`; true
/// for the empty segment, consistent with upstream all()).
pub open spec fn seg_digits_all(s: Seq<u8>, from: int) -> bool {
    exists|e: int|
        #![trigger seg_end_at(s, from, e)]
        seg_end_at(s, from, e) && forall|k: int| from <= k < e ==> #[trigger] is_digit(s[k])
}

/// Exec twin: scan the current segment (from `from`) to decide all-digits.
pub(crate) exec fn seg_digits_all_exec(s: &[u8], from: usize) -> (r: bool)
    requires
        from <= s.len(),
    ensures
        r == seg_digits_all(s@, from as int),
{
    let mut i: usize = from;
    let mut all = true;
    while i < s.len() && s[i] != 0x2e
        invariant
            from <= i <= s.len(),
            forall|k: int| (from as int) <= k < i as int ==> s@[k] != 0x2e,
            all == (forall|k: int| (from as int) <= k < i as int ==> is_digit(s@[k])),
        decreases
            s.len() - i,
    {
        if !is_digit_scan(s[i]) {
            all = false;
        }
        i += 1;
    }
    proof {
        let e = i as int;
        assert(seg_end_at(s@, from as int, e));
    }
    all
}

pub(crate) exec fn is_digit_scan(b: u8) -> (r: bool)
    ensures
        r == is_digit(b),
{
    b >= 0x30 && b <= 0x39
}


/// Exec twin: length of the current segment from `from` (= the machine-level
/// implementation of choose_segment_len).
pub(crate) exec fn seg_len_of(s: &[u8], from: usize) -> (r: usize)
    requires
        from <= s.len(),
    ensures
        r as int == choose_segment_len(s@, from as int),
{
    let mut i: usize = from;
    while i < s.len() && s[i] != 0x2e
        invariant
            from <= i <= s.len(),
            forall|k: int| (from as int) <= k < i as int ==> s@[k] != 0x2e,
        decreases
            s.len() - i,
    {
        i += 1;
    }
    proof {
        assert(seg_end_at(s@, from as int, i as int));
        lemma_witness_len(s@, from as int, 0, i as int);
    }
    i - from
}

/// Exec twin: length of the current segment from `from` (to the first '.' or the end).
pub(crate) exec fn seg_len_exec(s: &[u8], from: usize) -> (r: usize)
    requires
        from <= s.len(),
    ensures
        forall|j: int| (from as int) <= j < (from as int) + r as int ==> #[trigger] s@[j]
            != 0x2e,
        (from as int) + r as int == s.len()
            || s@[(from as int) + r as int] == 0x2e,
        from <= r + from,
{
    let mut i: usize = from;
    while i < s.len() && s[i] != 0x2e
        invariant
            from <= i <= s.len(),
            forall|k: int| (from as int) <= k < i as int ==> s@[k] != 0x2e,
        decreases
            s.len() - i,
    {
        i += 1;
    }
    i - from
}

/* ======================================================================
 * Dual-track byte-state recursion
 * ====================================================================== */

/// The upstream four-arm tie-break on unequal bytes (both segments unfinished; the impls.rs:77-92 mapping table).
pub open spec fn res_unequal(
    oa: Seq<u8>,
    a_off: int,
    sa: int,
    ob: Seq<u8>,
    b_off: int,
    bs: int,
) -> Ord2 {
    let qA = seg_digits_all(oa, sa);
    let qB = seg_digits_all(ob, bs);
    if qA && qB {
        // both digit segments: segment length (digit count) decides, then equal-length bytes decide
        let la = choose_segment_len(oa, sa);
        let lb = choose_segment_len(ob, bs);
        if la != lb {
            if la < lb {
                Ord2::Less
            } else {
                Ord2::Greater
            }
        } else if oa[a_off] < ob[b_off] {
            Ord2::Less
        } else {
            Ord2::Greater
        }
    } else if qA {
        Ord2::Less
    } else if qB {
        Ord2::Greater
    } else if oa[a_off] < ob[b_off] {
        Ord2::Less
    } else {
        Ord2::Greater
    }
}

/// The tie-break when one segment ends first (the ending side sits at its separator '.'; the ending side = a).
pub open spec fn res_a_ended(
    oa: Seq<u8>,
    sa: int,
    ob: Seq<u8>,
    bs: int,
) -> Ord2 {
    let qA = seg_digits_all(oa, sa);
    let qB = seg_digits_all(ob, bs);
    if qA {
        if qB {
            let la = choose_segment_len(oa, sa);
            let lb = choose_segment_len(ob, bs);
            if la != lb {
                if la < lb {
                    Ord2::Less
                } else {
                    Ord2::Greater
                }
            } else {
                Ord2::Greater
            }
        } else {
            // digit < non-digit (impls.rs:85-87)
            Ord2::Less
        }
    } else if qB {
        // non-digit > digit (impls.rs:88)
        Ord2::Greater
    } else {
        // both non-digit: the side ending first has the shorter prefix, hence smaller (Rust `Ord::cmp` prefix rule)
        Ord2::Less
    }
}

pub open spec fn choose_segment_len(s: Seq<u8>, from: int) -> int
    recommends
        0 <= from <= s.len(),
{
    segment_len_witness(s, from, 0)
}

pub open spec fn segment_len_witness(s: Seq<u8>, from: int, acc: int) -> int
    recommends
        from + acc <= s.len(),
    decreases
        s.len() - from - acc,
{
    if from + acc >= s.len() || s[from + acc] == 0x2e {
        acc
    } else {
        segment_len_witness(s, from, acc + 1)
    }
}

/// The dual-track state recursion (the case mapping table at the file head; remaining-slice + absolute-offset form).
pub open spec fn pre_cmp_st(
    oa: Seq<u8>,
    a: Seq<u8>,
    a_off: int,
    sa: int,
    ob: Seq<u8>,
    b: Seq<u8>,
    b_off: int,
    bs: int,
) -> Ord2
    decreases
        a.len() + b.len(),
{
    if a.len() == 0 {
        if b.len() == 0 {
            Ord2::Equal
        } else {
            Ord2::Less
        }
    } else if b.len() == 0 {
        Ord2::Greater
    } else {
        let ca = a[0];
        let cb = b[0];
        if ca == 0x2e && cb == 0x2e {
            pre_cmp_st(oa, a[1..], a_off + 1, a_off + 1, ob, b[1..], b_off + 1, b_off + 1)
        } else if cb == 0x2e {
            res_a_ended(ob, bs, oa, sa)
        } else if ca == 0x2e {
            res_a_ended(oa, sa, ob, bs)
        } else if ca == cb {
            pre_cmp_st(oa, a[1..], a_off + 1, sa, ob, b[1..], b_off + 1, bs)
        } else {
            res_unequal(oa, a_off, sa, ob, b_off, bs)
        }
    }
}

/// The empty-pre gate of impls.rs:52-62 (doc: "A pre-release version ... considered less
/// than the ordinary release"): an empty pre (= the ordinary release) is greater than any nonempty pre.
pub open spec fn pre_cmp_spec_top(a: Seq<u8>, b: Seq<u8>) -> Ord2 {
    if a.len() == 0 {
        if b.len() == 0 {
            Ord2::Equal
        } else {
            Ord2::Greater
        }
    } else if b.len() == 0 {
        Ord2::Less
    } else {
        pre_cmp_st(a, a, 0, 0, b, b, 0, 0)
    }
}

/* ======================================================================
 * Machine-level exec transcription (case-aligned with the state spec; Origins at each branch)
 * ====================================================================== */

/// Origin Rust: impls.rs:50-104 `impl Ord for Prerelease::cmp`
/// (transcribed into the state-recursion shape; the mapping table is at the
/// file head). The comparison of (a, b) = pre_cmp_st.
pub fn pre_cmp(x: &Prerelease, y: &Prerelease) -> (r: Ord2)
    ensures
        r == pre_cmp_spec_top(x.bytes@, y.bytes@),
{
    /* Origin Rust: if self.identifier.ptr_eq(&rhs.identifier) { return Ordering::Equal; }
     * -- the ptr_eq equal-value fast path: implied by the Equal theorem under the
     * equal-value model, no separate arm needed (ledger). */
    /* Origin Rust: match self.is_empty() { true => return Ordering::Greater, ... } */
    if x.bytes.len() == 0 {
        assert(x.bytes@.len() == 0);
        if y.bytes.len() == 0 {
            assert(y.bytes@.len() == 0);
            return Ord2::Equal;
        } else {
            assert(y.bytes@.len() > 0);
            return Ord2::Greater;
        }
    }
    if y.bytes.len() == 0 {
        assert(x.bytes@.len() > 0 && y.bytes@.len() == 0);
        return Ord2::Less;
    }
    assert(x.bytes@.len() > 0 && y.bytes@.len() > 0);
    /* Origin Rust: let lhs = self.as_str().split('.'); ... for lhs in lhs { ... } --
     * transcribed as the dual-track byte-state recursion (offset 0, all remaining),
     * case by case in lockstep with pre_cmp_st. */
    let r = pre_cmp_exec(&x.bytes, &x.bytes[..], 0, 0, &y.bytes, &y.bytes[..], 0, 0);
    assert(r == pre_cmp_st(x.bytes@, x.bytes@, 0, 0, y.bytes@, y.bytes@, 0, 0));
    r
}

fn pre_cmp_exec(
    oa: &[u8],
    a: &[u8],
    a_off: usize,
    sa: usize,
    ob: &[u8],
    b: &[u8],
    b_off: usize,
    bs: usize,
) -> (r: Ord2)
    requires
        sa <= a_off,
        bs <= b_off,
        a.len() + a_off == oa.len(),
        b.len() + b_off == ob.len(),
    ensures
        r == pre_cmp_st(oa@, a@, a_off as int, sa as int, ob@, b@, b_off as int, bs as int),
    decreases
        a.len() + b.len(),
{
    if a.len() == 0 {
        if b.len() == 0 {
            Ord2::Equal
        } else {
            Ord2::Less
        }
    } else if b.len() == 0 {
        Ord2::Greater
    } else {
        let ca = a[0];
        let cb = b[0];
        if ca == 0x2e && cb == 0x2e {
            pre_cmp_exec(oa, &a[1..], a_off + 1, a_off + 1, ob, &b[1..], b_off + 1, b_off + 1)
        } else if cb == 0x2e {
            res_a_ended_exec(ob, bs, oa, sa)
        } else if ca == 0x2e {
            res_a_ended_exec(oa, sa, ob, bs)
        } else if ca == cb {
            pre_cmp_exec(oa, &a[1..], a_off + 1, sa, ob, &b[1..], b_off + 1, bs)
        } else {
            res_unequal_exec(oa, a_off, sa, ob, b_off, bs)
        }
    }
}

fn res_unequal_exec(a: &[u8], a_off: usize, sa: usize, b: &[u8], b_off: usize, bs: usize) -> (r: Ord2)
    requires
        a_off < a.len(),
        b_off < b.len(),
        sa <= a_off,
        bs <= b_off,
    ensures
        r == res_unequal(a@, a_off as int, sa as int, b@, b_off as int, bs as int),
{
    let qA = seg_digits_all_exec(a, sa);
    let qB = seg_digits_all_exec(b, bs);
    if qA && qB {
        let la = seg_len_of(a, sa);
        let lb = seg_len_of(b, bs);
        if la != lb {
            if la < lb {
                Ord2::Less
            } else {
                Ord2::Greater
            }
        } else if a[a_off] < b[b_off] {
            Ord2::Less
        } else {
            Ord2::Greater
        }
    } else if qA {
        Ord2::Less
    } else if qB {
        Ord2::Greater
    } else if a[a_off] < b[b_off] {
        Ord2::Less
    } else {
        Ord2::Greater
    }
}

/// res_a_ended (the ending-first side = the first parameter pair).
fn res_a_ended_exec(a: &[u8], sa: usize, b: &[u8], bs: usize) -> (r: Ord2)
    requires
        sa <= a.len(),
        bs <= b.len(),
    ensures
        r == res_a_ended(a@, sa as int, b@, bs as int),
{
    let qA = seg_digits_all_exec(a, sa);
    let qB = seg_digits_all_exec(b, bs);
    if qA {
        if qB {
            let la = seg_len_of(a, sa);
            let lb = seg_len_of(b, bs);
            if la != lb {
                if la < lb {
                    Ord2::Less
                } else {
                    Ord2::Greater
                }
            } else {
                Ord2::Greater
            }
        } else {
            Ord2::Less
        }
    } else if qB {
        Ord2::Greater
    } else {
        Ord2::Less
    }
}

/* Comparison wrappers for the eval side (the transcription face of eval.rs's `ver.pre > cmp.pre` etc.) */

pub fn pre_lt(x: &Prerelease, y: &Prerelease) -> (r: bool)
    ensures
        r == (pre_cmp_spec_top(x.bytes@, y.bytes@) == Ord2::Less),
{
    pre_cmp(x, y) == Ord2::Less
}

pub fn pre_le(x: &Prerelease, y: &Prerelease) -> (r: bool)
    ensures
        r == (pre_cmp_spec_top(x.bytes@, y.bytes@) != Ord2::Greater),
{
    pre_cmp(x, y) != Ord2::Greater
}

pub fn pre_eq(x: &Prerelease, y: &Prerelease) -> (r: bool)
    ensures
        r == (pre_cmp_spec_top(x.bytes@, y.bytes@) == Ord2::Equal),
{
    pre_cmp(x, y) == Ord2::Equal
}

pub fn pre_gt(x: &Prerelease, y: &Prerelease) -> (r: bool)
    ensures
        r == (pre_cmp_spec_top(x.bytes@, y.bytes@) == Ord2::Greater),
{
    pre_cmp(x, y) == Ord2::Greater
}

pub fn pre_ge(x: &Prerelease, y: &Prerelease) -> (r: bool)
    ensures
        r == (pre_cmp_spec_top(x.bytes@, y.bytes@) != Ord2::Less),
{
    pre_cmp(x, y) != Ord2::Less
}

/// `Ord for Version` (derived: major, minor, patch, pre) -- this exec face
/// carries only the mmp+pre 4-tuple (= the face of Version::cmp_precedence;
/// a derive Ord's field order contains build, but that tie-break chain is not
/// transcribed here).
pub fn version_cmp_pre_model(a: &Version, b: &Version) -> (r: Ord2)
    ensures
        r == if a.major != b.major {
            if a.major < b.major {
                Ord2::Less
            } else {
                Ord2::Greater
            }
        } else if a.minor != b.minor {
            if a.minor < b.minor {
                Ord2::Less
            } else {
                Ord2::Greater
            }
        } else if a.patch != b.patch {
            if a.patch < b.patch {
                Ord2::Less
            } else {
                Ord2::Greater
            }
        } else {
            pre_cmp_spec_top(a.pre.bytes@, b.pre.bytes@)
        },
{
    if a.major != b.major {
        if a.major < b.major {
            Ord2::Less
        } else {
            Ord2::Greater
        }
    } else if a.minor != b.minor {
        if a.minor < b.minor {
            Ord2::Less
        } else {
            Ord2::Greater
        }
    } else if a.patch != b.patch {
        if a.patch < b.patch {
            Ord2::Less
        } else {
            Ord2::Greater
        }
    } else {
        pre_cmp(&a.pre, &b.pre)
    }
}


// ---------------------------------------------------------------------------
// Proof lemmas (a shared proof helper; measured: panels identical with the
// lemma at this position)
// ---------------------------------------------------------------------------
/// Lemma basis for the agreement of choose_segment_len with the scan.
proof fn lemma_witness_len(s: Seq<u8>, frm: int, acc: int, e: int)
    requires
        0 <= frm,
        0 <= acc,
        frm + acc <= e <= s.len(),
        seg_end_at(s, frm, e),
    ensures
        segment_len_witness(s, frm, acc) == e - frm,
    decreases
        e - frm - acc,
{
    if frm + acc == e {
    } else {
        lemma_witness_len(s, frm, acc + 1, e);
    }
}

} // verus!
