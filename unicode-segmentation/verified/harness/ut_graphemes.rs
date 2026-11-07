//! harness/ut_graphemes.rs -- witnesses of the transcribable face of the grapheme.rs inline UTs
//!
//! Covers the pair/classification-level obligations of the inventory (15 inline
//! grapheme.rs UTs):
//! - G16 test_incb_extend_excludes_linkers (grapheme.rs:1188-1196): the 5 named
//!   is_incb_linker assertions, all through the mirror's **verified** exec sites.
//! - G../G checked: the rule-matrix obligations of check_pair on **real
//!   characters** (classification via the tables axiom layer, rule behavior via
//!   the verified check_pair):
//!   GB3 ("\r","\n"), GB9c (InCB Consonant), GB11 (ZWJ+EP), GB12/13 (RIS),
//!   GB999 (ASCII x ASCII).
//!
//! Consumption: includes verified/src/lib.rs via #[path]; no spec copying.

use vstd::prelude::*;
use vstd::prelude::SpecOrd;

#[path = "../src/lib.rs"]
mod libm;

use libm::grapheme::check_pair;
use libm::grapheme::is_incb_extend;
use libm::grapheme::PairResult;
use libm::tables::grapheme::grapheme_category;
use libm::tables::grapheme::GraphemeCat;
use libm::tables::is_incb_linker;
use libm::grapheme::gceq;

verus! {

/// Exec discrimination of PairResult (constructor-split spec linkage).
fn pr_is(pr: PairResult, x: PairResult) -> (r: bool)
    ensures
        r == (pr == x),
{
    match (pr, x) {
        (PairResult::NotBreak, PairResult::NotBreak) => true,
        (PairResult::Break, PairResult::Break) => true,
        (PairResult::Extended, PairResult::Extended) => true,
        (PairResult::InCbConsonant, PairResult::InCbConsonant) => true,
        (PairResult::Regional, PairResult::Regional) => true,
        (PairResult::Emoji, PairResult::Emoji) => true,
        _ => false,
    }
}

/// G16 witness: test_incb_extend_excludes_linkers (grapheme.rs:1191-1195).
pub exec fn witness_incb_linker_exclusions() -> (r: bool)
    ensures
        r,
{
    // ZWNJ is not a linker
    let w0 = !is_incb_linker('\u{200c}');
    // Virama is a linker
    let w1 = is_incb_linker('\u{94d}');
    // 3 linkers added by Unicode 18 outside the Extend/ZWJ categories
    let w2 = is_incb_linker('\u{1cf5}');
    let w3 = is_incb_linker('\u{1cf6}');
    let w4 = is_incb_linker('\u{11a3a}');
    w0 && w1 && w2 && w3 && w4
}

/// Witness of the is_incb_extend derivation:
/// - (Any, 1CF5) is false -- the upstream comment (grapheme.rs:293-297) says a linker
///   whose gcb is neither Extend nor ZWJ is excluded by may_be_incb;
/// - (Extend, 094D) is false -- Virama itself is InCB=Linker, excluded by is_incb_linker;
/// - (ZWJ, 200D) is true -- ZWJ is InCB=Extend (not 200C, not a linker).
pub exec fn witness_is_incb_extend_derivation() -> (r: bool)
    ensures
        r,
{
    let w1 = !is_incb_extend(GraphemeCat::GC_Any, '\u{1cf5}');
    let w2 = !is_incb_extend(GraphemeCat::GC_Extend, '\u{94d}');
    let w3 = is_incb_extend(GraphemeCat::GC_ZWJ, '\u{200d}');
    let w4 = !is_incb_extend(GraphemeCat::GC_ZWJ, '\u{200c}');
    w1 && w2 && w3 && w4
}

/// Witness of the check_pair obligations on **real characters** (classification
/// values via the AX-g2/g3 anchors, rule behavior via the verified check_pair):
/// - GB3: "\r" x "\n" -- CR x LF does not break;
/// - GB9c: InCB Consonant ahead (0915 followed by 0915) triggers the InCbConsonant rule;
/// - GB11: ZWJ x Extended_Pictographic -> Emoji;
/// - GB12/13: RIS x RIS -> Regional;
/// - GB999: ASCII 'a' x 'b' -> Break.
pub exec fn witness_check_pair_real_chars() -> (r: bool)
    ensures
        r,
{
    let (l0, u0, c_cr) = grapheme_category('\r');
    let (l1, u1, c_lf) = grapheme_category('\n');
    assert(c_cr == GraphemeCat::GC_CR);
    assert(c_lf == GraphemeCat::GC_LF);
    let gb3 = pr_is(check_pair(c_cr, c_lf), PairResult::NotBreak);
    assert(gb3);

    let (_, _, c_ka1) = grapheme_category('\u{915}');
    let gb9c = pr_is(check_pair(c_ka1, c_ka1), PairResult::InCbConsonant);

    let (_, _, c_zwj) = grapheme_category('\u{200d}');
    let (_, _, c_ep) = grapheme_category('\u{1f600}');
    let gb11 = pr_is(check_pair(c_zwj, c_ep), PairResult::Emoji);

    let (_, _, c_ris1) = grapheme_category('\u{1f1e6}');
    let (_, _, c_ris2) = grapheme_category('\u{1f1ff}');
    let gb12 = pr_is(check_pair(c_ris1, c_ris2), PairResult::Regional);

    let (_, _, c_a) = grapheme_category('a');
    let (_, _, c_b) = grapheme_category('b');
    let gb999 = pr_is(check_pair(c_a, c_b), PairResult::Break);

    assert(gb9c);
    assert(gb11);
    assert(gb12);
    assert(gb999);
    gb3 && gb9c && gb11 && gb12 && gb999
}

/// The ascii fast path's boundary at 0x7F (the upstream grapheme.rs:357 comment
/// "except U+007F"): 0x7F takes GC_Control from the table (runtime-confirmed;
/// the AX duty is verified via the passing drivers); the fast path excludes it.
pub exec fn witness_ascii_fastpath_bound() -> (r: bool)
    ensures
        r,
{
    let (lo, hi, c_del) = grapheme_category('\u{7f}');
    let p1 = gceq(c_del, GraphemeCat::GC_Control);
    let (lo2, hi2, c_a) = grapheme_category('a');
    let p2 = gceq(c_a, GraphemeCat::GC_Any);
    p1 && p2
}

}

fn main() {}
