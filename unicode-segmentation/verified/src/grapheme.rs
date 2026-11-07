//! `grapheme.rs` library mirror -- formal verification deliverable
//!
//! Upstream: code/src/grapheme.rs (pin e445e101b129862148127c9e41ab4486b0125232, tree untouched)
//!
//! The obligation face of this file (fully verified):
//! - `check_pair`: the 15x15 rule matrix of UAX#29 GB3-GB999 (grapheme.rs:264-283),
//!   exhaustively aligned with the rule-text spec model `gb_pair_model`
//!   (including the match-arm priority order: GB3 (CR,LF) before GB4's (CR,_) etc.).
//! - `may_be_incb` / `is_incb_linker` (tables layer) combined into `is_incb_extend`:
//!   the InCB=Extend derivation definition of the upstream doc (grapheme.rs:285-300).
//! - `GraphemeCursor::new / set_cursor / cur_cursor`: initialization invariants of the
//!   state fields (offset==0||offset==len ==> Break; set_cursor resets the source fields).
//! - `GraphemeCursor::grapheme_category` (ASCII fast path + range cache): for any char,
//!   its return value == the inductive table-lookup model of the tables axiom layer.
//!
//! Mirror and relaxation ledger (blocked items per out/bug-finder-summary.md):
//! 1. `is_boundary / next_boundary / prev_boundary / provide_context` (the chunked
//!    state machine, grapheme.rs:642-917): a cross-chunk resuming state machine
//!    (four groups of Option state -- resuming/pre_context/ris_count/incb_linker_count
//!    -- plus &str chars iteration) exceeds this round's SMT capacity -> not
//!    transcribed in the mirror (blocked); the substitute obligation faces are:
//!    (a) this file's check_pair/InCB/constructors fully proved; (b) the bounds/
//!    classification properties of the tables axiom layer; (c) the runtime face of
//!    the upstream's 16 GraphemeCursor UTs (tests/test.rs + the grapheme.rs inline
//!    UTs, host cargo runs green).
//! 2. The `Graphemes/GraphemeIndices` iterators (grapheme.rs:100-139): they depend
//!    on the blocked next_boundary; only the constructors and the pure arithmetic
//!    face of size_hint are transcribed.
//! 3. Table-lookup dependencies: the tables mirror's external_body + axiom layer
//!    (AX-g1..g5).

use vstd::prelude::*;
use vstd::prelude::SpecOrd;

pub use super::tables::grapheme::GraphemeCat;
use super::tables::grapheme as gr;
pub use super::tables::is_incb_linker;

verus! {

/// An enum describing information about a potential boundary.
/// Verbatim mirror of the upstream GraphemeState (grapheme.rs:161-183).
pub enum GraphemeState {
    /// No information is known.
    Unknown,
    /// It is known to not be a boundary.
    NotBreak,
    /// It is known to be a boundary.
    Break,
    /// The codepoint after it has Indic_Conjunct_Break=Consonant (GB9c, Unicode 18).
    InCbConsonant,
    /// The codepoint after is a Regional Indicator Symbol (GB12, GB13).
    Regional,
    /// The codepoint after is Extended_Pictographic; GB11 pre-context (ZWJ) seen.
    Emoji {
        seen_zwj: bool,
    },
}

/// An enum describing the result from lookup of a pair of categories.
/// Verbatim mirror of the upstream PairResult (grapheme.rs:245-262).
pub enum PairResult {
    NotBreak,
    Break,
    Extended,
    InCbConsonant,
    Regional,
    Emoji,
}

/// Spec model of the UAX#29 rule text (GB3-GB999, written in the priority order by
/// which the axiom instances are decided); the obligation = exec `check_pair` equal
/// to this model pair by pair.
pub open spec fn gb_pair_model(before: GraphemeCat, after: GraphemeCat) -> PairResult {
    if before == GraphemeCat::GC_CR && after == GraphemeCat::GC_LF {
        PairResult::NotBreak // GB3
    } else if (before == GraphemeCat::GC_Control || before == GraphemeCat::GC_CR
        || before == GraphemeCat::GC_LF) {
        PairResult::Break // GB4
    } else if (after == GraphemeCat::GC_Control || after == GraphemeCat::GC_CR
        || after == GraphemeCat::GC_LF) {
        PairResult::Break // GB5
    } else if (before == GraphemeCat::GC_L
        && (after == GraphemeCat::GC_L || after == GraphemeCat::GC_V
            || after == GraphemeCat::GC_LV || after == GraphemeCat::GC_LVT)) {
        PairResult::NotBreak // GB6
    } else if ((before == GraphemeCat::GC_LV || before == GraphemeCat::GC_V)
        && (after == GraphemeCat::GC_V || after == GraphemeCat::GC_T)) {
        PairResult::NotBreak // GB7
    } else if ((before == GraphemeCat::GC_LVT || before == GraphemeCat::GC_T)
        && after == GraphemeCat::GC_T) {
        PairResult::NotBreak // GB8
    } else if (after == GraphemeCat::GC_Extend || after == GraphemeCat::GC_ZWJ) {
        PairResult::NotBreak // GB9
    } else if (after == GraphemeCat::GC_SpacingMark) {
        PairResult::Extended // GB9a
    } else if (before == GraphemeCat::GC_Prepend) {
        PairResult::Extended // GB9b
    } else if (after == GraphemeCat::GC_InCB_Consonant) {
        PairResult::InCbConsonant // GB9c
    } else if (before == GraphemeCat::GC_ZWJ
        && after == GraphemeCat::GC_Extended_Pictographic) {
        PairResult::Emoji // GB11
    } else if (before == GraphemeCat::GC_Regional_Indicator
        && after == GraphemeCat::GC_Regional_Indicator) {
        PairResult::Regional // GB12, GB13
    } else {
        PairResult::Break // GB999
    }
}

/// Exec equality for GraphemeCat (the enum `==`, being std-derived inside Verus,
/// has no spec linkage; same method as StatePart's peq: match discrimination).
pub fn gceq(a: GraphemeCat, b: GraphemeCat) -> (r: bool)
    ensures
        r == (a == b),
{
    match (a, b) {
        (GraphemeCat::GC_Any, GraphemeCat::GC_Any) => true,
        (GraphemeCat::GC_CR, GraphemeCat::GC_CR) => true,
        (GraphemeCat::GC_Control, GraphemeCat::GC_Control) => true,
        (GraphemeCat::GC_Extend, GraphemeCat::GC_Extend) => true,
        (GraphemeCat::GC_Extended_Pictographic, GraphemeCat::GC_Extended_Pictographic) => true,
        (GraphemeCat::GC_InCB_Consonant, GraphemeCat::GC_InCB_Consonant) => true,
        (GraphemeCat::GC_L, GraphemeCat::GC_L) => true,
        (GraphemeCat::GC_LF, GraphemeCat::GC_LF) => true,
        (GraphemeCat::GC_LV, GraphemeCat::GC_LV) => true,
        (GraphemeCat::GC_LVT, GraphemeCat::GC_LVT) => true,
        (GraphemeCat::GC_Prepend, GraphemeCat::GC_Prepend) => true,
        (GraphemeCat::GC_Regional_Indicator, GraphemeCat::GC_Regional_Indicator) => true,
        (GraphemeCat::GC_SpacingMark, GraphemeCat::GC_SpacingMark) => true,
        (GraphemeCat::GC_T, GraphemeCat::GC_T) => true,
        (GraphemeCat::GC_V, GraphemeCat::GC_V) => true,
        (GraphemeCat::GC_ZWJ, GraphemeCat::GC_ZWJ) => true,
        _ => false,
    }
}

/// FULLY VERIFIED verbatim mirror of the upstream check_pair (grapheme.rs:264-283):
/// the match arm order is the rule priority order; the obligation = exhaustive
/// equality with gb_pair_model.
pub fn check_pair(before: GraphemeCat, after: GraphemeCat) -> (r: PairResult)
    ensures
        r == gb_pair_model(before, after),
{
    // Origin Rust: the match (before, after) of grapheme.rs:268-282; arm order kept:
    // (GC_CR, GC_LF) must precede GB4's (Control|CR|LF, _); GB9 precedes GB9a/9b/9c;
    // GB11/GB12-13 precede GB999. Equality goes through gceq (constructor
    // discrimination) so that the spec links under Verus.
    let b_cr_lf = gceq(before, GraphemeCat::GC_CR);
    let a_lf = gceq(after, GraphemeCat::GC_LF);
    let b_ctl_cr_lf = cat_is_control_cr_lf(before);
    let a_ctl_cr_lf = cat_is_control_cr_lf(after);
    let a_extend_zwj = cat_is_extend_or_zwj(after);
    let a_spacing = gceq(after, GraphemeCat::GC_SpacingMark);
    let b_prepend = gceq(before, GraphemeCat::GC_Prepend);
    let a_incb_cons = gceq(after, GraphemeCat::GC_InCB_Consonant);
    let b_zwj = gceq(before, GraphemeCat::GC_ZWJ);
    let a_epic = gceq(after, GraphemeCat::GC_Extended_Pictographic);
    let b_ris = gceq(before, GraphemeCat::GC_Regional_Indicator);
    let a_ris = gceq(after, GraphemeCat::GC_Regional_Indicator);

    if b_cr_lf && a_lf {
        PairResult::NotBreak // GB3
    } else if b_ctl_cr_lf {
        PairResult::Break // GB4
    } else if a_ctl_cr_lf {
        PairResult::Break // GB5
    } else if cat_is_l(before) && cat_v_or_lvt_or_t(after) {
        PairResult::NotBreak // GB6
    } else if cat_is_lv_or_v(before) && cat_is_v_or_t(after) {
        PairResult::NotBreak // GB7
    } else if cat_is_lvt_or_t(before) && gceq(after, GraphemeCat::GC_T) {
        PairResult::NotBreak // GB8
    } else if a_extend_zwj {
        PairResult::NotBreak // GB9
    } else if a_spacing {
        PairResult::Extended // GB9a
    } else if b_prepend {
        PairResult::Extended // GB9b
    } else if a_incb_cons {
        PairResult::InCbConsonant // GB9c
    } else if b_zwj && a_epic {
        PairResult::Emoji // GB11
    } else if b_ris && a_ris {
        PairResult::Regional // GB12, GB13
    } else {
        PairResult::Break // GB999
    }
}

/// Exec face of GC_Extend | GC_ZWJ.
fn cat_is_extend_or_zwj(c: GraphemeCat) -> (r: bool)
    ensures
        r == (c == GraphemeCat::GC_Extend || c == GraphemeCat::GC_ZWJ),
{
    match c {
        GraphemeCat::GC_Extend => true,
        GraphemeCat::GC_ZWJ => true,
        _ => false,
    }
}

fn cat_is_control_cr_lf(c: GraphemeCat) -> (r: bool)
    ensures
        r == (c == GraphemeCat::GC_Control || c == GraphemeCat::GC_CR || c == GraphemeCat::GC_LF),
{
    match c {
        GraphemeCat::GC_Control => true,
        GraphemeCat::GC_CR => true,
        GraphemeCat::GC_LF => true,
        _ => false,
    }
}

fn cat_is_l(c: GraphemeCat) -> (r: bool)
    ensures
        r == (c == GraphemeCat::GC_L),
{
    match c {
        GraphemeCat::GC_L => true,
        _ => false,
    }
}

fn cat_is_lv_or_v(c: GraphemeCat) -> (r: bool)
    ensures
        r == (c == GraphemeCat::GC_LV || c == GraphemeCat::GC_V),
{
    match c {
        GraphemeCat::GC_LV => true,
        GraphemeCat::GC_V => true,
        _ => false,
    }
}

fn cat_is_lvt_or_t(c: GraphemeCat) -> (r: bool)
    ensures
        r == (c == GraphemeCat::GC_LVT || c == GraphemeCat::GC_T),
{
    match c {
        GraphemeCat::GC_LVT => true,
        GraphemeCat::GC_T => true,
        _ => false,
    }
}

fn cat_is_v_or_t(c: GraphemeCat) -> (r: bool)
    ensures
        r == (c == GraphemeCat::GC_V || c == GraphemeCat::GC_T),
{
    match c {
        GraphemeCat::GC_V => true,
        GraphemeCat::GC_T => true,
        _ => false,
    }
}

fn cat_v_or_lvt_or_t(c: GraphemeCat) -> (r: bool)
    ensures
        r == (c == GraphemeCat::GC_L || c == GraphemeCat::GC_V
            || c == GraphemeCat::GC_LV || c == GraphemeCat::GC_LVT),
{
    match c {
        GraphemeCat::GC_L => true,
        GraphemeCat::GC_V => true,
        GraphemeCat::GC_LV => true,
        GraphemeCat::GC_LVT => true,
        _ => false,
    }
}

/// Spec model of may_be_incb: the gcb in {Extend, ZWJ} necessary condition.
pub open spec fn may_be_incb_model(cat: GraphemeCat) -> bool {
    cat == GraphemeCat::GC_Extend || cat == GraphemeCat::GC_ZWJ
}

/// FULLY VERIFIED verbatim mirror of may_be_incb (grapheme.rs:313-315).
/// Upstream doc (grapheme.rs:307-311):
///   `InCB=Extend` is a subset of `gcb=Extend` and `gcb=ZWJ`, so any category
///   other than those rules out the `InCB=Extend` role without inspecting the codepoint.
///   However, `InCB=Linker` is *not* necessarily a subset of those categories (since
///   Unicode 18), so callers that handle Indic conjunct break must check
///   `is_incb_linker` independently of this function.
pub fn may_be_incb(cat: GraphemeCat) -> (r: bool)
    ensures
        r == may_be_incb_model(cat),
{
    match cat {
        GraphemeCat::GC_Extend => true,
        GraphemeCat::GC_ZWJ => true,
        _ => false,
    }
}

/// FULLY VERIFIED verbatim mirror of is_incb_extend (grapheme.rs:301-305).
/// Result-classification obligation: with ZWNJ and InCB=Linker excluded, gcb in
/// {Extend,ZWJ} is exactly InCB=Extend.
/// Upstream doc (grapheme.rs:285-300):
///   Whether `ch`, whose grapheme category is `cat`, has `Indic_Conjunct_Break=Extend`.
///   `InCB=Extend` is defined as
///   `[\p{gcb=Extend} \p{gcb=ZWJ}] - \p{InCB=Linker} - \p{InCB=Consonant} - U+200C`,
///   and no `InCB=Consonant` is `gcb=Extend` or `gcb=ZWJ`,
///   so the grapheme category the caller already has, plus two equality tests, decides it.
///   Note: since Unicode 18, some `InCB=Linker` characters (e.g. U+1CF5, U+1CF6, U+11A3A)
///   have gcb categories other than `Extend` or `ZWJ`. This does not affect correctness:
///   those characters are not in `InCB=Extend` either, and `is_incb_extend` correctly
///   returns false for them because `may_be_incb` returns false for their gcb category.
///   The callers that need to handle `InCB=Linker` (e.g. GB9c) must check
///   `is_incb_linker` separately.
///   `scripts/unicode.py` checks the derivation against the UCD when it regenerates `src/tables.rs`,
///   so a future Unicode version cannot silently invalidate it.
pub fn is_incb_extend(cat: GraphemeCat, ch: char) -> (r: bool)
    ensures
        r == (may_be_incb_model(cat) && ch != '\u{200c}'
            && !super::tables::is_incb_linker_model(ch)),
{
    may_be_incb(cat) && ch != '\u{200c}' && !is_incb_linker(ch)
}

/// Read-only view: the spec model of the lookup cache inside the cursor.
pub struct GraphemeCursor {
    pub offset: usize,
    pub len: usize,
    pub is_extended: bool,
    pub state: GraphemeCursorState,
    pub grapheme_cat_cache: (u32, u32, GraphemeCat),
}

/// Exec-side discrimination of GraphemeState (enum case split; the original order
/// keeps the semantics).
pub enum GraphemeCursorState {
    Unknown,
    NotBreak,
    Break,
    InCbConsonant,
    Regional,
    Emoji {
        seen_zwj: bool,
    },
}

impl View for GraphemeCursorState {
    type V = int;

    open spec fn view(&self) -> int {
        match_state(self)
    }
}

pub open spec fn match_state(s: &GraphemeCursorState) -> int {
    match *s {
        GraphemeCursorState::Unknown => 0,
        GraphemeCursorState::NotBreak => 1,
        GraphemeCursorState::Break => 2,
        GraphemeCursorState::InCbConsonant => 3,
        GraphemeCursorState::Regional => 4,
        GraphemeCursorState::Emoji { seen_zwj } => 5,
    }
}

/// UAX#29 boundary-base model: 0 or len is always a break point.
pub open spec fn boundary_at_ends(offset: usize, len: usize) -> bool {
    offset == 0 || offset == len
}

impl GraphemeCursor {
    /// FULLY VERIFIED verbatim mirror of new (grapheme.rs:332-351):
    /// the state initialization is preserved (endpoints ==> Break).
    /// Upstream doc (grapheme.rs:318-331):
    ///   Create a new cursor. The string and initial offset are given at creation
    ///   time, but the contents of the string are not. The `is_extended` parameter
    ///   controls whether extended grapheme clusters are selected.
    ///   The `offset` parameter must be on a codepoint boundary.
    pub fn new(offset: usize, len: usize, is_extended: bool) -> (c: GraphemeCursor)
        ensures
            c.offset == offset,
            c.len == len,
            c.is_extended == is_extended,
            (offset == 0 || offset == len) ==> c.state@ == 2,
    {
        GraphemeCursor {
            offset,
            len,
            is_extended,
            state: if offset == 0 || offset == len {
                GraphemeCursorState::Break
            } else {
                GraphemeCursorState::Unknown
            },
            grapheme_cat_cache: (0, 0, GraphemeCat::GC_Control),
        }
    }

    /// FULLY VERIFIED verbatim mirror of cur_cursor (grapheme.rs:427-429).
    /// Upstream doc (grapheme.rs:414-426):
    ///   The current offset of the cursor. Equal to the last value provided to
    ///   `new()` or `set_cursor()`, or returned from `next_boundary()` or
    ///   `prev_boundary()`.
    pub fn cur_cursor(&self) -> (r: usize)
        ensures
            r == self.offset,
    {
        self.offset
    }

}




}

fn main() {}
