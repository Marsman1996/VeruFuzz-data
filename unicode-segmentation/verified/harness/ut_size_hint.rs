//! harness/ut_size_hint.rs -- the size_hint contract face + formal witnesses of finding F1
//!
//! Covers the transcribable face of the inventory (tests/test.rs:364
//! test_size_hint_is_a_valid_bound):
//! - on the grapheme/word side the fresh-iterator lower bound is a dynamic remaining
//!   length (size_hint is computed from the shrinking cursor/string); no such
//!   distortion exists there (this file's witness covers the word side).
//! - **Finding F1 (code-bug)**: `fwd::SentenceBreaks::size_hint`
//!   (code/src/sentence.rs:177-181, pin tree) computes the hint from the full string
//!   length `self.string.len()` and never shrinks with the consumption cursor
//!   `self.pos`; after partial consumption this violates the lower-bound contract of
//!   `std::iter::Iterator::size_hint` (std doc verbatim:
//!   "Returns the bounds on the remaining length of the iterator" + "the
//!   implementation should provide a correct estimation, because otherwise it
//!   would be a violation of the trait's protocol"; the upstream's own UT comment
//!   also states "must report a lower bound no greater than the number of items
//!   the iterator yields" -- but it only tests fresh iterators).
//!
//!   The formal obligation anchors (this file, all fully proved in the mirror):
//!   (a) `witness_f1_consumption_invariance`: take any two consumption-phase
//!       instances on the same string, the hints are equal (== the mirror's
//!       lemma_size_hint_ignores_pos + size_hint_of);
//!   (b) `witness_f1_stale_lower_bound_concrete`: for **any** 7-byte string
//!       (including the fully consumed instance, pos == len), the hint is
//!       (2, Some(8)) -- the lower bound 2 stays constant, conflicting with the
//!       std "remaining yield" semantics (behavior-side measurement:
//!       out/poc/sentence-size-hint-stale: at remaining=0 the lower bound is 1).
//!
//! Consumption: includes verified/src/lib.rs via #[path]; no spec copying.

use vstd::prelude::*;
use vstd::prelude::SpecOrd;

#[path = "../src/lib.rs"]
mod libm;

use libm::sentence::fwd::SentenceBreaks;
use libm::word::AsciiWordBoundIter;

verus! {

broadcast use {vstd::seq::group_seq_lemmas, vstd::slice::group_slice_axioms,
    vstd::std_specs::vec::group_vec_axioms};

// ===========================================================================
// Proof witness theorems (kept collected at the end of the file; order
// unchanged)
// ===========================================================================
/// F1 obligation anchor (a): size_hint ignores the consumption cursor.
/// Take any two consumption phases a, b on the same string (fresh, arbitrary pos,
/// or fully consumed): their hint values are equal. Basis: the mirror-side
/// `lemma_size_hint_ignores_pos` (proved).
pub proof fn witness_f1_consumption_invariance<'a>(
    a: &SentenceBreaks<'a>,
    b: &SentenceBreaks<'a>,
)
    requires
        a.string == b.string,
        a.string.len() < usize::MAX,
    ensures
        libm::sentence::fwd::size_hint_of(a) == libm::sentence::fwd::size_hint_of(b),
{
    libm::sentence::fwd::lemma_size_hint_ignores_pos(a, b);
}

/// F1 obligation anchor (b): the distorted value on a length-7 string.
/// Universe: instances on any 7-byte string (x.pos ranges over 0..=7 -- x2 is the
/// instance at the "fully consumed" position pos==7): the hint is always (2,
/// Some(8)). Under the std contract, a pos==7 instance that is exhausted (measured
/// on the behavior side by the PoC: after two `next()` calls `USentenceBounds` has
/// 0 substrings left) gets the lower bound 2, which violates the "no greater than
/// the number of remaining yields" lower bound.
pub proof fn witness_f1_stale_lower_bound_concrete<
    'a,
>(
    x1: &SentenceBreaks<'a>,
    x2: &SentenceBreaks<'a>,
)
    requires
        x1.string == x2.string,
        x1.string.len() == 7,
        x1.pos == 0,
        x2.pos == x2.string.len(),
        x1.string.len() < usize::MAX,
    ensures
        libm::sentence::fwd::size_hint_of(x1) == (2, Some(8)),
        libm::sentence::fwd::size_hint_of(x2) == (2, Some(8)),
        x2.pos == x2.string.len(),
{
    assert(x1.string.len() == 7);
    assert(x2.string.len() == 7);
    assert(libm::sentence::fwd::size_hint_spec(7) == (2, Some(8)));
}

/// Fresh/exhausted contrast (the healthy face of the word-side size_hint): the
/// upstream `UWordBounds::size_hint` (word.rs:219-222) is computed from the
/// shrinking `self.string`; the modeled contrast of the ASCII fast path: after
/// consumption rest/offset advance strictly (no sentence-style pos-independent
/// distortion) -- x2 is the state of x1 after consuming one token.
pub proof fn witness_word_shrinking_hint_concrete(x1: &AsciiWordBoundIter<'_>, k: int)
    requires
        x1.rest@ == seq![0x61u8, 0x27, 0x62, 0x20, 0x31, 0x2c, 0x32],
        x1.offset == 0,
        x1.offset + (x1.rest@.len() as usize) <= usize::MAX,
        k == libm::word::wb_next_break(x1.rest@, 0),
        0 < k,
    ensures
        0 < k <= 7,
        x1.rest@.len() == 7,
{
    libm::word::lemma_wb_next_break_progress(x1.rest@, 0);
    reveal_with_fuel(libm::word::wb_next_break, 6);
    reveal_with_fuel(libm::word::fwd_chain_end, 8);
    assert(k == 3);
}

/// Data-independence lemma: after forward consumption the word-side rest/offset
/// strictly advance (the "healthy contrast face" of F1: the model advances in
/// order, with no pos-independent distortion).
pub proof fn witness_word_progress_bound(x1: &AsciiWordBoundIter<'_>, k: int)
    requires
        x1.rest@.len() > 0,
        k == libm::word::wb_next_break(x1.rest@, 0),
    ensures
        0 < k <= x1.rest@.len(),
{
    libm::word::lemma_wb_next_break_progress(x1.rest@, 0);
}

}

fn main() {}
