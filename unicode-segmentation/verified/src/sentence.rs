//! `sentence.rs` library mirror -- formal verification deliverable
//!
//! Upstream: code/src/sentence.rs (pin e445e101b129862148127c9e41ab4486b0125232, tree untouched)
//!
//! Mirror and relaxation ledger (KVerus relax caliber):
//! 1. The pure enum state-machine layer (SentenceBreaksState's next/end/match1
//!    match2 and match_sb8a/match_sb9/match_sb11) transcribed verbatim and fully
//!    verified (against the spec_* models; the UAX#29 rule comments are their spec
//!    source).
//! 2. The table-lookup dependency `se::sentence_category`: the tables mirror's
//!    external_body + axiom layer (AX-s1/s2; runtime validated in full:
//!    out/verus-bugfinder/tables_equiv).
//! 3. `fwd::SentenceBreaks::next` (the SB1-SB998 main loop) and `match_sb8`
//!    (depends on &str chars() iteration semantics): the external boundary keeps the
//!    verbatim body, no fabricated contract; the obligation face moves to the
//!    state-advance/matcher theorems (blocked items per the summary).
//! 4. `fwd::SentenceBreaks::size_hint` kept verbatim (**distortion included**: it
//!    computes the hint from the full string length and never shrinks with pos);
//!    `lemma_size_hint_ignores_pos` thematizes "the result ignores the consumed
//!    prefix" -- the formal-side evidence of finding F1; the behavior side is
//!    re-confirmed by out/poc/sentence-size-hint-stale.
//! 5. The std `Filter` adapter is outside the Verus support surface -> the
//!    UnicodeSentences filter body is not transcribed.
//! 6. relax: the visibility of fwd::SentenceBreaks.pos is opened (for theorems
//!    constructing consumed states).

use vstd::prelude::*;
use vstd::prelude::SpecOrd;

verus! {

pub use super::tables::sentence::SentenceCat;

// All of the logic for forward iteration over sentences
pub mod fwd {
    use vstd::prelude::*;
    use vstd::prelude::SpecOrd;
    broadcast use vstd::array::group_array_axioms; // seq lemmas via mod-scope broadcast in parent
    use vstd::string::StringSliceAdditionalSpecFns;
    pub use super::super::tables::sentence::SentenceCat;
    use core::cmp;

    // Describe a parsed part of source string as described in this table:
    // https://unicode.org/reports/tr29/#Default_Sentence_Boundaries
    #[derive(PartialEq, Eq, Clone, Copy)]
    pub enum StatePart {
        Sot,
        Eot,
        Other,
        CR,
        LF,
        Sep,
        ATerm,
        UpperLower,
        ClosePlus,
        SpPlus,
        STerm,
    }

    #[derive(Clone)]
    pub struct SentenceBreaksState(pub [StatePart; 4]);

    impl View for SentenceBreaksState {
        type V = Seq<StatePart>;

        open spec fn view(&self) -> Seq<StatePart> {
            self.0@
        }
    }

    pub const INITIAL_STATE: SentenceBreaksState = SentenceBreaksState([
        StatePart::Sot,
        StatePart::Sot,
        StatePart::Sot,
        StatePart::Sot,
    ]);

    /// The StatePart carried by `cat` (the match cat branch of the upstream next()).
    pub open spec fn part_of_cat(cat: SentenceCat) -> StatePart {
        match cat {
            SentenceCat::SC_CR => StatePart::CR,
            SentenceCat::SC_LF => StatePart::LF,
            SentenceCat::SC_Sep => StatePart::Sep,
            SentenceCat::SC_ATerm => StatePart::ATerm,
            SentenceCat::SC_Upper => StatePart::UpperLower,
            SentenceCat::SC_Lower => StatePart::UpperLower,
            SentenceCat::SC_Close => StatePart::ClosePlus,
            SentenceCat::SC_Sp => StatePart::SpPlus,
            SentenceCat::SC_STerm => StatePart::STerm,
            _ => StatePart::Other,
        }
    }

    /// StatePart equality in exec: by constructor discrimination (Verus cannot
    /// link the std-derived `==` with spec equality; this form is provable).
    pub fn peq(a: StatePart, b: StatePart) -> (r: bool)
        ensures r == (a == b)
    {
        match (a, b) {
            (StatePart::Sot, StatePart::Sot) => true,
            (StatePart::Eot, StatePart::Eot) => true,
            (StatePart::Other, StatePart::Other) => true,
            (StatePart::CR, StatePart::CR) => true,
            (StatePart::LF, StatePart::LF) => true,
            (StatePart::Sep, StatePart::Sep) => true,
            (StatePart::ATerm, StatePart::ATerm) => true,
            (StatePart::UpperLower, StatePart::UpperLower) => true,
            (StatePart::ClosePlus, StatePart::ClosePlus) => true,
            (StatePart::SpPlus, StatePart::SpPlus) => true,
            (StatePart::STerm, StatePart::STerm) => true,
            _ => false,
        }
    }

    impl SentenceBreaksState {
        /// Spec model of `next`: collapse ClosePlus x SC_Close / SpPlus x SC_Sp, else shift.
        pub open spec fn spec_next_seq(self, cat: SentenceCat) -> Seq<StatePart> {
            let parts = self@;
            let collapsed = (parts[3] == StatePart::ClosePlus && cat == SentenceCat::SC_Close)
                || (parts[3] == StatePart::SpPlus && cat == SentenceCat::SC_Sp);
            if collapsed {
                parts
            } else {
                Seq::new(
                    4,
                    |i: int| if i < 3 { parts[1 + i] } else { part_of_cat(cat) },
                )
            }
        }

        /// Spec model of `end` (SB2): shift left one and append Eot.
        pub open spec fn spec_end_seq(self) -> Seq<StatePart> {
            let parts = self@;
            Seq::new(4, |i: int| if i < 3 { parts[1 + i] } else { StatePart::Eot })
        }


        pub open spec fn spec_match1(self, part: StatePart) -> bool {
            part == self@[3]
        }

        /// match_sb8a (SB8a): SATerm Close* Sp*
        pub open spec fn spec_sb8a(self) -> bool {
            let parts = self@;
            let idx0 = if parts[3] == StatePart::SpPlus { 2 } else { 3 };
            let idx = if parts[idx0] == StatePart::ClosePlus { idx0 - 1 } else { idx0 };
            parts[idx] == StatePart::STerm || parts[idx] == StatePart::ATerm
        }

        /// match_sb9 (SB9): SATerm Close*
        pub open spec fn spec_sb9(self) -> bool {
            let parts = self@;
            let idx = if parts[3] == StatePart::ClosePlus { 2 } else { 3 };
            parts[idx] == StatePart::STerm || parts[idx] == StatePart::ATerm
        }

        /// match_sb11 (SB11): SATerm Close* Sp* ParaSep?
        pub open spec fn spec_sb11(self) -> bool {
            let parts = self@;
            let idx0 = if parts[3] == StatePart::Sep
                || parts[3] == StatePart::CR
                || parts[3] == StatePart::LF
            {
                2
            } else {
                3
            };
            let idx1 = if parts[idx0] == StatePart::SpPlus { idx0 - 1 } else { idx0 };
            let idx = if parts[idx1] == StatePart::ClosePlus { idx1 - 1 } else { idx1 };
            parts[idx] == StatePart::STerm || parts[idx] == StatePart::ATerm
        }

        /// FULLY VERIFIED verbatim translation of upstream next().
        pub fn next(&self, cat: SentenceCat) -> (r: SentenceBreaksState)
            ensures
                r@.len() == 4,
                r@ == self.spec_next_seq(cat),
        {
            let p0 = self.0[0usize];
            let p1 = self.0[1usize];
            let p2 = self.0[2usize];
            let p3 = self.0[3usize];
            let newp = match cat {
                SentenceCat::SC_CR => StatePart::CR,
                SentenceCat::SC_LF => StatePart::LF,
                SentenceCat::SC_Sep => StatePart::Sep,
                SentenceCat::SC_ATerm => StatePart::ATerm,
                SentenceCat::SC_Upper | SentenceCat::SC_Lower => StatePart::UpperLower,
                SentenceCat::SC_Close => StatePart::ClosePlus,
                SentenceCat::SC_Sp => StatePart::SpPlus,
                SentenceCat::SC_STerm => StatePart::STerm,
                _ => StatePart::Other,
            };
            let collapses_close = match cat {
                SentenceCat::SC_Close => peq(p3, StatePart::ClosePlus),
                _ => false,
            };
            let collapses_sp = match cat {
                SentenceCat::SC_Sp => peq(p3, StatePart::SpPlus),
                _ => false,
            };
            let collapsed = collapses_close || collapses_sp;
            if collapsed {
                SentenceBreaksState([p0, p1, p2, p3])
            } else {
                SentenceBreaksState([p1, p2, p3, newp])
            }
        }

        /// FULLY VERIFIED verbatim translation of upstream end().
        pub fn end(&self) -> (r: SentenceBreaksState)
            ensures
                r@.len() == 4,
                r@ == self.spec_end_seq(),
        {
            let p1 = self.0[1usize];
            let p2 = self.0[2usize];
            let p3 = self.0[3usize];
            SentenceBreaksState([p1, p2, p3, StatePart::Eot])
        }

        pub fn match1(&self, part: StatePart) -> (r: bool)
            ensures r == self.spec_match1(part)
        {
            peq(part, self.0[3usize])
        }

        pub fn match2(&self, part1: StatePart, part2: StatePart) -> (r: bool)
            ensures r == (part1 == self@[2] && part2 == self@[3])
        {
            peq(part1, self.0[2usize]) && peq(part2, self.0[3usize])
        }

        /// FULLY VERIFIED verbatim translation of upstream match_sb8a.
        pub fn match_sb8a(&self) -> (r: bool)
            ensures r == self.spec_sb8a()
        {
            let mut idx = if peq(self.0[3usize], StatePart::SpPlus) { 2usize } else { 3usize };
            if peq(self.0[idx], StatePart::ClosePlus) {
                idx = idx - 1;
            }
            peq(self.0[idx], StatePart::STerm) || peq(self.0[idx], StatePart::ATerm)
        }

        /// FULLY VERIFIED verbatim translation of upstream match_sb9.
        pub fn match_sb9(&self) -> (r: bool)
            ensures r == self.spec_sb9()
        {
            let idx = if peq(self.0[3usize], StatePart::ClosePlus) { 2usize } else { 3usize };
            peq(self.0[idx], StatePart::STerm) || peq(self.0[idx], StatePart::ATerm)
        }

        /// FULLY VERIFIED verbatim translation of upstream match_sb11.
        pub fn match_sb11(&self) -> (r: bool)
            ensures r == self.spec_sb11()
        {
            let mut idx = if peq(self.0[3usize], StatePart::Sep)
                || peq(self.0[3usize], StatePart::CR)
                || peq(self.0[3usize], StatePart::LF)
            {
                2usize
            } else {
                3usize
            };
            if peq(self.0[idx], StatePart::SpPlus) {
                idx = idx - 1;
            }
            if peq(self.0[idx], StatePart::ClosePlus) {
                idx = idx - 1;
            }
            peq(self.0[idx], StatePart::STerm) || peq(self.0[idx], StatePart::ATerm)
        }
    }

    #[derive(Clone)]
    pub struct SentenceBreaks<'a> {
        pub string: &'a str,
        pub pos: usize,
        pub state: SentenceBreaksState,
    }

    /// Spec face of the upstream size_hint: it depends only on the full string
    /// length slen (the legal lower bound = min(slen,2)?? no -- upstream writes
    /// cmp::min(slen,2); the upper bound is slen+1).
    pub open spec fn size_hint_spec(slen: int) -> (usize, Option<usize>) {
        (if slen < 2 { slen as usize } else { 2 }, Some((slen + 1) as usize))
    }

    impl<'a> SentenceBreaks<'a> {
        /// VERBATIM mirror of upstream `Iterator::size_hint` (sentence.rs:177-181).
        /// Contract: the result depends only on the full-string byte length (not on the
        /// consumption cursor pos) -- the distortion face of formal finding F1: the hint
        /// at a consumed position does not shrink.
        pub fn size_hint_exec(&self) -> (r: (usize, Option<usize>))
            requires
                self.string.len() < usize::MAX,
            ensures
                r == size_hint_spec(self.string.len() as int),
        {
            let slen = self.string.len();
            (if slen < 2 { slen } else { 2usize }, Some(slen + 1))
        }
    }

    /// Ghost reference bridge: the spec model of `x.size_hint_exec()` in a spec/
    /// proof context (the value == size_hint_spec(full-string byte length),
    /// equivalent to that exec fn's ensures).
    pub open spec fn size_hint_of(it: &SentenceBreaks<'_>) -> (usize, Option<usize>) {
        size_hint_spec(it.string.len() as int)
    }

    impl View for SentenceBreaks<'_> {
        type V = (Seq<char>, usize, SentenceBreaksState);

        open spec fn view(&self) -> (Seq<char>, usize, SentenceBreaksState) {
            (self.string@, self.pos, self.state)
        }
    }
    // =======================================================================
    // Proof lemma (moved to the end of the module; only the order changed)
    // =======================================================================
    /// F1 formal witness (one step): size_hint is completely independent of the
    /// consumption cursor pos. Take any two instances on the same string, at
    /// arbitrary pos each: their hints are equal -- the consumed prefix never
    /// affects the hint. This contradicts the lower-bound semantics of
    /// std::iter::Iterator::size_hint ("bounds on the REMAINING length"); the
    /// behavior-side re-confirmation is at out/poc/sentence-size-hint-stale.
    ///
    /// Input side: a, b are **any** two consumption phases (fresh or any pos) of
    /// SentenceBreaks instances on the same string. Conclusion: their size_hints
    /// are equal (by the size_hint_exec ensures: the value == size_hint_spec of
    /// the full-string length).
    pub proof fn lemma_size_hint_ignores_pos(a: &SentenceBreaks<'_>, b: &SentenceBreaks<'_>)
        requires
            a.string == b.string,
            a.string.len() < usize::MAX,
        ensures
            size_hint_spec(a.string.len() as int) == size_hint_spec(b.string.len() as int),
    {
        assert(a.string == b.string);
        assert(a.string.len() == b.string.len());
    }

}

fn main() {}

}
