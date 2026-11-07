//! `word.rs` library mirror -- formal verification deliverable
//!
//! Upstream: code/src/word.rs (pin e445e101b129862148127c9e41ab4486b0125232, tree untouched)
//!
//! The obligation face of this file (this round's **main verification target**):
//! - `AsciiWordBoundIter` (upstream lines 751-940; the upstream enables this path
//!   only when `s.is_ascii()`): **full verification** of the forward `next()` and
//!   backward `next_back()` byte-level algorithms, aligned step by step with the
//!   spec models of the UAX#29 ASCII subset (WB3 CRLF, WB3d whitespace runs,
//!   WB5-WB13b core-run + infix joining, WB999 single-byte segments):
//!   - exec `fn next` is equivalent to spec `wb_next_break(b, i)` call by call;
//!   - exec `fn next_back` is equivalent to spec `wb_prev_break(b, i)` call by call;
//!   - universal properties: `wb_next_break`/`wb_prev_break` never go out of
//!     bounds and always advance strictly;
//!   - the doc contract (lib.rs:166 "The concatenation of the substrings returned
//!     by this function is just the original string.") is fully proved on the
//!     tokens model (`lemma_tokens_concat_identity`).
//!
//! Mirror and relaxation ledger:
//! 1. relax: `rest: &'a str` -> `rest: &'a [u8]`. The upstream constructs this
//!    iterator only inside its `s.is_ascii()` branch (word.rs:973), so for an ASCII
//!    string the UTF-8 bytes correspond one-to-one with the characters and the
//!    byte-level model is lossless.
//! 2. `UWordBounds` (the Unicode-path state machine, from word.rs:215),
//!    `WordsIter`/`IndicesIter` and the std `Filter/Map` adapters: blocked this
//!    round (SMT state-machine scale + Filter extent); the verbatim bodies stay
//!    un-transcribed; the obligation face is carried jointly by (a) the full ASCII
//!    fast-path verification, (b) the `size_hint` contract, (c) the runtime face of
//!    the upstream proptests -- see out/bug-finder-summary.md.
//! 3. The `word_category` lookup: carried by the tables mirror axiom layer
//!    (AX-w1/w2).

use vstd::prelude::*;
use vstd::prelude::SpecOrd;
use vstd::slice::slice_subrange;

verus! {

broadcast use vstd::seq::group_seq_lemmas;

/// ASCII alphabetic (the ASCII subset of ALetter, per the upstream doc table word.rs:758-771).
pub open spec fn is_alpha_b(b: u8) -> bool {
    (0x41 <= b <= 0x5A) || (0x61 <= b <= 0x7A)
}

/// ASCII digit (Numeric).
pub open spec fn is_digit_b(b: u8) -> bool {
    0x30 <= b <= 0x39
}

/// core-run member bytes: letters/digits/underscore (ALetter | Numeric | ExtendNumLet).
pub open spec fn is_core_b(b: u8) -> bool {
    is_alpha_b(b) || is_digit_b(b) || b == 0x5F
}

/// Verbatim mirror of the upstream `is_infix` (word.rs:793-808): the numeric
/// separators of WB11/WB12 and the alphabetic separators of WB6/WB7
/// (MidLetter/MidNumLetQ).
pub open spec fn is_infix_b(b: u8, prev: u8, next: u8) -> bool {
    ((b == 0x2E || b == 0x2C || b == 0x3B || b == 0x27) && is_digit_b(prev) && is_digit_b(next))
        || ((b == 0x27 || b == 0x2E || b == 0x3A) && is_alpha_b(prev) && is_alpha_b(next))
}

/// Whether probe p is absorbed into the token (the continue condition of the while
/// loop at upstream lines 815-876): core bytes are absorbed directly; infix bytes
/// require both neighbors to match (WB11/12 numeric separators, WB6/7 alphabetic
/// separators).
pub open spec fn taken_fwd(b: Seq<u8>, p: int) -> bool {
    is_core_b(b[p])
        || (p >= 1 && p + 1 < b.len() as int && is_infix_b(b[p], b[p - 1], b[p + 1]))
}

/// The chain end of the core-run (the token's right end, exclusive). x is the
/// "rightmost absorbed byte"; the probe is x+1.
/// A single recursion (core and infix probes uniformly judged by taken_fwd),
/// mirroring the upstream loop's continue/break.
pub open spec fn fwd_chain_end(b: Seq<u8>, x: int) -> int
    decreases b.len() - x,
{
    let n = b.len() as int;
    if !(0 <= x < n) {
        x // degenerate value outside the precondition
    } else if x + 1 >= n {
        n
    } else if taken_fwd(b, x + 1) {
        fwd_chain_end(b, x + 1)
    } else {
        x + 1
    }
}

/// Forward break model of the ASCII path: returns the next boundary **strictly
/// greater than i**.
/// WB3d: whitespace run; WB5-13b: core-run(+infix); WB3: CRLF; WB999: single byte.
pub open spec fn wb_next_break(b: Seq<u8>, i: int) -> int
    decreases b.len() - i,
{
    let n = b.len() as int;
    if !(0 <= i <= n) {
        i // degenerate value outside the precondition
    } else if i >= n {
        n
    } else if b[i] == 0x20 {
        if i + 1 < n && b[i + 1] == 0x20 {
            wb_next_break(b, i + 1)
        } else {
            i + 1
        }
    } else if is_core_b(b[i]) {
        fwd_chain_end(b, i)
    } else if b[i] == 0x0D && i + 1 < n && b[i + 1] == 0x0A {
        i + 2
    } else {
        i + 1
    }
}

/// Backward break model of the ASCII path: returns the boundary **strictly
/// smaller than i**.
/// Mirror of next_back (upstream lines 879-940).
pub open spec fn wb_prev_break(b: Seq<u8>, i: int) -> int
    decreases i,
{
    let n = b.len() as int;
    if !(0 <= i <= n) {
        0 // degenerate value outside the precondition
    } else if i <= 0 {
        0
    } else if b[i - 1] == 0x20 {
        if i >= 2 && b[i - 2] == 0x20 {
            wb_prev_break(b, i - 1)
        } else {
            i - 1
        }
    } else if is_core_b(b[i - 1]) {
        back_chain_start(b, i - 1)
    } else if i >= 2 && b[i - 2] == 0x0D && b[i - 1] == 0x0A {
        i - 2
    } else {
        i - 1
    }
}

/// Whether the backward probe z is absorbed into the token (the loop condition at
/// upstream lines 901-920): core is absorbed directly; infix requires the prev
/// (the left neighbor of z; for z==0 the upstream approximates with the probe
/// itself) and next to match.
pub open spec fn taken_back(b: Seq<u8>, z: int) -> bool {
    is_core_b(b[z])
        || (z + 1 < b.len() as int
            && is_infix_b(b[z], if z >= 1 { b[z - 1] } else { b[z] }, b[z + 1]))
}

/// The start of a backward core-run chain. x is the "leftmost absorbed byte";
/// the probe is x-1.
pub open spec fn back_chain_start(b: Seq<u8>, x: int) -> int
    decreases x,
{
    let n = b.len() as int;
    if !(0 <= x < n) {
        x // degenerate value outside the precondition
    } else if x == 0 {
        0
    } else if taken_back(b, x - 1) {
        back_chain_start(b, x - 1)
    } else {
        x
    }
}

/* ---------- tokens model and doc contract ---------- */

pub open spec fn seq_concat(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    a.add(b)
}

/// Full concatenation of a token sequence.
pub open spec fn concat_all(ts: Seq<Seq<u8>>) -> Seq<u8>
    decreases ts.len(),
{
    if ts.len() == 0 {
        Seq::empty()
    } else {
        seq_concat(ts[0], concat_all(ts.subrange(1, ts.len() as int)))
    }
}

/// Forward tokens model of the whole string (recursive).
pub open spec fn wb_tokens(b: Seq<u8>) -> Seq<Seq<u8>>
    decreases b.len(),
{
    if b.len() == 0 {
        Seq::empty()
    } else {
        let k = wb_next_break(b, 0);
        if k <= 0 || k > b.len() as int {
            Seq::empty() // by lemma_wb_next_break_progress, 0<k<=len holds for a non-empty b, so this branch is never taken
        } else {
            (seq![b.subrange(0, k)]).add(wb_tokens(b.subrange(k, b.len() as int)))
        }
    }
}

/* ---------- exec mirror: the ASCII fast-path iterator ---------- */

/// Origin Rust: `struct AsciiWordBoundIter<'a> { rest: &'a str, offset: usize }`
/// Relax ledger item 1: rest changed from &str to &[u8] (the upstream uses this path
/// only for is_ascii inputs).
/// Upstream doc (word.rs:751-775):
///   ASCII-fast-path word-boundary iterator for strings that contain only ASCII characters.
///   Since we handle only ASCII characters, we can use a much simpler set of
///   word break values than the full Unicode algorithm.
///   https://www.unicode.org/reports/tr29/#Table_Word_Break_Property_Values
///   | Word_Break value | ASCII code points that belong to it                             |
///   | -----------------| --------------------------------------------------------------- |
///   | CR               | U+000D (CR)                                                     |
///   | LF               | U+000A (LF)                                                     |
///   | Newline          | U+000B (VT), U+000C (FF)                                        |
///   | Single_Quote     | U+0027 (')                                                      |
///   | Double_Quote     | U+0022 (")                                                      |
///   | MidNumLet        | U+002E (.) FULL STOP                                            |
///   | MidLetter        | U+003A (:) COLON                                                |
///   | MidNum           | U+002C (,), U+003B (;)                                          |
///   | Numeric          | U+0030 - U+0039 (0 ... 9)                                         |
///   | ALetter          | U+0041 - U+005A (A ... Z), U+0061 - U+007A (a ... z)                |
///   | ExtendNumLet     | U+005F (_) underscore                                           |
///   | WSegSpace        | U+0020 (SPACE)                                                  |
///   The macro MidNumLetQ boils down to: U+002E (.) FULL STOP and U+0027 (')
///   AHLetter is the same as ALetter, so we don't need to distinguish it.
///   Any other single ASCII byte is its own boundary (the default WB999).
pub struct AsciiWordBoundIter<'a> {
    pub rest: &'a [u8],
    pub offset: usize,
}

impl<'a> AsciiWordBoundIter<'a> {
    /// Origin Rust: `AsciiWordBoundIter::new` (word.rs:782-785).
    pub fn new(s: &'a [u8]) -> (it: AsciiWordBoundIter<'a>)
        ensures
            it.rest@ == s@,
            it.offset == 0,
    {
        AsciiWordBoundIter { rest: s, offset: 0 }
    }

    /// Origin Rust: word.rs:815-876 `fn next` (the forward main algorithm).
    pub fn next(&mut self) -> (r: Option<(usize, &'a [u8])>)
        requires
            old(self).offset + (old(self).rest@.len() as usize) <= usize::MAX,
        ensures
            match r {
                None => {
                    &&& old(self).rest.len() == 0
                    &&& final(self).rest.len() == 0
                    &&& final(self).offset == old(self).offset
                }
                Some((pos, word)) => {
                    let k = wb_next_break(old(self).rest@, 0);
                    &&& old(self).rest.len() > 0
                    &&& pos == old(self).offset
                    &&& word.view().len() == k
                    &&& word@ == old(self).rest@.subrange(0, k)
                    &&& 0 < k <= old(self).rest.len()
                    &&& final(self).rest@ == old(self).rest@.subrange(k, old(self).rest.len() as int)
                    &&& final(self).offset == old(self).offset + (k as usize)
                    &&& final(self).rest@.len() == old(self).rest@.len() - k
                    &&& final(self).offset + (final(self).rest@.len() as usize) <= usize::MAX
                }
            },
    {
        if self.rest.len() == 0 {
            return None;
        }
        let b = self.rest;
        let len = b.len();
        let k = Self::scan_next(b);
        let pos = self.offset;
        assert(self.rest@ == b@);
        self.rest = slice_subrange(b, k, len);
        self.offset += k;
        Some((pos, slice_subrange(b, 0, k)))
    }

    /// Forward single step: returns the relative break k (word = rest[0..k]);
    /// equivalence with spec `wb_next_break(rest@, 0)` is this function's obligation.
    fn scan_next(b: &[u8]) -> (k: usize)
        requires
            b.len() > 0,
        ensures
            0 < k <= b.len(),
            k as int == wb_next_break(b@, 0),
    {
        let b0 = b[0];
        if b0 == 0x20 {
            // 1) WB3d whitespace run
            let mut i: usize = 1;
            while i < b.len() && b[i] == 0x20
                invariant
                    1 <= i <= b.len(),
                    b.len() == b@.len(),
                    forall|j: int| 0 <= j < i ==> b[j as int] == 0x20,
                decreases b.len() - i,
            {
                i += 1;
            }
            assert(i == b.len() || b[i as int] != 0x20);
            proof {
                assert(i > 0);
                space_chain(b@, 0, i as int);
            }
            assert(wb_next_break(b@, 0) == i);
            i
        } else if is_core_exec(b0) {
            // 2) core-run (incl. infix joining)
            let mut i: usize = 1;
            while i < b.len()
                && (is_core_exec(b[i])
                    || (i + 1 < b.len() && is_infix_exec(b[i], b[i - 1], b[i + 1])))
                invariant
                    1 <= i <= b.len(),
                    b.len() == b@.len(),
                    fwd_chain_end(b@, (i - 1) as int) == fwd_chain_end(b@, 0),
                decreases b.len() - i,
            {
                assert(fwd_chain_end(b@, (i - 1) as int) == fwd_chain_end(b@, i as int));
                i += 1;
            }
            assert(
                i == b.len()
                    || !taken_fwd(b@, i as int)
            );
            assert(
                i == b.len() && (i - 1) as int + 1 >= b@.len() as int
                    || i < b.len() && !taken_fwd(b@, i as int)
            );
            assert(
                fwd_chain_end(b@, (i - 1) as int)
                    == (if i == b.len() { b@.len() as int } else { i as int })
            );
            assert(fwd_chain_end(b@, 0) == i);
            i
        } else if b0 == 0x0D && 1 < b.len() && b[1] == 0x0A {
            // 3) WB3: CR x LF
            assert(wb_next_break(b@, 0) == 2);
            2
        } else {
            // 4) WB999
            assert(wb_next_break(b@, 0) == 1);
            1
        }
    }

    /// Origin Rust: word.rs:879-940 `fn next_back`.
    pub fn next_back(&mut self) -> (r: Option<(usize, &'a [u8])>)
        requires
            old(self).offset + (old(self).rest@.len() as usize) <= usize::MAX,
        ensures
            match r {
                None => {
                    &&& old(self).rest.len() == 0
                    &&& final(self).rest@ == old(self).rest@
                    &&& final(self).offset == old(self).offset
                }
                Some((pos, word)) => {
                    let k = wb_prev_break(old(self).rest@, old(self).rest.len() as int);
                    &&& old(self).rest.len() > 0
                    &&& 0 <= k < old(self).rest.len()
                    &&& word@ == old(self).rest@.subrange(k, old(self).rest.len() as int)
                    &&& pos == old(self).offset + (k as usize)
                    &&& final(self).rest@ == old(self).rest@.subrange(0, k)
                    &&& final(self).offset == old(self).offset
                    &&& final(self).rest@.len() == k
                    &&& final(self).offset + (final(self).rest@.len() as usize) <= usize::MAX
                }
            },
    {
        if self.rest.len() == 0 {
            return None;
        }
        let b = self.rest;
        let len = b.len();
        let start = Self::scan_back(b);
        let pos = self.offset + start;
        self.rest = slice_subrange(b, 0, start);
        Some((pos, slice_subrange(b, start, len)))
    }

    /// Backward single step: returns the token start start (word = rest[start..len]).
    fn scan_back(b: &[u8]) -> (s: usize)
        requires
            b.len() > 0,
        ensures
            0 <= s < b.len(),
            s as int == wb_prev_break(b@, b.len() as int),
    {
        let len = b.len();
        if b[len - 1] == 0x20 {
            // 1) WB3d trailing space run
            let mut start: usize = len - 1;
            if start > 0 {
                while start > 0 && b[start - 1] == 0x20
                    invariant
                        0 <= start <= len - 1,
                        len == b@.len(),
                        forall|j: int| (start as int) <= j < len ==> b[j as int] == 0x20,
                    decreases start,
                {
                    start -= 1;
                }
                assert(start == 0 || b[(start - 1) as int] != 0x20);
            }
            proof {
                back_space_chain(b@, len as int, start as int);
            }
            assert(wb_prev_break(b@, len as int) == start as int);
            start
        } else if is_core_exec(b[len - 1]) {
            // 2) trailing core-run (incl. infix joining)
            let mut start: usize = len - 1;
            if start > 0 {
                while start > 0
                    && back_loop_cond(b, start)
                    invariant
                        0 <= start <= len - 1,
                        len == b@.len(),
                        back_chain_start(b@, (start as int))
                            == back_chain_start(b@, (len - 1) as int),
                    decreases start,
                {
                    assert(taken_back(b@, (start - 1) as int));
                    assert(
                        back_chain_start(b@, start as int)
                            == back_chain_start(b@, (start - 1) as int)
                    );
                    start -= 1;
                }
                assert(
                    start == 0
                        || !(is_core_b(b[(start - 1) as int])
                            || (taken_back_infix(b@, (start - 1) as int)))
                );
            }
            assert(wb_prev_break(b@, len as int) == (start as int));
            start
        } else if len >= 2 && b[len - 2] == 0x0D && b[len - 1] == 0x0A {
            // 3) trailing CRLF
            assert(wb_prev_break(b@, len as int) == (len - 2) as int);
            len - 2
        } else {
            // 4) WB999
            assert(wb_prev_break(b@, len as int) == (len - 1) as int);
            len - 1
        }
    }
}

/// next_back's loop condition (the exec face of the same judgment as taken_back).
pub fn back_loop_cond(b: &[u8], start: usize) -> (r: bool)
    requires
        0 < start < b.len(),
        b@.len() == b.len(),
    ensures
        r == taken_back(b@, (start - 1) as int),
{
    let x = b[start - 1];
    let prev = if start >= 2 { b[start - 2] } else { x };
    if is_core_exec(x) {
        assert(is_core_b(x));
        assert(taken_back(b@, (start - 1) as int));
        true
    } else {
        let nxt: u8 = b[start];
        if start >= 2 {
            assert(is_infix_b(x, prev, nxt) == taken_back_infix(b@, (start - 1) as int));
        } else {
            assert(is_infix_b(x, prev, nxt) == taken_back_infix(b@, (start - 1) as int));
        }
        let r = is_infix_exec(x, prev, b[start]);
        assert(taken_back(b@, (start - 1) as int) == r);
        r
    }
}

/// The infix disjunct of taken_back (the same proposition minus the core disjunct).
pub open spec fn taken_back_infix(b: Seq<u8>, z: int) -> bool {
    z + 1 < b.len() as int
        && is_infix_b(b[z], if z >= 1 { b[z - 1] } else { b[z] }, b[z + 1])
}

/// Origin Rust: word.rs:787-790 `fn is_core(b: u8)`
/// (equivalent-range transcription of the std `u8::is_ascii_*` predicates, no
/// external relax).
fn is_core_exec(b: u8) -> (r: bool)
    ensures
        r == is_core_b(b),
{
    is_alpha_exec(b) || is_digit_exec(b) || b == 0x5F
}

/// Origin Rust: equivalent transcription of std `u8::is_ascii_alphabetic`.
fn is_alpha_exec(b: u8) -> (r: bool)
    ensures
        r == is_alpha_b(b),
{
    (b >= 0x41 && b <= 0x5A) || (b >= 0x61 && b <= 0x7A)
}

/// Origin Rust: equivalent transcription of std `u8::is_ascii_digit`.
fn is_digit_exec(b: u8) -> (r: bool)
    ensures
        r == is_digit_b(b),
{
    b >= 0x30 && b <= 0x39
}

/// Origin Rust: word.rs:793-812 `fn is_infix(b, prev, next)`.
fn is_infix_exec(b: u8, prev: u8, next: u8) -> (r: bool)
    ensures
        r == is_infix_b(b, prev, next),
{
    let digitsep = (b == 0x2E || b == 0x2C || b == 0x3B || b == 0x27)
        && is_digit_exec(prev)
        && is_digit_exec(next);
    let alphasep = (b == 0x27 || b == 0x2E || b == 0x3A)
        && is_alpha_exec(prev)
        && is_alpha_exec(next);
    digitsep || alphasep
}

// ===========================================================================
// Proof lemmas (moved to the end of the file; only the order changed).
// ===========================================================================
/* ---------- common properties (model-health lemmas, all proved) ---------- */

pub proof fn lemma_fwd_chain_end_progress(b: Seq<u8>, x: int)
    requires
        0 <= x < b.len(),
    ensures
        x < fwd_chain_end(b, x) <= b.len(),
    decreases b.len() - x,
{
    let n = b.len() as int;
    if x + 1 >= n {
        assert(fwd_chain_end(b, x) == n);
    } else if taken_fwd(b, x + 1) {
        lemma_fwd_chain_end_progress(b, x + 1);
    } else {
        assert(fwd_chain_end(b, x) == x + 1);
    }
}

pub proof fn lemma_wb_next_break_progress(b: Seq<u8>, i: int)
    requires
        0 <= i <= b.len(),
    ensures
        i < b.len() ==> i < wb_next_break(b, i) <= b.len(),
        i == b.len() ==> wb_next_break(b, i) == b.len(),
    decreases b.len() - i,
{
    let n = b.len() as int;
    if i < n {
        if b[i] == 0x20 && i + 1 < n && b[i + 1] == 0x20 {
            lemma_wb_next_break_progress(b, i + 1);
        } else if is_core_b(b[i]) {
            lemma_fwd_chain_end_progress(b, i);
        }
    }
}

pub proof fn lemma_back_chain_start_progress(b: Seq<u8>, x: int)
    requires
        0 <= x < b.len(),
    ensures
        0 <= back_chain_start(b, x) <= x,
    decreases x,
{
    if x > 0 {
        if taken_back(b, x - 1) {
            lemma_back_chain_start_progress(b, x - 1);
        }
    }
}

pub proof fn lemma_wb_prev_break_progress(b: Seq<u8>, i: int)
    requires
        0 <= i <= b.len(),
    ensures
        i > 0 ==> 0 <= wb_prev_break(b, i) < i,
        i == 0 ==> wb_prev_break(b, i) == 0,
    decreases i,
{
    if i > 0 {
        if b[i - 1] == 0x20 && i >= 2 && b[i - 2] == 0x20 {
            lemma_wb_prev_break_progress(b, i - 1);
        } else if is_core_b(b[i - 1]) {
            lemma_back_chain_start_progress(b, i - 1);
        }
    }
}

/// The token of an all-whitespace string is exactly the whole string (WB3d).
pub proof fn lemma_space_token_shape(b: Seq<u8>)
    requires
        b.len() > 0,
        forall|j: int| 0 <= j < b.len() ==> b[j] == 0x20,
    ensures
        wb_next_break(b, 0) == b.len(),
{
    induction_space(b, 0);
}

/// Whitespace-run chain lemma: when b[j..i] is all spaces and the endpoint
/// property holds, wb_next_break(b, j) == i.
proof fn space_chain(b: Seq<u8>, j: int, i: int)
    requires
        0 <= j < i <= b.len(),
        forall|t: int| j <= t < i ==> b[t] == 0x20,
        i < b.len() ==> b[i as int] != 0x20,
    ensures
        wb_next_break(b, j) == i,
    decreases i - j,
{
    assert(b[j] == 0x20);
    if j + 1 < i {
        assert(b[j + 1] == 0x20);
        space_chain(b, j + 1, i);
        assert(wb_next_break(b, j) == wb_next_break(b, j + 1));
    } else {
        // j + 1 == i
        if i < b.len() {
            assert(b[i as int] != 0x20);
        }
        assert(wb_next_break(b, j) == j + 1);
        assert(j + 1 == i);
    }
}

/// Backward whitespace-run chain: when b[m..i) is all spaces and (m == 0 or
/// b[m-1] is not a space), wb_prev_break(b, i) == m.
proof fn back_space_chain(b: Seq<u8>, i: int, m: int)
    requires
        0 <= m < i <= b.len(),
        forall|t: int| m <= t < i ==> b[t] == 0x20,
        m == 0 || b[m - 1] != 0x20,
    ensures
        wb_prev_break(b, i) == m,
    decreases i - m,
{
    assert(b[i - 1] == 0x20);
    if i - 1 > m {
        assert(i >= 2);
        assert(b[i - 2] == 0x20);
        back_space_chain(b, i - 1, m);
        assert(wb_prev_break(b, i) == wb_prev_break(b, i - 1));
    } else {
        // i - 1 == m
        if m >= 1 {
            assert(b[m - 1] != 0x20);
        }
        assert(wb_prev_break(b, i) == i - 1);
        assert(i - 1 == m);
    }
}

proof fn induction_space(b: Seq<u8>, i: int)
    requires
        0 <= i < b.len(),
        forall|j: int| i <= j < b.len() ==> b[j] == 0x20,
    ensures
        wb_next_break(b, i) == b.len(),
    decreases b.len() - i,
{
    if i + 1 < b.len() {
        induction_space(b, i + 1);
    }
}

/// The doc contract (lib.rs:166 split_word_bounds: "The concatenation of the
/// substrings returned by this function is just the original string.") proven
/// by universal induction on the ASCII fast-path tokens model.
pub proof fn lemma_tokens_concat_identity(b: Seq<u8>)
    ensures
        concat_all(wb_tokens(b)) == b,
    decreases b.len(),
{
    if b.len() == 0 {
        assert(wb_tokens(b) =~= Seq::empty());
        assert(concat_all(Seq::<Seq<u8>>::empty()) =~= Seq::empty());
        assert(concat_all(wb_tokens(b)) =~= Seq::empty());
        assert(b =~= Seq::empty());
        assert(concat_all(wb_tokens(b)) =~= b);
    } else {
        lemma_wb_next_break_progress(b, 0);
        let k = wb_next_break(b, 0);
        let head = b.subrange(0, k);
        let rest = b.subrange(k, b.len() as int);
        assert(rest.len() == b.len() - k);
        assert(b == head.add(rest));
        assert(rest.len() > 0 || k == b.len());
        if rest.len() > 0 {
            lemma_tokens_concat_identity(rest);
        }
        let ts = wb_tokens(b);
        assert(ts.len() == 1 + wb_tokens(rest).len());
        assert(ts[0] == head);
        assert(ts.subrange(1, ts.len() as int) == wb_tokens(rest));
        let tail = concat_all(wb_tokens(rest));
        assert(concat_all(ts.subrange(1, ts.len() as int)) == tail);
        assert(concat_all(ts) == head.add(tail));
        assert(concat_all(ts) == head.add(concat_all(wb_tokens(rest))));
        assert(ts == (seq![head]).add(wb_tokens(rest)));
        assert(head.add(rest) =~= b);
    }
}

}

fn main() {}
