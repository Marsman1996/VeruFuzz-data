//! strsim 0.11.1 x Verus -- the `verified/src/`
//! verification tree.
//!
//! Upstream (the verification target, unmodified): `database/strsim/code/src/lib.rs`;
//!   repo  = https://github.com/rapidfuzz/strsim-rs
//!   pin   = dacc84c0dc61eff0ee0ff66962bcf2e17018ad26 (fetch.conf COMMIT)
//!
//! # Base-transcription notes (the KVerus migrate-level Origin annotation master key)
//!
//! The upstream takes generic iterators (`&Iter: IntoIterator` / `&str::chars()`)
//! as the input base, including std structures beyond the Verus compilation
//! domain (`StringWrapper`, the `Chars` iterator, `HashMap` counters). This
//! tree mirrors each function under the **base mappings** below, preserving
//! the algorithm bodies (loop structure, branches, arithmetic, comparison
//! order) line by line:
//!
//! | Upstream structure | Verification-tree base | Rationale |
//! | --- | --- | --- |
//! | `IntoIterator` element streams (count / multi-pass agreement of the main loops) | `&[char]` fixed-length sequences (`.len()`/`seq[i]`) | iterator multi-pass consistency relies on implicit std contracts; the slice base turns that contract into a type fact. `&str`-to-`Vec<char>` equivalence is defined by the per-character semantics of `chars()` |
//! | `HashMap<K, usize>` counters / most-recent row ids | assoc lists `Vec<(K, usize)>` (lookup = linear first match; insert = remove-then-add) | with Eq an equivalence relation (std doc guarantee) this matches the `HashMap` semantics of "unique keys + get returns the most recently inserted value"; the numeric behavior does not depend on the table structure |
//! | `f64` similarity arithmetic | keep f64 exec (Verus has no f64 SMT semantics) | only panic-free is promised (f64 ops enter no overflow obligations); the floating-point expected-value layer goes through runtime re-verification (out/verus-bugfinder) |
//!
//! The upstream `&str` wrapper layer (`hamming(&str)` etc. = immediate forward to the chars core)
//! converges to the same parameter shape (`&[char]`) in this tree; it is not an independent semantic site.
//!
//! # Verification-depth ledger per public API (machine-checked verification basis)
//!
//! | API | Depth |
//! | --- | --- |
//! | generic_hamming / hamming | full functional contract (the diff_count inductive spec twin + contract theorems) |
//! | generic_levenshtein / levenshtein | L0 panic-free + value-range bounds + empty-input exactness |
//! | osa_distance | L0 panic-free + value-range upper bound |
//! | generic_damerau_levenshtein | L0 + empty-input exactness + value-range upper bound (flat three-segment blanket, assault batch) |
//! | damerau_levenshtein(_impl) | L0 + empty-input exactness + value-range upper bound (the Zhao-Sahni row-phase blanket, assault batch) |
//! | generic_jaro / jaro / generic_jaro_winkler / jaro_winkler | L0 panic-free (usize side) |
//! | normalized_levenshtein | L0 panic-free (usize-side parameter contracts) |
//! | normalized_damerau_levenshtein | L0 panic-free (usize-side parameter contracts, assault batch) |
//! | sorensen_dice | L0 panic-free + multiset total-sum invariant (whitespace-filtered byte-length base, assault batch) |
//!
//! The f64 full-functional layer is a base-domain exclusion (Verus has no floating-point SMT backend) and is out of obligation by default -- UT expected values
//! are covered by runtime re-verification discipline.

#![forbid(unsafe_code)]

use vstd::prelude::*;
use vstd::seq::Seq;

verus! {

/* =====================================================================
 * Types and errors (mirror of lib.rs:32-49)
 * ===================================================================== */

/// Origin Rust: `pub enum StrSimError { DifferentLengthArgs }` (lib.rs:32);
/// the upstream `Display`/`Error` impl (lib.rs:37-47) is an fmt forwarder with no
/// algorithm site (outside the base mapping; this tree keeps the enum body and a mirrored PartialEq).
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum StrSimError {
    DifferentLengthArgs,
}

/// Origin Rust: `pub type HammingResult = Result<usize, StrSimError>;` (lib.rs:49)
pub type HammingResult = Result<usize, StrSimError>;

/* =====================================================================
 * spec twins (KVerus spec layer)
 * ===================================================================== */

/// Count of the positions where `a` and `b` differ over the first i positions (the hamming semantic twin).
pub open spec fn diff_count(a: Seq<char>, b: Seq<char>, i: int) -> nat
    decreases i,
{
    if i <= 0 {
        0nat
    } else {
        diff_count(a, b, i - 1) + (if a.index(i - 1) != b.index(i - 1) {
            1nat
        } else {
            0nat
        })
    }
}


/* =====================================================================
 * generic_hamming / hamming (mirror of lib.rs:53-86)
 * ===================================================================== */

/// Origin Rust: `pub fn generic_hamming<...>(a: Iter1, b: Iter2) -> HammingResult`
/// (lib.rs:53-72). The iterator `(ita.next(), itb.next())` paired loop is mirrored
/// as a two-index advance.
/// Upstream doc (lib.rs:51-52):
///   Calculates the number of positions in the two sequences where the elements
///   differ. Returns an error if the sequences have different lengths.
pub fn generic_hamming(a: &[char], b: &[char]) -> (r: HammingResult)
    ensures
        r.is_ok() <==> a@.len() == b@.len(),
        r.is_ok() ==> r.unwrap() == diff_count(a@, b@, (a@.len()) as int) as usize,
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    while i < a.len() && i < b.len()
        invariant
            i <= a.len(),
            i <= b.len(),
            count == diff_count(a@, b@, i as int) as usize,
            count <= i,
            a@.len() == a.len(),
            b@.len() == b.len(),
        decreases a.len() + b.len() - i,
    {
        if a[i] != b[i] {
            count = count + 1;
        }
        i = i + 1;
        proof {
            diff_count_step(a@, b@, (i - 1) as int);
            diff_count_le(a@, b@, i as int);
        }
    }
    if a.len() == b.len() {
        proof {
            assert(a@.len() == i as int) by {
                assert(a@.len() == a.len());
                assert(i == a.len());
            }
        }
        Ok(count)
    } else {
        Err(StrSimError::DifferentLengthArgs)
    }
}

/// Origin Rust: `pub fn hamming(a: &str, b: &str) -> HammingResult`
/// (lib.rs:84-86, forwarding `generic_hamming(a.chars(), b.chars())`).
/// Upstream doc (lib.rs:74-83):
///   Calculates the number of positions in the two strings where the characters
///   differ. Returns an error if the strings have different lengths.
///   use strsim::{hamming, StrSimError::DifferentLengthArgs};
///   assert_eq!(Ok(3), hamming("hamming", "hammers"));
///   assert_eq!(Err(DifferentLengthArgs), hamming("hamming", "ham"));
pub fn hamming(a: &[char], b: &[char]) -> (r: HammingResult)
    ensures
        r.is_ok() <==> a@.len() == b@.len(),
        r.is_ok() ==> r.unwrap() == diff_count(a@, b@, (a@.len()) as int) as usize,
{
    generic_hamming(a, b)
}

/* =====================================================================
 * generic_jaro / jaro (mirror of lib.rs:90-184) -- L0 on the usize side
 * ===================================================================== */

/// Input-memory precondition: an upper bound on the sum of the two lengths (implicit upstream via memory
/// assumptions; the upstream `i + search_range + 1` (lib.rs:118) can overflow usize for inputs of magnitude 2^63; made explicit here as a precondition --
/// the 2*(a+b)+8 tier covers the `max/2`-magnitude growth).
pub open spec fn jaro_len_precond(a_len: int, b_len: int) -> bool {
    2 * a_len + 2 * b_len + 8 <= usize::MAX as int
}

/// Count of the true slots inside one flags segment (the spec primitive of the jaro pairing invariant).
pub open spec fn flag_count(flags: Seq<bool>, lo: int, hi: int) -> nat
    decreases hi - lo,
{
    if hi <= lo {
        0nat
    } else {
        flag_count(flags, lo, hi - 1) + (if flags.index(hi - 1) {
            1nat
        } else {
            0nat
        })
    }
}

/* Kept in place (spec-2 exception, documented): the flag_count lemma
 * family stays at its original position. The inner-loop query of
 * generic_damerau_levenshtein sits at the Z3 rlimit margin, and
 * relocating this family after the exec fns measuredly and
 * deterministically turns that marginal query into an rlimit error;
 * the outcome-neutral lemma families moved to the end of the file. */

proof fn flag_count_all_false(flags: Seq<bool>, lo: int, hi: int)
    requires
        forall|q: int| lo <= q < hi ==> flags.index(q) == false,
    ensures
        flag_count(flags, lo, hi) == 0,
    decreases hi - lo,
{
    if hi <= lo {
    } else {
        flag_count_all_false(flags, lo, hi - 1);
        reveal_with_fuel(flag_count, 2);
    }
}

/// Update slot p inside the interval (previously false) to true: the segment count grows by exactly +1.
proof fn flag_count_set_one(flags: Seq<bool>, lo: int, hi: int, p: int)
    requires
        0 <= lo,
        lo <= p,
        p < hi,
        hi <= flags.len(),
        flags.index(p) == false,
    ensures
        flag_count(flags.update(p, true), lo, hi) == flag_count(flags, lo, hi) + 1,
    decreases hi - lo,
{
    if p == hi - 1 {
        // The prefix [lo, hi-1) does not contain p (p == hi-1 is beyond its upper end)
        flag_count_update_at_or_beyond(flags, lo, hi - 1, p);
        vstd::seq::lemma_seq_update_same(flags, p, true);
        assert(flags.update(p, true)[p] == true);
        reveal_with_fuel(flag_count, 2);
    } else {
        flag_count_set_one(flags, lo, hi - 1, p);
        vstd::seq::lemma_seq_update_same(flags, p, true);
        vstd::seq::lemma_seq_update_different(flags, hi - 1, p, true);
        assert(flags.update(p, true)[hi - 1] == flags[hi - 1]);
        reveal_with_fuel(flag_count, 2);
    }
}

/// Update at hi or beyond: the segment count is unchanged.
proof fn flag_count_update_at_or_beyond(
    flags: Seq<bool>,
    lo: int,
    hi: int,
    p: int,
)
    requires
        lo <= hi,
        hi <= p,
        p < flags.len(),
    ensures
        flag_count(flags.update(p, true), lo, hi) == flag_count(flags, lo, hi),
    decreases hi - lo,
{
    if hi <= lo {
    } else {
        flag_count_update_at_or_beyond(flags, lo, hi - 1, p);
        reveal_with_fuel(flag_count, 2);
    }
}

/// Update before lo: the segment count is unchanged.
proof fn flag_count_update_before(flags: Seq<bool>, lo: int, hi: int, p: int)
    requires
        p < lo,
        0 <= lo,
        lo <= hi,
        hi <= flags.len(),
    ensures
        flag_count(flags.update(p, true), lo, hi) == flag_count(flags, lo, hi),
    decreases hi - lo,
{
    if hi <= lo {
    } else {
        flag_count_update_before(flags, lo, hi - 1, p);
        reveal_with_fuel(flag_count, 2);
    }
}

proof fn flag_count_le_size(flags: Seq<bool>, lo: int, hi: int)
    requires
        lo <= hi,
        hi <= flags.len(),
    ensures
        flag_count(flags, lo, hi) <= (hi - lo) as nat,
    decreases hi - lo,
{
    if hi <= lo {
    } else {
        flag_count_le_size(flags, lo, hi - 1);
        reveal_with_fuel(flag_count, 2);
    }
}

proof fn flag_count_monotone(flags: Seq<bool>, lo: int, mid: int, hi: int)
    requires
        lo <= mid,
        mid <= hi,
    ensures
        flag_count(flags, lo, mid) <= flag_count(flags, lo, hi),
    decreases hi - mid,
{
    if mid == hi {
    } else {
        flag_count_monotone(flags, lo, mid, hi - 1);
        reveal_with_fuel(flag_count, 2);
    }
}

proof fn flag_count_extend_one(flags: Seq<bool>, lo: int, hi: int)
    requires
        lo <= hi,
        hi < flags.len(),
    ensures
        flag_count(flags, lo, hi + 1) == flag_count(flags, lo, hi)
            + (if flags.index(hi) { 1nat } else { 0nat }),
{
    reveal_with_fuel(flag_count, 2);
}

/// Origin Rust: `pub fn generic_jaro<...>(a, b) -> f64` (lib.rs:90-160).
/// The multi-pass `into_iter()` calls of the iterator are mirrored as fixed-length index loops; the
/// split_at_mut base of `b_flags/a_flags` becomes a shared-index Vec. f64 has no SMT semantics;
/// the usize-side L0 (indexing / overflow / subtraction no-underflow) is machine-checked via the flag_count pairing invariants.
/// Upstream doc (lib.rs:88-89):
///   Calculates the Jaro similarity between two sequences. The returned value
///   is between 0.0 and 1.0 (higher value means more similar).
pub fn generic_jaro(a: &[char], b: &[char]) -> (r: f64)
    requires
        jaro_len_precond(a.len() as int, b.len() as int),
{
    let a_len = a.len();
    let b_len = b.len();

    if a_len == 0 && b_len == 0 {
        return 1.0;
    } else if a_len == 0 || b_len == 0 {
        return 0.0;
    }

    // Origin Rust: `let mut search_range = max(a_len, b_len) / 2;
    //               search_range = search_range.saturating_sub(1);` (lib.rs:105-106)
    // (saturating_sub clamps to 0 when maxlen <= 1; the two-value expansion preserves semantics)
    let maxlen = if a_len >= b_len { a_len } else { b_len };
    assert(maxlen <= a_len + b_len);
    let search_range0 = maxlen / 2;
    assert(search_range0 <= maxlen);
    let search_range = if search_range0 >= 1 { search_range0 - 1 } else { 0 };
    assert(search_range <= search_range0);
    assert(search_range <= maxlen);

    // Origin Rust: `let mut flags_memory = vec![false; a_len + b_len];
    //               let (a_flags, b_flags) = flags_memory.split_at_mut(a_len);`
    // (lib.rs:109-110) -- mirrored as one Vec with two indexed regions.
    assert(2 * (a_len as int) + 2 * (b_len as int) + 8 <= usize::MAX as int) by {
        assert(a_len as int == a.len() as int);
        assert(b_len as int == b.len() as int);
    }
    let total = a_len + b_len;
    let mut flags: Vec<bool> = Vec::with_capacity(total);
    assert(total == a_len + b_len);
    let mut fi: usize = 0;
    while fi < total
        invariant
            fi <= total,
            flags.len() == fi,
            forall|q: int| 0 <= q < fi ==> flags[q] == false,
        decreases total - fi,
    {
        flags.push(false);
        fi = fi + 1;
    }
    proof {
        // As in the driving probe: total (= a_len + b_len) holds under 2*(a+b)+8 <= MAX
        assert(2 * (a_len as int) + 2 * (b_len as int) + 8 <= usize::MAX as int) by {}
        flag_count_all_false(flags@, 0, a_len as int);
        flag_count_all_false(flags@, a_len as int, (a_len + b_len) as int);
    }

    let mut matches: usize = 0;

    // Origin Rust: `for (i, a_elem) in a.into_iter().enumerate() { ... }` (lib.rs:114)
    let mut i: usize = 0;
    while i < a_len
        invariant
            i <= a_len,
            flags.len() == total,
            total == a_len + b_len,
            a_len == a.len(),
            b_len == b.len(),
            a_len >= 1,
            b_len >= 1,
            a_len <= flags.len(),
            search_range <= a_len + b_len,
            2 * (a_len as int) + 2 * (b_len as int) + 8 <= usize::MAX as int,
            matches == flag_count(flags@, 0, a_len as int),
            matches == flag_count(flags@, a_len as int, (a_len + b_len) as int),
            matches <= a_len,
            forall|q: int| i <= q < a_len ==> flags[q] == false,
        decreases a_len - i,
    {
        // Origin Rust: `let min_bound = i.saturating_sub(search_range);` (lib.rs:116)
        let min_bound = i.saturating_sub(search_range);
        // Origin Rust: `let max_bound = min(b_len, i + search_range + 1);` (lib.rs:118)
        assert(i as int + search_range as int + 1
            <= 2 * (a_len as int) + 2 * (b_len as int) + 2) by {
            assert(i <= a_len);
            assert(search_range <= a_len + b_len);
        }
        let max_bound = if b_len <= i + search_range + 1 {
            b_len
        } else {
            i + search_range + 1
        };
        assert(max_bound <= b_len);

        // Origin Rust: `for (j, b_elem) in b.into_iter().enumerate().take(max_bound)`
        // (lib.rs:120)
        let mut j: usize = 0;
        while j < max_bound
            invariant_except_break
                forall|q: int| i <= q < a_len ==> flags[q] == false,
            invariant
                i < a_len,
                j <= max_bound,
                max_bound <= b_len,
                a_len == a.len(),
                b_len == b.len(),
                b_len >= 1,
                total == a_len + b_len,
                flags.len() == total,
                a_len + j <= flags.len(),
                matches == flag_count(flags@, 0, a_len as int),
                matches == flag_count(flags@, a_len as int, (a_len + b_len) as int),
                matches <= a_len,
            ensures forall|q: int| i + 1 <= q < a_len ==> flags[q] == false
            decreases max_bound - j,
        {
            if min_bound <= j && a[i] == b[j] && !flags[a_len + j] {
                // Origin Rust: `a_flags[i] = true; b_flags[j] = true;
                //               matches += 1; break;` (lib.rs:122-126)
                proof {
                    assert(a_len + j < (flags@).len());
                    // The b-side segment count gains +1; the a-side slot i was never written before (tail invariant)
                    assert(flags[i as int] == false) by {
                        assert(i < a_len);
                        assert(i < flags.len());
                    }
                }
                let ghost flags_pre_view: Seq<bool> = flags@;
                flags.set(a_len + j, true);
                flags.set(i, true);
                matches = matches + 1;
                proof {
                    // post = pre.update(p_b, true).update(i, true), p_b = a_len + j
                    let ghost z = flags_pre_view.update((a_len + j) as int, true);
                    assert(flags@ == z.update(i as int, true));
                    // a segment [0, a_len): slot i was false (tail invariant) -> +1;
                    // p_b is out of bounds, no effect
                    flag_count_set_one(z, 0, a_len as int, i as int);
                    flag_count_update_at_or_beyond(
                        flags_pre_view,
                        0,
                        a_len as int,
                        (a_len + j) as int,
                    );
                    // b segment [a_len, a_len+b_len): slot p_b was false (guard) -> +1;
                    // i is before the segment, no effect
                    flag_count_set_one(
                        flags_pre_view,
                        a_len as int,
                        (a_len + b_len) as int,
                        (a_len + j) as int,
                    );
                    flag_count_update_before(
                        z,
                        a_len as int,
                        (a_len + b_len) as int,
                        i as int,
                    );
                    assert(flag_count(flags@, 0, a_len as int) == matches as int);
                    assert(flag_count(flags@, a_len as int, (a_len + b_len) as int)
                        == matches as int);
                    flag_count_le_size(flags@, 0, a_len as int);
                    assert(matches <= a_len);
                }
                break;
            }
            j = j + 1;
        }
        // Tail region preserved (the inner loop writes at most slot i itself)
        assert(forall|q: int| i + 1 <= q < a_len ==> flags[q] == false);
        i = i + 1;
    }

    let mut transpositions: usize = 0;
    if matches != 0 {
        // Origin Rust: the zip paired skipped-position transposition loop (lib.rs:131-149).
        // The dual advance of the iterator zip is mirrored as the double cursor ai/bi.
        let mut ai: usize = 0; // read cursor over the a sequence
        let mut bi: usize = 0; // read cursor over the b sequence
        // ghost pairing counter (proof-only): the number of consumed b-side set slots
        let ghost mut consumed: int = 0;
        while ai < a_len
            invariant
                ai <= a_len,
                bi <= b_len,
                a_len == a.len(),
                b_len == b.len(),
                total == a_len + b_len,
                flags.len() == total,
                ai < flags.len(),
                a_len + bi <= flags.len(),
                matches == flag_count(flags@, 0, a_len as int),
                matches == flag_count(flags@, a_len as int, (a_len + b_len) as int),
                consumed == flag_count(flags@, a_len as int, (a_len + bi) as int),
                transpositions as int <= consumed,
                matches as int >= 1,
            decreases a_len - ai,
        {
            if flags[ai] {
                // Find the next set slot on the b side (the upstream b_iter.next() loop)
                loop
                    invariant
                        matches as int >= 1,
                        ai < a_len,
                        bi <= b_len,
                        a_len == a.len(),
                        b_len == b.len(),
                        total == a_len + b_len,
                        flags.len() == total,
                        a_len + bi <= flags.len(),
                        matches == flag_count(flags@, 0, a_len as int),
                        matches == flag_count(flags@, a_len as int, (a_len + b_len) as int),
                        consumed == flag_count(flags@, a_len as int, (a_len + bi) as int),
                        transpositions as int <= consumed,
                    decreases b_len - bi,
                {
                    if bi < b_len {
                        if !flags[a_len + bi] {
                            proof {
                                assert(((a_len + bi) as int) < (flags@).len());
                                assert(flags@[(a_len + bi) as int] == false);
                                flag_count_extend_one(
                                    flags@,
                                    a_len as int,
                                    (a_len + bi) as int,
                                );
                            }
                            bi = bi + 1;
                            continue;
                        }
                        proof {
                            assert(((a_len + bi) as int) < (flags@).len());
                            flag_count_extend_one(
                                flags@,
                                a_len as int,
                                (a_len + bi) as int,
                            );
                            assert(flags@[(a_len + bi) as int] == true);
                        }
                        if a[ai] != b[bi] {
                            proof {
                                // This slot flags[a_len+bi] == true => prefix count +1;
                                // segment monotonicity => consumed+1 <= matches
                                flag_count_extend_one(
                                    flags@,
                                    a_len as int,
                                    ((a_len + bi)) as int,
                                );
                                flag_count_monotone(
                                    flags@,
                                    a_len as int,
                                    ((a_len + bi + 1)) as int,
                                    ((a_len + b_len)) as int,
                                );
                                assert(consumed + 1 <= matches as int);
                            }
                            assert(transpositions as int + 1 <= matches as int);
                            transpositions = transpositions + 1;
                        }
                        proof {
                            consumed = consumed + 1;
                        }
                        bi = bi + 1;
                        break;
                    } else {
                        // Upstream: after b_iter is exhausted, `loop { if let Some(..) {..} }`
                        // (lib.rs:135-147) does not break on the None branch -- its termination
                        // relies on "the a/b set counts == matches, pairwise equal" (machine-checked by
                        // the lemma above via the invariants) and that branch is unreachable; mirrored here
                        // as a break with a note (semantics: no set b-slot elements remain).
                        break;
                    }
                }
            }
            ai = ai + 1;
        }
        proof {
            // Pairing monotonicity corollary: consumed = prefix count <= full-segment count = matches,
            // and transpositions <= consumed => transpositions <= matches.
            flag_count_monotone(
                flags@,
                a_len as int,
                (a_len + bi) as int,
                (a_len + b_len) as int,
            );
            assert(consumed <= matches as int);
            assert(transpositions as int <= matches as int);
        }
    }
    let _ = transpositions / 2; // Origin Rust: `transpositions /= 2;` (lib.rs:150)
    proof {
        // Underflow fence for the f64 tail `matches - transpositions / 2`:
        // in the matches == 0 branch the transposition loop never ran (transpositions == 0);
        // in the matches != 0 branch the pairing invariant gives transpositions <= matches.
        if matches == 0 {
            assert(transpositions == 0);
        } else {
            assert(transpositions as int <= matches as int);
        }
        assert(transpositions as int / 2 <= matches as int);
    }

    if matches == 0 {
        0.0
    } else {
        // Origin Rust: the f64 combining arithmetic of lib.rs:155-158 (no SMT obligation)
        ((matches as f64 / a_len as f64)
            + (matches as f64 / b_len as f64)
            + (((matches - (transpositions / 2)) as f64) / (matches as f64)))
            / 3.0
    }
}

/// Origin Rust: `pub fn jaro(a: &str, b: &str) -> f64` (lib.rs:182-184, forwarding).
/// Upstream doc (lib.rs:173-181):
///   Calculates the Jaro similarity between two strings. The returned value
///   is between 0.0 and 1.0 (higher value means more similar).
///   use strsim::jaro;
///   assert!((0.392 - jaro("Friedrich Nietzsche", "Jean-Paul Sartre")).abs() <
///   0.001);
pub fn jaro(a: &[char], b: &[char]) -> (r: f64)
    requires
        jaro_len_precond(a.len() as int, b.len() as int),
{
    generic_jaro(a, b)
}

/// Origin Rust: `pub fn generic_jaro_winkler<...>(a, b) -> f64` (lib.rs:187-207).
/// Upstream doc (lib.rs:186-186):
///   Like Jaro but gives a boost to sequences that have a common prefix.
pub fn generic_jaro_winkler(a: &[char], b: &[char]) -> (r: f64)
    requires
        jaro_len_precond(a.len() as int, b.len() as int),
{
    let sim = generic_jaro(a, b);

    if sim > 0.7 {
        // Origin Rust: the common-prefix length (lib.rs:196-201): take(4).zip(b)
        //   .take_while(equal).count() mirrored as a fixed-length index advance.
        let mut prefix_length: usize = 0;
        let mut k: usize = 0;
        while k < 4
            invariant
                k <= 4,
                prefix_length <= k,
            decreases 4 - k,
        {
            if k < a.len() && k < b.len() && a[k] == b[k] {
                prefix_length = prefix_length + 1;
            } else {
                break;
            }
            k = k + 1;
        }

        sim + 0.1 * prefix_length as f64 * (1.0 - sim)
    } else {
        sim
    }
}

/// Origin Rust: `pub fn jaro_winkler(a: &str, b: &str) -> f64` (lib.rs:217-219).
/// Upstream doc (lib.rs:209-216):
///   Like Jaro but gives a boost to strings that have a common prefix.
///   use strsim::jaro_winkler;
///   assert!((0.866 - jaro_winkler("cheeseburger", "cheese fries")).abs() <
///   0.001);
pub fn jaro_winkler(a: &[char], b: &[char]) -> (r: f64)
    requires
        jaro_len_precond(a.len() as int, b.len() as int),
{
    generic_jaro_winkler(a, b)
}

/* =====================================================================
 * generic_levenshtein / levenshtein (mirror of lib.rs:229-267)
 * ===================================================================== */

/// Origin Rust: `pub fn generic_levenshtein<...>(a, b) -> usize` (lib.rs:229-255).
/// The row-advancing DP over the single-row cache is mirrored as index loops; the contract has three tiers:
///  1. L0: no panics (index fences + addition-overflow precondition)
///  2. empty-input exactness: a empty => b_len; b empty => a_len
///  3. value range: r <= |a| + |b| (the upper bound closes via the cache monotone-value invariant)
/// Upstream doc (lib.rs:221-228):
///   Calculates the minimum number of insertions, deletions, and substitutions
///   required to change one sequence into the other.
///   use strsim::generic_levenshtein;
///   assert_eq!(3, generic_levenshtein(&[1,2,3], &[1,2,3,4,5,6]));
pub fn generic_levenshtein(a: &[char], b: &[char]) -> (r: usize)
    requires
        a.len() + b.len() + 2 <= usize::MAX as int,
    ensures
        a.len() == 0 ==> r == b.len(),
        b.len() == 0 ==> r == a.len(),
        r <= a.len() + b.len(),
{
    let b_len = b.len();

    // Origin Rust: `let mut cache: Vec<usize> = (1..b_len + 1).collect();` (lib.rs:237)
    // cache[j] == j + 1 (0 <= j < b_len)
    let mut cache: Vec<usize> = Vec::with_capacity(b_len);
    assert(b_len + 1 <= usize::MAX);
    let mut cj: usize = 0;
    while cj < b_len
        invariant
            cj <= b_len,
            cache.len() == cj,
            b_len == b.len(),
            forall|q: int| 0 <= q < cj ==> cache[q] == q + 1,
        decreases b_len - cj,
    {
        cache.push(cj + 1);
        cj = cj + 1;
    }

    // Origin Rust: `let mut result = b_len;` (lib.rs:239)
    let mut result: usize = b_len;

    // Invariant system (D(i, j) = the edit distance over the prefixes):
    //   outer head(i):   result = D(i, b_len) <= i + b_len;
    //                    cache[q] = upper-row value <= i + q + 1
    //   inner head(i,j): result = D(i+1, j) <= (i + 1) + j;
    //                    distance_b = D(i, j) <= i + j;
    //                    written region cache[q<j] <= (i+2)+q | unwritten region cache[q>=j] <= i+q+1
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            cache.len() == b_len,
            b_len == b.len(),
            result <= i + b_len,
            b_len == 0 ==> result == i,
            i == 0 ==> result == b_len,
            a.len() as int + b.len() as int + 2 <= usize::MAX as int,
            i as int + (b_len as int) + 2 <= usize::MAX as int,
            forall|q: int| 0 <= q < b_len ==> cache[q] <= i + q + 1,
        decreases a.len() - i,
    {
        // Origin Rust: `result = i + 1; let mut distance_b = i;` (lib.rs:242-243)
        result = i + 1;
        let mut distance_b: usize = i;

        let mut j: usize = 0;
        while j < b_len
            invariant
                i < a.len(),
                j <= b_len,
                cache.len() == b_len,
                b_len == b.len(),
                b_len == 0 ==> result == i + 1,
                a.len() as int + b.len() as int + 2 <= usize::MAX as int,
                i as int + (b_len as int) + 2 <= usize::MAX as int,
                result <= (i + 1) + j,
                distance_b <= i + j,
                forall|q: int| 0 <= q < j ==> cache[q] <= (i + 1) + q + 1,
                forall|q: int| j <= q < b_len ==> cache[q] <= i + q + 1,
            decreases b_len - j,
        {
            // Origin Rust: `let cost = usize::from(a_elem != b_elem);` (lib.rs:246)
            let cost: usize = if a[i] != b[j] { 1 } else { 0 };
            proof {
                assert(distance_b <= i + j);
                assert(cache[j as int] <= i + j + 1) by {
                    assert(j >= j);
                }
            }
            // Origin Rust: `let distance_a = distance_b + cost;` (lib.rs:247)
            let distance_a: usize = distance_b + cost;
            // Origin Rust: `distance_b = cache[j];` (lib.rs:248)
            distance_b = cache[j];
            // Origin Rust: `result = min(result + 1, min(distance_a, distance_b + 1));` (lib.rs:249)
            let d1 = result + 1;
            let d2 = distance_b + 1;
            let m1 = if distance_a <= d2 { distance_a } else { d2 };
            result = if d1 <= m1 { d1 } else { m1 };
            proof {
                // All three candidates <= i + j + 2 (= the (i+1)+(j+1) row/col bound)
                assert(d1 <= (i + 1) + j + 1) by {
                    assert(result <= (i + 1) + j) by { assert(result <= (i + 1) + j); }
                }
                assert(distance_a <= i + j + 2) by {
                    assert(cost <= 1);
                }
                assert(d2 <= i + j + 2) by {
                    assert(distance_b == cache[j as int]);
                }
            }
            // Origin Rust: `cache[j] = result;` (lib.rs:250)
            cache.set(j, result);
            proof {
                assert(result <= (i + 1) + j + 1) by {}
                assert(cache[j as int] <= i + 1 + j + 1);
            }
            j = j + 1;
        }
        proof {
            // Inner-loop exit (j == b_len): result <= (i+1) + b_len;
            // the unwritten-region condition merges into the written side, the last value is irrelevant; distance_b is never read again.
            assert(result <= (i + 1) + b_len) by {
                assert(b_len >= j) by { assert(j == b_len); }
                assert(result <= (i + 1) + j) by { assert(j == b_len); }
            }
        }
        i = i + 1;
        proof {
            // Next outer head: result <= i_new + b_len; the written cache region merges into
            // the new blanket cache[q] <= i_new+q+1 (the (i+2)+q bound restated with the new i)
            assert(i <= a.len()) by { assert(i - 1 < a.len()); }
            assert(i as int + (b_len as int) + 2 <= usize::MAX as int) by {
                assert(a.len() as int + b.len() as int + 2 <= usize::MAX as int);
                assert(i <= a.len());
            }
        }
    }
    proof {
        if a.len() == 0 {
            assert(result == b_len) by { assert(i == 0); }
        } else {
            assert(result <= i + b_len) by { assert(i == a.len()); }
        }
        assert(result <= a.len() + b.len()) by {
            assert(result <= i + b_len);
            assert(i <= a.len());
        }
    }
    result
}

/// Origin Rust: `pub fn levenshtein(a: &str, b: &str) -> usize` (lib.rs:265-267).
/// Upstream doc (lib.rs:257-264):
///   Calculates the minimum number of insertions, deletions, and substitutions
///   required to change one string into the other.
///   use strsim::levenshtein;
///   assert_eq!(3, levenshtein("kitten", "sitting"));
pub fn levenshtein(a: &[char], b: &[char]) -> (r: usize)
    requires
        a.len() + b.len() + 2 <= usize::MAX as int,
    ensures
        a.len() == 0 ==> r == b.len(),
        b.len() == 0 ==> r == a.len(),
        r <= a.len() + b.len(),
{
    generic_levenshtein(a, b)
}

/* =====================================================================
 * osa_distance (mirror of lib.rs:296-333)
 * ===================================================================== */

/// Origin Rust: `pub fn osa_distance(a: &str, b: &str) -> usize` (lib.rs:296).
/// Three-row DP + head/tail character memory. Contract: L0 panic-free + the value-range upper bound
/// r <= max(a.len(), b.len()) + transposition-window slack (closed as (a+b+1)).
/// Upstream doc (lib.rs:288-295):
///   Like Levenshtein but allows for adjacent transpositions. Each substring can
///   only be edited once.
///   use strsim::osa_distance;
///   assert_eq!(3, osa_distance("ab", "bca"));
pub fn osa_distance(a: &[char], b: &[char]) -> (r: usize)
    requires
        a.len() + b.len() + 4 <= usize::MAX as int,
    ensures
        a.len() == 0 ==> r == b.len(),
        b.len() == 0 ==> r == a.len(),
        r <= a.len() + b.len(),
{
    let b_len = b.len();

    // Origin Rust: `let mut prev_two_distances: Vec<usize> = (0..b_len + 1).collect();`
    //               `let mut prev_distances: Vec<usize> = (0..b_len + 1).collect();`
    //               `let mut curr_distances: Vec<usize> = vec![0; b_len + 1];` (lib.rs:300-302)
    assert((b_len as int) + 1 <= usize::MAX as int) by {
        assert(a.len() as int + b.len() as int + 4 <= usize::MAX as int);
    }
    let b_len_p1 = b_len + 1;
    let mut prev_two_distances: Vec<usize> = Vec::with_capacity(b_len_p1);
    let mut prev_distances: Vec<usize> = Vec::with_capacity(b_len_p1);
    let mut curr_distances: Vec<usize> = Vec::with_capacity(b_len_p1);
    let mut cj: usize = 0;
    while cj < b_len_p1
        invariant
            cj <= b_len_p1,
            prev_two_distances.len() == cj,
            prev_distances.len() == cj,
            curr_distances.len() == cj,
            forall|q: int| 0 <= q < cj ==>
                prev_two_distances[q] == q as usize
                    && prev_distances[q] == q as usize
                    && curr_distances[q] == 0,
        decreases b_len_p1 - cj,
    {
        prev_two_distances.push(cj);
        prev_distances.push(cj);
        curr_distances.push(0);
        cj = cj + 1;
    }

    // Origin Rust: `let mut prev_a_char = char::MAX; let mut prev_b_char = char::MAX;`
    // (lib.rs:304-305)
    let mut prev_a_char: char = '\u{10FFFF}'; // Origin Rust: the char::MAX constant (lib.rs:304)
    let mut prev_b_char: char = '\u{10FFFF}'; // Origin Rust: the char::MAX constant (lib.rs:305)

    // Row-semantics note: the outer i (from 0) builds the D(i+1, .) row; at the loop head
    //   prev_distances = row i (D(i, q) = q); prev_two/curr are the earlier rows.
    // The value-range invariants are maintained in the "row+col" shape (D(r, c) <= r + c <= i + b_len),
    // which is the inductive source of the ensures-side r <= a.len() + b.len().
    // Origin Rust: `for (i, a_char) in a.chars().enumerate() { ... }` (lib.rs:307)
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            b_len == b.len(),
            a.len() as int + b.len() as int + 4 <= usize::MAX as int,
            prev_two_distances.len() == b_len + 1,
            prev_distances.len() == b_len + 1,
            curr_distances.len() == b_len + 1,
            forall|q: int| 0 <= q <= b_len ==> prev_distances[q] <= i + q,
            forall|q: int| 0 <= q <= b_len ==> prev_two_distances[q] <= (i + 1) + q,
            forall|q: int| 0 <= q <= b_len ==> curr_distances[q] <= (i + 1) + q,
            i == 0 ==> forall|q: int| 0 <= q <= b_len ==>
                prev_two_distances[q] == q as usize
                    && prev_distances[q] == q as usize
                    && curr_distances[q] == 0,
            b_len == 0 ==> prev_distances[0] == i,
        decreases a.len() - i,
    {
        let a_char = a[i];
        // Origin Rust: `curr_distances[0] = i + 1;` (lib.rs:308)
        curr_distances.set(0, i + 1);
        proof {
            assert(curr_distances[0] == (i + 1) as usize);
            assert(i + 1 <= (i + 1) + 0);
        }

        // Origin Rust: `for (j, b_char) in b.chars().enumerate() { ... }` (lib.rs:310)
        let mut j: usize = 0;
        while j < b_len
            invariant
                i < a.len(),
                j <= b_len,
                b_len == b.len(),
                i as int + (b_len as int) + 4 <= usize::MAX as int,
                b_len == 0 ==> curr_distances[0] == i + 1,
                prev_two_distances.len() == b_len + 1,
                prev_distances.len() == b_len + 1,
                curr_distances.len() == b_len + 1,
                forall|q: int| 0 <= q <= b_len ==> prev_distances[q] <= i + q,
                forall|q: int| 0 <= q <= b_len ==> prev_two_distances[q] <= (i + 1) + q,
                forall|q: int| 0 <= q <= b_len ==> curr_distances[q] <= (i + 1) + q,
            decreases b_len - j,
        {
            let b_char = b[j];
            // Origin Rust: `let cost = usize::from(a_char != b_char);` (lib.rs:311)
            let cost: usize = if a_char != b_char { 1 } else { 0 };
            // Origin Rust: `curr_distances[j + 1] = min(curr_distances[j] + 1,
            //               min(prev_distances[j + 1] + 1, prev_distances[j] + cost));`
            // (lib.rs:312-315)
            let c1 = curr_distances[j] + 1;
            let c2 = prev_distances[j + 1] + 1;
            let c3 = prev_distances[j] + cost;
            let m0 = if c2 <= c3 { c2 } else { c3 };
            let mut val = if c1 <= m0 { c1 } else { m0 };
            proof {
                // The row+col upper bound of val <= D(i+1, j+1): (i+1) + (j+1)
                assert(val <= (i + 1) + (j + 1)) by {
                    assert(c1 <= (i + 1) + j + 1) by {
                        assert(curr_distances[j as int] <= (i + 1) + j);
                    }
                    assert(c2 <= (i + 1) + (j + 1)) by {
                        assert(prev_distances[(j + 1) as int] <= i + (j + 1));
                    }
                    assert(c3 <= (i + 1) + j + 1) by {
                        assert(prev_distances[j as int] <= i + j);
                        assert(cost <= 1);
                    }
                }
            }
            // Origin Rust: `if i > 0 && j > 0 && a_char != b_char && a_char == prev_b_char
            //                && b_char == prev_a_char { ... }` (lib.rs:316-319)
            if i > 0
                && j > 0
                && a_char != b_char
                && a_char == prev_b_char
                && b_char == prev_a_char
            {
                val = if prev_two_distances[j - 1] + 1 <= val {
                    prev_two_distances[j - 1] + 1
                } else {
                    val
                };
                proof {
                    assert(prev_two_distances[(j - 1) as int] <= (i + 1) + (j - 1));
                }
            }

            curr_distances.set(j + 1, val);
            prev_b_char = b_char;
            j = j + 1;
        }

        // Origin Rust: `mem::swap(&mut prev_two_distances, &mut prev_distances);
        //               mem::swap(&mut prev_distances, &mut curr_distances);`
        // (lib.rs:324-325) -- the two swaps expand into a three-variable rotation:
        //   prev_two <- old prev_distances; prev_distances <- old curr_distances;
        //   curr_distances <- old prev_two_distances.
        let old_prev_two = prev_two_distances;
        let old_prev_one = prev_distances;
        let old_curr = curr_distances;
        prev_two_distances = old_prev_one;
        prev_distances = old_curr;
        curr_distances = old_prev_two;

        prev_a_char = a_char;
        i = i + 1;
        proof {
            // Next round with i (the new row number) i_new = i: maintains the three forall invariants
            let i2 = i;
            assert(forall|q: int| 0 <= q <= b_len ==> prev_distances[q] <= i2 + q) by {
                assert(forall|q: int| 0 <= q <= b_len ==>
                    old_curr[q] <= (i2 - 1) + 1 + q) by {
                    // old_curr is the just-built row i2: values <= (i2-1+1) + q
                    assert(forall|q: int| 0 <= q <= b_len ==> old_curr[q] <= (i2 - 1 + 1) + q);
                }
            }
            assert(forall|q: int| 0 <= q <= b_len ==>
                prev_two_distances[q] <= (i2 + 1) + q) by {
                assert(forall|q: int| 0 <= q <= b_len ==>
                    old_prev_one[q] <= (i2 - 1) + q + 1);
            }
            assert(forall|q: int| 0 <= q <= b_len ==>
                curr_distances[q] <= (i2 + 1) + q) by {
                assert(forall|q: int| 0 <= q <= b_len ==>
                    old_prev_two[q] <= (i2 - 1 + 1) + q);
            }
        }
    }

    // Origin Rust: `prev_distances[b_len]` (lib.rs:332)
    proof {
        assert(a.len() + b_len <= usize::MAX as int) by {
            assert(a.len() + b.len() + 4 <= usize::MAX as int);
        }
        assert(prev_distances[b_len as int] <= a.len() + b_len);
    }
    prev_distances[b_len]
}

/* =====================================================================
 * generic_damerau_levenshtein (mirror of lib.rs:349-410, char specialization)
 * -- assault batch (2026-11-03): the flat-matrix three-segment blanket (exact four-segment border + interior
 *    cell(x,y) <= (x-1)+(y-1) + global <= max_distance); the nonlinear sites consistently go
 *    through explicit vstd::arithmetic::mul lemma chains (the by (nonlinear_arith) tactic is
 *    unreliable on this machine profile; see the environment note in out/bug-finder-summary.md).
 * ===================================================================== */

/* Kept in place (spec-2 exception, documented): these two booster lemmas
 * feed the generic_damerau_levenshtein inner-loop query, which sits at
 * the Z3 rlimit margin; relocating them after the exec fns measuredly
 * and deterministically turns that query into an rlimit error. */
/* --- nonlinear-arithmetic booster lemma family ------------------------------- */

/// (a+1)*w == a*w + w (distributivity booster: distributive_add(x,y,z) => x*(y+z)==x*y+x*z).
proof fn dist_succ(a: int, w: int)
    requires
        0 <= a,
        0 <= w,
    ensures (a + 1) * w == a * w + w,
{
    vstd::arithmetic::mul::lemma_mul_is_distributive_add(w, a, 1);
    vstd::arithmetic::mul::lemma_mul_is_commutative(w, a + 1);
    vstd::arithmetic::mul::lemma_mul_is_commutative(w, a);
    assert(w * (a + 1) == w * a + w * 1);
    assert(w * 1 == w);
    assert(w * (a + 1) == (a + 1) * w);
    assert(w * a == a * w);
    assert((a + 1) * w == a * w + w);
}

/// The flat position-fence main lemma: row*w + x in [0, total).
/// width == ad+2 and total == (ad+2)*(bd+2) (called after the exec let bridging).
proof fn flat_pos_lt_total(w: int, ad: int, bd: int, total: int, row: int, x: int)
    requires
        1 <= ad,
        1 <= bd,
        w == ad + 2,
        total == (ad + 2) * (bd + 2),
        0 <= row <= bd + 1,
        0 <= x < w,
    ensures
        0 <= row * w + x < total,
{
    assert(row * w <= (bd + 1) * w) by {
        vstd::arithmetic::mul::lemma_mul_inequality(row, bd + 1, w);
    }
    assert((bd + 1) * w + w == (bd + 2) * w) by {
        dist_succ(bd + 1, w);
    }
    assert((bd + 2) * w == total) by {
        assert((bd + 2) * w == w * (bd + 2)) by {
            vstd::arithmetic::mul::lemma_mul_is_commutative(bd + 2, w);
        }
        assert(w * (bd + 2) == (ad + 2) * (bd + 2)) by {}
    }
    assert(row * w + x < total);
}


/* --- matrix twins ------------------------------------------------------------- */

pub open spec fn cell(dist: Seq<usize>, width: int, x: int, y: int) -> usize {
    dist.index(y * width + x)
}

pub open spec fn total_len(a_len: int, b_len: int) -> int {
    (a_len + 2) * (b_len + 2)
}

pub open spec fn matrix_blanks(
    dist: Seq<usize>,
    width: int,
    a_len: int,
    b_len: int,
    m: usize,
) -> bool {
    &&& width == a_len + 2
    &&& (total_len(a_len, b_len) as nat) == dist.len()
    &&& (forall|x: int| 1 <= x <= a_len + 1 ==> cell(dist, width, x, 0) == m)
    &&& (forall|y: int| 1 <= y <= b_len + 1 ==> cell(dist, width, 0, y) == m)
    &&& (forall|x: int| 1 <= x <= a_len + 1 ==> cell(dist, width, x, 1) == ((x - 1) as usize))
    &&& (forall|y: int| 1 <= y <= b_len + 1 ==> cell(dist, width, 1, y) == ((y - 1) as usize))
    &&& (forall|x: int, y: int|
            2 <= x <= a_len + 1 && 2 <= y <= b_len + 1 ==> cell(dist, width, x, y)
                <= (((x - 1) + (y - 1)) as usize))
    &&& (forall|x: int, y: int|
            0 <= x <= a_len + 1 && 0 <= y <= b_len + 1 ==> cell(dist, width, x, y) <= m)
}

/// Origin Rust: `fn flat_index(i: usize, j: usize, width: usize) -> usize
///               { j * width + i }` (lib.rs:337-339).
fn flat_index(i: usize, j: usize, width: usize) -> (r: usize)
    requires
        ((j as int) * (width as int)) + (i as int) <= usize::MAX as int,
    ensures
        (r as int) == ((i as int) + ((j as int) * (width as int))),
{
    j * width + i
}


/// Origin Rust: `pub fn generic_damerau_levenshtein<Elem>(...) -> usize`
/// (lib.rs:349-410, char-specialized base).
/// Upstream doc (lib.rs:341-348):
///   Like optimal string alignment, but substrings can be edited an unlimited
///   number of times, and the triangle inequality holds.
///   use strsim::generic_damerau_levenshtein;
///   assert_eq!(2, generic_damerau_levenshtein(&[1,2], &[2,3,1]));
pub fn generic_damerau_levenshtein(a_elems: &[char], b_elems: &[char]) -> (r: usize)
    requires
        total_len(a_elems.len() as int, b_elems.len() as int) + 8 <= usize::MAX as int,
        2 * (a_elems.len() as int) + 2 * (b_elems.len() as int) + 1
            <= usize::MAX as int,
    ensures
        a_elems.len() == 0 ==> r == b_elems.len(),
        b_elems.len() == 0 ==> r == a_elems.len(),
        r <= a_elems.len() + b_elems.len(),
{
    let a_len = a_elems.len();
    let b_len = b_elems.len();

    if a_len == 0 {
        return b_len;
    }
    if b_len == 0 {
        return a_len;
    }

    let width = a_len + 2;
    let total = (a_len + 2) * (b_len + 2);
    let max_distance = a_len + b_len;

    assert((total as int) == total_len(a_len as int, b_len as int)) by {
        assert(((a_len as int) + 2) == (width as int)) by {}
    }
    assert((width as int) == (a_len as int) + 2) by {}

    // Origin Rust: `let mut distances = vec![0; (a_len + 2) * (b_len + 2)];` (lib.rs:364)
    let mut distances: Vec<usize> = Vec::with_capacity(total);
    let mut bi: usize = 0;
    while bi < total
        invariant
            bi <= total,
            distances.len() == bi,
            forall|q: int| 0 <= q < bi ==> distances[q] == 0,
            (total as int) == total_len((a_len as int), (b_len as int)),
            (total as int) == ((a_len as int) + 2) * ((b_len as int) + 2),
            (width as int) == (a_len as int) + 2,
            1 <= a_len,
            1 <= b_len,
            (total as int) + 8 <= usize::MAX as int,
            2 * (a_len as int) + 2 * (b_len as int) + 1 <= usize::MAX as int,
        decreases total - bi,
    {
        distances.push(0);
        bi = bi + 1;
    }

    // Origin Rust: `distances[0] = max_distance;` (lib.rs:366)
    proof {
        let ad = a_len as int;
        let bd = b_len as int;
        assert((total as int) >= 3) by {
            vstd::arithmetic::mul::lemma_mul_inequality(1, ad + 2, bd + 2);
            assert(1 * (bd + 2) == bd + 2);
            assert((bd + 2) >= 3);
            assert(1 * (bd + 2) <= (ad + 2) * (bd + 2));
            assert((ad + 2) * (bd + 2) == (total as int));
        }
        assert(distances.len() >= 1);
    }
    distances.set(0, max_distance);

    // init all-zero -> the interior-cell zero bridge (for the border loop entry check)
    proof {
        let ad = a_len as int;
        let bd = b_len as int;
        let w = width as int;
        assert forall|x: int, y: int|
            (2 <= x <= ad + 1 && 2 <= y <= bd + 1) implies cell(distances@, w, x, y) == 0 by {
            flat_pos_lt_total(w, ad, bd, (total as int), y, x);
            assert(cell(distances@, w, x, y) == distances@[y * w + x]);
            assert(distances@[y * w + x] == 0);
        }
    }

    // Origin Rust: the column-border double-write loop (lib.rs:368-371)
    let mut i0: usize = 0;
    while i0 < a_len + 1
        invariant
            i0 <= a_len + 1,
            distances.len() == total,
            (total as int) == total_len((a_len as int), (b_len as int)),
            (total as int) == ((a_len as int) + 2) * ((b_len as int) + 2),
            (width as int) == (a_len as int) + 2,
            forall|q: int| 1 <= q <= (i0 as int) ==>
                (cell(distances@, width as int, q, 0) == max_distance
                    && cell(distances@, width as int, q, 1) == ((q - 1) as usize)),
            forall|x: int, y: int|
                (2 <= x <= (a_len as int) + 1 && 2 <= y <= (b_len as int) + 1)
                    ==> cell(distances@, width as int, x, y) == 0,
            distances@[(0 * (width as int) + 0) as int] == max_distance,
            2 * (a_len as int) + 2 * (b_len as int) + 1 <= usize::MAX as int,
            1 <= a_len,
            1 <= b_len,
        decreases a_len + 1 - i0,
    {
        let ghost pre = distances@;
        proof {
            let ad = a_len as int;
            let bd = b_len as int;
            let w = width as int;
            // The flat(i+1, 0) / flat(i+1, 1) fences
            flat_pos_lt_total(w, ad, bd, (total as int), 0, (i0 as int) + 1);
            flat_pos_lt_total(w, ad, bd, (total as int), 1, (i0 as int) + 1);
        }
        distances.set(i0 + 1, max_distance);
        let ghost mid = distances@;
        proof {
            let w = width as int;
            let q0 = (i0 as int) + 1;
            assert(mid == pre.update(q0, max_distance));
            vstd::seq::lemma_seq_update_same(pre, q0, max_distance);
            vstd::seq::lemma_seq_update_different(mid, w + q0, q0, max_distance);
        }
        distances.set(width + i0 + 1, i0);
        proof {
            let ad = (a_len as int);
            let bd = (b_len as int);
            let w = width as int;
            let q0 = (i0 as int) + 1;
            let post = distances@;
            assert(post == mid.update(w + q0, i0));
            vstd::seq::lemma_seq_update_same(mid, w + q0, i0);
            vstd::seq::lemma_seq_update_different(post, q0, w + q0, i0);
            // col-0 segment maintenance
            assert forall|q: int| 1 <= q <= ((i0 as int) + 1) implies cell(
                post,
                w,
                q,
                0,
            ) == max_distance by {
                if q == q0 {
                    assert(post.index(q0) == mid.index(q0));
                    assert(mid.index(q0) == max_distance);
                } else {
                    assert(q < q0);
                    let head_val = cell(pre, w, q, 0);
                    assert(head_val == max_distance);
                    assert(post.index(q) == mid.index(q)) by {
                        assert(post == mid.update(w + q0, i0));
                        vstd::seq::lemma_seq_update_different(post, q, w + q0, i0);
                    }
                    assert(mid.index(q) == pre.index(q)) by {
                        assert(mid == pre.update(q0, max_distance));
                        vstd::seq::lemma_seq_update_different(mid, q, q0, max_distance);
                    }
                }
            }
            // col-1 segment maintenance
            assert forall|q: int| 1 <= q <= ((i0 as int) + 1) implies cell(post, w, q, 1)
                == ((q - 1) as usize) by {
                if q == q0 {
                    assert(post.index(w + q0) == i0) by {
                        assert(post == mid.update(w + q0, i0));
                        vstd::seq::lemma_seq_update_same(mid, w + q0, i0);
                    }
                    assert((w + q0) == (w + (i0 as int) + 1));
                } else {
                    let head_val2 = cell(pre, w, q, 1);
                    assert(head_val2 == (((q - 1) as usize)));
                    assert(post.index(w + q) == mid.index(w + q)) by {
                        assert(post == mid.update(w + q0, i0));
                        vstd::seq::lemma_seq_update_different(post, w + q, w + q0, i0);
                    }
                    assert(mid.index(w + q) == pre.index(w + q)) by {
                        assert(mid == pre.update(q0, max_distance));
                        vstd::seq::lemma_seq_update_different(mid, w + q, q0, max_distance);
                    }
                    assert(mid.index(w + q) == ((q - 1) as usize));
                }
            }
            // interior zero-segment maintenance (both write slots lie outside interior)
            assert forall|x: int, y: int|
                2 <= x <= (ad + 1) && 2 <= y <= (bd + 1) implies cell(post, w, x, y)
                    == 0 by {
                let pos = y * w + x;
                let head_val3 = cell(pre, w, x, y);
                assert(head_val3 == 0);
                assert(pos >= 2 * w + 2) by {
                    vstd::arithmetic::mul::lemma_mul_inequality(2, y, w);
                    assert(pos == (y * w) + x);
                }
                assert(post.index(pos) == mid.index(pos)) by {
                    assert(post == mid.update(w + q0, i0));
                    assert(pos != (w + q0)) by {
                        assert((w + q0) <= w + ad + 1);
                        assert(2 * w + 2 > w + ad + 1) by {
                            assert(w + 1 > ad + 1) by {
                                assert(w == ad + 2);
                            }
                        }
                    }
                    vstd::seq::lemma_seq_update_different(post, pos, w + q0, i0);
                }
                assert(mid.index(pos) == pre.index(pos)) by {
                    assert(mid == pre.update(q0, max_distance));
                    assert(pos != q0) by {
                        assert(q0 <= ad + 1 <= w);
                    }
                    vstd::seq::lemma_seq_update_different(mid, pos, q0, max_distance);
                }
            }
        }
        i0 = i0 + 1;
    }

    // Origin Rust: the row-border double-write loop (lib.rs:373-376)
    let mut j0: usize = 0;
    while j0 < b_len + 1
        invariant
            j0 <= b_len + 1,
            distances.len() == total,
            (total as int) == total_len((a_len as int), (b_len as int)),
            (total as int) == ((a_len as int) + 2) * ((b_len as int) + 2),
            (width as int) == (a_len as int) + 2,
            forall|q: int| 1 <= q <= (a_len as int) + 1 ==>
                (cell(distances@, width as int, q, 0) == max_distance
                    && cell(distances@, width as int, q, 1) == ((q - 1) as usize)),
            forall|q: int| 1 <= q <= (j0 as int) ==>
                (cell(distances@, width as int, 0, q) == max_distance
                    && cell(distances@, width as int, 1, q) == ((q - 1) as usize)),
            forall|x: int, y: int|
                (2 <= x <= (a_len as int) + 1 && 2 <= y <= (b_len as int) + 1)
                    ==> cell(distances@, width as int, x, y) == 0,
            distances@[(0 * (width as int) + 0) as int] == max_distance,
            2 * (a_len as int) + 2 * (b_len as int) + 1 <= usize::MAX as int,
            1 <= a_len,
            1 <= b_len,
        decreases b_len + 1 - j0,
    {
        let ghost pre = distances@;
        proof {
            let ad = a_len as int;
            let bd = b_len as int;
            let w = width as int;
            let row = (j0 as int) + 1;
            // The fence for the exec product (j0+1)*width
            flat_pos_lt_total(w, ad, bd, (total as int), row, 0);
            flat_pos_lt_total(w, ad, bd, (total as int), row, 1);
            assert(row * w < (total as int));
            assert(((row * w) + 1) < (total as int));
            assert(((j0 + 1) * width) as int == row * w) by {
                assert(row == (j0 as int) + 1);
                assert(w == (width as int));
            }
            assert((((j0 + 1) * width) + 1) as int == row * w + 1);
            assert(cell(distances@, w, 0, row) == distances@[row * w]) by {}
            assert(cell(distances@, w, 1, row) == distances@[row * w + 1]) by {}
        }
        distances.set((j0 + 1) * width, max_distance);
        let ghost mid = distances@;
        proof {
            let w = width as int;
            let row = (j0 as int) + 1;
            assert(mid == pre.update(row * w, max_distance));
            vstd::seq::lemma_seq_update_same(pre, row * w, max_distance);
            vstd::seq::lemma_seq_update_different(mid, row * w + 1, row * w, max_distance);
        }
        distances.set((j0 + 1) * width + 1, j0);
        proof {
            let ad = (a_len as int);
            let bd = (b_len as int);
            let w = width as int;
            let row = (j0 as int) + 1;
            let pre0 = pre;
            let mid0 = mid;
            let post0 = distances@;
            assert(mid0 == pre0.update(row * w, max_distance));
            assert(post0 == mid0.update(row * w + 1, j0));
            vstd::seq::lemma_seq_update_same(mid0, row * w + 1, j0);
            vstd::seq::lemma_seq_update_different(post0, row * w, row * w + 1, j0);
            // col-segment (both twins) maintenance: q and w+q both differ from the row write slot (except the same-value point row==1 && q==1)
            vstd::arithmetic::mul::lemma_mul_inequality(1, row, w);
            assert forall|q: int| 1 <= q <= ad + 1 implies cell(post0, w, q, 0)
                    == max_distance && cell(post0, w, q, 1)
                    == (((q - 1) as usize)) by {
                assert(q < w <= row * w);
                assert(post0.index(q) == mid0.index(q)) by {
                    vstd::seq::lemma_seq_update_different(post0, q, row * w + 1, j0);
                }
                assert(mid0.index(q) == pre0.index(q)) by {
                    vstd::seq::lemma_seq_update_different(mid0, q, row * w, max_distance);
                }
                assert(cell(pre0, w, q, 0) == max_distance);
                assert(cell(pre0, w, q, 1) == (((q - 1) as usize)));
                if row == 1 && q == 1 {
                    assert(post0.index(w + q) == j0);
                    assert(j0 == 0);
                    assert((q - 1) == 0);
                } else {
                    assert(post0.index(w + q) == mid0.index(w + q)) by {
                        assert(row * w + 1 != w + q) by {
                            if row == 1 {
                                assert(q >= 2);
                                assert(row * w + 1 == w + 1 < w + q);
                            } else {
                                vstd::arithmetic::mul::lemma_mul_inequality(2, row, w);
                                assert(2 * w <= row * w);
                                assert(row * w >= 2 * w);
                                assert(row * w + 1 >= 2 * w + 1);
                                assert(q < w);
                                assert(2 * w + 1 > w + q);
                            }
                        }
                        vstd::seq::lemma_seq_update_different(post0, w + q, row * w + 1, j0);
                    }
                    assert(mid0.index(w + q) == pre0.index(w + q)) by {
                        assert(row * w != w + q) by {
                            if row == 1 {
                                assert(q >= 2);
                                assert(w < w + q);
                            } else {
                                vstd::arithmetic::mul::lemma_mul_inequality(2, row, w);
                                assert(row * w >= 2 * w);
                                assert(q < w);
                                assert(2 * w > w + q);
                            }
                        }
                        vstd::seq::lemma_seq_update_different(mid0, w + q, row * w, max_distance);
                    }
                }
            }
            // row-0 segment maintenance
            assert forall|q: int| 1 <= q <= row implies cell(post0, w, 0, q)
                    == max_distance by {
                if q == row {
                    assert(q * w == row * w);
                    assert(post0.index(q * w) == mid0.index(q * w)) by {
                        assert(row * w + 1 != q * w);
                        vstd::seq::lemma_seq_update_different(post0, q * w, row * w + 1, j0);
                    }
                    assert(mid0.index(q * w) == max_distance);
                } else {
                    assert(q < row);
                    assert(post0.index(q * w) == mid0.index(q * w)) by {
                        vstd::arithmetic::mul::lemma_mul_strict_inequality(q, row, w);
                        assert(q * w < row * w + 1);
                        assert(q * w != row * w + 1);
                        vstd::seq::lemma_seq_update_different(post0, q * w, row * w + 1, j0);
                    }
                    assert(mid0.index(q * w) == pre0.index(q * w)) by {
                        vstd::arithmetic::mul::lemma_mul_strict_inequality(q, row, w);
                        assert(q * w != row * w);
                        vstd::seq::lemma_seq_update_different(mid0, q * w, row * w, max_distance);
                    }
                    assert(cell(pre0, w, 0, q) == max_distance);
                }
            }
            // row-1 segment maintenance
            assert forall|q: int| 1 <= q <= row implies cell(post0, w, 1, q)
                    == (((q - 1) as usize)) by {
                if q == row {
                    assert(q * w + 1 == row * w + 1);
                    assert(post0.index(q * w + 1) == j0);
                    assert(j0 as int == q - 1);
                } else {
                    assert(q < row);
                    assert(post0.index(q * w + 1) == mid0.index(q * w + 1)) by {
                        vstd::arithmetic::mul::lemma_mul_strict_inequality(q, row, w);
                        assert(q * w + 1 != row * w + 1);
                        vstd::seq::lemma_seq_update_different(post0, q * w + 1, row * w + 1, j0);
                    }
                    assert(mid0.index(q * w + 1) == pre0.index(q * w + 1)) by {
                        vstd::arithmetic::mul::lemma_mul_strict_inequality(q, row, w);
                        dist_succ((row - 1), w);
                        assert(((row - 1) + 1) * w == (row - 1) * w + w);
                        assert(row * w == (row - 1) * w + w);
                        vstd::arithmetic::mul::lemma_mul_inequality(q, (row - 1), w);
                        assert(q * w <= (row - 1) * w);
                        assert(q * w + 1 <= (row - 1) * w + 1);
                        assert((row - 1) * w + 1 < (row - 1) * w + w);
                        assert(q * w + 1 < row * w);
                        assert(q * w + 1 != row * w);
                        vstd::seq::lemma_seq_update_different(mid0, q * w + 1, row * w, max_distance);
                    }
                    assert(cell(pre0, w, 1, q) == (((q - 1) as usize)));
                }
            }
            // interior zero-segment maintenance: the trichotomy distinctness of pos versus the two write slots
            assert forall|x: int, y: int|
                2 <= x <= (ad + 1) && 2 <= y <= (bd + 1) implies cell(post0, w, x, y)
                    == 0 by {
                let pos = y * w + x;
                assert(cell(pre0, w, x, y) == 0);
                if y == row {
                    assert(pos == row * w + x);
                    assert(x >= 2);
                    assert(pos != row * w);
                    assert(pos != row * w + 1);
                } else if y < row {
                    vstd::arithmetic::mul::lemma_mul_inequality((y + 1), row, w);
                    dist_succ(y, w);
                    assert((y * w) + x < (y * w) + w) by {
                        assert(x < w);
                    }
                    assert((y + 1) * w == y * w + w);
                    assert((y + 1) * w <= row * w);
                    assert(pos < row * w);
                } else {
                    assert(y >= row + 1);
                    vstd::arithmetic::mul::lemma_mul_inequality((row + 1), y, w);
                    assert((row + 1) * w <= y * w);
                    assert(pos >= y * w);
                    assert(pos >= (row + 1) * w);
                    dist_succ(row, w);
                    assert((row + 1) * w == row * w + w);
                    assert(row * w + w > row * w + 1);
                    assert((row + 1) * w > row * w + 1);
                }
                assert(post0.index(pos) == mid0.index(pos)) by {
                    assert(pos != row * w + 1);
                    vstd::seq::lemma_seq_update_different(post0, pos, row * w + 1, j0);
                }
                assert(mid0.index(pos) == pre0.index(pos)) by {
                    assert(pos != row * w);
                    vstd::seq::lemma_seq_update_different(mid0, pos, row * w, max_distance);
                }
            }
        }
        j0 = j0 + 1;
    }

    // Establishing matrix_blanks (the global <= m clause via the four border segments + the interior zero split).
    assert forall|x: int, y: int|
        0 <= x <= (a_len as int) + 1
        && 0 <= y <= (b_len as int) + 1 implies cell(
            distances@,
            width as int,
            x,
            y,
        ) <= max_distance by {
        if x == 0 && y == 0 {
            assert(cell(distances@, width as int, 0, 0) == max_distance);
        } else if x == 0 {
            assert(cell(distances@, width as int, 0, y) == max_distance);
        } else if y == 0 {
            assert(cell(distances@, width as int, x, 0) == max_distance);
        } else if x == 1 {
            assert(cell(distances@, width as int, 1, y) == (((y as int) - 1) as usize));
            assert(cell(distances@, width as int, 1, y) <= max_distance);
        } else if y == 1 {
            assert(cell(distances@, width as int, x, 1) == (((x as int) - 1) as usize));
            assert(cell(distances@, width as int, x, 1) <= max_distance);
        } else {
            assert(cell(distances@, width as int, x, y) == 0);
        }
    }
    assert(matrix_blanks(
        distances@,
        width as int,
        a_len as int,
        b_len as int,
        max_distance,
    ));

    // Origin Rust: `let mut elems: HashMap<Elem, usize> = HashMap::with_capacity(64);`
    //               => the assoc-list base (first-match get / replacement insert)
    let mut ekeys: Vec<char> = Vec::with_capacity(0);
    let mut evals: Vec<usize> = Vec::with_capacity(0);

    // The main double loop (mirror of lib.rs:380-407)
    let mut i: usize = 1;
    while i < a_len + 1
        invariant
            1 <= i <= a_len + 1,
            distances.len() == total,
            (total as int) == total_len((a_len as int), (b_len as int)),
            (total as int) == ((a_len as int) + 2) * ((b_len as int) + 2),
            (width as int) == (a_len as int) + 2,
            (total as int) + 8 <= usize::MAX as int,
            a_len == a_elems.len(),
            b_len == b_elems.len(),
            matrix_blanks(
                distances@,
                width as int,
                a_len as int,
                b_len as int,
                max_distance,
            ),
            ekeys.len() == evals.len(),
            forall|q: int| #![trigger evals[q]] 0 <= q < evals.len()
                ==> 1 <= evals[q] <= ((i as int) - 1),
            2 * (a_len as int) + 2 * (b_len as int) + 1 <= usize::MAX as int,
            max_distance == a_len + b_len,
            1 <= a_len,
            1 <= b_len,
        decreases a_len + 1 - i,
    {
        // Origin Rust: `let mut db = 0;` (lib.rs:381)
        let mut db: usize = 0;
        let mut j: usize = 1;
        while j < b_len + 1
            invariant
                1 <= j <= b_len + 1,
                1 <= i <= a_len,
                distances.len() == total,
                (total as int) == total_len((a_len as int), (b_len as int)),
                (total as int) == ((a_len as int) + 2) * ((b_len as int) + 2),
                (width as int) == (a_len as int) + 2,
                (total as int) + 8 <= usize::MAX as int,
                a_len == a_elems.len(),
                b_len == b_elems.len(),
                matrix_blanks(
                    distances@,
                    width as int,
                    a_len as int,
                    b_len as int,
                    max_distance,
                ),
                ekeys.len() == evals.len(),
                forall|q: int| #![trigger evals[q]] 0 <= q < evals.len()
                    ==> 1 <= evals[q] <= ((i as int) - 1),
                db <= (j as int) - 1,
                2 * (a_len as int) + 2 * (b_len as int) + 1 <= usize::MAX as int,
                max_distance == a_len + b_len,
                1 <= a_len,
                1 <= b_len,
            decreases b_len + 1 - j,
        {
            let bkey = b_elems[j - 1];
            let mut p: usize = 0;
            let mut found: bool = false;
            while p < ekeys.len()
                invariant
                    p <= ekeys.len(),
                    found ==> p < ekeys.len(),
                    found ==> ekeys[p as int] == bkey,
                    ekeys.len() == evals.len(),
                decreases ekeys.len() - p,
            {
                if ekeys[p] == bkey {
                    found = true;
                    break;
                }
                p = p + 1;
            }
            let k: usize = if found { evals[p] } else { 0 };
            proof {
                if found {
                    assert(evals[p as int] <= ((i as int) - 1));
                    assert(k as int <= ((i as int) - 1));
                } else {
                    assert(k == 0);
                }
                assert((k as int) < (i as int));
            }

            // Fences for the four flat read slots + the write slot (all via flat_pos_lt_total)
            proof {
                let ad = a_len as int;
                let bd = b_len as int;
                let w = width as int;
                let tot = total as int;
                let ii = i as int;
                let jj = j as int;
                flat_pos_lt_total(w, ad, bd, tot, jj + 1, ii);
                flat_pos_lt_total(w, ad, bd, tot, jj, ii + 1);
                flat_pos_lt_total(w, ad, bd, tot, (db as int), (k as int));
                flat_pos_lt_total(w, ad, bd, tot, jj, ii);
                flat_pos_lt_total(w, ad, bd, tot, jj + 1, ii + 1);
                // exec expression bridges
                assert(((j + 1) * width) as int == (jj + 1) * w) by {
                    assert(w == (width as int));
                }
                assert(((j) * width) as int == jj * w) by {
                    assert(w == (width as int));
                }
                assert(((k) * width) as int == (k as int) * w) by {
                    assert(w == (width as int));
                }
                assert((db * width) as int == (db as int) * w) by {
                    assert(w == (width as int));
                }
            }

            let fc_ij1 = flat_index(i, j + 1, width);
            proof {
                let w = width as int;
                let ii = i as int;
                let jj = j as int;
                assert((fc_ij1 as int) == ((jj + 1) * w + ii));
                assert(cell(distances@, w, ii, jj + 1) == distances@[fc_ij1 as int]);
                assert(cell(distances@, w, ii, jj + 1) <= max_distance);
                assert((distances@[fc_ij1 as int] as int)
                    < (usize::MAX as int));
            }
            let insertion_cost = distances[fc_ij1] + 1;
            let fc_i1j = flat_index(i + 1, j, width);
            proof {
                let w = width as int;
                let ii = i as int;
                let jj = j as int;
                assert((fc_i1j as int) == (jj * w + ii + 1));
                assert(cell(distances@, w, ii + 1, jj) == distances@[fc_i1j as int]);
                assert(cell(distances@, w, ii + 1, jj) <= max_distance);
            }
            let deletion_cost = distances[fc_i1j] + 1;
            let fc_kdb = flat_index(k, db, width);
            proof {
                let w = width as int;
                let ii = i as int;
                let jj = j as int;
                let ad = a_len as int;
                let bd = b_len as int;
                assert(w == (width as int));
                assert((fc_kdb as int) == (((k as int) + ((db as int) * w))));
                assert(cell(distances@, (width as int), (k as int), (db as int))
                    == cell(distances@, w, (k as int), (db as int)));
                assert(cell(distances@, (width as int), (k as int), (db as int))
                    == distances@[fc_kdb as int]);
                assert(cell(distances@, (width as int), (k as int), (db as int))
                    <= max_distance);
                assert(((i as int) - (k as int) - 1) <= (ad - 1));
                assert(((j as int) - (db as int) - 1) <= (bd - 1));
                assert((max_distance as int) == ((ad) + (bd)));
                assert(cell(distances@, (width as int), (k as int), (db as int)) as int
                    + (((i as int) - (k as int) - 1)) + 1
                    + (((j as int) - (db as int) - 1))
                    <= ((max_distance as int) + ad + bd + 1));
                assert((max_distance as int) + ad + bd + 1
                    <= (2 * ((a_len as int)) + 2 * ((b_len as int)) + 1));
                assert(2 * ((a_len as int)) + 2 * ((b_len as int)) + 1
                    <= usize::MAX as int);
            }
            let tsz = distances[fc_kdb] + (i - k - 1) + 1 + (j - db - 1);
            let fc_ij = flat_index(i, j, width);
            proof {
                let w = width as int;
                let ii = i as int;
                let jj = j as int;
                assert((fc_ij as int) == (jj * w + ii));
                assert(cell(distances@, w, ii, jj) == distances@[fc_ij as int]);
                assert(cell(distances@, w, ii, jj) <= max_distance);
            }
            let mut substitution_cost = distances[fc_ij] + 1;
            if a_elems[i - 1] == b_elems[j - 1] {
                db = j;
                substitution_cost = substitution_cost - 1;
            }

            let m1 = if deletion_cost <= tsz { deletion_cost } else { tsz };
            let m2 = if insertion_cost <= m1 { insertion_cost } else { m1 };
            let val = if substitution_cost <= m2 { substitution_cost } else { m2 };
            let fc_i1j1 = flat_index(i + 1, j + 1, width);
            proof {
                let w = width as int;
                let ii = i as int;
                let jj = j as int;
                let ad = a_len as int;
                let bd = b_len as int;
                assert(w == (width as int));
                // write-slot twin bridging
                assert((fc_i1j1 as int) == ((jj + 1) * w + ii + 1));
                assert(distances@[fc_i1j1 as int]
                    == cell(distances@, w, ii + 1, jj + 1));
                // ins/del/sub candidates: global cell <= m
                assert(cell(distances@, w, ii, jj + 1) <= max_distance);
                assert(cell(distances@, w, ii + 1, jj) <= max_distance);
                assert(cell(distances@, w, (k as int), (db as int)) <= max_distance);
                assert(cell(distances@, w, ii, jj) <= max_distance);
                assert((tsz as int) <= ((max_distance as int) + ad + 1 + bd));
                // written value <= i+j: val <= substitution = cell(i,j) +- 1, case split
                if ii >= 2 && jj >= 2 {
                    assert(cell(distances@, w, ii, jj)
                        <= (((ii - 1) + (jj - 1)) as usize));
                } else if ii == 1 {
                    assert(cell(distances@, w, 1, jj) == (((jj as int) - 1) as usize));
                } else {
                    assert(cell(distances@, w, ii, 1) == (((ii as int) - 1) as usize));
                }
                assert((substitution_cost as int) <= ii + jj - 1) by {
                    if a_elems[i - 1] == b_elems[j - 1] {
                        assert((substitution_cost as int)
                            == ((cell(distances@, w, ii, jj)) as int));
                    } else {
                        assert((substitution_cost as int)
                            == (((cell(distances@, w, ii, jj)) as int) + 1));
                    }
                }
                assert((val as int) <= (substitution_cost as int));
                assert((val as int) <= ii + jj);
                assert(cell(distances@.update(fc_i1j1 as int, val), w, ii + 1, jj + 1)
                    == val);
            }
            let ghost pre_w = distances@;
            distances.set(fc_i1j1, val);
            proof {
                let ad = (a_len as int);
                let bd = (b_len as int);
                let w = (width as int);
                let ii = (i as int);
                let jj = (j as int);
                let post0 = distances@;
                let pw = (fc_i1j1 as int);
                assert(post0 == pre_w.update(pw, val));
                // write-slot value range (for the same-slot cases in the segments below)
                assert((val as int) <= ii + jj);
                // Segment A col-0
                assert forall|q: int| 1 <= q <= ad + 1 implies cell(post0, w, q, 0)
                    == max_distance by {
                    assert(cell(pre_w, w, q, 0) == max_distance);
                    vstd::arithmetic::mul::lemma_mul_inequality(2, (jj + 1), w);
                    assert(pw >= 2 * w + (ii + 1));
                    assert(2 * w + (ii + 1) > ad + 1) by {
                        assert(w == ad + 2);
                        assert(ii >= 1);
                    }
                    assert(q < pw);
                    vstd::seq::lemma_seq_update_different(post0, q, pw, val);
                }
                // Segment C col-1
                assert forall|q: int| 1 <= q <= ad + 1 implies cell(post0, w, q, 1)
                    == (((q - 1) as usize)) by {
                    assert(cell(pre_w, w, q, 1) == (((q - 1) as usize)));
                    vstd::arithmetic::mul::lemma_mul_inequality(2, (jj + 1), w);
                    assert(pw >= 2 * w + 2);
                    assert(2 * w + 2 > w + q) by {
                        assert(w + 2 > q) by {
                            assert(q <= ad + 1);
                            assert(w == ad + 2);
                        }
                    }
                    assert(w + q < pw);
                    vstd::seq::lemma_seq_update_different(post0, w + q, pw, val);
                }
                // Segment B row-0
                assert forall|y: int| 1 <= y <= bd + 1 implies cell(post0, w, 0, y)
                    == max_distance by {
                    assert(cell(pre_w, w, 0, y) == max_distance);
                    let posy = y * w;
                    if y == (jj + 1) {
                        assert(pw - posy == ii + 1);
                        assert(pw != posy);
                    } else if y < (jj + 1) {
                        assert(y <= jj);
                        vstd::arithmetic::mul::lemma_mul_inequality(y, jj, w);
                        assert(y * w <= jj * w);
                        dist_succ(jj, w);
                        assert((jj + 1) * w == jj * w + w);
                        assert(posy == y * w);
                        assert(posy <= jj * w);
                        assert(jj * w < (jj + 1) * w);
                        assert(posy < (jj + 1) * w);
                        assert(posy < pw);
                    } else {
                        assert(y >= (jj + 2));
                        vstd::arithmetic::mul::lemma_mul_inequality((jj + 2), y, w);
                        assert(pw < ((jj + 1) * w) + w) by {
                            assert(ii + 1 < w);
                        }
                        assert((jj + 2) * w == (jj + 1) * w + w) by {
                            dist_succ((jj + 1), w);
                        }
                        assert(pw < (jj + 2) * w);
                        assert(pw <= posy) by {
                            assert(pw < (jj + 2) * w <= posy);
                        }
                    }
                    assert(pw != posy);
                    vstd::seq::lemma_seq_update_different(post0, posy, pw, val);
                }
                // Segment D row-1
                assert forall|y: int| 1 <= y <= bd + 1 implies cell(post0, w, 1, y)
                    == (((y - 1) as usize)) by {
                    assert(cell(pre_w, w, 1, y) == (((y - 1) as usize)));
                    let posy = y * w + 1;
                    if y == (jj + 1) {
                        assert(pw - posy == ii);
                        assert(ii >= 1);
                        assert(pw != posy);
                    } else if y < (jj + 1) {
                        vstd::arithmetic::mul::lemma_mul_inequality(y, jj, w);
                        assert(y * w <= jj * w);
                        dist_succ(jj, w);
                        assert((jj + 1) * w == jj * w + w);
                        assert(posy <= jj * w + 1);
                        assert(jj * w + 1 < (jj + 1) * w);
                        assert(posy < (jj + 1) * w);
                        assert(posy < pw);
                    } else {
                        assert(y >= (jj + 2));
                        vstd::arithmetic::mul::lemma_mul_inequality((jj + 2), y, w);
                        dist_succ((jj + 1), w);
                        assert(((jj + 1) + 1) * w == (jj + 1) * w + w);
                        assert(pw < (jj + 1) * w + w) by {
                            assert(ii + 1 < w);
                        }
                        assert(pw < (jj + 2) * w);
                        assert((jj + 2) * w <= posy) by {
                            assert(posy == y * w + 1);
                        }
                        assert(pw < posy);
                    }
                    assert(pw != posy);
                    vstd::seq::lemma_seq_update_different(post0, posy, pw, val);
                }
                // Segment E interior
                assert forall|x: int, y: int|
                    2 <= x <= ad + 1 && 2 <= y <= bd + 1 implies cell(post0, w, x, y)
                        <= (((x - 1) + (y - 1)) as usize) by {
                    let pos = y * w + x;
                    assert(cell(pre_w, w, x, y)
                        <= (((x - 1) + (y - 1)) as usize));
                    if pos == pw {
                        if y == (jj + 1) {
                            assert(pos - pw == x - (ii + 1));
                            assert(x == ii + 1);
                        } else if y <= jj {
                            dist_succ(y, w);
                            assert((y + 1) * w == y * w + w);
                            assert(pos < (y + 1) * w);
                            vstd::arithmetic::mul::lemma_mul_inequality((y + 1), (jj + 1), w);
                            assert((y + 1) * w <= (jj + 1) * w);
                            assert(pos < pw);
                            assert(pos != pw);
                        } else {
                            vstd::arithmetic::mul::lemma_mul_inequality((jj + 2), y, w);
                            dist_succ((jj + 1), w);
                            assert((jj + 2) * w == (jj + 1) * w + w);
                            assert(pos >= (jj + 2) * w);
                            assert(pw < (jj + 1) * w + w) by {
                                assert(ii + 1 < w);
                            }
                            assert(pos > pw);
                            assert(pos != pw);
                        }
                        assert(y == (jj + 1));
                        assert(x == ii + 1);
                        assert((val as int) <= (((x - 1) + (y - 1))));
                    } else {
                        assert(pos != pw);
                        vstd::seq::lemma_seq_update_different(post0, pos, pw, val);
                    }
                }
                // Segment F global <= m
                assert forall|x: int, y: int|
                    0 <= x <= ad + 1 && 0 <= y <= bd + 1 implies cell(post0, w, x, y)
                        <= max_distance by {
                    assert(cell(pre_w, w, x, y) <= max_distance);
                    let pos = y * w + x;
                    if pos == pw {
                        if y == (jj + 1) {
                            assert(pos - pw == x - (ii + 1));
                            assert(x == ii + 1);
                        } else if y <= jj {
                            dist_succ(y, w);
                            assert((y + 1) * w == y * w + w);
                            assert(pos < (y + 1) * w);
                            vstd::arithmetic::mul::lemma_mul_inequality((y + 1), (jj + 1), w);
                            assert((y + 1) * w <= (jj + 1) * w);
                            assert(pos < pw);
                            assert(pos != pw);
                        } else {
                            vstd::arithmetic::mul::lemma_mul_inequality((jj + 2), y, w);
                            dist_succ((jj + 1), w);
                            assert((jj + 2) * w == (jj + 1) * w + w);
                            assert(pos >= (jj + 2) * w);
                            assert(pw < (jj + 1) * w + w) by {
                                assert(ii + 1 < w);
                            }
                            assert(pos > pw);
                            assert(pos != pw);
                        }
                        assert(y == (jj + 1));
                        assert(x == ii + 1);
                        assert((val as int) <= ii + jj);
                        assert((max_distance as int) == (ad + bd));
                        assert(ii <= ad);
                        assert(jj <= bd);
                    } else {
                        assert(pos != pw);
                        vstd::seq::lemma_seq_update_different(post0, pos, pw, val);
                    }
                }
            }

            j = j + 1;
        }

        // Origin Rust: `elems.insert(a_elems[i - 1].clone(), i);` (lib.rs:406)
        let akey = a_elems[i - 1];
        let mut sp: usize = 0;
        let mut s_found: bool = false;
        while sp < ekeys.len()
            invariant
                sp <= ekeys.len(),
                s_found ==> sp < ekeys.len(),
                s_found ==> ekeys[sp as int] == akey,
                ekeys.len() == evals.len(),
            decreases ekeys.len() - sp,
        {
            if ekeys[sp] == akey {
                s_found = true;
                break;
            }
            sp = sp + 1;
        }
        if s_found {
            evals.set(sp, i);
        } else {
            ekeys.push(akey);
            evals.push(i);
        }
        i = i + 1;
    }

    proof {
        let w = width as int;
        let ad = a_len as int;
        let bd = b_len as int;
        let tot = total as int;
        let ii = ad + 1;
        let jj = bd + 1;
        flat_pos_lt_total(w, ad, bd, tot, jj, ii);
        assert((((b_len + 1) * width) as int) == (jj * w)) by {
            assert(jj == (b_len as int) + 1);
            assert(w == (width as int));
        }
        assert((((b_len + 1) * width) as int) + (((a_len + 1)) as int) == (jj * w + ii));
        assert(((jj * w) + ii) <= (usize::MAX as int)) by {
            assert((jj * w + ii) < tot);
            assert(tot + 8 <= usize::MAX as int);
        }
    }
    let fi = flat_index(a_len + 1, b_len + 1, width);
    proof {
        let w = width as int;
        let ad = a_len as int;
        let bd = b_len as int;
        let tot = total as int;
        flat_pos_lt_total(w, ad, bd, tot, bd + 1, ad + 1);
        let ii = ad + 1;
        let jj = bd + 1;
        assert((fi as int) == (jj * w + ii));
        assert(distances@[fi as int] == cell(distances@, w, ii, jj)) by {
            assert((fi as int) == (jj * w + ii));
        }
        assert(cell(distances@, w, ii, jj) <= (((ii - 1) + (jj - 1)) as usize)) by {
            // blank clause 5 at (a_len+1, b_len+1): an interior cell
            assert(2 <= ii <= ad + 1);
            assert(2 <= jj <= bd + 1);
        }
    }
    distances[fi]
}
/* =====================================================================
 * damerau_levenshtein_impl / damerau_levenshtein (mirror of lib.rs:605-675)
 * -- assault batch (2026-11-03): the Zhao-Sahni three-row isize DP; row-phase invariants
 *    (outer head phase r == row i-1) + fully linear indexing; the upstream
 *    HybridGrowingHashmapChar<RowId> (most-recent-row table) maps to the assoc-list base
 *    Vec<char>/Vec<isize> (lookup = linear first match; insert = replace or push).
 * ===================================================================== */

/// Origin Rust: `fn damerau_levenshtein_impl<Iter1, Iter2>(
///     s1: Iter1, len1: usize, s2: Iter2, len2: usize) -> usize` ([char] base).
pub fn damerau_levenshtein_impl(s1: &[char], s2: &[char]) -> (r: usize)
    requires
        8 * (s1.len() as int) + 8 * (s2.len() as int) + 64
            <= isize::MAX as int,
    ensures
        s1.len() == 0 ==> r == s2.len(),
        s2.len() == 0 ==> r == s1.len(),
        r <= s1.len() + s2.len(),
{
    // Origin Rust: `let max_val = max(len1, len2) as isize + 1;` (lib.rs:615)
    let len1 = s1.len();
    let len2 = s2.len();
    let maxlen = if len1 >= len2 { len1 } else { len2 };
    assert(maxlen as int <= s1.len() as int + s2.len() as int) by {
        if len1 >= len2 {
            assert(maxlen == len1);
        } else {
            assert(maxlen == len2);
        }
    }
    let max_val: isize = maxlen as isize + 1;
    assert((max_val as int) >= 1) by {}

    let size = len2 + 2;
    assert((size as int) >= 2) by {}

    // The global value-range blanket ([0, B_V]) -- the invariant baseline for the candidate arithmetic.
    // B_V = len1 + len2 + 4 >= max_val, also admitting any written/unwritten in-row value.
    assert(4 * (len1 as int) + 4 * (len2 as int) + 32 <= isize::MAX as int) by {
        assert(2 * (4 * (len1 as int) + 4 * (len2 as int) + 32)
            <= isize::MAX as int) by {
            assert(8 * (len1 as int) + 8 * (len2 as int) + 64
                <= isize::MAX as int);
        }
    }

    // Origin Rust: `let mut fr = vec![max_val; size]; let mut r1 = vec![max_val; size];`
    //               (lib.rs:620-621) -- mirrored as push-loop initialization.
    let mut fr: Vec<isize> = Vec::with_capacity(size);
    let mut r1: Vec<isize> = Vec::with_capacity(size);
    let mut ci: usize = 0;
    while ci < size
        invariant
            ci <= size,
            fr.len() == ci,
            r1.len() == ci,
            forall|q: int| 0 <= q < ci ==> (fr[q] == max_val && r1[q] == max_val),
            size == len2 + 2,
            (size as int) >= 2,
            8 * (len1 as int) + 8 * (len2 as int) + 64 <= isize::MAX as int,
            max_val >= 1,
            (max_val as int) <= (len1 as int) + (len2 as int) + 4,
            (size as int) <= isize::MAX as int / 8,
        decreases size - ci,
    {
        fr.push(max_val);
        r1.push(max_val);
        ci = ci + 1;
    }

    // Origin Rust: `let mut r: Vec<isize> = (max_val..max_val + 1)
    //               .chain(0..(size - 1) as isize).collect();` (lib.rs:622-624)
    //   => r[0] == max_val; r[q] == q - 1 (1 <= q <= size-1)
    let mut r: Vec<isize> = Vec::with_capacity(size);
    r.push(max_val);
    let mut cj: usize = 1;
    while cj < size
        invariant
            1 <= cj <= size,
            r.len() == cj,
            r[0] == max_val,
            forall|q: int| #![trigger r[q]] 1 <= q < cj ==> r[q] == q - 1,
            size == len2 + 2,
            8 * (len1 as int) + 8 * (len2 as int) + 64 <= isize::MAX as int,
            max_val >= 1,
            (max_val as int) <= (len1 as int) + (len2 as int) + 4,
            (cj as int) <= isize::MAX as int / 8,
        decreases size - cj,
    {
        r.push(cj as isize - 1);
        cj = cj + 1;
    }
    assert(forall|q: int| 1 <= q < size ==> r[q] == q - 1) by {}

    // Assoc-list base: the upstream HybridGrowingHashmapChar<RowId> (most-recent-row table):
    //   get(c) = default -1 / first-match value; set(c, i) = replace or push.
    let mut tkeys: Vec<char> = Vec::with_capacity(0);
    let mut tvals: Vec<isize> = Vec::with_capacity(0);

    // Origin Rust: `for (i, ch1) in s1.enumerate().map(|(i, ch1)| (i + 1, ch1)) { ... }`
    //               (lib.rs:626)
    let mut i: usize = 1;
    while i < len1 + 1
        invariant
            1 <= i <= len1 + 1,
            len1 == s1.len(),
            len2 == s2.len(),
            size == len2 + 2,
            (size as int) >= 2,
            r.len() == size,
            r1.len() == size,
            fr.len() == size,
            r[0] == max_val,
            r1[0] == max_val,
            max_val >= 1,
            (max_val as int) <= (len1 as int) + (len2 as int) + 4,
            // r is row (i-1) (the body swaps before writing: head phase = pre-swap)
            forall|q: int| #![trigger r[q]] 1 <= q < size
                ==> (0 <= r[q] <= ((i as int) - 1) + (q - 1)),
            forall|q: int| #![trigger r1[q]] 0 <= q < size
                ==> (0 <= r1[q] <= (len1 as int) + (len2 as int) + 8),
            forall|q: int| #![trigger fr[q]] 0 <= q < size
                ==> (0 <= fr[q] <= (len1 as int) + (len2 as int) + 8),
            // Empty-input exactness (initial row: r[q] == q-1, unwritten only when i == 1)
            i == 1 ==> (forall|q: int| #![trigger r[q]] 1 <= q < size ==> r[q] == q - 1),
            len2 == 0 ==> (r[(size - 1) as int] == (i - 1) as isize),
            // assoc list
            tkeys.len() == tvals.len(),
            forall|q: int| #![trigger tvals[q]] 0 <= q < tvals.len()
                ==> tvals[q] == -1 || (1 <= tvals[q] && tvals[q] <= (i as int) - 1),
            8 * (len1 as int) + 8 * (len2 as int) + 64 <= isize::MAX as int,
            max_val == (maxlen as isize) + 1,
        decreases len1 + 1 - i,
    {
        // Origin Rust: `mem::swap(&mut r, &mut r1);` (lib.rs:627) -- three-variable rotation
        let old_r = r;
        let old_r1 = r1;
        r = old_r1;
        r1 = old_r;
        proof {
            // After rotation: r1 is the previous r (row i-1), r is the row from two rounds back (within the max blanket)
        }
        // Origin Rust: `let mut last_col_id: isize = -1; let mut last_i2l1 = r[1];
        //               r[1] = i as isize; let mut t = max_val;` (lib.rs:628-631)
        let mut last_col_id: isize = -1;
        let mut last_i2l1: isize = r[1];
        r.set(1, i as isize);
        let mut t: isize = max_val;

        let ch1 = s1[i - 1];

        // Origin Rust: `for (j, ch2) in s2.clone().enumerate()
        //               .map(|(j, ch2)| (j + 1, ch2)) { ... }` (lib.rs:633)
        let mut j: usize = 1;
        while j < len2 + 1
            invariant
                1 <= j <= len2 + 1,
                1 <= i <= len1,
                len1 == s1.len(),
                len2 == s2.len(),
                size == len2 + 2,
                r.len() == size,
                r1.len() == size,
                fr.len() == size,
                r[0] == max_val,
                r1[0] == max_val,
                forall|q: int| #![trigger r1[q]] 1 <= q < size ==>
                    (0 <= r1[q] <= ((i as int) - 1) + (q - 1) + 1),
                // the r prefix is the written region of row i; beyond it the old row values
                forall|q: int| #![trigger r[q]] 1 <= q < (j as int) + 1
                    ==> (0 <= r[q] <= (i as int) + (q - 1)),
                forall|q: int| #![trigger r[q]] 0 <= q < size
                    ==> (0 <= r[q] <= (len1 as int) + (len2 as int) + 8),
                forall|q: int| #![trigger fr[q]] 0 <= q < size
                    ==> (0 <= fr[q] <= (len1 as int) + (len2 as int) + 8),
                len2 == 0 ==> (r[(size - 1) as int] == i as isize),
                0 <= last_i2l1 <= (len1 as int) + (len2 as int) + 8,
                0 <= t <= (len1 as int) + (len2 as int) + 8,
                last_col_id == -1 || (1 <= last_col_id && last_col_id <= (j as int) - 1),
                tkeys.len() == tvals.len(),
                forall|q: int| #![trigger tvals[q]] 0 <= q < tvals.len()
                    ==> tvals[q] == -1 || (1 <= tvals[q] && tvals[q] <= (i as int) - 1),
                max_val >= 1,
                8 * (len1 as int) + 8 * (len2 as int) + 64 <= isize::MAX as int,
            decreases len2 + 1 - j,
        {
            let ch2 = s2[j - 1];
            // Origin Rust: `let diag = r1[j] + isize::from(ch1 != ch2);` (lib.rs:634)
            let bool1: isize = if ch1 != ch2 { 1 } else { 0 };
            let diag: isize = r1[j] + bool1;
            // Origin Rust: `let left = r[j] + 1;` (lib.rs:635)
            let left: isize = r[j] + 1;
            // Origin Rust: `let up = r1[j + 1] + 1;` (lib.rs:636)
            let up: isize = r1[j + 1] + 1;
            // Origin Rust: `let mut temp = min(diag, min(left, up));` (lib.rs:637)
            let mut temp: isize = if diag <= left && diag <= up {
                diag
            } else if left <= up {
                left
            } else {
                up
            };
            proof {
                // temp <= the initialization min -- diag/left/up are all linear bounds
            }
            if ch1 == ch2 {
                // Origin Rust: `last_col_id = j as isize; fr[j + 1] = r1[j - 1];
                //               t = last_i2l1;` (lib.rs:639-642)
                last_col_id = j as isize;
                fr.set(j + 1, r1[j - 1]);
                t = last_i2l1;
            } else {
                // Origin Rust: `let k = last_row_id.get(ch2).val; let l = last_col_id;`
                //               (lib.rs:644-645; HashMap -> assoc-list first match, default -1)
                let mut p: usize = 0;
                let mut found: bool = false;
                while p < tkeys.len()
                    invariant
                        p <= tkeys.len(),
                        found ==> p < tkeys.len(),
                        found ==> tkeys[p as int] == ch2,
                        tkeys.len() == tvals.len(),
                    decreases tkeys.len() - p,
                {
                    if tkeys[p] == ch2 {
                        found = true;
                        break;
                    }
                    p = p + 1;
                }
                let k: isize = if found { tvals[p] } else { -1 };
                proof {
                    if found {
                        assert(tvals[p as int] <= (i as int) - 1);
                    }
                    assert((k as int) <= (i as int) - 1);
                    assert((k as int) >= -1);
                }
                let l: isize = last_col_id;
                // Origin Rust: `if j as isize - l == 1 { let transpose = fr[j + 1]
                //               + (i as isize - k); temp = min(temp, transpose); }`
                //               (lib.rs:647-651)
                if j as isize - l == 1 {
                    let transpose: isize = fr[j + 1] + (i as isize - k);
                    temp = if transpose <= temp { transpose } else { temp };
                } else {
                    // Origin Rust: `else if i as isize - k == 1 { let transpose =
                    //               t + (j as isize - l); ... }` (lib.rs:650-653)
                    if i as isize - k == 1 {
                        let transpose: isize = t + (j as isize - l);
                        temp = if transpose <= temp { transpose } else { temp };
                    }
                }
            }
            // Origin Rust: `last_i2l1 = r[j + 1]; r[j + 1] = temp;` (lib.rs:656-657)
            last_i2l1 = r[j + 1];
            r.set(j + 1, temp);
            j = j + 1;
        }

        // Origin Rust: `last_row_id.get_mut(ch1).val = i as isize;` (lib.rs:659)
        let mut sp: usize = 0;
        let mut s_found: bool = false;
        while sp < tkeys.len()
            invariant
                sp <= tkeys.len(),
                s_found ==> sp < tkeys.len(),
                s_found ==> tkeys[sp as int] == ch1,
                tkeys.len() == tvals.len(),
            decreases tkeys.len() - sp,
        {
            if tkeys[sp] == ch1 {
                s_found = true;
                break;
            }
            sp = sp + 1;
        }
        if s_found {
            tvals.set(sp, i as isize);
        } else {
            tkeys.push(ch1);
            tvals.push(i as isize);
        }
        i = i + 1;
    }

    // Origin Rust: `r[len2 + 1] as usize` (lib.rs:662)
    proof {
        // Both phases unified: at loop exit r == row (i-1) (i is 1 + the completed rounds)
        assert(i == len1 + 1 || len1 == 0);
        if len1 == 0 {
            assert(i == 1);
            assert(r[(size - 1) as int] == ((size - 1) - 1) as isize) by {
                assert(r[(size - 1) as int] == ((size as int) - 2) as isize) by {
                    assert(forall|q: int| #![trigger r[q]] 1 <= q < size
                        ==> r[q] == q - 1);
                    assert(1 <= ((size - 1) as int) && ((size - 1) as int) < size) by {
                        assert(size == len2 + 2);
                    }
                }
            }
            assert((size - 1) - 1 == len2);
        } else {
            assert(i == len1 + 1);
            assert(r[(size - 1) as int] <= (len1 as int) + (len2 as int)) by {
                assert(forall|q: int| #![trigger r[q]] 1 <= q < size
                    ==> 0 <= r[q] <= ((i as int) - 1) + (q - 1)) by {}
                assert((size - 1) as int == len2 + 1);
                assert(1 <= ((size - 1) as int) && ((size - 1) as int) < size) by {
                    assert(size == len2 + 2);
                }
            }
        }
        assert(r[(size - 1) as int] >= 0);
    }
    r[size - 1] as usize
}

/* --- damerau_levenshtein (mirror of lib.rs:673-675) ----------------------- */


/// Origin Rust: `pub fn damerau_levenshtein(a: &str, b: &str) -> usize
///     { damerau_levenshtein_impl(a.chars(), a.chars().count(),
///      b.chars(), b.chars().count()) }` (under the [char] base it converges to a direct call).
/// Upstream doc (lib.rs:665-672):
///   Like optimal string alignment, but substrings can be edited an unlimited
///   number of times, and the triangle inequality holds.
///   use strsim::damerau_levenshtein;
///   assert_eq!(2, damerau_levenshtein("ab", "bca"));
pub fn damerau_levenshtein(a: &[char], b: &[char]) -> (r: usize)
    requires
        8 * (a.len() as int) + 8 * (b.len() as int) + 64 <= isize::MAX as int,
    ensures
        a.len() == 0 ==> r == b.len(),
        b.len() == 0 ==> r == a.len(),
        r <= a.len() + b.len(),
{
    damerau_levenshtein_impl(a, b)
}

/* --- normalized_damerau_levenshtein (mirror of lib.rs:689-698) ------------- */



/* =====================================================================
 * normalized_levenshtein / normalized_damerau_levenshtein (the f64 boundary)
 * ===================================================================== */

/// Origin Rust: `pub fn normalized_levenshtein(a, b) -> f64` (lib.rs:281-286).
/// The f64 layer takes no SMT obligation; the usize side (the levenshtein distance, lengths) cites the proven contracts.
/// Upstream doc (lib.rs:269-280):
///   Calculates a normalized score of the Levenshtein algorithm between 0.0 and
///   1.0 (inclusive), where 1.0 means the strings are the same.
///   use strsim::normalized_levenshtein;
///   assert!((normalized_levenshtein("kitten", "sitting") - 0.57142).abs() < 0.00001);
///   assert!((normalized_levenshtein("", "") - 1.0).abs() < 0.00001);
///   assert!(normalized_levenshtein("", "second").abs() < 0.00001);
///   assert!(normalized_levenshtein("first", "").abs() < 0.00001);
///   assert!((normalized_levenshtein("string", "string") - 1.0).abs() < 0.00001);
pub fn normalized_levenshtein(a: &[char], b: &[char]) -> (r: f64)
    requires
        a.len() + b.len() + 2 <= usize::MAX as int,
{
    if a.len() == 0 && b.len() == 0 {
        return 1.0;
    }
    let la = a.len();
    let lb = b.len();
    let lm = if la >= lb { la } else { lb };
    1.0 - ((levenshtein(a, b) as f64) / (lm as f64))
}

/// Origin Rust: `pub fn normalized_damerau_levenshtein(a, b) -> f64`.
/// The f64 tail takes no SMT obligation; the usize-side impl contract is proven.
/// Upstream doc (lib.rs:677-688):
///   Calculates a normalized score of the Damerau-Levenshtein algorithm between
///   0.0 and 1.0 (inclusive), where 1.0 means the strings are the same.
///   use strsim::normalized_damerau_levenshtein;
///   assert!((normalized_damerau_levenshtein("levenshtein", "löwenbräu") - 0.27272).abs() < 0.00001);
///   assert!((normalized_damerau_levenshtein("", "") - 1.0).abs() < 0.00001);
///   assert!(normalized_damerau_levenshtein("", "flower").abs() < 0.00001);
///   assert!(normalized_damerau_levenshtein("tree", "").abs() < 0.00001);
///   assert!((normalized_damerau_levenshtein("sunglasses", "sunglasses") - 1.0).abs() < 0.00001);
pub fn normalized_damerau_levenshtein(a: &[char], b: &[char]) -> (r: f64)
    requires
        8 * (a.len() as int) + 8 * (b.len() as int) + 64 <= isize::MAX as int,
{
    if a.len() == 0 && b.len() == 0 {
        1.0
    } else {
        let len1 = a.len();
        let len2 = b.len();
        let dist = damerau_levenshtein_impl(a, b);
        let maxlen = if len1 >= len2 { len1 } else { len2 };
        1.0 - (dist as f64) / (maxlen as f64)
    }
}


/* =====================================================================
 * bigrams / sorensen_dice (mirror of lib.rs:701-750)
 * ===================================================================== */

/// Origin Rust: `fn bigrams(s: &str) -> impl Iterator<Item = (char, char)> + '_`
/// (lib.rs:701-703). spec twin: the i-th bigram = (s[i], s[i+1]).
pub open spec fn nth_bigram(s: Seq<char>, i: int) -> (char, char) {
    (s.index(i), s.index(i + 1))
}

/* --- multiset total-sum spec family (same shape as the flag_count lemma family) --- */

/// Assoc-list entries = Seq<((char,char), usize)>: the value sum over [lo, hi).
pub open spec fn entries_sum(s: Seq<((char, char), usize)>, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo {
        0
    } else {
        entries_sum(s, lo, hi - 1) + (s.index(hi - 1).1 as int)
    }
}


/* --- UTF-8 byte length of a char (the String::len base mapping) ----------------- */

pub fn char_utf8_len(c: char) -> (r: usize)
    ensures
        1 <= r <= 4,
{
    let v = c as u32;
    if v < 128 {
        1
    } else if v < 2048 {
        2
    } else if v < 65536 {
        3
    } else {
        4
    }
}

/* --- Vec<char> equality (String equality mirror: same length + pointwise equal) - */

fn chars_eq(fa: &Vec<char>, fb: &Vec<char>) -> (eq: bool)
    ensures
        eq <==> (fa@.len() == fb@.len()
            && forall|q: int| 0 <= q < fa@.len() ==> fa@[q] == fb@[q]),
{
    if fa.len() != fb.len() {
        return false;
    }
    let mut i: usize = 0;
    let mut all_eq = true;
    while i < fa.len()
        invariant
            i <= fa.len(),
            fa.len() == fb.len(),
            all_eq <==> (forall|q: int| 0 <= q < i ==> fa@[q] == fb@[q]),
        decreases fa.len() - i,
    {
        all_eq = all_eq && fa[i] == fb[i];
        i = i + 1;
    }
    all_eq
}

/* --- sorensen_dice body (mirror of lib.rs:717-750) ---------------------------- */

/// Origin Rust: mirror of upstream lib.rs:717-750
/// `pub fn sorensen_dice(a: &str, b: &str) -> f64` ([char] base).
/// Upstream doc (lib.rs:705-716):
///   Calculates a Sørensen-Dice similarity distance using bigrams.
///   See <https://en.wikipedia.org/wiki/S%C3%B8rensen%E2%80%93Dice_coefficient>.
///   use strsim::sorensen_dice;
///   assert_eq!(1.0, sorensen_dice("", ""));
///   assert_eq!(0.0, sorensen_dice("", "a"));
///   assert_eq!(0.0, sorensen_dice("french", "quebec"));
///   assert_eq!(1.0, sorensen_dice("ferris", "ferris"));
///   assert_eq!(0.8888888888888888, sorensen_dice("feris", "ferris"));
pub fn sorensen_dice(a: &[char], b: &[char]) -> (r: f64)
    requires
        4 * (a.len() as int) + 4 * (b.len() as int) + 8 <= usize::MAX as int,
{
    /* Origin Rust: `let a: String = a.chars().filter(|&x| !char::is_whitespace(x)).collect();`
     * (lib.rs:721-722) -- the String base is decomposed into Vec<char> + a byte-length count. */
    let mut fa: Vec<char> = Vec::with_capacity(a.len());
    let mut fa_bytes: usize = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            fa.len() <= i,
            fa_bytes <= 4 * fa.len(),
            4 * (a.len() as int) + 4 * (b.len() as int) + 8 <= usize::MAX as int,
        decreases a.len() - i,
    {
        if !char::is_whitespace(a[i]) {
            let bl = char_utf8_len(a[i]);
            fa.push(a[i]);
            fa_bytes = fa_bytes + bl;
        }
        i = i + 1;
    }

    let mut fb: Vec<char> = Vec::with_capacity(b.len());
    let mut fb_bytes: usize = 0;
    let mut j: usize = 0;
    while j < b.len()
        invariant
            j <= b.len(),
            fb.len() <= j,
            fb_bytes <= 4 * fb.len(),
            4 * (a.len() as int) + 4 * (b.len() as int) + 8 <= usize::MAX as int,
        decreases b.len() - j,
    {
        if !char::is_whitespace(b[j]) {
            let bl = char_utf8_len(b[j]);
            fb.push(b[j]);
            fb_bytes = fb_bytes + bl;
        }
        j = j + 1;
    }

    /* Origin Rust: `if a == b { return 1.0; }` (lib.rs:724-726) */
    let eq = chars_eq(&fa, &fb);
    if eq {
        return 1.0;
    }

    /* Origin Rust: `if a.len() < 2 || b.len() < 2 { return 0.0; }` (lib.rs:728-730)
     * (the String::len byte-length semantics) */
    if fa_bytes < 2 || fb_bytes < 2 {
        return 0.0;
    }
    assert(fa.len() >= 1);
    assert(fb.len() >= 1);

    /* Origin Rust: `let mut a_bigrams: HashMap<(char,char), usize> = HashMap::new();
     * for bigram in bigrams(&a) { *a_bigrams.entry(bigram).or_insert(0) += 1; }`
     * (lib.rs:732-736) -- HashMap -> the assoc list Vec<((char,char), usize)> (linear first match) */
    let mut a_bigrams: Vec<((char, char), usize)> = Vec::new();
    let mut ci: usize = 0;
    while ci + 1 < fa.len()
        invariant
            ci + 1 <= fa.len(),
            a_bigrams.len() <= ci,
            entries_sum(a_bigrams@, 0, a_bigrams.len() as int) == ci as int,
            forall|q: int| 0 <= q < a_bigrams.len() ==> 0 <= a_bigrams[q].1,
            fa.len() >= 1,
            4 * (a.len() as int) + 4 * (b.len() as int) + 8 <= usize::MAX as int,
            fa.len() as int <= a.len() as int,
        decreases fa.len() - ci,
    {
        let key: (char, char) = (fa[ci], fa[ci + 1]);
        let mut p: usize = 0;
        let mut found: bool = false;
        while p < a_bigrams.len()
            invariant
                p <= a_bigrams.len(),
                found ==> p < a_bigrams.len(),
                found ==> a_bigrams@[p as int].0 == key,
                a_bigrams.len() <= ci,
                entries_sum(a_bigrams@, 0, a_bigrams.len() as int) == ci as int,
                forall|q: int| 0 <= q < a_bigrams.len() ==> 0 <= a_bigrams[q].1,
            decreases a_bigrams.len() - p,
        {
            let e = a_bigrams[p];
            if e.0 == key {
                found = true;
                break;
            }
            p = p + 1;
        }
        if found {
            proof {
                assert(a_bigrams[p as int] == a_bigrams@[p as int]);
                entries_sum_ge_entry(a_bigrams@, p as int);
                assert(a_bigrams@[p as int].1 as int <= ci as int);
                entries_sum_set_plus_one(
                    a_bigrams@,
                    0,
                    a_bigrams.len() as int,
                    p as int,
                );
                // newv = e.1 + 1 value range: e.1 <= the sum == ci, ci + 2 <= fa.len() (loop head)
                assert(ci as int + 1 <= (fa.len() as int) - 1);
                assert(fa.len() as int <= (a.len() as int));
                assert(4 * (a.len() as int) + 4 * (b.len() as int) + 8
                    <= usize::MAX as int);
            }
            let e = a_bigrams[p];
            let newv = e.1 + 1;
            a_bigrams.set(p, (key, newv));
        } else {
            proof {
                entries_sum_push_add(a_bigrams@, key, 1);
            }
            a_bigrams.push((key, 1));
        }
        ci = ci + 1;
    }
    assert(entries_sum(a_bigrams@, 0, a_bigrams.len() as int)
        == (fa.len() as int) - 1) by {
        assert(ci + 1 == fa.len() || fa.len() == 0);
    }

    /* Origin Rust: `let mut intersection_size = 0; for bigram in bigrams(&b) {
     * a_bigrams.entry(bigram).and_modify(|bi| { if *bi > 0 { *bi -= 1;
     * intersection_size += 1; } }); }` (lib.rs:738-747) */
    let mut intersection_size: usize = 0;
    let mut cj: usize = 0;
    while cj + 1 < fb.len()
        invariant
            cj + 1 <= fb.len(),
            intersection_size <= cj,
            entries_sum(a_bigrams@, 0, a_bigrams.len() as int)
                == (fa.len() as int) - 1 - (intersection_size as int),
            forall|q: int| 0 <= q < a_bigrams.len() ==> 0 <= a_bigrams[q].1,
            fa.len() >= 1,
            fa.len() as int <= a.len() as int,
            fb.len() as int <= b.len() as int,
            4 * (a.len() as int) + 4 * (b.len() as int) + 8 <= usize::MAX as int,
        decreases fb.len() - cj,
    {
        let key: (char, char) = (fb[cj], fb[cj + 1]);
        let mut p: usize = 0;
        let mut found: bool = false;
        while p < a_bigrams.len()
            invariant
                p <= a_bigrams.len(),
                found ==> p < a_bigrams.len(),
                found ==> a_bigrams@[p as int].0 == key,
                entries_sum(a_bigrams@, 0, a_bigrams.len() as int)
                    == (fa.len() as int) - 1 - (intersection_size as int),
                forall|q: int| 0 <= q < a_bigrams.len() ==> 0 <= a_bigrams[q].1,
            decreases a_bigrams.len() - p,
        {
            let e = a_bigrams[p];
            if e.0 == key {
                found = true;
                break;
            }
            p = p + 1;
        }
        if found {
            let e = a_bigrams[p];
            if e.1 > 0 {
                proof {
                    assert(a_bigrams[p as int] == a_bigrams@[p as int]);
                    entries_sum_set_minus_one(
                        a_bigrams@,
                        0,
                        a_bigrams.len() as int,
                        p as int,
                    );
                }
                let newv = e.1 - 1;
                a_bigrams.set(p, (key, newv));
                intersection_size = intersection_size + 1;
            }
        }
        cj = cj + 1;
    }

    /* Origin Rust: `(2 * intersection_size) as f64 / (a.len() + b.len() - 2) as f64`
     * (lib.rs:749) */
    let num = 2 * intersection_size;
    let den = fa_bytes + fb_bytes - 2;
    proof {
        // intersection size <= processed b-bigram count <= fb.len() <= b.len()
        assert(cj + 1 == fb.len());
        assert(intersection_size as int <= (fb.len() as int));
        assert((fb.len() as int) <= (b.len() as int));
        // num = 2*i <= 4*i <= 4*b <= MAX-4a-8
        assert(4 * (intersection_size as int) <= 4 * (b.len() as int));
        assert(4 * (b.len() as int)
            <= (usize::MAX as int) - (4 * (a.len() as int) + 8));
        assert((num as int) <= 4 * (b.len() as int));
        assert((num as int) <= (usize::MAX as int) - 8);
        // den = fa_bytes + fb_bytes - 2: byte length <= 4*char count => the two sides sum to <= 4a+4b <= MAX-8
        assert(fa_bytes <= 4 * fa.len());
        assert(fb_bytes <= 4 * fb.len());
        assert((fa.len() as int) <= (a.len() as int));
        assert((fa_bytes as int) + (fb_bytes as int)
            <= 4 * ((a.len() as int) + (b.len() as int)));
        assert(fa_bytes >= 2);
        assert(fb_bytes >= 2);
        assert(den >= 2);
        assert((den as int) <= (usize::MAX as int) - 10);
    }
    (num as f64) / (den as f64)
}


// =========================================================================
// Proof lemmas (moved to the end of the file; only the order changed).
// Kept-in-place exceptions (banners at their original positions): the
// flag_count family and the two nonlinear boosters, whose relocation past
// the exec fns measuredly flips the rlimit-marginal inner-loop query of
// generic_damerau_levenshtein into a deterministic rlimit error. This
// crate carries no SPEC-DOC MISMATCH mark: the triage closed strsim as a
// zero-findings crate (0 code-bug / 0 doc-inconsistency, nothing to
// annotate).
proof fn diff_count_step(a: Seq<char>, b: Seq<char>, i: int)
    requires
        0 <= i,
        i < a.len(),
        i < b.len(),
    ensures
        diff_count(a, b, i + 1) == diff_count(a, b, i)
            + (if a.index(i) != b.index(i) {
                1nat
            } else {
                0nat
            }),
{
    reveal_with_fuel(diff_count, 2);
}

proof fn diff_count_le(a: Seq<char>, b: Seq<char>, i: int)
    requires i >= 0,
    ensures diff_count(a, b, i) <= i as nat,
    decreases i,
{
    if i == 0 {
    } else {
        diff_count_le(a, b, i - 1);
        reveal_with_fuel(diff_count, 2);
    }
}

proof fn entries_sum_nonneg(s: Seq<((char, char), usize)>, lo: int, hi: int)
    requires
        lo <= hi,
        forall|q: int| lo <= q < hi ==> 0 <= s.index(q).1,
    ensures entries_sum(s, lo, hi) >= 0
    decreases hi - lo,
{
    if hi <= lo {
    } else {
        entries_sum_nonneg(s, lo, hi - 1);
        reveal_with_fuel(entries_sum, 2);
    }
}

proof fn entries_sum_extend_one(s: Seq<((char, char), usize)>, lo: int, hi: int)
    requires
        lo <= hi,
        hi < s.len(),
    ensures
        entries_sum(s, lo, hi + 1)
            == entries_sum(s, lo, hi) + (s.index(hi).1 as int),
{
    reveal_with_fuel(entries_sum, 2);
}

proof fn entries_sum_monotone(
    s: Seq<((char, char), usize)>,
    lo: int,
    mid: int,
    hi: int,
)
    requires
        lo <= mid,
        mid <= hi,
        forall|q: int| lo <= q < hi ==> 0 <= s.index(q).1,
    ensures entries_sum(s, lo, mid) <= entries_sum(s, lo, hi)
    decreases hi - mid,
{
    if mid == hi {
    } else {
        entries_sum_monotone(s, lo, mid, hi - 1);
        reveal_with_fuel(entries_sum, 2);
    }
}

/// A single entry value <= the whole-segment value sum over [0, len) (nonnegative sum + single-point inclusion + monotonicity).
proof fn entries_sum_ge_entry(s: Seq<((char, char), usize)>, p: int)
    requires
        0 <= p < s.len(),
        forall|q: int| 0 <= q < s.len() ==> 0 <= s.index(q).1,
    ensures s.index(p).1 as int <= entries_sum(s, 0, s.len() as int)
{
    entries_sum_nonneg(s, 0, p);
    entries_sum_extend_one(s, 0, p);
    entries_sum_monotone(s, 0, p + 1, s.len() as int);
}

/// Update slot p >= hi (after hi): the segment sum is unchanged.
proof fn entries_sum_update_at_or_beyond(
    s: Seq<((char, char), usize)>,
    lo: int,
    hi: int,
    p: int,
    u: ((char, char), usize),
)
    requires
        0 <= lo,
        lo <= hi,
        hi <= p,
        0 <= p,
        p < s.len(),
    ensures entries_sum(s.update(p, u), lo, hi) == entries_sum(s, lo, hi)
    decreases hi - lo,
{
    if hi <= lo {
    } else {
        entries_sum_update_at_or_beyond(s, lo, hi - 1, p, u);
        vstd::seq::lemma_seq_update_same(s, p, u);
        assert(s.update(p, u).index(hi - 1) == s.index(hi - 1));
        reveal_with_fuel(entries_sum, 2);
    }
}

proof fn entries_sum_update_before(
    s: Seq<((char, char), usize)>,
    lo: int,
    hi: int,
    p: int,
    u: ((char, char), usize),
)
    requires
        p < lo,
        0 <= lo,
        lo <= hi,
        hi <= s.len(),
    ensures entries_sum(s.update(p, u), lo, hi) == entries_sum(s, lo, hi)
    decreases hi - lo,
{
    if hi <= lo {
    } else {
        entries_sum_update_before(s, lo, hi - 1, p, u);
        vstd::seq::lemma_seq_update_different(s, hi - 1, p, u);
        assert(s.update(p, u).index(hi - 1) == s.index(hi - 1));
        reveal_with_fuel(entries_sum, 2);
    }
}

/// Update slot p (old value v, new value v+1): the segment sum gains +1.
proof fn entries_sum_set_plus_one(
    s: Seq<((char, char), usize)>,
    lo: int,
    hi: int,
    p: int,
)
    requires
        0 <= lo,
        lo <= p,
        p < hi,
        hi <= s.len(),
        (s.index(p).1 as int) < usize::MAX as int,
    ensures
        entries_sum(
            s.update(p, (s.index(p).0, (s.index(p).1 + 1) as usize)),
            lo,
            hi,
        ) == entries_sum(s, lo, hi) + 1,
    decreases hi - p,
{
    let u = (s.index(p).0, (s.index(p).1 + 1) as usize);
    if p == hi - 1 {
        entries_sum_update_at_or_beyond(s, lo, hi - 1, p, u);
        vstd::seq::lemma_seq_update_same(s, p, u);
        assert(s.update(p, u).index(p).1 == u.1);
        reveal_with_fuel(entries_sum, 2);
    } else {
        entries_sum_set_plus_one(s, lo, hi - 1, p);
        vstd::seq::lemma_seq_update_different(s, hi - 1, p, u);
        assert(s.update(p, u).index(hi - 1) == s.index(hi - 1));
        reveal_with_fuel(entries_sum, 2);
    }
}

/// Update slot p (old value v >= 1, new value v-1): the segment sum loses 1.
proof fn entries_sum_set_minus_one(
    s: Seq<((char, char), usize)>,
    lo: int,
    hi: int,
    p: int,
)
    requires
        0 <= lo,
        lo <= p,
        p < hi,
        hi <= s.len(),
        1 <= s.index(p).1,
    ensures
        entries_sum(
            s.update(p, (s.index(p).0, (s.index(p).1 - 1) as usize)),
            lo,
            hi,
        ) == entries_sum(s, lo, hi) - 1,
    decreases hi - p,
{
    let u = (s.index(p).0, (s.index(p).1 - 1) as usize);
    if p == hi - 1 {
        entries_sum_update_at_or_beyond(s, lo, hi - 1, p, u);
        vstd::seq::lemma_seq_update_same(s, p, u);
        assert(s.update(p, u).index(p).1 == u.1);
        reveal_with_fuel(entries_sum, 2);
    } else {
        entries_sum_set_minus_one(s, lo, hi - 1, p);
        vstd::seq::lemma_seq_update_different(s, hi - 1, p, u);
        assert(s.update(p, u).index(hi - 1) == s.index(hi - 1));
        reveal_with_fuel(entries_sum, 2);
    }
}

proof fn entries_sum_push_add(
    s: Seq<((char, char), usize)>,
    k: (char, char),
    v: usize,
)
    ensures
        entries_sum(s.push((k, v)), 0, ((s.len() + 1) as int))
            == entries_sum(s, 0, s.len() as int) + (v as int),
{
    let n = s.len() as int;
    let new = s.push((k, v));
    assert(new.index(n) == (k, v));
    assert(forall|q: int| 0 <= q < n ==> new.index(q) == s.index(q));
    prefix_agree_sum(new, s, n);
    reveal_with_fuel(entries_sum, 2);
}

proof fn prefix_agree_sum(x: Seq<((char, char), usize)>, y: Seq<((char, char), usize)>, n: int)
    requires
        0 <= n,
        x.len() >= n,
        y.len() >= n,
        forall|q: int| 0 <= q < n ==> x.index(q) == y.index(q),
    ensures entries_sum(x, 0, n) == entries_sum(y, 0, n)
    decreases n,
{
    if n <= 0 {
    } else {
        prefix_agree_sum(x, y, n - 1);
        assert(x.index(n - 1) == y.index(n - 1));
        reveal_with_fuel(entries_sum, 2);
    }
}

} // verus!
