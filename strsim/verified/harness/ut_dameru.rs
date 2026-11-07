//! damerau family + sorensen_dice UT
//! consuming harness.
//! Coverage: the empty-input contract exemplars of code/src/lib.rs:1137-1154
//! damerau_levenshtein_empty/first_empty/second_empty (closed exactly via the
//! impl contract) +
//! the empty-input exemplars of generic_damerau (lib.rs:344-347 doctest) +
//! full-execution L0 smokes of normalized_damerau(681-687) and sorensen_dice
//! (lib.rs:708-716/1251-1302)
//! (the f64 expected-value layer goes through out/verus-bugfinder runtime
//! re-verification).

#[path = "../src/lib.rs"]
mod strsim_v;

use vstd::prelude::*;

verus! {

fn run_ut_damerau_empty() {
    // UT damerau_levenshtein_empty (lib.rs:1137-1139): == 0
    let r = strsim_v::damerau_levenshtein(&[], &[]);
    assert(r == 0);

    // UT damerau_levenshtein_first_empty (lib.rs:1147-1149): == 7
    let r = strsim_v::damerau_levenshtein(
        &[],
        &['d', 'a', 'm', 'e', 'r', 'a', 'u'],
    );
    assert(r == 7);

    // UT damerau_levenshtein_second_empty (lib.rs:1152-1154): == 7
    let r = strsim_v::damerau_levenshtein(
        &['d', 'a', 'm', 'e', 'r', 'a', 'u'],
        &[],
    );
    assert(r == 7);
}

fn run_ut_generic_damerau_empty() {
    // generic_damerau_levenshtein empty-input contract (the early-return slots of lib.rs:356-361)
    let g0 = strsim_v::generic_damerau_levenshtein(&[], &[]);
    assert(g0 == 0);
    let g1 = strsim_v::generic_damerau_levenshtein(
        &[],
        &['a', 'b', 'c'],
    );
    assert(g1 == 3);
    let g2 = strsim_v::generic_damerau_levenshtein(
        &['a', 'b', 'c'],
        &[],
    );
    assert(g2 == 3);
}

fn run_ut_damerau_value_smoke() {
    proof {
        // small-constant product requires bridge (z3 does not automatically evaluate spec-mode products)
        assert(strsim_v::total_len(2, 2) + 8 <= usize::MAX as int) by {
            assert(strsim_v::total_len(2, 2) == 16);
        }
        assert(2 * 2 + 2 * 2 + 1 <= usize::MAX as int) by {}
    }
    // Full L0 execution (the main DP path): the exact value layer goes through
    // runtime re-verification
    // (upstream UTs: damerau_levenshtein_same/diff/reversed/unequal... lib.rs:1141-1216)
    let _ = strsim_v::damerau_levenshtein(
        &['d', 'a', 'm', 'e', 'r', 'a', 'u'],
        &['d', 'a', 'm', 'e', 'r', 'a', 'u'],
    );
    let _ = strsim_v::generic_damerau_levenshtein(
        &['1', '2'],
        &['2', '3'],
    );

    // normalized_damerau_levenshtein (lib.rs:689-698): f64 takes no SMT
    // obligation;
    // empty/non-empty calls are executed (including the machine check of the maxlen>=1 divisor branch)
    let _ = strsim_v::normalized_damerau_levenshtein(&[], &[]);
    let _ = strsim_v::normalized_damerau_levenshtein(
        &['l', 'e', 'v', 'e', 'n', 's', 'h', 't', 'e', 'i', 'n'],
        &['l', 'ö', 'w', 'e', 'n', 'b', 'r', 'ä', 'u'],
    );
}

fn run_ut_sorensen_smoke() {
    // sorensen_dice (lib.rs:717-750): full L0 execution of every branch
    // (the Eq early return 1.0 / the byte-length <2 early return 0.0 / the multiset main path)
    let _ = strsim_v::sorensen_dice(&[], &[]);
    let _ = strsim_v::sorensen_dice(&['a'], &['a']);
    let _ = strsim_v::sorensen_dice(&['a'], &['b']);
    let _ = strsim_v::sorensen_dice(&['f', 'e', 'r', 'r', 'i', 's'], &['f', 'e', 'r', 'i', 's']);
    // the multi-word smoke of UT sorensen_dice_all (lib.rs:1251-1302, the f64 value layer via runtime re-verification)
    let _ = strsim_v::sorensen_dice(
        &['a', 'p', 'p', 'l', 'e', ' ', 'e', 'v', 'e', 'n', 't'],
        &['a', 'p', 'p', 'l', 'e', ' ', ' ', ' ', ' ', 'e', 'v', 'e', 'n', 't'],
    );
    // multibyte: the byte-length base path (fa_bytes semantics)
    let _ = strsim_v::sorensen_dice(&['\u{9999}', '\u{8349}'], &['\u{8349}', '\u{9999}']);
}

}

fn main() {
    run_ut_damerau_empty();
    run_ut_generic_damerau_empty();
    run_ut_damerau_value_smoke();
    run_ut_sorensen_smoke();
}
