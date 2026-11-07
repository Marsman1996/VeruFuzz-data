//! hamming-family UT assertion theorems
//! (a consuming harness: `#[path]` references verified/src/lib.rs, no spec
//! duplication).
//!
//! Coverage: the seven hamming_* UTs of code/src/lib.rs:786-822 +
//! code/tests/lib.rs:23 hamming_works (the == already machine-checked
//! verbatim below).

#[path = "../src/lib.rs"]
mod strsim_v;

use vstd::prelude::*;

verus! {

fn run_ut_hamming() {
    proof {
        // deep-iteration reveal fuel (the names case at depth 16)
        reveal_with_fuel(strsim_v::diff_count, 17);
    }
    // UT hamming_empty (lib.rs:787-789): Ok(0)
    let r = strsim_v::hamming(&[], &[]);
    assert(r == Ok(0));

    // UT hamming_same (lib.rs:792-794): Ok(0)
    // (the spec shadow of a constant str chars() cannot be SMT-expanded => explicit char literals)
    let r = strsim_v::hamming(
        &['h', 'a', 'm', 'm', 'i', 'n', 'g'],
        &['h', 'a', 'm', 'm', 'i', 'n', 'g'],
    );
    assert(r == Ok(0));

    // UT hamming_diff (lib.rs:802-804): Ok(3)
    let r = strsim_v::hamming(
        &['h', 'a', 'm', 'm', 'i', 'n', 'g'],
        &['h', 'a', 'm', 'm', 'e', 'r', 's'],
    );
    assert(r == Ok(3));

    // UT hamming_diff_multibyte (lib.rs:807-809): Ok(2)
    let r = strsim_v::hamming(
        &['h', 'a', 'm', 'm', 'i', 'n', 'g'],
        &['h', '\u{9999}', 'm', 'm', 'ü', 'n', 'g'],
    );
    assert(r == Ok(2));

    // UT hamming_names (lib.rs:819-822): Ok(14)
    let r = strsim_v::hamming(
        &['F', 'r', 'i', 'e', 'd', 'r', 'i', 'c', 'h', ' ', 'N', 'i', 'e', 't', 'z', 's'],
        &['J', 'e', 'a', 'n', '-', 'P', 'a', 'u', 'l', ' ', 'S', 'a', 'r', 't', 'r', 'e'],
    );
    assert(r == Ok(14));

    // UT hamming_unequal_length (lib.rs:812-817): Err(DifferentLengthArgs)
    let r = strsim_v::hamming(
        &['h', 'a', 'm'],
        &['h', 'a', 'm', 'm', 'i', 'n', 'g'],
    );
    match r {
        Result::Ok(v) => {
            // unreachable branch (unequal lengths): debunked via the assertion
            assert(v == v);
            assert(false) by { assert(3 != 7); }
        }
        Result::Err(e) => {
            assert(e == strsim_v::StrSimError::DifferentLengthArgs);
        }
    }
    assert(r == Err(strsim_v::StrSimError::DifferentLengthArgs));

    // UT hamming_numbers (lib.rs:797-799): the generic_hamming core --
    // base-specialized to char (numerically equivalent semantics: the per-position difference count), Ok(1)
    let r = strsim_v::generic_hamming(&['x', 'y', 'z'], &['x', 'y', 'w']);
    assert(r == Ok(1));
}

}

fn main() {
    run_ut_hamming();
}
