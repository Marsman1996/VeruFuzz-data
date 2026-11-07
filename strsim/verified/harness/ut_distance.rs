//! distance-family (levenshtein / osa / jaro
//! families) UT assertion theorems. Coverage follows the src contract
//! depth:
//! the empty-input exactness theorems of levenshtein/osa
//! (lib.rs:1019-1026 / 1064-1071 fully machine-checked) + L0 smokes of
//! concrete jaro-family calls (the f64 expected-value layer goes through
//! out/verus-bugfinder runtime re-verification).

#[path = "../src/lib.rs"]
mod strsim_v;

use vstd::prelude::*;

verus! {

fn run_ut_levenshtein() {
    // UT levenshtein_empty (lib.rs:986-988): 0
    let r = strsim_v::levenshtein(&[], &[]);
    assert(r == 0);

    // UT levenshtein_first_empty (lib.rs:1019-1021): == 7
    let r = strsim_v::levenshtein(
        &[],
        &['s', 'i', 't', 't', 'i', 'n', 'g'],
    );
    assert(r == 7);

    // UT levenshtein_second_empty (lib.rs:1023-1026): == 6
    let r = strsim_v::levenshtein(
        &['k', 'i', 't', 't', 'e', 'n'],
        &[],
    );
    assert(r == 6);
}

fn run_ut_osa() {
    // UT osa_distance_empty (lib.rs:1054-1056): 0
    let r = strsim_v::osa_distance(&[], &[]);
    assert(r == 0);

    // UT osa_distance_first_empty (lib.rs:1064-1066): == 7
    let r = strsim_v::osa_distance(
        &[],
        &['d', 'a', 'm', 'e', 'r', 'a', 'u'],
    );
    assert(r == 7);

    // UT osa_distance_second_empty (lib.rs:1068-1071): == 7
    let r = strsim_v::osa_distance(
        &['d', 'a', 'm', 'e', 'r', 'a', 'u'],
        &[],
    );
    assert(r == 7);
}

fn run_ut_jaro_smoke() {
    // jaro family: L0 calls with concrete inputs (obligation = panic-free
    // execution); f64 expected-value assertions have no SMT semantics in
    // Verus;
    // the corresponding UT assertions are carried by runtime re-verification
    // (out/verus-bugfinder/).
    // Precondition satisfaction (the two lengths sit far below the usize bound) is machine-checked at each call.
    let _ = strsim_v::jaro(&[], &[]);
    let _ = strsim_v::jaro(&['a'], &[]);
    let _ = strsim_v::jaro(
        &['a', ' ', 'j', 'k', 'e'],
        &['j', 'a', 'n', 'e', ' ', 'a', ' ', 'k'],
    );
    let _ = strsim_v::jaro_winkler(
        &['c', 'h', 'e', 'e', 's', 'e', 'b', 'u', 'r', 'g', 'e', 'r'],
        &['c', 'h', 'e', 'e', 's', 'e', ' ', 'f', 'r', 'i', 'e', 's'],
    );
    let _ = strsim_v::jaro_winkler(&[], &[]);
    let _ = strsim_v::generic_jaro(
        &['x', 'y'],
        &['x', 'y', 'z'],
    );
    let _ = strsim_v::generic_jaro_winkler(&['a'], &['a']);
}

}

fn main() {
    run_ut_levenshtein();
    run_ut_osa();
    run_ut_jaro_smoke();
}
