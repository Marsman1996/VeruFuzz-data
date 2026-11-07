//! num-integer **harness zone** -- the div-family UT assertion transcriptions
//! (the two-zone split from src/lib.rs): the 24
//! (n, d) example pairs of the doc # Examples of test_div_rem /
//! test_div_mod_floor / test_ceil (8 pairs x 3 families, all negative
//! divisors included) + the pure UT assertion aggregation functions.
//!
//! Reference-style note: the UT examples use the direct example-evaluation
//! shape -- the obligations discharge pair by pair via the inlined
//! `a / b`, `a % b` (z3 fully evaluates concrete values) -- and depend on
//! no shared model of the src side; the obligation anchors (the expected
//! errors of the div-family L0 transcriptions), the fix refutations and
//! the witnesses all stay in src/lib.rs.
//!
//! Run: VERUS_Z3_PATH=<z3> <verus> database/num-integer/verified/harness/ut_div.rs
//! Reading the output: expected 9 verified / 0 errors.

use vstd::prelude::*;

verus! {

/// UT (lib.rs:634-656 test_div_rem + the doc # Examples lib.rs:252-261) assertion transcription:
/// the truncated results of the 8 (n, d) pairs equal the doc expectations one by one (the direct
/// example-evaluation shape -- z3 fully evaluates the machine `/`, `%` on concrete values; the identity obligations forward to the call sites in the same shape).
// Split into two 4-example functions: the whole 8-clause disjunction trips an ambiguity beyond the z3 instantiation budget (4 clauses prove in full).
exec fn div_rem_pair_a(a: i64, b: i64, eq: i64, er: i64) -> (ret: bool)
    requires
        (a == 8 && b == 3 && eq == 2 && er == 2)
            || (a == 8 && b == (0-3i64) && eq == (0-2i64) && er == 2)
            || (a == (0-8i64) && b == 3 && eq == (0-2i64) && er == (0-2i64))
            || (a == (0-8i64) && b == (0-3i64) && eq == 2 && er == (0-2i64)),
    ensures
        a == 8 && b == 3 ==> ret == true,
        a == 8 && b == (0-3i64) ==> ret == true,
        a == (0-8i64) && b == 3 ==> ret == true,
        a == (0-8i64) && b == (0-3i64) ==> ret == true,
{
    let (q, r) = (a / b, a % b);   // lib.rs:592
    q == eq && r == er
}

exec fn div_rem_pair_b(a: i64, b: i64, eq: i64, er: i64) -> (ret: bool)
    requires
        (a == 1 && b == 2 && eq == 0 && er == 1)
            || (a == 1 && b == (0-2i64) && eq == 0 && er == 1)
            || (a == (0-1i64) && b == 2 && eq == 0 && er == (0-1i64))
            || (a == (0-1i64) && b == (0-2i64) && eq == 0 && er == (0-1i64)),
    ensures
        a == 1 && b == 2 ==> ret == true,
        a == 1 && b == (0-2i64) ==> ret == true,
        a == (0-1i64) && b == 2 ==> ret == true,
        a == (0-1i64) && b == (0-2i64) ==> ret == true,
{
    let (q, r) = (a / b, a % b);   // lib.rs:592
    q == eq && r == er
}

pub exec fn ut_test_div_rem_examples() -> (ok: bool)
    ensures ok == true,
{
div_rem_pair_a(8i64, 3i64, 2i64, 2i64)
        && div_rem_pair_a(8i64, 0-3i64, 0-2i64, 2i64)
        && div_rem_pair_a(0-8i64, 3i64, 0-2i64, 0-2i64)
        && div_rem_pair_a(0-8i64, 0-3i64, 2i64, 0-2i64)
        && div_rem_pair_b(1i64, 2i64, 0i64, 1i64)
        && div_rem_pair_b(1i64, 0-2i64, 0i64, 1i64)
        && div_rem_pair_b(0-1i64, 2i64, 0i64, 0-1i64)
        && div_rem_pair_b(0-1i64, 0-2i64, 0i64, 0-1i64)
}

/// UT (lib.rs:658-681 test_div_mod_floor + the doc # Examples) assertion transcription:
/// the floor family's 8 (n, d) pairs (negative divisors included) equal the doc expectations one by one.
pub exec fn ut_test_div_mod_floor_examples() -> (ok: bool)
    ensures ok == true,
{
    div_floor_pair_a(8i64, 3i64, 2i64, 2i64)
        && div_floor_pair_a(8i64, 0-3i64, 0-3i64, 0-1i64)
        && div_floor_pair_a(0-8i64, 3i64, 0-3i64, 1i64)
        && div_floor_pair_a(0-8i64, 0-3i64, 2i64, 0-2i64)
        && div_floor_pair_b(1i64, 2i64, 0i64, 1i64)
        && div_floor_pair_b(1i64, 0-2i64, 0-1i64, 0-1i64)
        && div_floor_pair_b(0-1i64, 2i64, 0-1i64, 1i64)
        && div_floor_pair_b(0-1i64, 0-2i64, 0i64, 0-1i64)
}

/// The concrete instance kernel (same as the div_mod_floor macro-expansion body, doc-example-level evidence):
/// the negative-divisor doc expectations are fully covered here (the universal contract is limited to positive divisors).
exec fn div_floor_pair_a(a: i64, b: i64, eq: i64, er: i64) -> (ret: bool)
    requires
        (a == 8 && b == 3 && eq == 2 && er == 2)
            || (a == 8 && b == (-3i64) && eq == (-3i64) && er == (-1i64))
            || (a == (-8i64) && b == 3 && eq == (-3i64) && er == 1)
            || (a == (-8i64) && b == (-3i64) && eq == 2 && er == (-2i64)),
    ensures
        a == 8 && b == 3 ==> ret == true,
        a == 8 && b == (-3i64) ==> ret == true,
        a == (-8i64) && b == 3 ==> ret == true,
        a == (-8i64) && b == (-3i64) ==> ret == true,
{
    let (q, r) = (a / b, a % b);   // lib.rs:472->592
    let (q, r) = if (r > 0 && b < 0) || (r < 0 && b > 0) { (q - 1, r + b) } else { (q, r) };
    q == eq && r == er
}

exec fn div_floor_pair_b(a: i64, b: i64, eq: i64, er: i64) -> (ret: bool)
    requires
        (a == 1 && b == 2 && eq == 0 && er == 1)
            || (a == 1 && b == (-2i64) && eq == (-1i64) && er == (-1i64))
            || (a == (-1i64) && b == 2 && eq == (-1i64) && er == 1)
            || (a == (-1i64) && b == (-2i64) && eq == 0 && er == (-1i64)),
    ensures
        a == 1 && b == 2 ==> ret == true,
        a == 1 && b == (-2i64) ==> ret == true,
        a == (-1i64) && b == 2 ==> ret == true,
        a == (-1i64) && b == (-2i64) ==> ret == true,
{
    let (q, r) = (a / b, a % b);   // lib.rs:472->592
    let (q, r) = if (r > 0 && b < 0) || (r < 0 && b > 0) { (q - 1, r + b) } else { (q, r) };
    q == eq && r == er
}

/// UT: transcription of the div_ceil doc # Examples (lib.rs:76-91).
pub exec fn ut_test_div_ceil_examples() -> (ok: bool)
    ensures ok == true,
{
    div_ceil_pair_a(8i64, 3i64, 3i64)
        && div_ceil_pair_a(8i64, 0-3i64, 0-2i64)
        && div_ceil_pair_a(0-8i64, 3i64, 0-2i64)
        && div_ceil_pair_a(0-8i64, 0-3i64, 3i64)
        && div_ceil_pair_b(1i64, 2i64, 1i64)
        && div_ceil_pair_b(1i64, 0-2i64, 0i64)
        && div_ceil_pair_b(0-1i64, 2i64, 0i64)
        && div_ceil_pair_b(0-1i64, 0-2i64, 1i64)
}

exec fn div_ceil_pair_a(a: i64, b: i64, eq: i64) -> (ret: bool)
    requires
        (a == 8 && b == 3 && eq == 3)
            || (a == 8 && b == (-3i64) && eq == (-2i64))
            || (a == (-8i64) && b == 3 && eq == (-2i64))
            || (a == (-8i64) && b == (-3i64) && eq == 3),
    ensures
        a == 8 && b == 3 ==> ret == true,
        a == 8 && b == (-3i64) ==> ret == true,
        a == (-8i64) && b == 3 ==> ret == true,
        a == (-8i64) && b == (-3i64) ==> ret == true,
{
    let (d, r) = (a / b, a % b);   // lib.rs:482->592; the concrete-value obligations are discharged by the example requires
    let q = if (r > 0 && b > 0) || (r < 0 && b < 0) { d + 1 } else { d };
    q == eq
}

exec fn div_ceil_pair_b(a: i64, b: i64, eq: i64) -> (ret: bool)
    requires
        (a == 1 && b == 2 && eq == 1)
            || (a == 1 && b == (-2i64) && eq == 0)
            || (a == (-1i64) && b == 2 && eq == 0)
            || (a == (-1i64) && b == (-2i64) && eq == 1),
    ensures
        a == 1 && b == 2 ==> ret == true,
        a == 1 && b == (-2i64) ==> ret == true,
        a == (-1i64) && b == 2 ==> ret == true,
        a == (-1i64) && b == (-2i64) ==> ret == true,
{
    let (d, r) = (a / b, a % b);   // lib.rs:482->592; the concrete-value obligations are discharged by the example requires
    let q = if (r > 0 && b > 0) || (r < 0 && b < 0) { d + 1 } else { d };
    q == eq
}

}

fn main() {}
