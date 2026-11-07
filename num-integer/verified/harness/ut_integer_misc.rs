//! num-integer **harness zone** -- the Integer trait difference-set example
//! batch. Covers these families from the upstream inline UT (the lib.rs
//! `$test_mod` macro expansion, i64 instances as the main line):
//!   - next_multiple_of's 8 doc-example pairs (lib.rs:293-303)
//!   - prev_multiple_of's 8 doc-example pairs (lib.rs:324-336)
//!   - test_multiple_of_one_limits (lib.rs:830-838: MIN/MAX x {1, -1})
//!   - test_even / test_odd (lib.rs:804-828 signed / :1033-1049 unsigned)
//!   - the inc / dec doc examples (lib.rs:349-351 / :367-369)
//!
//! Direct example-evaluation shape: the pair functions emit the upstream machine
//! expression directly under concrete requires pinning; z3 fully evaluates concrete
//! values (the machine `/`/`%` have the rust_rem axiom bridge; the bit-level
//! `&1` goes through by (bit_vector) assertions -- the same deployment as
//! src/average.rs, the assertions using only parameter terms). The
//! obligation anchors (the expected errors: division by zero / subtraction
//! underflow / addition overflow / MIN/-1) live in src/lib.rs sections 6-8
//! and are not repeated here.
//!
//! Run: VERUS_Z3_PATH=<z3> <verus> database/num-integer/verified/harness/ut_integer_misc.rs
//! Reading the output: expected Nv/0e.

use vstd::prelude::*;

verus! {

// =========================================================================
// 1. next_multiple_of -- the 8 doc-example pairs (lib.rs:293-303) + the +/-1 limits group
// =========================================================================

/// next_multiple_of single-group direct evaluation (the macro-expansion body lib.rs:594-605, with
/// the tip's `other == -1` guard; mod_floor :603 inlined). 4 examples per function (same as
/// ut_div: the 8-clause disjunction exceeds the z3 instantiation budget).
exec fn next_pair_a(a: i64, b: i64, exp: i64) -> (ret: bool)
    requires
        b != 0,
        (a == 16 && b == 8 && exp == 16)
            || (a == 23 && b == 8 && exp == 24)
            || (a == 16 && b == (0 - 8) && exp == 16)
            || (a == 23 && b == (0 - 8) && exp == 16),
    ensures
        a == 16 && b == 8 ==> ret == true,
        a == 23 && b == 8 ==> ret == true,
        a == 16 && b == (0 - 8) ==> ret == true,
        a == 23 && b == (0 - 8) ==> ret == true,
{
    if b == -1 {
        return a == exp;        // lib.rs:598-601 tip guard
    }
    let r = a % b;              // lib.rs:603->459 (the example domain b != 0)
    let m = if (r > 0 && b < 0) || (r < 0 && b > 0) { r + b } else { r };
    a + (if m == 0 { 0 } else { b - m }) == exp   // lib.rs:604
}

exec fn next_pair_b(a: i64, b: i64, exp: i64) -> (ret: bool)
    requires
        b != 0,
        (a == (0 - 16) && b == 8 && exp == (0 - 16))
            || (a == (0 - 23) && b == 8 && exp == (0 - 16)),
    ensures
        ret == true,
{
    if b == -1 {
        return a == exp;        // lib.rs:598-601 tip guard
    }
    let r = a % b;
    let m = if (r > 0 && b < 0) || (r < 0 && b > 0) { r + b } else { r };
    a + (if m == 0 { 0 } else { b - m }) == exp
}

/// The two negative-dividend cases of the negative-divisor group. z3 does not land concrete
/// values for the builtin `%` (negative divisor) under the 4-way disjunctive combination --
/// they live in this separate function with segmented value hints added,
/// and then discharge fully.
exec fn next_pair_c(a: i64, b: i64, exp: i64) -> (ret: bool)
    requires
        b != 0,
        (a == (0 - 16) && b == (0 - 8) && exp == (0 - 16))
            || (a == (0 - 23) && b == (0 - 8) && exp == (0 - 24)),
    ensures
        ret == true,
{
    if b == -1 {
        return a == exp;
    }
    let r = a % b;
    assert(r@ == 0 || r@ == (0 - 7));          // truncated remainder (sign follows the dividend)
    let m = if (r > 0 && b < 0) || (r < 0 && b > 0) { r + b } else { r };
    assert(m@ == 0 || m@ == (0 - 7));           // no adjustment branch in this group
    let d = if m == 0 { 0 } else { b - m };
    assert(d@ == 0 || d@ == (0 - 1));
    a + d == exp
}

/// test_multiple_of_one_limits (lib.rs:830-838) + the :604/:615 bound-end semantics
/// -- the whole +/-1 group (the guarded or m=0 paths, all safe endpoints).
exec fn next_pair_limits(a: i64, b: i64, exp: i64) -> (ret: bool)
    requires
        (a == (0 - 9223372036854775807 - 1) && b == 1 && exp == (0 - 9223372036854775807 - 1))    // MIN, 1
            || (a == 9223372036854775807 && b == 1 && exp == 9223372036854775807)                  // MAX, 1
            || (a == (0 - 9223372036854775807 - 1) && b == (0 - 1) && exp == (0 - 9223372036854775807 - 1))  // MIN, -1 (guard)
            || (a == 9223372036854775807 && b == (0 - 1) && exp == 9223372036854775807),          // MAX, -1 (guard)
    ensures
        ret == true,
{
    if b == -1 {
        return a == exp;
    }
    let r = a % b;
    let m = if (r > 0 && b < 0) || (r < 0 && b > 0) { r + b } else { r };
    a + (if m == 0 { 0 } else { b - m }) == exp
}

pub exec fn ut_test_next_multiple_of_examples() -> (ok: bool)
    ensures
        ok == true,
{
    next_pair_a(16, 8, 16)
        && next_pair_a(23, 8, 24)
        && next_pair_a(16, 0 - 8, 16)
        && next_pair_a(23, 0 - 8, 16)
        && next_pair_b(0 - 16, 8, 0 - 16)
        && next_pair_b(0 - 23, 8, 0 - 16)
        && next_pair_c(0 - 16, 0 - 8, 0 - 16)
        && next_pair_c(0 - 23, 0 - 8, 0 - 24)
        && next_pair_limits(0 - 9223372036854775807 - 1, 1, 0 - 9223372036854775807 - 1)
        && next_pair_limits(9223372036854775807, 1, 9223372036854775807)
        && next_pair_limits(0 - 9223372036854775807 - 1, 0 - 1, 0 - 9223372036854775807 - 1)
        && next_pair_limits(9223372036854775807, 0 - 1, 9223372036854775807)
}

// =========================================================================
// 2. prev_multiple_of -- the 8 doc-example pairs (lib.rs:324-336) + the +/-1 limits group
// =========================================================================

exec fn prev_pair_a(a: i64, b: i64, exp: i64) -> (ret: bool)
    requires
        b != 0,
        (a == 16 && b == 8 && exp == 16)
            || (a == 23 && b == 8 && exp == 16)
            || (a == 16 && b == (0 - 8) && exp == 16)
            || (a == 23 && b == (0 - 8) && exp == 24),
    ensures
        a == 16 && b == 8 ==> ret == true,
        a == 23 && b == 8 ==> ret == true,
        a == 16 && b == (0 - 8) ==> ret == true,
        a == 23 && b == (0 - 8) ==> ret == true,
{
    if b == -1 {
        return a == exp;        // lib.rs:611 tip guard
    }
    let r = a % b;              // lib.rs:615->459
    let m = if (r > 0 && b < 0) || (r < 0 && b > 0) { r + b } else { r };
    a - m == exp                // lib.rs:615
}

exec fn prev_pair_b(a: i64, b: i64, exp: i64) -> (ret: bool)
    requires
        b != 0,
        (a == (0 - 16) && b == 8 && exp == (0 - 16))
            || (a == (0 - 23) && b == 8 && exp == (0 - 24))
            || (a == (0 - 16) && b == (0 - 8) && exp == (0 - 16))
            || (a == (0 - 23) && b == (0 - 8) && exp == (0 - 16)),
    ensures
        a == (0 - 16) && b == 8 ==> ret == true,
        a == (0 - 23) && b == 8 ==> ret == true,
        a == (0 - 16) && b == (0 - 8) ==> ret == true,
        a == (0 - 23) && b == (0 - 8) ==> ret == true,
{
    if b == -1 {
        return a == exp;
    }
    let r = a % b;
    let m = if (r > 0 && b < 0) || (r < 0 && b > 0) { r + b } else { r };
    a - m == exp
}

exec fn prev_pair_limits(a: i64, b: i64, exp: i64) -> (ret: bool)
    requires
        (a == (0 - 9223372036854775807 - 1) && b == 1 && exp == (0 - 9223372036854775807 - 1))    // MIN, 1
            || (a == 9223372036854775807 && b == 1 && exp == 9223372036854775807)                // MAX, 1
            || (a == (0 - 9223372036854775807 - 1) && b == (0 - 1) && exp == (0 - 9223372036854775807 - 1))  // MIN, -1 (guard)
            || (a == 9223372036854775807 && b == (0 - 1) && exp == 9223372036854775807),         // MAX, -1 (guard)
    ensures
        ret == true,
{
    if b == -1 {
        return a == exp;
    }
    let r = a % b;
    let m = if (r > 0 && b < 0) || (r < 0 && b > 0) { r + b } else { r };
    a - m == exp
}

pub exec fn ut_test_prev_multiple_of_examples() -> (ok: bool)
    ensures
        ok == true,
{
    prev_pair_a(16, 8, 16)
        && prev_pair_a(23, 8, 16)
        && prev_pair_a(16, 0 - 8, 16)
        && prev_pair_a(23, 0 - 8, 24)
        && prev_pair_b(0 - 16, 8, 0 - 16)
        && prev_pair_b(0 - 23, 8, 0 - 24)
        && prev_pair_b(0 - 16, 0 - 8, 0 - 16)
        && prev_pair_b(0 - 23, 0 - 8, 0 - 16)
        && prev_pair_limits(0 - 9223372036854775807 - 1, 1, 0 - 9223372036854775807 - 1)
        && prev_pair_limits(9223372036854775807, 1, 9223372036854775807)
        && prev_pair_limits(0 - 9223372036854775807 - 1, 0 - 1, 0 - 9223372036854775807 - 1)
        && prev_pair_limits(9223372036854775807, 0 - 1, 9223372036854775807)
}

// =========================================================================
// 3. is_even / is_odd -- test_even (lib.rs:804-815) / test_odd (:817-828);
//    the signed bit-level `&1` bridges to `%2` via the bit_vector assertion (params-only)
// =========================================================================

exec fn even_pair_signed(x: i64, exp: bool) -> (ret: bool)
    requires
        (x == (0 - 4i64) && exp == true) || (x == (0 - 3i64) && exp == false)
            || (x == (0 - 2i64) && exp == true) || (x == (0 - 1i64) && exp == false)
            || (x == 0i64 && exp == true) || (x == 1i64 && exp == false)
            || (x == 2i64 && exp == true) || (x == 3i64 && exp == false),
    ensures
        ret == true,
{
    assert((x & 1 == 0) == (x % 2 == 0)) by (bit_vector);   // :580 bit bridge
    ((x & 1) == 0) == exp
}

exec fn odd_pair_signed(x: i64, exp: bool) -> (ret: bool)
    requires
        (x == (0 - 4i64) && exp == false) || (x == (0 - 3i64) && exp == true)
            || (x == (0 - 2i64) && exp == false) || (x == (0 - 1i64) && exp == true)
            || (x == 0i64 && exp == false) || (x == 1i64 && exp == true)
            || (x == 2i64 && exp == false) || (x == 3i64 && exp == true),
    ensures
        ret == true,
{
    assert((x & 1 == 0) == (x % 2 == 0)) by (bit_vector);   // :586 via :580
    !((x & 1) == 0) == exp
}

exec fn even_pair_unsigned(x: u64, exp: bool) -> (ret: bool)
    requires
        (x == 0u64 && exp == true) || (x == 1u64 && exp == false)
            || (x == 2u64 && exp == true) || (x == 3u64 && exp == false),
    ensures
        ret == true,
{
    (x % 2 == 0) == exp           // lib.rs:941 (the unsigned `%2` is direct)
}

exec fn odd_pair_unsigned(x: u64, exp: bool) -> (ret: bool)
    requires
        (x == 0u64 && exp == false) || (x == 1u64 && exp == true)
            || (x == 2u64 && exp == false) || (x == 3u64 && exp == true),
    ensures
        ret == true,
{
    !(x % 2 == 0) == exp          // lib.rs:946-947
}

pub exec fn ut_test_even_odd_examples() -> (ok: bool)
    ensures
        ok == true,
{
    even_pair_signed(0 - 4i64, true)
        && even_pair_signed(0 - 3i64, false)
        && even_pair_signed(0 - 2i64, true)
        && even_pair_signed(0 - 1i64, false)
        && even_pair_signed(0i64, true)
        && even_pair_signed(1i64, false)
        && even_pair_signed(2i64, true)
        && even_pair_signed(3i64, false)
        && odd_pair_signed(0 - 4i64, false)
        && odd_pair_signed(0 - 3i64, true)
        && odd_pair_signed(0 - 2i64, false)
        && odd_pair_signed(0 - 1i64, true)
        && odd_pair_signed(0i64, false)
        && odd_pair_signed(1i64, true)
        && odd_pair_signed(2i64, false)
        && odd_pair_signed(3i64, true)
        && even_pair_unsigned(0u64, true)
        && even_pair_unsigned(1u64, false)
        && even_pair_unsigned(2u64, true)
        && even_pair_unsigned(3u64, false)
        && odd_pair_unsigned(0u64, false)
        && odd_pair_unsigned(1u64, true)
        && odd_pair_unsigned(2u64, false)
        && odd_pair_unsigned(3u64, true)
}

// =========================================================================
// 4. inc / dec -- the doc examples (lib.rs:349-351 / :367-369)
// =========================================================================

/// The dec doc example: `let mut x: i32 = 43; x.dec(); assert_eq!(x, 42);`
/// (the direct-evaluation i64 variant; the MIN-end overflow anchor is in src/lib.rs section 8 / out/poc/).
exec fn dec_pair(x: i64, exp: i64) -> (ret: bool)
    requires
        (x == 43i64 && exp == 42i64) || (x == (0 - 43i64) && exp == (0 - 44i64)),
    ensures
        ret == true,
{
    (x - 1) == exp                 // lib.rs:359
}

/// The inc doc example: `let mut x: i32 = 41; x.inc(); assert_eq!(x, 42);`
exec fn inc_pair(x: i64, exp: i64) -> (ret: bool)
    requires
        (x == 41i64 && exp == 42i64) || (x == (0 - 41i64) && exp == (0 - 40i64)),
    ensures
        ret == true,
{
    (x + 1) == exp                 // lib.rs:376
}

pub exec fn ut_test_inc_dec_examples() -> (ok: bool)
    ensures
        ok == true,
{
    dec_pair(43i64, 42i64)
        && dec_pair(0 - 43i64, 0 - 44i64)
        && inc_pair(41i64, 42i64)
        && inc_pair(0 - 41i64, 0 - 40i64)
}

}

fn main() {}
