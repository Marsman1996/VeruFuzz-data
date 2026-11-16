//! Batch J6 harness -- the weekday quickcheck properties, transcribed
//! from the upstream `#[cfg(test)]` quickcheck block (jcore
//! civil/weekday.rs:525-543) into theorem proofs, following the J2
//! quickcheck_date.rs / J3 quickcheck_time.rs precedent.
//!
//! Upstream quickcheck block (verbatim shape):
//!   quickcheck::quickcheck! {
//!       fn prop_weekday_add_sub(wd: Weekday, n: i64) -> bool {
//!           wd.wrapping_add(n).wrapping_sub(n) == wd
//!       }
//!       fn prop_weekday_since_until(wd1: Weekday, wd2: Weekday) -> bool {
//!           wd1.until(wd2) == wd2.since(wd1)
//!       }
//!       fn prop_since_add_equals_self(wd1: Weekday, wd2: Weekday) -> bool {
//!           let days = wd1.since(wd2);
//!           wd2.wrapping_add(days.into()) == wd1
//!       }
//!       fn prop_until_add_equals_other(wd1: Weekday, wd2: Weekday) -> bool {
//!           let days = wd1.until(wd2);
//!           wd1.wrapping_add(days.into()) == wd2
//!       }
//!   }
//!
//! Landing record (this file): all four properties land. The derived
//! enum equality `==` in the upstream assertions is contract-opaque (J1
//! finding 2), so the laws are stated at the wd_monday_one index level /
//! through the exec contracts' own twins (the J3 materialization
//! discipline); `days.into()` is the i8 -> i64 zero extension (the
//! since/until contract's index expression at the widened type).
//!
//! Stretch note (the batch instruction's J3-defer tail): the five
//! deferred time quickcheck properties (prop_until_then_add /
//! prop_until_then_sub / prop_since_then_add / prop_since_then_sub /
//! prop_until_is_since_negated) each build a `Span` through `Time::
//! until`/`Time::since` (wrapper time.rs:1223/:1257) -- the Span surface
//! is J5 agent territory, so they remain deferred to the span batch;
//! this file's additions come from the weekday quickcheck block instead.

use vstd::prelude::*;
use vstd::arithmetic::div_mod::{
    lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse,
    lemma_mod_multiples_vanish,
};
use vstd::arithmetic::mul::lemma_mul_is_commutative;

#[path = "../src/lib.rs"]
mod jiff_lib;

verus! {

use jiff_lib::weekday::{
    Weekday, spec_wrapping_add_m0, spec_wrapping_sub_m0, wd_monday_one,
};

/// Theorem form of prop_weekday_add_sub (jcore weekday.rs:526-528):
///   wd.wrapping_add(n).wrapping_sub(n) == wd
/// Materialization: the two exec calls bind their results to the
/// spec twins (the wrapping_add/-sub contracts), so the composite law is
/// stated over the twin chain: wa is the added weekday, wr the
/// subsequently subtracted one; the exact quickcheck instantiation is
/// the special case where wa/wr are the values the exec faces return.
pub proof fn prop_weekday_add_sub(
    w: Weekday,
    n: int,
    wa: Weekday,
    wr: Weekday,
)
    requires
        (wd_monday_one(wa) - 1) == spec_wrapping_add_m0(w, n)
            && (wd_monday_one(wr) - 1) == spec_wrapping_sub_m0(wa, n),
    ensures wd_monday_one(wr) == wd_monday_one(w),
{
    let x: int = wd_monday_one(w) - 1;
    let p: int = n % 7;
    lemma_fundamental_div_mod(n, 7);
    assert(0 <= p && p < 7);
    let a: int = spec_wrapping_add_m0(w, n);
    assert(a == (x + p) % 7);
    assert((wd_monday_one(wa) - 1) == a);
    let t: int = (0 - p) % 7;
    assert((wd_monday_one(wr) - 1) == ((a + t) % 7));
    if p == 0 {
        assert(t == 0) by {
            lemma_fundamental_div_mod_converse(0 - 0, 7, 0, 0);
        }
        assert(a == x) by {
            lemma_fundamental_div_mod_converse(x, 7, 0, x);
        }
        assert((a + t) % 7 == x) by {
            lemma_fundamental_div_mod_converse(x, 7, 0, x);
        }
    } else {
        assert(t == 7 - p) by {
            lemma_fundamental_div_mod_converse(0 - p, 7, -1, 7 - p);
        }
        // a = (x + p) - 7 * k_x, where x + p sits in 0..=12 so k_x in
        // {0, 1}; then a + t = x + 7 * (1 - k_x), a multiple-of-7 shift
        // of x:
        let kx: int = (x + p) / 7;
        lemma_fundamental_div_mod(x + p, 7);
        assert((x + p) == 7 * kx + a);
        assert(kx == 0 || kx == 1);
        assert((a + t) == x + 7 * (1 - kx));
        lemma_mul_is_commutative(1 - kx, 7);
        assert(x + 7 * (1 - kx) == x + (1 - kx) * 7);
        lemma_mod_multiples_vanish(1 - kx, x, 7);
        assert((x + (1 - kx) * 7) % 7 == x % 7);
        assert(x % 7 == x) by {
            lemma_fundamental_div_mod_converse(x, 7, 0, x);
        }
        assert((a + t) % 7 == x);
    }
    assert((wd_monday_one(wr) - 1) == x);
    assert(wd_monday_one(wr) == wd_monday_one(w));
}

/// Theorem form of prop_weekday_since_until (jcore weekday.rs:530-532):
///   wd1.until(wd2) == wd2.since(wd1)
/// Materialization: both faces' contracts pin the same index
/// expression, so the equality of the two code paths is witnessed by an
/// exec fn computing both and asserting their agreement (the value it
/// returns already carries the until/since contract equality; proof fns
/// cannot call exec fns in this build -- the J6 probe finding).
pub exec fn prop_weekday_since_until(
    w1: Weekday,
    w2: Weekday,
) -> (r: i8)
    ensures
        r as int
            == (wd_monday_one(w2) - wd_monday_one(w1)) % 7
            && 0 <= r as int
            && (r as int) < 7,
{
    let a = w1.until(w2);
    let b = w2.since(w1);
    proof {
        assert(a as int == b as int);
        assert(a as int
            == (wd_monday_one(w2) - wd_monday_one(w1)) % 7);
    }
    a
}

/// Theorem form of prop_since_add_equals_self (jcore weekday.rs:534-537):
///   let days = wd1.since(wd2);
///   wd2.wrapping_add(days.into()) == wd1
/// Materialization: days is the since twin expression; wrapping_add's
/// twin over wd2 applied to it reduces back to wd1's index.
pub proof fn prop_since_add_equals_self(w1: Weekday, w2: Weekday)
    ensures
        ((wd_monday_one(w2) - 1)
            + ((wd_monday_one(w1) - wd_monday_one(w2)) % 7)) % 7
            == wd_monday_one(w1) - 1,
{
    let x1: int = wd_monday_one(w1) - 1;
    let x2: int = wd_monday_one(w2) - 1;
    assert(0 <= x1 && x1 < 7);
    assert(0 <= x2 && x2 < 7);
    let d: int = (x1 - x2) % 7;
    if x1 >= x2 {
        assert(d == x1 - x2) by {
            lemma_fundamental_div_mod_converse(x1 - x2, 7, 0, x1 - x2);
        }
        assert(x2 + d == x1);
        assert((x2 + d) % 7 == x1) by {
            lemma_fundamental_div_mod_converse(x1, 7, 0, x1);
        }
    } else {
        assert(d == x1 - x2 + 7) by {
            lemma_fundamental_div_mod_converse(
                x1 - x2,
                7,
                -1,
                x1 - x2 + 7,
            );
        }
        let total: int = x2 + d;
        assert(total == x1 + 7);
        assert(total % 7 == x1) by {
            lemma_fundamental_div_mod_converse(x1 + 7, 7, 1, x1);
        }
    }
}

/// Theorem form of prop_until_add_equals_other
/// (jcore weekday.rs:539-542):
///   let days = wd1.until(wd2);
///   wd1.wrapping_add(days.into()) == wd2
pub proof fn prop_until_add_equals_other(w1: Weekday, w2: Weekday)
    ensures
        ((wd_monday_one(w1) - 1)
            + ((wd_monday_one(w2) - wd_monday_one(w1)) % 7)) % 7
            == wd_monday_one(w2) - 1,
{
    let x1: int = wd_monday_one(w1) - 1;
    let x2: int = wd_monday_one(w2) - 1;
    assert(0 <= x1 && x1 < 7);
    assert(0 <= x2 && x2 < 7);
    let d: int = (x2 - x1) % 7;
    if x2 >= x1 {
        assert(d == x2 - x1) by {
            lemma_fundamental_div_mod_converse(x2 - x1, 7, 0, x2 - x1);
        }
        assert(x1 + d == x2);
        assert((x1 + d) % 7 == x2) by {
            lemma_fundamental_div_mod_converse(x2, 7, 0, x2);
        }
    } else {
        assert(d == x2 - x1 + 7) by {
            lemma_fundamental_div_mod_converse(
                x2 - x1,
                7,
                -1,
                x2 - x1 + 7,
            );
        }
        let total: int = x1 + d;
        assert(total == x2 + 7);
        assert(total % 7 == x2) by {
            lemma_fundamental_div_mod_converse(x2 + 7, 7, 1, x2);
        }
    }
}

} // verus!

// Standalone driver form (the src/ crate root carries its own main; this
// file's module mount does not include it).
fn main() {}
