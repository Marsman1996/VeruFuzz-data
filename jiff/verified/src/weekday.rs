//! Batch J6 -- the civil weekday core, Verus transcription of:
//!   - code/crates/jiff-core/src/civil/weekday.rs (the whole 544-line
//!     file at this pin: the Weekday enum at :12-20, the four from_/to_
//!     offset faces at :26-126, wrapping_add/wrapping_sub at :134-162,
//!     next/previous at :170-182, since/until at :190-203, and the two
//!     cycle iterator structs at :208-260)
//!   - the offset-domain bounds the from_* faces range-check against are
//!     the define_bounds! instantiations at jcore bounds.rs:388-397
//!     (WeekdayMondayZero i8 0,6 / WeekdayMondayOne 1,7 /
//!     WeekdaySundayZero 0,6 / WeekdaySundayOne 1,7).
//!
//! Planning note: harness-inventory.md section 6.2 has no batch clause
//! for weekday (its batches stop at J5's span core); this file is the
//! tail-clearing pass over the weekday surface, recorded as such in
//! J6/notes.md.
//!
//! Materialization ledger (this file):
//! - Result<T, RangeError> faces materialize as Option<T> (the J1
//!   bounds.rs ledger: the error value is a zero-sized witness); the
//!   rbail!(b::X::error()) transcriptions end in Option::None.
//! - const fn materializes as exec fn (no const verification in this
//!   build); the quickcheck::Arbitrary impl (weekday.rs:262-276) is test
//!   tier and the Hash/Eq/Debug/defmt derives are body-free faces; none
//!   are transcribed.
//! - The enum discriminant face: upstream declares the variants with
//!   explicit discriminants `Monday = 1..= Sunday = 7` (#[repr(u8)],
//!   weekday.rs:10-20) and reads them back with `self as i8`
//!   (to_monday_one_offset, :105-107). Verus has no enum->int cast, so
//!   the discriminant read materializes as the equivalent literal match
//!   over the variants (value-identical: the match arms spell the same
//!   1..=7 the repr assigns), and every contract speaks through the
//!   spec index fn wd_monday_one rather than derived enum equality (J1
//!   finding 2: derived PartialEq is contract-opaque; variant tests and
//!   the index twin are the binding shapes).
//! - mod-7 wrapping shoulders: every wrapping/since/until face goes
//!   through the vstd div_mod machinery. The std i8/i64 rem_euclid the
//!   upstream bodies call has no vstd spec in this build (the J2
//!   finding-13 family), so the std bodies are inlined at the fixed
//!   divisor 7 with full domains: rem_euclid_7 (i64, the divisor
//!   TimeSecond-style fix-up x + 7 can never overflow at that width) --
//!   negative inputs carry their Euclid obligation explicitly, the
//!   i64::MIN corner is upstream's own documented case ("i64::MIN
//!   .rem_euclid(7) is 6", weekday.rs:140-141 and :156).
//! - wrapping_add's start.wrapping_add(days.rem_euclid(7)) keeps the
//!   machine wrapping_add shape but is proven a plain addition: both
//!   operands are in 0..=6 (bound-hoisted), so no wrap can occur (the
//!   J3 finding-28 pattern).
//! - The since/until i8 subtraction materializes at i64: both operands
//!   are in 0..=6 and the difference in -6..=6, value-identical at either
//!   width (the J2 is_leap_year precedent).
//! - The WeekdaysForward/Reverse iterators: the upstream core::iter::
//!   Iterator trait impls (:228-237, :248-258) materialize as inherent
//!   exec next methods with a two-state contract (old(self)/final(self)
//!   -- the probe-verified shape); the FusedIterator marker impls are
//!   body-free type faces, not transcribed.

use vstd::prelude::*;
use vstd::arithmetic::div_mod::{
    lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse,
    lemma_mod_multiples_basic, rust_rem,
};
use vstd::arithmetic::mul::{
    lemma_mul_basics, lemma_mul_is_commutative,
    lemma_mul_is_distributive_add_other_way, lemma_mul_unary_negation,
};

verus! {

// ===========================================================================
// spec models
// ===========================================================================

/// The Monday-one-offset index of a weekday: the spec face of the
/// upstream #[repr(u8)] discriminants (Monday = 1 ..= Sunday = 7,
/// weekday.rs:12-20) and of the `self as i8` read in
/// to_monday_one_offset (:106).
pub open spec fn wd_monday_one(w: Weekday) -> int {
    match w {
        Weekday::Monday => 1,
        Weekday::Tuesday => 2,
        Weekday::Wednesday => 3,
        Weekday::Thursday => 4,
        Weekday::Friday => 5,
        Weekday::Saturday => 6,
        Weekday::Sunday => 7,
    }
}

/// Spec twin of Weekday::wrapping_add (weekday.rs:134-147): the mod-7
/// reduction of the monday-zero index over the Euclid residue of the
/// day delta. All wrapping/since/until laws below state their equality
/// at this index level (the derived enum equality is contract-opaque,
/// J1 finding 2).
pub open spec fn spec_wrapping_add_m0(w: Weekday, days: int) -> int {
    ((wd_monday_one(w) - 1) + (days % 7)) % 7
}

/// Spec twin of Weekday::wrapping_sub (weekday.rs:155-162). Note the
/// i64::MIN corner: upstream replaces the negation failure with -6
/// (days.rem_euclid(7) of i64::MIN is 6, so subtracting i64::MIN acts as
/// subtracting 1 day -- weekday.rs:156-161); at the unrestricted int of
/// the spec twin the Euclid residue (0 - (days % 7)) % 7 is that same
/// value for every days including the corner (2^63 == 1 mod 7, so
/// ((-2^63) % 7) == 6 and (-6) % 7 == 1).
pub open spec fn spec_wrapping_sub_m0(w: Weekday, days: int) -> int {
    ((wd_monday_one(w) - 1) + ((0 - (days % 7)) % 7)) % 7
}

// ===========================================================================
// std rem_euclid inline at the fixed divisor 7 (full i64 domain)
// ===========================================================================

/// std i64::rem_euclid body (self % rhs, + rhs when the remainder is
/// negative), inlined at the week divisor 7 -- the J2/J3 finding-13
/// pattern (no vstd spec for the std method in this build). Full i64
/// domain: the trunc remainder sits in -6..=6 and the + 7 fix-up can
/// never overflow, so no caller-side domain restriction is needed.
pub exec fn rem_euclid_7(a: i64) -> (r: i64)
    ensures
        r as int == (a as int) % 7
            && 0 <= r as int
            && (r as int) < 7,
{
    let x = a % 7i64;
    proof {
        let ai: int = a as int;
        assert(x as int == rust_rem(ai, 7));
        if a == 0 {
            assert(rust_rem(ai, 7) == 0);
            assert(ai % 7 == 0);
        } else if a > 0 {
            assert(rust_rem(ai, 7) == ai % 7);
        } else {
            let n: int = 0 - ai;
            let q: int = n / 7;
            let e: int = n % 7;
            lemma_fundamental_div_mod(n, 7);
            assert(n == 7 * q + e);
            assert(0 <= e < 7);
            lemma_mul_is_commutative(q, 7);
            lemma_mul_unary_negation(q, 7);
            assert(ai == (0 - q) * 7 + (0 - e));
            if x == 0 {
                assert(ai == (0 - q) * 7);
                assert(rust_rem(ai, 7) == 0);
                lemma_mod_multiples_basic(0 - q, 7);
                assert(ai % 7 == 0);
            } else {
                let w: int = 7 - e;
                assert(0 < w < 7);
                lemma_mul_is_distributive_add_other_way(7, q, 1);
                lemma_mul_basics(7);
                assert((q + 1) * 7 == q * 7 + 1 * 7);
                assert(1 * 7 == 7);
                assert((q + 1) * 7 == q * 7 + 7);
                lemma_mul_unary_negation(q + 1, 7);
                assert((0 - (q + 1)) * 7 == (0 - q * 7) - 7);
                assert(ai == (0 - (q + 1)) * 7 + w);
                lemma_fundamental_div_mod_converse(ai, 7, 0 - (q + 1), w);
                assert(ai % 7 == w);
                assert(rust_rem(ai, 7) == 0 - e);
                assert(x as int == 0 - e);
                assert(x as int + 7 == w);
            }
        }
    }
    if x < 0 {
        x + 7i64
    } else {
        x
    }
}

// ===========================================================================
// Weekday (jcore civil/weekday.rs:12-218)
// ===========================================================================

/// Origin Rust (weekday.rs:6-20):
///     /// A representation for the day of the week.
///     #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
///     #[repr(u8)]
///     #[allow(missing_docs)]
///     pub enum Weekday {
///         Monday = 1,
///         Tuesday = 2,
///         ...
///         Sunday = 7,
///     }
/// Upstream doc (weekday.rs:6):
///   A representation for the day of the week.
/// The Debug/Eq/Hash derives and the `#[cfg(feature = "arbitrary")]`
/// derive are body-free or test-tier faces, not transcribed (ledger).
#[derive(Clone, Copy)]
pub enum Weekday {
    Monday,
    Tuesday,
    Wednesday,
    Thursday,
    Friday,
    Saturday,
    Sunday,
}

impl Weekday {
    /// Origin Rust (weekday.rs:23-39):
    ///     pub const fn from_monday_zero_offset(
    ///         offset: i8,
    ///     ) -> Result<Weekday, RangeError> {
    ///         Ok(match offset {
    ///             0 => Weekday::Monday,
    ///             ...
    ///             6 => Weekday::Sunday,
    ///             _ => rbail!(b::WeekdayMondayZero::error()),
    ///         })
    ///     }
    /// Upstream doc (weekday.rs:21-22):
    ///   Convert a 0-offset to a `Weekday`. Monday corresponds to offset `0`
    ///   and Sunday corresponds to offset `6`.
    /// The range check is the WeekdayMondayZero interval (jcore
    /// bounds.rs:388: i8 0, 6).
    pub exec fn from_monday_zero_offset(offset: i8) -> (r: Option<Weekday>)
        ensures
            match r {
                Option::Some(w) => (w is Monday <==> offset == 0)
                    && (w is Tuesday <==> offset == 1)
                    && (w is Wednesday <==> offset == 2)
                    && (w is Thursday <==> offset == 3)
                    && (w is Friday <==> offset == 4)
                    && (w is Saturday <==> offset == 5)
                    && (w is Sunday <==> offset == 6)
                    && wd_monday_one(w) == (offset as int) + 1,
                Option::None => !(0 <= offset && offset <= 6),
            },
    {
        match offset {
            0 => Option::Some(Weekday::Monday),
            1 => Option::Some(Weekday::Tuesday),
            2 => Option::Some(Weekday::Wednesday),
            3 => Option::Some(Weekday::Thursday),
            4 => Option::Some(Weekday::Friday),
            5 => Option::Some(Weekday::Saturday),
            6 => Option::Some(Weekday::Sunday),
            _ => Option::None,
        }
    }

    /// Origin Rust (weekday.rs:41-57):
    ///     pub const fn from_monday_one_offset(
    ///         offset: i8,
    ///     ) -> Result<Weekday, RangeError> { ... 1..=7 arms ... }
    /// Upstream doc (weekday.rs:40):
    ///   Convert a 1-offset to a `Weekday`. Monday corresponds to offset `1`
    ///   and Sunday corresponds to offset `7`.
    /// The range check is the WeekdayMondayOne interval (jcore
    /// bounds.rs:391: i8 1, 7).
    pub exec fn from_monday_one_offset(offset: i8) -> (r: Option<Weekday>)
        ensures
            match r {
                Option::Some(w) => (w is Monday <==> offset == 1)
                    && (w is Tuesday <==> offset == 2)
                    && (w is Wednesday <==> offset == 3)
                    && (w is Thursday <==> offset == 4)
                    && (w is Friday <==> offset == 5)
                    && (w is Saturday <==> offset == 6)
                    && (w is Sunday <==> offset == 7)
                    && wd_monday_one(w) == offset as int,
                Option::None => !(1 <= offset && offset <= 7),
            },
    {
        match offset {
            1 => Option::Some(Weekday::Monday),
            2 => Option::Some(Weekday::Tuesday),
            3 => Option::Some(Weekday::Wednesday),
            4 => Option::Some(Weekday::Thursday),
            5 => Option::Some(Weekday::Friday),
            6 => Option::Some(Weekday::Saturday),
            7 => Option::Some(Weekday::Sunday),
            _ => Option::None,
        }
    }

    /// Origin Rust (weekday.rs:59-75):
    ///     pub const fn from_sunday_zero_offset(
    ///         offset: i8,
    ///     ) -> Result<Weekday, RangeError> { ... }
    /// Upstream doc (weekday.rs:58-59):
    ///   Convert a 0-offset to a `Weekday`. Sunday corresponds to offset `0`
    ///   and Saturday corresponds to offset `6`.
    /// The range check is the WeekdaySundayZero interval (jcore
    /// bounds.rs:394: i8 0, 6).
    pub exec fn from_sunday_zero_offset(offset: i8) -> (r: Option<Weekday>)
        ensures
            match r {
                Option::Some(w) => (w is Sunday <==> offset == 0)
                    && (w is Monday <==> offset == 1)
                    && (w is Tuesday <==> offset == 2)
                    && (w is Wednesday <==> offset == 3)
                    && (w is Thursday <==> offset == 4)
                    && (w is Friday <==> offset == 5)
                    && (w is Saturday <==> offset == 6)
                    && (offset == 0 ==> wd_monday_one(w) == 7)
                    && (1 <= offset && offset <= 6
                        ==> wd_monday_one(w) == offset as int),
                Option::None => !(0 <= offset && offset <= 6),
            },
    {
        match offset {
            0 => Option::Some(Weekday::Sunday),
            1 => Option::Some(Weekday::Monday),
            2 => Option::Some(Weekday::Tuesday),
            3 => Option::Some(Weekday::Wednesday),
            4 => Option::Some(Weekday::Thursday),
            5 => Option::Some(Weekday::Friday),
            6 => Option::Some(Weekday::Saturday),
            _ => Option::None,
        }
    }

    /// Origin Rust (weekday.rs:77-93):
    ///     pub const fn from_sunday_one_offset(
    ///         offset: i8,
    ///     ) -> Result<Weekday, RangeError> { ... }
    /// Upstream doc (weekday.rs:76-77):
    ///   Convert a 1-offset to a `Weekday`. Sunday corresponds to offset `1`
    ///   and Saturday corresponds to offset `7`.
    /// The range check is the WeekdaySundayOne interval (jcore
    /// bounds.rs:397: i8 1, 7).
    pub exec fn from_sunday_one_offset(offset: i8) -> (r: Option<Weekday>)
        ensures
            match r {
                Option::Some(w) => (w is Sunday <==> offset == 1)
                    && (w is Monday <==> offset == 2)
                    && (w is Tuesday <==> offset == 3)
                    && (w is Wednesday <==> offset == 4)
                    && (w is Thursday <==> offset == 5)
                    && (w is Friday <==> offset == 6)
                    && (w is Saturday <==> offset == 7)
                    && (offset == 1 ==> wd_monday_one(w) == 7)
                    && (2 <= offset && offset <= 7
                        ==> wd_monday_one(w)
                            == (offset as int) - 1),
                Option::None => !(1 <= offset && offset <= 7),
            },
    {
        match offset {
            1 => Option::Some(Weekday::Sunday),
            2 => Option::Some(Weekday::Monday),
            3 => Option::Some(Weekday::Tuesday),
            4 => Option::Some(Weekday::Wednesday),
            5 => Option::Some(Weekday::Thursday),
            6 => Option::Some(Weekday::Friday),
            7 => Option::Some(Weekday::Saturday),
            _ => Option::None,
        }
    }

    /// Origin Rust (weekday.rs:95-100):
    ///     pub const fn to_monday_zero_offset(self) -> i8 {
    ///         self.to_monday_one_offset() - 1
    ///     }
    /// Upstream doc (weekday.rs:94-95):
    ///   Returns the weekday as a 0-offset. Monday corresponds to offset `0`
    ///   and Sunday corresponds to offset `6`.
    pub exec fn to_monday_zero_offset(self) -> (r: i8)
        ensures
            r as int == wd_monday_one(self) - 1
                && 0 <= r as int
                && (r as int) < 7,
    {
        self.to_monday_one_offset() - 1
    }

    /// Origin Rust (weekday.rs:102-107):
    ///     pub const fn to_monday_one_offset(self) -> i8 {
    ///         self as i8
    ///     }
    /// Upstream doc (weekday.rs:101-102):
    ///   Returns the weekday as a 1-offset. Monday corresponds to offset `1`
    ///   and Sunday corresponds to offset `7`.
    /// Ledger: the enum->int cast materializes as the literal discriminant
    /// match (the repr assigns Monday=1..=Sunday=7, the exact arms below).
    pub exec fn to_monday_one_offset(self) -> (r: i8)
        ensures r as int == wd_monday_one(self),
    {
        match self {
            Weekday::Monday => 1,
            Weekday::Tuesday => 2,
            Weekday::Wednesday => 3,
            Weekday::Thursday => 4,
            Weekday::Friday => 5,
            Weekday::Saturday => 6,
            Weekday::Sunday => 7,
        }
    }

    /// Origin Rust (weekday.rs:109-119):
    ///     pub const fn to_sunday_zero_offset(self) -> i8 {
    ///         let offset = self.to_monday_one_offset();
    ///         if offset == 7 { 0 } else { offset }
    ///     }
    /// Upstream doc (weekday.rs:108-109):
    ///   Returns the weekday as a 0-offset. Sunday corresponds to offset `0`
    ///   and Saturday corresponds to offset `6`.
    pub exec fn to_sunday_zero_offset(self) -> (r: i8)
        ensures
            r as int
                == if wd_monday_one(self) == 7 {
                    0
                } else {
                    wd_monday_one(self)
                }
                && 0 <= r as int
                && (r as int) < 7,
    {
        let offset = self.to_monday_one_offset();
        if offset == 7 {
            0
        } else {
            offset
        }
    }

    /// Origin Rust (weekday.rs:121-126):
    ///     pub const fn to_sunday_one_offset(self) -> i8 {
    ///         self.to_sunday_zero_offset() + 1
    ///     }
    /// Upstream doc (weekday.rs:120-121):
    ///   Returns the weekday as a 1-offset. Sunday corresponds to offset `1`
    ///   and Saturday corresponds to offset `7`.
    pub exec fn to_sunday_one_offset(self) -> (r: i8)
        ensures
            r as int
                == if wd_monday_one(self) == 7 {
                    1
                } else {
                    wd_monday_one(self) + 1
                }
                && 1 <= r as int
                && (r as int) <= 7,
    {
        self.to_sunday_zero_offset() + 1
    }

    /// Origin Rust (weekday.rs:128-147):
    ///     pub const fn wrapping_add(self, days: i64) -> Weekday {
    ///         let start = self.to_monday_zero_offset() as i64;
    ///         // We are careful to `rem_euclid` on `rhs` before doing
    ///         // wrapping arithmetic, otherwise the result is not
    ///         // correct. Namely, it would assume that, e.g., since
    ///         // `i64::MAX.rem_euclid(7)` is 0, then the next value would be
    ///         // `rem_euclid(7) == 1`. But `i64::MIN.rem_euclid(7)` is 6.
    ///         let end = (start.wrapping_add(days.rem_euclid(7)) % 7) as i8;
    ///         // Always valid because of the mod 7 above.
    ///         unwrapr!(
    ///             Weekday::from_monday_zero_offset(end),
    ///             "weekday is always 0..=6",
    ///         )
    ///     }
    /// Upstream doc (weekday.rs:127-133):
    ///   Add the given number of days to this weekday, using wrapping
    ///   arithmetic, and return the resulting weekday.
    ///   Adding a multiple of `7` (including `0`) is guaranteed to produce
    ///   the same weekday as this one.
    /// Ledger: the machine wrapping_add keeps its shape under the
    /// bound-hoisted no-wrap facts (both operands in 0..=6, sum in 0..=12,
    /// plain-sum identity -- the J3 finding-28 pattern); days' negative
    /// half of the domain discharges through the rem_euclid_7 Euclid
    /// obligation (the i64::MIN corner is upstream's own cited case).
    pub exec fn wrapping_add(self, days: i64) -> (r: Weekday)
        ensures
            (wd_monday_one(r) - 1)
                == spec_wrapping_add_m0(self, days as int),
    {
        let start = self.to_monday_zero_offset() as i64;
        let dre = rem_euclid_7(days);
        let sum = start + dre;
        let m = sum % 7i64;
        let end = m as i8;
        proof {
            assert(0 <= start as int && (start as int) < 7);
            assert(0 <= dre as int && (dre as int) < 7);
            let sumi: int = (start as int) + (dre as int);
            assert(sumi <= 12);
            assert(m as int == sumi % 7);
            assert((end as int) == sumi % 7);
            assert(0 <= sumi % 7 && sumi % 7 < 7);
            assert(
                spec_wrapping_add_m0(self, days as int)
                    == ((wd_monday_one(self) - 1) + (dre as int)) % 7
            );
            assert(
                ((wd_monday_one(self) - 1) + (dre as int)) % 7
                    == (end as int)
            );
        }
        let Some(w) = Weekday::from_monday_zero_offset(end) else {
            proof { assert(false); }
            unreachable!()
        };
        w
    }

    /// Origin Rust (weekday.rs:149-162):
    ///     pub const fn wrapping_sub(self, days: i64) -> Weekday {
    ///         // i64::MIN.rem_euclid(7) == 6
    ///         let days = match days.checked_neg() {
    ///             Some(days) => days,
    ///             None => -6,
    ///         };
    ///         self.wrapping_add(days)
    ///     }
    /// Upstream doc (weekday.rs:148-154):
    ///   Subtract the given number of days from this weekday, using wrapping
    ///   arithmetic, and return the resulting weekday.
    ///   Subtracting a multiple of `7` (including `0`) is guaranteed to
    ///   produce the same weekday as this one.
    /// std checked_neg has no vstd spec in this build (the J4b finding-12
    /// pit): it is inlined branch-for-branch; the only negation failure
    /// is i64::MIN, where upstream substitutes -6 (whose rem_euclid-7
    /// residue 1 matches 2^63 == 1 mod 7 -- the spec twin's Euclid
    /// residue is the same number on that corner, proven below).
    pub exec fn wrapping_sub(self, days: i64) -> (r: Weekday)
        ensures
            (wd_monday_one(r) - 1)
                == spec_wrapping_sub_m0(self, days as int),
    {
        let neg: i64 = if days == (-9223372036854775808i64) {
            -6i64
        } else {
            0i64 - days
        };
        proof {
            if days == (-9223372036854775808i64) {
                // (-(2^63)) % 7 == 6, so the residue of the substituted
                // -6 (whose rem_euclid-7 is 1) minus... both equal:
                // spec residue (0 - (days % 7)) % 7 == (0 - 6) % 7 == 1
                assert((neg % 7) as int == 1);
                assert((days as int) % 7 == 6);
                assert((0 - 6) % 7 == 1);
                assert(
                    spec_wrapping_sub_m0(self, days as int)
                        == ((wd_monday_one(self) - 1) + 1) % 7
                );
                assert(
                    spec_wrapping_add_m0(self, neg as int)
                        == ((wd_monday_one(self) - 1) + 1) % 7
                );
            } else {
                assert(
                    (neg as int) == 0 - (days as int)
                );
                let p: int = (days as int) % 7;
                assert(0 <= p < 7);
                assert((neg as int) % 7 == (0 - p) % 7);
                assert(
                    spec_wrapping_add_m0(self, neg as int)
                        == ((wd_monday_one(self) - 1)
                            + ((0 - p) % 7)) % 7
                );
                assert(
                    spec_wrapping_sub_m0(self, days as int)
                        == ((wd_monday_one(self) - 1)
                            + ((0 - p) % 7)) % 7
                );
            }
        }
        let w = self.wrapping_add(neg);
        proof {
            assert(
                (wd_monday_one(w) - 1)
                    == spec_wrapping_add_m0(self, neg as int)
            );
            assert(
                spec_wrapping_add_m0(self, neg as int)
                    == spec_wrapping_sub_m0(self, days as int)
            );
        }
        w
    }

    /// Origin Rust (weekday.rs:164-172):
    ///     pub const fn next(self) -> Weekday {
    ///         self.wrapping_add(1)
    ///     }
    /// Upstream doc (weekday.rs:163-169):
    ///   Returns the next weekday, wrapping around at the end of week to the
    ///   beginning of the week.
    ///   This is a convenience routing for calling [`Weekday::wrapping_add`]
    ///   with a value of `1`.
    pub exec fn next(self) -> (r: Weekday)
        ensures
            wd_monday_one(r)
                == (wd_monday_one(self) % 7) + 1,
    {
        self.wrapping_add(1i64)
    }

    /// Origin Rust (weekday.rs:174-182):
    ///     pub const fn previous(self) -> Weekday {
    ///         self.wrapping_sub(1)
    ///     }
    /// Upstream doc (weekday.rs:173-179):
    ///   Returns the previous weekday, wrapping around at the beginning of
    ///   week to the end of the week.
    ///   This is a convenience routing for calling [`Weekday::wrapping_sub`]
    ///   with a value of `1`.
    pub exec fn previous(self) -> (r: Weekday)
        ensures
            wd_monday_one(r)
                == if wd_monday_one(self) == 1 {
                    7
                } else {
                    wd_monday_one(self) - 1
                },
    {
        self.wrapping_sub(1i64)
    }

    /// Origin Rust (weekday.rs:184-193):
    ///     pub const fn since(self, other: Weekday) -> i8 {
    ///         (self.to_monday_zero_offset() - other.to_monday_zero_offset())
    ///             .rem_euclid(7)
    ///     }
    /// Upstream doc (weekday.rs:184-188):
    ///   Returns the number of days from `other` to this weekday.
    ///   Adding the returned number of days to `other` is guaranteed to sum
    ///   to this weekday. The number of days returned is guaranteed to be in
    ///   the range `0..=6`.
    pub exec fn since(self, other: Weekday) -> (r: i8)
        ensures
            r as int
                == (wd_monday_one(self) - wd_monday_one(other)) % 7
                && 0 <= r as int
                && (r as int) < 7,
    {
        let a = self.to_monday_zero_offset();
        let b = other.to_monday_zero_offset();
        let d = (a as i64) - (b as i64);
        let dr = rem_euclid_7(d);
        proof {
            assert((a as int) == wd_monday_one(self) - 1);
            assert((b as int) == wd_monday_one(other) - 1);
            assert((d as int) == (a as int) - (b as int));
            assert(-6 <= (d as int) && (d as int) <= 6);
            assert((dr as int) == ((a as int) - (b as int)) % 7);
            assert(((a as int) - (b as int)) % 7
                == ((wd_monday_one(self) - 1)
                    - (wd_monday_one(other) - 1)) % 7);
            assert(
                ((wd_monday_one(self) - 1) - (wd_monday_one(other) - 1))
                    % 7
                == (wd_monday_one(self) - wd_monday_one(other)) % 7
            );
        }
        dr as i8
    }

    /// Origin Rust (weekday.rs:195-203):
    ///     pub const fn until(self, other: Weekday) -> i8 {
    ///         other.since(self)
    ///     }
    /// Upstream doc (weekday.rs:195-199):
    ///   Returns the number of days until `other` from this weekday.
    ///   Adding the returned number of days to this weekday is guaranteed to
    ///   sum to `other` weekday. The number of days returned is guaranteed
    ///   to be in the range `0..=6`.
    pub exec fn until(self, other: Weekday) -> (r: i8)
        ensures
            r as int
                == (wd_monday_one(other) - wd_monday_one(self)) % 7
                && 0 <= r as int
                && (r as int) < 7,
    {
        other.since(self)
    }

    /// Origin Rust (weekday.rs:205-210):
    ///     pub const fn cycle_forward(self) -> WeekdaysForward {
    ///         WeekdaysForward { next: self }
    ///     }
    /// Upstream doc (weekday.rs:204-206):
    ///   Starting with this weekday, this returns an unending iterator that
    ///   cycles forward through the days of the week.
    pub exec fn cycle_forward(self) -> (r: WeekdaysForward)
        ensures wd_monday_one(r.next) == wd_monday_one(self),
    {
        WeekdaysForward { next: self }
    }

    /// Origin Rust (weekday.rs:212-217):
    ///     pub const fn cycle_reverse(self) -> WeekdaysReverse {
    ///         WeekdaysReverse { next: self }
    ///     }
    /// Upstream doc (weekday.rs:211-213):
    ///   Starting with this weekday, this returns an unending iterator that
    ///   cycles backward through the days of the week.
    pub exec fn cycle_reverse(self) -> (r: WeekdaysReverse)
        ensures wd_monday_one(r.next) == wd_monday_one(self),
    {
        WeekdaysReverse { next: self }
    }
}

// ===========================================================================
// WeekdaysForward / WeekdaysReverse (jcore weekday.rs:220-260)
// ===========================================================================

/// Origin Rust (weekday.rs:220-226):
///     /// An unending iterator of the days of the week.
///     pub struct WeekdaysForward { next: Weekday }
/// The upstream core::iter::Iterator impl (:228-237,
///     fn next(&mut self) -> Option<Weekday> {
///         let next = self.next;
///         self.next = self.next.wrapping_add(1);
///         Some(next)
///     })
/// materializes as the inherent next method below (trait faces are not
/// verifiable surfaces in this build); the FusedIterator marker impl
/// (:239) is a body-free type face. The two-state contract is the
/// old(self)/final(self) shape (probe-verified; J6/notes.md).
pub struct WeekdaysForward {
    pub next: Weekday,
}

impl WeekdaysForward {
    pub exec fn next(&mut self) -> (r: Option<Weekday>)
        ensures
            match r {
                Option::Some(w) =>
                    wd_monday_one(w) == wd_monday_one(old(self).next),
                Option::None => false,
            }
                && wd_monday_one(final(self).next)
                    == (wd_monday_one(old(self).next) % 7) + 1,
    {
        let n = self.next;
        self.next = self.next.wrapping_add(1i64);
        Option::Some(n)
    }
}

/// Origin Rust (weekday.rs:241-260): the reverse-cycling twin.
///     pub struct WeekdaysReverse { next: Weekday }
///     // impl Iterator: let next = self.next;
///     //     self.next = self.next.wrapping_sub(1); Some(next)
pub struct WeekdaysReverse {
    pub next: Weekday,
}

impl WeekdaysReverse {
    pub exec fn next(&mut self) -> (r: Option<Weekday>)
        ensures
            match r {
                Option::Some(w) =>
                    wd_monday_one(w) == wd_monday_one(old(self).next),
                Option::None => false,
            }
                && wd_monday_one(final(self).next)
                    == if wd_monday_one(old(self).next) == 1 {
                        7
                    } else {
                        wd_monday_one(old(self).next) - 1
                    },
    {
        let n = self.next;
        self.next = self.next.wrapping_sub(1i64);
        Option::Some(n)
    }
}

// ===========================================================================
// from_/to_ offset roundtrip panels (the upstream to_*-offset unit tests,
// jcore weekday.rs:346-392, transcribed as ensured exec witnesses: from
// every weekday, enclose the offset and read it back through the from
// face -- proof fns cannot call exec fns in this build, so the panel
// carries these as ensures-form exec witnesses, J6 probe finding)
// ===========================================================================

exec fn panel_roundtrip_monday_zero(w: Weekday) -> (r: Weekday)
    ensures wd_monday_one(r) == wd_monday_one(w),
{
    let o = w.to_monday_zero_offset();
    let Some(r) = Weekday::from_monday_zero_offset(o) else {
        proof { assert(false); }
        unreachable!()
    };
    r
}

exec fn panel_roundtrip_monday_one(w: Weekday) -> (r: Weekday)
    ensures wd_monday_one(r) == wd_monday_one(w),
{
    let o = w.to_monday_one_offset();
    let Some(r) = Weekday::from_monday_one_offset(o) else {
        proof { assert(false); }
        unreachable!()
    };
    r
}

exec fn panel_roundtrip_sunday_zero(w: Weekday) -> (r: Weekday)
    ensures wd_monday_one(r) == wd_monday_one(w),
{
    let o = w.to_sunday_zero_offset();
    let Some(r) = Weekday::from_sunday_zero_offset(o) else {
        proof { assert(false); }
        unreachable!()
    };
    r
}

exec fn panel_roundtrip_sunday_one(w: Weekday) -> (r: Weekday)
    ensures wd_monday_one(r) == wd_monday_one(w),
{
    let o = w.to_sunday_one_offset();
    let Some(r) = Weekday::from_sunday_one_offset(o) else {
        proof { assert(false); }
        unreachable!()
    };
    r
}

// ===========================================================================
// wrapping extremes panel (the upstream bug-catch regression points that
// the upstream tests pin: Tuesday.wrapping_add(i64::MAX) == Tuesday,
// weekday.rs:434; the Monday.wrapping_sub(i64::MIN + n) sweep,
// weekday.rs:475-480)
// ===========================================================================

/// Tuesday + i64::MAX: 2^63 == 1 (mod 7), so i64::MAX == 0 (mod 7) and
/// the day does not move (upstream test weekday.rs:431-435 -- "This
/// caught a bug where our wrapping arithmetic ... was incorrect when
/// overflow occurred").
exec fn panel_add_i64_max() -> (r: Weekday)
    ensures wd_monday_one(r) == 2 && r is Tuesday,
{
    let t = Weekday::Tuesday.wrapping_add(9223372036854775807i64);
    t
}

/// Monday - i64::MIN: the negation corner, upstream test
/// weekday.rs:477-480 -- "This found a bug where we were negating the
/// integer given and assuming it wouldn't panic." (Monday, Saturday,
/// Sunday, Tuesday at offsets -9223372036854775805..-8, i.e. delta days
/// 2^63-3 .. 2^63-2 .. 2^63-1 .. 2^63 -- all take the -6 substitution).
exec fn panel_sub_i64_min() -> (r: Weekday)
    ensures wd_monday_one(r) == 2 && r is Tuesday,
{
    let m = Weekday::Monday.wrapping_sub((-9223372036854775808i64));
    let m2 = Weekday::Monday.wrapping_sub((-9223372036854775807i64));
    let m3 = Weekday::Monday.wrapping_sub((-9223372036854775806i64));
    let m4 = Weekday::Monday.wrapping_sub((-9223372036854775805i64));
    proof {
        assert(wd_monday_one(m) == 2);
        assert(m is Tuesday);
        assert(m2 is Monday);
        assert(m3 is Sunday);
        assert(m4 is Saturday);
    }
    m
}

} // verus!
