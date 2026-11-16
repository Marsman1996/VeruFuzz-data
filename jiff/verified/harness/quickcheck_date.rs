//! Batch J2 harness -- the quickcheck date properties, transcribed from
//! upstream `#[cfg(test)] mod tests` quickcheck blocks into proof
//! theorems (the quickcheck quickcheck! invocations are the inventories'
//! harness surface; here the discard-at-extremes discipline becomes the
//! `spec_* is Some` precondition, and the from_bool assertion becomes the
//! ensures clause).
//!
//! Upstream source of record (crates/jiff-core/src/civil/date.rs, pin
//! 627c7358):
//!   quickcheck::quickcheck! {
//!       fn prop_tomorrow_yesterday_is_identity(d: Date)
//!           -> quickcheck::TestResult {
//!           let Ok(yesterday) = d.yesterday() else {
//!               return quickcheck::TestResult::discard()
//!           };
//!           quickcheck::TestResult::from_bool(yesterday.tomorrow() == Ok(d))
//!       }
//!
//!       fn prop_yesterday_tomorrow_is_identity(d: Date)
//!           -> quickcheck::TestResult {
//!           let Ok(tomorrow) = d.tomorrow() else {
//!               return quickcheck::TestResult::discard()
//!           };
//!           quickcheck::TestResult::from_bool(tomorrow.yesterday() == Ok(d))
//!       }
//!   }
//! (jcore date.rs:2047-2060; the Arbitrary instance feeds
//! Date::new_constrain over the full Year/Month/Day ranges, so the law
//! quantifies over every reachable calendar date.)
//!
//! Deferred properties, recorded for the next batch (see
//! out/kverus-run/J2/notes.md):
//!   * prop_add_equals_sub (jcore date.rs:2062-2067) and the main-crate
//!     4-lot (prop_checked_add_then_sub, prop_checked_sub_then_add,
//!     prop_since_then_add, prop_until_then_sub, crates/jiff/src/civil/
//!     date.rs:3765-3818): each needs either the Span surface (cut from
//!     the J2 closure by inventory trimming principle 5) or the
//!     Neri-Schneider roundtrip (deferred), so no theorem form is
//!     available at this batch's spec altitude.

use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod jiff_lib;

verus! {

use jiff_lib::date::{
    Date, days_in_month_spec, spec_tomorrow, spec_yesterday, valid_date,
};

/// Theorem form of jcore prop_tomorrow_yesterday_is_identity
/// (date.rs:2048-2053): the yesterday-taken-at-least-once dates give
/// tomorrow(yesterday(d)) == d. Upstream asserts equality on the
/// Result<Date>; the Option face is the J1/J2 error-model reflection.
pub proof fn prop_tomorrow_yesterday_is_identity(d: Date)
    requires
        valid_date(d),
        spec_yesterday(d) is Some,
    ensures
        match spec_yesterday(d) {
            Option::Some(yd) => spec_tomorrow(yd) == Option::Some(d),
            Option::None => false,
        },
{
    match spec_yesterday(d) {
        Option::None => {}
        Option::Some(yd) => {
            let y: int = d.year as int;
            let m: int = d.month as int;
            let dd: int = d.day as int;
            if dd > 1 {
                // yesterday: same year-month, day-1 inside the month, so
                // tomorrow steps back up within the month
                assert(yd.day as int == dd - 1);
                assert(((dd - 1) as int) < days_in_month_spec(y, m));
                assert(spec_tomorrow(yd) == Option::Some(Date {
                    year: yd.year,
                    month: yd.month,
                    day: (dd - 1 + 1) as i8,
                }));
                assert((dd - 1 + 1) as i8 == d.day);
            } else {
                // dd == 1 (validity gives dd >= 1)
                if m > 1 {
                    // yesterday landed on the last day of the previous
                    // month; tomorrow carries back to the 1st
                    assert(yd.month as int == m - 1);
                    assert(yd.day as int == days_in_month_spec(y, m - 1));
                    assert(spec_tomorrow(yd) == Option::Some(Date {
                        year: yd.year,
                        month: (m - 1 + 1) as i8,
                        day: 1,
                    }));
                    assert((m - 1 + 1) as i8 == d.month);
                } else {
                    // month == 1: yesterday landed on Dec 31 of the
                    // previous year (or was None at the minimum, which
                    // the requires excludes)
                    assert(yd.year as int == y - 1);
                    assert(yd.month as int == 12);
                    assert(yd.day as int == 31);
                    assert(spec_tomorrow(yd) == Option::Some(Date {
                        year: (y - 1 + 1) as i16,
                        month: 1,
                        day: 1,
                    }));
                    assert((y - 1 + 1) as i16 == d.year);
                }
            }
        }
    }
}

/// Theorem form of jcore prop_yesterday_tomorrow_is_identity
/// (date.rs:2055-2060).
pub proof fn prop_yesterday_tomorrow_is_identity(d: Date)
    requires
        valid_date(d),
        spec_tomorrow(d) is Some,
    ensures
        match spec_tomorrow(d) {
            Option::Some(td) => spec_yesterday(td) == Option::Some(d),
            Option::None => false,
        },
{
    match spec_tomorrow(d) {
        Option::None => {}
        Option::Some(td) => {
            let y: int = d.year as int;
            let m: int = d.month as int;
            let dd: int = d.day as int;
            if dd < days_in_month_spec(y, m) {
                // tomorrow: same month, day+1
                assert(td.day as int == dd + 1);
                assert(((dd + 1) as int) > 1);
                assert(spec_yesterday(td) == Option::Some(Date {
                    year: td.year,
                    month: td.month,
                    day: (dd + 1 - 1) as i8,
                }));
                assert((dd + 1 - 1) as i8 == d.day);
            } else if m < 12 {
                // last day of the month: tomorrow is the 1st of the next
                // month; yesterday steps back to the last day of d's
                // month, which is dd itself
                assert(td.month as int == m + 1);
                assert(td.day as int == 1);
                assert(((m + 1) as int) > 1);
                assert(spec_yesterday(td) == Option::Some(Date {
                    year: td.year,
                    month: (m + 1 - 1) as i8,
                    day: days_in_month_spec(y, m) as i8,
                }));
                assert(days_in_month_spec(y, m) == dd);
                assert((m + 1 - 1) as i8 == d.month);
            } else {
                // Dec 31 (or Dec 30 in the 28-day non-carry case is
                // impossible: dd == days_in_month and the days_in_month
                // face gives December 31 days): tomorrow is Jan 1 of the
                // next year
                assert(days_in_month_spec(y, 12) == 31);
                assert(dd == 31);
                assert(td.year as int == y + 1);
                assert(td.month as int == 1);
                assert(td.day as int == 1);
                assert(spec_yesterday(td) == Option::Some(Date {
                    year: (y + 1 - 1) as i16,
                    month: 12,
                    day: 31,
                }));
                assert((y + 1 - 1) as i16 == d.year);
            }
        }
    }
}

} // verus!

// Standalone driver form (the src/ crate root carries its own main; this
// file's module mount does not include it).
fn main() {}
