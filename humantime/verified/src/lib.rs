//! humantime (GitHub tip 997ff56, fetch.conf COMMIT) x Verus --
//! aggregate verification **crate root** (verus 0.2026.10.29)
//!
//! Mirrors the upstream `DB/code/src/{lib.rs, date.rs, duration.rs}` module
//! layout:
//!   - `src/date.rs`     section F1: the pre-epoch `.expect` panic
//!                       reproduction (the one expected error sits exactly on
//!                       the transcribed date.rs:264 line -- the reproduction
//!                       target itself)
//!   - `src/duration.rs` section F2: positive verification of the tip
//!                       `add_current` + the parse_unit numeric chain,
//!                       section F3: the library-body transcription (fmt
//!                       components spec/exec); its UT roundtrip
//!                       value-layer theorems live in harness/roundtrip.rs
//!   - `src/lib.rs` (this file) cross-file delegation entries (the thin
//!                       FromStr / Display wrappers of wrapper.rs) -- the
//!                       caller-side obligations land here
//!
//! The `pub use` face of the upstream lib.rs (mapped to model names):
//!   pub use self::date::{format_rfc3339, ..., parse_rfc3339, ...}
//!   pub use self::duration::{format_duration, parse_duration, ...}
//!   pub use self::wrapper::{Duration, Timestamp}  wrapper merged into this
//!   root's delegation entries (the upstream wrapper.rs's 135 lines become
//!   the entry fns here).
//!
//! Run: VERUS_Z3_PATH=<z3> <verus>/source/target-verus/release/verus \
//!     database/humantime/verified/src/lib.rs
//! Verdict: exactly 1 error in total (the panic line in src/date.rs = the F1
//! reproduction anchor, upstream date.rs:264); all the rest verified -- all
//! obligations of the cross-file entries are discharged at the call sites
//! (this file), including the parsing-side delegations
//! (timestamp_from_str_entry / duration_from_str_entry_full).

use vstd::prelude::*;

mod date;
mod duration;

verus! {


// ---------- cross-file delegation entries (upstream wrapper.rs) ----------

/// Upstream wrapper.rs:131-135: `Display for Timestamp::fmt` delegates to
/// `format_rfc3339(self.0).fmt(f)` -> date.rs's `Rfc3339Timestamp::fmt`. In
/// the fix (tip-suggested) form the whole chain passes its obligations;
/// the panic obligation of `timestamp_fmt_upstream` (the bug form) lives
/// inside `src/date.rs` (the reproduction anchor).
/// Controls: epoch => Ok (UT smoke); far future => a graceful Err
/// (fmt::Error).
/// Upstream doc (date.rs:203-209):
///   Format an RFC3339 timestamp `2018-02-14T00:28:07Z`
///   This function formats timestamp with smart precision: i.e. if it has no
///   fractional seconds, they aren't written at all. And up to nine digits if
///   they are.
///   The value is always UTC and ignores system timezone.
pub exec fn timestamp_display_entry_fixed(t_secs: i64, t_nanos: u32) -> (r: Result<(), ()>)
    ensures
        t_secs@ == 0 ==> r matches Ok(_),    // UT smoke: epoch => "1970-01-01T00:00:00Z"
        t_secs@ >= 253_402_300_800 ==> r matches Err(_),  // year-9999 cap: graceful Err
        t_secs@ < 0 ==> r matches Err(_),   // fixed form: pre-epoch graceful Err
{
    date::timestamp_fmt_fixed(t_secs, t_nanos)
}

/// Upstream wrapper.rs:86-91: `FromStr for Duration::from_str` delegates to
/// `parse_duration(s)` -> the Parser/parse_unit/add_current chain of
/// duration.rs. The numeric-core obligations are discharged through
/// `duration::parse_unit_core` (at this call site): the UT exemplar
/// "12min" (test_units, upstream duration.rs:499) -> 720s.
/// Upstream doc (wrapper.rs:9-24):
///   A wrapper for duration that has `FromStr` implementation
///   This is useful if you want to use it somewhere where `FromStr` is
///   expected.
///   See `parse_duration` for the description of the format.
pub exec fn duration_from_str_entry_12min() -> (r: Result<(u64, u32), ()>)
    ensures
        r === Ok((720u64, 0u32)),
        duration::result_sat_sem(r, duration::parse_unit_core_sem(12, 4, 0, 0)),
        duration::result_sat_sem(r, duration::add_current_sem(720, 0, 0, 0)),
{
    duration::parse_unit_core(12, 4, 0, 0)
}

/// Upstream wrapper.rs:124-129: `FromStr for Timestamp` delegates to
/// `parse_rfc3339_weak(s).map(Timestamp)` -- the weak variant (the wrapper
/// doc states "The 'weak' format is used").
/// Upstream doc (date.rs:95-107):
///   Parse RFC3339-like timestamp `2018-02-14 00:28:07`
///   Supported features:
///   1. Any precision of fractional digits `2018-02-14 00:28:07.133`.
///   2. Supports timestamp with or without either of `T`, `Z` or `+00:00`.
///   3. Anything valid for [`parse_rfc3339`](parse_rfc3339) is valid for this
///      function
///   Unsupported feature: localized timestamps. Only UTC is supported, even
///      if `Z` is not specified.
///   This function is intended to use for parsing human input. Whereas
///   `parse_rfc3339` is for strings generated programmatically.
pub exec fn timestamp_from_str_entry(b: &Vec<u8>) -> (r: Result<(u64, u32), isize>)
    requires
        b@.len() >= 19,
        forall |i: int| #![auto] 0 <= i < b@.len() ==> b@[i] <= 127,
    ensures
        r === date::rfc3339_weak_value_sem(b@),
{
    date::parse_rfc3339_weak_model(b)
}

/// Upstream wrapper.rs:86-91: `FromStr for Duration` delegates to
/// `parse_duration(s).map(Duration)`. The property contract forwards with
/// the callee (the "0" special case / empty input Empty / nanos normalized).
/// Upstream doc (duration.rs:338-363):
///   Parse duration object `1hour 12min 5s`
///   The duration object is a concatenation of time spans. Where each time
///   span is an integer number and a suffix. Supported suffixes:
///   * `nsec`, `ns` -- nanoseconds
///   * `usec`, `us`, `µs` -- microseconds
///   * `msec`, `ms` -- milliseconds
///   * `seconds`, `second`, `sec`, `s`
///   * `minutes`, `minute`, `min`, `m`
///   * `hours`, `hour`, `hr`, `hrs`, `h`
///   * `days`, `day`, `d`
///   * `weeks`, `week`, `wk`, `wks`, `w`
///   * `months`, `month`, `M` -- defined as 30.44 days
///   * `years`, `year`, `yr`, `yrs`, `y` -- defined as 365.25 days
pub exec fn duration_from_str_entry_full(b: &Vec<u8>)
    -> (r: Result<(u64, u32), (isize, usize, usize)>)
    ensures
        r.is_Ok() ==> r.get_Ok_0().1@ < duration::NANOS_PER_SEC,
        b@ == seq![0x30] ==> r === Ok((0u64, 0u32)),
        (b@ != seq![0x30] && duration::parse_first_char_sem(b@, 0).is_Ok()
            && duration::parse_first_char_sem(b@, 0).get_Ok_0().0.is_None())
            ==> r === Err((duration::P2_ERR_EMPTY, 0, 0)),
        (b@ != seq![0x30] && duration::parse_first_char_sem(b@, 0) matches Err(_))
            ==> r === Err((duration::P2_ERR_NUMBER_EXPECTED, 0, 0)),
{
    duration::parse_duration_model(b)
}

//  (the UT roundtrip value-layer entries (upstream duration.rs:715-741,
//   all_86400_seconds/random_*) live in verified/harness/roundtrip.rs,
//   referencing src/duration.rs via #[path] mod.)

}

fn main() {}
