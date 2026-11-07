//! humantime (GitHub tip 997ff56, fetch.conf COMMIT) x Verus -- **src/date.rs
//! transcription** (verus 0.2026.10.29; mirrors upstream `DB/code/src/date.rs`).
//!
//! This module carries section F1: the pre-epoch `.expect` panic reproduction
//! of the `format_rfc3339` family / `Rfc3339Timestamp::fmt` (upstream
//! date.rs:261-264).
//!
//! Reproduced obligation: `Rfc3339Timestamp::fmt` (upstream date.rs:257-380, the
//! single converging point of the five `format_rfc3339*` family variants and
//! the `Display` of `Timestamp`) executes `.expect("all times should be after
//! the epoch")` (upstream date.rs:263-264) on a valid `SystemTime` **earlier
//! than the Unix epoch** and panics; the same fmt takes the graceful
//! `Err(fmt::Error)` branch (upstream date.rs:268-270) for the far future
//! (secs >= 253_402_300_800, year 9999). Neither of the two rustdoc blocks
//! (the `format_rfc3339` series and `Rfc3339Timestamp`) declares any
//! `# Panics`.
//!
//! Method (the state after the migrate -> spec -> fix loop):
//!   1. Modeling: `SystemTime` is built on signed seconds `i64` (Unix
//!      `tv_sec`; Windows FILETIME likewise covers pre-1970 instants);
//!      `duration_since(UNIX_EPOCH)` is transcribed per the documented std
//!      semantics (pre-epoch => Err(SystemTimeError)) as
//!      `t >= 0 ? Some(t) : None`, in spec+exec twins;
//!   2. L0: verbatim transcription of upstream date.rs:261-270 (expect
//!      expanded as match/Err => panic; the far-future check kept verbatim)
//!      => the obligation failure lands exactly on the expect/panic branch
//!      line (Verus encodes an explicit panic as `requires false`,
//!      std_specs/core.rs);
//!   3. Fix counter-witness (Fix Code): the Err branch returns `fmt::Error`
//!      (modeled `Err(())`), the same posture as the far-future handling --
//!      this variant passes all obligations and doubles as the two control
//!      groups (epoch => Ok; far future => graceful Err);
//!   4. Reachability bridge: `t == -1` (UNIX_EPOCH - 1s) has no documented
//!      precondition, so duration_since yields None => the panic branch is
//!      reachable;
//!   5. Scope cut: the civil-calendar rendering after the far-future check
//!      inside `fmt` (the LEAPOCH divisions, the months loop, the 30-byte
//!      buffer) is irrelevant to this obligation (the panic site sits above
//!      it) and is short-circuited by returning `Ok(())` -- an out-of-scope
//!      downgrade, not an erasure of the target site.
//!
//! Runtime double confirmation: swapping `fn main` to call
//! `timestamp_fmt_upstream(-1, 0)` and running `verus --no-verify --compile`
//! yields exit 101 with the panic message `all times should be after the
//! epoch`, matching upstream date.rs:264:14 (record:
//! `out/issue-report-bugfinder-f1.md`).
//!
//! Verdict: this file expects **exactly 1 error** on the panic line of
//! `timestamp_fmt_upstream` (the transcription of upstream date.rs:264, i.e.
//! the `panic!("all times should be after the epoch")` line in this file);
//! all the rest (fixed/control/family theorems + the section-P1 parsing-side
//! family) is verified. Section P1: the parse_rfc3339/_weak parsing-side
//! sem families live in the lower half of this file (the two_digits numeric
//! chain, the calendar leap_years, the frac Scanner, the strict/weak
//! layers); the UT exemplars sit in verified/harness/ut_parse.rs.

use vstd::prelude::*;
use vstd::arithmetic::mul::{lemma_mul_inequality, lemma_mul_is_distributive_add};

verus! {


// ---------- spec layer (witness style) ----------

/// Output semantic codes (no-spec-enum idiom: pub open spec const).
pub open spec const OUT_OK: int = 0;            // normal formatting
pub open spec const OUT_FMT_ERROR: int = 1;     // graceful Err(fmt::Error) (upstream:269)
pub open spec const OUT_PANIC_EXPECT: int = 2;  // the .expect trigger of upstream:264

/// Upstream date.rs:268: the year-9999 upper bound (the only bound the fmt
/// gracefully rejects).  (Corresponds to the upstream `if secs_since_epoch >=
/// 253_402_300_800`.)
pub open spec const RFC3339_SECS_MAX: int = 253_402_300_800;

/// Precision-tier model (int codes of the upstream date.rs:51-58 Precision enum).
pub open spec const PREC_SMART: int = 0;   // upstream Precision::Smart
pub open spec const PREC_SECONDS: int = 1; // upstream Precision::Seconds
pub open spec const PREC_MILLIS: int = 2;  // upstream Precision::Millis
pub open spec const PREC_MICROS: int = 3;  // upstream Precision::Micros
pub open spec const PREC_NANOS: int = 4;   // upstream Precision::Nanos

/// Machine precondition of `Result::expect`: the receiver must be `Ok`.
/// `SystemTime::duration_since(UNIX_EPOCH)` is exactly `Err(SystemTimeError)`
/// for pre-epoch values (documented std behavior; the signed-seconds model
/// covers both Unix tv_sec and Windows FILETIME -- both can represent
/// pre-1970-01-01 instants).
pub open spec fn duration_since_ok(t_secs: i64) -> bool {
    t_secs@ >= 0
}

/// spec/exec twin semantic faces of `duration_since` (None iff Err).
pub open spec fn duration_since_spec(t_secs: i64) -> (r: Option<u64>) {
    if t_secs >= 0 { Some(t_secs as u64) } else { None }
}

/// Spec transcription of `Rfc3339Timestamp::fmt` (upstream date.rs:262-270):
/// the sole implementation every `format_rfc3339*` variant and the `Display`
/// of `Timestamp` reaches; nanos only affect sub-second rendering (out of
/// scope) and never the three-way exit.
pub open spec fn timestamp_fmt_sem(t_secs: i64, t_nanos: u32) -> int {
    if !duration_since_ok(t_secs) {
        OUT_PANIC_EXPECT                   // upstream:260-264: expect on Err
    } else if t_secs@ >= RFC3339_SECS_MAX {
        OUT_FMT_ERROR                      // upstream:268-270: graceful cap
    } else {
        OUT_OK
    }
}

// ---------- exec layer: verbatim L0 transcription ----------

/// Exec face of `duration_since(UNIX_EPOCH)`: the model implementation is
/// equal to the spec (signed-seconds decision, no panic surface).
pub exec fn duration_since_model(t_secs: i64) -> (r: Option<u64>)
    ensures
        r == duration_since_spec(t_secs),
{
    if t_secs >= 0 { Some(t_secs as u64) } else { None }
}

/// **Upstream transcription** (upstream date.rs:261-270). The rustdoc declares
/// no precondition => requires empty. The panic site (the `.expect` of
/// upstream date.rs:264) is transcribed in its expanded form (Err => panic):
/// this is the F1 target site -- the obligation failure must land on this
/// line; external_body/erasure is forbidden.
/// Return value: `Ok(())` = normal formatting (the tail rendering is
/// short-circuited, out of scope), `Err(())` = `fmt::Error`.
/// Upstream doc (date.rs:60-60):
///   A wrapper type that allows you to Display a SystemTime
pub exec fn timestamp_fmt_upstream(t_secs: i64, t_nanos: u32) -> (r: Result<(), ()>) {
    let dur = match duration_since_model(t_secs) {   // upstream:261-263
        Some(d) => d,
        None => panic!("all times should be after the epoch"), // upstream:264 <- EXPECTED
    };
    let secs_since_epoch: u64 = dur;                 // upstream:265 dur.as_secs()
    let nanos: u32 = t_nanos;                        // upstream:266 dur.subsec_nanos()
    //  (out of scope) nanos only affect the buffer contents across
    //  Smart/precise tiers (upstream:345-375)
    if secs_since_epoch >= 253_402_300_800 {         // upstream:268
        return Err(());                              // upstream:269-270: graceful year-9999 cap
    }
    //  (out-of-scope short-circuit) the LEAPOCH calendar rendering and the
    //  30-byte buffer (upstream:273-378) have no bearing on this obligation
    Ok(())
}

// ---------- Fix counter-witness (Fix Code: the Err branch matches the far-future handling) ----------

/// The issue-draft fix form: the Err branch of `duration_since` returns
/// `fmt::Error` instead of expect -- the same posture as the existing
/// far-future branch of the same function (upstream:268-270).
/// With that, all obligations of this function pass, and it doubles as the
/// two control groups.  (The cross-file caller is
/// src/lib.rs::timestamp_display_entry_fixed -- the Display delegation of
/// wrapper.rs:131-135.)
/// Upstream doc (date.rs:60-60):
///   A wrapper type that allows you to Display a SystemTime
pub exec fn timestamp_fmt_fixed(t_secs: i64, t_nanos: u32) -> (r: Result<(), ()>)
    ensures
        timestamp_fmt_sem(t_secs, t_nanos) == OUT_OK ==> r matches Ok(_),
        timestamp_fmt_sem(t_secs, t_nanos) == OUT_FMT_ERROR ==> r matches Err(_),
        timestamp_fmt_sem(t_secs, t_nanos) == OUT_PANIC_EXPECT ==> r matches Err(_),
{
    let dur = match duration_since_model(t_secs) {
        Some(d) => d,
        None => return Err(()),          // FIX: pre-epoch => fmt::Error (same posture as far-future)
    };
    let secs_since_epoch: u64 = dur;
    if secs_since_epoch >= 253_402_300_800 {
        return Err(());
    }
    Ok(())
}

// ---------- family entries (upstream:210-248 five constructors; Display converges lazily) ----------

/// `format_rfc3339(system_time)` (upstream:210-212): builds a Smart-precision
/// Rfc3339Timestamp -- **never panics**; the panic surface sits in the lazy
/// Display fmt (timestamp_fmt_* above). The five variants differ only in the
/// precision tier (u64 codes 0..=4 on the exec face, mirroring spec consts PREC_*).
/// Upstream doc (date.rs:203-209):
///   Format an RFC3339 timestamp `2018-02-14T00:28:07Z`
///   This function formats timestamp with smart precision: i.e. if it has no
///   fractional seconds, they aren't written at all. And up to nine digits if
///   they are.
///   The value is always UTC and ignores system timezone.
pub exec fn format_rfc3339_entry(t_secs: i64, t_nanos: u32) -> (r: (i64, u32, u64))
    ensures
        r == (t_secs, t_nanos, 0u64),      // PREC_SMART
{
    (t_secs, t_nanos, 0)                   // upstream:211 Rfc3339Timestamp(t, Smart)
}

/// `format_rfc3339_seconds(system_time)` (upstream:219-221): the Seconds tier.
/// Upstream doc (date.rs:214-218):
///   Format an RFC3339 timestamp `2018-02-14T00:28:07Z`
///   This format always shows timestamp without fractional seconds.
///   The value is always UTC and ignores system timezone.
pub exec fn format_rfc3339_seconds_entry(t_secs: i64, t_nanos: u32) -> (r: (i64, u32, u64))
    ensures
        r == (t_secs, t_nanos, 1u64),      // PREC_SECONDS
{
    (t_secs, t_nanos, 1)                   // upstream:220
}

/// `format_rfc3339_millis(system_time)` (upstream:228-230): the Millis tier.
/// Upstream doc (date.rs:223-227):
///   Format an RFC3339 timestamp `2018-02-14T00:28:07.000Z`
///   This format always shows milliseconds even if millisecond value is zero.
///   The value is always UTC and ignores system timezone.
pub exec fn format_rfc3339_millis_entry(t_secs: i64, t_nanos: u32) -> (r: (i64, u32, u64))
    ensures
        r == (t_secs, t_nanos, 2u64),      // PREC_MILLIS
{
    (t_secs, t_nanos, 2)                   // upstream:229
}

/// `format_rfc3339_micros(system_time)` (upstream:237-239): the Micros tier.
/// Upstream doc (date.rs:232-236):
///   Format an RFC3339 timestamp `2018-02-14T00:28:07.000000Z`
///   This format always shows microseconds even if microsecond value is
///   zero.
///   The value is always UTC and ignores system timezone.
pub exec fn format_rfc3339_micros_entry(t_secs: i64, t_nanos: u32) -> (r: (i64, u32, u64))
    ensures
        r == (t_secs, t_nanos, 3u64),      // PREC_MICROS
{
    (t_secs, t_nanos, 3)                   // upstream:238
}

/// `format_rfc3339_nanos(system_time)` (upstream:246-248): the Nanos tier.
/// Upstream doc (date.rs:241-245):
///   Format an RFC3339 timestamp `2018-02-14T00:28:07.000000000Z`
///   This format always shows nanoseconds even if nanosecond value is zero.
///   The value is always UTC and ignores system timezone.
pub exec fn format_rfc3339_nanos_entry(t_secs: i64, t_nanos: u32) -> (r: (i64, u32, u64))
    ensures
        r == (t_secs, t_nanos, 4u64),      // PREC_NANOS
{
    (t_secs, t_nanos, 4)                   // upstream:247
}


/* ================================================================
 * Section P1: parse_rfc3339 / parse_rfc3339_weak -- parsing-side
 * transcription
 *  (mirrors upstream date.rs:64-201)
 *
 * Coverage: two_digits (:64-75), parse_rfc3339 (:84-93),
 * the delimiter/digit-pair extraction/calendar numeric chain of parse_rfc3339_weak (:108-165),
 * the fractional-digit Scanner (:167-189), the tail Z / segment-length checks (:187-188),
 *  the total_seconds cap (:191-194) and the UNIX_EPOCH re-composition (:196).
 *
 * Modeling: the SystemTime output is (secs: u64, nanos: u32) relative to
 * the epoch, always post-epoch (same family as the section-F1
 * signed-seconds model). The input string is carried as Vec<u8>/Seq<u8>
 * restricted to the ASCII domain (upstream scans by Unicode char;
 * non-ASCII input is left to runtime re-confirmation, see the verdict note).
 * Multi-byte positions such as the µ of "µs" are outside this domain; no
 * in-domain divergence is observed for post-2000-01-01 inputs.
 * Error codes: the int model of the three upstream Error enum variants.
 * ================================================================ */

// ---------- error codes (the int model of the upstream date.rs:29-37 Error enum) ----------

/// upstream `Error::InvalidFormat` ("timestamp format is invalid", :44-46).
/// exec/spec dual-read const (the exec face cannot read a spec const; the
/// isize carries the int codes of the three variants).
pub const DERR_INVALID_FORMAT: isize = 10;
/// upstream `Error::OutOfRange` ("numeric component is out of range", :43-45).
pub const DERR_OUT_OF_RANGE: isize = 11;
/// upstream `Error::InvalidDigit` ("bad character where digit is expected", :42-44).
pub const DERR_INVALID_DIGIT: isize = 12;

/// Upstream date.rs:23: `max::SECONDS` of the 64-bit cfg (the last second of year 9999).
pub open spec const DATE_MAX_SECONDS: int = 253_402_300_800 - 1;

// ---------- input-layer byte predicates and two_digits (upstream date.rs:64-75) ----------

/// ASCII digit decision (the in-domain counterpart of upstream `char::to_digit(10)`).
pub open spec fn is_digit_byte(b: u8) -> bool {
    48 <= b@ <= 57
}

/// ASCII digit byte -> decimal value (0..=9).
pub open spec fn digit_val(b: u8) -> int {
    b@ - 48
}

/// `two_digits` (upstream date.rs:64-75) spec: two digits -> decimal value,
/// any non-digit -> None (the None face of upstream `.ok_or(Error::InvalidDigit)`).
pub open spec fn two_digits_sem(b1: u8, b2: u8) -> (r: Option<u64>) {
    if is_digit_byte(b1) && is_digit_byte(b2) {
        Some(((digit_val(b1) * 10 + digit_val(b2)) as u64))
    } else {
        None
    }
}

/// `two_digits` exec transcription (upstream date.rs:64-75; `b as char` +
/// `to_digit(10)` is just the byte-value difference in the ASCII domain).
/// The output bound <= 99 is the source of the later numeric chain's requires.
/// Upstream doc (date.rs:65-65):
///   Converts two digits given in ASCII to its proper decimal representation.
pub exec fn two_digits_model(b1: u8, b2: u8) -> (r: Option<u64>)
    ensures
        r === two_digits_sem(b1, b2),
        r.is_Some() ==> r.get_Some_0()@ <= 99,
{
    if b1 >= b'0' && b1 <= b'9' && b2 >= b'0' && b2 <= b'9' {
        Some(((b1 - b'0') as u64) * 10 + ((b2 - b'0') as u64))
    } else {
        None
    }
}

// ---------- leap year and the month table (upstream date.rs:136-152 / :199-201) ----------

/// `is_leap_year` spec (upstream date.rs:199-201).
pub open spec fn is_leap_year_spec(y: u64) -> bool {
    y@ % 4 == 0 && (y@ % 100 != 0 || y@ % 400 == 0)
}

/// `is_leap_year` exec transcription (upstream date.rs:199-201).
pub exec fn is_leap_year_model(y: u64) -> (r: bool)
    ensures
        r == is_leap_year_spec(y),
{
    y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)
}

/// Month-table spec (the match of upstream date.rs:137-152): Some((ydays0, mdays));
/// month outside 1..=12 -> None (upstream `_ => return Err(OutOfRange)`).
pub open spec fn month_days_sem(month: u64, leap: bool) -> (r: Option<(u64, u64)>) {
    if month@ == 1 { Some((0, 31)) }
    else if month@ == 2 && leap { Some((31, 29)) }
    else if month@ == 2 { Some((31, 28)) }
    else if month@ == 3 { Some((59, 31)) }
    else if month@ == 4 { Some((90, 30)) }
    else if month@ == 5 { Some((120, 31)) }
    else if month@ == 6 { Some((151, 30)) }
    else if month@ == 7 { Some((181, 31)) }
    else if month@ == 8 { Some((212, 31)) }
    else if month@ == 9 { Some((243, 30)) }
    else if month@ == 10 { Some((273, 31)) }
    else if month@ == 11 { Some((304, 30)) }
    else if month@ == 12 { Some((334, 31)) }
    else { None }
}

/// Month-table exec transcription (upstream date.rs:137-152).
pub exec fn month_days_model(month: u64, leap: bool) -> (r: Option<(u64, u64)>)
    ensures
        r === month_days_sem(month, leap),
{
    if month == 1 { Some((0, 31)) }
    else if month == 2 && leap { Some((31, 29)) }
    else if month == 2 { Some((31, 28)) }
    else if month == 3 { Some((59, 31)) }
    else if month == 4 { Some((90, 30)) }
    else if month == 5 { Some((120, 31)) }
    else if month == 6 { Some((151, 30)) }
    else if month == 7 { Some((181, 31)) }
    else if month == 8 { Some((212, 31)) }
    else if month == 9 { Some((243, 30)) }
    else if month == 10 { Some((273, 31)) }
    else if month == 11 { Some((304, 30)) }
    else if month == 12 { Some((334, 31)) }
    else { None }
}

// ---------- date numeric chain (upstream date.rs:128-165 + the :191 total) ----------

/// Parsing-side numeric-chain spec: domain/calendar errors -> None (all of
/// them correspond to the upstream OutOfRange checks at :128 / :151 / :154 --
/// same error-code origin, so merging changes no observable behavior);
/// otherwise Some(total_seconds) = time + days*86400 (upstream :191, the cap
/// check not yet included).
pub open spec fn rfc3339_date_sem(
    year: u64, month: u64, day: u64, hour: u64, minute: u64, second: u64,
) -> (r: Option<u64>) {
    if year@ < 1970 || hour@ > 23 || minute@ > 59 || second@ > 60 {
        None                                                   // upstream:128-129
    } else {
        let sec2: u64 = if second@ == 60 { 59u64 } else { second }; // upstream:132-134
        let leap: bool = is_leap_year_spec(year);             // upstream:136
        match month_days_sem(month, leap) {                  // upstream:137-152
            None => None,
            Some((ydays0, mdays)) => {
                if day@ > mdays@ || day@ == 0 {
                    None                                      // upstream:153-154
                } else {
                    let ydays: int = ydays0@
                        + (day@ - 1)                          // upstream:156
                        + (if leap && month@ > 2 { 1int } else { 0int }); // upstream:157-159
                    let leap_years: int = ((year@ - 1) - 1968) / 4
                        - ((year@ - 1) - 1900) / 100
                        + ((year@ - 1) - 1600) / 400;         // upstream:161-162
                    let days: int = (year@ - 1970) * 365 + leap_years + ydays; // :163
                    Some((sec2@ + minute@ * 60 + hour@ * 3600 + days * 86400) as u64) // :165+:191
                }
            }
        }
    }
}

/// Exec transcription of upstream date.rs:128-165 + :191. The requires are
/// exactly the two_digits output domain (each component <= 99, combined
/// year <= 9999) -- supplied by the parse-side caller; nanos are irrelevant.
/// All u64 overflow-freedom obligations are proved in the body (see the proof block).
pub exec fn rfc3339_date_part(
    year: u64, month: u64, day: u64, hour: u64, minute: u64, second: u64,
) -> (r: Option<u64>)
    requires
        year@ <= 9_999,
        month@ <= 99,
        day@ <= 99,
        hour@ <= 99,
        minute@ <= 99,
        second@ <= 99,
    ensures
        r === rfc3339_date_sem(year, month, day, hour, minute, second),
{
    if year < 1970 || hour > 23 || minute > 59 || second > 60 {
        return None;                                          // upstream:128-129
    }
    let second: u64 = if second == 60 { 59 } else { second }; // upstream:132-134
    let leap: bool = is_leap_year_model(year);                // upstream:136
    let (mut ydays, mdays): (u64, u64) = match month_days_model(month, leap) {
        Some((a, b)) => (a, b),
        None => return None,                                  // upstream:151
    };
    if day > mdays || day == 0 {
        return None;                                          // upstream:153-154
    }
    ydays += day - 1;                                         // upstream:156
    if leap && month > 2 {
        ydays += 1;                                           // upstream:157-159
    }
    let t1: u64 = (year - 1) - 1968;                          // upstream:161
    let t2: u64 = (year - 1) - 1900;
    let t3: u64 = (year - 1) - 1600;
    let leap_years: u64 = t1 / 4 - t2 / 100 + t3 / 400;       // upstream:162
    let days: u64 = (year - 1970) * 365 + leap_years + ydays; // upstream:163
    let time: u64 = second + minute * 60 + hour * 3600;       // upstream:165
    proof {
        // ---- overflow-freedom bounds (the requires domain + the post-gate intervals) ----
        // year-1970 in [0, 8029]
        assert(0 <= (year as int - 1970) <= 8029);
        // t1 in [1, 8030], so t1/4 <= 2007, t2/100 <= 80, t3/400 <= 20
        assert(1 <= (t1 as int) <= 8030);
        assert((t1 as int) / 4 <= 2007);
        assert((t2 as int) / 100 <= 80);
        assert((t3 as int) / 400 <= 20);
        assert(-80 <= (leap_years as int) <= 2027);
        // ydays <= 334 + 30 + 1 = 365
        assert(ydays as int <= 365);
        // days <= 8029*365 + 2027 + 365 = 2_932_937
        lemma_mul_inequality(year as int - 1970, 8029, 365);
        assert((year as int - 1970) * 365 <= 8029 * 365);
        assert(days as int <= 8029 * 365 + 2027 + 365);
        // days * 86400 <= 2_932_937 * 86_400 < u64::MAX
        lemma_mul_inequality(days as int, 2_932_937, 86_400);
        assert((days as int) * 86_400 < 18_446_744_073_709_551_615);
        // time <= 59 + 59*60 + 23*3600 = 86_399
        assert(time as int <= 86_399);
        assert((time as int) + (days as int) * 86_400 < 18_446_744_073_709_551_615);
    }
    Some(time + days * 86_400)                                // upstream:191
}

/// Value-core spec of `parse_rfc3339_weak` (the upstream :128-194 numeric
/// mainline + the :192 cap check): the value-face API without the fractional
/// string layer. None iff all OutOfRange exits.
pub open spec fn rfc3339_core_sem(
    year: u64, month: u64, day: u64, hour: u64, minute: u64, second: u64,
    nanos: u64,
) -> (r: Option<(u64, u32)>) {
    match rfc3339_date_sem(year, month, day, hour, minute, second) {
        None => None,
        Some(total) => {
            if total@ > DATE_MAX_SECONDS {
                None                                          // upstream:192-193
            } else {
                Some((total, nanos as u32))                   // upstream:196 re-composition
            }
        }
    }
}

/// Value-core exec of `parse_rfc3339_weak` (upstream :128-194 main chain)
/// with the :192 cap. The requires equal rfc3339_date_part's (the two_digits
/// domain) plus nanos < 1e9 (the std Duration subsec_nanos invariant).
pub exec fn rfc3339_core(
    year: u64, month: u64, day: u64, hour: u64, minute: u64, second: u64,
    nanos: u64,
) -> (r: Option<(u64, u32)>)
    requires
        year@ <= 9_999,
        month@ <= 99,
        day@ <= 99,
        hour@ <= 99,
        minute@ <= 99,
        second@ <= 99,
        nanos@ < 1_000_000_000,
    ensures
        r === rfc3339_core_sem(year, month, day, hour, minute, second, nanos),
{
    let total: u64 = match rfc3339_date_part(year, month, day, hour, minute, second) {
        None => return None,
        Some(t) => t,
    };
    //  (253_402_300_799u64 == DATE_MAX_SECONDS, as the exec-face literal)
    if total > 253_402_300_799u64 {
        return None;                                          // upstream:192-193
    }
    Some((total, nanos as u32))
}

// ---------- fractional-digit Scanner (upstream date.rs:167-189) ----------

/// Fractional-digit scan spec (a recursive mirror of the upstream
/// :169-186 for loop):
///   - 'Z': terminates Ok exactly at the last position, else InvalidDigit;
///   - '+': terminates Ok exactly at len-6 (the "+00:00" start), else InvalidDigit;
///   - digit: `nanos += mult * d; mult /= 10` (upstream :184-185);
///   - otherwise -> InvalidDigit; exhaustion -> Ok (the accumulated value).
/// Note: fractional digits are **silently truncated** once mult has dropped
/// to 0 (the semantic fact of upstream :185 `mult /= 10` -- digits past the
/// 9th no longer count; see the SPEC-DOC MISMATCH note at frac_scan_model).
pub open spec fn frac_scan_sem(b: Seq<u8>, idx: int, nanos: int, mult: int)
    -> (r: Result<u32, isize>)
    decreases b.len() - idx,
{
    // Base case sealed with idx >= b.len() (every legitimate call reaches the
    // base case at idx == b.len(); this shape keeps out-of-domain arguments
    // out of the recursion, so termination holds unconditionally)
    if idx >= b.len() {
        Ok(nanos as u32)
    } else if b[idx] == 0x5a {                                // b'Z'
        if idx + 1 == b.len() { Ok(nanos as u32) } else { Err(DERR_INVALID_DIGIT) }
    } else if b[idx] == 0x2b {                                // b'+'
        if b.len() - idx == 6 { Ok(nanos as u32) } else { Err(DERR_INVALID_DIGIT) }
    } else if is_digit_byte(b[idx]) {
        frac_scan_sem(b, idx + 1, nanos + mult * digit_val(b[idx]), mult / 10)
    } else {
        Err(DERR_INVALID_DIGIT)
    }
}

/// Fractional-digit scan exec transcription (the recursion relays the upstream
/// for loop; byte advancement is equivalent). The requires (a)
/// `nanos + 10*mult <= 1e9` and (b) `mult==0 => nanos < 1e9` are the closed form
/// of the loop invariant: they cover exactly the nanosecond bounds of every
/// intermediate state of the upstream scan (the input face of the 1e9
/// normalization invariant), so the :196 `Duration::new(total, nanos)` is
/// panic-free.
pub exec fn frac_scan_model(b: &Vec<u8>, idx: usize, nanos: u32, mult: u32)
    -> (r: Result<u32, isize>)
    requires
        idx@ <= b@.len(),
        nanos@ + 10 * mult@ <= 1_000_000_000,
        mult@ == 0 ==> nanos@ < 1_000_000_000,
    ensures
        r === frac_scan_sem(b@, idx as int, nanos as int, mult as int),
        r.is_Ok() ==> r.get_Ok_0()@ < 1_000_000_000,
        // SPEC-DOC MISMATCH (unreported): the "Any precision of fractional
        // digits" doc promise is unprovable -- past the 9th digit mult == 0
        // and the extra digits are silently truncated; the ensures above
        // carries the implementation-faithful truncating form.
    decreases b@.len() - idx@,
{
    if idx == b.len() {
        return Ok(nanos);
    }
    let byte: u8 = b[idx];
    if byte == b'Z' {                                         // upstream:172-175
        if idx + 1 == b.len() {
            return Ok(nanos);
        } else {
            return Err(DERR_INVALID_DIGIT);
        }
    }
    if byte == b'+' {                                         // upstream:176-181
        if b.len() - idx == 6 {
            return Ok(nanos);
        } else {
            return Err(DERR_INVALID_DIGIT);
        }
    }
    if !(byte >= b'0' && byte <= b'9') {
        return Err(DERR_INVALID_DIGIT);                       // upstream:184 ok_or
    }
    let d: u32 = (byte - b'0') as u32;
    proof {
        // u32 overflow-freedom: mult*d <= 9*mult <= 1e9 (invariant (a));
        // nanos+mult*d <= 1e9 < 2^32.
        lemma_mul_is_distributive_add(mult as int, d as int, 1);
        lemma_mul_inequality(d as int + 1, 10, mult as int);   // (d+1)*mult <= 10*mult
        assert((mult as int) * (d as int) + (mult as int) <= 10 * mult as int);
        assert((nanos as int) + (mult as int) * (d as int) < 4_294_967_296);
        // invariant (a) maintenance: nanos2 + 10*mult2 <= 1e9
        assert(10 * ((mult as int) / 10) <= mult as int);      // div/mod basics
        assert((mult as int) * (d as int) + 10 * ((mult as int) / 10) <= 10 * mult as int);
        // next-frame (b): mult2 == 0 => nanos2 < 1e9 (for 0 < mult: 1e9 - mult truncates)
        if mult / 10 == 0 && mult > 0 {
            assert(mult as int <= 9);
            assert((nanos as int) + (mult as int) * (d as int) <= 1_000_000_000 - (mult as int));
        }
    }
    let nanos2: u32 = nanos + mult * d;                       // upstream:184
    let mult2: u32 = mult / 10;                               // upstream:185
    proof {
        assert(nanos2 as int + 10 * (mult2 as int) <= 1_000_000_000);
    }
    frac_scan_model(b, idx + 1, nanos2, mult2)
}

// ---------- tail-suffix predicate (upstream date.rs:89 `s.ends_with("+00:00")` / :187) ----------

/// Spec face of `&b[19..] == b"+00:00"` / `s.ends_with("+00:00")`.
pub open spec fn ends_plus0000_sem(b: Seq<u8>) -> bool {
    b.len() >= 6
        && b[b.len() - 6] == 0x2b && b[b.len() - 5] == 0x30 && b[b.len() - 4] == 0x30
        && b[b.len() - 3] == 0x3a && b[b.len() - 2] == 0x30 && b[b.len() - 1] == 0x30
}

/// Exec transcription (byte-by-byte comparison, equal to `ends_with` in the ASCII domain).
pub exec fn ends_plus0000_model(b: &Vec<u8>) -> (r: bool)
    ensures
        r == ends_plus0000_sem(b@),
{
    let n: usize = b.len();
    n >= 6 && b[n - 6] == b'+' && b[n - 5] == b'0' && b[n - 4] == b'0'
        && b[n - 3] == b':' && b[n - 2] == b'0' && b[n - 1] == b'0'
}

// ---------- parse_rfc3339_weak full layer (upstream date.rs:108-197) ----------

/// Full-semantic spec of `parse_rfc3339_weak`: structural checks (:109-118) ->
/// two_digits extraction (:121-126) -> numeric chain (:128-165) ->
/// fractional/tail checks (:167-189) -> cap check (:192-193) -> Ok re-composition (:196).
pub open spec fn rfc3339_weak_value_sem(b: Seq<u8>) -> (r: Result<(u64, u32), isize>) {
    if b.len() < 19 {
        Err(DERR_INVALID_FORMAT)                              // upstream:109-110
    } else if b[4] != 0x2d || b[7] != 0x2d
        || (b[10] != 0x54 && b[10] != 0x20)
        || b[13] != 0x3a || b[16] != 0x3a {
        Err(DERR_INVALID_FORMAT)                              // upstream:113-118
    } else {
        let y1 = two_digits_sem(b[0], b[1]);                  // upstream:121
        let y2 = two_digits_sem(b[2], b[3]);
        let mo = two_digits_sem(b[5], b[6]);                  // upstream:122
        let da = two_digits_sem(b[8], b[9]);                  // upstream:123
        let ho = two_digits_sem(b[11], b[12]);                // upstream:124
        let mi = two_digits_sem(b[14], b[15]);                // upstream:125
        let se = two_digits_sem(b[17], b[18]);                // upstream:126
        if y1.is_None() || y2.is_None() || mo.is_None() || da.is_None()
            || ho.is_None() || mi.is_None() || se.is_None() {
            Err(DERR_INVALID_DIGIT)                            // upstream:121-126 `?`
        } else {
            let year: u64 = ((y1.get_Some_0()@ * 100 + y2.get_Some_0()@) as u64);
            match rfc3339_date_sem(year, mo.get_Some_0(), da.get_Some_0(),
                ho.get_Some_0(), mi.get_Some_0(), se.get_Some_0()) {
                None => Err(DERR_OUT_OF_RANGE),
                Some(total) => {
                    if b.len() >= 20 && b[19] == 0x2e {       // upstream:169
                        match frac_scan_sem(b, 20, 0, 100_000_000) {
                            Err(e) => Err(e),                 // upstream:175/:181/:184
                            Ok(n) => {
                                if total@ > DATE_MAX_SECONDS {
                                    Err(DERR_OUT_OF_RANGE)    // upstream:192-193
                                } else {
                                    Ok((total, n as u32))     // upstream:196
                                }
                            }
                        }
                    } else if b.len() != 19                    // upstream:187
                        && (b.len() > 25
                            || (b[19] != 0x5a && !ends_plus0000_sem(b))) {
                        Err(DERR_INVALID_FORMAT)               // upstream:188
                    } else if total@ > DATE_MAX_SECONDS {
                        Err(DERR_OUT_OF_RANGE)                // upstream:192-193
                    } else {
                        Ok((total, 0u32))                      // upstream:196
                    }
                }
            }
        }
    }
}

/// `parse_rfc3339_weak` exec transcription (upstream date.rs:108-197).
/// The ASCII-domain note on the requires: upstream scans by Unicode
/// `char`; multi-byte input >= 0x80 is left to runtime re-confirmation
/// (this model does not cover UTF-8 splitting).
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
pub exec fn parse_rfc3339_weak_model(b: &Vec<u8>) -> (r: Result<(u64, u32), isize>)
    requires
        b@.len() >= 19,
        forall |i: int| #![auto] 0 <= i < b@.len() ==> b@[i] <= 127,
    ensures
        r === rfc3339_weak_value_sem(b@),
{
    if b[4] != b'-' || b[7] != b'-'
        || (b[10] != b'T' && b[10] != b' ')
        || b[13] != b':' || b[16] != b':' {
        return Err(DERR_INVALID_FORMAT);                      // upstream:113-118
    }
    let year_h: u64 = match two_digits_model(b[0], b[1]) {    // upstream:121
        None => return Err(DERR_INVALID_DIGIT),
        Some(v) => v,
    };
    let year_l: u64 = match two_digits_model(b[2], b[3]) {
        None => return Err(DERR_INVALID_DIGIT),
        Some(v) => v,
    };
    let month: u64 = match two_digits_model(b[5], b[6]) {      // upstream:122
        None => return Err(DERR_INVALID_DIGIT),
        Some(v) => v,
    };
    let day: u64 = match two_digits_model(b[8], b[9]) {        // upstream:123
        None => return Err(DERR_INVALID_DIGIT),
        Some(v) => v,
    };
    let hour: u64 = match two_digits_model(b[11], b[12]) {    // upstream:124
        None => return Err(DERR_INVALID_DIGIT),
        Some(v) => v,
    };
    let minute: u64 = match two_digits_model(b[14], b[15]) {   // upstream:125
        None => return Err(DERR_INVALID_DIGIT),
        Some(v) => v,
    };
    let second: u64 = match two_digits_model(b[17], b[18]) {   // upstream:126
        None => return Err(DERR_INVALID_DIGIT),
        Some(v) => v,
    };
    let year: u64 = year_h * 100 + year_l;
    // Numeric main chain (upstream:128-165): domain/calendar error codes share
    // the same origin (both OutOfRange); folding them into rfc3339_date_part
    // changes no externally observable behavior.
    let total: u64 = match rfc3339_date_part(year, month, day, hour, minute, second) {
        None => return Err(DERR_OUT_OF_RANGE),
        Some(t) => t,
    };
    // Fractional digits (upstream:167-189)
    let nanos: u32 = if b.len() >= 20 && b[19] == b'.' {       // upstream:169
        match frac_scan_model(b, 20, 0, 100_000_000) {
            Err(e) => return Err(e),
            Ok(n) => n,
        }
    } else {
        if b.len() != 19                                      // upstream:187
            && (b.len() > 25
                || (b[19] != b'Z' && !ends_plus0000_model(b))) {
            return Err(DERR_INVALID_FORMAT);                  // upstream:188
        }
        0
    };
    //  (253_402_300_799u64 == DATE_MAX_SECONDS, as the exec-face literal)
    if total > 253_402_300_799u64 {                            // upstream:192
        return Err(DERR_OUT_OF_RANGE);                        // upstream:193
    }
    Ok((total, nanos))                                         // upstream:196
}

// ---------- parse_rfc3339 (the strict variant, upstream date.rs:84-93) ----------

/// Full-semantic spec of `parse_rfc3339`: length (:85-86) + 'T' / tail Z or
/// +00:00 (:89-90) -> delegation to weak (:92).
pub open spec fn parse_rfc3339_sem(b: Seq<u8>) -> (r: Result<(u64, u32), isize>) {
    if b.len() < 20 {
        Err(DERR_INVALID_FORMAT)                               // upstream:85-86
    } else if b[10] != 0x54                                    // upstream:89
        || (b[b.len() - 1] != 0x5a && !ends_plus0000_sem(b)) {
        Err(DERR_INVALID_FORMAT)                               // upstream:90
    } else {
        rfc3339_weak_value_sem(b)                              // upstream:92
    }
}

/// `parse_rfc3339` exec transcription (upstream date.rs:84-93).
/// Upstream doc (date.rs:77-83):
///   Parse RFC3339 timestamp `2018-02-14T00:28:07Z`
///   Supported features:
///   - Any precision of fractional digits `2018-02-14T00:28:07.133Z`.
///   - The UTC timezone can be indicated with `Z` or `+00:00`.
///   Unsupported feature: localized timestamps. Only UTC is supported.
pub exec fn parse_rfc3339_model(b: &Vec<u8>) -> (r: Result<(u64, u32), isize>)
    requires
        b@.len() >= 20,
        forall |i: int| #![auto] 0 <= i < b@.len() ==> b@[i] <= 127,
    ensures
        r === parse_rfc3339_sem(b@),
{
    if b[10] != b'T'                                           // upstream:89
        || (b[b.len() - 1] != b'Z' && !ends_plus0000_model(b)) {
        return Err(DERR_INVALID_FORMAT);                       // upstream:90
    }
    parse_rfc3339_weak_model(b)                                 // upstream:92
}

// ===========================================================================
// Proof lemmas (witness-style reachability/family/control theorems, placed at
// the end of the file so the exec implementation reads directly)
// ===========================================================================
/// PoC trigger: `format_rfc3339(UNIX_EPOCH - 1s)`. The documentation side
/// declares no precondition; `duration_since` on -1 is Err (documented std
/// behavior) => the expect branch is reachable.
pub proof fn f1_reachability_witness() {
    let t_secs: i64 = -1i64;
    assert(!duration_since_ok(t_secs));                 // duration_since => Err(1s)
    assert(duration_since_spec(-1i64) == None);
    assert(timestamp_fmt_sem(t_secs, 0u32) == OUT_PANIC_EXPECT);
}

/// Control 1: `format_rfc3339(UNIX_EPOCH)` => Ok("1970-01-01T00:00:00Z").
///  (upstream UT smoke_tests_format, date.rs:441-444)
pub proof fn control_epoch_ok() {
    assert(duration_since_ok(0i64));
    assert(0 < RFC3339_SECS_MAX);
    assert(timestamp_fmt_sem(0i64, 0u32) == OUT_OK);
}

/// Control 2 / the inconsistency evidence: the far future (>= the year-9999
/// threshold) is not a panic -- the same fmt returns `fmt::Error` gracefully;
/// the pre-epoch branch could have been handled in exactly the same posture.
///  (the graceful path of the upstream upper_bound UT)
pub proof fn control_far_future_graceful() {
    let t_secs: i64 = 253_402_300_800i64;
    assert(duration_since_ok(t_secs));
    assert(timestamp_fmt_sem(t_secs, 0u32) == OUT_FMT_ERROR);
}

/// Family theorem: **every** pre-epoch instant triggers the same panic (no
/// documented precondition excludes any of them).
pub proof fn f1_panic_is_a_family() {
    assert(forall |t: i64| t < 0 ==> timestamp_fmt_sem(t, 0u32) == OUT_PANIC_EXPECT);
}
}
