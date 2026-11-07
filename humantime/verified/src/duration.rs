//! humantime (GitHub tip 997ff56, fetch.conf COMMIT) x Verus -- **src/duration.rs
//! transcription** (verus 0.2026.10.29; mirrors upstream `DB/code/src/duration.rs`).
//!
//! This module carries two sections:
//!   section F2 **positive verification**: the tip `add_current` (upstream
//!   duration.rs:294-303, guard `>=`) + the parse_unit numeric chain, verified
//!   panic-free under the documented contract (overflow => Err(NumberOverflow),
//!   duration.rs:41-51);
//!   section F3 library-body transcription: `fmt_components` /
//!   `format_duration_core` (the component decomposition of `FormattedDuration::fmt`,
//!   upstream duration.rs:429-459) + the shared reconstruction models
//!   secs/nanos_reconstruct kept in src; the UT roundtrip theorems live in
//!   verified/harness/roundtrip.rs (via #[path] mod, no duplicate fact source).
//!
//! Section F2 background: the 2.4.0 release's `if nsec > 1_000_000_000` (2.4.0
//! line duration.rs:296) is off by one operator, letting `nsec == 1e9` skip
//! normalization; the un-normalized nanos are handed to `Duration::new`
//! together with saturated seconds, triggering the "overflow in
//! Duration::new" panic at core/src/time.rs:201. The tip changed the guard to
//! **`>=`** (this pin tree's duration.rs:296) -- this module formally confirms:
//! **the fix exactly restores the L0/documented contract** (the old bug form's
//! obligation failure sits exactly at :301's Duration::new carry precondition).
//!
//! Section F3 contract source: the format_duration doc (upstream:375-391)
//! "guaranteed to have same value when using parse_duration" -- the
//! value-layer foundation of the roundtrip is proven here with lemmas; the
//! string layer (item_plural writing) is out of scope.
//!
//! Runtime double confirmation (section F2): after swapping `fn main` to call
//! `add_current_tip(0, 1_000_000_000, 18446744073709551615u64, 0)`,
//! `--no-verify --compile` runs **without panic**, returning Err (the trigger
//! input `"{u64::MAX}s 999999999ns 1ns"`); the 2.4.0 old form panics on the
//! same input at the real source (std Duration::new) with "overflow in
//! Duration::new" (core time.rs:201).
//!
//! Verdict: this file expects **0 errors** (all verified). Section P2: the
//! parse_duration Scanner state machine (the parse_first_char frozen-off rule
//! / frac_part / scan_num / scan_unit / the unit_resolved stub /
//! parse_unit_full_core / parse_spans_model / parse_duration_model) is
//! appended in the lower half; the UT exemplars and the F5 obligation
//! anchors sit in verified/harness/ut_parse.rs.

use vstd::prelude::*;
// (No standing call for this import remains in src, but removing it degrades
//  the z3 context of f2_tip_fractional_100_0m -- obligation set unchanged --
//  so it stays.)
use vstd::arithmetic::div_mod::{
    lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse, lemma_mod_mod,
    lemma_mod_pos_bound,
};

verus! {


/* ================================================================
 * Section F2: add_current (tip `>=`) positive verification + the parse_unit numeric chain
 * ================================================================ */

// ---------- A1/A2: constants and u64 checked semantics (vstd built-in assume_specification) ----------

pub open spec const U64_MAX: int = 18446744073709551615;
/// 1 second = 1e9 nanoseconds (the upstream:296-298 normalization base / the std Duration invariant upper bound).
pub open spec const NANOS_PER_SEC: int = 1_000_000_000;

// ---------- A3: the carry contract of core Duration::new (spec+exec twins) ----------

/// core `Duration::new(secs, nanos)`: when the checked_add of the `nanos/1e9`
/// carry into secs fails, the internal `.expect("overflow in Duration::new")`
/// panics (core/src/time.rs:201). That std condition is exactly the requires
/// of `duration_new_model` (the 2.4.0 bug reproduction anchor).
pub open spec fn duration_new_ok_spec(secs: u64, nanos: u32) -> bool {
    !(nanos@ >= NANOS_PER_SEC && secs@ == U64_MAX)
}

#[verifier::external_body] // body is core's; the *panic condition* is the harness contract itself
pub exec fn duration_new_model(secs: u64, nanos: u32) -> (r: (u64, u32))
    requires
        duration_new_ok_spec(secs, nanos),
    ensures
        true,
{
    (secs, nanos)
}

// ---------- L0: verbatim transcription of the tip's upstream duration.rs:294-303 ----------

/// Functional postcondition of the tip `add_current` (machine u64 parameters,
/// int-face @ views; `Option<(u64,u32)>`: None iff the upstream
/// Err(NumberOverflow)).
/// Characterization: `nsec1 = out_nanos + nsec` (:295 checked_add); if
/// `nsec1 >= 1e9` (the tip's :296 `>=`) carry `q = nsec1/1e9` into sec
/// (:297 checked_add) and normalize (:298);
/// total seconds `out_secs + sec` (:300 checked_add); hence the :301
/// `Duration::new` carry precondition is always satisfiable (nsec_final < 1e9).
pub open spec fn add_current_sem(sec: u64, nsec: u64, out_secs: u64, out_nanos: u32) -> (r: Option<(u64, u32)>) {
    let nsec1: int = out_nanos@ + nsec@;      // :295
    if nsec1 > U64_MAX {
        None                                  // :295 overflow -> Err(NumberOverflow)
    } else {
        let (carry, nsec_final): (int, int) =
            if nsec1 >= NANOS_PER_SEC {       // :296 (tip `>=`)
                (nsec1 / NANOS_PER_SEC, nsec1 % NANOS_PER_SEC) // :297/:298
            } else { (0, nsec1) };
        let sec1: int = sec@ + carry;         // sec + q (:297)
        if sec1 > U64_MAX {
            None                              // :297 overflow -> Err(NumberOverflow)
        } else if out_secs@ + sec1 > U64_MAX {
            None                              // :300 overflow -> Err(NumberOverflow)
        } else {
            Some(((out_secs@ + sec1) as u64, nsec_final as u32)) // :301 Ok
        }
    }
}

/// Bridge between the exec result and the semantics (machine types compared
/// directly; `@` only the operand-position idiom).
pub open spec fn result_sat_sem(r: Result<(u64, u32), ()>, sem: Option<(u64, u32)>) -> bool {
    match r {
        Ok(p) => sem == Some(p),
        Err(_) => sem == None,
    }
}

/// Transcription of the tip `add_current` (upstream duration.rs:294-303).
/// Inputs: the pending (sec, nsec) and the current accumulator state
/// (out_secs, out_nanos); the model `Err(())` =
/// NumberOverflow.
///
/// The requires are model-domain assumptions only (not caller duties
/// beyond the documented contract):
///   - `out_nanos < 1e9`: the std Duration subsec_nanos invariant (the
///     accumulator is written back normalized by this fn; the Parser side
///     maintains it inductively).
///   - (contrast the 2.4.0 old PoC's `nsec <= 1e9` domain assumption:
///     **the tip form no longer needs it** -- `>=` normalization holds for
///     any u64 nsec: exactly the full domain the fix grants.)
///
/// Postcondition: the functional semantics (result_sat_sem x add_current_sem,
/// fully determines r) + the Ok branch always normalizes nanos (< 1e9,
/// restoring the std Duration invariant, so the :301 Duration::new call
/// carries no panic obligation).
///
/// The cross-file caller is src/lib.rs::duration_from_str_entry_12min
/// (the FromStr delegation chain of wrapper.rs:86-91).
pub exec fn add_current_tip(
    sec: u64,
    nsec: u64,
    out_secs: u64,
    out_nanos: u32,
) -> (r: Result<(u64, u32), ()>)
    requires
        out_nanos@ < NANOS_PER_SEC,   // A1: the std Duration subsec_nanos invariant
    ensures
        result_sat_sem(r, add_current_sem(sec, nsec, out_secs, out_nanos)),
        r.is_Ok() ==> {
            let (s, n) = r.get_Ok_0();
            n@ < NANOS_PER_SEC        // normalization postcondition (restores the std invariant)
        }
{
    let mut sec_m: u64 = sec;

    // upstream:295: `let mut nsec = (out.subsec_nanos() as u64).add(nsec)?;`
    let base: u64 = out_nanos as u64;
    let mut nsec_m: u64 = match base.checked_add(nsec) {
        None => return Err(()),                  // `?` -> NumberOverflow
        Some(v) => v,
    };

    if nsec_m >= 1_000_000_000 {                 // upstream:296 (tip verbatim `>=`)
        // upstream:297: `sec = sec.add(nsec / 1e9)?;` (the div constant is nonzero)
        let q: u64 = nsec_m / 1_000_000_000;
        match sec_m.checked_add(q) {
            None => return Err(()),              // `?` -> NumberOverflow (the triggering value returns here)
            Some(v) => { sec_m = v; }
        }
        nsec_m = nsec_m % 1_000_000_000;         // upstream:298
    }

    // upstream:300: `sec = out.as_secs().add(sec)?;`
    match out_secs.checked_add(sec_m) {
        None => return Err(()),                  // `?` -> NumberOverflow
        Some(v) => { sec_m = v; }
    }

    // upstream:301: `*out = Duration::new(sec, nsec as u32);`
    let nanos_u32: u32 = nsec_m as u32;          // cast: nsec_m < 1e9 < 2^32 (domain proven)
    let _ = duration_new_model(sec_m, nanos_u32); // the carry precondition is now satisfiable
    Ok((sec_m, nanos_u32))
}

// ---------- direct sequence: the numeric core of parse_unit ----------

/// Unit table (the numeric literals of upstream:255-266 / the :318-336 Unit enum):
/// idx 0..=9 in order Nanosecond..Year; returns (whole seconds per n, whole nanos per n).
pub open spec fn unit_scale_sem(unit: u64) -> (r: (u64, u64)) {
    if unit@ == 0 { (0, 1) }              // Unit::Nanosecond
    else if unit@ == 1 { (0, 1_000) }     // Unit::Microsecond
    else if unit@ == 2 { (0, 1_000_000) } // Unit::Millisecond
    else if unit@ == 3 { (1, 0) }         // Unit::Second
    else if unit@ == 4 { (60, 0) }        // Unit::Minute
    else if unit@ == 5 { (3_600, 0) }     // Unit::Hour
    else if unit@ == 6 { (86_400, 0) }    // Unit::Day
    else if unit@ == 7 { (604_800, 0) }   // Unit::Week (86400*7)
    else if unit@ == 8 { (2_630_016, 0) } // Unit::Month (30.44d)
    else { (31_557_600, 0) }              // Unit::Year (365.25d)
}

pub exec fn unit_scale(unit: u64) -> (r: (u64, u64))
    requires
        unit@ <= 9,
    ensures
        r == unit_scale_sem(unit),
{
    if unit == 0 { (0, 1) }
    else if unit == 1 { (0, 1_000) }
    else if unit == 2 { (0, 1_000_000) }
    else if unit == 3 { (1, 0) }
    else if unit == 4 { (60, 0) }
    else if unit == 5 { (3_600, 0) }
    else if unit == 6 { (86_400, 0) }
    else if unit == 7 { (604_800, 0) }
    else if unit == 8 { (2_630_016, 0) }
    else { (31_557_600, 0) }
}

/// Semantics of the `parse_unit` integer part (upstream:254-267): the two
/// checked_muls n*(usec,unsec),
/// either one overflowing => Err; otherwise it feeds into add_current.
pub open spec fn parse_unit_core_sem(n: u64, unit: u64, out_secs: u64, out_nanos: u32) -> (r: Option<(u64, u32)>) {
    let (usec, unsec): (u64, u64) = unit_scale_sem(unit);
    if n@ * usec@ > U64_MAX || n@ * unsec@ > U64_MAX {
        None                                 // upstream:257-265 checked_mul `?`
    } else {
        add_current_sem((n@ * usec@) as u64, (n@ * unsec@) as u64, out_secs, out_nanos)
    }
}

/// Transcription of the `parse_unit` integer part (upstream:254-267): the
/// upstream character scanning (the string-taking branch of Parser::parse /
/// parse_unit) is an input-layer external stub -- this core carries all the
/// numeric obligations.
pub exec fn parse_unit_core(
    n: u64,
    unit: u64,
    out_secs: u64,
    out_nanos: u32,
) -> (r: Result<(u64, u32), ()>)
    requires
        unit@ <= 9,
        out_nanos@ < NANOS_PER_SEC,
    ensures
        result_sat_sem(r, parse_unit_core_sem(n, unit, out_secs, out_nanos)),
        r.is_Ok() ==> r.get_Ok_0().1@ < NANOS_PER_SEC,
{
    let (usec, unsec) = unit_scale(unit);
    let sec = match n.checked_mul(usec) {         // upstream:257-265: n.mul(...)? (arm-by-arm isomorphic)
        None => return Err(()),
        Some(v) => v,
    };
    let nsec = match n.checked_mul(unsec) {
        None => return Err(()),
        Some(v) => v,
    };
    add_current_tip(sec, nsec, out_secs, out_nanos)
}

/// Semantics of the `parse_unit` fractional part (upstream:275-286):
/// n*(usec,unsec)/d -- `OverflowOp::div` (upstream:98-103) demands a zero
/// remainder; fractional ns is unsupported (:276).
/// The requires (d>0) is the machine precondition of the upstream div; the
/// upstream denominator is always >= 10 (the 10-powers of parse_fractional_part).
///  (Upstream div acts on the **product**: `n.mul(...)?.div(d)?`)
pub open spec fn parse_unit_frac_sem(n: u64, unit: u64, d: u64, out_secs: u64, out_nanos: u32) -> (r: Option<(u64, u32)>) {
    // the let initializers sit at argument position -- the 0+ identity lands
    // the values on the int face
    let di: int = 0 + d@;
    let ni: int = 0 + n@;
    if unit@ == 0 {
        None                                  // upstream:276: fractional nanos -> NumberOverflow
    } else {
        let (usec, unsec): (u64, u64) = unit_scale_sem(unit);
        let usi: int = 0 + usec@;
        let uni: int = 0 + unsec@;
        if ni * usi > U64_MAX || ni * uni > U64_MAX {
            None                              // upstream:278-285 checked_mul `?`
        } else if ni * usi % di != 0 || ni * uni % di != 0 {
            None                              // upstream:278-285 div(d) `?` (zero-remainder check)
        } else {
            add_current_sem((ni * usi / di) as u64, (ni * uni / di) as u64, out_secs, out_nanos)
        }
    }
}

/// Transcription of the `parse_unit` fractional part (upstream:275-286).
/// Apart from `out_nanos < 1e9` the requires are machine preconditions
/// (the div divisor is nonzero -- against the upstream `OverflowOp::div`
/// contract verbatim).
pub exec fn parse_unit_frac_core(
    n: u64,
    unit: u64,
    d: u64,
    out_secs: u64,
    out_nanos: u32,
) -> (r: Result<(u64, u32), ()>)
    requires
        unit@ <= 9,
        d@ > 0,
        out_nanos@ < NANOS_PER_SEC,
    ensures
        result_sat_sem(r, parse_unit_frac_sem(n, unit, d, out_secs, out_nanos)),
        r.is_Ok() ==> r.get_Ok_0().1@ < NANOS_PER_SEC,
{
    if unit == 0 {
        return Err(());                           // upstream:276
    }
    let (usec, unsec) = unit_scale(unit);
    let sec = match n.checked_mul(usec) {         // upstream:278-285: n.mul(...)?
        None => return Err(()),
        Some(v) => v,
    };
    let nsec = match n.checked_mul(unsec) {
        None => return Err(()),
        Some(v) => v,
    };
    // upstream:278-285: `n.mul(...)?.div(d)?` (zero remainder passes, else NumberOverflow)
    let sec = if sec % d == 0 { sec / d } else { return Err(()); };
    let nsec = if nsec % d == 0 { nsec / d } else { return Err(()); };
    add_current_tip(sec, nsec, out_secs, out_nanos)
}

// ---------- input-layer stub (external_body + faithful spec) ----------

/// `Unit::from_str` (upstream:318-336): a pure string -> unit mapping table
/// (10 fully enumerated families, otherwise `_ => Err(())`). This is the
/// input-parsing layer: an external_body stub; the faithful spec = the table
/// matched entry by entry (Ok iff the unique table idx; Err iff no idx hits).
/// Byte model Vec<u8> (String has no vstd spec; the µs of "µs" is two UTF-8 bytes).
pub open spec fn spec_unit_match(unit: u64, s: Seq<u8>) -> bool {
    (unit@ == 0 && (s == seq![0x6e, 0x73] || s == seq![0x6e, 0x73, 0x65, 0x63]
        || s == seq![0x6e, 0x61, 0x6e, 0x6f, 0x73]))                       // "ns"/"nsec"/"nanos"
    || (unit@ == 1 && (s == seq![0x75, 0x73] || s == seq![0x75, 0x73, 0x65, 0x63]
        || s == seq![0xc2, 0xb5, 0x73]))                                    // "us"/"usec"/"µs"
    || (unit@ == 2 && s == seq![0x6d, 0x73])                                // "ms" (isomorphic families: ms/s/m/h/d/w/M/y)
    || (unit@ == 3 && s == seq![0x73])                                      // "s"
    || (unit@ == 4 && s == seq![0x6d])                                      // "m"
    || (unit@ == 5 && s == seq![0x68])                                      // "h"
    || (unit@ == 6 && s == seq![0x64])                                      // "d"
    || (unit@ == 7 && s == seq![0x77])                                      // "w"
    || (unit@ == 8 && s == seq![0x4d])                                      // "M"
    || (unit@ == 9 && s == seq![0x79])                                      // "y"
}

#[verifier::external_body]
pub exec fn unit_from_str_model(s: &Vec<u8>) -> (r: Result<u64, ()>)
    ensures
        match r {
            Ok(u) => u@ <= 9 && spec_unit_match(u, s@),
            Err(_) => forall |u: u64| u@ <= 9 ==> !spec_unit_match(u, s@),
        },
{
    Err(()) // stub body (does not participate in verification obligations; the real implementation is upstream:318-336)
}

// ---------- UT-contract anchoring (the test_overlow spirit: overflow => Err, not panic) ----------

/// PoC trigger state: `"{u64::MAX}s 999999999ns 1ns"` (the input that
/// demonstrably panicked in 2.4.0) reaches nsec == 1e9 and secs == MAX after
/// the :295 addition -- the tip form **returns Err(NumberOverflow)** via the
/// :297 `?` (the documented error channel, no panic obligation).
/// Semantics: sem(0, 1e9, MAX, 0) = None (carry=1 makes out_secs+sec1 > U64_MAX).
pub exec fn f2_tip_overflow_returns_err() -> (r: Result<(u64, u32), ()>)
    ensures
        r matches Err(_),                  // the documented NumberOverflow, no panic
        !(r matches Ok(_)),
{
    add_current_tip(0, 1_000_000_000, 18446744073709551615u64, 0)
}

/// UT control 1 (test_units, upstream:499): "12min" -> 720s.
pub exec fn f2_tip_regular_input_12min() -> (r: Result<(u64, u32), ()>)
    ensures
        r === Ok((720u64, 0u32)),
{
    parse_unit_core(12, 4, 0, 0)
}

/// UT control 2 (test_units, upstream:520): "12M" -> 12*2_630_016 seconds.
pub exec fn f2_tip_regular_input_12M() -> (r: Result<(u64, u32), ()>)
    ensures
        r === Ok((31_560_192u64, 0u32)),
{
    parse_unit_core(12, 8, 0, 0)
}

/// UT fractional case (test_fractional_units, upstream:638): "100.0m" -> 6000s
///  (the fractional d==1 divides trivially).
pub exec fn f2_tip_fractional_100_0m() -> (r: Result<(u64, u32), ()>)
    ensures
        r === Ok((6_000u64, 0u32)),
{
    proof {
        // "100.0m": minute=idx4 => (60,0); the d==1 division is trivial;
        // zero-initialized add_current
        assert(parse_unit_frac_sem(100u64, 4u64, 1u64, 0u64, 0u32)
            == Some((6000u64, 0u32)));
    }
    parse_unit_frac_core(100, 4, 1, 0, 0)
}


/* ================================================================
 * Section F3: FormattedDuration::fmt components + the roundtrip value-layer theorems
 * ================================================================ */

// The time-unit weights of upstream:437-449 (the String-layer rendering item_plural is out of scope)
pub open spec const Y_SECONDS: int = 31_557_600;   // 365.25d (the upstream years weight)
pub open spec const MO_SECONDS: int = 2_630_016;   // 30.44d (the upstream months weight)
pub open spec const DAY_SECONDS: int = 86_400;
pub open spec const HOUR_SECONDS: int = 3_600;
pub open spec const MILLIS_BASE: int = 1_000_000;
pub open spec const MICROS_BASE: int = 1_000;

/// Numeric components of `FormattedDuration::fmt` (upstream:429-459; the
/// rendering layer is out of scope). `nanos` is the subsec_nanos of the std
/// Duration (< 1e9).
pub open spec fn fmt_components(
    secs: u64, nanos: u32,
) -> (r: (u64, u64, u64, u64, u64, u64, u32, u32, u32)) {
    let years: u64 = secs / 31_557_600;                       // upstream:437
    let ydays: u64 = secs % 31_557_600;                       // upstream:438
    let months: u64 = ydays / 2_630_016;                      // upstream:439
    let mdays: u64 = ydays % 2_630_016;                       // upstream:440
    let days: u64 = mdays / 86_400;                           // upstream:441
    let day_secs: u64 = mdays % 86_400;                       // upstream:442
    let hours: u64 = day_secs / 3_600;                        // upstream:443
    let minutes: u64 = day_secs % 3_600 / 60;                 // upstream:444
    let seconds: u64 = day_secs % 60;                         // upstream:445
    let millis: u32 = nanos / 1_000_000;                      // upstream:447
    let micros: u32 = nanos / 1000 % 1000;                    // upstream:448
    let nanosec: u32 = nanos % 1000;                          // upstream:449
    (years, months, days, hours, minutes, seconds, millis, micros, nanosec)
}

/// Exec transcription (upstream:429-459): all divisions/mods are by nonzero
/// constants (no panic surface); the component bounds match the documented
/// rendering (hours<24, minutes/seconds<60, ms/us/ns<1000 -- the narrowing
/// domain of ` as u32` is guaranteed by the requires nanos<1e9).
/// Upstream doc (duration.rs:375-392):
///   Formats duration into a human-readable string
///   Note: this format is guaranteed to have same value when using
///   parse_duration, but we can change some details of the exact
///   composition of the value.
pub exec fn format_duration_core(
    secs: u64, nanos: u32,
) -> (r: (u64, u64, u64, u64, u64, u64, u32, u32, u32))
    requires
        nanos@ < NANOS_PER_SEC,   // the std Duration subsec_nanos invariant
    ensures
        r == fmt_components(secs, nanos),
        r.3@ < 24,                // hours
        r.4@ < 60,                // minutes
        r.5@ < 60,                // seconds
        r.6@ < 1000,              // millis
        r.7@ < 1000,              // micros
        r.8@ < 1000,              // nanosec
{
    let years: u64 = secs / 31_557_600;                       // upstream:437
    let ydays: u64 = secs % 31_557_600;                       // upstream:438
    let months: u64 = ydays / 2_630_016;                      // upstream:439
    let mdays: u64 = ydays % 2_630_016;                       // upstream:440
    let days: u64 = mdays / 86_400;                           // upstream:441
    let day_secs: u64 = mdays % 86_400;                       // upstream:442
    let hours: u64 = day_secs / 3_600;                        // upstream:443
    let minutes: u64 = day_secs % 3_600 / 60;                 // upstream:444
    let seconds: u64 = day_secs % 60;                         // upstream:445
    let millis: u32 = nanos / 1_000_000;                      // upstream:447
    let micros: u32 = nanos / 1000 % 1000;                    // upstream:448
    let nanosec: u32 = nanos % 1000;                          // upstream:449
    (years, months, days, hours, minutes, seconds, millis, micros, nanosec)
}

/// Numeric core of the UT roundtrip property (upstream:715-741
/// all_86400_seconds / random_second / random_any): the seconds component
/// is reconstructed by the unit weights (the FromStr table of upstream:322-332).
///  (Shared component->total reconstruction model, kept in src with
///   fmt_components for the harness roundtrip theorems to reference via
///   #[path] mod; removal degrades the z3 context of the unrelated
///   f2_tip_fractional_100_0m.)
pub open spec fn secs_reconstruct(c: (u64, u64, u64, u64, u64, u64)) -> int {
    let (years, months, days, hours, minutes, seconds) = c;
    years@ * Y_SECONDS + months@ * MO_SECONDS + days@ * DAY_SECONDS
        + hours@ * HOUR_SECONDS + minutes@ * 60 + seconds@
}

/// Sub-second components reconstructed by the ms/us/ns weights.
pub open spec fn nanos_reconstruct(c: (u32, u32, u32)) -> int {
    let (millis, micros, nanosec) = c;
    millis@ * MILLIS_BASE + micros@ * MICROS_BASE + nanosec@
}

/* ================================================================
 * Section P2: the parse_duration Scanner state machine -- parsing-side
 * transcription
 *  (mirrors upstream duration.rs:112-373)
 *
 * Coverage: Parser::parse_first_char (:173-187), the double-layer scan state
 * machine of Parser::parse (:118-171, the 'outer label + loop1 digit spans + loop2
 * unit-letter/whitespace/digit restart), parse_fractional_part (:189-228),
 * the string dispatch of parse_unit + the OverflowOp numeric chain (:234-291),
 * parse_duration (:364-373, including the "0" special case).
 *
 * Structure: the upstream iterative state machine carrying 'outer /
 * 'while let Some(c)' is rewritten as an **equally-shaped exec recursion**
 * (byte positions strictly increase, decreases = len - idx, equivalent
 * behavior) -- one spec sem + one exec mirror per sub-state-machine. The
 * position bookkeeping follows the upstream off semantics (InvalidCharacter
 * => the offending character's position; NumberExpected => the scan-start
 * frozen offset (:174 `let off = self.off()`), see the G2 obligation anchor).
 *
 * Input domain: ASCII bytes (upstream scans by Unicode `char`;
 * `char::is_whitespace` is modeled as {0x20, 0x09..=0x0d}, letters as
 * a-z/A-Z; 'µ' (two UTF-8 bytes) and non-ASCII whitespace/letters are left
 * to runtime re-confirmation).
 *
 * Error codes (the int-code model of the upstream duration.rs:7-54 Error
 * enum, exec face): the carrier tuple (code, off1, off2).
 * ================================================================ */

/// Upstream `Error::InvalidCharacter(offset)` (:14; code=10+0=20, kept distinct from the date side).
pub const P2_ERR_INVALID_CHARACTER: isize = 20;
/// upstream `Error::NumberExpected(offset)` (:23).
pub const P2_ERR_NUMBER_EXPECTED: isize = 21;
/// upstream `Error::NumberOverflow` (:51).
pub const P2_ERR_NUMBER_OVERFLOW: isize = 22;
/// upstream `Error::UnknownUnit{start,end}` (:31-40).
pub const P2_ERR_UNKNOWN_UNIT: isize = 23;
/// upstream `Error::Empty` (:53).
pub const P2_ERR_EMPTY: isize = 24;

// ---------- ASCII byte predicates (the in-domain literal counterparts of char::is_whitespace / loop1-2) ----------

/// In-domain whitespace byte model: space + \t \n \v \f \r (the ASCII face of char::is_whitespace).
pub open spec fn is_ws_byte(b: u8) -> bool {
    b@ == 0x20 || (0x09 <= b@ <= 0x0d)
}

/// ASCII letters ( 'a'..='z' | 'A'..='Z'; the in-ASCII-domain face of the
/// upstream :133/:157 arms `_ | _ | 'µ'`; the enum doc sentence "anything
/// that is not alphanumeric is prohibited" cannot be promised -- see the
/// SPEC-DOC MISMATCH notes at scan_num_model / scan_unit_model).
pub open spec fn is_unit_letter(b: u8) -> bool {
    (0x61 <= b@ <= 0x7a) || (0x41 <= b@ <= 0x5a)
}

// ---------- parse_first_char (upstream duration.rs:173-187) ----------

/// `parse_first_char` spec (recursive mirror): skips whitespace; a digit ->
/// (value, successor position); a non-digit non-whitespace ->
/// `Error::NumberExpected(off)` with off **frozen at the scan start**
/// (upstream :174 `let off = self.off()` sits outside the loop -- the error
/// offset does not advance over skipped whitespace; that semantics disagrees
/// with the upstream :23 doc "offset of the erroneous character", see the
/// SPEC-DOC MISMATCH note at parse_first_char_model).
pub open spec fn parse_first_char_sem(b: Seq<u8>, idx: int)
    -> (r: Result<(Option<u64>, usize), (isize, usize)>)
{
    parse_first_char_go(b, idx, idx)
}

/// Recursive body with the frozen off (a mirror of the upstream :173-187 for
/// loop; off0 = the entry snapshot of :174's `let off = self.off()`, the
pub open spec fn parse_first_char_go(b: Seq<u8>, idx: int, off0: int)
    -> (r: Result<(Option<u64>, usize), (isize, usize)>)
    decreases b.len() - idx,
{
    if idx >= b.len() {
        Ok((None, idx as usize))
    } else {
        let c = b[idx];
        if 48 <= c <= 57 {                      // '0'..='9' (upstream:177)
            Ok((Some(((c - 48) as u64) as u64), (idx + 1) as usize))   // upstream:178
        } else if is_ws_byte(c) {               // upstream:180
            parse_first_char_go(b, idx + 1, off0)
        } else {
            Err((P2_ERR_NUMBER_EXPECTED, off0 as usize))   // upstream:182 (frozen off)
        }
    }
}

/// Exec mirror of `parse_first_char` (upstream :173-187): off0 frozen at the
/// entry (upstream :174's `let off = self.off()`).
pub exec fn parse_first_char_model(b: &Vec<u8>, idx: usize)
    -> (r: Result<(Option<u64>, usize), (isize, usize)>)
    requires
        idx@ <= b@.len(),
    ensures
        r === parse_first_char_sem(b@, idx as int),
        // progress properties: resume bounded; a digit => resume > idx
        // (terminates the upper recursion)
        r matches Ok((None, p)) ==> p <= b@.len(),
        r matches Ok((Some(v), p)) ==> p <= b@.len() && p > idx,
        // Err channel (upstream:182 NumberExpected; frozen off = entry)
        r matches Err((code, c)) ==> code == P2_ERR_NUMBER_EXPECTED && c == idx,
        // SPEC-DOC MISMATCH (unreported): the "byte offset of the erroneous
        // character" doc promise is unprovable -- the offset is frozen at scan
        // entry, so with preceding whitespace it points at the first skipped
        // byte rather than the erroneous character; the ensures above carries
        // the implementation-faithful frozen form.
{
    parse_first_char_go_model(b, idx, idx)
}

/// Recursive body with the frozen off (a same-shaped recursion over the :175-185 for loop).
exec fn parse_first_char_go_model(b: &Vec<u8>, idx: usize, off0: usize)
    -> (r: Result<(Option<u64>, usize), (isize, usize)>)
    requires
        idx@ <= b@.len(),
        off0@ <= b@.len(),
    ensures
        r === parse_first_char_go(b@, idx as int, off0 as int),
        r matches Ok((None, p)) ==> p <= b@.len(),
        r matches Ok((Some(v), p)) ==> p <= b@.len() && p > idx,
        r matches Err((code, c)) ==> code == P2_ERR_NUMBER_EXPECTED && c == off0,
    decreases b@.len() - idx@,
{
    if idx == b.len() {
        return Ok((None, idx));
    }
    let c: u8 = b[idx];
    if c >= b'0' && c <= b'9' {                                 // upstream:177-178
        return Ok((Some((c - b'0') as u64), idx + 1));
    }
    if c == b' ' || (0x09 <= c && c <= 0x0d) {                   // upstream:180
        return parse_first_char_go_model(b, idx + 1, off0);
    }
    Err((P2_ERR_NUMBER_EXPECTED, off0))                         // upstream:182 (frozen off)
}

// ---------- parse_fractional_part (upstream duration.rs:189-228) ----------

/// `parse_fractional_part` spec. dot = the byte index of the '.'; the `off`
/// initial value is the '.' position of the :231 off(), at the :138 call
/// site); returns (num, den, term_start, resume) with the denominator already
/// > 1 when digits were seen:
///   term_start = the off value of the upstream `start = off` (the terminal
///   letter position; on exhaustion it advances with the digits to len; with
///   no digits it stays at dot -- matching the upstream `*off` per-position
///   update);
///   resume = the successor scan position (terminal letter +1; exhaustion = len).
/// Exits: denominator==1 (empty fraction) -> InvalidCharacter(dot) (upstream:220-222);
/// a non-digit non-whitespace non-letter -> InvalidCharacter(the current position) (upstream:214-215);
/// checked mul/add overflow -> NumberOverflow (upstream:196/:198/:203/:206).
pub open spec fn frac_part_sem(
    b: Seq<u8>, dot: int, idx: int, num: int, den: int, zeros: bool,
) -> (r: Result<(u64, u64, usize, usize), (isize, usize)>)
    decreases b.len() - idx,
{
    if idx >= b.len() {
        if den == 1 {
            Err((P2_ERR_INVALID_CHARACTER, dot as usize))   // upstream:220-222
        } else {
            Ok((num as u64, den as u64, b.len() as usize, b.len() as usize)) // *off->len
        }
    } else {
        let c = b[idx];
        if c == 0x30 {                                       // '0' (upstream:195-200)
            if den * 10 > U64_MAX {
                Err((P2_ERR_NUMBER_OVERFLOW, 0usize))
            } else if !zeros && num * 10 > U64_MAX {
                Err((P2_ERR_NUMBER_OVERFLOW, 0usize))         // upstream:198
            } else {
                frac_part_sem(b, dot, idx + 1, if !zeros { num * 10 } else { num },
                    den * 10, zeros)
            }
        } else if 0x31 <= c <= 0x39 {                        // '1'..='9' (upstream:201-208)
            if den * 10 > U64_MAX || num * 10 + (c - 48) > U64_MAX {
                Err((P2_ERR_NUMBER_OVERFLOW, 0usize))         // upstream:203-207
            } else {
                frac_part_sem(b, dot, idx + 1, num * 10 + (c - 48), den * 10, false)
            }
        } else if is_ws_byte(c) {                            // upstream:209
            frac_part_sem(b, dot, idx + 1, num, den, zeros)
        } else if is_unit_letter(c) {                        // upstream:210-212 (break)
            if den == 1 {
                Err((P2_ERR_INVALID_CHARACTER, dot as usize))   // upstream:220-222
            } else {
                Ok((num as u64, den as u64, idx as usize, (idx + 1) as usize))
            }
        } else {
            Err((P2_ERR_INVALID_CHARACTER, idx as usize))    // upstream:213-215
        }
    }
}

/// Exec mirror of `parse_fractional_part` (upstream :189-228). The checked_muls
/// correspond digit by digit (no panic surface).
pub exec fn frac_part_model(
    b: &Vec<u8>, dot: usize, idx: usize,
    num: u64, den: u64, zeros: bool,
) -> (r: Result<(u64, u64, usize, usize), (isize, usize)>)
    requires
        dot@ <= idx@ <= b@.len(),
        den@ >= 1,
    ensures
        r === frac_part_sem(b@, dot as int, idx as int, num as int, den as int, zeros),
        // Progress/domain properties (the recursion termination of the upper
        //   state machine and the upstream div precondition follow by induction):
        //   Ok => resume bounded, position ts >= dot, den > 1 (the flip side of the :220 upstream Err);
        //   Err channel is one of {InvalidCharacter, NumberOverflow}.
        r matches Ok((nu, de, ts, resume)) ==> {
            dot <= ts && ts <= b@.len() && resume <= b@.len()
                && (resume == b@.len() || resume == ts + 1)
                && idx <= resume && de > 1
        },
        r matches Err((code, a)) ==> {
            code == P2_ERR_INVALID_CHARACTER || code == P2_ERR_NUMBER_OVERFLOW
        },
    decreases b@.len() - idx@,
{
    if idx == b.len() {
        if den == 1 {
            return Err((P2_ERR_INVALID_CHARACTER, dot));      // upstream:220-222
        } else {
            return Ok((num, den, b.len(), b.len()));          // *off -> len
        }
    }
    let c: u8 = b[idx];
    if c == b'0' {                                            // upstream:195-200
        let den1: Option<u64> = den.checked_mul(10);
        match den1 {
            None => return Err((P2_ERR_NUMBER_OVERFLOW, 0)),
            Some(den2) => {
                let num2: u64 = if !zeros {
                    match num.checked_mul(10) {              // upstream:198
                        None => return Err((P2_ERR_NUMBER_OVERFLOW, 0)),
                        Some(v) => v,
                    }
                } else { num };
                return frac_part_model(b, dot, idx + 1, num2, den2, zeros);
            }
        }
    }
    if c >= b'1' && c <= b'9' {                               // upstream:201-208
        let d: u64 = (c - b'0') as u64;
        let den1: Option<u64> = den.checked_mul(10);
        let m1: u64 = match den1 {
            None => return Err((P2_ERR_NUMBER_OVERFLOW, 0)),
            Some(den2) => den2,
        };
        let m2: Option<u64> = num.checked_mul(10);               // upstream:206
        let m3: u64 = match m2 {
            None => return Err((P2_ERR_NUMBER_OVERFLOW, 0)),
            Some(v) => v,
        };
        let m4: Option<u64> = m3.checked_add(d);                 // upstream:206 c-48
        let num3: u64 = match m4 {
            None => return Err((P2_ERR_NUMBER_OVERFLOW, 0)),
            Some(v) => v,
        };
        return frac_part_model(b, dot, idx + 1, num3, m1, false);
    }
    if c == b' ' || (0x09 <= c && c <= 0x0d) {                // upstream:209
        return frac_part_model(b, dot, idx + 1, num, den, zeros);
    }
    if (0x61 <= c && c <= 0x7a) || (0x41 <= c && c <= 0x5a) {     // upstream:210-212
        //  ('µ' (UTF-8 lead 0xc2) is non-ASCII, outside the runtime confirmation scope)
        if den == 1 {
            return Err((P2_ERR_INVALID_CHARACTER, dot));      // upstream:220-222
        }
        return Ok((num, den, idx, idx + 1));
    }
    Err((P2_ERR_INVALID_CHARACTER, idx))                      // upstream:213-215
}

// ---------- loop1: digit-span scanning (upstream duration.rs:121-146) ----------
//
//  (The functional-spec recursion of the composite state machine jumps across
//   variables, so termination cannot be proved automatically -- the composite
//   layer of this file uses **property-style contracts** in place of a
//   total-function spec: monotone progress + the per-error channel codes;
//   the value-layer semantics ride on the numeric cores (parse_unit_core /
//   _frac_core) and the harness exemplar anchors; the basic recursions
//   (parse_first_char/frac_part) keep total-function sems.)

/// loop1 exec mirror (upstream :121-146). Property contract:
///   - monotone progress: start >= idx, and resume > idx or resume = len -- the
///     exec recursion termination duty of the 'outer state machine
///     (parse_spans_model) is discharged by induction on it;
///   - error channels: Overflow / InvalidCharacter(position).
pub exec fn scan_num_model(b: &Vec<u8>, idx: usize, n: u64)
    -> (r: Result<(usize, usize, Option<(u64, u64)>, u64), (isize, usize, usize)>)
    requires
        idx@ <= b@.len(),
    ensures
        r matches Ok((start, resume, frac, n1)) ==> {
            idx <= start && start <= resume && resume <= b@.len()
                && (resume == b@.len() || resume > idx)
                && (frac matches Some((nu, de)) ==> de > 1)
        },
        r matches Err((code, a, y)) ==> {
            // SPEC-DOC MISMATCH (unreported): the enum doc "anything that is
            // not alphanumeric is prohibited" implies alphanumeric input is
            // accepted, but only [a-zA-Z] (plus the out-of-model µ) pass the
            // letter arms; non-ASCII alphanumerics reach this
            // InvalidCharacter channel. The ensures carries the
            // implementation-faithful form.
            code == P2_ERR_INVALID_CHARACTER || code == P2_ERR_NUMBER_OVERFLOW
        },
    decreases b@.len() - idx@,
{
    if idx == b.len() {
        return Ok((b.len(), b.len(), None, n));               // exhausted: off = len
    }
    let c: u8 = b[idx];
    if c >= b'0' && c <= b'9' {                                // upstream:126-131
        let d: u64 = (c - b'0') as u64;
        let m1: Option<u64> = n.checked_mul(10);                 // upstream:128
        let m2: u64 = match m1 {
            None => return Err((P2_ERR_NUMBER_OVERFLOW, 0, 0)),
            Some(v) => v,
        };
        let m3: Option<u64> = m2.checked_add(d);                 // upstream:129
        let n2: u64 = match m3 {
            None => return Err((P2_ERR_NUMBER_OVERFLOW, 0, 0)),
            Some(v) => v,
        };
        return scan_num_model(b, idx + 1, n2);
    }
    if c == b' ' || (0x09 <= c && c <= 0x0d) {                  // upstream:132
        return scan_num_model(b, idx + 1, n);
    }
    if (0x61 <= c && c <= 0x7a) || (0x41 <= c && c <= 0x5a) {   // upstream:133-135
        return Ok((idx, idx + 1, None, n));
    }
    if c == b'.' {                                              // upstream:136-140
        match frac_part_model(b, idx, idx + 1, 0, 1, true) {    // :138
            Err((e, off)) => return Err((e, off, 0)),
            Ok((num, den, ts, resume)) => {
                return Ok((ts, resume, Some((num, den)), n));
            }
        }
    }
    Err((P2_ERR_INVALID_CHARACTER, idx, 0))                    // upstream:141-142
}

// ---------- loop2: unit-letter-span scanning (upstream duration.rs:147-163) ----------

/// loop2 exec mirror (upstream :147-163). Property contract:
///   - kind 0 (exhausted): unit_end = next = len;
///   - kind 1/2: next = unit_end + 1 and idx <= unit_end < len -- guaranteeing
///     that the recursion position of parse_spans_model strictly advances;
///   - an illegal character -> InvalidCharacter(that character's position) (upstream:158-160).
pub exec fn scan_unit_model(b: &Vec<u8>, idx: usize)
    -> (r: Result<(usize, usize, u64, u64), (isize, usize, usize)>)
    requires
        idx@ <= b@.len(),
    ensures
        r matches Ok((uend, next, kind, dv)) ==> {
            idx <= uend && uend <= b@.len()
                && (kind == 0 ==> next == b@.len() && uend == b@.len())
                && (kind != 0 ==> next == uend + 1 && uend < b@.len() && next <= b@.len())
        },
        r matches Err((code, a, y)) ==> code == P2_ERR_INVALID_CHARACTER,
        // SPEC-DOC MISMATCH (unreported): same as loop1 -- the enum doc
        // "anything that is not alphanumeric is prohibited" implies
        // alphanumeric input is accepted, but only [a-zA-Z] (plus the
        // out-of-model µ) pass the letter arms; the ensures carries the
        // implementation-faithful rejection channel.
    decreases b@.len() - idx@,
{
    if idx == b.len() {
        return Ok((b.len(), b.len(), 0u64, 0u64));
    }
    let c: u8 = b[idx];
    if c >= b'0' && c <= b'9' {                                 // upstream:150-155
        return Ok((idx, idx + 1, 1u64, (c - b'0') as u64));
    }
    if c == b' ' || (0x09 <= c && c <= 0x0d) {                   // upstream:156
        return Ok((idx, idx + 1, 2u64, 0u64));
    }
    if (0x61 <= c && c <= 0x7a) || (0x41 <= c && c <= 0x5a) {
        return scan_unit_model(b, idx + 1);
    }
    Err((P2_ERR_INVALID_CHARACTER, idx, 0))                     // upstream:158-160
}

// ---------- unit-span resolution (upstream duration.rs:234-291, with the OverflowOp chain) ----------

/// Unit-string decision spec: the unique unit in 0..=9 that hits (the alias
/// literals are mutually exclusive), else None.
///  (The upstream FromStr arm order only affects alias matching within a
///  unit; across units the arms are mutually exclusive, hence equal to this
///  first-hit decision.)
pub open spec fn unit_resolved(b: Seq<u8>, start: int, end: int) -> (r: Option<u64>) {
    let sp: Seq<u8> = b.subrange(start, end);
    if spec_unit_match(0, sp) { Some(0) }
    else if spec_unit_match(1, sp) { Some(1) }
    else if spec_unit_match(2, sp) { Some(2) }
    else if spec_unit_match(3, sp) { Some(3) }
    else if spec_unit_match(4, sp) { Some(4) }
    else if spec_unit_match(5, sp) { Some(5) }
    else if spec_unit_match(6, sp) { Some(6) }
    else if spec_unit_match(7, sp) { Some(7) }
    else if spec_unit_match(8, sp) { Some(8) }
    else if spec_unit_match(9, sp) { Some(9) }
    else { None }
}

/// Ranged stub of `Unit::from_str(&self.src[start..end])` (the upstream
/// :242 / :318-336 parse-table input layer). external_body + faithful spec
/// (the decision face above).
#[verifier::external_body]
pub exec fn unit_from_str_range_model(b: &Vec<u8>, start: usize, end: usize)
    -> (r: Result<u64, ()>)
    requires
        start@ <= end@ <= b@.len(),
    ensures
        match unit_resolved(b@, start as int, end as int) {
            Some(u) => r === Ok(u),
            None => r matches Err(_),
        },
{
    Err(()) // external body: the real implementation is upstream :318-336
}

/// Full-layer spec of `parse_unit` (upstream :234-291, the integer + fractional
/// parts): the unit resolved (idx); None iff all Err exits are
/// NumberOverflow (the :257-265 / :276 / :278-285 mul/div/add chain).
pub open spec fn parse_unit_full_sem(
    n: u64, unit: u64, frac: Option<(u64, u64)>, out_secs: u64, out_nanos: u32,
) -> (r: Result<(u64, u32), (isize, usize, usize)>) {
    match parse_unit_core_sem(n, unit, out_secs, out_nanos) {     // upstream:254-267
        None => Err((P2_ERR_NUMBER_OVERFLOW, 0usize, 0usize)),
        Some(p1) => match frac {
            Some((num, den)) => {
                match parse_unit_frac_sem(num, unit, den, p1.0, p1.1) {   // :270-287
                    //  (both the Nanosecond+fraction of :276 and the div nonzero-remainder length fold into NumberOverflow)
                    None => Err((P2_ERR_NUMBER_OVERFLOW, 0usize, 0usize)),
                    Some(p2) => Ok(p2),
                }
            }
            None => Ok(p1),
        },
    }
}

/// `parse_unit` exec mirror (the unit-resolved side; the string dispatch lives in parse_spans_model).
pub exec fn parse_unit_full_core(
    n: u64, unit: u64, frac: Option<(u64, u64)>, out: (u64, u32),
) -> (r: Result<(u64, u32), (isize, usize, usize)>)
    requires
        unit@ <= 9,
        out.1@ < NANOS_PER_SEC,
        frac.is_Some() ==> {                    // upstream :220: denominator > 1 (the :325 div precondition)
            let (nu, de) = frac.get_Some_0();
            de@ > 1
        },
    ensures
        r === parse_unit_full_sem(n, unit, frac, out.0, out.1),
    {
    let r1: Result<(u64, u32), ()> = parse_unit_core(n, unit, out.0, out.1);  // upstream:254-267
    match r1 {
        Err(()) => return Err((P2_ERR_NUMBER_OVERFLOW, 0, 0)),
        Ok((s1, n1)) => {
            match frac {
                Some((num, den)) => {
                    // upstream:270-287 (Nanosecond + fraction of :276 -> NumberOverflow)
                    let r2: Result<(u64, u32), ()> =
                        parse_unit_frac_core(num, unit, den, s1, n1);
                    match r2 {
                        Err(()) => return Err((P2_ERR_NUMBER_OVERFLOW, 0, 0)),
                        Ok(p2) => return Ok(p2),
                    }
                }
                None => return Ok((s1, n1)),
            }
        }
    }
}

// ---------- 'outer state machine (a same-shaped recursion over upstream duration.rs:118-171) ----------

/// 'outer state machine exec mirror. Property contract:
///   - the Err channel code is one of {20,21,22,23} with the same shape
///     (the position/span range carried in the fields);
///   - Ok => the accumulator nanos stay normalized (the std Duration
///     invariant kept inductively) + unit-resolution determinism delegated
///     through the channel (each parse_unit_full_core semantic face is
///     already decided by its sem).
///   - the recursion termination duty follows by induction from the
///     monotone-progress ensures of loop1/loop2.
pub exec fn parse_spans_model(
    b: &Vec<u8>, idx: usize, n: u64, out: (u64, u32),
) -> (r: Result<(u64, u32), (isize, usize, usize)>)
    requires
        idx@ <= b@.len(),
        out.1@ < NANOS_PER_SEC,               // the std Duration subsec_nanos invariant (kept inductively)
    ensures
        r.is_Ok() ==> r.get_Ok_0().1@ < NANOS_PER_SEC,
        r matches Err((code, a, u)) ==> {
            code == P2_ERR_INVALID_CHARACTER || code == P2_ERR_NUMBER_EXPECTED
                || code == P2_ERR_NUMBER_OVERFLOW || code == P2_ERR_UNKNOWN_UNIT
        },
    decreases b@.len() - idx@,
{
    let (start, resume, frac, n1) =
        match scan_num_model(b, idx, n) {                          // upstream:121-146
            Err(e) => return Err(e),
            Ok((s0, r0, f0, nn0)) => (s0, r0, f0, nn0),
        };
    let (uend, next, kind, dv) =
        match scan_unit_model(b, resume) {                        // upstream:147-163
            Err(e) => return Err(e),
            Ok((u0, n0, k0, d0)) => (u0, n0, k0, d0),
        };
    let out1 = match unit_from_str_range_model(b, start, uend) { // upstream:242
        Err(()) => {
            return Err((P2_ERR_UNKNOWN_UNIT, start, uend));       // upstream:245-251
        }
        Ok(unit) => {
            match parse_unit_full_core(n1, unit, frac, out) {      // upstream:254-291
                Err(e) => return Err(e),
                Ok(o1) => o1,
            }
        }
    };
    if kind == 0 {                                                // upstream:165-168
        return Ok(out1);
    }
    if kind == 1 {                                                // upstream:150-155 continue 'outer
        return parse_spans_model(b, next, dv, out1);
    }
    // whitespace -> upstream:166-169
    match parse_first_char_model(b, next) {
        Err((e, off)) => return Err((e, off, 0)),
        Ok((opt, p2)) => match opt {
            None => return Ok(out1),                              // upstream:168
            Some(v) => return parse_spans_model(b, p2, v, out1),
        },
    }
}

// ---------- parse_duration (upstream duration.rs:364-373) ----------

/// `parse_duration` exec transcription (upstream :364-373). Property contract:
///   - the "0" special case (:365-366); empty input / pure whitespace -> Empty (:119);
///   - a first char that is neither digit nor whitespace -> NumberExpected(0)
///     (:182, the same-shaped face of the G2 anchor);
///   - Ok => nanos normalized (Duration::new has no panic surface).
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
pub exec fn parse_duration_model(b: &Vec<u8>)
    -> (r: Result<(u64, u32), (isize, usize, usize)>)
    ensures
        r.is_Ok() ==> r.get_Ok_0().1@ < NANOS_PER_SEC,
        b@ == seq![0x30] ==> r === Ok((0u64, 0u32)),               // upstream:365-366
        (b@ != seq![0x30] && parse_first_char_sem(b@, 0).is_Ok()
            && parse_first_char_sem(b@, 0).get_Ok_0().0.is_None())
            ==> r === Err((P2_ERR_EMPTY, 0, 0)),                     // upstream:119
        (b@ != seq![0x30] && parse_first_char_sem(b@, 0) matches Err(_))
            ==> r === Err((P2_ERR_NUMBER_EXPECTED, 0, 0)),           // upstream:182
{
    if b.len() == 1 && b[0] == b'0' {                             // upstream:365-366
        return Ok((0, 0));
    }
    match parse_first_char_model(b, 0) {                          // upstream:119
        Err((e, off)) => {
            proof {
                assert(e == P2_ERR_NUMBER_EXPECTED);   // the channel property of parse_first_char_model
            }
            return Err((P2_ERR_NUMBER_EXPECTED, 0, 0));
        }
        Ok((None, _)) => return Err((P2_ERR_EMPTY, 0, 0)),
        Ok((Some(v), p)) => {
            proof {
                assert(b@ != seq![0x30]);    // the "0" special case already excluded => first char is not '0'
            }
            parse_spans_model(b, p, v, (0, 0))
        }
    }
}


// ===========================================================================
// Proof lemmas (the section-F2 invariant-closure base; placed at the end of
// the file so the exec implementation reads directly)
// ===========================================================================
/// A1 invariant closure (the induction base): for any input, the Ok component
/// of add_current_sem always satisfies subsec_nanos < 1e9 -- a chained parse
/// (multiple unit spans) can keep using it as the accumulator.
///  (the 'outer-loop induction invariant of the upstream Parser::parse, model face)
pub proof fn f2_tip_invariant_closed() {
    assert(forall |s: u64, n: u64, os: u64, on: u32|
        on@ < NANOS_PER_SEC && add_current_sem(s, n, os, on).is_Some()
        ==> match add_current_sem(s, n, os, on) {
            Some((_, nv)) => nv@ < NANOS_PER_SEC,
            None => false,
        });
}
}
