//! humantime **harness zone** -- the UT roundtrip value-layer theorems over
//! upstream duration.rs:715-741 (all_86400_seconds / random_second /
//! random_any) + the format_duration doc exemplars; the library-body
//! transcription (fmt_components / format_duration_core,
//! FormattedDuration::fmt of upstream duration.rs:429-459) and the shared
//! reconstruction models secs/nanos_reconstruct stay in src/duration.rs.
//!
//! Reference-style structure: `#[path = "../src/duration.rs"] mod duration;`
//! -- it references the src-side verified spec/exec directly (the fmt
//! component decomposition, the unit-weight constants, the reconstruction
//! models), **duplicating no fact source** (referenced names resolve
//! through `use duration::*`).
//!
//! Run: VERUS_Z3_PATH=<z3> <verus> database/humantime/verified/harness/roundtrip.rs
//! Verdict: expects 0 errors (the duration module is re-verified as a whole
//! for the section-F2/F3 library transcriptions plus this file's roundtrip
//! theorems -- the same obligation set as before the split).

// The referenced vstd lemmas
use vstd::prelude::*;
use vstd::arithmetic::div_mod::{
    lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse, lemma_mod_mod,
    lemma_mod_pos_bound,
};

#[path = "../src/duration.rs"]
mod duration;

use duration::*;

verus! {




/// Reconstruction sum (the spec cap used to guide the trigger).
pub open spec fn asserting_reconstruct(c: (u64, u64, u64, u64, u64, u64)) -> int {
    secs_reconstruct(c)
}


// ---------- UT exemplars (format_duration doc examples + smoke) ----------

/// UT exemplar (upstream:388 and test_combo, duration.rs:707): "2h 37m" iff 9420s.
pub exec fn ut_witness_2h37m() -> (r: (u64, u64, u64, u64, u64, u64, u32, u32, u32))
    ensures
        r == (0, 0, 0, 2, 37, 0, 0, 0, 0),
{
    format_duration_core(9420, 0)
}

/// UT exemplar (upstream:390 and test_units): "32ms" iff 32_000_000 ns.
pub exec fn ut_witness_32ms() -> (r: (u64, u64, u64, u64, u64, u64, u32, u32, u32))
    ensures
        r == (0, 0, 0, 0, 0, 0, 32, 0, 0),
{
    format_duration_core(0, 32_000_000)
}

// ---------- the value-layer roundtrip entry ----------

/// The **value-layer roundtrip entry** over upstream duration.rs:715-741 (the
/// UT all_86400_seconds / random renames): the formatting components
/// (duration.rs) are reconstructed through the lemmas (the caller's
/// obligation) back to the original value -- the machine-carried proof of
/// the doc contract "guaranteed to have same value when using parse_duration"
/// (upstream:377-379).
///  (The String-layer read/write is out of scope: the lemmas guarantee that
///   the weight reconstruction equals the original value.)
pub exec fn ut_roundtrip_value_layer(sec: u64, nanos: u32)
    -> (c: (u64, u64, u64, u64, u64, u64, u32, u32, u32))
    requires
        nanos@ < 1_000_000_000,   // the std Duration subsec_nanos invariant
    ensures
        c == duration::fmt_components(sec, nanos),
        secs_reconstruct((c.0, c.1, c.2, c.3, c.4, c.5)) == sec@,
        nanos_reconstruct((c.6, c.7, c.8)) == nanos@,
{
    let c = duration::format_duration_core(sec, nanos);
    proof {
        lemma_secs_roundtrip(sec);
        lemma_nanos_roundtrip(nanos);
    }
    c
}



// ===========================================================================
// Proof lemmas (the roundtrip value-layer bases; placed at the end of the
// file so the exec implementation reads directly)
// ===========================================================================
/// Seconds-component reconstruction theorem (forall; the value-layer base
/// of the roundtrip): reading "2h 37m" on the parse side accumulates the unit
/// weights (upstream:322-332 table) and rebuilds secs exactly.
pub proof fn lemma_secs_roundtrip(secs: u64)
    ensures
        secs_reconstruct((fmt_components(secs, 0u32).0, fmt_components(secs, 0u32).1,
            fmt_components(secs, 0u32).2, fmt_components(secs, 0u32).3,
            fmt_components(secs, 0u32).4, fmt_components(secs, 0u32).5)) == secs@,
{
    // int face (the let initializer sits at argument position -- via the 0+ identity)
    let si: int = 0 + secs@;
    let years: int = si / Y_SECONDS;
    let ydays: int = si % Y_SECONDS;
    let months: int = ydays / MO_SECONDS;
    let mdays: int = ydays % MO_SECONDS;
    let days: int = mdays / DAY_SECONDS;
    let day_secs: int = mdays % DAY_SECONDS;
    let hours: int = day_secs / HOUR_SECONDS;
    let minutes: int = (day_secs % HOUR_SECONDS) / 60;
    let seconds: int = day_secs % 60;
    lemma_fundamental_div_mod(si, Y_SECONDS);      // secs = years*Y + ydays
    lemma_fundamental_div_mod(ydays, MO_SECONDS);     // ydays = months*M + mdays
    lemma_fundamental_div_mod(mdays, DAY_SECONDS);    // mdays = days*DAY + day_secs
    lemma_fundamental_div_mod(day_secs, HOUR_SECONDS);// day_secs = hours*H + rem_h
    lemma_fundamental_div_mod(day_secs % HOUR_SECONDS, 60); // rem_h = minutes*60 + rem_m
    lemma_mod_mod(day_secs, 60, 60);                  // rem_h % 60 == day_secs % 60
    asserting_reconstruct((years as u64, months as u64, days as u64, hours as u64,
        minutes as u64, seconds as u64));
    assert(si == years * Y_SECONDS + ydays);
    assert(ydays == months * MO_SECONDS + mdays);
    assert(mdays == days * DAY_SECONDS + day_secs);
    assert(day_secs == hours * HOUR_SECONDS + day_secs % HOUR_SECONDS);
    assert(day_secs % HOUR_SECONDS == minutes * 60 + seconds);
}
/// Nanoseconds-component reconstruction theorem: nanos = millis*1e6 + micros*1e3 + nanosec
///  (the value-layer base of the sub-second side of the roundtrip; micros in the
///   source form nanos/1000 % 1000).
pub proof fn lemma_nanos_roundtrip(nanos: u32)
    requires
        nanos@ < 1_000_000_000,
    ensures
        nanos_reconstruct((nanos / 1_000_000, nanos / 1000 % 1000, nanos % 1000)) == nanos@,
{
    let ni: int = 0 + nanos@;                       // int face
    let millis: int = ni / MILLIS_BASE;
    let micros: int = ni / 1000 % 1000;
    let nanosec: int = ni % 1000;
    let q1: int = ni / 1000;
    lemma_mod_pos_bound(q1, 1000);                  // micros < 1000
    lemma_mod_pos_bound(ni, 1000);                  // nanosec < 1000
    lemma_fundamental_div_mod(ni, MICROS_BASE);     // ni = 1000*q1 + nanosec
    lemma_fundamental_div_mod(q1, 1000);            // q1 = 1000*(q1/1000) + micros
    assert(ni == 1000 * q1 + nanosec);
    assert(q1 == 1000 * (q1 / 1000) + micros);
    assert(ni == 1_000_000 * (q1 / 1000) + 1000 * micros + nanosec);
    // quotient/remainder uniqueness: 0 <= 1000*micros + nanosec < 1e6 =>
    // millis == q1/1000, and ni % 1e6 == 1000*micros + nanosec
    lemma_fundamental_div_mod_converse(ni, MILLIS_BASE, q1 / 1000,
        1000 * micros + nanosec);
    lemma_fundamental_div_mod(ni, MILLIS_BASE);     // ni = millis*1e6 + ni%1e6
    assert(millis == ni / MILLIS_BASE);
}
}

fn main() {}
